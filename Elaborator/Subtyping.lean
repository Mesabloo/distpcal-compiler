module

public import Elaborator.Monad
public import Core.TypedTLAPlus.Coercion

public section

/-! `<:`, `lub`, `glb`, and term-level coercion, plus the direction-aware metavariable-solving
algorithm used in place of a literal `Specialize` rule.

Term-level coercions aren't always available: `Set`/`Function`/`Tuple`/`Record` can always be
wrapped generally (a set-image, a domain remap via `CHOOSE`, or projecting components/fields out
of the original expression). `Seq` and `Operator` cannot in general — `Seq` has no static arity to
rebuild a literal over, and `Operator` would need a first-class operator value this grammar has no
constructor for — so for these two the structural rule still computes the correct `<:` relation
recursively, but only returns a coercion when the sub-coercion needed is `.id`. `Channel` supports
subtyping only via plain reflexivity (`τ = τ'`); a `receive`'s element-vs-reference coercion is
computed directly, not through `Channel(τ) <: Channel(τ')`. -/

open TypedTLAPlus (Typ MVarId Coercion)

/--
  The three outcomes of a subtyping check — not a plain success/failure, since an unresolved
  metavariable hit from the upper-bound side can't yield a concrete coercion yet, only a recorded
  pending bound. `pending` carries *which* metavariable the eventual coercion depends on, so a
  caller can wrap its expression in `TypedTLAPlus.Expression.mvar` tagged with that id, to be
  resolved once the metavariable is.
-/
inductive SubtypeResult : Type
  /-- `τ <: τ'` holds, and `coe` witnesses it. -/
  | success (coe : Coercion)
  /-- `τ <: τ'` holds *if* metavariable `n` resolves wide enough — not yet known to hold outright. -/
  | pending (n : MVarId)
  /-- `τ <: τ'` does not hold. -/
  | failure

/--
  Per-unresolved-metavariable pending upper bounds — accumulated until `?n` resolves from a
  lower bound (`subtype` itself, below) or defaults at the end of checking. A bound can itself be
  a metavariable (`?m <: ?n`, both unresolved) — recorded here unchanged rather than merged with
  `?n`'s own identity, since `?m`'s and `?n`'s eventual solutions may legitimately diverge, only
  staying `<:`-related.
-/
structure PendingBounds : Type where
  protected bounds : Std.HashMap MVarId (List Typ)

instance : EmptyCollection PendingBounds := ⟨⟨{}⟩⟩

/-- The pending-upper-bounds effect `subtype` needs on top of `MonadMetavarContext`. -/
class MonadPendingBounds (m : Type → Type) where
  /-- The upper bounds recorded so far on a metavariable, `[]` if none (including if it's already
  resolved — callers only consult this while a metavariable is still unresolved). -/
  pendingUpperBounds : MVarId → m (List Typ)
  /-- Record one more upper bound on a metavariable. -/
  addPendingUpperBound : MVarId → Typ → m Unit
export MonadPendingBounds (pendingUpperBounds addPendingUpperBound)

instance {m} [Monad m] [MonadStateOf PendingBounds m] : MonadPendingBounds m where
  pendingUpperBounds n := return (← getThe PendingBounds).bounds.getD n []
  addPendingUpperBound n τ := modify λ ⟨bounds⟩ ↦ ⟨bounds.insert n (τ :: bounds.getD n [])⟩

variable {m : Type → Type} [Monad m] [MonadMetavarContext Typ m] [MonadPendingBounds m]
  [MonadFresh m]

/-- Needed for `subtype`/`tryAxioms`'s own `partial def`s below to type-check at all (an arbitrary
`m` isn't otherwise known nonempty). -/
local instance : Inhabited (m SubtypeResult) := ⟨pure .failure⟩

/-- `subtype` applied pointwise across two equal-length lists (the `Tuple`/`Record`/`Operator`
structural rules below), short-circuiting on the first `pending`/`failure` and otherwise
collecting every component's coercion, in order. -/
private def subtypeAll (go : Typ → Typ → m SubtypeResult) :
    List (Typ × Typ) → m (Except SubtypeResult (List Coercion))
  | [] => return .ok []
  | (τ, τ') :: rest => do
    match ← go τ τ' with
    | .failure => return .error .failure
    | .pending n => return .error (.pending n)
    | .success c => do
      match ← subtypeAll go rest with
      | .error e => return .error e
      | .ok cs => return .ok (c :: cs)

/-- The three non-structural coercions (`STR-TO-SEQ`/`SEQ-TO-FUN`/`TUPLE-TO-SEQ`) — tried once
`subtype` itself finds no direct structural/reflexive match. Each produces an intermediate type
and an axiom coercion, then recurses on `(intermediate, τ')` via `subtypeRec` (always `subtype`
itself, passed in so this stays a plain, non-mutually-recursive `def`) and composes — this
realizes `<:`'s transitivity without a separate closure step: e.g. `Str <: Seq(Int) <: Int → Int`
falls out of `STR-TO-SEQ` finding `Seq(Int)`, recursing, and `SEQ-TO-FUN` firing in turn.
Terminates because the three axioms are acyclic and each only ever fires once per chain. -/
private partial def tryAxioms (subtypeRec : Typ → Typ → m SubtypeResult) (τ τ' : Typ) :
    m SubtypeResult := do
  let chainWith (axiomCoe : Coercion) (mid : Typ) : m SubtypeResult := do
    match ← subtypeRec mid τ' with
    | .failure => return .failure
    | .pending n => return .pending n
    | .success .id => return .success axiomCoe
    | .success next => return .success (.comp axiomCoe next)
  match τ with
  | .str => chainWith .strToSeq (.seq .int)
  | .seq τ₀ => do
    let i ← freshName "i"
    chainWith (.seqToFun τ₀ i) (.function .int τ₀)
  | .tuple (τ₀ :: rest) =>
    if rest.all (· == τ₀) then
      chainWith (.tupleToSeq (rest.length + 1) τ₀) (.seq τ₀)
    else return .failure
  | _ => return .failure

/--
  The type checker's subtyping judgment — see the module doc for `Coercion`'s own
  scope/limitations, and `tryAxioms`/each structural case below for how `Coercion` data gets
  built (discharge itself lives in `Core/TypedTLAPlus/Coercion.lean`'s `Coercion.apply`). Also
  implements the direction-aware metavariable-solving algorithm in the three `mvar` cases below.

  `partial`: no structurally-decreasing measure across `tryAxioms`' recursive calls (its
  intermediate types can be *larger* than the input, e.g. `Str` to `Seq(Int)`).
-/
partial def subtype (τ τ' : Typ) : m SubtypeResult := do
  match τ, τ' with
  | .mvar a, .mvar b => do
    -- A metavariable is trivially its own subtype, resolved or not — checked before the
    -- `assigned?` dispatch below, since two references to one *scheme* declaration can compare
    -- a shared, still-unassigned metavariable against itself. Without this check, `none, none`
    -- would record a spurious self-referential pending bound (`a`'s upper bound becoming `.mvar
    -- a`) instead of recognizing the comparison as vacuous. `Elaborator/Resolution.lean`'s
    -- `resolveExprMVars` relies on this `b <: b` reflexivity always succeeding.
    if a == b then return .success .id
    else match ← assigned? a, ← assigned? b with
    | some s, _ => subtype s τ'
    | none, some t => subtype τ t
    | none, none => addPendingUpperBound a (.mvar b) *> return .pending a
  | .mvar a, _ => do
    match ← assigned? a with
    | some s => subtype s τ'
    | none => addPendingUpperBound a τ' *> return .pending a
  | _, .mvar b => do
    match ← assigned? b with
    | some s => subtype τ s
    | none => do
      let bounds ← pendingUpperBounds b
      match ← subtypeAll subtype (bounds.map (τ, ·)) with
      | .error r => return r
      | .ok _ => assignMVar b τ *> return .success .id
  | .bool, .bool | .int, .int | .str, .str | .address, .address => return .success .id
  | .var a, .var b => return if a == b then .success .id else .failure
  | .const a, .const b => return if a == b then .success .id else .failure
  | .set τ₀, .set τ₀' => do
    match ← subtype τ₀ τ₀' with
    | .success .id => return .success .id
    | .pending n => return .pending n
    | .failure => return .failure
    | .success c => do
      let x ← freshName "x"
      return .success (.set x τ₀ c)
  | .seq τ₀, .seq τ₀' => do
    match ← subtype τ₀ τ₀' with
    | .success .id => return .success .id
    | .pending n => return .pending n
    | _ => return .failure
  | .channel τ₀, .channel τ₀' => return if τ₀ == τ₀' then .success .id else .failure
  | .tuple τs, .tuple τs' => do
    if τs.length ≠ τs'.length then return .failure
    else
      match ← subtypeAll subtype (τs.zip τs') with
      | .error r => return r
      | .ok coes =>
        if coes.all (· matches .id) then return .success .id
        else return .success (.tuple coes τs')
  | .record fs, .record fs' => do
    if fs.map Prod.fst ≠ fs'.map Prod.fst then return .failure
    else
      match ← subtypeAll subtype (fs.map Prod.snd |>.zip (fs'.map Prod.snd)) with
      | .error r => return r
      | .ok coes =>
        if coes.all (· matches .id) then return .success .id
        else
          let fields := ((fs.map Prod.fst).zip coes).zip (fs'.map Prod.snd)
            |>.map λ ((name, c), τ') ↦ (name, c, τ')
          return .success (.record fields)
  | .operator τs τ₀, .operator τs' τ₀' => do
    if τs.length ≠ τs'.length then return .failure
    else
      match ← subtypeAll subtype (τs'.zip τs) with
      | .error r => return r
      | .ok argCoes => do
        match ← subtype τ₀ τ₀' with
        | .failure => return .failure
        | .pending n => return .pending n
        | .success retCoe =>
          if argCoes.all (· matches .id) && retCoe matches .id then return .success .id
          else return .failure
  | .function dom rng, .function dom' rng' => do
    match ← subtype dom dom' with
    | .failure => return .failure
    | .pending n => return .pending n
    | .success cDom => do
      match ← subtype rng rng' with
      | .failure => return .failure
      | .pending n => return .pending n
      | .success cRng =>
        if cDom matches .id && cRng matches .id then return .success .id
        else do
          let x ← freshName "x"
          let y ← freshName "y"
          return .success (.function x y dom rng dom' cDom cRng)
  | _, _ => tryAxioms subtype τ τ'

/-- Whether `τ <: τ'` holds, ignoring the coercion payload — all `lub`/`glb` need. -/
private def isSubtype (τ τ' : Typ) : m Bool := return (← subtype τ τ') matches .success _

/-- The least upper bound of two types under `<:`, where it exists — `<:` is a partial order with
no `⊤`, so `lub` is a *partial* function: comparable types have one (the wider of the two),
incomparable ones don't. -/
def lub (τ τ' : Typ) : m (Option Typ) := do
  if ← isSubtype τ τ' then return some τ'
  else if ← isSubtype τ' τ then return some τ
  else return none

/-- The greatest lower bound, dual to `lub`. -/
def glb (τ τ' : Typ) : m (Option Typ) := do
  if ← isSubtype τ τ' then return some τ
  else if ← isSubtype τ' τ then return some τ'
  else return none

end
