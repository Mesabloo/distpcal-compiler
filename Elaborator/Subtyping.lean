import Elaborator.Monad
import Core.TypedTLAPlus.Coercion

/-!
  `<:`, `lub`, `glb`, and term-level coercion (§5.3, thesis Fig. 3.1.7's `SUBTYPE` rule and Fig.
  3.1.8's subtyping rules), plus the direction-aware metavariable-solving algorithm `PLAN.md`
  §5.3/§2 commits to instead of the thesis's literal `Specialize` rule. Prior art's own
  `Checker/Typechecker/Convertibility.lean` is a `sorry` stub (`CLAUDE.md`) — the algorithm here,
  and every coercion term below, is new implementation work, not a port.

  **`Coercion` is this project's own addition, not the thesis's** — the thesis's `<:` is a purely
  type-level relation with no accompanying term-level witness. Concretely realizing a coercion as
  an `Expr → Expr` sometimes has no available term at all in `TypedTLAPlus.Expression`'s current
  grammar, for structural reasons worth recording once here rather than re-discovering at every
  call site:
  - **`Set`** wraps generally, for *any* `Set(τ)`-typed expression (literal or opaque), via the
    existing set-image node (`{coerce(x) : x ∈ S}`, `Expression.map'`).
  - **`Function`** (covariant in *both* arguments here, unlike ordinary contravariant-domain
    function subtyping — TLA⁺ functions behave like finite maps/hash tables, not closures, thesis
    p. 13) also wraps generally, via a domain remap: the new domain is the image of the old one
    under the domain coercion (`{coerceDom(x) : x ∈ DOMAIN(f)}`), and each new-domain element `y`
    recovers the original argument via `CHOOSE x ∈ DOMAIN(f) : coerceDom(x) = y` to apply the
    original function and the range coercion. (Resolves a domain-construction question the
    project owner's own earlier Isabelle draft of this exact algorithm left an open `TODO` on.)
  - **`Tuple`/`Record`** also wrap generally: arity/field-set is *static* (part of the type
    itself), so a new literal can always be rebuilt by projecting each component/field out of the
    original (possibly opaque) expression via `fnCall`/`recordAccess`.
  - **`Seq`, `Operator` do not wrap in general.** `Seq`'s length is a *dynamic* property, not
    part of the type, so (unlike `Tuple`) there is no static arity to project a fixed-size
    literal rebuild over, and (unlike `Set`) `TypedTLAPlus.Expression` has no "generic map, stays
    `Seq`-typed" node — its only `Seq`-typed literal former (`.seq`) takes an already-fixed
    `List`. `Operator` would need to produce a new first-class operator *value* (an
    eta-expansion/`LAMBDA`), which this grammar has no constructor for at all (thesis Fig. 3.1.4
    has a `LAMBDA` typing rule, but no corresponding `CoreTLAPlus`/`TypedTLAPlus.Expression`
    constructor exists — a gap in its own right, not this file's to fix). For these two, the
    structural rule below still computes the correct `<:` *relation* recursively (useful
    wherever only the boolean fact is needed), but only ever returns a `success` *coercion* when
    the sub-coercion needed turns out to be `.id` — i.e. when nothing would actually need
    wrapping in the first place.
  - **`Channel` gets no subtyping at all beyond plain reflexivity** (`PLAN.md` §2/§9.15,
    resolved after this file's first draft, which had it covariant with the same "`.id`-only"
    treatment as `Seq`/`Operator` above). Not just because there's no literal former to wrap an
    opaque channel value with — the actual need for it disappeared: `[Receive]`'s own channel-
    element-vs-reference-type coercion is computed directly (`subtype` on the two element types,
    stored on the `receive` statement node, discharged at `Guarded2Network`), never by routing
    through a `Channel(τ) <: Channel(τ')` check here. So `Channel(τ) <: Channel(τ')` only ever
    needs to hold — and only ever *should* hold — for `τ = τ'`.
-/

open TypedTLAPlus (Typ MVarId Expression Coercion Expr)

/--
  The three outcomes of a subtyping check (`PLAN.md` §5.3) — not a plain success/failure, since an
  unresolved metavariable hit from the upper-bound side can't yield a concrete coercion yet, only
  a recorded pending bound. `pending` carries *which* metavariable the eventual coercion depends
  on, so a caller (`Elaborator/Expressions.lean`, not yet written) can wrap its expression in
  `TypedTLAPlus.Expression.mvar` tagged with that id, to be resolved once the metavariable is.
-/
inductive SubtypeResult : Type
  /-- `τ <: τ'` holds, and `coe` witnesses it. -/
  | success (coe : Coercion)
  /-- `τ <: τ'` holds *if* metavariable `n` resolves wide enough — not yet known to hold outright. -/
  | pending (n : MVarId)
  /-- `τ <: τ'` does not hold. -/
  | failure

/--
  Per-unresolved-metavariable pending upper bounds (`PLAN.md` §5.3's direction-aware solving) —
  accumulated until `?n` resolves from a lower bound (`subtype` itself, below) or defaults at the
  end of checking (`Elaborator/Elaborator.lean`, not yet written). A bound can itself be a
  metavariable (`?m <: ?n`, both unresolved) — recorded here unchanged rather than merged with
  `?n`'s own identity, per `PLAN.md` §5.3's own justification for why merging the two would be
  unsound (`?m`'s and `?n`'s eventual solutions may legitimately diverge, only staying `<:`-related).
-/
structure PendingBounds : Type where
  private bounds : Std.HashMap MVarId (List Typ)

instance : EmptyCollection PendingBounds := ⟨⟨{}⟩⟩

/-- The pending-upper-bounds effect `subtype` needs on top of `MonadMetavarContext` — kept as its
own class (`Elaborator/Monad.lean`'s doc on `MonadMetavarContext` already points here) rather than
folded into that one, since it's tracking a different thing (bounds *not yet* resolved into a
value, not the value itself). -/
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

/-- `DOMAIN`/`Len`/`..`/`=`, referenced the same way every other builtin is in this project's
ASTs — `CoreTLAPlus.Expression.var`'s own doc: "(by canonical spelling, e.g. `"+"`, `"\\in"`,
`"DOMAIN"`) a builtin operator referenced as a value" — not invented for this file. -/
private def builtin (name : String) (τ : Typ) : Expr := .var name τ

/-- `Str <: Seq(Int)` (thesis Fig. 3.1.8's `STR-TO-SEQ`). The thesis has no term-level coercions
at all (module doc), so there is no prior semantics to match here — `"Str2Seq"` is a placeholder
builtin name pending `Elaborator/Declarations.lean`'s real bundled-stub operator table (§7, task
7), the same "the real vocabulary doesn't exist yet" situation `Elaborator/Errors.lean`'s
`TCError.todo` already documents for errors. -/
private def strToSeqCoercion (e : Expr) : Expr :=
  .opCall (builtin "Str2Seq" (.operator [.str] (.seq .int))) [e]

/-- `Seq(τ) <: Int → τ` (thesis Fig. 3.1.8's `SEQ-TO-FUN`) — `[i ∈ 1..Len(e) ↦ e[i]]`. `i` must
already be a fresh name (chosen by the caller, `Elaborator/Monad.lean`'s `MonadFresh`) — this
helper stays a pure `Expr → Expr` once that choice is made, matching `Coercion.fn`'s own shape. -/
private def seqToFunCoercion (τ : Typ) (i : String) (e : Expr) : Expr :=
  let range : Expr := .opCall (builtin ".." (.operator [.int, .int] (.set .int)))
    [.nat "1", .opCall (builtin "Len" (.operator [.seq τ] .int)) [e]]
  .fn i .int range (.fnCall e (.var i .int))

/-- `⟨τ,...,τ⟩ <: Seq(τ)` (thesis Fig. 3.1.8's `TUPLE-TO-SEQ`, uniform tuple only) — unlike the
other two non-structural axioms, needs no fresh name at all: a tuple's arity `n` is static (part
of its own type), so the result is just a literal `.seq` of the `n` projected, coerced
components. -/
private def tupleToSeqCoercion (n : Nat) (τ : Typ) (e : Expr) : Expr :=
  .seq ((List.range n).map λ i ↦ .fnCall e (.nat (toString (i + 1)))) τ

/-- `Set(τ) <: Set(τ')` (thesis Fig. 3.1.8's `SET`, module doc) — `{coerce(x) : x ∈ e}`. -/
private def setCoercion (x : String) (τ : Typ) (c : Coercion) (e : Expr) : Expr :=
  .map' (c.apply (.var x τ)) x τ e

/-- `⟨τ₁,...,τₙ⟩ <: ⟨τ₁',...,τₙ'⟩` (thesis Fig. 3.1.8's `TUPLE`, module doc) — a new literal tuple,
each component projected out of `e` (via `fnCall`, tuples being encoded as unary functions from
naturals, thesis p. 9) and coerced. -/
private def tupleCoercion (coes : List Coercion) (τs' : List Typ) (e : Expr) : Expr :=
  .tuple <| ((List.range coes.length).zip coes).zip τs' |>.map λ ((i, c), τ'ᵢ) ↦
    (τ'ᵢ, c.apply (.fnCall e (.nat (toString (i + 1)))))

/-- `[x₁:τ₁,...] <: [x₁:τ₁',...]` (thesis Fig. 3.1.8's `RECORD`, module doc) — a new literal
record, each field projected out of `e` (via `recordAccess`) and coerced. -/
private def recordCoercion (fields : List (String × Coercion × Typ)) (e : Expr) : Expr :=
  .record <| fields.map λ (name, c, τ'ᵢ) ↦ (τ'ᵢ, name, c.apply (.recordAccess e name))

/-- `τ₁ → τ₂ <: τ₁' → τ₂'` (thesis Fig. 3.1.8's `FUNCTION`, module doc's own long explanation of
why this needs the `CHOOSE`-based domain remap) — `[y ∈ {coerceDom(x) : x ∈ DOMAIN(f)} ↦
coerceRng(f[CHOOSE x ∈ DOMAIN(f) : coerceDom(x) = y])]`. -/
private def functionCoercion
    (x y : String) (dom rng dom' : Typ) (cDom cRng : Coercion) (f : Expr) : Expr :=
  let domainExpr : Expr := .opCall (builtin "DOMAIN" (.operator [.function dom rng] (.set dom))) [f]
  let newDomain : Expr := .map' (cDom.apply (.var x dom)) x dom domainExpr
  let eqTy : Typ := .operator [dom', dom'] .bool
  let recoveredArg : Expr :=
    .choose x dom (some domainExpr)
      (.opCall (builtin "=" eqTy) [cDom.apply (.var x dom), .var y dom'])
  .fn y dom' newDomain (cRng.apply (.fnCall f recoveredArg))

variable {m : Type → Type} [Monad m] [MonadMetavarContext Typ m] [MonadPendingBounds m]
  [MonadFresh m]

/-- Needed for `subtype`/`tryAxioms`'s own `partial def`s below to type-check at all (an arbitrary
`m` isn't otherwise known nonempty) — same fix prior art already uses for the same reason
(`TypedTLAPlus.Expression.traverse`'s own local `Inhabited (F (Expression α))` instance). -/
local instance : Inhabited (m SubtypeResult) := ⟨pure .failure⟩

/-- `subtype` applied pointwise across two equal-length lists (the `Tuple`/`Record`/`Operator`
structural rules below), short-circuiting on the first `pending`/`failure` and otherwise
collecting every component's coercion, in order. Structurally recursive on the list, so — unlike
`subtype` itself — this needs no `partial`. -/
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

/-- The three non-structural coercions (thesis Fig. 3.1.8's `STR-TO-SEQ`/`SEQ-TO-FUN`/
`TUPLE-TO-SEQ`) — tried once `subtype` itself finds no direct structural/reflexive match. Each
produces an intermediate type and an axiom coercion, then recurses on `(intermediate, τ')` via
`subtypeRec` (always `subtype` itself; passed in rather than called directly so this stays a
plain, non-mutually-recursive `def`) and composes — this is what realizes `<:`'s transitivity
(`PLAN.md` §5.3: "a genuine partial order... reflexive-transitive closure") without a separate
closure step: e.g. `Str <: Seq(Int) <: Int → Int` falls out of `STR-TO-SEQ` finding `Seq(Int)`,
recursing, and `SEQ-TO-FUN` firing in turn. Terminates because the three axioms are already known
acyclic (`PLAN.md` §5.3's partial-order argument) and each only ever fires once per chain. -/
private partial def tryAxioms (subtypeRec : Typ → Typ → m SubtypeResult) (τ τ' : Typ) :
    m SubtypeResult := do
  let chainWith (axiomCoe : Coercion) (mid : Typ) : m SubtypeResult := do
    match ← subtypeRec mid τ' with
    | .failure => return .failure
    | .pending n => return .pending n
    | .success .id => return .success axiomCoe
    | .success (.fn g) => return .success <| .fn λ e ↦ g (axiomCoe.apply e)
  match τ with
  | .str => chainWith (.fn strToSeqCoercion) (.seq .int)
  | .seq τ₀ => do
    let i ← freshName "i"
    chainWith (.fn (seqToFunCoercion τ₀ i)) (.function .int τ₀)
  | .tuple (τ₀ :: rest) =>
    if rest.all (· == τ₀) then
      chainWith (.fn (tupleToSeqCoercion (rest.length + 1) τ₀)) (.seq τ₀)
    else return .failure
  | _ => return .failure

/--
  The type checker's subtyping judgment (thesis Fig. 3.1.7's `SUBTYPE`/Fig. 3.1.8, `PLAN.md`
  §5.3) — see the module doc for `Coercion`'s own scope/limitations, and `tryAxioms`/each
  `*Coercion` helper above for the non-structural/structural cases respectively. Also implements
  the direction-aware metavariable-solving algorithm (`PLAN.md` §5.3) in the three `mvar` cases
  below, in place of the thesis's literal `Specialize` rule.

  `partial`: no structurally-decreasing measure across `tryAxioms`' recursive calls (its
  intermediate types can be *larger* than the input, e.g. `Str` to `Seq(Int)`), matching this
  project's existing convention for the same situation (`TypedTLAPlus.Expression.map`/`.traverse`).
-/
partial def subtype (τ τ' : Typ) : m SubtypeResult := do
  match τ, τ' with
  | .mvar a, .mvar b => do
    match ← assigned? a, ← assigned? b with
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
      return .success <| .fn (setCoercion x τ₀ c ·)
  | .seq τ₀, .seq τ₀' => do
    match ← subtype τ₀ τ₀' with
    | .success .id => return .success .id
    | .pending n => return .pending n
    | .failure | .success (.fn _) => return .failure
  | .channel τ₀, .channel τ₀' => return if τ₀ == τ₀' then .success .id else .failure
  | .tuple τs, .tuple τs' => do
    if τs.length ≠ τs'.length then return .failure
    else
      match ← subtypeAll subtype (τs.zip τs') with
      | .error r => return r
      | .ok coes =>
        if coes.all (· matches .id) then return .success .id
        else return .success <| .fn (tupleCoercion coes τs' ·)
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
          return .success <| .fn (recordCoercion fields ·)
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
          return .success <| .fn (functionCoercion x y dom rng dom' cDom cRng ·)
  | _, _ => tryAxioms subtype τ τ'

/-- Whether `τ <: τ'` holds, ignoring the coercion payload — all `lub`/`glb` need (`PLAN.md`
§5.3, thesis p. 13). -/
private def isSubtype (τ τ' : Typ) : m Bool := return (← subtype τ τ') matches .success _

/-- The least upper bound of two types under `<:`, where it exists — `<:` here is a genuine
partial order with no `⊤` (`PLAN.md` §5.3), so `lub` is a *partial* function: comparable types
have one (the wider of the two), incomparable ones don't. Used by the `ENUMERATION`/`Empty set`
checking rules (thesis Fig. 3.1.8's addendum, `Elaborator/Expressions.lean`, not yet written). -/
def lub (τ τ' : Typ) : m (Option Typ) := do
  if ← isSubtype τ τ' then return some τ'
  else if ← isSubtype τ' τ then return some τ
  else return none

/-- The greatest lower bound, dual to `lub`. -/
def glb (τ τ' : Typ) : m (Option Typ) := do
  if ← isSubtype τ τ' then return some τ
  else if ← isSubtype τ' τ then return some τ'
  else return none
