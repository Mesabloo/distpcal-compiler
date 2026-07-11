import Elaborator.Declarations
import Core.TypedPlusCal.Syntax

/-!
  Statement/showable/process/algorithm checking: `checkStatement`/`checkBlock`/`checkBranches`/
  `checkPlusCalDeclarations`/`checkProcess`/`checkAlgorithm`, turning a `CorePlusCal.Algorithm
  (Option Typ) (CoreTLAPlus.Expression (Option Typ))` (`α` still the optional, user-written
  `@type` annotation) into a `TypedPlusCal.Algorithm`.

  A few notable points:
  - `[Multicast]`'s `e1` premise is checked against `Set(τ)`: multicast's desugared semantics
    tests `y ∈ e1`, which only type-checks if `e1 : Set(τ)`.
  - Algorithm-level `variables` (`Algorithm.globalState.variables`) are checked the same way a
    process's own local variables are (`checkVariables` below, shared by both).
  - A `with`-bound variable's/PlusCal `variables` entry's/multicast bind's optional annotation is
    checked against when present, otherwise inferred from the initializer.
  - `[Goto]` performs no type check at all — label existence is the well-formedness pass's job.
  - A `receive`/`send`'s channel reference, and a `with`/`variables` entry's Ref-typed
    destination, are checked via `inferRef` below, not `Elaborator/Expressions.lean`'s
    `inferExpr`/`checkExpr` — `CorePlusCal.Ref` is a distinct type from `CoreTLAPlus.Expression`,
    so it needs its own small synthesis judgment: a `Γ`-lookup on `name` followed by
    `Elaborator/Expressions.lean`'s own `indexInto` once per bracket group.
  - A channel/FIFO declaration's Γ-binding domain follows the same `n = 1`/`n > 1` reconciliation
    as function definitions (`Elaborator/Declarations.lean`): `m = 1` binds a channel's own
    Γ-type at plain `Address → Channel(τ)`; `m > 1` needs the tupled
    `⟨Address,...⟩ → Channel(τ)` domain.
-/

open TypedTLAPlus (Typ Coercion)

/-- The checker's actual PlusCal input: `CorePlusCal.*` at `α := Option Typ` (a `with`-bound
variable's/`variables` entry's optional `@type`) and `β := SrcExpr`. -/
abbrev SrcRef := CorePlusCal.Ref SrcExpr
abbrev SrcStatement (b : Bool) := CorePlusCal.Statement (Option Typ) SrcExpr b
abbrev SrcBlock (b : Bool) := CorePlusCal.Block (Option Typ) SrcExpr b
abbrev SrcBranches (b : Bool) := CorePlusCal.Branches (Option Typ) SrcExpr b
abbrev SrcDeclarations := CorePlusCal.Declarations (Option Typ) SrcExpr
abbrev SrcProcess := CorePlusCal.Process (Option Typ) SrcExpr
abbrev SrcAlgorithm := CorePlusCal.Algorithm (Option Typ) SrcExpr
abbrev SrcMulticastFilter := SurfacePlusCal.MulticastFilter (Option Typ) SrcExpr

/-- The `showable` predicate, used by `print`: `Int`/`Bool`/`Str`/`Address` atomic;
`Function`/`Set`/`Seq`/`Tuple`/`Record` recursively (a `Function` is showable when both its
domain and range are). `Operator`/`Channel`/`Const`/rigid type variables, and anything containing
them, are not showable. Pure and non-monadic — **callers must resolve `τ`'s metavariables first**
(`resolveTypeMVarsForDisplay`, at the point of use, not here) so `.mvar _ => false` only ever
fires on a genuinely still-unresolved metavariable, not one that's already been pinned to
something showable. `partial`: nested `List` recursion over `Tuple`/`Record`'s components/fields
isn't visibly structurally decreasing to Lean. -/
partial def showable : Typ → Bool
  | .bool | .int | .str | .address => true
  | .function dom rng => showable dom && showable rng
  | .set τ | .seq τ => showable τ
  | .tuple τs => τs.all showable
  | .record fs => fs.all (showable ∘ Prod.snd)
  | .operator .. | .channel .. | .var _ | .const _ | .mvar _ => false

/-- The `sendable` predicate, used by a channel's own declared element type
(`checkChannelDecl`): the same restriction as `showable` (a `CONSTANT` isn't sendable either,
even though it's just an opaque value at this point — the project owner's own concern: a
`CONSTANT` gets substituted by the user *after* code generation, and an unsendable
instantiation would silently break this invariant once compiled), currently identical in shape
but named and defined separately since the two represent distinct restrictions that only
happen to coincide today, not the same rule reused. Same non-monadic, resolve-first contract as
`showable`. -/
partial def sendable : Typ → Bool
  | .bool | .int | .str | .address => true
  | .function dom rng => sendable dom && sendable rng
  | .set τ | .seq τ => sendable τ
  | .tuple τs => τs.all sendable
  | .record fs => fs.all (sendable ∘ Prod.snd)
  | .operator .. | .channel .. | .var _ | .const _ | .mvar _ => false

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- `Elaborator/Expressions.lean`'s `checkExpr`, closed out via `resolveMVars` immediately, so a
metavariable freshened while checking one statement doesn't leak unresolved into the next. -/
private def checkExprR (e : SrcExpr) (τ : Typ) : m TypedPlusCal.Expression := do
  resolveMVars (← checkExpr e τ)

/-- `inferExpr`, closed out via `resolveMVars` the same way `checkExprR` is. -/
private def inferExprR (e : SrcExpr) : m (Typ × TypedPlusCal.Expression) := do
  let (τ, e') ← inferExpr e
  return (τ, ← resolveMVars e')

/-- Needed for the `partial def`s below to type-check at all (an arbitrary `m` isn't otherwise
known nonempty). -/
local instance {b} : Inhabited (m (TypedPlusCal.Statement b)) := ⟨pure default⟩
local instance {b} : Inhabited (m (TypedPlusCal.Block b)) := ⟨pure default⟩
local instance {b} : Inhabited (m (TypedPlusCal.Branches b)) := ⟨pure default⟩

/-- Synthesize a `Ref`'s type: a `Γ`-lookup on `name`, then `Elaborator/Expressions.lean`'s own
`indexInto` once per bracket group. `pos` is borrowed from the enclosing statement — a `Ref`
carries no position of its own. -/
private def inferRef (pos : SourceSpan) (r : SrcRef) : m (Typ × TypedPlusCal.Ref) := do
  match (← readThe Context).get? r.name with
  | none => throw (.unboundVariable pos r.name)
  | some { type := τ₀, .. } => do
    let (τ, args') ← r.args.foldlM (init := (τ₀, ([] : List TypedPlusCal.Expression)))
      λ (τ, acc) idx ↦ do
        let (τ', idx') ← indexInto pos τ idx
        let idx' ← resolveMVars idx'
        return (τ', acc ++ [idx'])
    return (τ, { name := r.name, args := args', type := τ })

/-- One `Declarations.variables` entry, checked: absent initializer, the annotation is mandatory
(nothing else could pin the type down); `=`-initialized, infer/check the value directly;
`∈`-initialized, infer/check against `Set(ann)` and take the element type. -/
private def checkVariable (x : String) (ann : Option Typ) (isParam : Bool)
    (init : Option (Bool × SrcExpr)) :
    m (Typ × (String × Typ × Bool × Option (Bool × TypedPlusCal.Expression))) := do
  match init with
  | none => do
    let τ ← requireAnnotation SourceSpan.placeholder s!"variable `{x}`" ann
    return (τ, x, τ, isParam, none)
  | some (true, e) => do
    let (τ, e') ← match ann with
      | some τ => pure (τ, ← checkExprR e τ)
      | none => inferExprR e
    return (τ, x, τ, isParam, some (true, e'))
  | some (false, e) => do
    let (τ, e') ← match ann with
      | some τ => pure (τ, ← checkExprR e (.set τ))
      | none => do
        let (setTy, e') ← inferExprR e
        match setTy with
        | .set τ => pure (τ, e')
        | _ => throw (.notASetType SourceSpan.placeholder setTy)
    return (τ, x, τ, isParam, some (false, e'))

/-- `∀ 1≤i≤m, Γ,[self:Address]⊢eᵢ⇑τᵢ` over a whole `variables` list — each subsequent entry's
initializer sees every earlier one already bound, matching real PlusCal's sequential-initializer
semantics. -/
private def checkVariables :
    List (String × Option Typ × Bool × Option (Bool × SrcExpr)) →
      m (List (String × Typ × Bool × Option (Bool × TypedPlusCal.Expression)) × List (String × Typ))
  | [] => return ([], [])
  | (x, ann, isParam, init) :: rest => do
    let (τ, entry) ← checkVariable x ann isParam init
    let (rest', bindings) ← extend x τ (checkVariables rest)
    return (entry :: rest', (x, τ) :: bindings)

/-- One channel declaration entry: every index set checks against `Set(Address)`; the Γ-binding
is simply whatever the mandatory `@type` annotation itself already says (no rule ever synthesizes
it) — a plain `Channel(τ)` for a bare, unindexed channel, or `dom → Channel(τ)` for an indexed
one. Returns the full Γ-binding type alongside the checked *element* type and the checked index
sets.

The annotation *is* the full Γ-binding type, not just the bare element type — do not reconstruct
it from `idxSets.length` instead, which would double-wrap unindexed channels and reject indexed
ones. -/
private def checkChannelDecl (x : String) (ann : Option Typ) (idxSets : List SrcExpr) :
    m (Typ × Typ × List TypedPlusCal.Expression) := do
  let bindTy ← requireAnnotation SourceSpan.placeholder s!"channel `{x}`" ann
  let elemTy ← match bindTy with
    | .channel τ => pure τ
    | .function _ (.channel τ) => pure τ
    | _ => throw (.notAChannelType SourceSpan.placeholder bindTy)
  -- `elemTy` comes straight from the user's own `@type` annotation, never from unification, so
  -- it can never contain a `Typ.mvar` — no resolution step needed before testing `sendable`,
  -- unlike `showable`'s call site (`print`, above), which checks an *inferred* type.
  unless sendable elemTy do throw (.notSendable SourceSpan.placeholder elemTy)
  let idxSets' ← idxSets.mapM (checkExprR · (.set .address))
  return (bindTy, elemTy, idxSets')

/-- `checkChannelDecl` over a whole `channels`/`fifos` list, threaded the same way
`checkVariables` is. -/
private def checkChannelDecls :
    List (String × Option Typ × List SrcExpr) →
      m (List (String × Typ × List TypedPlusCal.Expression) × List (String × Typ))
  | [] => return ([], [])
  | (x, ann, idxs) :: rest => do
    let (bindTy, elemTy, idxs') ← checkChannelDecl x ann idxs
    let (rest', bindings) ← extend x bindTy (checkChannelDecls rest)
    return ((x, elemTy, idxs') :: rest', (x, bindTy) :: bindings)

/-- `Declarations` checking, shared by both `Algorithm.globalState` and a `Process`'s own
`localState`: `variables` first, then `channels`/`fifos`, each stage's bindings in scope for the
next. -/
def checkPlusCalDeclarations (decls : SrcDeclarations) : m (TypedPlusCal.Declarations × List (String × Typ)) := do
  let (vars', varBindings) ← checkVariables decls.variables
  extendAll varBindings do
    let (channels', chBindings) ← checkChannelDecls decls.channels
    extendAll chBindings do
      let (fifos', fifoBindings) ← checkChannelDecls decls.fifos
      return ({ «variables» := vars', channels := channels', fifos := fifos' },
        varBindings ++ chBindings ++ fifoBindings)

/-- One `MulticastFilter.binds` entry, checked against the channel's own declared domain type
`domTy`: an `=`-bind is a plain, `domTy`-independent let (infer/check its own value); an
`∈`-bind is checked against `Set(domTy)`, taking `domTy` itself as the bound variable's type. -/
private def checkMulticastBind (domTy : Typ) (x : String) (ann : Option Typ) (isEq : Bool)
    (e : SrcExpr) : m (Typ × (String × Typ × Bool × TypedPlusCal.Expression)) := do
  if isEq then do
    let (τ, e') ← match ann with
      | some τ => pure (τ, ← checkExprR e τ)
      | none => inferExprR e
    return (τ, x, τ, true, e')
  else do
    let e' ← checkExprR e (.set domTy)
    return (domTy, x, domTy, false, e')

/-- `checkMulticastBind` over the whole bind list, threaded the same way `checkVariables` is. -/
private def checkMulticastBinds (domTy : Typ) :
    List (String × Option Typ × Bool × SrcExpr) →
      m (List (String × Typ × Bool × TypedPlusCal.Expression) × List (String × Typ))
  | [] => return ([], [])
  | (x, ann, isEq, e) :: rest => do
    let (τ, entry) ← checkMulticastBind domTy x ann isEq e
    let (rest', bindings) ← extend x τ (checkMulticastBinds domTy rest)
    return (entry :: rest', (x, τ) :: bindings)

mutual
  /-- `Γ|Ξ⊩S ok` — a transform, not a pure `ok`-judgment: every embedded
  `CoreTLAPlus.Expression`/`Ref` becomes a checked `TypedPlusCal.Expression`/`Ref`, and `receive`
  additionally gains its `Coercion`.

  `partial`: no structurally-decreasing measure across the mutual group visible to Lean
  (`Block`'s `begin : List (Statement _ _ false)` field). -/
  partial def checkStatement {b} (s : SrcStatement b) : m (TypedPlusCal.Statement b) := match_source s with
    /-
      ─────────────── [Goto]
       Γ|Ξ⊩ goto l ok
      (no type check — label existence is the well-formedness pass's job.)
    -/
    | .goto l, pos => return .goto l @@ pos
    /-
      ─────────── [Skip]
       Γ|Ξ⊩ skip ok
    -/
    | .skip, pos => return .skip @@ pos
    /-
       Γ|Ξ⊢e⇑τ       τ is showable
      ───────────────────────────── [Print]
             Γ|Ξ⊩ print e ok
    -/
    | .print e, pos => do
      let (τ, e') ← inferExprR e
      -- `τ` isn't necessarily stored anywhere inside `e'` (many expression shapes carry no own
      -- type at all), so `resolveMVars e'`'s traversal above may not have touched it: resolve it
      -- separately before testing `showable`, so an already-pinned metavariable is checked
      -- against its real type instead of unconditionally failing as `.mvar _`.
      let τ ← resolveTypeMVarsForDisplay τ
      if showable τ then return .print e' @@ pos
      else throw (.notShowable pos τ)
    /-
       ∀ (r,e), Γ|Ξ⊢r⇑τ       Γ|Ξ⊢e⇓τ
      ─────────────────────────────────── [Assign]
              Γ|Ξ⊩ r:=e ok
    -/
    | .assign asss, pos => do
      let asss' ← asss.mapM λ (r, e) ↦ do
        let (τ, r') ← inferRef pos r
        return (r', ← checkExprR e τ)
      return .assign asss' @@ pos
    /-
       Γ|Ξ⊢e⇓Bool       Γ|Ξ⊩B₁ ok       Γ|Ξ⊩B₂ ok
      ──────────────────────────────────────────── [If]
                Γ|Ξ⊩ if e then B₁ else B₂ ok
    -/
    | .if e B₁ B₂, pos => do
      let e' ← checkExprR e .bool
      let B₁' ← checkBlock B₁
      let B₂' ← checkBlock B₂
      return .if e' B₁' B₂' @@ pos
    /-
       Γ|Ξ⊢e⇓Bool
      ────────────────── [Await]
       Γ|Ξ⊩ await e ok
    -/
    | .await e, pos => return .await (← checkExprR e .bool) @@ pos
    /-
       Γ|Ξ⊢e⇑τ       Γ,x:τ|Ξ⊩B ok
      ───────────────────────────── [With-eq]
       Γ|Ξ⊩ with x=e do B ok
      (`ann` checked against if present, else inferred as here.)
    -/
    | .with x ann true val B, pos => do
      let (τ, val') ← match ann with
        | some τ => pure (τ, ← checkExprR val τ)
        | none => inferExprR val
      let B' ← extend x τ (checkBlock B)
      return .with x τ true val' B' @@ pos
    /-
       Γ|Ξ⊢e⇑Set(τ)       Γ,x:τ|Ξ⊩B ok
      ───────────────────────────────── [With-in]
       Γ|Ξ⊩ with x∈e do B ok
    -/
    | .with x ann false val B, pos => do
      let (τ, val') ← match ann with
        | some τ => pure (τ, ← checkExprR val (.set τ))
        | none => do
          let (setTy, val') ← inferExprR val
          match setTy with
          | .set τ => pure (τ, val')
          | _ => throw (.notASetType pos setTy)
      let B' ← extend x τ (checkBlock B)
      return .with x τ false val' B' @@ pos
    /-
       Γ|Ξ⊢e⇓Bool
      ────────────────── [Assert]
       Γ|Ξ⊩ assert e ok
    -/
    | .assert e, pos => return .assert (← checkExprR e .bool) @@ pos
    /-
       ∀ 1≤i≤n, Γ|Ξ⊩Bᵢ ok
      ──────────────────────────────────── [Either]
       Γ|Ξ⊩ either B₁ or ... or Bₙ ok
    -/
    | .either branches, pos => return .either (← checkBranches branches) @@ pos
    /-
       Γ|Ξ⊢e⇓Bool       Γ|Ξ⊩B ok
      ──────────────────────────── [While]
       Γ|Ξ⊩ while e do B ok
    -/
    | .while e B, pos => do
      let e' ← checkExprR e .bool
      let B' ← checkBlock B
      return .while e' B' @@ pos
    /-
       Γ|Ξ⊢c⇑Channel(τc)       Γ|Ξ⊢r⇑τr
      ──────────────────────────────────── [Receive]
                Γ|Ξ⊩ receive(c,r) ok
      (Synthesizes *both* sides and `subtype`s the two element types directly, storing the
      result on the node — `Channel <:` is reflexivity-only, so checking `c` against
      `Channel(τr)` directly can't produce a real upcast.)
    -/
    | .receive c r, pos => do
      let (cTy, c') ← inferRef pos c
      match cTy with
      | .channel elemTy => do
        let (refTy, r') ← inferRef pos r
        match ← subtype elemTy refTy with
        | .failure => throw (.failedToConvertTypes pos (← resolveTypeMVarsForDisplay refTy) (← resolveTypeMVarsForDisplay elemTy))
        | .success coe => return .receive c' r' coe @@ pos
        | .pending _ => throw (.todo pos
            "unreachable: a channel/reference's declared type can never contain an unresolved metavariable")
      | _ => throw (.notAChannelType pos cTy)
    /-
       Γ|Ξ⊢c⇑Channel(τ)       Γ|Ξ⊢e⇓τ
      ──────────────────────────────── [Send]
             Γ|Ξ⊩ send(c,e) ok
    -/
    | .send c e, pos => do
      let (cTy, c') ← inferRef pos c
      match cTy with
      | .channel τ => return .send c' (← checkExprR e τ) @@ pos
      | _ => throw (.notAChannelType pos cTy)
    /-
       x:τ→Channel(τ')∈Γ       Γ|Ξ⊢e1⇓Set(τ)       Γ,y:τ|Ξ⊢e2⇓τ'
      ──────────────────────────────────────────────────────────── [Multicast]
                    Γ|Ξ⊩ multicast(x,[y∈e1↦e2]) ok
      (`Set(τ)` on `e1`; generalized to a whole bind list rather than a single one.)
    -/
    | .multicast x filter, pos => do
      match (← readThe Context).get? x with
      | none => throw (.unboundVariable pos x)
      | some { type := .function domTy (.channel elemTy), .. } => do
        let (binds', bindings) ← checkMulticastBinds domTy filter.binds
        let val' ← extendAll bindings (checkExprR filter.val elemTy)
        return .multicast x { binds := binds', val := val' } @@ pos
      | some got => throw (.notAChannelType pos got.type)

  /-- `Γ|Ξ⊩B ok` for atomic blocks — check every non-terminal statement, then the terminal one. -/
  partial def checkBlock {b} (blk : SrcBlock b) : m (TypedPlusCal.Block b) := do
    let begin' ← blk.begin.mapM checkStatement
    let end' ← checkStatement blk.end
    return .mk begin' end'

  /-- `either`'s own branch list, checked pointwise — no dedicated rule beyond `[Either]`
  reusing `Γ|Ξ⊩B ok` per branch. -/
  partial def checkBranches {b} : SrcBranches b → m (TypedPlusCal.Branches b)
    | .either blk => return .either (← checkBlock blk)
    | .or blk rest => return .or (← checkBlock blk) (← checkBranches rest)
end

/--
  `Γ|Ξ⊩ p∈S ⋆ x1=e1;...;xm=em ⋆ T1...Tn ok`: `S` must be `Set(Address)`, checked *without* `self`
  in scope; everything else about a process — `mailbox`, local variables, and every thread — is
  checked with `self:Address` already in scope. `mailbox`'s own filter/index expressions are
  simply inferred, unconstrained, but still need `self` in scope (`@mailbox: agt[self];` is the
  standard idiom).

  `process (p = e)` checks `e` against `Address` directly, not `Set(Address)` (dispatches on
  `proc.«=|∈»` rather than constructing a singleton set `{e}` and checking that).
-/
def checkProcess (proc : SrcProcess) : m TypedPlusCal.Process := do
  let id' ← if proc.«=|∈» then checkExprR proc.id .address else checkExprR proc.id (.set .address)
  extend "self" .address do
    let mailbox' ← proc.mailbox.mapM λ (name, args) ↦ do
      let args' ← args.mapM λ e ↦ do
        let (_, e') ← inferExprR e
        return e'
      return (name, args')
    let (localState', bindings) ← checkPlusCalDeclarations proc.localState
    let threads' ← extendAll bindings
      (proc.threads.mapM (·.mapM (λ (l, blk) ↦ return (l, ← checkBlock blk))))
    return {
      mailbox := mailbox'
      isFair := proc.isFair
      name := proc.name
      «=|∈» := proc.«=|∈»
      id := id'
      localState := localState'
      threads := threads'
    } @@ posOf proc

/-- `Γ|Ξ⊩ fifos c1:τ1,...,cm:τm; P1∥...∥Pn ok`: every channel declaration checked (also covers
`globalState.variables`), then every process checked against `Γ` extended by those bindings.
Those bindings stay scoped to the algorithm itself — PlusCal declarations don't leak into the
surrounding TLA⁺ module's own `Γ`. -/
def checkAlgorithm (algo : SrcAlgorithm) : m TypedPlusCal.Algorithm := do
  let (globalState', bindings) ← checkPlusCalDeclarations algo.globalState
  let processes' ← extendAll bindings (algo.processes.mapM checkProcess)
  return {
    isFair := algo.isFair
    name := algo.name
    globalState := globalState'
    processes := processes'
  } @@ posOf algo
