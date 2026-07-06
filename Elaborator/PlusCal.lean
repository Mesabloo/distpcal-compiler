import Elaborator.Declarations
import Core.TypedPlusCal.Syntax

/-!
  Statement/showable/process/algorithm checking (§5.3, thesis §3.1.5, Figs. 3.1.13–3.1.16):
  `checkStatement`/`checkBlock`/`checkBranches`/`checkPlusCalDeclarations`/`checkProcess`/
  `checkAlgorithm`, turning a `CorePlusCal.Algorithm (Option Typ) (CoreTLAPlus.Expression
  (Option Typ))` (the checker's actual PlusCal input, `α` still the optional, user-written
  `@type` annotation) into a `TypedPlusCal.Algorithm` (`Core/TypedPlusCal/Syntax.lean`'s own
  fresh AST, not an `abbrev` — see that file's module doc for why).

  **Two deliberate corrections to the thesis figures, both concrete necessities rather than
  style choices — flagged with the project owner before implementing either:**
  - **`[Multicast]`'s `e1` premise (Fig. 3.1.13) is checked against `Set(τ)`, not the literal
    `τ` the figure renders.** The figure's own accompanying prose gives multicast's desugared
    semantics as `x := [y ∈ DOMAIN x ↦ IF y ∈ e1 THEN Append(x[y], e2) ELSE x[y]]` — `y ∈ e1` is
    a set-membership test, which only type-checks if `e1 : Set(τ)`. Checked directly against the
    PDF page image (not just extracted text) to rule out an extraction artifact — the figure
    really does render a bare `τ`, not `Set(τ)`, so this is treated as a transcription error in
    the source thesis, not a deliberate design choice to preserve.
  - **Algorithm-level `variables` (`Algorithm.globalState.variables`) are checked, even though
    Fig. 3.1.16's `[Algorithm]` rule only mentions `fifos`.** The rule is silent on plain global
    `variables` entirely (unlike `[Process]`, Fig. 3.1.15, which does cover a process's own
    `localState.variables`) — but `CorePlusCal.Algorithm.globalState : Declarations`
    structurally allows real PlusCal syntax to populate them (`algorithm Foo { variables x = 0;
    fifos ...; process ... }`), so this is treated as the figure omitting a case it didn't
    anticipate, not excluding it. Checked the same way `[Process]`'s own local variables are
    (`checkVariables` below, shared by both).

  **A free implementation choice, not a spec question:** a `with`-bound variable's/PlusCal
  `variables` entry's/multicast bind's optional annotation (`ann`, a `with`/`variables`
  declaration's own `@type`) is neither required nor even mentioned by Figs. 3.1.13/3.1.15's
  `[With-eq]`/`[With-in]`/`[Process]` rules (the bound type is always fully determined by the
  initializer alone) — checked against it when present, otherwise inferred, exactly
  `Elaborator/Expressions.lean`'s own record-literal-field convention (`inferExpr`'s `.record`
  case). Neither reading contradicts the thesis; this project's own annotation infrastructure
  just makes the annotated form available too.

  **`[Receive]`'s own deviation is `PLAN.md` §5.3/§9.15's, not a new one here** — see
  `Core/TypedPlusCal/Syntax.lean`'s module doc for why `receive` needed a fresh AST rather than
  reusing `CorePlusCal.Statement` at `α := Typ`/`β := Expr` the way every other constructor does.

  **`[Goto]` performs no type check at all** (thesis, Fig. 3.1.13) — label existence is the
  well-formedness pass's job (§5.2a, sequenced after this one, §7), not this file's.

  **A `receive`/`send`'s channel reference, and a `with`/`variables` entry's Ref-typed
  destination, are checked via `inferRef` below, not `Elaborator/Expressions.lean`'s
  `inferExpr`/`checkExpr`** — `CorePlusCal.Ref` (`name`, indexed by a flat `List β`, one entry
  per bracket group, already pre-tupled multi-index — that file's own doc) is a distinct type
  from `CoreTLAPlus.Expression`, not a wrapper around one, so it needs its own small synthesis
  judgment: a `Γ`-lookup on `name` followed by `Elaborator/Expressions.lean`'s own `indexInto`
  (reused directly, not reimplemented) once per bracket group.

  **A channel/FIFO declaration's Γ-binding domain follows `Elaborator/Declarations.lean`'s own
  `n = 1`/`n > 1` reconciliation for function definitions, for the same underlying reason**
  (`CorePlusCal.Ref`'s "multi-index calls are pre-tupled, multi-argument definitions aren't"
  note): Fig. 3.1.16's `[Channel declaration]` rule always shows the *general*, already-tupled
  `⟨Address,...,Address⟩ → Channel(τ)` domain, but a real channel access via `Ref` collapses a
  multi-argument index the same way `CoreTLAPlus.Expression.fnCall` does — so `m = 1` binds a
  channel's own Γ-type at plain `Address → Channel(τ)` (matching a single-index `Ref` access
  directly), while `m > 1` needs the tupled `⟨Address,...⟩ → Channel(τ)` domain the figure
  literally shows.
-/

open TypedTLAPlus (Typ Coercion)

/-- The checker's actual PlusCal input: `CorePlusCal.*` at `α := Option Typ` (a `with`-bound
variable's/`variables` entry's optional `@type`) and `β := SrcExpr` (`Elaborator/
Expressions.lean`'s own convention, reused directly). -/
abbrev SrcRef := CorePlusCal.Ref SrcExpr
abbrev SrcStatement (b : Bool) := CorePlusCal.Statement (Option Typ) SrcExpr b
abbrev SrcBlock (b : Bool) := CorePlusCal.Block (Option Typ) SrcExpr b
abbrev SrcBranches (b : Bool) := CorePlusCal.Branches (Option Typ) SrcExpr b
abbrev SrcDeclarations := CorePlusCal.Declarations (Option Typ) SrcExpr
abbrev SrcProcess := CorePlusCal.Process (Option Typ) SrcExpr
abbrev SrcAlgorithm := CorePlusCal.Algorithm (Option Typ) SrcExpr
abbrev SrcMulticastFilter := SurfacePlusCal.MulticastFilter (Option Typ) SrcExpr

/-- The `showable` predicate (thesis Fig. 3.1.14, module doc's own note on `[Print]`): `Int`/
`Bool`/`Str`/`Address` atomic; `Function`/`Set`/`Seq`/`Tuple`/`Record` recursively, exactly as the
figure shows (a `Function` — an ordinary TLA⁺ function/finite map — *is* showable when both its
domain and range are, unlike an `Operator`/`Channel`, neither of which the figure lists at all —
those, and anything containing them, are simply not showable). `partial`: nested `List`
recursion (`Tuple`/`Record`'s components/fields), same caveat as `SurfaceTLAPlus.Typ`'s own
`DecidableEq` instance. -/
partial def showable : Typ → Bool
  | .bool | .int | .str | .address => true
  | .function dom rng => showable dom && showable rng
  | .set τ | .seq τ => showable τ
  | .tuple τs => τs.all showable
  | .record fs => fs.all (showable ∘ Prod.snd)
  | .operator .. | .channel .. | .var _ | .const _ | .mvar _ => false

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- `Elaborator/Expressions.lean`'s `checkExpr`, closed out via `resolveMVars` immediately —
matches `Elaborator/Declarations.lean`'s identical per-produced-expression discipline (`PLAN.md`
§5.3's single end-of-check defaulting point: a metavariable `specializeOperator` freshens while
checking one statement/declaration entry must not leak, still unresolved, into the next one's `Γ`). -/
private def checkExprR (e : SrcExpr) (τ : Typ) : m TypedPlusCal.Expression := do
  resolveMVars (← checkExpr e τ)

/-- `inferExpr`, closed out via `resolveMVars` the same way `checkExprR` is. -/
private def inferExprR (e : SrcExpr) : m (Typ × TypedPlusCal.Expression) := do
  let (τ, e') ← inferExpr e
  return (τ, ← resolveMVars e')

/-- Needed for the `partial def`s below to type-check at all (module doc's own convention,
`Elaborator/Expressions.lean`/`Subtyping.lean`'s identical fix for the same reason). -/
local instance {b} : Inhabited (m (TypedPlusCal.Statement b)) := ⟨pure default⟩
local instance {b} : Inhabited (m (TypedPlusCal.Block b)) := ⟨pure default⟩
local instance {b} : Inhabited (m (TypedPlusCal.Branches b)) := ⟨pure default⟩

/-- Synthesize a `Ref`'s type (module doc): a `Γ`-lookup on `name`, then `Elaborator/
Expressions.lean`'s own `indexInto` once per bracket group. `pos` is borrowed from the enclosing
statement — a `Ref` carries no position of its own (`Core/CorePlusCal/Syntax.lean`'s `Ref` has no
`@@`-tagged field), matching `SourceSpan.placeholder`'s own reasoning for declaration entries. -/
private def inferRef (pos : SourceSpan) (r : SrcRef) : m (Typ × TypedPlusCal.Ref) := do
  match (← readThe Context).get? r.name with
  | none => throw (.unboundVariable pos r.name)
  | some τ₀ => do
    let (τ, args') ← r.args.foldlM (init := (τ₀, ([] : List TypedPlusCal.Expression)))
      λ (τ, acc) idx ↦ do
        let (τ', idx') ← indexInto pos τ idx
        let idx' ← resolveMVars idx'
        return (τ', acc ++ [idx'])
    return (τ, { name := r.name, args := args' })

/-- One `Declarations.variables` entry, checked (module doc's own note on the optional-
annotation convention, and on why `[Process]`'s local variables and `Algorithm.globalState`'s
global ones share this one helper): absent initializer, the annotation is mandatory (nothing
else could pin the type down); `=`-initialized, infer/check the value directly; `∈`-initialized,
infer/check against `Set(ann)` and take the element type. -/
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

/-- `∀ 1≤i≤m, Γ,[self:Address]⊢eᵢ⇑τᵢ` (thesis Figs. 3.1.9/3.1.15) over a whole `variables` list —
each subsequent entry's initializer sees every earlier one already bound (matching real PlusCal's
own sequential-initializer semantics, and `Elaborator/Declarations.lean`'s identical threading
for TLA⁺-level `VARIABLES`/operator parameters). -/
private def checkVariables :
    List (String × Option Typ × Bool × Option (Bool × SrcExpr)) →
      m (List (String × Typ × Bool × Option (Bool × TypedPlusCal.Expression)) × List (String × Typ))
  | [] => return ([], [])
  | (x, ann, isParam, init) :: rest => do
    let (τ, entry) ← checkVariable x ann isParam init
    let (rest', bindings) ← extend x τ (checkVariables rest)
    return (entry :: rest', (x, τ) :: bindings)

/-- `[Channel declaration]` (thesis Fig. 3.1.16), one entry: every index set checks against
`Set(Address)` (independent of the annotation's own shape); the Γ-binding is simply whatever the
mandatory `@type` annotation itself already says (no rule ever synthesizes it) — a plain
`Channel(τ)` for a bare, unindexed channel (`fifos ping : Channel(τ);`, no brackets at all; not
covered by Fig. 3.1.16's own always-indexed notation, but a real, common surface form
`CorePlusCal.Declarations.channels`/`fifos`' own `List β` genuinely allows), or `dom → Channel(τ)`
for an indexed one (`Address → Channel(τ)`/`⟨Address,...⟩ → Channel(τ)`, matching Fig. 3.1.16's own
notation for `m = 1`/`m > 1`). Returns the full Γ-binding type alongside the checked *element*
type (what `TypedPlusCal.Declarations` itself stores, `Core/TypedPlusCal/Syntax.lean`'s doc) and
the checked index sets.

**The annotation *is* the full Γ-binding type, not just the bare element type — this project's own
existing `channels`/`fifos` fixtures (`tests/regression/`) already confirm this,** both for
unindexed channels (`(* @type: Channel(Str); *)`) and indexed ones (`PingPongs.tla`'s `(* @type:
Address -> Channel(Str); *) pong[Pongs]` — the *whole* function type, not just `Channel(Str)`).
An earlier version of this function *reconstructed* the Γ-binding type from `idxSets.length`
instead of trusting the annotation directly, which double-wrapped every unindexed channel
(`Channel(Channel(τ))`) and rejected every indexed one outright — both found via hand-verification
against `PingPongs.tla`/`TPC2.tla`. -/
private def checkChannelDecl (x : String) (ann : Option Typ) (idxSets : List SrcExpr) :
    m (Typ × Typ × List TypedPlusCal.Expression) := do
  let bindTy ← requireAnnotation SourceSpan.placeholder s!"channel `{x}`" ann
  let elemTy ← match bindTy with
    | .channel τ => pure τ
    | .function _ (.channel τ) => pure τ
    | _ => throw (.notAChannelType SourceSpan.placeholder bindTy)
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
`localState` (module doc's note on why the global-`variables` case is covered at all): `variables`
first, then `channels`/`fifos` (both `[Channel declaration]`-checked identically — `Core/
CorePlusCal/Syntax.lean`'s own doc on why they're two separate lists is a backend/desugaring
distinction, not a typing one), each stage's bindings in scope for the next. -/
def checkPlusCalDeclarations (decls : SrcDeclarations) : m (TypedPlusCal.Declarations × List (String × Typ)) := do
  let (vars', varBindings) ← checkVariables decls.variables
  extendAll varBindings do
    let (channels', chBindings) ← checkChannelDecls decls.channels
    extendAll chBindings do
      let (fifos', fifoBindings) ← checkChannelDecls decls.fifos
      return ({ «variables» := vars', channels := channels', fifos := fifos' },
        varBindings ++ chBindings ++ fifoBindings)

/-- One `MulticastFilter.binds` entry, checked against the channel's own declared domain type
`domTy` (module doc's own note on the generalization beyond the thesis's single-bind figure):
an `=`-bind is a plain, `domTy`-independent let (infer/check its own value); an `∈`-bind is
checked against `Set(domTy)` — the one case Fig. 3.1.13's `[Multicast]` literally shows — taking
`domTy` itself as the bound variable's type. -/
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
  /-- `Γ|Ξ⊩S ok` (thesis Fig. 3.1.13) — see the module doc for the two corrections
  (`[Multicast]`'s `Set(τ)` fix) and reused pieces (`inferRef`) applied throughout. Genuinely a
  *transform*, not the thesis's pure `ok`-judgment (`Core/TypedPlusCal/Syntax.lean`'s own module
  doc): every embedded `CoreTLAPlus.Expression`/`Ref` becomes a checked `TypedPlusCal.Expression`/
  `Ref`, and `receive` additionally gains its `Coercion`.

  `partial`: no structurally-decreasing measure across the mutual group visible to Lean (`Block`'s
  `begin : List (Statement _ _ false)` field, same caveat `CorePlusCal.Statement.bimap`'s own doc
  already notes for this exact family). -/
  partial def checkStatement {b} (s : SrcStatement b) : m (TypedPlusCal.Statement b) := match_source s with
    /-
      ─────────────── [Goto]
       Γ|Ξ⊩ goto l ok
      (no type check — label existence is the well-formedness pass's job, module doc.)
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
      (`ann`, module doc's own free choice — checked against if present, else inferred as here.)
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
      (`PLAN.md` §5.3/§9.15's own deliberate deviation from the literal figure, module doc:
      synthesize *both* sides and `subtype` the two element types directly, storing the result on
      the node — `Channel <:` is reflexivity-only here, `Elaborator/Subtyping.lean`'s own note, so
      checking `c` against `Channel(τr)` the figure's literal way can't produce a real upcast.)
    -/
    | .receive c r, pos => do
      let (cTy, c') ← inferRef pos c
      match cTy with
      | .channel elemTy => do
        let (refTy, r') ← inferRef pos r
        match ← subtype elemTy refTy with
        | .failure => throw (.failedToConvertTypes pos refTy elemTy)
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
      (`Set(τ)` on `e1`, module doc's own correction; generalized to a whole bind list the same
      way `EXCEPT`'s path walk generalizes beyond a one-step figure, `Elaborator/Expressions.lean`.)
    -/
    | .multicast x filter, pos => do
      match (← readThe Context).get? x with
      | none => throw (.unboundVariable pos x)
      | some (.function domTy (.channel elemTy)) => do
        let (binds', bindings) ← checkMulticastBinds domTy filter.binds
        let val' ← extendAll bindings (checkExprR filter.val elemTy)
        return .multicast x { binds := binds', val := val' } @@ pos
      | some got => throw (.notAChannelType pos got)

  /-- `Γ|Ξ⊩B ok` for atomic blocks (thesis §3.1.5's own remark: produces no type information,
  same as statements) — check every non-terminal statement, then the terminal one. -/
  partial def checkBlock {b} (blk : SrcBlock b) : m (TypedPlusCal.Block b) := do
    let begin' ← blk.begin.mapM checkStatement
    let end' ← checkStatement blk.end
    return .mk begin' end'

  /-- `either`'s own branch list, checked pointwise — no dedicated rule beyond `[Either]`
  reusing `Γ|Ξ⊩B ok` per branch (thesis Fig. 3.1.13). -/
  partial def checkBranches {b} : SrcBranches b → m (TypedPlusCal.Branches b)
    | .either blk => return .either (← checkBlock blk)
    | .or blk rest => return .or (← checkBlock blk) (← checkBranches rest)
end

/--
  `Γ|Ξ⊩ p∈S ⋆ x1=e1;...;xm=em ⋆ T1...Tn ok` (thesis Fig. 3.1.15's `[Process]`): `S` must be
  `Set(Address)`, checked *without* `self` in scope (Fig. 3.1.15's own premise, `Γ⊢S⇓Set(Address)`
  — no `self` on that `Γ`); everything else about a process — `mailbox`, local variables, and
  every thread — is checked with `self:Address` already in scope (`checkPlusCalDeclarations`,
  shared with the algorithm-level case, for local variables; local bindings additionally in
  scope for the threads). `mailbox`'s own filter/index expressions (this project's own extension,
  no thesis rule) are simply inferred, unconstrained — elaborating them into real
  `TypedPlusCal.Expression`s is a structural requirement of the output type, not a typing
  judgment the thesis specifies, but they still need `self` (`@mailbox: agt[self];` is the
  standard idiom, confirmed via hand-verification against `TPC2.tla` — an earlier version of
  this function checked `mailbox` *before* extending `Γ` with `self`, rejecting exactly this).

  **`process (p = e)` checks `e` against `Address` directly, not `Set(Address)`.** Fig. 3.1.15
  only ever shows the `∈`-form's rule, per its own prose: "process (x = e) can be seen as
  process (x ∈ {e})" — taken literally, that would check `e` against `Address` then re-run the
  *same* `Set(Address)` rule against the singleton `{e}`, but that's just a roundabout way of
  saying `e : Address` directly (checking `{e} : Set(Address)` reduces to exactly that once `{e}`
  is expanded), so this dispatches on `proc.«=|∈»` instead of literally constructing `{e}`.
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

/--
  `Γ|Ξ⊩ fifos c1:τ1,...,cm:τm; P1∥...∥Pn ok` (thesis Fig. 3.1.16's `[Algorithm]`): every channel
  declaration checked (`checkPlusCalDeclarations`, module doc — also covers `globalState.variables`,
  the algorithm-level correction noted at the top of this file), then every process checked
  against `Γ` extended by those bindings. Those bindings stay scoped to the algorithm itself —
  PlusCal declarations don't leak into the surrounding TLA⁺ module's own `Γ` (confirmed with the
  project owner), so nothing here is exposed to `Elaborator/Elaborator.lean`'s `declarations₂`. -/
def checkAlgorithm (algo : SrcAlgorithm) : m TypedPlusCal.Algorithm := do
  let (globalState', bindings) ← checkPlusCalDeclarations algo.globalState
  let processes' ← extendAll bindings (algo.processes.mapM checkProcess)
  return {
    isFair := algo.isFair
    name := algo.name
    globalState := globalState'
    processes := processes'
  } @@ posOf algo
