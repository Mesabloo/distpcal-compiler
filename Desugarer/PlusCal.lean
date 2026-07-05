import Desugarer.Errors
import Core.SurfacePlusCal.Syntax
import Core.CorePlusCal.Syntax
import Desugarer.TLAPlus
import Parser_.Annotations

/-!
  Statement desugaring: `SurfacePlusCal`'s implicit-fallthrough statement lists become
  `CorePlusCal`'s explicit-`goto`, type-indexed-terminal `Block`s (§5.2). Written from scratch —
  prior art's `Desugarer/PlusCal.lean` is an empty stub in every branch (`PLAN.md` §3.2/§5.2).

  Mostly structural: by the time this runs, `Module.desugar` (`Desugarer/TLAPlus.lean`) has
  already desugared every embedded `β`-typed expression to `CoreTLAPlus.Expression`, so the
  goto-explicitization machinery below never needs to recurse into expressions at all. The one
  exception is `Process.desugar`/`Algorithm.desugar` themselves, which — per the project owner's
  choice to fuse annotation checking into statement desugaring rather than keep a second,
  separately-named "raw, still-generic" `CorePlusCal`-shaped type around just to bridge the gap
  between structural desugaring and annotation checking (`Core/CorePlusCal/Syntax.lean`'s module
  doc) — also validate and strip every `Process`/`Declarations`-level annotation (`@mailbox`,
  `@type`, `@parameter`) down to its content right here, including running full expression
  desugaring (`SurfaceTLAPlus.Expression.desugar`, via a throwaway local monad instantiation,
  `desugarMailboxArg` below) over a `@mailbox`'s filter arguments — those were never desugared at
  all before this (`Module.desugar`'s own traversal treats annotations as opaque, untouched
  payload), a real, previously-latent gap that only became visible once `CorePlusCal.Process`
  gained a genuine `mailbox : Option (String × List β)` field that these arguments have to
  actually inhabit.

  **Labels may appear inside `if`/`while`/`either` bodies, not just at a thread's top level** —
  confirmed by the project owner with a worked example (a `while` loop with a labelled step
  inside its body) after an earlier draft of this module wrongly rejected exactly that as
  unsupported. A label anywhere marks the start of a new addressable atomic block, so any label
  found nested inside a control-flow body has to be *extracted* into its own top-level
  `(label, Block)` entry, with explicit `goto`s inserted to stitch control flow back together —
  this is genuine basic-block extraction, not a special case:

  - `while (cond) { S; l: T }` (a labelled step inside a loop body) becomes: the `while`
    statement's own body ends in `goto l` instead of falling through; `l`'s extracted content
    (`T`) ends in `goto` back to the label that owns the *whole* `while` statement (re-checking
    `cond` is exactly re-entering that label) — reusing that label directly when the `while` is
    the first thing under it, or synthesizing a fresh "loop" label otherwise (e.g. if some other
    statement runs once before the loop starts).
  - `if (cond) { l: S } else { T }` (only one branch has a nested label) similarly needs a
    continuation label for "whatever comes after the whole `if`" — *both* branches redirect to
    it, since `CorePlusCal.Statement.if`'s two branches must share one terminality.
  - `either`'s branches are handled the same way as `if`'s, generalized to *n* branches.
  - **`with` is the one genuine exception**: real PlusCal doesn't allow labels, `goto`, or
    `while` inside a `with` body at all, at any nesting depth (it introduces a binding that only
    makes sense within one atomic step) — its body is always desugared via the cheap,
    no-extraction path below, and a nested label (`nestedLabel`) or `while` (`whileInWith`)
    found there is a hard error, not something to extract.

  A `goto` may still only appear as the last statement of the list it's *directly* embedded in —
  `goto` immediately followed by *more, unlabelled* statements is unreachable dead code, not
  something to route around (this restriction is unaffected by the correction above: `goto`
  immediately followed by a *label* is exactly the normal "block ends here" case).

  **A `while` must always be immediately preceded by a real, user-written label — and this
  compiler does not auto-insert one if it's missing.** Confirmed against the PlusCal manual
  (§3.2.4/§3.7: "A while statement must be labeled", unconditionally, unlike `if`/`either`, which
  only need a label *after* them and only when they themselves contain something requiring one)
  and independently by the thesis's own `𝒞_cflow` rewrite rule (`PLAN.md` §5.4), whose pattern
  `while e {B1}; B2; goto l'` *at label `l`* already assumes the `while` starts the block it's
  found in. **Corrected after an earlier draft got this wrong**, per the project owner: real
  PlusCal's *default* translator behavior (no `-label` flag) rejects an unlabelled `while` rather
  than inventing a label for it — that auto-insertion is what the *opt-in* `-label` flag does, not
  the default, and this compiler matches the default, not `-label`. The same correction applies to
  `if`/`either`'s own "must be followed by a label" requirement (§3.2.2/§3.2.3): a missing
  continuation label is rejected (`notFollowedByLabel`), not synthesized. `desugarSegment`'s
  `while` case checks whether the current segment is empty and has a real label to attribute the
  `while` to (`acc.isEmpty ∧ ownLabel.isSome`) and throws `whileNotLabelled` if not, rather than
  minting a fresh "loop" label as an earlier draft did; `desugarContinuation` throws
  `notFollowedByLabel` when what follows a label/`goto`-containing `if`/`either` isn't itself
  already labelled, rather than minting a fresh "cont" label. `List.needsExtraction` reflects this
  too: *any* `while` found anywhere inside a nested `if`/`either`/`while` body forces the
  extraction-capable path (not just one found away from that list's own first element, since
  position within a brace-delimited branch was never actually the same thing as "immediately
  preceded by a label" — a real bug in the same earlier draft, found together with the
  auto-insertion mistake above) so `desugarSegment` gets the chance to check it's properly
  labelled and reject it if not, rather than silently folding it into a bigger atomic step via the
  flat `desugarLabelFreeBlock` path.

  **Thread termination:** if a thread's last label runs out of statements without an explicit
  terminal, `goto Done` is inserted automatically — `"Done"` is a reserved sentinel that never
  needs a matching label definition (confirmed with the project owner; standard PlusCal's
  official translator convention, though its exact interaction with this project's
  multi-threaded-per-process extension isn't documented anywhere found during research — worth
  flagging to whoever implements well-labelledness checking, §5.2a, since `"Done"` must stay
  exempt from "every `goto` targets a real label").

  **`ownLabel`/`fallthrough` and `WithContext`'s with-bound-variable list are `Reader` effects
  (`SegmentContext`/`WithContext` below), not manually-threaded parameters** — following
  `Desugarer/Monad.lean`'s
  `MonadDesugarerExpr` precedent (a `Reader` of "what `@` currently refers to", `CLAUDE.md`'s
  monad-polymorphism convention applied literally). Both genuinely are "ambient, locally
  overridable context" rather than data being built up: every recursive call that doesn't change
  them inherits the current value for free (no `ownLabel fallthrough` passed at every call site
  the way an untracked value would need to be), and every call that *does* change them
  (`.inl`'s new label, `.while`'s loop body, `.if`/`.either`'s branches, `with`'s own body) uses
  `withTheReader` to override just for that sub-computation. `acc` — the segment's own accumulated
  non-terminal statements — stays an explicit fold parameter rather than `MonadState`: unlike the
  two `Reader`s, it isn't ambient context inherited by unrelated sub-computations, it *is* the
  value being computed by this specific recursive walk, and it resets to `[]` at points that
  don't line up with either `Reader`'s own scoping (e.g. `.while`'s "reuse this label" case
  starts a fresh `acc` while *keeping* the same `ownLabel`) — modeling that as `MonadState` would
  need as much manual save/restore around each reset as a plain parameter already gets for free.
-/

namespace SurfacePlusCal
  /-- The reader context `Statement.desugarLabelFree` and friends thread through their
  recursion: which variable names, if any, are currently bound by an enclosing `with`
  (innermost binding first, but order is never actually relied upon — membership is all that
  matters). Propagated unchanged through `if`/`either`'s own sub-bodies (both remain legal
  inside `with`); each `with`'s own recursive call prepends its own bound names on top of
  whatever's already there, so nested `with`s accumulate rather than replace. "Are we
  (transitively) inside a `with` body at all?" is just `boundVars.isEmpty`, used by the `while`
  check below exactly as before; "is `name` specifically with-bound?" is `boundVars.contains`,
  used by the write check below (`withBoundVarWritten`) — a `with`-bound name is a local
  binding to a fixed value, not a process variable, so writing to it (via `assign` or
  `receive`) is meaningless. -/
  structure WithContext where
    boundVars : List String := []

  /-- The reader context `desugarSegment` threads through its recursion: which label (if any)
  "owns" the segment currently being built (`none` for an `if`/`either` branch, which has no
  address of its own), and where to `goto` if this segment runs out of statements without an
  explicit redirect. -/
  structure SegmentContext where
    ownLabel : Option String
    fallthrough : String
    deriving Inhabited

  variable {α β : Type} {m : Type → Type} [Monad m] [MonadExceptOf DesugarError m]
    [MonadStateOf (List DesugarWarning) m]
    [MonadReaderOf WithContext m] [MonadWithReaderOf WithContext m]
    [MonadReaderOf SegmentContext m] [MonadWithReaderOf SegmentContext m]

  /-- The reserved sentinel `goto` target meaning "this thread has terminated" — never needs a
  matching label. -/
  def doneLabel : String := "Done"

  /-- The one concrete expression type every function below that touches a `Ref`'s own indices
  (`Statement.desugarLabelFree`, `desugarSegment`, `Thread.desugar`) is fixed at, same as
  `Process.desugar`/`Algorithm.desugar` already are — needed to call `SurfaceTLAPlus.
  wrapIndices` (`x[e₁, …, eₙ] := v` collapsing to `x[<<e₁, …, eₙ>>] := v`, `Ref.desugarRef`
  below), which is itself only meaningful once `β` is concretely `CoreTLAPlus.Expression`. -/
  private abbrev CoreExpr := CoreTLAPlus.Expression (List Annotation)

  /-- `x[e₁, …, eₙ]`'s indices, per bracket group, collapsed to `CorePlusCal.Ref`'s own unary
  shape (`Core/CorePlusCal/Syntax.lean`'s module doc) via `SurfaceTLAPlus.wrapIndices` — same
  rule as `fnCall`/`except`. `pos` is the *enclosing statement*'s own position (matching
  `withBoundVarWritten`'s existing precedent just below, rather than trying to recover a
  `Ref`'s own position). -/
  def Ref.desugarRef (pos : SourceSpan) (r : SurfacePlusCal.Ref CoreExpr) : CorePlusCal.Ref CoreExpr :=
    { name := r.name, args := r.args.map (SurfaceTLAPlus.wrapIndices pos) }

  mutual
    /--
      Does this statement, anywhere within it (at any nesting depth), need the expensive,
      extraction-capable desugaring path (`desugarSegment`) rather than the cheap
      always-non-terminal one (`desugarLabelFreeBlock`)? Three independent reasons force this,
      all checked recursively through every `if`/`while`/`either` sub-body: a label anywhere
      (needing extraction into its own top-level block), an `if`/`either` branch or `while` body
      whose own last statement is a bare `goto` (which cannot be embedded non-terminally at all —
      `goto` only exists as `Statement α β true`), or a `while` anywhere at all. A bare `goto`
      here, by itself, is *not* flagged (`false`) — what matters is whether it ends up as some
      list's own last element, which `List.needsExtraction` below checks directly; a `with` body
      never needs extraction (real PlusCal disallows labels/`goto`/`while` there entirely,
      `rejectLabels`/`whileInWith`).
    -/
    partial def Statement.needsExtraction : Statement α β → Bool
      | .if _ b1 b2 => b1.needsExtraction || (b2.map (·.needsExtraction)).getD false
      | .either bs => bs.any (·.needsExtraction)
      | .while _ b => b.needsExtraction
      | .with .. | .skip | .goto _ | .print _ | .assign _ | .await _ | .assert _
      | .receive .. | .send .. | .multicast .. => false

    /--
      `List.needsExtraction` (declared at the root `List` namespace, not nested here, so plain
      dot-notation on a `List (String ⊕ Statement α β)` value resolves to it): `true` as soon as
      a label is found anywhere, its own last element is a bare `goto`, any statement in it
      (`Statement.needsExtraction`) does, or a `while` appears *anywhere* in the list.

      That last case is a real, independent restriction, not just "a `while` away from this
      list's own first element" (an earlier draft's mistake, found and corrected alongside the
      auto-insertion mistake described in this file's module doc): being first inside a
      brace-delimited `if`/`either` branch is not the same thing as being immediately preceded by
      an actual label, so *every* `while` found here — wherever it sits — has to go through
      `desugarSegment`, which is the only place that can actually check whether it's properly
      labelled and reject it (`whileNotLabelled`) if not. `desugarLabelFreeBlock`'s flat path has
      no such check and must never be handed a list containing one.
    -/
    partial def _root_.List.needsExtraction : List (String ⊕ Statement α β) → Bool
      | [] => false
      | .inl _ :: _ => true
      | .inr (.while ..) :: _ => true
      | .inr s :: rest =>
        (match s, rest with
          | .goto _, [] => true
          | _, _ => false)
        || s.needsExtraction
        || rest.needsExtraction
  end

  /-- Reject any statement-list entry that is a label — used for `with` bodies, the one
  construct real PlusCal never allows a label inside. -/
  def rejectLabels : List (String ⊕ Statement α β) → m (List (Statement α β))
    | [] => pure []
    | .inl l :: _ => throw (.nestedLabel (posOf l))
    | .inr s :: rest => (s :: ·) <$> rejectLabels rest

  /-- Flatten a multi-binder `with (x = e, y ∈ S, …) { … }` into a nested chain of single-binder
  `CorePlusCal.Statement.with`s (`with (x = e) { with (y ∈ S) { … } }`) — `CorePlusCal.Statement.
  with` only ever binds one variable at a time (`Core/CorePlusCal/Syntax.lean`'s module doc), so
  every binder past the first gets wrapped in its own label-free `Block` (`⟨[], ·⟩`, no leading
  statements of its own) around the next binder in the chain, with `B` — the already-desugared
  original body — as the innermost one's. -/
  def buildWithChain (vars : List (String × α × Bool × β)) (B : CorePlusCal.Block α β false) :
      CorePlusCal.Statement α β false :=
    match vars with
    | [] => unreachable! -- `with` always binds at least one variable, by construction of the parser (`sepBy1`)
    | [(x, ann, eq, e)] => .with x ann eq e B
    | (x, ann, eq, e) :: rest => .with x ann eq e ⟨[], buildWithChain rest B⟩

  mutual
    /--
      Desugar a statement known to *not* be the last of its enclosing sequence and known
      (by `needsExtraction`) to need no extraction anywhere inside it: always yields a
      non-terminal (`false`) `CorePlusCal.Statement`, with `if`/`while`/`either`'s own
      sub-blocks recursing via `desugarLabelFreeBlock` (still extraction-free, by the same
      assumption).

      Reads `WithContext` to tell which names, if any, are currently `with`-bound — inherited
      as-is through `if`/`either`'s own sub-bodies (both are legal inside `with`), extended only
      by `with`'s own recursive call via `withTheReader`. A `while` is rejected outright the
      moment it's seen with any names currently bound (`boundVars` non-empty): unlike a nested
      label (also illegal inside `with`, `rejectLabels`), a `while` needs no label of its own
      nearby to be illegal here — the manual (§3.2.6) lists it as its own, unconditional
      restriction (`whileInWith`). An `assign` targeting a currently-`with`-bound name, or a
      `receive` whose target `Ref` is one, is likewise rejected outright (`withBoundVarWritten`)
      — a `with`-bound name is a local binding to a fixed value, not a process variable with
      state to update, and `receive` writes into its target the same way `assign` does.
    -/
    partial def Statement.desugarLabelFree (s : Statement α CoreExpr) : m (CorePlusCal.Statement α CoreExpr false) := match_source s with
      | .goto _, pos => throw (.gotoNotInTailPosition pos)
      | .skip, _ => pure .skip
      | .print e, _ => pure (.print e)
      | .assign a, pos => do
        let ctx ← readThe WithContext
        match a.find? (λ (r, _) ↦ ctx.boundVars.contains r.name) with
        | some (r, _) => throw (.withBoundVarWritten pos r.name)
        | none => pure (.assign (a.map λ (r, e) ↦ (Ref.desugarRef pos r, e)))
      | .if cond b1 b2, _ => .if cond <$> desugarLabelFreeBlock b1 <*> desugarLabelFreeBlock (b2.getD [])
      | .await e, _ => pure (.await e)
      | .with vars b, _ =>
        let newNames := vars.map (·.1)
        buildWithChain vars <$> withTheReader WithContext ({ boundVars := newNames ++ ·.boundVars }) (desugarLabelFreeBlock b)
      | .assert e, _ => pure (.assert e)
      | .either branches, _ => .either <$> Branches.desugarLabelFree branches
      | .while cond b, pos => do
        let ctx ← readThe WithContext
        if !ctx.boundVars.isEmpty then throw (.whileInWith pos)
        else .while cond <$> desugarLabelFreeBlock b
      | .receive c r, pos => do
        let ctx ← readThe WithContext
        if ctx.boundVars.contains r.name then throw (.withBoundVarWritten pos r.name)
        else pure (.receive (Ref.desugarRef pos c) (Ref.desugarRef pos r))
      | .send c e, pos => pure (.send (Ref.desugarRef pos c) e)
      | .multicast c f, _ => pure (.multicast c f)

    /-- Desugar a statement-list known to be entirely label-free into a non-terminal block:
    every entry desugars via `Statement.desugarLabelFree`, except the last, whose own natural
    terminality (a bare `goto`, or an `if`/`either` that recursively is) is preserved. -/
    partial def desugarLabelFreeBlock (stmts : List (String ⊕ Statement α CoreExpr)) :
        m (CorePlusCal.Block α CoreExpr false) := do
      go (← rejectLabels stmts)
    where
      go : List (Statement α CoreExpr) → m (CorePlusCal.Block α CoreExpr false)
        | [] => pure ⟨[], .skip⟩
        | [s] => match_source s with
          | .goto _, pos => throw (.gotoNotInTailPosition pos)
          | _, _ => (⟨[], ·⟩) <$> Statement.desugarLabelFree s
        | s :: rest => do
          let s' ← Statement.desugarLabelFree s
          let block ← go rest
          pure ⟨s' :: block.begin, block.end⟩

    partial def Branches.desugarLabelFree (branches : List (List (String ⊕ Statement α CoreExpr))) :
        m (CorePlusCal.Branches α CoreExpr false) := match branches with
      | [] => unreachable! -- `either` always has ≥2 branches, by construction of the parser
      | [b] => .either <$> desugarLabelFreeBlock b
      | b :: bs => .or <$> desugarLabelFreeBlock b <*> Branches.desugarLabelFree bs
  end

  /-- Turn a list of desugared branch-blocks into `CorePlusCal.Branches`. -/
  def buildBranches : List (CorePlusCal.Block α β true) → CorePlusCal.Branches α β true
    | [] => unreachable!
    | [b] => .either b
    | b :: bs => .or b (buildBranches bs)

  /--
    Desugar `stmts` — the content directly following a label, per the ambient `SegmentContext`'s
    `ownLabel` (if this call is processing exactly that; `none` if it's an `if`/`either` branch,
    which has no address of its own) — into the terminal `CorePlusCal.Block` for *this* segment,
    plus every `(label, Block)` pair extracted from labels found nested within it
    (`if`/`while`/`either` bodies). `SegmentContext.fallthrough` is where to implicitly `goto` if
    this segment (or its last extracted continuation) runs out of statements without an explicit
    redirect.

    `acc` accumulates this segment's own non-terminal statements so far, in order — kept as an
    explicit parameter rather than folded into the `Reader` context (this file's module doc).
  -/
  partial def desugarSegment (acc : List (CorePlusCal.Statement α CoreExpr false)) :
      List (String ⊕ Statement α CoreExpr) → m (CorePlusCal.Block α CoreExpr true × List (String × CorePlusCal.Block α CoreExpr true))
    | [] => do
      let ctx ← readThe SegmentContext
      pure (⟨acc, .goto ctx.fallthrough⟩, [])
    | .inl nextLabel :: rest => do
      let ctx ← readThe SegmentContext
      let (nextBlock, extracted) ←
        withTheReader SegmentContext (λ _ ↦ { ctx with ownLabel := some nextLabel }) (desugarSegment [] rest)
      pure (⟨acc, .goto nextLabel⟩, (nextLabel, nextBlock) :: extracted)
    | .inr s :: rest => match_source s with
      | .goto l, _ => match rest with
        | [] => pure (⟨acc, .goto l⟩, [])
        | .inl nextLabel :: rest' => do
          let ctx ← readThe SegmentContext
          let (nextBlock, extracted) ←
            withTheReader SegmentContext (λ _ ↦ { ctx with ownLabel := some nextLabel }) (desugarSegment [] rest')
          pure (⟨acc, .goto l⟩, (nextLabel, nextBlock) :: extracted)
        | .inr s' :: _ => throw (.gotoNotInTailPosition (posOf s'))
      -- A `while` must always be immediately preceded by a real, user-written label —
      -- confirmed both by the PlusCal manual (§3.2.4/§3.7, "A while statement must be labeled",
      -- unconditionally) and by the thesis's own `𝒞_cflow` rewrite rule (`PLAN.md` §5.4), whose
      -- pattern `while e {B1}; B2; goto l'` *at label `l`* already assumes the `while` starts the
      -- block. Unlike a nested label/`goto` (genuinely extracted, since the user *did* write
      -- something to hang a block on), there is nothing to extract here if `acc` is non-empty or
      -- there's no real label to attribute the `while` to (`ownLabel = none`, e.g. inside an
      -- `if`/`either` branch) — this compiler does not invent a label the user didn't write, per
      -- the project owner (real PlusCal's own default, non-`-label` behavior rejects this too).
      | .while cond body, pos => do
        let ctx ← readThe SegmentContext
        if hAcc : acc.isEmpty ∧ ctx.ownLabel.isSome then
          let loopLabel := ctx.ownLabel.get hAcc.2
          if !body.needsExtraction then do
            let bodyBlock ← desugarLabelFreeBlock body
            desugarSegment [.while cond bodyBlock] rest
          else do
            let (bodyBlock, ex) ←
              withTheReader SegmentContext (λ _ ↦ { ownLabel := some loopLabel, fallthrough := loopLabel })
                (desugarSegment [] body)
            let (result, ex') ← desugarSegment [.while cond bodyBlock] rest
            pure (result, ex ++ ex')
        else throw (.whileNotLabelled pos)
      | .if cond b1 b2, _ =>
        let b2 := b2.getD []
        if !b1.needsExtraction && !b2.needsExtraction then do
          let block1 ← desugarLabelFreeBlock b1
          let block2 ← desugarLabelFreeBlock b2
          desugarSegment (acc ++ [.if cond block1 block2]) rest
        else do
          let (cont, contResult) ← desugarContinuation rest
          let branchCtx : SegmentContext := { ownLabel := none, fallthrough := cont }
          let (block1, ex1) ← withTheReader SegmentContext (λ _ ↦ branchCtx) (desugarSegment [] b1)
          let (block2, ex2) ← withTheReader SegmentContext (λ _ ↦ branchCtx) (desugarSegment [] b2)
          pure (⟨acc, .if cond block1 block2⟩, ex1 ++ ex2 ++ contResult)
      | .either branches, _ =>
        if !branches.any (·.needsExtraction) then do
          let block ← Branches.desugarLabelFree branches
          desugarSegment (acc ++ [.either block]) rest
        else do
          let (cont, contResult) ← desugarContinuation rest
          let branchCtx : SegmentContext := { ownLabel := none, fallthrough := cont }
          let results ← branches.mapM (withTheReader SegmentContext (λ _ ↦ branchCtx) <| desugarSegment [] ·)
          pure (⟨acc, .either (buildBranches (results.map Prod.fst))⟩, results.flatMap Prod.snd ++ contResult)
      | _, _ => do
        let s' ← Statement.desugarLabelFree s
        desugarSegment (acc ++ [s']) rest
  where
    /-- The continuation label for "whatever comes after a control-flow statement that needed
    extraction", plus its own extracted content (hoisted alongside everything else): the next
    real label if `rest` starts with one, the ambient `SegmentContext.fallthrough` if `rest` is
    empty, or a hard error (`notFollowedByLabel`) otherwise — this compiler does not invent a
    continuation label the user didn't write, matching real PlusCal's own default (non-`-label`)
    behavior for "an `if`/`either` containing a label or `goto` must be followed by a labelled
    statement" (§3.2.2/§3.2.3). -/
    desugarContinuation :
        List (String ⊕ Statement α CoreExpr) → m (String × List (String × CorePlusCal.Block α CoreExpr true))
      | [] => do
        let ctx ← readThe SegmentContext
        pure (ctx.fallthrough, [])
      | .inl nextLabel :: rest' => do
        let (nextBlock, ex) ←
          withTheReader SegmentContext ({ · with ownLabel := some nextLabel }) (desugarSegment [] rest')
        pure (nextLabel, (nextLabel, nextBlock) :: ex)
      | .inr s :: _ => throw (.notFollowedByLabel (posOf s))

  /-- Desugar one parallel thread (`{...}` block) into its sequence of labelled, terminal
  `CorePlusCal.Block`s — the thread's own top-level labels plus everything extracted from
  nested labels within `if`/`while`/`either` bodies. -/
  def Thread.desugar : List (String ⊕ Statement α CoreExpr) → m (List (String × CorePlusCal.Block α CoreExpr true))
    | [] => pure []
    | .inr s :: _ => throw (.unlabelledStatement (posOf s))
    | .inl firstLabel :: rest => do
      let (block, extracted) ←
        withTheReader SegmentContext (λ _ ↦ { ownLabel := some firstLabel, fallthrough := doneLabel }) (desugarSegment [] rest)
      pure ((firstLabel, block) :: extracted)

  /-- Run `SurfaceTLAPlus.Expression.desugar` against a single, self-contained expression,
  discarding the fresh-name counter — the same concrete instantiation `SurfaceTLAPlus.Module.
  runDesugarer` (`Desugarer/TLAPlus.lean`) uses, just scoped to one expression rather than a
  whole module. Needed for `@mailbox`'s filter arguments (`extractMailbox` below), which
  `Module.desugar`'s own traversal never reaches (annotations are opaque payload there). -/
  private def desugarMailboxArg (e : SurfaceTLAPlus.Expression (List Annotation)) :
      Except DesugarError (CoreTLAPlus.Expression (List Annotation)) :=
    let d : ReaderT (Option (CoreTLAPlus.Expression (List Annotation))) (StateT Nat (Except DesugarError)) _ := e.desugar
    (d.run none).run' 0

  /-- Validate and extract a `Process.ann` slot: at most one `@mailbox`, nothing else
  (`DesugarError.wrongAnnotationKindAtSite`/`duplicateAnnotation`, compared by channel name only
  — same reasoning as the old `checkMailboxOnly`), with its filter arguments fully desugared
  (`desugarMailboxArg`) rather than left as raw, never-consumed `SurfaceTLAPlus.Expression`s. -/
  def extractMailbox {m : Type → Type} [Monad m] [MonadExceptOf DesugarError m]
      (anns : List Annotation) : m (Option (String × List (CoreTLAPlus.Expression (List Annotation)))) := do
    let mut mailbox : Option (String × List (SurfaceTLAPlus.Expression (List Annotation))) := none
    for ann in anns do
      match ann with
      | .«@mailbox» pos name args =>
        match mailbox with
        | some (name', _) => unless name == name' do throw (.duplicateAnnotation pos "@mailbox")
        | none => mailbox := some (name, args)
      | _ => throw (.wrongAnnotationKindAtSite ann.posOf ann.name "@mailbox")
    match mailbox with
    | none => return none
    | some (name, args) => match args.mapM desugarMailboxArg with
      | .error e => throw e
      | .ok args' => return some (name, args')

  /-- Validate `@parameter`'s placement (only on a `∈`-initialized entry) and extract its
  *presence* into the dedicated `isParameter` field — a repeated `@parameter` is a warning,
  not an error, since it's content-free (nothing for two instances to disagree about). Leaves
  every other annotation (in practice, at most one `@type`) untouched in `α`, for the later,
  uniform `stripEmbeddedTypeAnnotations` to validate/extract exactly like any other `@type`-
  only slot — `Declarations` shares that same `α` with `Statement`/`MulticastFilter`
  (`Core/CorePlusCal/Syntax.lean`'s module doc), so there is no need to duplicate `@type`'s own
  duplicate-detection here. `channels`/`fifos` never allow `@parameter` at all, so they pass
  through unexamined — `stripEmbeddedTypeAnnotations` alone is enough to reject one that
  sneaks in. -/
  def Declarations.desugarCheck {β : Type} {m : Type → Type} [Monad m] [MonadExceptOf DesugarError m]
      [MonadStateOf (List DesugarWarning) m]
      (decls : Declarations (List Annotation) β) : m (CorePlusCal.Declarations (List Annotation) β) := do
    let «variables» ← decls.variables.mapM λ (x, anns, init) ↦ do
      -- `init`'s `Bool` is `true` for `=`, `false` for `∈` (`Declarations.variables`'s own doc
      -- comment) — `@parameter` only makes sense on a `∈`-initialized variable, matching
      -- `TPC2.tla`'s `aState ∈ {"accept","refuse"}` example.
      let allowParameter := match init with
        | some (false, _) => true
        | _ => false
      let mut seenParameter := false
      let mut rest : List Annotation := []
      for ann in anns do
        match ann with
        | .«@parameter» pos =>
          unless allowParameter do throw (.wrongAnnotationKindAtSite pos "@parameter" "@type")
          if seenParameter then modify (DesugarWarning.duplicateParameterAnnotation pos :: ·)
          seenParameter := true
        | other => rest := other :: rest
      return (x, rest.reverse, seenParameter, init)
    return { «variables», channels := decls.channels, fifos := decls.fifos }

  /-- Desugar one process: goto-explicitize its threads (`Thread.desugar`) and, fused in
  alongside that, validate/extract its `@mailbox` annotation (`extractMailbox`) and its local
  declarations' `@parameter` annotations (`Declarations.desugarCheck`). -/
  def Process.desugar (p : Process (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
      m (CorePlusCal.Process (List Annotation) (CoreTLAPlus.Expression (List Annotation))) := do
    let mailbox ← extractMailbox p.ann
    let localState ← p.localState.desugarCheck
    (CorePlusCal.Process.mk mailbox p.isFair p.name p.«=|∈» p.id localState ·)
      <$> traverse Thread.desugar p.threads

  /-- Desugar a whole algorithm: its global declarations (`Declarations.desugarCheck`) and
  every process (`Process.desugar`). -/
  def Algorithm.desugar (a : Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
      m (CorePlusCal.Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) := do
    let globalState ← a.globalState.desugarCheck
    (CorePlusCal.Algorithm.mk a.isFair a.name globalState ·) <$> traverse Process.desugar a.processes

end SurfacePlusCal

/-- If `r` is a *bare* reference (`r.args` empty — `x`, never `x[…]`), record it as a write
against `seen`, throwing `DesugarError.conflictingAssignment` if it's already there; an indexed
reference is never tracked at all (`DesugarError.conflictingAssignment`'s own doc comment). -/
private def checkWrite {β} {m : Type → Type} [Monad m] [MonadExceptOf DesugarError m]
    (seen : List String) (r : CorePlusCal.Ref β) (pos : SourceSpan) : m (List String) :=
  if r.args.isEmpty then
    if seen.contains r.name then throw (.conflictingAssignment pos r.name)
    else pure (r.name :: seen)
  else pure seen

/-!
  `PLAN.md` §5.2a's well-labelledness bullet, "no two assignments to the same variable within
  one atomic step, on the same control path" — checked early here (against `CorePlusCal`,
  right after statement desugaring) rather than deferred to the eventual `WellFormedness`
  pass, matching how the sibling `with`-bound-write-rejection check was already added ad hoc
  during this same phase. Purely syntactic, only tracks *bare* variable writes (`checkWrite`
  above) from `assign` (every entry of one `||`-list included) and `receive`'s *both* `Ref`s —
  the channel `c` counts as a write too, not just the target `x` (per the project owner:
  `receive(x, a); receive(x, b)` must error, same as re-receiving into, or re-assigning, the
  same variable). `if`/`either`'s branches are separate control paths — checked independently,
  starting from the same already-seen set, never against each other — but their writes are
  unioned into what continues past them, so a write in either branch still conflicts with one
  afterward in the same block (exactly the manual's "one branch and whatever both branches
  converge to afterward" case). `while`/`with` bodies don't fork execution, so they're checked
  sequentially, merged with everything around them.
-/
mutual
  partial def CorePlusCal.Statement.checkAssignConflicts {α β b} {m : Type → Type} [Monad m]
      [MonadExceptOf DesugarError m] (seen : List String) (s : CorePlusCal.Statement α β b) : m (List String) :=
    match_source s with
    | .assign asss, pos =>
      asss.foldlM (init := seen) λ seen (r, _) ↦ checkWrite seen r pos
    | .receive c r, pos => do
      let seen ← checkWrite seen c pos
      checkWrite seen r pos
    | .if _ B₁ B₂, _ => do
      let seen₁ ← CorePlusCal.Block.checkAssignConflicts seen B₁
      let seen₂ ← CorePlusCal.Block.checkAssignConflicts seen B₂
      pure (seen₁ ++ seen₂)
    | .either branches, _ => CorePlusCal.Branches.checkAssignConflicts seen branches
    | .while _ B, _ => CorePlusCal.Block.checkAssignConflicts seen B
    | .with _ _ _ _ B, _ => CorePlusCal.Block.checkAssignConflicts seen B
    | .skip, _ | .goto _, _ | .print _, _ | .await _, _ | .assert _, _
    | .send _ _, _ | .multicast _ _, _ => pure seen

  partial def CorePlusCal.Block.checkAssignConflicts {α β b} {m : Type → Type} [Monad m]
      [MonadExceptOf DesugarError m] (seen : List String) (B : CorePlusCal.Block α β b) : m (List String) := do
    let seen ← B.begin.foldlM (init := seen) λ seen s ↦ CorePlusCal.Statement.checkAssignConflicts seen s
    CorePlusCal.Statement.checkAssignConflicts seen B.end

  partial def CorePlusCal.Branches.checkAssignConflicts {α β b} {m : Type → Type} [Monad m]
      [MonadExceptOf DesugarError m] (seen : List String) : CorePlusCal.Branches α β b → m (List String)
    | .either B => CorePlusCal.Block.checkAssignConflicts seen B
    | .or B rest => do
      let seen₁ ← CorePlusCal.Block.checkAssignConflicts seen B
      let seen₂ ← CorePlusCal.Branches.checkAssignConflicts seen rest
      pure (seen₁ ++ seen₂)
end

/-- Run `checkAssignConflicts` over every atomic step (one top-level `(label, Block)` pair per
thread) of a whole algorithm — each starts with a fresh, empty `seen` set, since crossing a
label is exactly crossing an atomic-step boundary. -/
def CorePlusCal.Algorithm.checkAssignConflicts {α β} (algo : CorePlusCal.Algorithm α β) :
    Except DesugarError Unit := do
  for p in algo.processes do
    for thread in p.threads do
      for (_, block) in thread do
        let _ ← CorePlusCal.Block.checkAssignConflicts [] block
  pure ()

/--
  §5.1's annotation-placement prerequisite, residual PlusCal half — companion to
  `Desugarer/TLAPlus.lean`'s `CoreTLAPlus.Module.stripTLAPlusAnnotations`. `Process.mailbox` and
  `Declarations.variables`' `isParameter` are already resolved by the time this runs
  (`Process.desugar`/`Declarations.desugarCheck` above) — everything else reachable through
  `α` (`Declarations`' remaining entries, `MulticastFilter`'s per-bind annotations, a
  `with`-bound variable's own annotation, and every embedded expression's own quantifier/
  record-literal annotation slots, `β`'s internal `α`, reached via `traverse`) is uniformly
  `@type`-only, checked/stripped via the same `extractType` (`Desugarer/TLAPlus.lean`) as the
  TLA⁺ side — in one `Bitraversable` walk, since `Declarations` shares `Algorithm`'s own `α`
  rather than a separate parameter (`Core/CorePlusCal/Syntax.lean`'s module doc).
-/
def CorePlusCal.Algorithm.stripEmbeddedTypeAnnotations
    (algo : CorePlusCal.Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
    Except DesugarError (CorePlusCal.Algorithm (Option SurfaceTLAPlus.Typ) (CoreTLAPlus.Expression (Option SurfaceTLAPlus.Typ))) :=
  bitraverse extractType (traverse extractType) algo

/-- Run statement desugaring — now fused with `@mailbox`/`@parameter` checking/extraction
(`Process.desugar`/`Algorithm.desugar`, `Core/CorePlusCal/Syntax.lean`'s module doc) — against
the concrete monad it's ever needed at: `WithContext`'s and `SegmentContext`'s `Reader`s, error
reporting, and a `List DesugarWarning` accumulator (mirroring `Parser_/Common.lean`'s
`ParserWarningM`, for the `@parameter`-duplicate warning) — no fresh-name synthesis needed for
the goto-explicitization itself (unlike `Desugarer/TLAPlus.lean`'s expression desugaring), since
this compiler never invents a label the user didn't write (this file's module doc). Neither
`Reader`'s outer seed value is ever actually observed: `Thread.desugar` always establishes a
real `SegmentContext` via `withTheReader` before `desugarSegment` reads one, and `WithContext`'s
default (`boundVars := []`) is exactly the correct ambient value for everything outside of a
`with` body anyway. Also runs `CorePlusCal.Algorithm.checkAssignConflicts` (no two assignments
to the same variable within one atomic step) before `stripEmbeddedTypeAnnotations`, so the
returned `CorePlusCal.Algorithm` is always fully checked, with every annotation slot —
declaration-level and expression-level alike — resolved to its actual content. -/
def SurfacePlusCal.Algorithm.runDesugarer (a : SurfacePlusCal.Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
    Except DesugarError (CorePlusCal.Algorithm (Option SurfaceTLAPlus.Typ) (CoreTLAPlus.Expression (Option SurfaceTLAPlus.Typ)) × List DesugarWarning) := do
  let desugar : ReaderT SurfacePlusCal.WithContext (ReaderT SurfacePlusCal.SegmentContext (StateT (List DesugarWarning) (Except DesugarError))) _ :=
    a.desugar
  let (algo, warnings) ← ((desugar.run {}).run default).run []
  algo.checkAssignConflicts
  let algo ← algo.stripEmbeddedTypeAnnotations
  return (algo, warnings)
