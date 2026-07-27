module

public import Desugarer.Errors
public import Core.SurfacePlusCal.Syntax
public import Core.CorePlusCal.Syntax
public import Desugarer.TLAPlus
public import Parser_.Annotations

public section


/-!
  Statement desugaring: `SurfacePlusCal`'s implicit-fallthrough statement lists become
  `CorePlusCal`'s explicit-`goto`, type-indexed-terminal `Block`s.

  A label may appear inside an `if`/`while`/`either` body, not just at a thread's top level: it
  marks the start of a new addressable atomic block, so it is extracted into its own top-level
  `(label, Block)` entry, with explicit `goto`s stitching control flow back together. `with` is
  the one exception — its body never allows a nested label, `goto`, or `while`, and one found
  there is a hard error.

  A `goto` may only appear as the last statement of its enclosing list. A `while` must be
  immediately preceded by a real label; none is auto-inserted. An `if`/`either` containing a
  label or `goto` must itself be followed by a real label; none is synthesized.

  If a thread's last label runs out of statements without an explicit terminal, `goto Done` is
  inserted — `"Done"` is a reserved sentinel needing no matching label definition.

  `ownLabel`/`fallthrough` and `WithContext`'s bound-variable list are `Reader` effects
  (`SegmentContext`/`WithContext` below); `acc` — the segment's own accumulated statements —
  stays an explicit fold parameter.
-/

namespace SurfacePlusCal
  /-- Names currently bound by an enclosing `with` (innermost first; order doesn't matter),
  threaded as a `Reader` through `Statement.desugarLabelFree` and friends. Nested `with`s
  accumulate rather than replace. Used to reject a `while`, or a write (`assign`/`receive`)
  targeting a with-bound name — a fixed local binding, not a process variable. -/
  structure WithContext where
    boundVars : List String := []

  /-- The `Reader` context `desugarSegment` threads through its recursion: which label (if any)
  owns the segment being built (`none` for an `if`/`either` branch, which has no address of its
  own), and where to `goto` if the segment runs out of statements without an explicit redirect. -/
  structure SegmentContext where
    ownLabel : Option String
    fallthrough : String
    deriving Inhabited

  variable {β : Type} {m : Type → Type} [Monad m] [MonadDiagnostic DesugarWarning DesugarError m]
    [MonadFresh m] [MonadReaderOf WithContext m] [MonadWithReaderOf WithContext m]
    [MonadReaderOf SegmentContext m] [MonadWithReaderOf SegmentContext m]

  /-- The reserved sentinel `goto` target meaning "this thread has terminated" — never needs a
  matching label. -/
  private def doneLabel : String := "Done"

  /-- The concrete expression type used once `β` is fixed to `CoreTLAPlus.Expression`. -/
  abbrev CoreExpr := CoreTLAPlus.Expression (List Annotation)

  /-- The annotation slot every PlusCal node carries through desugaring: the raw comment
  annotations parsed at each site, which `stripEmbeddedTypeAnnotations` later turns into an
  `Option Typ`. Pinned rather than left generic, matching `Declarations.desugarCheck` below —
  collapsing a `multicast` filter has to read `@type` off each component and build one for the
  binder it synthesizes, which no generic annotation type allows. -/
  abbrev CoreAnn := List Annotation

  /-- `x[e₁, …, eₙ]`'s indices, per bracket group, collapsed to `CorePlusCal.Ref`'s own unary
  shape via `SurfaceTLAPlus.wrapIndices`; `.field` segments pass through unchanged. `pos` is the
  enclosing statement's own position.

  No `@@` here: `Ref` is not a position-carrying node in this codebase (neither
  `CorePlusCal.Ref`'s `Functor`/`Traversable` instances nor any downstream pass registers one),
  and every diagnostic about a `Ref` is reported against its enclosing statement's span. -/
  def Ref.desugarRef (pos : SourceSpan) (r : SurfacePlusCal.Ref CoreExpr) : CorePlusCal.Ref CoreExpr :=
    { name := r.name, args := r.args.map (Sum.map id (SurfaceTLAPlus.wrapIndices pos)) }

  /-- Collapse a `multicast`'s surface filter to `CorePlusCal.Multicast`'s single binder.

  `multicast(c, [x₁ ⋈₁ e₁, …, xₙ ⋈ₙ eₙ ↦ v])` reaches every `c[y]` for `y` in the Cartesian
  product of the components, an `∈`-bind contributing its own set and an `=`-bind the singleton
  `{e}` — so the components name the parts of a recipient *tuple* and do not scope over one
  another. One component is already that binder. Several collapse to a fresh one over
  `D₁ \X … \X Dₙ`, with each original name rewritten in `v` to its projection off it, exactly as
  `SurfaceTLAPlus.collapseToSingleBinder` does for a multi-binder function literal.

  The synthesized binder's declared type is the tuple of the components' own, which is available
  only when every one of them carries a `@type`; a filter annotating some but not all warns
  (`partialMulticastAnnotation`) and keeps none, the recipient's type being fixed by the
  channel's declared domain regardless. Annotations of other kinds on a collapsed component are
  dropped with it — `stripEmbeddedTypeAnnotations` is what would otherwise reject them, and
  there is no longer a site for them to sit at. -/
  def MulticastFilter.collapse (pos : SourceSpan)
      (f : SurfacePlusCal.MulticastFilter CoreAnn CoreExpr) :
      m (CorePlusCal.Multicast CoreAnn CoreExpr) := do
    -- An `=`-bind is the singleton component `{e}`; an `∈`-bind is its set as written.
    let components := f.binds.map λ (x, anns, isEq, e) ↦
      (x, anns, if isEq then (.set [e] @@ pos : CoreExpr) else e)
    match components with
    -- The parser reads the bind list with `sepBy1` and nothing else builds a filter, so an empty
    -- one is unreachable — the same footing `SurfaceTLAPlus.collapseToSingleBinder`'s own empty
    -- case stands on.
    | [] => unreachable!
    | [(recipient, ann, set)] => return { recipient, ann, set, val := f.val } @@ pos
    | (_, _, dom₀) :: rest =>
      let recipient ← freshName "recipient"
      let set := rest.foldl (init := dom₀) λ acc (_, _, dom) ↦
        .opCall (.var SurfaceTLAPlus.cartesianProduct.canonicalName @@ pos) [acc, dom] @@ pos
      let val := components.zipIdx.foldr (init := f.val) λ ((x, _, _), i) val ↦
        SurfaceTLAPlus.CoreTLAPlus.Expression.subst x (SurfaceTLAPlus.tupleProj pos recipient i) val
      return { recipient, ann := ← tupleAnnotation pos (components.map (·.2.1)), set, val } @@ pos
  where
    /-- `<<τ₁, …, τₙ>>` from the components' own `@type` annotations, or none at all (with a
    warning) when only some of them have one. -/
    tupleAnnotation (pos : SourceSpan) (anns : List CoreAnn) : m CoreAnn := do
      let types := anns.map λ as ↦ as.findSome? λ
        | .«@type» _ τ => some τ
        | _ => none
      match types.mapM id with
      | some τs => return [.«@type» pos (.tuple τs)]
      | none =>
        if types.any (·.isSome) then warn (.partialMulticastAnnotation pos)
        return []

  mutual
    /-- Does this statement need the extraction-capable desugaring path (`desugarSegment`) rather
    than the cheap always-non-terminal one (`desugarLabelFreeBlock`)? True if a label appears
    anywhere within it, an `if`/`either` branch or `while` body ends in a bare `goto`, or a
    `while` appears anywhere. A `with` body never needs extraction. -/
    partial def Statement.needsExtraction : Statement CoreAnn β → Bool
      | .if _ b1 b2 => b1.needsExtraction || (b2.map (·.needsExtraction)).getD false
      | .either bs => bs.any (·.needsExtraction)
      | .while _ b => b.needsExtraction
      | .with .. | .skip | .goto _ | .print _ | .assign _ | .await _ | .assert _
      | .receive .. | .send .. | .multicast .. => false

    /-- Declared at the root `List` namespace so dot-notation on a `List (String ⊕ Statement CoreAnn
    β)` resolves to it. `true` as soon as a label is found anywhere, the last element is a bare
    `goto`, any statement (`Statement.needsExtraction`) does, or a `while` appears in the list. -/
    partial def _root_.List.needsExtraction : List (String ⊕ Statement CoreAnn β) → Bool
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
  def rejectLabels : List (String ⊕ Statement CoreAnn β) → m (List (Statement CoreAnn β))
    | [] => pure []
    | .inl l :: _ => throw (.nestedLabel (posOf l))
    | .inr s :: rest => (s :: ·) <$> rejectLabels rest

  /-- Flatten a multi-binder `with (x = e, y ∈ S, …) { … }` into a nested chain of single-binder
  `CorePlusCal.Statement.with`s (`with (x = e) { with (y ∈ S) { … } }`) — `CorePlusCal.Statement.
  with` only ever binds one variable at a time (`Core/CorePlusCal/Syntax.lean`'s module doc).
  Every binder past the first is wrapped in its own label-free `Block` (`⟨[], ·⟩`) around the
  next binder, with `B` — the already-desugared body — innermost.

  Every link of the chain is registered at `pos`, the whole surface `with`'s own span: the chain
  is one source construct, and no binder past the first has a narrower span of its own to
  report. -/
  def buildWithChain (pos : SourceSpan) (vars : List (String × CoreAnn × Bool × β))
      (B : CorePlusCal.Block CoreAnn β false) : CorePlusCal.Statement CoreAnn β false :=
    match vars with
    | [] => unreachable! -- `with` always binds at least one variable, by construction of the parser (`sepBy1`)
    | [(x, ann, eq, e)] => .with x ann eq e B @@ pos
    | (x, ann, eq, e) :: rest => .with x ann eq e ⟨[], buildWithChain pos rest B⟩ @@ pos

  mutual
    /-- Desugar a statement known not to be last in its enclosing sequence and known to need no
    extraction anywhere inside it: always yields a non-terminal (`false`) `CorePlusCal.Statement`,
    with `if`/`while`/`either`'s sub-blocks recursing via `desugarLabelFreeBlock`.

    Reads `WithContext` for which names are currently `with`-bound. A `while` is rejected outright
    if any are bound (`whileInWith`); an `assign` or `receive` targeting a bound name is likewise
    rejected (`withBoundVarWritten`). -/
    partial def Statement.desugarLabelFree (s : Statement CoreAnn CoreExpr) : m (CorePlusCal.Statement CoreAnn CoreExpr false) := match_source s with
      | .goto _, pos => throw (.gotoNotInTailPosition pos)
      | .skip, pos => pure (.skip @@ pos)
      | .print e, pos => pure (.print e @@ pos)
      | .assign a, pos => do
        let ctx ← readThe WithContext
        match a.find? (λ (r, _) ↦ ctx.boundVars.contains r.name) with
        | some (r, _) => throw (.withBoundVarWritten pos r.name)
        | none => pure (.assign (a.map λ (r, e) ↦ (Ref.desugarRef pos r, e)) @@ pos)
      | .if cond b1 b2, pos =>
        (.if cond · · @@ pos) <$> desugarLabelFreeBlock b1 <*> desugarLabelFreeBlock (b2.getD [])
      | .await e, pos => pure (.await e @@ pos)
      | .with vars b, pos =>
        let newNames := vars.map (·.1)
        buildWithChain pos vars <$> withTheReader WithContext ({ boundVars := newNames ++ ·.boundVars }) (desugarLabelFreeBlock b)
      | .assert e, pos => pure (.assert e @@ pos)
      | .either branches, pos => (.either · @@ pos) <$> Branches.desugarLabelFree branches
      | .while cond b, pos => do
        let ctx ← readThe WithContext
        if !ctx.boundVars.isEmpty then throw (.whileInWith pos)
        else (.while cond · @@ pos) <$> desugarLabelFreeBlock b
      | .receive c r, pos => do
        let ctx ← readThe WithContext
        if ctx.boundVars.contains r.name then throw (.withBoundVarWritten pos r.name)
        else pure (.receive (Ref.desugarRef pos c) (Ref.desugarRef pos r) @@ pos)
      | .send c e, pos => pure (.send (Ref.desugarRef pos c) e @@ pos)
      | .multicast c f, pos => (.multicast c · @@ pos) <$> MulticastFilter.collapse (posOf f) f

    /-- Desugar a statement-list known to be entirely label-free into a non-terminal block:
    every entry desugars via `Statement.desugarLabelFree`, except the last, whose own natural
    terminality (a bare `goto`, or an `if`/`either` that recursively is) is preserved. -/
    partial def desugarLabelFreeBlock (stmts : List (String ⊕ Statement CoreAnn CoreExpr)) :
        m (CorePlusCal.Block CoreAnn CoreExpr false) := do
      go (← rejectLabels stmts)
    where
      go : List (Statement CoreAnn CoreExpr) → m (CorePlusCal.Block CoreAnn CoreExpr false)
        | [] => pure ⟨[], .skip @@ SourceSpan.placeholder⟩
        | [s] => match_source s with
          | .goto _, pos => throw (.gotoNotInTailPosition pos)
          | _, _ => (⟨[], ·⟩) <$> Statement.desugarLabelFree s
        | s :: rest => do
          let s' ← Statement.desugarLabelFree s
          let block ← go rest
          pure ⟨s' :: block.begin, block.end⟩

    partial def Branches.desugarLabelFree (branches : List (List (String ⊕ Statement CoreAnn CoreExpr))) :
        m (CorePlusCal.Branches CoreAnn CoreExpr false) := match branches with
      | [] => unreachable! -- `either` always has ≥2 branches, by construction of the parser
      | [b] => .either <$> desugarLabelFreeBlock b
      | b :: bs => .or <$> desugarLabelFreeBlock b <*> Branches.desugarLabelFree bs
  end

  /-- Turn a list of desugared branch-blocks into `CorePlusCal.Branches`. -/
  def buildBranches : List (CorePlusCal.Block CoreAnn β true) → CorePlusCal.Branches CoreAnn β true
    | [] => unreachable!
    | [b] => .either b
    | b :: bs => .or b (buildBranches bs)

  /-- Desugar `stmts` — content directly following a label, per the ambient `SegmentContext`'s
  `ownLabel` (if this call is processing exactly that; `none` for an `if`/`either` branch, which
  has no address of its own) — into the terminal `CorePlusCal.Block` for this segment, plus every
  `(label, Block)` pair extracted from labels nested within it (`if`/`while`/`either` bodies).
  `SegmentContext.fallthrough` is where to implicitly `goto` once the segment (or its last
  extracted continuation) runs out of statements without an explicit redirect.

  `acc` accumulates the segment's own non-terminal statements so far, in order — an explicit
  parameter rather than folded into the `Reader` context (module doc above). -/
  partial def desugarSegment (acc : List (CorePlusCal.Statement CoreAnn CoreExpr false)) :
      List (String ⊕ Statement CoreAnn CoreExpr) → m (CorePlusCal.Block CoreAnn CoreExpr true × List (String × CorePlusCal.Block CoreAnn CoreExpr true))
    | [] => do
      let ctx ← readThe SegmentContext
      pure (⟨acc, .goto ctx.fallthrough @@ SourceSpan.placeholder⟩, [])
    | .inl nextLabel :: rest => do
      let ctx ← readThe SegmentContext
      let (nextBlock, extracted) ←
        withTheReader SegmentContext (λ _ ↦ { ctx with ownLabel := some nextLabel }) (desugarSegment [] rest)
      pure (⟨acc, .goto nextLabel @@ SourceSpan.placeholder⟩, (nextLabel, nextBlock) :: extracted)
    | .inr s :: rest => match_source s with
      | .goto l, pos => match rest with
        | [] => pure (⟨acc, .goto l @@ pos⟩, [])
        | .inl nextLabel :: rest' => do
          let ctx ← readThe SegmentContext
          let (nextBlock, extracted) ←
            withTheReader SegmentContext (λ _ ↦ { ctx with ownLabel := some nextLabel }) (desugarSegment [] rest')
          pure (⟨acc, .goto l @@ pos⟩, (nextLabel, nextBlock) :: extracted)
        | .inr s' :: _ => throw (.gotoNotInTailPosition (posOf s'))
      -- A `while` must be immediately preceded by a real label: nothing to extract unless `acc`
      -- is empty and there's a real label to attribute the `while` to.
      | .while cond body, pos => do
        let ctx ← readThe SegmentContext
        if hAcc : acc.isEmpty ∧ ctx.ownLabel.isSome then
          let loopLabel := ctx.ownLabel.get hAcc.2
          if !body.needsExtraction then do
            let bodyBlock ← desugarLabelFreeBlock body
            desugarSegment [.while cond bodyBlock @@ pos] rest
          else do
            let (bodyBlock, ex) ←
              withTheReader SegmentContext (λ _ ↦ { ownLabel := some loopLabel, fallthrough := loopLabel })
                (desugarSegment [] body)
            let (result, ex') ← desugarSegment [.while cond bodyBlock @@ pos] rest
            pure (result, ex ++ ex')
        else throw (.whileNotLabelled pos)
      | .if cond b1 b2, pos =>
        let b2 := b2.getD []
        if !b1.needsExtraction && !b2.needsExtraction then do
          let block1 ← desugarLabelFreeBlock b1
          let block2 ← desugarLabelFreeBlock b2
          desugarSegment (acc ++ [.if cond block1 block2 @@ pos]) rest
        else do
          let (cont, contResult) ← desugarContinuation rest
          let branchCtx : SegmentContext := { ownLabel := none, fallthrough := cont }
          let (block1, ex1) ← withTheReader SegmentContext (λ _ ↦ branchCtx) (desugarSegment [] b1)
          let (block2, ex2) ← withTheReader SegmentContext (λ _ ↦ branchCtx) (desugarSegment [] b2)
          pure (⟨acc, .if cond block1 block2 @@ pos⟩, ex1 ++ ex2 ++ contResult)
      | .either branches, pos =>
        if !branches.any (·.needsExtraction) then do
          let block ← Branches.desugarLabelFree branches
          desugarSegment (acc ++ [.either block @@ pos]) rest
        else do
          let (cont, contResult) ← desugarContinuation rest
          let branchCtx : SegmentContext := { ownLabel := none, fallthrough := cont }
          let results ← branches.mapM (withTheReader SegmentContext (λ _ ↦ branchCtx) <| desugarSegment [] ·)
          pure (⟨acc, .either (buildBranches (results.map Prod.fst)) @@ pos⟩, results.flatMap Prod.snd ++ contResult)
      | _, _ => do
        let s' ← Statement.desugarLabelFree s
        desugarSegment (acc ++ [s']) rest
  where
    /-- The continuation label for whatever comes after a control-flow statement that needed
    extraction, plus its own extracted content: the next real label if `rest` starts with one,
    the ambient `SegmentContext.fallthrough` if `rest` is empty, or `notFollowedByLabel`
    otherwise. -/
    desugarContinuation :
        List (String ⊕ Statement CoreAnn CoreExpr) → m (String × List (String × CorePlusCal.Block CoreAnn CoreExpr true))
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
  def Thread.desugar : List (String ⊕ Statement CoreAnn CoreExpr) → m (List (String × CorePlusCal.Block CoreAnn CoreExpr true))
    | [] => pure []
    | .inr s :: _ => throw (.unlabelledStatement (posOf s))
    | .inl firstLabel :: rest => do
      let (block, extracted) ←
        withTheReader SegmentContext (λ _ ↦ { ownLabel := some firstLabel, fallthrough := doneLabel }) (desugarSegment [] rest)
      pure ((firstLabel, block) :: extracted)

  /-- Run `SurfaceTLAPlus.Expression.desugar` on a single, self-contained expression — used for
  `@mailbox`'s filter arguments (`extractMailbox` below). The only effect the caller's own `m`
  doesn't already supply is the `@`-reader `Expression.desugar` wants, added as a local `ReaderT`
  layer and run at `none` — a filter argument is never inside an `EXCEPT` update. Fresh-name
  generation reaches `Common/Fresh.lean`'s single process-wide counter through `m` like every
  other pass, rather than through a pinned `IO`, so this stays a separate namespace from nothing:
  no `0`-restarted counter the way a locally-threaded `StateT Nat` would give it. -/
  private def desugarMailboxArg {m : Type → Type} [Monad m]
      [MonadDiagnostic DesugarWarning DesugarError m] [MonadFresh m]
      (e : SurfaceTLAPlus.Expression (List Annotation)) :
      m (CoreTLAPlus.Expression (List Annotation)) :=
    let d : ReaderT (Option (CoreTLAPlus.Expression (List Annotation))) m _ := e.desugar
    d.run none

  /-- Validate and extract a `Process.ann` slot: at most one `@mailbox`, nothing else, with its
  filter arguments fully desugared (`desugarMailboxArg`). -/
  def extractMailbox {m : Type → Type} [Monad m] [MonadDiagnostic DesugarWarning DesugarError m]
      [MonadFresh m] (anns : List Annotation) :
      m (Option (String × List (CoreTLAPlus.Expression (List Annotation)))) := do
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
    | some (name, args) =>
      (some ∘ (name, ·)) <$> args.mapM desugarMailboxArg

  /-- Validate `@parameter`'s placement (only on a `∈`-initialized entry) and extract its
  *presence* into the dedicated `isParameter` field — a repeated `@parameter` is a warning, not
  an error. Every other annotation is left untouched in `α` for `stripEmbeddedTypeAnnotations`
  to validate later. -/
  def Declarations.desugarCheck {β : Type} {m : Type → Type} [Monad m]
      [MonadDiagnostic DesugarWarning DesugarError m]
      (decls : Declarations (List Annotation) β) : m (CorePlusCal.Declarations (List Annotation) β) := do
    let «variables» ← decls.variables.mapM λ (x, anns, init) ↦ do
      -- `init`'s `Bool` is `true` for `=`, `false` for `∈`; `@parameter` only makes sense on a
      -- `∈`-initialized variable.
      let allowParameter := match init with
        | some (false, _) => true
        | _ => false
      let mut seenParameter := false
      let mut rest : List Annotation := []
      for ann in anns do
        match ann with
        | .«@parameter» pos =>
          unless allowParameter do throw (.wrongAnnotationKindAtSite pos "@parameter" "@type")
          if seenParameter then warn (DesugarWarning.duplicateParameterAnnotation pos)
          seenParameter := true
        | other => rest := other :: rest
      return (x, rest.reverse, seenParameter, init)
    return { «variables», channels := decls.channels, fifos := decls.fifos }

  /-- Desugar one process: goto-explicitize its threads (`Thread.desugar`) and validate/extract
  its `@mailbox` annotation (`extractMailbox`) and its local declarations' `@parameter`
  annotations (`Declarations.desugarCheck`). -/
  def Process.desugar (p : Process (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
      m (CorePlusCal.Process (List Annotation) (CoreTLAPlus.Expression (List Annotation))) := do
    let mailbox ← extractMailbox p.ann
    let localState ← p.localState.desugarCheck
    (CorePlusCal.Process.mk mailbox p.isFair p.name p.«=|∈» p.id localState · @@ posOf p)
      <$> traverse Thread.desugar p.threads

  /-- Desugar a whole algorithm: its global declarations (`Declarations.desugarCheck`) and
  every process (`Process.desugar`). -/
  def Algorithm.desugar (a : Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
      m (CorePlusCal.Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) := do
    let globalState ← a.globalState.desugarCheck
    (CorePlusCal.Algorithm.mk a.isFair a.name globalState · @@ posOf a) <$> traverse Process.desugar a.processes

end SurfacePlusCal

/-- Records `r`'s base variable (`r.name`) as a write against `seen`, throwing
`DesugarError.conflictingAssignment` if already present — regardless of indexing, since deciding
whether two indexed writes to the same base variable actually alias is out of scope for this
syntactic check; `x[0] := 3` and `x[1] := 4` conflict even though they touch different
elements. -/
private def checkWrite {β} {m : Type → Type} [Monad m]
    [MonadDiagnostic DesugarWarning DesugarError m]
    (seen : List String) (r : CorePlusCal.Ref β) (pos : SourceSpan) : m (List String) :=
  if seen.contains r.name then throw (.conflictingAssignment pos r.name)
  else pure (r.name :: seen)

/-!
  Checks that no two assignments write the same base variable within one atomic step, on the
  same control path, regardless of indexing (`checkWrite` above) — from both of `assign`'s and
  `receive`'s `Ref`s (the channel counts as a write too, not just the target). `if`/`either`
  branches are separate control paths, checked independently from the same starting set, with
  their writes unioned into what continues past them.
-/
mutual
  partial def CorePlusCal.Statement.checkAssignConflicts {α β b} {m : Type → Type} [Monad m]
      [MonadDiagnostic DesugarWarning DesugarError m]
      (seen : List String) (s : CorePlusCal.Statement α β b) : m (List String) :=
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
      [MonadDiagnostic DesugarWarning DesugarError m]
      (seen : List String) (B : CorePlusCal.Block α β b) : m (List String) := do
    let seen ← B.begin.foldlM (init := seen) λ seen s ↦ CorePlusCal.Statement.checkAssignConflicts seen s
    CorePlusCal.Statement.checkAssignConflicts seen B.end

  partial def CorePlusCal.Branches.checkAssignConflicts {α β b} {m : Type → Type} [Monad m]
      [MonadDiagnostic DesugarWarning DesugarError m]
      (seen : List String) : CorePlusCal.Branches α β b → m (List String)
    | .either B => CorePlusCal.Block.checkAssignConflicts seen B
    | .or B rest => do
      let seen₁ ← CorePlusCal.Block.checkAssignConflicts seen B
      let seen₂ ← CorePlusCal.Branches.checkAssignConflicts seen rest
      pure (seen₁ ++ seen₂)
end

/-- Run `checkAssignConflicts` over every atomic step (one top-level `(label, Block)` pair per
thread) of a whole algorithm — each starts with a fresh, empty `seen` set, since crossing a
label is exactly crossing an atomic-step boundary.

`DiagT … Id` rather than a bare `Except`, for the same reason as
`CoreTLAPlus.Module.stripTLAPlusAnnotations` (`Desugarer/TLAPlus.lean`): one `MonadDiagnostic`
shape for every entry point, absorbed by the caller with `DiagT.lift`. Emits no warnings today. -/
def CorePlusCal.Algorithm.checkAssignConflicts {α β} (algo : CorePlusCal.Algorithm α β) :
    DiagT DesugarWarning DesugarError Id Unit := do
  for p in algo.processes do
    for thread in p.threads do
      for (_, block) in thread do
        let _ ← CorePlusCal.Block.checkAssignConflicts [] block
  pure ()

/-- Validate and strip every remaining `@type`-only annotation slot in an already
`Process.desugar`/`Declarations.desugarCheck`-processed algorithm, using the same `extractType`
(`Desugarer/TLAPlus.lean`) as the TLA⁺ side — and, like it, reports through `DiagT … Id` rather
than a bare `Except`. -/
def CorePlusCal.Algorithm.stripEmbeddedTypeAnnotations
    (algo : CorePlusCal.Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
    DiagT DesugarWarning DesugarError Id (CorePlusCal.Algorithm (Option SurfaceTLAPlus.Typ) (CoreTLAPlus.Expression (Option SurfaceTLAPlus.Typ))) :=
  bitraverse extractType (traverse extractType) algo

/-- Run statement desugaring (fused with `@mailbox`/`@parameter` checking/extraction) against the
concrete monad it needs: `WithContext`'s and `SegmentContext`'s `Reader`s, plus `MonadDiagnostic`
for error reporting and the `List DesugarWarning` accumulator — instantiated at `DiagT`, so a
warning emitted before a later fatal error still survives. Also runs
`CorePlusCal.Algorithm.checkAssignConflicts` before `stripEmbeddedTypeAnnotations`, so the
returned `CorePlusCal.Algorithm` is fully checked with every annotation slot resolved — both run
after warnings are already extracted, since neither touches them. The base monad `n` stays
abstract for the same reason as `Desugarer/TLAPlus.lean`'s `runDesugarer`: the fresh-name counter
it needs belongs to one compile, not to the process. -/
def SurfacePlusCal.Algorithm.runDesugarer {n : Type → Type} [Monad n] [MonadFresh n]
    (a : SurfacePlusCal.Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :
    DiagT DesugarWarning DesugarError n (CorePlusCal.Algorithm (Option SurfaceTLAPlus.Typ) (CoreTLAPlus.Expression (Option SurfaceTLAPlus.Typ))) := do
  let desugar : ReaderT SurfacePlusCal.WithContext (ReaderT SurfacePlusCal.SegmentContext (DiagT DesugarWarning DesugarError n))
      (CorePlusCal.Algorithm (List Annotation) (CoreTLAPlus.Expression (List Annotation))) :=
    a.desugar
  -- `DiagT` has its own `Monad`/`MonadExceptOf` instances (`Common/Errors.lean`) — bind directly,
  -- no manual unwrapping of the underlying `List DesugarWarning × Except DesugarError _` pair.
  let algo ← (desugar.run {}).run default
  DiagT.lift id id algo.checkAssignConflicts
  DiagT.lift id id algo.stripEmbeddedTypeAnnotations

end
