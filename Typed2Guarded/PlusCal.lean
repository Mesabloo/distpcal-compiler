import PlusCalCompiler.SurfacePlusCal.Syntax
import PlusCalCompiler.GuardedPlusCal.Syntax
import Mathlib.Control.Monad.Writer
import PlusCalCompiler.Errors
import PlusCalCompiler.Passes.SourceCodeToSurface.Annotations
import Extra.List

namespace SurfacePlusCal
  open SurfaceTLAPlus (Expression Typ)

  inductive TranslationError : Type _
    | unexpectedGlobalVariables (pos : SourceSpan)
    | typeLessChannel (pos : SourceSpan) (name : String)
    | channelIncorrectType (pos : SourceSpan) (name : String)
    | tooManyTypesChannel (pos : SourceSpan) (name : String)
    | channelNotEnoughParameters (pos : SourceSpan) (name : String) (expected got : Nat)
    | higherOrderChannelsUnsupported (pos : SourceSpan) (name : String)
    | uninitializedVariable (pos : SourceSpan) (name : String)
    | typeLessVariable (pos : SourceSpan) (name : String)
    | tooManyTypesVariable (pos : SourceSpan) (name : String)
    | incorrectMailboxSpecification (pos : SourceSpan)
    | tooManyMailboxes (pos : SourceSpan) (name : String)
    | unknownChannel (pos : SourceSpan) (name : String)
    | wrongChannelDimension (pos : SourceSpan) (name : String) (expected got : Nat)
    | threadMustStartWithLabel (pos : SourceSpan)
    | unexpectedLabelInEitherBranch (pos : SourceSpan) (label : String)
    | missingGotoAtEndOfBranch (pos : SourceSpan)
    | unexpectedWhileStatement (pos : SourceSpan)
    | unexpectedIfStatement (pos : SourceSpan)
    | unexpectedEitherStatement (pos : SourceSpan)
    | unexpectedAwaitStatement (pos : SourceSpan)
    | unexpectedGotoStatement (pos : SourceSpan)
    | unexpectedReceiveStatement (pos : SourceSpan)
    | unexpectedWithStatement (pos : SourceSpan)
    | channelReferenceTooManyIndices (pos : SourceSpan) (got : Nat)
    | channelReferenceExpectedNIndices (pos : SourceSpan) (name : String) (got expected : Nat)
    | unexpectedParallelAssignment (pos : SourceSpan)
    | cannotReceiveWithoutIndicatedMailbox (pos : SourceSpan)
    | cannotReceiveFromNonMailbox (pos : SourceSpan)
    | labelInWithStatement (pos : SourceSpan) (x : ℒ)
    deriving Inhabited

  instance : CompilerDiagnostic TranslationError String where
    isError := true
    msgOf
      | .unexpectedGlobalVariables _ => "Distributed algorithms may not contain a globally shared state.\nProcesses must instead communicate via message-passing."
      | .typeLessChannel _ name => s!"Channel/FIFO '{name}' is missing a type annotation."
      | .channelIncorrectType _ name => s!"Type of channel/FIFO '{name}' must be a function of Addresses."
      | .channelNotEnoughParameters _ name expected got => s!"Channel/FIFO '{name}' has dimension {expected} but its type has {got} arguments."
      | .tooManyTypesChannel _ name => s!"Channel/FIFO '{name}' has too many type annotations (expected 1)."
      | .higherOrderChannelsUnsupported _ name => s!"Channel/FIFO '{name}' may not contain values of type `Channel(_)` or `(_) => _`."
      | .uninitializedVariable _ name => s!"Variable '{name}' must be initialized."
      | .typeLessVariable _ name => s!"Variable '{name}' is missing a type information."
      | .tooManyTypesVariable _ name => s!"Variable '{name}' has too many types attached (only 1 is wanted)."
      | .incorrectMailboxSpecification _ => s!"'@mailbox' annotation expects an expression of the form `var` or `var[self]`."
      | .tooManyMailboxes _ name => s!"Only at most one '@mailbox' annotation was expected for process '{name}'"
      | .unknownChannel _ name => s!"Unknown channel/FIFO '{name}' in '@mailbox' annotation."
      | .wrongChannelDimension _ name expected got => s!"Channel/FIFO '{name}' has dimension {expected} but is used with {got} arguments."
      | .threadMustStartWithLabel _ => s!"Threads must all start with a label."
      | .unexpectedLabelInEitherBranch _ name => s!"Unexpected label '{name}' in a branch of an `either` statement."
      | .missingGotoAtEndOfBranch _ => s!"Missing `goto` statement at end of atomic branch."
      | .unexpectedWhileStatement _ => s!"Unexpected `while` statement in atomic branch.\nIt should have been translated to `if` already."
      | .unexpectedIfStatement _ => s!"Unexpected `if` statement in atomic branch.\nIt should have been translated to `either` already."
      | .unexpectedEitherStatement _ => s!"`either` statements are expected only at the top level of an atomic block."
      | .unexpectedAwaitStatement _ => s!"`await` statements are expected only at the beginning of atomic branches."
      | .unexpectedReceiveStatement _ => s!"`receive` statements are expected only at the beginning of atomic branches."
      | .unexpectedWithStatement _ => s!"`with` statements are expected only at the beginning of atomic branches."
      | .unexpectedGotoStatement _ => s!"`goto` statements are only expected at the very end of atomic branches, as the last instruction."
      | .channelReferenceTooManyIndices _ got => s!"Channel references may have at most 1 index, but {got} were given."
      | .channelReferenceExpectedNIndices _ name got expected => s!"Channel/FIFO '{name}' has dimension {expected}, but was indexed by {got} arguments."
      | .unexpectedParallelAssignment _ => s!"Unexpected parallel assignment.\nAssignments may only be to a single reference."
      | .cannotReceiveWithoutIndicatedMailbox _ => s!"Cannot receive messages when no `@mailbox` annotation is present on the surrounding process."
      | .cannotReceiveFromNonMailbox _ => s!"Cannot receive messages from a reference which is not the indicated mailbox of the surrounding process."
      | .labelInWithStatement _ l => s!"Label '{l}' found inside a `with` block where it is not allowed."
    posOf
      | .unexpectedGlobalVariables pos
      | .typeLessChannel pos _
      | .channelIncorrectType pos _
      | .tooManyTypesChannel pos _
      | .channelNotEnoughParameters pos _ _ _
      | .higherOrderChannelsUnsupported pos _
      | .uninitializedVariable pos _
      | .typeLessVariable pos _
      | .tooManyTypesVariable pos _
      | .incorrectMailboxSpecification pos
      | .tooManyMailboxes pos _
      | .unknownChannel pos _
      | .wrongChannelDimension pos _ _ _
      | .threadMustStartWithLabel pos
      | .unexpectedLabelInEitherBranch pos _
      | .missingGotoAtEndOfBranch pos
      | .unexpectedWhileStatement pos
      | .unexpectedIfStatement pos
      | .unexpectedEitherStatement pos
      | .unexpectedAwaitStatement pos
      | .unexpectedReceiveStatement pos
      | .unexpectedWithStatement pos
      | .unexpectedGotoStatement pos
      | .channelReferenceTooManyIndices pos _
      | .channelReferenceExpectedNIndices pos _ _ _
      | .unexpectedParallelAssignment pos
      | .cannotReceiveWithoutIndicatedMailbox pos
      | .labelInWithStatement pos _
      | .cannotReceiveFromNonMailbox pos => pos

  inductive TranslationWarning : Type _
    | uselessFairModifier (pos : SourceSpan)
    | unrecognizedAnnotation (pos : SourceSpan) (name : String)

  instance : CompilerDiagnostic TranslationWarning String where
    isError := false
    msgOf
      | .uselessFairModifier _ => "`fair` modifiers on algorithms and processes are ignored."
      | .unrecognizedAnnotation _ name => s!"Unrecognized annotation '{name}' for this binding."
    posOf
      | .uselessFairModifier pos
      | .unrecognizedAnnotation pos _ => pos

  variable {m : Type _ → Type _} [Monad m]
    [MonadExcept TranslationError m] [MonadWriter (List TranslationWarning) m]
    {α} -- the type of annotations

  @[always_inline]
  private abbrev warn (w : TranslationWarning) : m Unit := tell [w]

  /--
    Checks whether channel/FIFOs have an acceptable type ascribed to them, i.e. that they have
    type `⟨ADDRESS, …, ADDRESS⟩ → Channel(τ)`, where the domain may be empty (a function of zero parameter) and
    `τ` may not contain instances of `Channel(_)` or `(_) ⇒ _` (i.e. no channels/operators may be transmitted).
  -/
  private partial def channelHasCorrectType? (name : Located 𝒱) (anns : List Annotation) (dims : List (Located (Expression Annotation))) : m Typ := do
    match ← anns.filterM λ | .«@type» _ => pure true
                           | ann => false <$ warn (.unrecognizedAnnotation name.segment ann.name) with
      | [.«@type» τ] => do
        let rec containsChannelsOrOps : Typ → Bool
          | .channel _ | .operator _ _ => true
          | .bool | .int | .str | .var _ | .const _ | .address => false
          | .set τ | .seq τ => containsChannelsOrOps τ
          | .function τ₁ τ₂ => containsChannelsOrOps τ₁ || containsChannelsOrOps τ₂
          | .tuple τs => τs.any containsChannelsOrOps
          | .record fs => fs.any λ ⟨_, τ⟩ ↦ containsChannelsOrOps τ

        match τ.data with
          | .function (.tuple args) (.channel τ) => do
            if args.length ≠ dims.length then
              throw <| .channelNotEnoughParameters name.segment name.data dims.length args.length
            if containsChannelsOrOps τ then
              throw <| .higherOrderChannelsUnsupported name.segment name.data
            unless args.all (· == .address) do
              throw <| .channelIncorrectType name.segment name.data
          | .function .address (.channel τ) => do
            if containsChannelsOrOps τ then
              throw <| .higherOrderChannelsUnsupported name.segment name.data
            unless dims.length = 1 do
              throw <| .channelNotEnoughParameters name.segment name.data dims.length 1
          | .channel τ => do
            if containsChannelsOrOps τ then
              throw <| .higherOrderChannelsUnsupported name.segment name.data
          | _ => throw <| .channelIncorrectType name.segment name.data
        return τ.data
      | [_] => unreachable!
      | [] => throw <| .typeLessChannel name.segment name.data
      | _ => throw <| .tooManyTypesChannel name.segment name.data

  private def variableHasTypeAndInit? (var : Located 𝒱) (anns : List Annotation) (init : Option (Bool × Located (Expression Annotation))) : m (Typ × Bool × Located (Expression Annotation)) := do
    let typ ← match ← anns.filterM λ | .«@type» _ => pure true
                                     | .«@parameter» => pure false
                                     | ann => false <$ warn (.unrecognizedAnnotation var.segment ann.name) with
              | [.«@type» τ] => do pure τ.data
              | [_] => unreachable!
              | [] => throw <| .typeLessVariable var.segment var.data
              | _ => throw <| .tooManyTypesVariable var.segment var.data
    unless init.isSome do throw <| .uninitializedVariable var.segment var.data
    return ⟨typ, init.get!⟩

  private def processHasMailbox? (var : Located 𝒱) (anns : List Annotation) (chans : Std.HashMap String (Typ × List (Located (Expression Annotation)))) : m (Option (Located (Expression Annotation))) := do
    let mailbox ← match ← anns.filterM λ | .«@mailbox» _ _ _ => pure true
                                         | ann => false <$ warn (.unrecognizedAnnotation var.segment ann.name) with
                  | [.«@mailbox» pos name args] =>
                    unless args == [.var "self"] || args == [] do throw <| .incorrectMailboxSpecification pos
                    let chan := chans.find? name
                    if let .some ⟨_, args'⟩ := chan then
                      unless args.length == args'.length do
                        throw <| .wrongChannelDimension pos name args'.length args.length
                      if args.length > 0 then
                        pure <| .some ⟨pos, .fnCall ⟨pos, .var name⟩ (Located.mk pos <$> args)⟩
                      else
                        pure <| .some ⟨pos, .var name⟩
                    else
                      throw <| .unknownChannel pos name
                  | [_] => unreachable!
                  | [] => pure .none
                  | _ => throw <| .tooManyMailboxes var.segment var.data

  private partial def checkAtomicGuardedBlock? (chans : Std.HashMap String (Typ × List (Located (Expression Annotation)))) (mailbox : Option (Located (Expression Annotation))) (label : Located ℒ) (stmts : List (Located (Statement Annotation))) : m (GuardedPlusCal.AtomicBlock Typ (Located (Expression Annotation))) := do
    let _ {β} : Inhabited (m β) := ⟨throw (m := m) default⟩

    /- Checks that a given list of instructions is of the form `PRECOND; B; goto _`. -/
    let rec checkBlockIsGuarded (pos : SourceSpan) : List (Located (Statement Annotation)) → (inPrecond : Bool := true) → m (GuardedPlusCal.AtomicBranch Typ (Located (Expression Annotation)))
      -- PRECOND
      | ⟨pos, .with bs Ss'⟩ :: Ss, true => do
        let Is := bs.map λ ⟨x, «=|∈», e⟩ ↦ GuardedPlusCal.Statement.let x.data sorry «=|∈».data e @@ pos
        let Ss' ← Ss'.traverse λ | .inl ⟨pos, l⟩ => throw <| .labelInWithStatement pos l
                                 | .inr S => pure S
        let B ← checkBlockIsGuarded pos (Ss' ++ Ss) true
        return { B with
          precondition := match h : Is with
            | [] => B.precondition
            | _ :: _ => .some <| B.precondition.elim (GuardedPlusCal.Block.ofList Is (h ▸ List.cons_ne_nil _ _)) (GuardedPlusCal.Block.prepend Is)
        }
      | ⟨pos, .await e⟩ :: Ss, true => do
        let B ← checkBlockIsGuarded pos Ss true
        let I : GuardedPlusCal.Statement .. := .await e @@ pos
        return { B with
          precondition := .some <| B.precondition.elim (GuardedPlusCal.Block.end I) (GuardedPlusCal.Block.cons I)
        }
      | ⟨pos, .receive ⟨p, c⟩ ⟨_, r⟩⟩ :: Ss, true => do
        unless c.args.length ≤ 1 do throw <| .channelReferenceTooManyIndices p c.args.length
        if let .some ⟨_, args'⟩ := chans.find? c.name then
          unless (c.args.head?.getD []).length = args'.length do throw <| .channelReferenceExpectedNIndices p c.name ((c.args.head?.map List.length).getD 0) args'.length
          match mailbox with
          | .none => throw <| .cannotReceiveWithoutIndicatedMailbox pos
          | .some expr =>
            if !Expression.stripPosEq expr ⟨p, .fnCall ⟨p, .var c.name⟩ (c.args.head?.getD [])⟩ && !Expression.stripPosEq expr ⟨p, .var c.name⟩ then
              throw <| .cannotReceiveFromNonMailbox pos
          let B ← checkBlockIsGuarded pos Ss true
          let I : GuardedPlusCal.Statement .. := .receive ⟨c.name, c.args.head?.getD []⟩ ⟨r.name, r.args⟩ @@ pos
          return { B with
            precondition := .some <| B.precondition.elim (GuardedPlusCal.Block.end I) (GuardedPlusCal.Block.cons I)
          }
        else
          throw <| .unknownChannel p c.name
      -- B
      | ⟨pos, .skip⟩ :: Ss, _ => do
        let B ← checkBlockIsGuarded pos Ss false
        return { B with
          action := B.action.cons (.skip @@ pos)
        }
      | ⟨pos, .print e⟩ :: Ss, _ => do
        let B ← checkBlockIsGuarded pos Ss false
        return { B with
          action := B.action.cons (.print e @@ pos)
        }
      | ⟨pos, .assert e⟩ :: Ss, _ => do
        let B ← checkBlockIsGuarded pos Ss false
        return { B with
          action := B.action.cons (.assert e @@ pos)
        }
      | ⟨pos, .assign bs⟩ :: Ss, _ => match bs with
        | [⟨⟨_, r⟩, e⟩] => do
          let B ← checkBlockIsGuarded pos Ss false
          return { B with
            action := B.action.cons (.assign ⟨r.name, r.args⟩ e @@ pos)
          }
        | [] => unreachable!
        | _ => throw <| .unexpectedParallelAssignment pos
      | ⟨pos, .send ⟨p, c⟩ e⟩ :: Ss, _ => do
        unless c.args.length ≤ 1 do throw <| .channelReferenceTooManyIndices p c.args.length
        if let .some ⟨_, args'⟩ := chans.find? c.name then
          unless (c.args.head?.getD []).length = args'.length do throw <| .channelReferenceExpectedNIndices p c.name ((c.args.head?.map List.length).getD 0) args'.length
          let B ← checkBlockIsGuarded pos Ss true
          return { B with
            action := B.action.cons (.send ⟨c.name, c.args.head?.getD []⟩ e @@ pos)
          }
        else
          throw <| .unknownChannel p c.name
      | ⟨pos, .multicast ⟨p, c⟩ ⟨_, bs, e⟩⟩ :: Ss, _ => do
        if let .some ⟨_, args'⟩ := chans.find? c then
          unless bs.length = args'.length do throw <| .channelReferenceExpectedNIndices p c bs.length args'.length
          let bs ← bs.mapM λ ⟨name, anns, «=|∈», e⟩ ↦ do
            let ⟨τ, «=|∈», e⟩ ← variableHasTypeAndInit? name anns (some ⟨«=|∈», e⟩)
            pure ⟨name.data, τ, «=|∈», e⟩
          let B ← checkBlockIsGuarded pos Ss true
          return { B with
            action := B.action.cons (.multicast c bs e @@ pos)
          }
        else
          throw <| .unknownChannel p c
      -- goto
      | [⟨pos, .goto l⟩], _ => return { precondition := .none, action := GuardedPlusCal.Block.end (.goto l.data @@ pos)}
      -- errors
      | ⟨pos, .while ..⟩ :: _, _ => throw <| .unexpectedWhileStatement pos
      | ⟨pos, .if ..⟩ :: _, _ => throw <| .unexpectedIfStatement pos
      | ⟨pos, .either ..⟩ :: _, _ => throw <| .unexpectedEitherStatement pos
      | ⟨pos, .await ..⟩ :: _, false => throw <| .unexpectedAwaitStatement pos
      | ⟨pos, .receive ..⟩ :: _, false => throw <| .unexpectedReceiveStatement pos
      | ⟨pos, .with ..⟩ :: _, false => throw <| .unexpectedWithStatement pos
      | ⟨pos, .goto ..⟩ :: _, _ => throw <| .unexpectedGotoStatement pos
      | [], _ => throw <| .missingGotoAtEndOfBranch pos

    match stmts with
    | [⟨_, .either blocks⟩] =>
      -- Check that there are no labels in all branches, only instructions
      unless blocks.all (·.all Sum.isRight) do
        let .some (.inl firstLabel) := blocks.flatten.find? Sum.isLeft | unreachable!
        throw <| .unexpectedLabelInEitherBranch firstLabel.segment firstLabel.data
      return ⟨label.data, ← traverse (checkBlockIsGuarded 0 ∘ List.filterMap Sum.getRight?) blocks⟩
    | block => return ⟨label.data, [← checkBlockIsGuarded 0 block]⟩

  /--
    Translates a surface "guarded-valid" `SurfacePlusCal.Algorithm` to an algorithm in our Guarded PlusCal
    sublanguage.
    This merely performs some syntactical checks, while preserving the shape of the code.

    A surface algorithm is "guarded-valid" iff:
    * It contains no global variables.
    * All channels/FIFOs/variables have their types annotated.
    * Every mailbox indicated in the source code may belong to a unique process.
    * Indices of global channels/FIFOs may only have builtin type `Address`.
    * Every atomic block of every thread of every process is of one of the forms
      * `l: PRECOND; B; goto _`
      * `l: either { PRECOND₁; B₁; goto _ } or … or { PRECONDₙ; Bₙ; goto _ }`

      where
      * `PRECOND` is a possibly empty sequence of `receive`/`await`, optionnally nested inside `with` blocks
      * `B` is a possibly empty sequence of instructions which are not `receive`/`await`/`if`/`while`/`with`.
    * Processes that make use of the `receive` instruction may only do so from their indicated mailboxes.
  -/
  def Algorithm.toGuarded (alg : Located (Algorithm Annotation)) :
    m (Located (GuardedPlusCal.Algorithm Typ (Located (Expression Annotation)))) := do
      if alg.data.isFair.data then warn (.uselessFairModifier alg.data.isFair.segment)

      -- Check that no global variables
      unless alg.data.globalState.variables.isEmpty do
        throw <| .unexpectedGlobalVariables (alg.data.globalState.variables[0]!).fst.segment

      -- Check that all channels/FIFOs have an associated type
      let mut channels : Std.HashMap String (Typ × List (Located (Expression Annotation))) := ∅
      let mut fifos : Std.HashMap String (Typ × List (Located (Expression Annotation))) := ∅
      for ⟨isChan, var, anns, dims⟩ in alg.data.globalState.channels.map (true, ·) ++ alg.data.globalState.fifos.map (false, ·) do
        let typ ← channelHasCorrectType? var anns dims
        if isChan then
          channels := channels.insert var.data ⟨typ, dims⟩
        else
          fifos := fifos.insert var.data ⟨typ, dims⟩

      let mut procs : List (GuardedPlusCal.Process Typ (Located (Expression Annotation))) := []
      for proc in alg.data.processes do
        if proc.isFair.data then warn (.uselessFairModifier proc.isFair.segment)

        -- Check that all variables are initialised and have an associated type
        assert! proc.localState.channels.isEmpty
        assert! proc.localState.fifos.isEmpty
        let mut «variables» : Std.HashMap String (Typ × Bool × Located (Expression Annotation)) := ∅
        for ⟨var, anns, init⟩ in proc.localState.variables do
          let ⟨typ, «=|∈», init⟩ ← variableHasTypeAndInit? var anns init
          «variables» := «variables».insert var.data ⟨typ, «=|∈», init⟩

        let allChans := channels.mergeWith (λ _ v _ ↦ v) fifos -- NOTE: in practice, these should be disjoint
        -- Check if process has a mailbox declared
        let mailbox ← processHasMailbox? proc.name proc.ann allChans

        let mut threads := []
        for thread in proc.threads do
          if h : ¬thread.isEmpty ∧ ¬thread[0]!.isLeft then
            throw <| .threadMustStartWithLabel (thread[0]!.getRight <| Sum.not_isLeft.mp h.right).segment

          let blocks := thread.splitBy (λ x y ↦ x.isRight && y.isRight)
                            |>.splitBy (λ | [.inl _], _ => true | _, _ => false)
                            |>.map λ | [[.inl l], inrs] => (⟨l, inrs.filterMap Sum.getRight?⟩ : _ × _)
                                     | _ => unreachable!
          let blocks ← Traversable.traverse (Function.uncurry <| checkAtomicGuardedBlock? allChans mailbox) blocks
          threads := threads.concat blocks

        procs := procs.concat {
          name := proc.name.data
          mailbox
          locals := «variables»
          threads
        }

      return {
        name := alg.data.name.data
        channels
        fifos
        procs
      } <$ alg

  def Algorithm.toGuarded.run (alg : Located (Algorithm Annotation)) :
    Except TranslationError (Located (GuardedPlusCal.Algorithm Typ (Located (Expression Annotation))) × List TranslationWarning) :=
      WriterT.run <| Algorithm.toGuarded alg
end SurfacePlusCal
