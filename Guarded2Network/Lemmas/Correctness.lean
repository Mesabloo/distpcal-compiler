module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Algorithm
public import VerifiedCompiler.Denotational.Correctness

@[expose] public section

/-!
  The pass, as `Compiler.Correctness` states a pass: the compiled algorithm's initial states are
  covered by related source ones, and its behaviour refines the source's. Everything below this file
  proves it; this file is only the packaging.

  **Two program types, and both are forced.**

  `SourceProgram` bundles an algorithm with the front-end facts about it. `Compiler.Correctness`
  quantifies over *every* program of its source type, so a hypothesis hoisted outside — `∀ algo,
  AlgorithmFresh mbox c₀ algo` — would ask one mailbox assignment to be fresh for every algorithm at
  once, which no assignment is. The statement would hold vacuously and say nothing. Bundling puts
  each algorithm next to its own `mbox`/`c₀`, which is how every rung below already reads them.

  `TargetProgram` is a phantom index: the pass's output is an algorithm and nothing more, but the
  framework's `Reduce`/`Abort`/`Diverge` classes take the semantics as an `outParam`, so the program
  type has to determine the value universe its semantics is taken in. `ComputableNetworkPlusCal.
  Algorithm` does not mention `V`; `TargetProgram V` does.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Memory)
open GuardedPlusCal (AlgState ChanKey FIFOs Instances ProcState Trace)

variable {V : Type} [ExprSemantics V] [SeqBuiltins V]

/-! # The two program types -/

/-- **Everything the front end owes this pass, at one algorithm.** Four syntactic conditions and one
semantic: `AlgorithmFresh` (the generated `inbox` collides with nothing the source uses),
`MailboxUsed` (a declared mailbox is one its process receives on, `checkReceiveChannels`),
`LabelsHygienic` (no source label is one the pass could generate), `Nodup` on the process names
(`duplicateProcessName`) — and `InitKeys`, the key a receiving instance starts on, which is the one
thing here no checker establishes (`PLAN.md` §5.2a).

`keys` quantifies over the FIFO map because `InitKeys.declared` is stated against it: which map an
initial state carries is not fixed until that state is chosen. The other two clauses do not mention
it, so nothing is lost by letting the witness depend on it. -/
structure FrontEnd (mbox : String → String → Mailbox)
  (c₀ : String → ComputableGuardedPlusCal.Ref) (algo : ComputableGuardedPlusCal.Algorithm) :
    Prop where
  /-- The generated `inbox` is fresh for every branch of every process. -/
  fresh : AlgorithmFresh mbox c₀ algo
  /-- A process with a mailbox is a process that receives. -/
  used : MailboxUsed mbox algo
  /-- No source label is one the pass could have generated. -/
  hygienic : ∀ p ∈ algo.processes, LabelsHygienic p
  /-- No two processes share a name. -/
  names : (algo.processes.map (·.name)).Nodup
  /-- Each receiving instance starts on a key that resolves, exists, and is its own. -/
  keys : ∀ F : FIFOs V, ∃ key, InitKeys (V := V) c₀ algo F key

/-- **A source program of this pass**: an algorithm, the mailbox and channel assignment its
processes are read at, and the front end's facts about all three. See this file's module doc for why
the facts are bundled into the type rather than hoisted into a hypothesis. -/
structure SourceProgram (V : Type) [ExprSemantics V] : Type where
  /-- The algorithm itself. -/
  algo : ComputableGuardedPlusCal.Algorithm
  /-- Which mailbox each process name gets, as a function of the name the pass will generate. -/
  mbox : String → String → Mailbox
  /-- Which channel each process name receives on. -/
  c₀ : String → ComputableGuardedPlusCal.Ref
  /-- And the front end's guarantees about them. -/
  wellFormed : FrontEnd (V := V) mbox c₀ algo

/-- **A target program of this pass** — a compiled algorithm, indexed by the value universe its
semantics is taken in. The index is phantom; see this file's module doc for why it is there. -/
def TargetProgram (V : Type) : Type := ComputableNetworkPlusCal.Algorithm

/-! # Their semantics, as the framework indexes it -/

instance : Reduce (SourceProgram V)
    (Set (AlgState (String × V) V × Trace V × AlgState (String × V) V)) :=
  ⟨λ s ↦ (GuardedPlusCal.Algorithm.algebra s.algo).reducing⟩

instance : Abort (SourceProgram V) (Set (AlgState (String × V) V × Trace V)) :=
  ⟨λ s ↦ (GuardedPlusCal.Algorithm.algebra s.algo).aborting⟩

instance : Diverge (SourceProgram V) (Set (AlgState (String × V) V × Trace V)) :=
  ⟨λ s ↦ (GuardedPlusCal.Algorithm.algebra s.algo).diverging⟩

instance : Reduce (TargetProgram V)
    (Set (AlgState (String × V) V × Trace V × AlgState (String × V) V)) :=
  ⟨λ algo' ↦ (NetworkPlusCal.Algorithm.algebra algo').reducing⟩

instance : Abort (TargetProgram V) (Set (AlgState (String × V) V × Trace V)) :=
  ⟨λ algo' ↦ (NetworkPlusCal.Algorithm.algebra algo').aborting⟩

instance : Diverge (TargetProgram V) (Set (AlgState (String × V) V × Trace V)) :=
  ⟨λ algo' ↦ (NetworkPlusCal.Algorithm.algebra algo').diverging⟩

/-- The pass itself, at those two types. `Algorithm.toNetwork` never looks at anything a
`SourceProgram` carries beyond the algorithm — the rest is what the *proof* reads. -/
def compile (s : SourceProgram V) : G2NM (TargetProgram V) :=
  ComputableGuardedPlusCal.Algorithm.toNetwork s.algo

/-! # The theorem -/

open Std.Do in
/-- **`Guarded2Network` is a correct pass.** The whole development meets here.

The relation is `algRelatesTo` at the mailbox and receiving labels read off the *compiled*
algorithm — which is why `Compiler.Correctness` indexes its relation by the target program, and why
both halves live inside one triple. The `init` half is `Algorithm.init_refines`, the refinement half
is `Algorithm.toNetwork_refines`, and `triple_forall` is what lets one run of the pass answer both
at every prefix function at once. -/
theorem correct [DecidableEq V] :
    Compiler.Correctness
      (λ (_ : SourceProgram V) (algo' : TargetProgram V) ↦
        algRelatesTo (V := V) (procMailbox algo') (procRxLabels algo'))
      compile (λ s ↦ GuardedPlusCal.Algorithm.init s.algo) NetworkPlusCal.Algorithm.init where
  correct s := by
    unfold compile
    refine triple_forall (ι := ChanKey V → List V)
      (λ pref ↦ Algorithm.toNetwork_spec (V := V) (pref := pref) s.wellFormed.fresh) ?_
    intro algo' h
    refine ⟨?_, algRelatesTo.refines ?_⟩
    · rintro ⟨Ps', F⟩ hinit
      obtain ⟨key, hkeys⟩ := s.wellFormed.keys F
      obtain ⟨Ps, hsrc, hrel⟩ := Algorithm.init_refines (h λ _ ↦ []).2 (h λ _ ↦ []).1
        s.wellFormed.used s.wellFormed.hygienic s.wellFormed.names hkeys hinit
      exact ⟨⟨Ps, F⟩, hsrc, hrel⟩
    · exact algebraRefines (λ pref ↦ (h pref).2) s.wellFormed.used s.wellFormed.fresh
        s.wellFormed.hygienic

/-- And so it is correct in the composable form, which is what a whole-pipeline statement chains
(`Compiler.Correct.comp`). -/
theorem correct' [DecidableEq V] :
    Compiler.Correct compile (λ s : SourceProgram V ↦ GuardedPlusCal.Algorithm.init s.algo)
      NetworkPlusCal.Algorithm.init :=
  correct.toCorrect

assert_no_sorry correct'

end Guarded2Network

end
