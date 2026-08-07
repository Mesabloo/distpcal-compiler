module

public import Guarded2Network.PlusCal
public import Core.ComputableTLAPlus.Semantics.Interface

@[expose] public section

/-!
  What the sequence expressions `Guarded2Network` builds over `inbox` *mean*.

  `Core/ComputableTLAPlus/Semantics/Interface.lean` keeps the expression layer abstract: `Eval` is a
  relation with no axioms about any particular operator, and the only sequence facts it carries are
  value-level (`seqAppend`, `isSeq`). That is deliberate — Core's semantics has no business naming
  TLA⁺'s `Sequences` module. But this pass compiles a `receive` into `Head`/`Tail`/`Len` calls over
  `inbox` (`Guarded2Network.head`/`.tail`/`.lenGt`), so its refinement proof has to know that
  `Head(inbox)` denotes the first element of what `inbox` holds — a fact about those expressions,
  not about `Eval` in general.

  So the laws live here, in a class the refinement theorems take instance-implicit, and the split
  is: **`ExprSemantics` says what a sequence *value* is, `SeqBuiltins` says what this pass's
  sequence *expressions* evaluate to.** A concrete TLA⁺ evaluator will satisfy both; nothing in
  `Core/` has to mention `Head` to state either.

  Each law is an `↔` against the expression's shape rather than a one-directional evaluation rule,
  because the proof needs both readings: forwards to compute the target's guard from the source's
  channel contents, backwards to rule out a target step the source cannot match.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Memory Typ)

/-- The meaning of `Guarded2Network`'s own sequence expressions, on top of `ExprSemantics`'s
value-level sequence vocabulary. -/
class SeqBuiltins (V : Type) [ExprSemantics V] where
  /-- `Head(e)` denotes the first element of the sequence `e` denotes — and denotes nothing when
  that sequence is empty, which is what makes an empty `inbox` *block* the guard rather than abort
  the branch. -/
  evalHead {M : Memory V} {e : ComputablePlusCal.Expression} {τ : Typ} {v : V} :
    ExprSemantics.Eval M (head τ e) v ↔
      ∃ s vs, ExprSemantics.Eval M e s ∧ ExprSemantics.isSeq s (v :: vs)
  /-- `Tail(e)` denotes the sequence of everything but that first element. -/
  evalTail {M : Memory V} {e : ComputablePlusCal.Expression} {τ : Typ} {t : V} :
    ExprSemantics.Eval M (tail τ e) t ↔
      ∃ s v vs, ExprSemantics.Eval M e s ∧ ExprSemantics.isSeq s (v :: vs) ∧
        ExprSemantics.isSeq t vs
  /-- `Len(e) > n` is a boolean whenever `e` is a sequence, and is `TRUE` exactly when that
  sequence has more than `n` elements. Two clauses rather than one: the guards this pass emits are
  `await`s, and `Statement.aborting`'s `await` case distinguishes "evaluates to a non-boolean"
  (abort) from "evaluates to something other than `TRUE`" (block), so a proof that the compiled
  guard never aborts needs the boolean-ness separately from the truth condition. -/
  evalLenGt {M : Memory V} {e : ComputablePlusCal.Expression} {τ : Typ} {n : Nat} {s : V}
      {vs : List V} :
    ExprSemantics.Eval M e s → ExprSemantics.isSeq s vs →
      ∃ b, ExprSemantics.Eval M (lenGt τ e n) b ∧ ExprSemantics.isBool b ∧
        (b = ExprSemantics.tru ↔ n < vs.length)
  /-- The empty-sequence literal `<<>>` denotes the empty sequence. What
  `Guarded2Network/PlusCal.lean`'s `inbox` initializer (`.seq [] τ`) contributes to the initial
  state, and so what the refinement invariant starts from. -/
  evalSeqNil {M : Memory V} {τ : Typ} {s : V} :
    ExprSemantics.Eval M (.seq [] τ) s ↔ ExprSemantics.isSeq s []

end Guarded2Network

end
