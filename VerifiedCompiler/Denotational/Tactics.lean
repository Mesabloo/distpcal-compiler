module

public import VerifiedCompiler.Denotational.StrongRefinement

@[expose] public section

/-!
  Tactics for discharging `StrongRefinement` obligations.

  These are shaped by the framework as it now stands, not by prior art's. Two changes make prior
  art's tactic set the wrong target:

  - **A refinement obligation is a disjunction over two different shapes.** `Terminating` concludes
    *either* "the source takes a matching step" (a source state, a source trace, the post-relation,
    `Rτ`, and membership) *or* "the source aborted having emitted a sequentially consistent prefix"
    (a source trace, `≼[Rτ]`, membership). `Diverging` has its own two. Prior art had neither
    disjunction in this form, so it had nothing to say about choosing between them; `refines_match`
    / `refines_abort` / `refines_diverge` are that choice, with the witness supplied and every
    remaining side condition left as a numbered goal.
  - **Traces are related by `Rτ`, not equal, and prefixes are `≼[Rτ]`, not `<+:`.** A goal that
    used to be closed by `rfl`/`le_rfl` now needs the relation's own lemmas. `trace_rel` and
    `trace_pfx` close the two shapes at a `Rτ` that relates a trace to itself, which is the common
    case for a pass that preserves traces exactly — including this project's own `Guarded2Network`,
    since reception is unobservable there.

  Every tactic here leaves goals rather than searching: the leaf discharge is `sem_side`'s job
  (`Core/NetworkPlusCal/Semantics/Lemmas.lean`), and per plan §3's rule a search tactic runs
  terminally or not at all.
-/

namespace StrongRefinement

/-- The source matches the target's step: supply the source state it steps to, and — with the
two-argument form — the source trace it emits. Leaves the post-relation, the `Rτ` obligation and
the source-membership obligation, in that order.

The trace is a witness, not a goal, so it cannot be left as `_`: an existential's witness has to be
a term by the time the body elaborates. The one-argument form therefore leaves it as the **first**
goal, ahead of the three obligations; prefer the two-argument form wherever the emitted trace is
already known, which for a trace-preserving pass is everywhere. -/
syntax "refines_match " term (", " term)? : tactic

macro_rules
  | `(tactic| refines_match $σ:term) => `(tactic| refine Or.inl ⟨$σ, ?_, ?_, ?_, ?_⟩)
  | `(tactic| refines_match $σ:term, $ε:term) => `(tactic| refine Or.inl ⟨$σ, $ε, ?_, ?_, ?_⟩)

/-- The source aborted instead, having emitted `ε`. Leaves the `≼[Rτ]` obligation and membership in
the source's aborting semantics. Covers both `Terminating`'s right disjunct and the whole of
`Aborting`, which is the same shape without the `Or`. -/
macro "refines_abort " ε:term : tactic =>
  `(tactic| first
    | refine Or.inr ⟨$ε, ?_, ?_⟩
    | refine ⟨$ε, ?_, ?_⟩)

/-- The source diverges too, emitting `ε` — `Diverging`'s left disjunct. Its right disjunct is an
abort, which `refines_abort` already covers. -/
macro "refines_diverge " ε:term : tactic => `(tactic| refine Or.inl ⟨$ε, ?_, ?_⟩)

/-- Close a `Rτ ε' ε` goal when the two traces are literally the same and `Rτ` is reflexive at it —
the shape a trace-preserving pass produces at every leaf. Falls back to an assumption, for a pass
carrying the relatedness as a hypothesis. -/
macro "trace_rel" : tactic => `(tactic| first | rfl | assumption)

/-- Close a `ε' ≼[Rτ] ε` goal the same way: `≼[·]` is extensive with no hypotheses on the relation,
so a related pair is a prefix pair (`Trace.scPrefix_of`). -/
macro "trace_pfx" : tactic =>
  `(tactic| first
    | exact Trace.scPrefix_of rfl
    | exact Trace.scPrefix_of ‹_›
    | apply Trace.scPrefix_of)

/-! ## Validation

  Two examples, one per disjunct, against the identity refinement — enough to catch the failure
  mode these macros exist to prevent: a `refine` whose `?_` count or order drifts from the
  definition it targets. They are cheap and they break loudly if `Terminating`/`Aborting` change
  shape.
-/

/-- The matching disjunct: the target's step is the source's, trace and all. -/
example {α ε : Type} [Monoid ε] (sem : Set (α × ε × α)) :
    StrongRefinement.Terminating (α := α) (β := α) Eq Eq Eq sem ∅ sem := by
  intro σₜ σₜ' ε σₛ sim step
  subst sim
  refines_match σₜ', ε
  · rfl
  · trace_rel
  · exact step

/-- The aborting shape, where the source's trace is a sequentially consistent prefix of the
target's rather than equal to it. -/
example {α ε : Type} [Monoid ε] (sem' : Set (α × ε)) :
    StrongRefinement.Aborting (α := α) (β := α) Eq Eq sem' sem' := by
  intro σₜ ε σₛ sim step
  subst sim
  refines_abort ε
  · trace_pfx
  · exact step

end StrongRefinement

end
