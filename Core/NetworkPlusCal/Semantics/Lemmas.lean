module

meta import CustomPrelude
public import Core.NetworkPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Semantics.Lemmas

@[expose] public section

/-!
  Network PlusCal's own semantic equations, mirroring `GuardedPlusCal.Semantics.Lemmas` at this
  language's `Statement.reducing`/`.aborting`/`.diverging`.

  Everything generic — the `Block.reducing`/`.aborting`/`.diverging` equations — lives in
  `GuardedPlusCal`'s own semantic lemmas and is *used* here, not restated: `LocalState` is shared
  between the two languages unchanged, so a refinement relates a `GuardedPlusCal` block to a
  `NetworkPlusCal` one over that one state type directly, with no encoding to transport across
  first.
-/

namespace NetworkPlusCal

open ComputableTLAPlus (Memory ExprSemantics OperatorEnv Model)
open GuardedPlusCal (Block Behavior Trace FIFOs LocalState Ref selfName EvalStep)

variable {V : Type} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}

/-! # Constructor-intro lemmas — see `GuardedPlusCal.Semantics.Lemmas`'s `Intro` section for why
these exist and why they're duplicated per language rather than shared. No `receive` here — that
is this language's whole point. -/

section Intro

theorem Statement.reducing.with.intro {σ σ' : LocalState V} {ε : Trace V}
    {name ann bound e}
    (h : ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ Finmap.lookup name M = none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
      match bound with
        | true => σ' = ⟨(M.insert name v), F, .none⟩
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = ⟨(M.insert name v'), F, .none⟩) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.reducing.await.intro {σ σ' : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.await e) :=
  h

theorem Statement.reducing.skip.intro {σ σ' : LocalState V} {ε : Trace V}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω NetworkPlusCal.Statement.skip :=
  h

theorem Statement.reducing.goto.intro {σ : LocalState V} {σ' : LocalState V}
    {ε : Trace V} {label}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .some label⟩ ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.goto label) :=
  h

theorem Statement.reducing.print.intro {σ σ' : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F v p, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e v ∧ M.lookup selfName = .some p ∧
      ε = Stream'.Seq.cons (.print p v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.print e) :=
  h

theorem Statement.reducing.assert.intro {σ σ' : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.assert e) :=
  h

theorem Statement.reducing.send.intro {σ σ' : LocalState V} {ε : Trace V} {c e}
    (h : ∃ M F v cpath vs p,
      ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some vs ∧ M.lookup selfName = .some p ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, (F.insert ⟨c.name, cpath⟩ (vs.concat v)), .none⟩ ∧
      ε = Stream'.Seq.cons (.send p ⟨c.name, cpath⟩ v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.send c e) :=
  h

theorem Statement.reducing.assign.intro {σ σ' : LocalState V} {ε : Trace V} {r e}
    (h : ∃ M F M' v rpath,
      ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M', F, .none⟩ ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.assign r e) :=
  h

theorem Statement.aborting.with.intro {σ : LocalState V} {ε : Trace V}
    {name ann bound e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
          | true => False
          | false => ¬ ExprSemantics.isSet v}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.aborting.await.intro {σ : LocalState V} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.await e) :=
  h

theorem Statement.aborting.print.intro {σ : LocalState V} {ε : Trace V} {e}
    (h : ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.print e) :=
  h

theorem Statement.aborting.assert.intro {σ : LocalState V} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.assert e) :=
  h

theorem Statement.aborting.send.intro {σ : LocalState V} {ε : Trace V} {c e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts Ξ Ω M c ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep Ξ Ω M) c.args cpath ∧
          F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.send c e) :=
  h

theorem Statement.aborting.assign.intro {σ : LocalState V} {ε : Trace V} {r e}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts Ξ Ω M r ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
          ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
          Memory.update M r.name rpath v = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.assign r e) :=
  h

end Intro

/-! # Constructor-elim lemmas

  The mirror image of the section above, for the three constructors `Guarded2Network`'s reorder
  lemmas (`Guarded2Network/Lemmas/Reorder.lean`) have to take *apart* rather than build: commuting an
  assignment past a guard means reading both composites' membership down to their components. A
  proof outside this file must not `unfold Statement.reducing` to do that (`LEAN_STYLE.md`), so the
  decomposition is named here, where the definition lives.

  Only the constructors that pass actually needs, and only for this language — the reorder happens
  entirely on the target side. Each is `:= h` for the same reason its `.intro` twin is: the
  hypothesis and the conclusion are the same proposition, one written as `Set` membership and one as
  the body that membership unfolds to. Not in the `sem` rule set: these run backwards, and aesop
  applying an elimination lemma to a goal is not what that set is for.
-/

section Elim

/-- Stated as a bare implication rather than with a named hypothesis, unlike its siblings below:
`bound`'s `match` sits in the *conclusion* here, and a hypothesis mentioning `bound` gets generalized
into that match's motive (`match bound, h with`), which then no longer matches the definition.
`Statement.aborting.with.elim` is the same case. -/
theorem Statement.reducing.with.elim {σ σ' : LocalState V} {ε : Trace V}
    {name ann bound e} :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.with name ann bound e) →
      ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ Finmap.lookup name M = none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
        match bound with
          | true => σ' = ⟨(M.insert name v), F, .none⟩
          | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = ⟨(M.insert name v'), F, .none⟩ :=
  id

theorem Statement.reducing.await.elim {σ σ' : LocalState V} {ε : Trace V} {e}
    (h : ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.await e)) :
    ∃ M F, σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M, F, .none⟩ ∧ ExprSemantics.Eval Ξ Ω M e ExprSemantics.tru ∧ ε = 1 :=
  h

theorem Statement.reducing.assign.elim {σ σ' : LocalState V} {ε : Trace V} {r e}
    (h : ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.assign r e)) :
    ∃ M F M' v rpath,
      ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = ⟨M, F, .none⟩ ∧ σ' = ⟨M', F, .none⟩ ∧ ε = 1 :=
  h

@[inherit_doc Statement.reducing.with.elim]
theorem Statement.aborting.with.elim {σ : LocalState V} {ε : Trace V}
    {name ann bound e} :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.with name ann bound e) →
      (⟨σ, ε⟩ : LocalState V × Trace V) ∈
        {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
        ∪ {⟨σ, ε⟩ | ∃ M F v, ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧ match bound with
            | true => False
            | false => ¬ ExprSemantics.isSet v} :=
  id

theorem Statement.aborting.await.elim {σ : LocalState V} {ε : Trace V} {e}
    (h : ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.await e)) :
    (⟨σ, ε⟩ : LocalState V × Trace V) ∈
      {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ ExprSemantics.Eval Ξ Ω M e v ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1} :=
  h

theorem Statement.aborting.assign.elim {σ : LocalState V} {ε : Trace V} {r e}
    (h : ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.assign r e)) :
    (⟨σ, ε⟩ : LocalState V × Trace V) ∈
      {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, ExprSemantics.Aborts Ξ Ω M e ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts Ξ Ω M r ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
          ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
          Memory.update M r.name rpath v = .none ∧ σ = ⟨M, F, .none⟩ ∧ ε = 1} :=
  h

/-- Which values a `with` may bind, as a predicate on the value instead of a match on `bound`:
`true` (a `let`) admits the expression's own value, `false` (a nondeterministic pick) any member of
it. Neither the memory nor the FIFOs enter that choice, and that is the whole content of the two
`.iff` lemmas below. -/
def Statement.BoundValue (bound : Bool) (u v : V) : Prop :=
  match bound with
  | true => u = v
  | false => ExprSemantics.mem u v

/-- `with`'s reducing case with the `bound` match pulled out into `BoundValue`: one existential over
the value that lands in memory, no case split. `.elim` above mirrors the definition; this mirrors
what consumers actually do with it. `Guarded2Network/Lemmas/Reorder.lean` moves this clause between
two memories in both directions, and without the factoring that is four near-identical blocks. -/
theorem Statement.reducing.with.iff {σ σ' : LocalState V} {ε : Trace V} {name ann bound e} :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing Ξ Ω (NetworkPlusCal.Statement.with name ann bound e) ↔
      ∃ M F v u, ExprSemantics.Eval Ξ Ω M e v ∧ Finmap.lookup name M = none ∧ Statement.BoundValue bound u v ∧
        σ = ⟨M, F, .none⟩ ∧ σ' = ⟨(M.insert name u), F, .none⟩ ∧ ε = 1 := by
  iff_rintro h ⟨M, F, v, u, hv, hname, hbv, rfl, rfl, rfl⟩
  · obtain ⟨M, F, v, hv, hname, rfl, rfl, hb⟩ := Statement.reducing.with.elim h
    cases bound with
    | true => exact ⟨M, F, v, v, hv, hname, rfl, rfl, hb, rfl⟩
    | false =>
      obtain ⟨u, hmem, rfl⟩ := hb
      exact ⟨M, F, v, u, hv, hname, hmem, rfl, rfl, rfl⟩
  · refine Statement.reducing.with.intro ⟨M, F, v, hv, hname, rfl, rfl, ?_⟩
    cases bound with
    | true =>
      obtain rfl : u = v := hbv
      rfl
    | false => exact ⟨u, hbv, rfl⟩

/-- `with`'s aborting case, factored the same way: the state and trace are fixed by the statement,
and what remains is either the guard expression having no value at all or — only under a
nondeterministic pick — its value not being a set. `bound = true` cannot abort past evaluation,
which the definition says with a `False` branch and this says by pinning `bound` to `false`. -/
theorem Statement.aborting.with.iff {σ : LocalState V} {ε : Trace V} {name ann bound e} :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.with name ann bound e) ↔
      ∃ M F, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
        (ExprSemantics.Aborts Ξ Ω M e ∨ ∃ v, ExprSemantics.Eval Ξ Ω M e v ∧ bound = false ∧ ¬ ExprSemantics.isSet v) := by
  iff_rintro h ⟨M, F, rfl, rfl, hd⟩
  · rcases Statement.aborting.with.elim h with ⟨M, F, habort, rfl, rfl⟩ | ⟨M, F, v, hv, rfl, rfl, hb⟩
    · exact ⟨M, F, rfl, rfl, .inl habort⟩
    · cases bound with
      | true => exact hb.elim
      | false => exact ⟨M, F, rfl, rfl, .inr ⟨v, hv, rfl, hb⟩⟩
  · rcases hd with habort | ⟨v, hv, rfl, hset⟩
    · exact Statement.aborting.with.intro (.inl ⟨M, F, habort, rfl, rfl⟩)
    · exact Statement.aborting.with.intro (.inr ⟨M, F, v, hv, rfl, rfl, hset⟩)

/-- `await`'s aborting case with the state and trace matched once instead of once per union member,
leaving a plain disjunction over what actually went wrong. -/
theorem Statement.aborting.await.iff {σ : LocalState V} {ε : Trace V} {e} :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.await e) ↔
      ∃ M F, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
        ((ExprSemantics.Aborts Ξ Ω M e) ∨ ∃ v, ExprSemantics.Eval Ξ Ω M e v ∧ ¬ ExprSemantics.isBool v) := by
  iff_rintro h ⟨M, F, rfl, rfl, hd⟩
  · rcases Statement.aborting.await.elim h with ⟨M, F, habort, rfl, rfl⟩ | ⟨M, F, v, hb, hv, rfl, rfl⟩
    · exact ⟨M, F, rfl, rfl, .inl habort⟩
    · exact ⟨M, F, rfl, rfl, .inr ⟨v, hv, hb⟩⟩
  · rcases hd with habort | ⟨v, hv, hb⟩
    · exact Statement.aborting.await.intro (.inl ⟨M, F, habort, rfl, rfl⟩)
    · exact Statement.aborting.await.intro (.inr ⟨M, F, v, hb, hv, rfl, rfl⟩)

/-- `assign`'s aborting case, same factoring: one state match, then the four ways an assignment can
fail — the target name unbound, the right-hand side without a value, an index expression of the
reference without a value, or the update itself rejected by `updatePath`. Four union members each
repeating `σ = ⟨M, F, .none⟩ ∧ ε = 1` is what makes the raw form expensive to take apart. -/
theorem Statement.aborting.assign.iff {σ : LocalState V} {ε : Trace V} {r e} :
    ⟨σ, ε⟩ ∈ Statement.aborting Ξ Ω (NetworkPlusCal.Statement.assign r e) ↔
      ∃ M F, σ = ⟨M, F, .none⟩ ∧ ε = 1 ∧
        (r.name ∉ M ∨ (ExprSemantics.Aborts Ξ Ω M e) ∨ Ref.pathAborts Ξ Ω M r ∨
          ∃ v rpath, ExprSemantics.Eval Ξ Ω M e v ∧ List.Forall₂ (EvalStep Ξ Ω M) r.args rpath ∧
            Memory.update M r.name rpath v = .none) := by
  iff_rintro h ⟨M, F, rfl, rfl, hd⟩
  · rcases Statement.aborting.assign.elim h with
      ((⟨M, F, hn, rfl, rfl⟩ | ⟨M, F, ha, rfl, rfl⟩) | ⟨M, F, hp, rfl, rfl⟩) |
        ⟨M, F, v, rpath, hv, hpath, hupd, rfl, rfl⟩
    · exact ⟨M, F, rfl, rfl, .inl hn⟩
    · exact ⟨M, F, rfl, rfl, .inr (.inl ha)⟩
    · exact ⟨M, F, rfl, rfl, .inr (.inr (.inl hp))⟩
    · exact ⟨M, F, rfl, rfl, .inr (.inr (.inr ⟨v, rpath, hv, hpath, hupd⟩))⟩
  · rcases hd with hn | ha | hp | ⟨v, rpath, hv, hpath, hupd⟩
    · exact Statement.aborting.assign.intro (.inl (.inl (.inl ⟨M, F, hn, rfl, rfl⟩)))
    · exact Statement.aborting.assign.intro (.inl (.inl (.inr ⟨M, F, ha, rfl, rfl⟩)))
    · exact Statement.aborting.assign.intro (.inl (.inr ⟨M, F, hp, rfl, rfl⟩))
    · exact Statement.aborting.assign.intro (.inr ⟨M, F, v, rpath, hv, hpath, hupd, rfl, rfl⟩)

end Elim

/-! `Statement.listReducing`'s two equations, so a proof about a generated statement run inducts on
the list without reaching through the wrapper to `Block.listReducing`. -/

theorem Statement.listReducing_nil {g : Bool} :
    Statement.listReducing (V := V) Ξ Ω (g := g) [] = Relation.Idle := rfl

theorem Statement.listReducing_cons {g : Bool} {S : ComputableNetworkPlusCal.Statement g false}
    {A : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listReducing (V := V) Ξ Ω (S :: A) =
      Statement.reducing Ξ Ω S ∘ᵣ₂ Statement.listReducing Ξ Ω A := rfl

/-- A statement run splits wherever its list does. `Guarded2Network`'s consumption assignments
accumulate by `++` — one `receive` appends its pair to what earlier ones left — so every proof about
them meets this shape rather than a `cons`. -/
theorem Statement.listReducing_append {g : Bool}
    {A B : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listReducing (V := V) Ξ Ω (A ++ B) =
      Statement.listReducing Ξ Ω A ∘ᵣ₂ Statement.listReducing Ξ Ω B :=
  Block.listReducing_append _

theorem Statement.listAborting_nil {g : Bool} :
    Statement.listAborting (V := V) Ξ Ω (g := g) [] = ∅ := rfl

theorem Statement.listAborting_cons {g : Bool} {S : ComputableNetworkPlusCal.Statement g false}
    {A : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listAborting (V := V) Ξ Ω (S :: A) =
      Statement.aborting Ξ Ω S ∪ Statement.reducing Ξ Ω S ∘ᵣ₁ Statement.listAborting Ξ Ω A := rfl

@[inherit_doc Statement.listReducing_append]
theorem Statement.listAborting_append {g : Bool}
    {A B : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listAborting (V := V) Ξ Ω (A ++ B) =
      Statement.listAborting Ξ Ω A ∪ Statement.listReducing Ξ Ω A ∘ᵣ₁ Statement.listAborting Ξ Ω B :=
  Block.listAborting_append _ _

theorem Statement.listBlocking_nil {g : Bool} :
    Statement.listBlocking (V := V) Ξ Ω (g := g) [] = ∅ := rfl

theorem Statement.listBlocking_cons {g : Bool} {S : ComputableNetworkPlusCal.Statement g false}
    {A : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listBlocking (V := V) Ξ Ω (S :: A) =
      Statement.blocking Ξ Ω S ∪ Statement.reducing Ξ Ω S ∘ᵣ₁ Statement.listBlocking Ξ Ω A := rfl

@[inherit_doc Statement.listReducing_append]
theorem Statement.listBlocking_append {g : Bool}
    {A B : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listBlocking (V := V) Ξ Ω (A ++ B) =
      Statement.listBlocking Ξ Ω A ∪ Statement.listReducing Ξ Ω A ∘ᵣ₁ Statement.listBlocking Ξ Ω B :=
  Block.listAborting_append _ _

/-- A blocked guard emits nothing — the Network twin of
`GuardedPlusCal.Statement.blocking_trace_eq_one`. -/
theorem Statement.blocking_trace_eq_one {b b' : Bool}
    {S : ComputableNetworkPlusCal.Statement b b'} {σ : LocalState V} {ε : Trace V}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ Statement.blocking Ξ Ω S) : ε = 1 := by
  cases S with
  | «with» x ann bound e => obtain ⟨-, -, -, -, -, rfl, -⟩ := h; rfl
  | await e => obtain ⟨-, -, -, -, -, -, -, rfl⟩ := h; rfl
  | _ => exact h.elim

/-- No execution statement blocks, so no block of them does — the Network twin of
`GuardedPlusCal.Statement.blockBlocking_eq_empty`. -/
theorem Statement.blockBlocking_eq_empty {b : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement false) b} :
    Statement.blockBlocking (V := V) Ξ Ω B = ∅ := by
  rw [Statement.blockBlocking, ← GuardedPlusCal.Block.diverging_eq_aborting]
  apply GuardedPlusCal.Block.diverging_eq_empty
  rintro b S
  rfl

/-- A branch is blocked exactly when its precondition is — the Network twin of
`GuardedPlusCal.AtomicBranch.blocking_eq_precondition`. -/
theorem AtomicBranch.blocking_eq_precondition (B : ComputableNetworkPlusCal.AtomicBranch) :
    AtomicBranch.blocking (V := V) Ξ Ω B =
      B.precondition.elim ∅ (Statement.blockBlocking Ξ Ω) := by
  rw [AtomicBranch.blocking]
  cases B.precondition with
  | none => simp only [Option.elim_none, Statement.blockBlocking_eq_empty]
  | some B' =>
    simp only [Option.elim_some, Statement.blockBlocking_eq_empty,
      Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]

/-- A list of Network guards is silent throughout — the twin of
`GuardedPlusCal.Statement.listBlocking_trace_eq_one`. -/
theorem Statement.listBlocking_trace_eq_one
    {A : List (ComputableNetworkPlusCal.Statement true false)} {σ : LocalState V} {ε : Trace V}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ Statement.listBlocking Ξ Ω A) : ε = 1 := by
  induction A generalizing σ ε with
  | nil => rw [Statement.listBlocking_nil] at h; exact h.elim
  | cons S A ih =>
    rw [Statement.listBlocking_cons] at h
    rcases h with h | ⟨σ', ε₁, ε₂, hred, htail, rfl⟩
    · exact Statement.blocking_trace_eq_one h
    · cases S with
      | «with» x ann bound e =>
        obtain ⟨-, -, -, -, -, -, rfl, -⟩ := hred; rw [ih htail, one_mul]
      | await e => obtain ⟨-, -, -, -, -, rfl⟩ := hred; rw [ih htail, one_mul]

/-- A blocked branch emits nothing — the Network twin of
`GuardedPlusCal.AtomicBranch.blocking_trace_eq_one`. -/
theorem AtomicBranch.blocking_trace_eq_one {B : ComputableNetworkPlusCal.AtomicBranch}
    {σ : LocalState V} {ε : Trace V}
    (h : (⟨σ, ε⟩ : LocalState V × Trace V) ∈ AtomicBranch.blocking Ξ Ω B) : ε = 1 := by
  rw [AtomicBranch.blocking_eq_precondition] at h
  cases hpre : B.precondition with
  | none => rw [hpre] at h; exact h.elim
  | some B' =>
    rw [hpre, Option.elim_some, Statement.blockBlocking,
      GuardedPlusCal.Block.aborting_eq_listAborting] at h
    exact Statement.listBlocking_trace_eq_one h

/-- An `await` that fires changes nothing and emits nothing, so its step relation sits inside
`Relation.Idle`. What lets a guard be dropped off the front of a run that fails after it. -/
theorem Statement.reducing_await_le_idle {e : ComputablePlusCal.Expression} :
    Statement.reducing (V := V) Ξ Ω (.await e) ≤ Relation.Idle := by
  rintro ⟨σ, ε, σ'⟩ h
  obtain ⟨M, F, rfl, rfl, -, rfl⟩ := Statement.reducing.await.elim h
  exact ⟨rfl, rfl⟩

/-! # What the flat encoding used to bridge

  Now that `LocalState` itself is flat, a refinement proof needs no translation between an indexed
  and a flat state — `Statement.reducing`/`.aborting` already are the shape `StrongRefinement` wants.
  What survives from the old bridging section are the facts genuinely about this language: no
  statement or block diverges, a branch's `aborting` in the uniform composed shape a
  `StrongRefinement.Comp` produces, and that a step never removes a channel from the map. -/

omit [ExprSemantics V] in
/-- No statement diverges. -/
@[simp] theorem Statement.diverging_eq_empty {b b' : Bool}
    (S : ComputableNetworkPlusCal.Statement b b') : Statement.diverging (V := V) S = ∅ := rfl

/-- No block diverges either — `Statement.diverging_eq_empty` propagated through the fold. -/
@[simp] theorem Statement.blockDiverging_eq_empty {g b : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    Block.diverging (λ ⦃_⦄ ↦ (Statement.diverging (V := V))) (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B =
      ∅ := by
  apply GuardedPlusCal.Block.diverging_eq_empty
  intro _ _; rfl

/-- The `match` on the precondition, discharged — see `GuardedPlusCal.AtomicBranch.aborting_eq`. -/
theorem AtomicBranch.aborting_eq (B : ComputableNetworkPlusCal.AtomicBranch) :
    AtomicBranch.aborting (V := V) Ξ Ω B =
      B.precondition.elim ∅ (Statement.blockAborting Ξ Ω) ∪
        B.precondition.elim Relation.Idle (Statement.blockReducing Ξ Ω) ∘ᵣ₁
          Statement.blockAborting Ξ Ω B.action := by
  rw [AtomicBranch.aborting]
  cases B.precondition with
  | none => rw [Option.elim, Option.elim, Relation.lcomp₁.left_id_eq, Set.empty_union]
  | some => rfl

/-- **A branch ends at the label its terminal `goto` names.** `AtomicBranch.reducing` composes the
precondition onto the action block, and the action block composes its `begin` onto its `last`, so the
final state is whatever `last` produced — and `goto` is the only statement that produces a label at
all (it is the only terminal constructor, `Core/GuardedPlusCal/Syntax.lean`).

Stated with the `goto`'s target supplied rather than existentially, because every caller already
knows it: it is read off the *source* branch through `BranchRefines.last_eq`, and what is wanted is
that the step agrees with it. This is what lets a caller rule out where a compiled block can jump to
without inspecting the run — `Guarded2Network`'s `ProcessRefines.exits`, which needs a compiled
code thread never to land on a receiving thread's label. -/
theorem AtomicBranch.reducing_label {M M' : Memory V} {F F' : FIFOs V} {l label : String}
    {ε : Trace V} {Br : ComputableNetworkPlusCal.AtomicBranch}
    (hlast : Br.action.last = .goto label)
    (h : (⟨⟨M, F, .none⟩, ε, ⟨M', F', .some l⟩⟩ :
      LocalState V × Trace V × LocalState V) ∈ AtomicBranch.reducing Ξ Ω Br) :
    l = label := by
  obtain ⟨_, _, _, _, hblock, _⟩ := h
  obtain ⟨_, _, _, _, hstmt, _⟩ := hblock
  rw [hlast] at hstmt
  obtain ⟨_, _, _, hdone, _⟩ := hstmt
  simpa only [LocalState.label_mk, Option.some.injEq] using congrArg LocalState.label hdone

/-- **A statement never removes a channel.** `send` is the only constructor that writes the map, and
it writes at a key it has just read, so its `insert` only ever overwrites. -/
theorem Statement.reducing_fifos_mem {b b' : Bool}
    {S : ComputableNetworkPlusCal.Statement b b'} {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈ Statement.reducing Ξ Ω S)
    {k : GuardedPlusCal.ChanKey V} (h : σ.fifos.lookup k ≠ .none) :
    σ'.fifos.lookup k ≠ .none := by
  cases S with
  | «with» x ann bound e =>
    obtain ⟨M, F, v, -, -, rfl, -, hb⟩ := step
    cases bound with
    | true => obtain rfl := hb; exact h
    | false => obtain ⟨-, -, rfl⟩ := hb; exact h
  | await e => obtain ⟨M, F, rfl, rfl, -, -⟩ := step; exact h
  | skip => obtain ⟨M, F, rfl, rfl, -⟩ := step; exact h
  | goto label => obtain ⟨M, F, rfl, rfl, -⟩ := step; exact h
  | print e => obtain ⟨M, F, v, p, rfl, rfl, -, -, -⟩ := step; exact h
  | assert e => obtain ⟨M, F, rfl, rfl, -, -⟩ := step; exact h
  | multicast c filter => exact step.elim
  | assign r e => obtain ⟨M, F, M', v, rpath, -, -, -, rfl, rfl, -⟩ := step; exact h
  | send c e =>
    obtain ⟨M, F, v, cpath, vs, p, -, -, hlk, -, rfl, rfl, -⟩ := step
    rw [LocalState.fifos_mk] at h ⊢
    by_cases hk : k = ⟨c.name, cpath⟩
    · subst hk
      rw [Finmap.lookup_insert]
      exact Option.some_ne_none _
    · rwa [Finmap.lookup_insert_of_ne _ hk]

/-- **Nor does a block.** One `Statement.reducing_fifos_mem` per step of the same left-to-right
induction the locality argument runs. -/
theorem Block.reducing_fifos_mem {b b' : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement b) b'} {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      Block.reducing (λ ⦃_⦄ ↦ Statement.reducing Ξ Ω) B)
    {k : GuardedPlusCal.ChanKey V} (h : σ.fifos.lookup k ≠ .none) :
    σ'.fifos.lookup k ≠ .none := by
  induction B using Block.cons_end_induct generalizing σ σ' ε with
  | «end» S =>
    rw [Block.reducing_end] at step
    exact Statement.reducing_fifos_mem step h
  | cons S B IH =>
    rw [Block.reducing_cons] at step
    obtain ⟨σ'', ε₁, ε₂, hhead, htail, rfl⟩ := step
    exact IH htail (Statement.reducing_fifos_mem hhead h)

/-- **Nor a branch**, precondition and action together — a missing precondition being
`Relation.Idle`, which writes nothing. -/
theorem AtomicBranch.reducing_fifos_mem {Br : ComputableNetworkPlusCal.AtomicBranch}
    {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈ AtomicBranch.reducing Ξ Ω Br)
    {k : GuardedPlusCal.ChanKey V} (h : σ.fifos.lookup k ≠ .none) :
    σ'.fifos.lookup k ≠ .none := by
  obtain ⟨σ'', ε₁, ε₂, hpres, hact, rfl⟩ := step
  refine Block.reducing_fifos_mem hact ?_
  match hp : Br.precondition with
  | .none =>
    rw [hp] at hpres
    obtain ⟨rfl, -⟩ := hpres
    exact h
  | .some B' =>
    rw [hp] at hpres
    exact Block.reducing_fifos_mem hpres h

end NetworkPlusCal

end
