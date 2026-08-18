module

meta import CustomPrelude
public import Core.NetworkPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Semantics.Lemmas

@[expose] public section

/-!
  Network PlusCal's half of the flat state encoding a refinement proof is stated over.

  Everything generic lives in Guarded PlusCal's own semantic lemmas and is *used* here, not
  restated: the `Block.reducing`/`.aborting`/`.diverging` equations, the `*_map` relabelling lemmas,
  and `LocalState'`/`toLocalState'`/`toLocalState'_inj` itself — the two languages share one state
  space, so they share its flat encoding too. What
  is genuinely per-language is the primed statement semantics, since that is defined from this
  language's own `Statement.reducing`.

  That sharing is the point: a refinement relates a `GuardedPlusCal` block to a `NetworkPlusCal`
  one over a single `LocalState'`, with no isomorphism to transport across first.
-/

namespace NetworkPlusCal

open ComputableTLAPlus (Memory ExprSemantics)
open GuardedPlusCal (Block Behavior Trace FIFOs LocalState LocalState' Ref selfName EvalStep)

variable {V : Type} [ExprSemantics V]

/-! # Constructor-intro lemmas — see `GuardedPlusCal.Semantics.Lemmas`'s `Intro` section for why
these exist and why they're duplicated per language rather than shared. No `receive` here — that
is this language's whole point. -/

section Intro

theorem Statement.reducing.with.intro {σ σ' : LocalState V false} {ε : Trace V}
    {name ann bound e}
    (h : ∃ M F v, M ⊢ e ⇒ v ∧ Finmap.lookup name M = none ∧ σ = .running M F ∧ ε = 1 ∧
      match bound with
        | true => σ' = .running (M.insert name v) F
        | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = .running (M.insert name v') F) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.reducing.await.intro {σ σ' : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.await e) :=
  h

theorem Statement.reducing.skip.intro {σ σ' : LocalState V false} {ε : Trace V}
    (h : ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing NetworkPlusCal.Statement.skip :=
  h

theorem Statement.reducing.goto.intro {σ : LocalState V false} {σ' : LocalState V true}
    {ε : Trace V} {label}
    (h : ∃ M F, σ = .running M F ∧ σ' = .done M F label ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.goto label) :=
  h

theorem Statement.reducing.print.intro {σ σ' : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F v p, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ v ∧ M.lookup selfName = .some p ∧
      ε = Stream'.Seq.cons (.print p v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.print e) :=
  h

theorem Statement.reducing.assert.intro {σ σ' : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ ExprSemantics.tru ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.assert e) :=
  h

theorem Statement.reducing.send.intro {σ σ' : LocalState V false} {ε : Trace V} {c e}
    (h : ∃ M F v cpath vs p,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) c.args cpath ∧
      F.lookup ⟨c.name, cpath⟩ = .some vs ∧ M.lookup selfName = .some p ∧
      σ = .running M F ∧ σ' = .running M (F.insert ⟨c.name, cpath⟩ (vs.concat v)) ∧
      ε = Stream'.Seq.cons (.send p ⟨c.name, cpath⟩ v) 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.send c e) :=
  h

theorem Statement.reducing.assign.intro {σ σ' : LocalState V false} {ε : Trace V} {r e}
    (h : ∃ M F M' v rpath,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = .running M F ∧ σ' = .running M' F ∧ ε = 1) :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.assign r e) :=
  h

theorem Statement.aborting.with.intro {σ : LocalState V false} {ε : Trace V}
    {name ann bound e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1 ∧ match bound with
          | true => False
          | false => ¬ ExprSemantics.isSet v}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.with name ann bound e) :=
  h

theorem Statement.aborting.await.intro {σ : LocalState V false} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.await e) :=
  h

theorem Statement.aborting.print.intro {σ : LocalState V false} {ε : Trace V} {e}
    (h : ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1) :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.print e) :=
  h

theorem Statement.aborting.assert.intro {σ : LocalState V false} {ε : Trace V} {e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, v ≠ ExprSemantics.tru ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.assert e) :=
  h

theorem Statement.aborting.send.intro {σ : LocalState V false} {ε : Trace V} {c e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts M c ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F cpath, List.Forall₂ (EvalStep M) c.args cpath ∧
          F.lookup ⟨c.name, cpath⟩ = .none ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.send c e) :=
  h

theorem Statement.aborting.assign.intro {σ : LocalState V false} {ε : Trace V} {r e}
    (h : (⟨σ, ε⟩ : LocalState V false × Trace V) ∈ {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts M r ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
          M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
          Memory.update M r.name rpath v = .none ∧ σ = .running M F ∧ ε = 1}) :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.assign r e) :=
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
theorem Statement.reducing.with.elim {σ σ' : LocalState V false} {ε : Trace V}
    {name ann bound e} :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.with name ann bound e) →
      ∃ M F v, M ⊢ e ⇒ v ∧ Finmap.lookup name M = none ∧ σ = .running M F ∧ ε = 1 ∧
        match bound with
          | true => σ' = .running (M.insert name v) F
          | false => ∃ v', ExprSemantics.mem v' v ∧ σ' = .running (M.insert name v') F :=
  id

theorem Statement.reducing.await.elim {σ σ' : LocalState V false} {ε : Trace V} {e}
    (h : ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.await e)) :
    ∃ M F, σ = .running M F ∧ σ' = .running M F ∧ M ⊢ e ⇒ ExprSemantics.tru ∧ ε = 1 :=
  h

theorem Statement.reducing.assign.elim {σ σ' : LocalState V false} {ε : Trace V} {r e}
    (h : ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.assign r e)) :
    ∃ M F M' v rpath,
      M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
      Memory.update M r.name rpath v = .some M' ∧
      σ = .running M F ∧ σ' = .running M' F ∧ ε = 1 :=
  h

@[inherit_doc Statement.reducing.with.elim]
theorem Statement.aborting.with.elim {σ : LocalState V false} {ε : Trace V}
    {name ann bound e} :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.with name ann bound e) →
      (⟨σ, ε⟩ : LocalState V false × Trace V) ∈
        {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
        ∪ {⟨σ, ε⟩ | ∃ M F v, M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1 ∧ match bound with
            | true => False
            | false => ¬ ExprSemantics.isSet v} :=
  id

theorem Statement.aborting.await.elim {σ : LocalState V false} {ε : Trace V} {e}
    (h : ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.await e)) :
    (⟨σ, ε⟩ : LocalState V false × Trace V) ∈
      {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v, ¬ ExprSemantics.isBool v ∧ M ⊢ e ⇒ v ∧ σ = .running M F ∧ ε = 1} :=
  h

theorem Statement.aborting.assign.elim {σ : LocalState V false} {ε : Trace V} {r e}
    (h : ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.assign r e)) :
    (⟨σ, ε⟩ : LocalState V false × Trace V) ∈
      {⟨σ, ε⟩ | ∃ M F, r.name ∉ M ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, M ⊢ e ↯ ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F, Ref.pathAborts M r ∧ σ = .running M F ∧ ε = 1}
      ∪ {⟨σ, ε⟩ | ∃ M F v rpath,
          M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
          Memory.update M r.name rpath v = .none ∧ σ = .running M F ∧ ε = 1} :=
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
theorem Statement.reducing.with.iff {σ σ' : LocalState V false} {ε : Trace V} {name ann bound e} :
    ⟨σ, ε, σ'⟩ ∈ Statement.reducing (NetworkPlusCal.Statement.with name ann bound e) ↔
      ∃ M F v u, M ⊢ e ⇒ v ∧ Finmap.lookup name M = none ∧ Statement.BoundValue bound u v ∧
        σ = .running M F ∧ σ' = .running (M.insert name u) F ∧ ε = 1 := by
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
theorem Statement.aborting.with.iff {σ : LocalState V false} {ε : Trace V} {name ann bound e} :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.with name ann bound e) ↔
      ∃ M F, σ = .running M F ∧ ε = 1 ∧
        (M ⊢ e ↯ ∨ ∃ v, M ⊢ e ⇒ v ∧ bound = false ∧ ¬ ExprSemantics.isSet v) := by
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
theorem Statement.aborting.await.iff {σ : LocalState V false} {ε : Trace V} {e} :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.await e) ↔
      ∃ M F, σ = .running M F ∧ ε = 1 ∧
        ((M ⊢ e ↯) ∨ ∃ v, M ⊢ e ⇒ v ∧ ¬ ExprSemantics.isBool v) := by
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
repeating `σ = .running M F ∧ ε = 1` is what makes the raw form expensive to take apart. -/
theorem Statement.aborting.assign.iff {σ : LocalState V false} {ε : Trace V} {r e} :
    ⟨σ, ε⟩ ∈ Statement.aborting (NetworkPlusCal.Statement.assign r e) ↔
      ∃ M F, σ = .running M F ∧ ε = 1 ∧
        (r.name ∉ M ∨ (M ⊢ e ↯) ∨ Ref.pathAborts M r ∨
          ∃ v rpath, M ⊢ e ⇒ v ∧ List.Forall₂ (EvalStep M) r.args rpath ∧
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

-- Leaf discharge for `sem_side` (see below).
attribute [aesop safe apply (rule_sets := [sem])]
  Statement.reducing.with.intro Statement.reducing.await.intro
  Statement.reducing.skip.intro Statement.reducing.goto.intro Statement.reducing.print.intro
  Statement.reducing.assert.intro Statement.reducing.send.intro Statement.reducing.assign.intro
  Statement.aborting.with.intro Statement.aborting.await.intro
  Statement.aborting.print.intro Statement.aborting.assert.intro Statement.aborting.send.intro
  Statement.aborting.assign.intro

/-! `Statement.listReducing`'s two equations, so a proof about a generated statement run inducts on
the list without reaching through the wrapper to `Block.listReducing`. -/

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listReducing_nil {g : Bool} :
    Statement.listReducing (V := V) (g := g) [] = Relation.Idle := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listReducing_cons {g : Bool} {S : ComputableNetworkPlusCal.Statement g false}
    {A : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listReducing (V := V) (S :: A) =
      Statement.reducing S ∘ᵣ₂ Statement.listReducing A := rfl

/-- `Statement.reducing` in the flat encoding — see `GuardedPlusCal.Statement.reducing'`. -/
def Statement.reducing' {b b' : Bool} (S : ComputableNetworkPlusCal.Statement b b') :
    Set (LocalState' V × Trace V × LocalState' V) :=
  {⟨⟨M, F, l⟩, ε, ⟨M', F', l'⟩⟩ | ∃ σ' : LocalState V b',
    l = Option.none ∧ ⟨LocalState.running M F, ε, σ'⟩ ∈ Statement.reducing S ∧ match b', σ' with
      | true, σ' => ∃ l'', σ' = LocalState.done M' F' l'' ∧ l' = Option.some l''
      | false, σ' => σ' = LocalState.running M' F' ∧ l' = Option.none}

@[inherit_doc Statement.reducing']
def Statement.aborting' {b b' : Bool} (S : ComputableNetworkPlusCal.Statement b b') :
    Set (LocalState' V × Trace V) :=
  {⟨⟨M, F, l⟩, ε⟩ | l = Option.none ∧ ⟨LocalState.running M F, ε⟩ ∈ Statement.aborting S}

@[inherit_doc Statement.reducing']
def Statement.diverging' {b b' : Bool} (S : ComputableNetworkPlusCal.Statement b b') :
    Set (LocalState' V × Trace V) :=
  {⟨⟨M, F, l⟩, ε⟩ | l = Option.none ∧ ⟨LocalState.running M F, ε⟩ ∈ Statement.diverging S}

/-! `Statement.listReducing`/`.listAborting` in the flat encoding, with their two equations. A
generated statement run is what `Guarded2Network` prepends to an action block, and the refinement
invariant it is proved against lives on `LocalState'`. -/

@[inherit_doc Statement.reducing']
def Statement.listReducing' {g : Bool} (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState' V × Trace V × LocalState' V) :=
  Block.listReducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') A

@[inherit_doc Statement.reducing']
def Statement.listAborting' {g : Bool} (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState' V × Trace V) :=
  Block.listAborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
    (λ ⦃_⦄ ↦ Statement.reducing') A

@[inherit_doc Statement.reducing']
def Statement.listDiverging' {g : Bool} (A : List (ComputableNetworkPlusCal.Statement g false)) :
    Set (LocalState' V × Trace V) :=
  Block.listAborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
    (λ ⦃_⦄ ↦ Statement.reducing') A

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listReducing'_nil {g : Bool} :
    Statement.listReducing' (V := V) (g := g) [] = Relation.Idle := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listReducing'_cons {g : Bool} {S : ComputableNetworkPlusCal.Statement g false}
    {A : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listReducing' (V := V) (S :: A) =
      Statement.reducing' S ∘ᵣ₂ Statement.listReducing' A := rfl

/-- A statement run splits wherever its list does. `Guarded2Network`'s consumption assignments
accumulate by `++` — one `receive` appends its pair to what earlier ones left — so every proof about
them meets this shape rather than a `cons`. Named at this instantiation because that is how it is
used; the content is `Block.listReducing_append`. -/
theorem Statement.listReducing'_append {g : Bool}
    {A B : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listReducing' (V := V) (A ++ B) =
      Statement.listReducing' A ∘ᵣ₂ Statement.listReducing' B :=
  Block.listReducing_append _

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listAborting'_nil {g : Bool} :
    Statement.listAborting' (V := V) (g := g) [] = ∅ := rfl

@[aesop safe apply (rule_sets := [sem])]
theorem Statement.listAborting'_cons {g : Bool} {S : ComputableNetworkPlusCal.Statement g false}
    {A : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listAborting' (V := V) (S :: A) =
      Statement.aborting' S ∪ Statement.reducing' S ∘ᵣ₁ Statement.listAborting' A := rfl

@[inherit_doc Statement.listReducing'_append]
theorem Statement.listAborting'_append {g : Bool}
    {A B : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listAborting' (V := V) (A ++ B) =
      Statement.listAborting' A ∪ Statement.listReducing' A ∘ᵣ₁ Statement.listAborting' B :=
  Block.listAborting_append _ _

/-- An `await` that fires changes nothing and emits nothing, so its step relation sits inside
`Relation.Idle`. What lets a guard be dropped off the front of a run that fails after it. -/
theorem Statement.reducing'_await_le_idle {e : ComputablePlusCal.Expression} :
    Statement.reducing' (V := V) (.await e) ≤ Relation.Idle := by
  rintro ⟨⟨M, F, l⟩, ε, ⟨M', F', l'⟩⟩ ⟨_, rfl, hred, rfl, rfl⟩
  obtain ⟨M₀, F₀, hM, hM', -, rfl⟩ := Statement.reducing.await.elim hred
  injection hM with hM hF
  injection hM' with hM'' hF''
  subst hM; subst hF; subst hM''; subst hF''
  exact ⟨rfl, rfl⟩

omit [ExprSemantics V] in
/-- No statement diverges — see `GuardedPlusCal.Statement.diverging'_eq_empty`. -/
@[simp] theorem Statement.diverging'_eq_empty {b b' : Bool}
    (S : ComputableNetworkPlusCal.Statement b b') :
    Statement.diverging' (V := V) S = ∅ := by
  ext ⟨⟨M, F, l⟩, ε⟩
  iff_rintro ⟨-, hd⟩ hd
  · exact hd.elim
  · exact hd.elim

/-- No *list* of statements diverges — see `GuardedPlusCal.Statement.listDiverging'_eq_empty`. -/
@[simp] theorem Statement.listDiverging'_eq_empty {g : Bool}
    {A : List (ComputableNetworkPlusCal.Statement g false)} :
    Statement.listDiverging' (V := V) A = ∅ := by
  induction A with
  | nil => rfl
  | cons S A IH =>
    show Statement.diverging' S ∪ Statement.reducing' S ∘ᵣ₁ Statement.listDiverging' A = ∅
    rw [Statement.diverging'_eq_empty, IH, Relation.lcomp₁.right_empty_eq_empty, Set.union_self]

/-- No *block* diverges either — the same fact at block shape, which is how a branch-level
refinement gets its target diverging component as `∅` rather than as something to carry. -/
@[simp] theorem Block.diverging'_eq_empty {g b : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
        (λ ⦃_⦄ ↦ Statement.reducing') B = ∅ := by
  show Statement.listDiverging' B.begin ∪ _ ∘ᵣ₁ Statement.diverging' B.last = ∅
  rw [Statement.listDiverging'_eq_empty, Statement.diverging'_eq_empty,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_self]

private theorem Statement.reducing'_eq_map {b b' : Bool}
    (S : ComputableNetworkPlusCal.Statement b b') :
    Statement.reducing' (V := V) S =
      Prod.map₃ LocalState.toLocalState' id LocalState.toLocalState' '' Statement.reducing S := by
  ext ⟨⟨M, F, l⟩, e, ⟨M', F', l'⟩⟩
  constructor
  · cases b' with
    | false =>
      rintro ⟨⟨M'', F''⟩, rfl, sem, _|_, rfl⟩
      exists _, sem
    | true =>
      rintro ⟨⟨M'', F'', l''⟩, rfl, sem, _, _|_, rfl⟩
      exists _, sem
  · cases b' with
    | false =>
      rintro ⟨⟨⟨_, _⟩, _, ⟨_, _⟩⟩, sem, _|_⟩
      exists _, rfl, sem
    | true =>
      rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _, l⟩⟩, sem, _|_⟩
      exists _, rfl, sem, l

private theorem Statement.aborting'_eq_map {b b' : Bool}
    (S : ComputableNetworkPlusCal.Statement b b') :
    Statement.aborting' (V := V) S =
      Prod.map LocalState.toLocalState' id '' Statement.aborting S := by
  ext ⟨⟨M, F, l⟩, e⟩
  iff_rintro ⟨rfl, sem⟩ ⟨⟨⟨_⟩, _⟩, _, _|_⟩
  · exists _, sem
  · trivial

-- `Statement.diverging` is `∅` regardless of the expression semantics, so this one does not use it.
omit [ExprSemantics V] in
private theorem Statement.diverging'_eq_map {b b' : Bool}
    (S : ComputableNetworkPlusCal.Statement b b') :
    Statement.diverging' (V := V) S =
      Prod.map LocalState.toLocalState' id '' Statement.diverging S := by
  ext ⟨⟨M, F, l⟩, e⟩
  iff_rintro ⟨rfl, sem⟩ ⟨⟨⟨_⟩, _⟩, _, _|_⟩
  · exists _, sem
  · trivial

/-- An equation between two two-step compositions survives the move to the flat encoding.

Item 7's reorder lemmas are proved on `Statement.reducing`, where the intro/elim lemmas live;
`relatesTo` and `StrongRefinement` are stated on `LocalState'`. This is the bridge, and
`Relation.lcomp₂.image` plus `LocalState.toLocalState'_inj` is all it takes — the injectivity being
what stops the flattened composition from acquiring middle states the original never had. -/
theorem Statement.reducing'_lcomp₂_congr {g₁ g₂ g₃ g₄ : Bool}
    {S₁ : ComputableNetworkPlusCal.Statement g₁ false}
    {S₂ : ComputableNetworkPlusCal.Statement g₂ false}
    {T₁ : ComputableNetworkPlusCal.Statement g₃ false}
    {T₂ : ComputableNetworkPlusCal.Statement g₄ false}
    (h : Statement.reducing (V := V) S₁ ∘ᵣ₂ Statement.reducing S₂ =
      Statement.reducing T₁ ∘ᵣ₂ Statement.reducing T₂) :
    Statement.reducing' (V := V) S₁ ∘ᵣ₂ Statement.reducing' S₂ =
      Statement.reducing' T₁ ∘ᵣ₂ Statement.reducing' T₂ := by
  rw [Statement.reducing'_eq_map, Statement.reducing'_eq_map, Statement.reducing'_eq_map,
    Statement.reducing'_eq_map, ← Relation.lcomp₂.image (LocalState.toLocalState'_inj (b := false)),
    ← Relation.lcomp₂.image (LocalState.toLocalState'_inj (b := false)), h]

/-- The aborting counterpart of `Statement.reducing'_lcomp₂_congr`, over the shape a two-step run's
aborts have: either the first statement aborts, or it runs and the second does.

An *inclusion* rather than an equation, because that is what the reorder lemmas prove — a guard can
block where an assignment cannot, so the two sides are ordered and not equal. Injectivity is still
what carries it, `Set.image_mono` doing the rest. -/
theorem Statement.aborting'_lcomp₁_congr {g₁ g₂ g₃ g₄ : Bool}
    {S₁ : ComputableNetworkPlusCal.Statement g₁ false}
    {S₂ : ComputableNetworkPlusCal.Statement g₂ false}
    {T₁ : ComputableNetworkPlusCal.Statement g₃ false}
    {T₂ : ComputableNetworkPlusCal.Statement g₄ false}
    (h : Statement.aborting (V := V) S₁ ∪ Statement.reducing S₁ ∘ᵣ₁ Statement.aborting S₂ ≤
      Statement.aborting T₁ ∪ Statement.reducing T₁ ∘ᵣ₁ Statement.aborting T₂) :
    Statement.aborting' (V := V) S₁ ∪ Statement.reducing' S₁ ∘ᵣ₁ Statement.aborting' S₂ ≤
      Statement.aborting' T₁ ∪ Statement.reducing' T₁ ∘ᵣ₁ Statement.aborting' T₂ := by
  rw [Statement.aborting'_eq_map, Statement.aborting'_eq_map, Statement.aborting'_eq_map,
    Statement.aborting'_eq_map, Statement.reducing'_eq_map, Statement.reducing'_eq_map,
    ← Relation.lcomp₁.image (LocalState.toLocalState'_inj (b := false)),
    ← Relation.lcomp₁.image (LocalState.toLocalState'_inj (b := false)),
    ← Set.image_union, ← Set.image_union]
  exact Set.image_mono h

theorem Block.reducing'_eq_map {g b : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map₃ LocalState.toLocalState' id LocalState.toLocalState' ''
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.reducing_map _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.reducing'_eq_map S]

theorem Block.aborting'_eq_map {g b : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
        (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map LocalState.toLocalState' id ''
        Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.aborting_map _ _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.aborting'_eq_map S]
  conv_rhs => enter [2, b, S]; rw [← Statement.reducing'_eq_map S]

theorem Block.diverging'_eq_map {g b : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
        (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map LocalState.toLocalState' id ''
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.diverging_map _ _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.diverging'_eq_map S]
  conv_rhs => enter [2, b, S]; rw [← Statement.reducing'_eq_map S]

/-! The membership-level corollaries, mirroring `GuardedPlusCal.LocalState.sem_glue₁` and friends. -/

theorem LocalState.sem_glue₁ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {l : String}
    {ε : Trace V} {B : Block (ComputableNetworkPlusCal.Statement g) true} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.done M₂ F₂ l⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, some l)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

theorem LocalState.sem_glue₂ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableNetworkPlusCal.Statement g) false} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.running M₂ F₂⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, none)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

theorem LocalState.abort_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.aborting'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

theorem LocalState.div_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.diverging'_eq_map, Set.mem_image]
  iff_rintro sem ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩
  · exists _, sem
  · exact sem

/-! # `AtomicBranch`/`AtomicBlock`, flat

  `AtomicBlock` only exists on this side (`Semantics/Denotational.lean`'s module doc for why).
  Mirrors `Statement.blockReducing`/`AtomicBranch.reducing` (`Semantics/Denotational.lean`) at the
  flat encoding, built from the primed leaf functions above rather than proved equal to an
  image of the indexed version after the fact — the indexed `AtomicBranch.reducing`/etc. are
  themselves already exactly "precondition, then action" by definition, so no separate
  `sem_eq`/`abort_eq`/`div_eq` step is needed. -/

/-- `AtomicBranch.reducing` in the flat encoding. -/
def AtomicBranch.reducing' (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState' V × Trace V × LocalState' V) :=
  B.precondition.elim Relation.Idle
    (Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing')) ∘ᵣ₂
    Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B.action

@[inherit_doc AtomicBranch.reducing']
def AtomicBranch.aborting' (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState' V × Trace V) :=
  match B.precondition with
  | .none => Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
      (λ ⦃_⦄ ↦ Statement.reducing') B.action
  | .some B' =>
    Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
        (λ ⦃_⦄ ↦ Statement.reducing') B' ∪
      Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B' ∘ᵣ₁
        Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
          (λ ⦃_⦄ ↦ Statement.reducing') B.action

@[inherit_doc AtomicBranch.reducing']
def AtomicBranch.diverging' (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState' V × Trace V) :=
  match B.precondition with
  | .none => Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
      (λ ⦃_⦄ ↦ Statement.reducing') B.action
  | .some B' =>
    Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
        (λ ⦃_⦄ ↦ Statement.reducing') B' ∪
      Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B' ∘ᵣ₁
        Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
          (λ ⦃_⦄ ↦ Statement.reducing') B.action

/-- The `match` on the precondition, discharged: `.none` composes with the identity relation and
contributes no aborting runs of its own, which is exactly what `Option.elim` says. The uniform form
is what a `StrongRefinement.Comp` of a precondition half and an action half produces, so this is the
bridge between the definition above and every proof about it. -/
theorem AtomicBranch.aborting'_eq (B : ComputableNetworkPlusCal.AtomicBranch) :
    AtomicBranch.aborting' (V := V) B =
      B.precondition.elim ∅ (Block.aborting (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ Statement.aborting') (λ ⦃_⦄ ↦ Statement.reducing')) ∪
        B.precondition.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ Statement.reducing')) ∘ᵣ₁
          Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
            (λ ⦃_⦄ ↦ Statement.reducing') B.action := by
  rw [AtomicBranch.aborting']
  cases B.precondition with
  | none => rw [Option.elim, Option.elim, Relation.lcomp₁.left_id_eq, Set.empty_union]
  | some => rfl

@[inherit_doc AtomicBranch.aborting'_eq]
theorem AtomicBranch.diverging'_eq (B : ComputableNetworkPlusCal.AtomicBranch) :
    AtomicBranch.diverging' (V := V) B =
      B.precondition.elim ∅ (Block.diverging (β := λ _ ↦ LocalState' V)
          (λ ⦃_⦄ ↦ Statement.diverging') (λ ⦃_⦄ ↦ Statement.reducing')) ∪
        B.precondition.elim Relation.Idle (Block.reducing (β := λ _ ↦ LocalState' V)
            (λ ⦃_⦄ ↦ Statement.reducing')) ∘ᵣ₁
          Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
            (λ ⦃_⦄ ↦ Statement.reducing') B.action := by
  rw [AtomicBranch.diverging']
  cases B.precondition with
  | none => rw [Option.elim, Option.elim, Relation.lcomp₁.left_id_eq, Set.empty_union]
  | some => rfl

/-- No `NetworkPlusCal` statement diverges, so no branch does either. -/
@[simp] theorem AtomicBranch.diverging'_eq_empty (B : ComputableNetworkPlusCal.AtomicBranch) :
    AtomicBranch.diverging' (V := V) B = ∅ := by
  rw [AtomicBranch.diverging'_eq, Block.diverging'_eq_empty, Relation.lcomp₁.right_empty_eq_empty,
    Set.union_empty]
  cases B.precondition with
  | none => rfl
  | some => exact Block.diverging'_eq_empty

/-- Every name in a flat `Block.reducing` membership's endpoints is `none` — the label field only
ever changes at the `AtomicBranch`-composition boundary (`sem_glue₁`/`₂`'s job), never inside a
single `Statement.reducing'`-built `Block`. Needed to split a flat intermediate state into the
`.running`/`.done` case `sem_glue₃`/`div_glue₃`'s proofs match on. -/
theorem LocalState'.sem_label_eq {B : Block (ComputableNetworkPlusCal.Statement true) false}
    {σ σ' : LocalState' V} {ε : Trace V}
    (h : ⟨σ, ε, σ'⟩ ∈ Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B) :
    σ.2.2 = none ∧ σ'.2.2 = none := by
  rw [Block.reducing'_eq_map, Set.mem_image] at h
  obtain ⟨⟨⟨_, _⟩, _, ⟨_, _⟩⟩, _, rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem LocalState.sem_glue₃ {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {l : String}
    {ε : Trace V} {Br : ComputableNetworkPlusCal.AtomicBranch} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.done M₂ F₂ l⟩ ∈ AtomicBranch.reducing Br ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, some l)⟩ ∈ AtomicBranch.reducing' (V := V) Br := by
  unfold AtomicBranch.reducing AtomicBranch.reducing'
  cases hpre : Br.precondition with
  | none =>
    simp only [Option.elim]
    rw [Relation.lcomp₂.left_id_eq, Relation.lcomp₂.left_id_eq]
    exact LocalState.sem_glue₁
  | some B' =>
    simp only [Option.elim]
    iff_rintro ⟨⟨M', F'⟩, ε₁, ε₂, red_pre, red_act, rfl⟩ ⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, red_act, rfl⟩
    · exact ⟨(M', F', none), ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mp red_pre, (LocalState.sem_glue₁ (B := Br.action)).mp red_act, rfl⟩
    · have hl' : l' = none := (LocalState'.sem_label_eq (B := B') (σ := ((M₁, F₁, none) : LocalState' V))
        (σ' := (M', F', l')) red_pre).2
      subst hl'
      exact ⟨LocalState.running M' F', ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mpr red_pre, (LocalState.sem_glue₁ (B := Br.action)).mpr red_act, rfl⟩

/-- **A branch ends at the label its terminal `goto` names.** `AtomicBranch.reducing` composes the
precondition onto the action block, and the action block composes its `begin` onto its `last`, so the
final state is whatever `last` produced — and `goto` is the only statement that produces a `.done`
one at all (it is the only terminal constructor, `Core/GuardedPlusCal/Syntax.lean`).

Stated with the `goto`'s target supplied rather than existentially, because every caller already
knows it: it is read off the *source* branch through `BranchRefines.last_eq`, and what is wanted is
that the step agrees with it. This is what lets a caller rule out where a compiled block can jump to
without inspecting the run — `Guarded2Network`'s `CodeLabelRefines.exits`, which needs a compiled
code thread never to land on a receiving thread's label. -/
theorem AtomicBranch.reducing_label {M M' : Memory V} {F F' : FIFOs V} {l label : String}
    {ε : Trace V} {Br : ComputableNetworkPlusCal.AtomicBranch}
    (hlast : Br.action.last = .goto label)
    (h : (⟨.running M F, ε, .done M' F' l⟩ :
      LocalState V false × Trace V × LocalState V true) ∈ AtomicBranch.reducing Br) :
    l = label := by
  obtain ⟨_, _, _, _, hblock, _⟩ := h
  obtain ⟨_, _, _, _, hstmt, _⟩ := hblock
  rw [hlast] at hstmt
  obtain ⟨_, _, _, hdone, _⟩ := hstmt
  injection hdone

theorem LocalState.abort_glue₂ {M₁ : Memory V} {F₁ : FIFOs V} {ε : Trace V}
    {Br : ComputableNetworkPlusCal.AtomicBranch} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈ AtomicBranch.aborting Br ↔
      ⟨(M₁, F₁, none), ε⟩ ∈ AtomicBranch.aborting' (V := V) Br := by
  unfold AtomicBranch.aborting AtomicBranch.aborting'
  cases hpre : Br.precondition with
  | none => exact LocalState.abort_glue
  | some B' =>
    iff_rintro (h|⟨⟨M', F'⟩, ε₁, ε₂, red_pre, abort_act, rfl⟩) (h|⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, abort_act, rfl⟩)
    · exact Or.inl ((LocalState.abort_glue (B := B')).mp h)
    · exact Or.inr ⟨(M', F', none), ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mp red_pre, (LocalState.abort_glue (B := Br.action)).mp abort_act, rfl⟩
    · exact Or.inl ((LocalState.abort_glue (B := B')).mpr h)
    · have hl' : l' = none := (LocalState'.sem_label_eq (B := B') (σ := ((M₁, F₁, none) : LocalState' V))
        (σ' := (M', F', l')) red_pre).2
      subst hl'
      exact Or.inr ⟨LocalState.running M' F', ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mpr red_pre, (LocalState.abort_glue (B := Br.action)).mpr abort_act, rfl⟩

theorem LocalState.div_glue₃ {M₁ : Memory V} {F₁ : FIFOs V} {ε : Trace V}
    {Br : ComputableNetworkPlusCal.AtomicBranch} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈ AtomicBranch.diverging Br ↔
      ⟨(M₁, F₁, none), ε⟩ ∈ AtomicBranch.diverging' (V := V) Br := by
  unfold AtomicBranch.diverging AtomicBranch.diverging'
  cases hpre : Br.precondition with
  | none => exact LocalState.div_glue
  | some B' =>
    iff_rintro (h|⟨⟨M', F'⟩, ε₁, ε₂, red_pre, div_act, rfl⟩) (h|⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, div_act, rfl⟩)
    · exact Or.inl ((LocalState.div_glue (B := B')).mp h)
    · exact Or.inr ⟨(M', F', none), ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mp red_pre, (LocalState.div_glue (B := Br.action)).mp div_act, rfl⟩
    · exact Or.inl ((LocalState.div_glue (B := B')).mpr h)
    · have hl' : l' = none := (LocalState'.sem_label_eq (B := B') (σ := ((M₁, F₁, none) : LocalState' V))
        (σ' := (M', F', l')) red_pre).2
      subst hl'
      exact Or.inr ⟨LocalState.running M' F', ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mpr red_pre, (LocalState.div_glue (B := Br.action)).mpr div_act, rfl⟩

theorem LocalState.div_glue₂ {M₁ : Memory V} {F₁ : FIFOs V} {ε : Trace V}
    {B : ComputableNetworkPlusCal.AtomicBlock} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈ AtomicBlock.diverging B ↔
      ∃ Br ∈ B.branches, ⟨(M₁, F₁, none), ε⟩ ∈ AtomicBranch.diverging' (V := V) Br := by
  unfold AtomicBlock.diverging
  iff_rintro ⟨Br, Br_in, h⟩ ⟨Br, Br_in, h⟩
  · exact ⟨Br, Br_in, LocalState.div_glue₃.mp h⟩
  · exact ⟨Br, Br_in, LocalState.div_glue₃.mpr h⟩

/-! ## What a step leaves in the channel map

  Only `send` writes a channel, and it writes at a key it has just *read*, so a step changes what a
  queue holds but never which keys exist. Stated one level at a time, statement to branch, the same
  shape as `Guarded2Network/Lemmas/Locality.lean`'s argument about the written name.

  The presence half is what a refinement invariant needs: `Guarded2Network`'s receiving thread aborts
  on a channel that resolves to no FIFO at all, and the source has no such thread to abort with — so
  ruling that state out is what makes the aborting half of that pass's refinement true rather than
  merely hard.
-/

/-- **A statement never removes a channel.** `send` is the only constructor that writes the map, and
it writes at a key it has just read, so its `insert` only ever overwrites. -/
theorem Statement.reducing'_fifos_mem {b b' : Bool}
    {S : ComputableNetworkPlusCal.Statement b b'} {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈ Statement.reducing' S)
    {k : GuardedPlusCal.ChanKey V} (h : σ.fifos.lookup k ≠ .none) :
    σ'.fifos.lookup k ≠ .none := by
  obtain ⟨M₁, F₁, l₁⟩ := σ
  obtain ⟨M₂, F₂, l₂⟩ := σ'
  cases S with
  | «with» x ann bound e =>
    obtain ⟨_, _, ⟨M, F, v, _, _, hM, _, hb⟩, hpost, _⟩ := step
    injection hM with _ hF
    subst hF
    cases bound with
    | true =>
      subst hb
      injection hpost with _ hF'
      subst hF'
      exact h
    | false =>
      obtain ⟨_, _, rfl⟩ := hb
      injection hpost with _ hF'
      subst hF'
      exact h
  | await e =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _, _⟩, hpost, _⟩ := step
    injection hM with _ hF
    subst hF; subst hσ'
    injection hpost with _ hF'
    subst hF'
    exact h
  | skip =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _⟩, hpost, _⟩ := step
    injection hM with _ hF
    subst hF; subst hσ'
    injection hpost with _ hF'
    subst hF'
    exact h
  | goto label =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _⟩, _, hpost, _⟩ := step
    injection hM with _ hF
    subst hF
    rw [hσ'] at hpost
    injection hpost with _ hF'
    subst hF'
    exact h
  | print e =>
    obtain ⟨_, _, ⟨M, F, _, _, hM, hσ', _, _, _⟩, hpost, _⟩ := step
    injection hM with _ hF
    subst hF; subst hσ'
    injection hpost with _ hF'
    subst hF'
    exact h
  | assert e =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _, _⟩, hpost, _⟩ := step
    injection hM with _ hF
    subst hF; subst hσ'
    injection hpost with _ hF'
    subst hF'
    exact h
  | multicast c filter =>
    obtain ⟨_, -, hmem, -⟩ := step
    exact hmem.elim
  | assign r e =>
    obtain ⟨_, _, ⟨M, F, _, _, _, _, _, _, hM, hσ', _⟩, hpost, _⟩ := step
    injection hM with _ hF
    subst hF; subst hσ'
    injection hpost with _ hF'
    subst hF'
    exact h
  | send c e =>
    obtain ⟨_, _, ⟨M, F, _, cpath, vs, _, _, _, hlk, _, hM, hσ', _⟩, hpost, _⟩ := step
    injection hM with _ hF
    subst hF; subst hσ'
    injection hpost with _ hF'
    subst hF'
    simp only [LocalState'.fifos_mk] at h ⊢
    by_cases hk : k = ⟨c.name, cpath⟩
    · subst hk
      rw [Finmap.lookup_insert]
      exact Option.some_ne_none _
    · rwa [Finmap.lookup_insert_of_ne _ hk]

/-- **Nor does a block.** One `Statement.reducing'_fifos_mem` per step of the same left-to-right
induction the locality argument runs. -/
theorem Block.reducing'_fifos_mem {b b' : Bool}
    {B : Block (ComputableNetworkPlusCal.Statement b) b'} {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B)
    {k : GuardedPlusCal.ChanKey V} (h : σ.fifos.lookup k ≠ .none) :
    σ'.fifos.lookup k ≠ .none := by
  induction B using Block.cons_end_induct generalizing σ σ' ε with
  | «end» S =>
    rw [Block.reducing_end] at step
    exact Statement.reducing'_fifos_mem step h
  | cons S B IH =>
    rw [Block.reducing_cons] at step
    obtain ⟨σ'', ε₁, ε₂, hhead, htail, rfl⟩ := step
    exact IH htail (Statement.reducing'_fifos_mem hhead h)

/-- **Nor a branch**, precondition and action together — a missing precondition being
`Relation.Idle`, which writes nothing. -/
theorem AtomicBranch.reducing'_fifos_mem {Br : ComputableNetworkPlusCal.AtomicBranch}
    {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈ AtomicBranch.reducing' Br)
    {k : GuardedPlusCal.ChanKey V} (h : σ.fifos.lookup k ≠ .none) :
    σ'.fifos.lookup k ≠ .none := by
  obtain ⟨σ'', ε₁, ε₂, hpres, hact, rfl⟩ := step
  refine Block.reducing'_fifos_mem hact ?_
  match hp : Br.precondition with
  | .none =>
    rw [hp] at hpres
    obtain ⟨rfl, -⟩ := hpres
    exact h
  | .some B' =>
    rw [hp] at hpres
    exact Block.reducing'_fifos_mem hpres h

-- Leaf discharge for `sem_side`.
attribute [aesop norm simp (rule_sets := [sem])]
  LocalState.sem_glue₁ LocalState.sem_glue₂ LocalState.abort_glue LocalState.div_glue

end NetworkPlusCal

/-! # `sem_red`/`sem_side`

  Between them they say *from which state to which state* a `Statement.reducing` step goes, leaving
  every side condition as one existential body goal. One macro covers both languages: `LocalState`
  is shared, so nothing about the dispatch itself is per-language, only which intro lemma matches.

  Aesop only ever runs terminally here — the goals it would otherwise leave are whatever the search
  happened to stop at, the same instability as non-terminal `simp`, worse because later proof steps
  are written against a fixed goal order.
-/

/-- Dispatch is a lookup, not a search: the statement's head constructor determines the intro
lemma uniquely, so `apply` (not `aesop`) picks it, and the side-goal count/order comes from the
lemma itself rather than a hand-counted `?_` list — a `Statement` field change breaks the intro
lemma's own type, not this macro. Tries both languages' lemma names in `first`; `apply` fails
cleanly on a head-constructor mismatch, so trying the wrong language costs nothing. -/
macro "sem_red" : tactic => `(tactic| first
  | apply GuardedPlusCal.Statement.reducing.with.intro
  | apply GuardedPlusCal.Statement.reducing.await.intro
  | apply GuardedPlusCal.Statement.reducing.receive.intro
  | apply GuardedPlusCal.Statement.reducing.skip.intro
  | apply GuardedPlusCal.Statement.reducing.goto.intro
  | apply GuardedPlusCal.Statement.reducing.print.intro
  | apply GuardedPlusCal.Statement.reducing.assert.intro
  | apply GuardedPlusCal.Statement.reducing.send.intro
  | apply GuardedPlusCal.Statement.reducing.assign.intro
  | apply NetworkPlusCal.Statement.reducing.with.intro
  | apply NetworkPlusCal.Statement.reducing.await.intro
  | apply NetworkPlusCal.Statement.reducing.skip.intro
  | apply NetworkPlusCal.Statement.reducing.goto.intro
  | apply NetworkPlusCal.Statement.reducing.print.intro
  | apply NetworkPlusCal.Statement.reducing.assert.intro
  | apply NetworkPlusCal.Statement.reducing.send.intro
  | apply NetworkPlusCal.Statement.reducing.assign.intro)

/-- `sem_red`'s leaf discharge: the side conditions it leaves — evaluation transfers, memberships,
freshness — are a real search problem, handed to the `sem` rule set. Terminal, and `aesop?` prints
the found proof when it fails. -/
macro "sem_side" : tactic => `(tactic| aesop (rule_sets := [sem]))

end
