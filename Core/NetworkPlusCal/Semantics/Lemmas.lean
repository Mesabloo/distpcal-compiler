module

public import Core.NetworkPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Semantics.Lemmas

@[expose] public section

/-!
  Network PlusCal's half of the flat state encoding item 7 needs.

  Everything generic lives in `Core/GuardedPlusCal/Semantics/Lemmas.lean` and is *used* here, not
  restated: the `Block.reducing`/`.aborting`/`.diverging` equations, the `*_map` relabelling lemmas,
  and `LocalState'`/`toLocalState'`/`toLocalState'_inj` itself — the two languages share one state
  space (see `Semantics/Denotational.lean`'s module doc), so they share its flat encoding too. What
  is genuinely per-language is the primed statement semantics, since that is defined from this
  language's own `Statement.reducing`.

  That sharing is the point: item 7 relates a `GuardedPlusCal` block to a `NetworkPlusCal` one over
  a single `LocalState'`, with no isomorphism to transport across first.
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
    (h : ∃ M F v, M ⊢ e ⇒ v ∧ AList.lookup name M = none ∧ σ = .running M F ∧ ε = 1 ∧
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
      σ = .running M F ∧ σ' = .running M (F.replace ⟨c.name, cpath⟩ (vs.concat v)) ∧
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

-- Leaf discharge for `sem_side` (T1, see below).
attribute [aesop safe apply (rule_sets := [sem])]
  Statement.reducing.with.intro Statement.reducing.await.intro
  Statement.reducing.skip.intro Statement.reducing.goto.intro Statement.reducing.print.intro
  Statement.reducing.assert.intro Statement.reducing.send.intro Statement.reducing.assign.intro
  Statement.aborting.with.intro Statement.aborting.await.intro
  Statement.aborting.print.intro Statement.aborting.assert.intro Statement.aborting.send.intro
  Statement.aborting.assign.intro

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
  constructor
  · rintro ⟨rfl, sem⟩
    exists _, sem
  · rintro ⟨⟨⟨_⟩, _⟩, _, _|_⟩
    trivial

-- `Statement.diverging` is `∅` regardless of the expression semantics, so this one does not use it.
omit [ExprSemantics V] in
private theorem Statement.diverging'_eq_map {b b' : Bool}
    (S : ComputableNetworkPlusCal.Statement b b') :
    Statement.diverging' (V := V) S =
      Prod.map LocalState.toLocalState' id '' Statement.diverging S := by
  ext ⟨⟨M, F, l⟩, e⟩
  constructor
  · rintro ⟨rfl, sem⟩
    exists _, sem
  · rintro ⟨⟨⟨_⟩, _⟩, _, _|_⟩
    trivial

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
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩; exact sem

theorem LocalState.sem_glue₂ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableNetworkPlusCal.Statement g) false} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.running M₂ F₂⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, none)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩; exact sem

theorem LocalState.abort_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.aborting'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩; exact sem

theorem LocalState.div_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : Trace V} {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.diverging'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩; exact sem

/-! # `AtomicBranch`/`AtomicBlock`, flat

  `AtomicBlock` only exists on this side (`Semantics/Denotational.lean`'s module doc for why).
  Mirrors `Statement.blockReducing`/`AtomicBranch.reducing` (`Semantics/Denotational.lean`) at the
  flat encoding, built from the primed leaf functions above rather than proved equal to an
  image of the indexed version after the fact — the indexed `AtomicBranch.reducing`/etc. are
  themselves already exactly "precondition, then action" by definition, so there is no separate
  `sem_eq`/`abort_eq`/`div_eq` step to port here the way prior art needed (its `AtomicBranch`
  semantics went through a `Reduce`/`Abort`/`Diverge` instance first). -/

/-- `AtomicBranch.reducing` in the flat encoding. -/
def AtomicBranch.reducing' (B : ComputableNetworkPlusCal.AtomicBranch) :
    Set (LocalState' V × Trace V × LocalState' V) :=
  B.precondition.elim {⟨x, e, y⟩ | x = y ∧ e = 1}
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
    constructor
    · rintro ⟨⟨M', F'⟩, ε₁, ε₂, red_pre, red_act, rfl⟩
      exact ⟨(M', F', none), ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mp red_pre, (LocalState.sem_glue₁ (B := Br.action)).mp red_act, rfl⟩
    · rintro ⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, red_act, rfl⟩
      have hl' : l' = none := (LocalState'.sem_label_eq (B := B') (σ := ((M₁, F₁, none) : LocalState' V))
        (σ' := (M', F', l')) red_pre).2
      subst hl'
      exact ⟨LocalState.running M' F', ε₁, ε₂,
        (LocalState.sem_glue₂ (B := B')).mpr red_pre, (LocalState.sem_glue₁ (B := Br.action)).mpr red_act, rfl⟩

theorem LocalState.abort_glue₂ {M₁ : Memory V} {F₁ : FIFOs V} {ε : Trace V}
    {Br : ComputableNetworkPlusCal.AtomicBranch} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈ AtomicBranch.aborting Br ↔
      ⟨(M₁, F₁, none), ε⟩ ∈ AtomicBranch.aborting' (V := V) Br := by
  unfold AtomicBranch.aborting AtomicBranch.aborting'
  cases hpre : Br.precondition with
  | none => exact LocalState.abort_glue
  | some B' =>
    constructor
    · rintro (h|⟨⟨M', F'⟩, ε₁, ε₂, red_pre, abort_act, rfl⟩)
      · exact Or.inl ((LocalState.abort_glue (B := B')).mp h)
      · exact Or.inr ⟨(M', F', none), ε₁, ε₂,
          (LocalState.sem_glue₂ (B := B')).mp red_pre, (LocalState.abort_glue (B := Br.action)).mp abort_act, rfl⟩
    · rintro (h|⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, abort_act, rfl⟩)
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
    constructor
    · rintro (h|⟨⟨M', F'⟩, ε₁, ε₂, red_pre, div_act, rfl⟩)
      · exact Or.inl ((LocalState.div_glue (B := B')).mp h)
      · exact Or.inr ⟨(M', F', none), ε₁, ε₂,
          (LocalState.sem_glue₂ (B := B')).mp red_pre, (LocalState.div_glue (B := Br.action)).mp div_act, rfl⟩
    · rintro (h|⟨⟨M', F', l'⟩, ε₁, ε₂, red_pre, div_act, rfl⟩)
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
  constructor
  · rintro ⟨Br, Br_in, h⟩
    exact ⟨Br, Br_in, LocalState.div_glue₃.mp h⟩
  · rintro ⟨Br, Br_in, h⟩
    exact ⟨Br, Br_in, LocalState.div_glue₃.mpr h⟩

-- Leaf discharge for `sem_side` (T1).
attribute [aesop norm simp (rule_sets := [sem])]
  LocalState.sem_glue₁ LocalState.sem_glue₂ LocalState.abort_glue LocalState.div_glue

end NetworkPlusCal

/-! # T1 — `sem_red`/`sem_side`

  `sem_redg`/`sem_redn`'s role, prior art's per-language dispatch macros: say *from which state to
  which state* a `Statement.reducing` step goes, leaving every side condition as one existential
  body goal. One macro now, not two — `LocalState` is shared, so nothing about the dispatch itself
  is per-language, only which intro lemma matches.

  Aesop only ever runs terminally here (`Rule: aesop closes the goal or it is not used`,
  plan §3 T1) — the goals it would otherwise leave are whatever the search happened to stop at,
  the same instability as non-terminal `simp`, worse because later proof steps are written
  against a fixed goal order.
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
freshness — are a real search problem, handed to the `sem` rule set. Terminal, per T1's rule;
`aesop?` prints the found proof when it fails, unlike prior art's bare `fail "Statement
unsupported (yet)"`. -/
macro "sem_side" : tactic => `(tactic| aesop (rule_sets := [sem]))

end
