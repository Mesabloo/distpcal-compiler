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
open GuardedPlusCal (Block Behavior FIFOs LocalState LocalState')

variable {V : Type} [ExprSemantics V]

/-- `Statement.reducing` in the flat encoding — see `GuardedPlusCal.Statement.reducing'`. -/
def Statement.reducing' {b b' : Bool} (S : ComputableNetworkPlusCal.Statement b b') :
    Set (LocalState' V × List (Behavior V) × LocalState' V) :=
  {⟨⟨M, F, l⟩, ε, ⟨M', F', l'⟩⟩ | ∃ σ' : LocalState V b',
    l = Option.none ∧ ⟨LocalState.running M F, ε, σ'⟩ ∈ Statement.reducing S ∧ match b', σ' with
      | true, σ' => ∃ l'', σ' = LocalState.done M' F' l'' ∧ l' = Option.some l''
      | false, σ' => σ' = LocalState.running M' F' ∧ l' = Option.none}

@[inherit_doc Statement.reducing']
def Statement.aborting' {b b' : Bool} (S : ComputableNetworkPlusCal.Statement b b') :
    Set (LocalState' V × List (Behavior V)) :=
  {⟨⟨M, F, l⟩, ε⟩ | l = Option.none ∧ ⟨LocalState.running M F, ε⟩ ∈ Statement.aborting S}

@[inherit_doc Statement.reducing']
def Statement.diverging' {b b' : Bool} (S : ComputableNetworkPlusCal.Statement b b') :
    Set (LocalState' V × List (Behavior V)) :=
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
    {ε : List (Behavior V)} {B : Block (ComputableNetworkPlusCal.Statement g) true} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.done M₂ F₂ l⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, some l)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩; exact sem

theorem LocalState.sem_glue₂ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V}
    {ε : List (Behavior V)} {B : Block (ComputableNetworkPlusCal.Statement g) false} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.running M₂ F₂⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, none)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩; exact sem

theorem LocalState.abort_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : List (Behavior V)} {B : Block (ComputableNetworkPlusCal.Statement g) b} :
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
    {ε : List (Behavior V)} {B : Block (ComputableNetworkPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.diverging'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩; exact sem

end NetworkPlusCal

end
