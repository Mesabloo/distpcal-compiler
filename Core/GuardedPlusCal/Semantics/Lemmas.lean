module

public import Core.GuardedPlusCal.Semantics.Denotational
public import Core.GuardedPlusCal.Syntax.Lemmas

@[expose] public section

/-!
  Semantic equations for Guarded PlusCal: how `Block.reducing`/`.aborting`/`.diverging` decompose
  along `Block`'s list-like interface (`end`/`cons`/`concat`/`prepend`), and how they commute with an
  injective relabelling of the state type.

  Everything here is about *this* language's own semantics, not about the relationship between
  Guarded and Network PlusCal — prior art inlined these into `Guarded2Network/Lemmas.lean`, which is
  what made that file 7521 lines.

  Nothing in this file mentions values or the expression layer: the `Block` combinators are generic
  over the statement family `α`, the state family `β`, and the behavior monoid `γ`, so
  `NetworkPlusCal`'s own semantics reuses these lemmas verbatim rather than restating them.

  Prior art phrased these with the `⟦·⟧*`/`⟦·⟧⊥`/`⟦·⟧∞` notations, resolving the semantics through
  `Reduce`/`Abort`/`Diverge` instances. Those instances do not exist here (see
  `Semantics/Denotational.lean`'s module doc), so each lemma takes the step relation explicitly.
-/

namespace GuardedPlusCal

open ComputableTLAPlus (Memory ExprSemantics)

/-! # Reduction -/

section Reducing

variable {α β : Bool → Type} {γ : Type} [Monoid γ]
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))

theorem Block.reducing_end {b : Bool} {S : α b} : Block.reducing f (Block.end S) = f S := by
  rw [Block.reducing]

theorem Block.reducing_cons {b : Bool} {B : Block α b} {S : α false} :
    Block.reducing f (Block.cons S B) = f S ∘ᵣ₂ Block.reducing f B := by
  rw [Block.reducing]

theorem Block.reducing_concat {b : Bool} {B : Block α false} {S : α b} :
    Block.reducing f (B.concat S) = Block.reducing f B ∘ᵣ₂ f S := by
  induction B using Block.cons_end_induct' with
  | «end» S' =>
    rw [Block.concat_end, Block.reducing_cons, Block.reducing_end, Block.reducing_end]
  | cons S' B IH =>
    rw [Block.concat_cons, Block.reducing_cons, IH, Block.reducing_cons, ← Relation.lcomp₂.assoc]

theorem Block.reducing_left_append_of_ne_nil {b : Bool} {A : List (α false)} {B : Block α b}
    (A_ne_nil : A ≠ []) :
    Block.reducing f {B with begin := A ++ B.begin} =
      A.tail.foldl (init := f (A.head A_ne_nil)) (λ sem x ↦ sem ∘ᵣ₂ f x) ∘ᵣ₂ Block.reducing f B := by
  generalize B'_eq : { B with begin := A ++ B.begin } = B'
  have B'_begin_eq : B'.begin = A ++ B.begin := by subst B'; dsimp

  induction B' using Block.reducing.induct generalizing A with
  | case1 B' B'_begin_eq' =>
    rw [B'_begin_eq'] at B'_begin_eq
    symm at B'_begin_eq
    apply List.append_ne_nil_of_left_ne_nil at B'_begin_eq
    · contradiction
    · assumption
  | case2 B' S Ss h₁ IH =>
    subst B'

    dsimp at h₁
    rw [List.append_eq_cons_iff] at h₁
    obtain ⟨rfl, _⟩|⟨Ss, rfl, rfl⟩ := h₁
    · contradiction
    · dsimp at *

      match (generalizing := false) Ss_eq : Ss with
      | [] => rw [List.foldl_nil, List.nil_append, ← Block.cons, Block.reducing_cons]
      | _ :: _ =>
        specialize @IH Ss (Ss_eq ▸ List.cons_ne_nil _ _) rfl rfl
        rw [← Ss_eq, ← Block.cons.eq_def (B := { begin := Ss ++ B.begin, last := B.last}),
          Block.reducing_cons, IH, Relation.lcomp₂.assoc,
          ← List.foldl_hom (f := λ sem ↦ f S ∘ᵣ₂ sem) (g₁ := λ sem x ↦ sem ∘ᵣ₂ f x)
            (g₂ := λ sem x ↦ sem ∘ᵣ₂ f x)]
        · rw [← List.foldl_cons, List.cons_head_tail]
        · intros x y
          rw [← Relation.lcomp₂.assoc]

theorem Block.reducing_left_append {b : Bool} {A : List (α false)} {B : Block α b} :
    Block.reducing f {B with begin := A ++ B.begin} =
      A.foldl (init := {⟨x, e, y⟩ | x = y ∧ e = 1}) (λ sem x ↦ sem ∘ᵣ₂ f x) ∘ᵣ₂ Block.reducing f B := by
  cases A with
  | nil => rw [List.foldl_nil, List.nil_append, Relation.lcomp₂.left_id_eq]
  | cons =>
    rw [List.foldl_cons, Block.reducing_left_append_of_ne_nil f (List.cons_ne_nil _ _),
      Relation.lcomp₂.left_id_eq, List.head_cons, List.tail_cons]

theorem Block.reducing_prepend {b : Bool} {A : List (α false)} {B : Block α b} :
    Block.reducing f (B.prepend A) =
      A.foldl (init := {⟨x, e, y⟩ | x = y ∧ e = 1}) (λ sem x ↦ sem ∘ᵣ₂ f x) ∘ᵣ₂ Block.reducing f B :=
  Block.reducing_left_append f

theorem Block.reducing_eq_foldr {B : Block α false} :
    Block.reducing f B = List.foldr (f · ∘ᵣ₂ ·) {⟨x, e, y⟩ | x = y ∧ e = 1} B.toList := by
  induction B using Block.reducing.induct with
  | case1 B _ =>
    let ⟨[], S⟩ := B
    simp [Block.toList, Block.reducing, Relation.lcomp₂.right_id_eq]
  | case2 B S Ss h IH =>
    let ⟨_ :: _, S'⟩ := B
    obtain _|_ := h

    rw [Block.reducing, Block.toList, List.concat_eq_append, List.cons_append, List.foldr_cons]
    dsimp at IH ⊢
    rw [IH, Block.toList, List.concat_eq_append]

end Reducing

/-! # Abortion and divergence

  `aborting` and `diverging` share their shape exactly — both are "this element goes wrong, or it
  steps and the rest does" — so the two families of lemmas below are literal mirrors of each other.
-/

section Aborting

variable {α β : Bool → Type} {γ : Type} [Monoid γ]
  (g : ⦃b : Bool⦄ → α b → Set (β false × γ))
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))

theorem Block.aborting_end {b : Bool} {S : α b} : Block.aborting g f (Block.end S) = g S := by
  rw [Block.aborting]

theorem Block.aborting_cons {b : Bool} {S : α false} {B : Block α b} :
    Block.aborting g f (Block.cons S B) = g S ∪ f S ∘ᵣ₁ Block.aborting g f B := by
  rw [Block.aborting]

theorem Block.aborting_eq_foldr {b : Bool} {B : Block α b} :
    Block.aborting g f B = List.foldr (λ S sem ↦ g S ∪ f S ∘ᵣ₁ sem) (g B.last) B.begin := by
  induction B using Block.aborting.induct with
  | case1 B _ =>
    let ⟨[], S⟩ := B
    simp [Block.aborting]
  | case2 B S Ss h IH =>
    let ⟨_ :: _, S'⟩ := B
    obtain _|_ := h
    simp [Block.aborting, IH]

theorem Block.aborting_eq_foldr_toList {B : Block α false} :
    Block.aborting g f B = List.foldr (λ S sem ↦ g S ∪ f S ∘ᵣ₁ sem) ∅ B.toList := by
  rw [Block.aborting_eq_foldr, Block.toList, List.concat_eq_append, List.foldr_concat,
    Relation.lcomp₁.right_empty_eq_empty, Set.union_empty]

theorem Block.aborting_concat {b : Bool} {S : α b} {B : Block α false} :
    Block.aborting g f (B.concat S) =
      Block.aborting g f B ∪ Block.reducing f B ∘ᵣ₁ g S := by
  induction B using Block.cons_end_induct' with
  | «end» S' =>
    rw [Block.concat_end, Block.aborting_cons, Block.aborting_end, Block.aborting_end,
      Block.reducing_end]
  | cons S' B IH =>
    rw [Block.concat_cons, Block.aborting_cons, IH, Block.aborting_cons,
      Relation.lcomp₁.right_union_eq_union, Block.reducing_cons, ← Set.union_assoc,
      Relation.lcomp₁.left_lcomp₂_eq]

theorem Block.aborting_left_append {b : Bool} {A : List (α false)} {B : Block α b} :
    Block.aborting g f { B with begin := A ++ B.begin } =
      List.foldr (λ x sem ↦ g x ∪ f x ∘ᵣ₁ sem) (Block.aborting g f B) A := by
  simp [Block.aborting_eq_foldr]

end Aborting

section Diverging

variable {α β : Bool → Type} {γ : Type} [Monoid γ]
  (d : ⦃b : Bool⦄ → α b → Set (β false × γ))
  (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b))

theorem Block.diverging_end {b : Bool} {S : α b} : Block.diverging d f (Block.end S) = d S := by
  rw [Block.diverging]

theorem Block.diverging_cons {b : Bool} {S : α false} {B : Block α b} :
    Block.diverging d f (Block.cons S B) = d S ∪ f S ∘ᵣ₁ Block.diverging d f B := by
  rw [Block.diverging]

theorem Block.diverging_eq_foldr {b : Bool} {B : Block α b} :
    Block.diverging d f B = List.foldr (λ S sem ↦ d S ∪ f S ∘ᵣ₁ sem) (d B.last) B.begin := by
  induction B using Block.diverging.induct with
  | case1 B _ =>
    let ⟨[], S⟩ := B
    simp [Block.diverging]
  | case2 B S Ss h IH =>
    let ⟨_ :: _, S'⟩ := B
    obtain _|_ := h
    simp [Block.diverging, IH]

theorem Block.diverging_concat {b : Bool} {S : α b} {B : Block α false} :
    Block.diverging d f (B.concat S) =
      Block.diverging d f B ∪ Block.reducing f B ∘ᵣ₁ d S := by
  induction B using Block.cons_end_induct' with
  | «end» S' =>
    rw [Block.concat_end, Block.diverging_cons, Block.diverging_end, Block.diverging_end,
      Block.reducing_end]
  | cons S' B IH =>
    rw [Block.concat_cons, Block.diverging_cons, IH, Block.diverging_cons,
      Relation.lcomp₁.right_union_eq_union, Block.reducing_cons, ← Set.union_assoc,
      Relation.lcomp₁.left_lcomp₂_eq]

theorem Block.diverging_left_append {b : Bool} {A : List (α false)} {B : Block α b} :
    Block.diverging d f { B with begin := A ++ B.begin } =
      List.foldr (λ x sem ↦ d x ∪ f x ∘ᵣ₁ sem) (Block.diverging d f B) A := by
  simp [Block.diverging_eq_foldr]

end Diverging

/-! # Relabelling the state type

  Item 7 needs to move between the `Bool`-indexed `LocalState` and a flat, unindexed encoding of it,
  so that source and target states inhabit one type and `StrongRefinement`'s relation can be stated.
  These three lemmas are what make that move sound: an injective relabelling of states commutes with
  taking a block's semantics. Injectivity is genuinely needed — without it, two distinct
  intermediate states could be identified and a composite step invented that the original relation
  never had.
-/

theorem Block.reducing_map {α β δ : Bool → Type} {γ : Type} [Monoid γ] {b : Bool} {B : Block α b}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (g : ⦃b : Bool⦄ → β b → δ b)
    (g_inj : ∀ ⦃b⦄, Function.Injective (@g b)) :
    Prod.map₃ (@g _) id (@g _) '' Block.reducing f B =
      Block.reducing (λ ⦃_⦄ x ↦ Prod.map₃ (@g _) id (@g _) '' f x) B := by
  induction B using Block.reducing.induct with
  | case1 B _ =>
    let ⟨[], _⟩ := B
    repeat rw [Block.reducing]
  | case2 B S Ss h IH =>
    let ⟨_ :: _, _⟩ := B
    cases h
    repeat rw [Block.reducing]
    dsimp at IH ⊢
    rw [← IH]

    ext ⟨a', e, c'⟩
    constructor
    · rintro ⟨⟨a, e, c⟩, ⟨b₀, e₁, e₂, _, _, rfl⟩, _|_⟩
      exists g b₀, e₁, e₂
      and_intros
      · exists ⟨a, e₁, b₀⟩
      · exists ⟨b₀, e₂, c⟩
      · rfl
    · rintro ⟨b', e₁, e₂, ⟨⟨a, e₁', b₀⟩, _, h₁⟩, ⟨⟨b'', e₂', c⟩, _, h₂⟩, rfl⟩

      have : g a = a' ∧ e₁' = e₁ ∧ g b₀ = b' := by cases h₁; trivial
      obtain ⟨_, _, _⟩ := this
      have : g b'' = b' ∧ e₂' = e₂ ∧ g c = c' := by cases h₂; trivial
      obtain ⟨h₃, _, _⟩ := this
      subst a' e₁' b' e₂' c'

      have : b'' = b₀ := g_inj h₃
      subst b''

      exists ⟨a, e₁ * e₂, c⟩
      and_intros
      · exists b₀, e₁, e₂
      · rfl

theorem Block.aborting_map {α β δ : Bool → Type} {γ : Type} [Monoid γ] {b : Bool} {B : Block α b}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (g : ⦃b : Bool⦄ → α b → Set (β false × γ))
    (h : ⦃b : Bool⦄ → β b → δ b) (h_inj : ∀ ⦃b⦄, Function.Injective (@h b)) :
    Prod.map (@h _) id '' Block.aborting g f B =
      Block.aborting (λ ⦃_⦄ x ↦ Prod.map (@h _) id '' g x)
        (λ ⦃_⦄ x ↦ Prod.map₃ (@h _) id (@h _) '' f x) B := by
  induction B using Block.aborting.induct with
  | case1 B _ =>
    let ⟨[], _⟩ := B
    repeat rw [Block.aborting]
  | case2 B S Ss h' IH =>
    let ⟨_ :: _, _⟩ := B
    obtain _|_ := h'
    repeat rw [Block.aborting]
    rw [Set.image_union]
    dsimp at IH ⊢
    congr

    ext ⟨x, e⟩
    constructor
    · rintro ⟨⟨a, e⟩, ⟨b₀, e₁, e₂, _, sem, rfl⟩, _|_⟩
      exists h b₀, e₁, e₂
      and_intros
      · exists ⟨a, e₁, b₀⟩
      · rw [← IH]
        exists ⟨b₀, e₂⟩
      · rfl
    · rw [← IH]
      rintro ⟨y, e₁, e₂, ⟨⟨a, e₁, b₀⟩, _, _|_⟩, ⟨⟨b', e₂'⟩, _, eq⟩, rfl⟩
      exists ⟨a, e₁ * e₂⟩
      and_intros
      · have : b' = b₀ := by
          rw [Prod.map, Prod.mk.injEq] at eq
          exact h_inj eq.left

        have : e₂' = e₂ := by
          rw [Prod.map, Prod.mk.injEq] at eq
          exact eq.right

        subst b' e₂'
        exists b₀, e₁, e₂
      · rfl

theorem Block.diverging_map {α β δ : Bool → Type} {γ : Type} [Monoid γ] {b : Bool} {B : Block α b}
    (f : ⦃b : Bool⦄ → α b → Set (β false × γ × β b)) (d : ⦃b : Bool⦄ → α b → Set (β false × γ))
    (h : ⦃b : Bool⦄ → β b → δ b) (h_inj : ∀ ⦃b⦄, Function.Injective (@h b)) :
    Prod.map (@h _) id '' Block.diverging d f B =
      Block.diverging (λ ⦃_⦄ x ↦ Prod.map (@h _) id '' d x)
        (λ ⦃_⦄ x ↦ Prod.map₃ (@h _) id (@h _) '' f x) B := by
  induction B using Block.diverging.induct with
  | case1 B _ =>
    let ⟨[], _⟩ := B
    repeat rw [Block.diverging]
  | case2 B S Ss h' IH =>
    let ⟨_ :: _, _⟩ := B
    obtain _|_ := h'
    repeat rw [Block.diverging]
    rw [Set.image_union]
    dsimp at IH ⊢
    congr

    ext ⟨x, e⟩
    constructor
    · rintro ⟨⟨a, e⟩, ⟨b₀, e₁, e₂, _, sem, rfl⟩, _|_⟩
      exists h b₀, e₁, e₂
      and_intros
      · exists ⟨a, e₁, b₀⟩
      · rw [← IH]
        exists ⟨b₀, e₂⟩
      · rfl
    · rw [← IH]
      rintro ⟨y, e₁, e₂, ⟨⟨a, e₁, b₀⟩, _, _|_⟩, ⟨⟨b', e₂'⟩, _, eq⟩, rfl⟩
      exists ⟨a, e₁ * e₂⟩
      and_intros
      · have : b' = b₀ := by
          rw [Prod.map, Prod.mk.injEq] at eq
          exact h_inj eq.left

        have : e₂' = e₂ := by
          rw [Prod.map, Prod.mk.injEq] at eq
          exact eq.right

        subst b' e₂'
        exists b₀, e₁, e₂
      · rfl

/-! # The flat state encoding

  `LocalState` is indexed by whether the state is terminal, which is what makes the block semantics
  typecheck: only a terminal statement may produce a `done`. `StrongRefinement` cannot use an
  indexed state type — its relation has to hold source and target states of one fixed type — so item
  7 works over `LocalState'`, where the index becomes an ordinary `Option String` field: `none` for
  running, `some l` for done at label `l`.

  `toLocalState'` is the translation, `toLocalState'_inj` its injectivity, and the `*_eq_map` lemmas
  below say the two encodings give the same block semantics up to that translation. The `*_glue`
  lemmas are the membership-level corollaries, which is the form item 7 actually rewrites with.
-/

section Flat

variable {V : Type}

/-- `LocalState` with the terminality index traded for an `Option String` field. -/
abbrev LocalState' (V : Type) : Type := Memory V × FIFOs V × Option String

/-- `LocalState` in the flat encoding. -/
def LocalState.toLocalState' : {b : Bool} → LocalState V b → LocalState' V
  | false, .running M F => ⟨M, F, .none⟩
  | true, .done M F l => ⟨M, F, .some l⟩

theorem LocalState.toLocalState'_inj ⦃b : Bool⦄ :
    Function.Injective (@LocalState.toLocalState' V b) := by
  cases b with
  | false => rintro ⟨M, F⟩ ⟨M', F'⟩ (_|_); rfl
  | true => rintro (_|⟨M, F, l⟩) (_|⟨M', F', l'⟩) (_|_); rfl

variable [ExprSemantics V]

/-- `Statement.reducing` in the flat encoding. A step is only taken from a *running* state, so the
source's label field must be `none`; the target's records whether the statement was terminal. -/
def Statement.reducing' {b b' : Bool} (S : ComputableGuardedPlusCal.Statement b b') :
    Set (LocalState' V × List (Behavior V) × LocalState' V) :=
  {⟨⟨M, F, l⟩, ε, ⟨M', F', l'⟩⟩ | ∃ σ' : LocalState V b',
    l = Option.none ∧ ⟨LocalState.running M F, ε, σ'⟩ ∈ Statement.reducing S ∧ match b', σ' with
      | true, σ' => ∃ l'', σ' = LocalState.done M' F' l'' ∧ l' = Option.some l''
      | false, σ' => σ' = LocalState.running M' F' ∧ l' = Option.none}

@[inherit_doc Statement.reducing']
def Statement.aborting' {b b' : Bool} (S : ComputableGuardedPlusCal.Statement b b') :
    Set (LocalState' V × List (Behavior V)) :=
  {⟨⟨M, F, l⟩, ε⟩ | l = Option.none ∧ ⟨LocalState.running M F, ε⟩ ∈ Statement.aborting S}

@[inherit_doc Statement.reducing']
def Statement.diverging' {b b' : Bool} (S : ComputableGuardedPlusCal.Statement b b') :
    Set (LocalState' V × List (Behavior V)) :=
  {⟨⟨M, F, l⟩, ε⟩ | l = Option.none ∧ ⟨LocalState.running M F, ε⟩ ∈ Statement.diverging S}

private theorem Statement.reducing'_eq_map {b b' : Bool}
    (S : ComputableGuardedPlusCal.Statement b b') :
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
    (S : ComputableGuardedPlusCal.Statement b b') :
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
    (S : ComputableGuardedPlusCal.Statement b b') :
    Statement.diverging' (V := V) S =
      Prod.map LocalState.toLocalState' id '' Statement.diverging S := by
  ext ⟨⟨M, F, l⟩, e⟩
  constructor
  · rintro ⟨rfl, sem⟩
    exists _, sem
  · rintro ⟨⟨⟨_⟩, _⟩, _, _|_⟩
    trivial

theorem Block.reducing'_eq_map {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map₃ LocalState.toLocalState' id LocalState.toLocalState' ''
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.reducing_map _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.reducing'_eq_map S]

theorem Block.aborting'_eq_map {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.aborting (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.aborting')
        (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map LocalState.toLocalState' id ''
        Block.aborting (λ ⦃_⦄ ↦ Statement.aborting) (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.aborting_map _ _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.aborting'_eq_map S]
  conv_rhs => enter [2, b, S]; rw [← Statement.reducing'_eq_map S]

theorem Block.diverging'_eq_map {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
        (λ ⦃_⦄ ↦ Statement.reducing') B =
      Prod.map LocalState.toLocalState' id ''
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B := by
  rw [Block.diverging_map _ _ _ LocalState.toLocalState'_inj]
  conv_rhs => enter [1, b, S]; rw [← Statement.diverging'_eq_map S]
  conv_rhs => enter [2, b, S]; rw [← Statement.reducing'_eq_map S]

/-! The four membership-level corollaries item 7 rewrites with. Each says that a concrete indexed
step is the same fact as the corresponding flat one — the direction that matters is `mp`, which
lets an indexed hypothesis be fed to a `StrongRefinement` goal stated over `LocalState'`. -/

theorem LocalState.sem_glue₁ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V} {l : String}
    {ε : List (Behavior V)} {B : Block (ComputableGuardedPlusCal.Statement g) true} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.done M₂ F₂ l⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, some l)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩; exact sem

theorem LocalState.sem_glue₂ {g : Bool} {M₁ M₂ : Memory V} {F₁ F₂ : FIFOs V}
    {ε : List (Behavior V)} {B : Block (ComputableGuardedPlusCal.Statement g) false} :
    ⟨LocalState.running M₁ F₁, ε, LocalState.running M₂ F₂⟩ ∈
        Block.reducing (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε, (M₂, F₂, none)⟩ ∈
        Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.reducing'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _, _|⟨_, _⟩⟩, sem, _|_⟩; exact sem

theorem LocalState.abort_glue {g b : Bool} {M₁ : Memory V} {F₁ : FIFOs V}
    {ε : List (Behavior V)} {B : Block (ComputableGuardedPlusCal.Statement g) b} :
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
    {ε : List (Behavior V)} {B : Block (ComputableGuardedPlusCal.Statement g) b} :
    ⟨LocalState.running M₁ F₁, ε⟩ ∈
        Block.diverging (λ ⦃_⦄ ↦ Statement.diverging) (λ ⦃_⦄ ↦ Statement.reducing) B ↔
      ⟨(M₁, F₁, none), ε⟩ ∈
        Block.diverging (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ Statement.diverging')
          (λ ⦃_⦄ ↦ Statement.reducing') B := by
  rw [Block.diverging'_eq_map, Set.mem_image]
  constructor
  · intro sem; exists _, sem
  · rintro ⟨⟨⟨_, _⟩, _⟩, sem, _|_⟩; exact sem

end Flat

end GuardedPlusCal

end
