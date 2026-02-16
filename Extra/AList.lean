import Mathlib.Data.List.AList
import Mathlib.Data.Finmap
import Extra.List
import Batteries.Classes.SatisfiesM
import CustomPrelude

namespace AList
  def merge.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} (x y : AList β) (f : (x : α) → β x → β x → β x) : AList β :=
    y.foldl (d := x) λ acc k b ↦
      if h : k ∈ acc then acc.replace k (f k (acc.lookup k |>.get (AList.lookup_isSome.mpr h)) b) else acc.insert k b

  instance {α : Type _} {β : α → Type _} [Repr α] [(x : α) → Repr (β x)] : Repr (AList β) where
    reprPrec list _ :=
      .bracket "{ "
        ("entries" ++ " := " ++ .group (.nest 11 <| repr list.entries) ++ "," ++ .line ++
         "nodupKeys" ++ " := " ++ "⋯")
        " }"

  @[inline]
  def find?.{u, v} {α : Type u} {β : α → Type v} (p : α → Bool) (x : AList β) : Option ((k : α) × β k) :=
    x.entries.find? (p ∘ Sigma.fst)

  @[inline]
  def get.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} (x : AList β) (k : α) (h : k ∈ x) : β k :=
    x.lookup k |>.get (lookup_isSome.mpr h)

  theorem lookup_eq_some_get_of_mem.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {k : α} {x : AList β} (k_mem : k ∈ x) :
      AList.lookup k x = some (x.get k k_mem) := by
    grind [= get]

  def map.{u, v} {α : Type u} {β γ : α → Type v} (f : (k : α) → β k → γ k) (x : AList β) : AList γ where
    entries := x.entries.map λ ⟨k, b⟩ ↦ ⟨k, f k b⟩
    nodupKeys := by
      unfold List.NodupKeys List.keys
      have : List.map (λ ⟨k, b⟩ => Sigma.mk k (f k b) |>.fst) x.entries = List.map Sigma.fst x.entries := by congr
      rw [List.map_map, Function.comp_def, this]
      exact x.nodupKeys

  theorem in_entries_to_in_keys.{u, v} {α : Type u} {β : α → Type v} {k : α} {v : β k} {x : AList β} : ⟨k, v⟩ ∈ x.entries → k ∈ x.keys := by
    unfold AList.keys List.keys
    generalize x.entries = xs
    intros k_v_in_entries
    induction k_v_in_entries with
      | head _ => exact List.mem_of_mem_head? rfl
      | tail y _ IH => exact List.mem_of_mem_tail IH

  def traverse {α : Type} [DecidableEq α] {β γ : α → Type} {F : Type → Type} [Applicative F] (f : (k : α) → β k → F (γ k)) (x : AList β) : F (AList γ) :=
    (λ kvs : List (Sigma γ) ↦ {entries := kvs.dedupKeys, nodupKeys := List.nodupKeys_dedupKeys ..})
      -- NOTE: I don't know how else to state that the keys are not duplicated.
      -- In practice, I don't know of any applicative functor for which our list traversal *may* duplicate our keys,
      -- so this `List.dedupKeys` should actually do nothing (while still consuming runtime, though…).
      --
      -- Also note that we can state and prove that the set of keys in `kvs` is a subset of `x.keys` (with some clever use of `Subtype` and `List.attach`),
      -- BUT this doesn't help us in proving that `kvs` doesn't contain duplicated keys (because we may only state properties on individual keys,
      -- in isolation with other keys of the list).
      --
      -- This problem actually stems from the fact that we cannot state properties on the result of `x.entries.traverse`, because its
      -- result is in the applicative functor `F`, which we may not unwrap.
      <$> x.entries.traverse λ ⟨k, v⟩ ↦ Sigma.mk k <$> f k v
    -- (λ (kvs : List {y : Nat × Sigma γ // ∃ (h : y.fst < x.entries.length), x.entries[y.fst].fst = y.snd.fst}) ↦ {
    --   entries := kvs.unattach.map Prod.snd |>.dedupKeys
    --   nodupKeys := List.nodupKeys_dedupKeys ..
    -- }) <$> x.entries.enum.attach.traverse λ ⟨⟨i, k, x⟩, h⟩ ↦ (λ v ↦ Subtype.mk (i, Sigma.mk k v) (by
    --   obtain ⟨i_valid, ith_eq⟩ := List.mem_enum h
    --   apply congrArg Sigma.fst at ith_eq
    --   exists i_valid
    --   symm
    --   simpa using ith_eq
    -- )) <$> f k x

    def removeAll.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} (ks : List α) (x : AList β) : AList β :=
      ks.foldl (init := x) λ x k ↦ x.erase k

    theorem lookup_removeAll_mem.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {ks : List α} {k} {x : AList β}
      (k_in : k ∈ ks) : AList.lookup k (AList.removeAll ks x) = .none := by
        unfold removeAll

        induction k_in with
        | head ks =>
          rw [List.foldl_eq_of_comm']
          · rw [lookup_erase]
          · intros _ _ _
            apply erase_erase
        | tail k' k_in IH =>
          rw [List.foldl_eq_of_comm']
          · by_cases k_eq : k = k'
            · subst k
              rw [lookup_erase]
            · rwa [lookup_erase_ne _]
              · assumption
          · intros _ _ _
            apply erase_erase

  theorem lookup_removeAll_not_mem.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {ks : List α} {k} {x : AList β}
    (k_in : k ∉ ks) : AList.lookup k (AList.removeAll ks x) = AList.lookup k x := by
      unfold removeAll

      induction ks with
      | nil => rw [List.foldl_nil]
      | cons k' ks IH =>
        apply List.ne_and_not_mem_of_not_mem_cons at k_in
        obtain ⟨k_ne, k_not_in_ks⟩ := k_in
        rw [List.foldl_eq_of_comm']
        · rw [lookup_erase_ne]
          · apply IH
            assumption
          · assumption
        · intros _ _ _
          apply erase_erase

  theorem removeAll_nil.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} : AList.removeAll [] x = x := by
    unfold removeAll
    rw [List.foldl_nil]

  theorem removeAll_cons.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {ks : List α} : AList.removeAll (k :: ks) x = AList.removeAll ks (AList.erase k x) := by
    unfold removeAll
    rw [List.foldl_cons]

  theorem removeAll_cons'.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {ks : List α} : AList.removeAll (k :: ks) x = AList.erase k (AList.removeAll ks x) := by
    unfold removeAll
    rw [List.foldl_eq_of_comm']
    intros _ _ _
    apply erase_erase

  theorem lookup_replace.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {v : β k} : AList.lookup k (AList.replace k v x) = v <$ AList.lookup k x := by
    unfold AList.lookup AList.replace
    apply List.dlookup_kreplace

  theorem lookup_replace_ne.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k k' : α} {v : β k'} (k_ne : k ≠ k') : AList.lookup k (AList.replace k' v x) = AList.lookup k x := by
    unfold AList.lookup AList.replace
    apply List.dlookup_kreplace_ne
    assumption

  theorem lookup_map.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {f : (k : α) → β k → β k} : AList.lookup k (AList.map f x) = f k <$> AList.lookup k x := by
    unfold AList.lookup AList.map
    erw [List.dlookup_map₂]
    rfl

  theorem List.keys_map_const.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : List (Sigma β)} {f : (k : α) → β k → β k} :
    (List.map (λ ⟨k ,v⟩ ↦ ⟨k, f k v⟩) x).keys = x.keys := by
      induction x with
      | nil => rfl
      | cons x xs IH =>
        simp_rw [List.map_cons, List.keys_cons]
        congr

  theorem map_insert.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {v : β k} {f : (k : α) → β k → β k} :
    AList.map f (AList.insert k v x) = AList.insert k (f k v) (AList.map f x) := by
      unfold AList.map AList.insert
      dsimp
      congr
      by_cases k_in_keys : k ∈ x.entries.keys
      · obtain ⟨_, l₁, l₂, k_not_in, entries_eq, kerase_eq⟩ := List.exists_of_kerase k_in_keys
        rw [entries_eq, kerase_eq] at *
        have k_not_in' : k ∉ (List.map (fun x ↦ ⟨x.fst, f x.fst x.snd⟩) l₁).keys := by
          rwa [List.keys_map_const]
        conv_rhs => rw [List.map_append, List.map_cons, List.kerase_append_right k_not_in']
        rw [List.kerase_cons_eq (by rfl), List.map_append]
      · have h' : k ∉ (List.map (λ ⟨k, v⟩ ↦ ⟨k, f k v⟩) x.entries).keys := by rwa [List.keys_map_const]
        rw [List.kerase_of_notMem_keys k_in_keys, List.kerase_of_notMem_keys h']

  theorem List.kreplace_singleton.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {k : α} {v b : β k} : List.kreplace k v [⟨k, b⟩] = [⟨k, v⟩] := by
    rw [List.kreplace_cons, ite_cond_eq_true]
    apply eq_true
    rfl

  theorem replace_insert.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {v b : β k} : replace k v (insert k b x) = insert k v x := by
    unfold replace insert
    congr
    erw [List.kreplace_cons, ite_cond_eq_true]
    · rfl
    · apply eq_true
      rfl

  theorem List.kreplace_kerase_ne.{v, u} {α : Type u} [DecidableEq α] {β : α → Type v} {x : List (Sigma β)} {k a : α} {v : β k} (h : k ≠ a) :
    List.kreplace k v (List.kerase a x) = List.kerase a (List.kreplace k v x) := by
      induction x with
      | nil => rfl
      | cons x xs IH =>
        by_cases a_eq : a = x.fst
        · subst a
          rw [List.kerase_cons_eq (by rfl), List.kreplace_cons, ite_cond_eq_false]
          · rw [List.kerase_cons_eq (by rfl)]
          · apply eq_false
            exact h
        · rw [List.kerase_cons_ne, List.kreplace_cons, List.kreplace_cons]
          · by_cases k_eq : k = x.fst
            · subst k
              repeat rw [ite_cond_eq_true]
              · rw [List.kerase_cons_ne]
                exact Ne.symm h
              · apply eq_true rfl
              · apply eq_true rfl
            · repeat rw [ite_cond_eq_false]
              · rw [IH, List.kerase_cons_ne]
                exact a_eq
              · apply eq_false k_eq
              · apply eq_false k_eq
          · exact a_eq

  theorem replace_insert_ne.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k a : α} {v : β k} {b : β a} (h : k ≠ a) :
    replace k v (insert a b x) = insert a b (replace k v x) := by
      unfold replace insert
      congr
      dsimp
      erw [List.kreplace_cons, ite_cond_eq_false]
      · congr
        apply List.kreplace_kerase_ne
        exact h
      · apply eq_false
        exact h

  theorem map_ne_eq.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {l : AList β} {a : α} {f : (k : α) → β k → β k} (h : a ∉ l) : map (fun k' v ↦ if k' = a then f k' v else v) l = l := by
    induction l with
    | H0 => rfl
    | IH a' b l _ IH =>
      rw [mem_insert, not_or] at h
      obtain ⟨a_ne_a', a_not_in_l⟩ := h
      specialize IH a_not_in_l
      rw [map_insert, IH, ite_cond_eq_false]
      apply eq_false
      exact Ne.symm a_ne_a'

  theorem replace_eq_map.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {f : (k : α) → β k → β k} {v : β k} (h : AList.lookup k x = some v) :
    AList.map (λ k' v ↦ if k' = k then f k' v else v) x = AList.replace k (f k v) x := by
      induction x with
      | H0 => rfl
      | IH a b l _ IH =>
        rw [map_insert]
        by_cases k_eq : k = a
        · subst k
          rw [AList.lookup_insert] at h
          obtain _|_ := h
          rw [AList.replace_insert, ite_cond_eq_true]
          · rwa [map_ne_eq]
          · apply eq_true
            rfl
        · rw [AList.lookup_insert_ne k_eq] at h
          specialize IH h
          rw [IH, replace_insert_ne k_eq, ite_cond_eq_false]
          apply eq_false
          exact Ne.symm k_eq

  theorem List.kerase_kinsert.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {k : α} {v : β k} {xs : List (Sigma β)} : List.kerase k (List.kinsert k v xs) = List.kerase k xs := by
    simp

  theorem List.kerase_of_not_mem.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {k : α} {xs : List (Sigma β)} (h : k ∉ List.keys xs) : List.kerase k xs = xs := by
    simp [*]

  theorem erase_insert.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {v : β k} : AList.erase k (AList.insert k v x) = AList.erase k x := by
    unfold erase insert
    simp

  theorem lookup_union.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x y : AList β} {k : α} : AList.lookup k (x ∪ y) = (AList.lookup k x <|> AList.lookup k y) := by
    ext v
    erw [lookup_union_eq_some, Option.orElse_eq_some, ← lookup_eq_none]

  theorem union_insert_ext_of_not_mem.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x y : AList β} {k : α} {v : β k} (h : k ∉ x) :
      ∀ k', (x ∪ y.insert k v).lookup k' = ((x ∪ y).insert k v).lookup k' := by
    induction x using insertRec with
    | H0 =>
      simp_rw [empty_union]
      exact λ _ ↦ True.intro
    | IH a b l _ IH =>
      intro k'

      have : k ≠ a := by simp_all
      have : k ∉ l := by simp_all

      rw [← insert_union]
      by_cases h' : k' = a
      · subst k'
        rw [lookup_insert, lookup_insert_ne ‹k ≠ a›.symm, ← insert_union, lookup_insert]
      · rw [lookup_insert_ne h', IH ‹k ∉ l› k']
        by_cases h'' : k' = k
        · subst k'
          rw [lookup_insert, lookup_insert]
        · rw [lookup_insert_ne h'', lookup_insert_ne h'', ← insert_union, lookup_insert_ne h']

  theorem notMem_iff.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} : k ∉ x ↔ x.lookup k = none := by
    iff_intro h h
    · rwa [lookup_eq_none]
    · rwa [lookup_eq_none] at h

  theorem mem_insert_of_ne.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k k' : α} {v : β k'}
    (neq : k ≠ k') :
      k ∈ AList.insert k' v x ↔ k ∈ x := by
    simp only [mem_insert, false_or, neq]

  -- TODO: constructively rewrite this proof?
  theorem mem_of_lookup_eq_some.{u, v} {α : Type u} [DecidableEq α] {β : α → Type v} {x : AList β} {k : α} {v : β k} (h : x.lookup k = some v) : k ∈ x := by
    by_contra! h'
    rw [notMem_iff, h] at h'
    contradiction
end AList
