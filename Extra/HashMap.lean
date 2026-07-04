import Batteries.Data.HashMap.Basic
import Mathlib.Data.List.Defs
import Std.Data.DHashMap.Lemmas
import Std.Data.DHashMap.RawLemmas
import CustomPrelude
import Mathlib.Data.List.Dedup
import Extra.List
import Mathlib.Data.Multiset.Dedup

namespace Std.Internal.List
  theorem keys_dedup_of_distinct.{u, v} {α : Type u} {β : α → Type v} [DecidableEq α] {l : List ((a : α) × β a)}
    (h : DistinctKeys l) :
      (keys l).dedup = keys l := by
    have : (keys l).Nodup := List.Pairwise.imp not_eq_of_beq_eq_false h.distinct
    rw [List.Nodup.dedup this]

  theorem keys_perm_of_perm {α} {β : α → _} {xs ys : List ((a : α) × β a)} (h : xs.Perm ys) : (keys xs).Perm (keys ys) := by
    induction h with
    | nil => exact .nil
    | cons x _ IH =>
      rw [keys_cons, keys_cons]
      apply List.Perm.cons
      apply IH
    | swap x y l =>
      rw [keys_cons, keys_cons, keys_cons, keys_cons]
      apply List.Perm.swap
    | trans _ _ _ _ =>
      apply List.Perm.trans <;> assumption

  theorem keys_replaceEntry.{u, v} {α : Type u} {β : α → Type v} [DecidableEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l = true) (h' : DistinctKeys l) :
      keys (replaceEntry k v l) = keys l := by
    induction l with
    | nil => rfl
    | cons x l IH =>
      let ⟨k', v'⟩ := x

      unfold replaceEntry
      by_cases h'' : k' == k
      · rw [h'', cond_true]
        rw [beq_iff_eq] at h''
        subst k'
        rfl
      · apply eq_false_of_ne_true at h''
        rw [h'', cond_false]
        rw [beq_eq_false_iff_ne] at h''

        replace h : containsKey k l = true := by simp_all
        replace h' : DistinctKeys l := by simp_all

        rw [keys_cons, IH h h', ← keys_cons (v := v')]

  theorem keys_insertEntry.{u, v} {α : Type u} {β : α → Type v} [DecidableEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : DistinctKeys l) :
      (keys (Std.Internal.List.insertEntry k v l)).Perm (keys l ++ [k]).dedup := by
    by_cases h' : containsKey k l
    · rw [insertEntry_of_containsKey h', keys_replaceEntry h' h]
      symm
      trans (keys l).dedup
      · apply List.Subset.dedup_append_left
        rw [← mem_keys_iff_contains] at h'
        rwa [List.singleton_subset]
      · rw [keys_dedup_of_distinct h]
    · rw [Bool.bool_iff_false] at h'
      rw [insertEntry_of_containsKey_eq_false h', keys_cons, List.Disjoint.dedup_append]
      · rw [List.dedup_singleton, keys_dedup_of_distinct h]
        exact List.cons_perm_concat
      · rwa [List.disjoint_singleton, mem_keys_iff_contains, Bool.bool_iff_false]
end Std.Internal.List

namespace Std.DHashMap
  open Internal Raw Raw₀

  theorem keys_eq_map_fst_toList {α β} [BEq α] [Hashable α] {t : DHashMap α β} : t.keys = t.toList.map Sigma.fst := by
    unfold keys toList
    rw [toList_eq_toListModel, keys_eq_keys_toListModel, ← Internal.List.keys_eq_map]

  attribute [local instance 5] instDecidableEqOfLawfulBEq

  theorem keys_insert_perm_dedup {α} {β : α → _} [DecidableEq α] [Hashable α] [LawfulHashable α] {k : α} {v : β k} (t : DHashMap α β) :
      (t.insert k v).keys.Perm (t.keys ++ [k]).dedup := by
    unfold insert keys
    simp [Raw₀.insert_eq_insertₘ]
    simp_to_model [keys]

    have t_wf : WFImp t.inner := by
      apply Internal.Raw.WF.out
      exact t.wf

    trans
    · apply Internal.List.keys_perm_of_perm
      apply Internal.Raw₀.toListModel_insertₘ
      exact t_wf
    · apply Internal.List.keys_insertEntry
      exact t_wf.distinct

  namespace Const
  end Const
end Std.DHashMap

set_option linter.deprecated false in
@[deprecated "Remove this instance once `Batteries.HashMap` either gets removed or becomes an alias for `Std.HashMap`" (since := "07/06/3035")]
instance {α β} [BEq α] [Hashable α] : Coe (Std.HashMap α β) (Batteries.HashMap α β) where
  coe x := ⟨x⟩

namespace Std.HashMap
  -- def mapVal {α β γ} [BEq α] [Hashable α] (f : α → β → γ) (t : HashMap α β) : HashMap α γ where
  --   val := t.val.mapVal f
  --   property := t.val.WF.mapVal

  abbrev find? {α β} [BEq α] [Hashable α] (m : HashMap α β) (k : α) : Option β := Prod.snd <$> m.findEntry? k

  def traverseWithKey {α β γ} [BEq α] [Hashable α] {m : Type _ → Type _} [Applicative m] (f : α → β → m γ) (t : HashMap α β) : m (HashMap α γ) :=
    -- ugly way: copy into list, traverse list, then remake hashmap
    -- very inefficient, but all in all I don't quite care now
    let t' := t.toList
    let t' : m (List (α × γ)) := t'.traverse λ ⟨k, v⟩ ↦ Prod.mk k <$> f k v
    HashMap.ofList <$> t'

  attribute [local instance 5] instDecidableEqOfLawfulBEq

  theorem keys_eq_map_fst_toList {α β} [BEq α] [LawfulBEq α] [Hashable α] {t : HashMap α β} : t.keys = t.toList.map Prod.fst :=
    Std.HashMap.map_fst_toList_eq_keys.symm

  theorem toList_eq_inner_toList {α β} [BEq α] [LawfulBEq α] [Hashable α] {t : HashMap α β} : t.toList = DHashMap.Const.toList t.inner := rfl

  theorem keys_Nodup {α β} [DecidableEq α] [Hashable α] (t : HashMap α β) : t.keys.Nodup :=
    List.Pairwise.imp ne_of_beq_false Std.HashMap.distinct_keys

  theorem keys_union_eq {α β} [DecidableEq α] [Hashable α] {t u : HashMap α β} : t.keys ∪ u.keys = t.keys.removeAll u.keys ++ u.keys := by
    have : (t.keys.removeAll u.keys).dedup = t.keys.removeAll u.keys := by
      rw [List.dedup_eq_self]
      apply List.Nodup.sublist (l₂ := t.keys)
      · exact List.filter_sublist
      · apply keys_Nodup

    rw [List.union_eq_append, this]

  theorem keys_insert_perm_dedup {α β} [DecidableEq α] [Hashable α] {t : HashMap α β} {k : α} {v : β} : (t.insert k v).keys.Perm (t.keys ++ [k]).dedup := by
    unfold insert keys
    apply DHashMap.keys_insert_perm_dedup

  theorem keys_insert_perm_of_mem {α β} [DecidableEq α] [Hashable α] {t : HashMap α β} {k : α} {v : β} (h : k ∈ t) : (t.insert k v).keys.Perm t.keys := by
    trans (t.keys ++ [k]).dedup
    · exact keys_insert_perm_dedup
    · replace h : k ∈ t.keys := by simp [h]
      trans
      · apply List.Subset.dedup_append_left
        simp [*]
      · rw [List.Nodup.dedup (keys_Nodup _)]

  theorem keys_insert_perm_of_not_mem {α β} [DecidableEq α] [Hashable α] {t : HashMap α β} {k : α} {v : β} (h : k ∉ t) : (t.insert k v).keys.Perm (t.keys ++ [k]) := by
    trans (t.keys ++ [k]).dedup
    · exact keys_insert_perm_dedup
    · replace h : k ∉ t.keys := by simp [h]
      rw [List.Disjoint.dedup_append, List.Nodup.dedup (keys_Nodup _), List.dedup_singleton]
      rwa [List.disjoint_singleton]

  theorem keys_insert_perm {α β} [DecidableEq α] [Hashable α] {t : HashMap α β} {k : α} {v : β} : (t.insert k v).keys.Perm (t.keys.filter (· ≠ k) ++ [k]) := by
    by_cases h : k ∈ t.keys
    · obtain ⟨xs, ys, h'⟩ := List.append_of_mem h
      rw [List.append_cons] at h'

      rw [List.filter_ne_of_nodup (keys_Nodup _) h']
      trans t.keys
      · apply keys_insert_perm_of_mem
        exact mem_of_mem_keys h
      · rw [h', List.append_assoc, List.append_assoc, List.perm_append_left_iff]
        exact List.perm_append_comm
    · have : ∀ k' ∈ t.keys, decide (k' ≠ k) = true := by
        simp_rw [decide_eq_true_eq]
        rwa [← List.forall_mem_ne'] at h

      rw [List.filter_eq_self.mpr this]

      apply keys_insert_perm_of_not_mem
      simp_all

  private theorem decide_ne_iff_beq {α} [DecidableEq α] {x y : α} : decide (x ≠ y) = !x == y := by
    rw [decide_not, Bool.beq_eq_decide_eq]

  theorem keys_mergeWith_perm_union {α β} [DecidableEq α] [Hashable α] {t u : HashMap α β} (f : α → β → β → β) : (mergeWith f t u).keys.Perm (t.keys ∪ u.keys) := by
    unfold mergeWith fold

    rw [DHashMap.Const.fold_eq_foldl_toList, ← toList_eq_inner_toList, keys_union_eq]
    repeat rw [keys_eq_map_fst_toList (t := u)]

    have u_keys_nodup : (List.map Prod.fst u.toList).Nodup := by
      rw [← keys_eq_map_fst_toList]
      apply keys_Nodup

    generalize u.toList = u at u_keys_nodup ⊢
    induction u generalizing t with
    | nil => rw [List.foldl_nil, List.map_nil, List.removeAll_nil, List.append_nil]
    | cons x u IH =>
      rw [List.foldl_cons, List.map_cons, List.removeAll_cons]
      trans
      · apply IH
        apply List.Nodup.of_cons
        assumption
      · rw [List.append_cons]
        apply List.Perm.append
        · split <;> {
          · trans
            · apply List.removeAll_perm_of_perm
              apply keys_insert_perm
            · have : x.1 ∉ List.map Prod.fst u := by simp_all
              rw [← List.concat_eq_append, ← List.removeAll_concat_of_not_mem this, List.concat_eq_append]
              conv_lhs => enter [1, 1, 1, x]; apply decide_ne_iff_beq
          }
        · rfl

  theorem keys_mergeWith_perm {α β} [DecidableEq α] [Hashable α] {t u : HashMap α β} (f : α → β → β → β) : (t.mergeWith f u).keys.Perm (t.keys ++ u.keys).dedup := by
    rw [List.dedup_append, List.Nodup.dedup (keys_Nodup _)]
    apply keys_mergeWith_perm_union _
