import PlusCalCompiler.CoreTLAPlus.Semantics.Operational
import Extra.List
import Extra.AList
import Extra.Nat

namespace List
  theorem traverse_eq_some {α β : Type _} (f : α → Option β) {xs ys} :
      List.traverse f xs = .some ys ↔ List.Forall₂ (f · = .some ·) xs ys := by
    induction xs, ys using List.induction₂' with
    | nil_nil => simp [List.traverse_nil']
    | nil_cons y ys => simp [List.traverse_nil']
    | cons_nil x xs =>
      simp! [List.traverse_cons']
      erw [Option.bind_eq_some_iff]
      push_neg
      intros _ h₁ h₂
      erw [Option.map_eq_some_iff] at *
      (rcases h₁, h₂ with ⟨⟨_, _, rfl⟩, ⟨_, _, _|_⟩⟩)
    | cons_cons x y xs ys IH =>
      erw [List.traverse_cons', List.forall₂_cons, ← IH, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨_, h₁, h₂⟩
        rw [Option.map_eq_map, Option.map_eq_some_iff] at h₁ h₂
        rcases h₁, h₂ with ⟨⟨_, _, rfl⟩, ⟨_, _, _|_⟩⟩
        and_intros <;> assumption
      · rintro ⟨h₁, h₂⟩
        exists (λ ys ↦ y :: ys)
        rw [h₁, h₂]
        and_intros <;> rfl

  theorem traverse_eq_none {α β : Type _} (f : α → Option β) {xs} :
      List.traverse f xs = none ↔ ∃ x ∈ xs, f x = none := by
    induction xs with
    | nil =>
      simp [List.traverse_nil']
    | cons x xs IH =>
      simp_rw [List.traverse_cons', seq_eq_bind, Option.bind_eq_bind,
               Option.map_eq_map, Option.bind_eq_none_iff, Option.map_eq_none_iff,
               Option.map_eq_some_iff, IH]
      iff_intro h h
      · cases f_x_eq : f x with
        | none =>
          exists x, List.mem_cons_self
        | some g =>
          obtain ⟨x', x'_in, f_x'_eq⟩ := h (λ xs ↦ g :: xs) ⟨g, f_x_eq, rfl⟩
          exists x', List.mem_cons_of_mem _ x'_in
      · rintro _ ⟨g, f_x_eq, rfl⟩
        obtain ⟨x', ⟨⟩|⟨_, x'_in⟩, f_x'_eq⟩ := h
        · rw [f_x'_eq] at f_x_eq
          contradiction
        · exists _, x'_in

  theorem traverse_attachWith_eq_traverse {α β} {F : Type _ → Type _} [Applicative F] {xs : List α} {f : α → F β} {P : α → Prop} (h : ∀ x ∈ xs, P x) :
      List.traverse (λ ⟨x, _⟩ ↦ f x) (List.attachWith xs P h) = List.traverse f xs := by
    induction xs with
    | nil => simp [List.traverse_nil']
    | cons x xs IH => simp [List.traverse_cons', IH]

  theorem traverse_attach_eq_traverse {α β} {F : Type _ → Type _} [Applicative F] {xs : List α} (f : α → F β) :
      List.traverse (λ ⟨x, _⟩ ↦ f x) (List.attach xs) = List.traverse f xs := by
    apply traverse_attachWith_eq_traverse

  theorem traverse_attach_eq_traverse' {α β} {F : Type _ → Type _} [Applicative F] {xs : List α} (f : α → F β) :
      List.traverse (λ x ↦ f x.val) (List.attach xs) = List.traverse f xs := by
        apply traverse_attach_eq_traverse

  theorem attach_map_val' {α β} {xs : List α} {f : α → β} : List.map (λ ⟨x, _⟩ ↦ f x) xs.attach = List.map f xs := by
    simp
end List

namespace CoreTLAPlus
  theorem prims_Head : prims.lookup "Head" = Head := by
    unfold prims
    rw [AList.lookup_insert]

  theorem prims_Tail : prims.lookup "Tail" = Tail := by
    unfold prims
    rw [AList.lookup_insert_ne, AList.lookup_insert]
    simp

  theorem prims_Len : prims.lookup "Len" = Len := by
    unfold prims
    rw [AList.lookup_insert_ne, AList.lookup_insert_ne, AList.lookup_insert]
    · simp
    · simp

  theorem prims_keys_eq : prims.keys = ["Head", "Tail", "Len"] := rfl

  theorem prims_toFinmap_keys_eq : prims.toFinmap.keys = {"Head", "Tail", "Len"} := rfl

  theorem Head_spec {vs} {v} (h : Head vs = .some v) : ∃ v' vs', vs = [.seq (v' :: vs')] ∧ v = v' := by
    unfold Head at h
    split at h using vs_singleton
    · rw [List.length_eq_one_iff] at vs_singleton
      obtain ⟨v', rfl⟩ := vs_singleton
      split at h using v' vs v'_eq
      · refine ⟨v, vs.drop 1, ?_, rfl⟩
        cases v'_eq
        congr
        obtain ⟨vs_len_pos, head_eq⟩ := List.getElem_of_getElem? h
        obtain ⟨_, _, rfl⟩ := List.exists_cons_of_length_pos vs_len_pos
        cases head_eq
        rw [List.drop_one, List.tail_cons, List.getElem_zero, List.head_cons]
      · contradiction
    · contradiction

  theorem Tail_spec {vs} {v} (h : Tail vs = .some v) : ∃ v' vs', vs = [.seq (v' :: vs')] ∧ v = .seq vs' := by
    unfold Tail at h
    split at h using vs_singleton
    · rw [List.length_eq_one_iff] at vs_singleton
      obtain ⟨v', rfl⟩ := vs_singleton
      split at h using v' vs' v'_eq
      · obtain _|_ := h
        refine ⟨v', vs', ?_, rfl⟩
        simp_all
      · contradiction
    · contradiction

  theorem Len_spec {vs} {v} (h : Len vs = .some v) : ∃ vs', vs = [.seq vs'] ∧ v = .int vs'.length := by
    unfold Len at h
    split at h using vs_singleton
    · rw [List.length_eq_one_iff] at vs_singleton
      obtain ⟨v', rfl⟩ := vs_singleton
      split at h using vs' v'_eq
      · obtain _|_ := h
        refine ⟨vs', ?_, rfl⟩
        simp_all
      · contradiction
    · contradiction

  theorem eval_mem_ext {M₁ M₂ : Memory} (mem_ext : ∀ v, M₁.lookup v = M₂.lookup v) : {e : Expression Typ} → eval M₁ e = eval M₂ e
    | .var pos name => by
      unfold eval
      rw [mem_ext name]
    | .str pos raw => by unfold eval; rfl
    | .nat pos raw => by unfold eval; rfl
    | .bool pos raw => by unfold eval; rfl
    | .set pos elems => by
      have IH : ∀ e ∈ elems, eval M₁ e = eval M₂ e := λ _ _ ↦ eval_mem_ext mem_ext
      unfold eval
      congr
      ext1 ⟨e, e_in⟩
      apply IH _ e_in
    | .record pos fields => by
      have IH : ∀ f ∈ fields, eval M₁ f.2.2 = eval M₂ f.2.2 := λ f f_in ↦ eval_mem_ext mem_ext
      unfold eval
      congr
      ext ⟨⟨x, τ, e⟩, f_in⟩
      dsimp
      erw [IH ⟨x, τ, e⟩ f_in]
    | .prefix pos op e => by
      have IH : eval M₁ e = eval M₂ e := eval_mem_ext mem_ext
      unfold eval
      rw [IH]
    | .infix pos e₁ op e₂ => by
      have IH₁ : eval M₁ e₁ = eval M₂ e₁ := eval_mem_ext mem_ext
      have IH₂ : eval M₁ e₂ = eval M₂ e₂ := eval_mem_ext mem_ext
      unfold eval
      rw [IH₁, IH₂]
    | .funcall pos fn args => by
      have IH₁ : eval M₁ fn = eval M₂ fn := eval_mem_ext mem_ext
      have IH₂ : ∀ e ∈ args, eval M₁ e = eval M₂ e := λ _ _ ↦ eval_mem_ext mem_ext
      unfold eval
      congr
      · ext ⟨arg, arg_in⟩
        dsimp
        rw [IH₂ _ arg_in]
      · ext1
        congr
    | .access pos e x => by
      have IH : eval M₁ e = eval M₂ e := eval_mem_ext mem_ext
      unfold eval
      rw [IH]
    | .seq pos es => by
      have IH : ∀ e ∈ es, eval M₁ e = eval M₂ e := λ _ _ ↦ eval_mem_ext mem_ext
      unfold eval
      congr
      ext1 ⟨e, e_in⟩
      apply IH _ e_in
    | .opcall pos fn args => by
      have IH₁ : eval M₁ fn = eval M₂ fn := eval_mem_ext mem_ext
      have IH₂ : ∀ e ∈ args, eval M₁ e = eval M₂ e := λ _ _ ↦ eval_mem_ext mem_ext
      unfold eval
      rw [IH₁]
      congr
      ext ⟨e, e_in⟩
      dsimp
      rw [IH₂ e e_in]
    | .except pos fn upds => by
      have IH₁ : eval M₁ fn = eval M₂ fn := eval_mem_ext mem_ext
      have IH₂ : ∀ r ∈ upds, eval M₁ r.2 = eval M₂ r.2 := λ _upd _ ↦ eval_mem_ext mem_ext
      have IH₃ : ∀ r ∈ upds, ∀ k ∈ r.1, match k with | .inr _ => True | .inl es => ∀ e ∈ es, eval M₁ e = eval M₂ e := λ _upd _ k _ ↦ match k with
        | .inr _ => True.intro
        | .inl _es => λ _e _ ↦ eval_mem_ext mem_ext

      unfold eval
      congr 1
      ext1
      congr 2
      ext1 ⟨⟨upd, e⟩, p⟩
      dsimp
      congr
      · ext1 ⟨_, p'⟩
        split
        · rfl
        · congr
          ext1 ⟨_, p''⟩
          injections; subst_eqs
          rw [IH₃ _ p _ p' _ p'']
      · rw [IH₂ _ p]
  termination_by e => e
  decreasing_by
    all_goals simp_wf; try decreasing_trivial
    · calc
        sizeOf f.2.2 < sizeOf f := let ⟨_, _, _⟩ := f; by simp +arith
        _ < sizeOf fields := by decreasing_trivial
        _ < _ := by simp +arith
    · calc
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial
    · apply Nat.le_of_lt
      calc
        _ < sizeOf (Sum.inl (β := String) _es) := by decreasing_trivial
        _ < sizeOf _upd.1 := by decreasing_trivial
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial

  theorem eval_not_fv_irrel {M : Memory} {v} : {e : Expression Typ} → v ∉ e.freeVars → eval M e = eval (M.erase v) e
    | .var pos name, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      rw [List.mem_singleton] at v_not_in_e
      unfold eval
      rw [AList.lookup_erase_ne (Ne.symm v_not_in_e)]
    | .str pos raw, v_not_in_e => by unfold eval; rfl
    | .nat pos raw, v_not_in_e => by unfold eval; rfl
    | .bool pos raw, v_not_in_e => by unfold eval; rfl
    | .set pos elems, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      simp_rw [List.mem_flatMap, not_exists, not_and] at v_not_in_e

      have IH : ∀ e ∈ elems, v ∉ e.freeVars → eval M e = eval (M.erase v) e := λ _ _ ↦ eval_not_fv_irrel

      unfold eval
      congr
      ext1 ⟨e, e_in⟩
      apply IH _ e_in
      apply v_not_in_e ⟨e, e_in⟩
      apply List.mem_attach
    | .record pos fields, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      simp_rw [List.mem_flatMap, not_exists, not_and] at v_not_in_e

      have IH : ∀ f ∈ fields, eval M f.2.2 = eval (M.erase v) f.2.2 := λ _ f_in ↦ eval_not_fv_irrel (v_not_in_e _ (List.mem_attach _ ⟨_, f_in⟩))

      unfold eval
      congr
      ext1 ⟨f, f_in⟩
      dsimp
      rw [IH _ f_in]
    | .prefix pos op e, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e

      have IH : eval M e = eval (M.erase v) e := eval_not_fv_irrel v_not_in_e

      unfold eval
      rw [IH]
    | .infix pos e₁ op e₂, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      simp_rw [List.not_mem_union_iff] at v_not_in_e

      have IH₁ : eval M e₁ = eval (M.erase v) e₁ := eval_not_fv_irrel v_not_in_e.left
      have IH₂ : eval M e₂ = eval (M.erase v) e₂ := eval_not_fv_irrel v_not_in_e.right

      unfold eval
      rw [IH₁, IH₂]
    | .funcall pos fn args, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and] at v_not_in_e

      have IH₁ : eval M fn = eval (M.erase v) fn := eval_not_fv_irrel v_not_in_e.left
      have IH₂ : ∀ arg ∈ args, eval M arg = eval (M.erase v) arg := λ _ arg_in ↦ eval_not_fv_irrel (v_not_in_e.right _ (List.mem_attach _ ⟨_, arg_in⟩))

      unfold eval
      congr
      · ext1 ⟨_, arg_in⟩
        dsimp
        rw [IH₂ _ arg_in]
      · ext1
        congr
    | .access pos e x, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e

      have IH : eval M e = eval (M.erase v) e := eval_not_fv_irrel v_not_in_e

      unfold eval
      rw [IH]
    | .seq pos es, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      simp_rw [List.mem_flatMap, not_exists, not_and] at v_not_in_e

      have IH : ∀ e ∈ es, v ∉ e.freeVars → eval M e = eval (M.erase v) e := λ _ _ ↦ eval_not_fv_irrel

      unfold eval
      congr
      ext1 ⟨e, e_in⟩
      apply IH _ e_in
      apply v_not_in_e ⟨e, e_in⟩
      apply List.mem_attach
    | .opcall pos fn args, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and] at v_not_in_e

      have IH₁ : eval M fn = eval (M.erase v) fn := eval_not_fv_irrel v_not_in_e.left
      have IH₂ : ∀ e ∈ args, eval M e = eval (M.erase v) e := λ e e_in ↦ eval_not_fv_irrel (v_not_in_e.right ⟨_, e_in⟩ (List.mem_attach _ ⟨_, e_in⟩))

      unfold eval
      congr
      · ext1 ⟨_, e_in⟩
        dsimp
        rw [IH₂ _ e_in]
      · ext1
        congr
    | .except pos fn upds, v_not_in_e => by
      unfold Expression.freeVars at v_not_in_e
      simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and] at v_not_in_e

      have IH₁ : eval M fn = eval (M.erase v) fn := eval_not_fv_irrel v_not_in_e.left
      have IH₂ : ∀ r ∈ upds, eval M r.2 = eval (M.erase v) r.2 := λ _upd p ↦ eval_not_fv_irrel (by
        have := v_not_in_e.right _ (List.mem_attach _ ⟨_, p⟩)
        simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and] at this
        exact this.right
      )
      have IH₃ : ∀ r ∈ upds, ∀ k ∈ r.1, match k with
        | .inr _ => True
        | .inl es => ∀ e' ∈ es, eval M e' = eval (M.erase v) e' := λ _upd p k p' ↦ match k with
        | .inr _ => True.intro
        | .inl _es => λ _e p'' ↦ eval_not_fv_irrel (by
            have := v_not_in_e.right _ (List.mem_attach _ ⟨_, p⟩)
            simp_rw [List.not_mem_union_iff, List.mem_flatMap, not_exists, not_and] at this
            replace this := this.left _ (List.mem_attach _ ⟨_, p'⟩)
            simp_rw [List.mem_flatMap, not_exists, not_and] at this
            exact this _ (List.mem_attach _ ⟨_, p''⟩)
          )

      unfold eval
      congr
      ext1
      congr
      ext1 ⟨_, p⟩
      dsimp
      congr
      · ext1 ⟨_, p'⟩
        split
        · rfl
        · congr
          ext1 ⟨_, p''⟩
          injections; subst_eqs
          rw [IH₃ _ p _ p' _ p'']
      · ext1
        rw [IH₂ _ p]
  termination_by e => e
  decreasing_by
    all_goals simp_wf; try decreasing_trivial
    · rename String × Typ × Expression Typ => f
      calc
        sizeOf f.2.2 < sizeOf f := let ⟨_, _, _⟩ := f; by simp +arith
        _ < sizeOf fields := by decreasing_trivial
        _ < _ := by simp +arith
    · calc
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial
    · apply Nat.le_of_lt
      calc
        _ < sizeOf (Sum.inl (β := String) _es) := by decreasing_trivial
        _ < sizeOf _upd.1 := by decreasing_trivial
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial

  theorem eval_subst {M : Memory} {e e'} {v} {x} (h : x ∉ prims) (eval_e' : M ⊢ e' ⇒ v) : eval M (e.replace x e') = eval (M.insert x v) e := by
    cases e with
    | var pos name =>
      by_cases x_eq : x = name
      · subst x_eq
        rw [Expression.replace, ite_cond_eq_true _ _ (eq_true rfl)]
        conv_rhs => unfold eval; rw [AList.lookup_insert]; apply dite_cond_eq_false (eq_false h)
        assumption
      · rw [Expression.replace, ite_cond_eq_false _ _ (eq_false x_eq)]
        conv_rhs => unfold eval; rw [AList.lookup_insert_ne (Ne.symm x_eq)]
        conv_lhs => unfold eval
    | str pos raw | nat pos raw | bool pos raw =>
      unfold Expression.replace eval
      rfl
    | set pos elems =>
      unfold Expression.replace eval
      congr 1
      simp_rw [List.attach_map, List.traverse_map, Function.comp_def]

      have IH : ∀ e ∈ elems, eval M (e.replace x e') = eval (M.insert x v) e := λ _ _ ↦ eval_subst h eval_e'

      rw [List.traverse_attach_eq_traverse' (f := λ (y : {x : _ // x ∈ elems}) ↦ eval M (Expression.replace (↑y) x e'))]
      congr
      ext1 ⟨e, e_in⟩
      apply IH _ e_in
    | record pos fields =>
      unfold Expression.replace eval
      congr 1
      simp_rw [List.attach_map, List.traverse_map, Function.comp_def]

      have IH : ∀ f ∈ fields, eval M (f.2.2.replace x e') = eval (M.insert x v) f.2.2 := λ _ _ ↦ eval_subst h eval_e'

      rw [List.traverse_attach_eq_traverse' (f := λ (y : {x : _ // x ∈ fields}) ↦ (λ x ↦ (y.1.1, x)) <$> eval M (y.1.2.2.replace x e'))]
      congr 1
      funext ⟨⟨y, τ, e⟩, f_in⟩
      congr 1
      apply IH _ f_in
    | «prefix» pos op e =>
      have IH : eval M (e.replace x e') = eval (M.insert x v) e := eval_subst h eval_e'

      unfold Expression.replace eval
      congr 1
    | «infix» pos e₁ op e₂ =>
      have IH₁ : eval M (e₁.replace x e') = eval (M.insert x v) e₁ := eval_subst h eval_e'
      have IH₂ : eval M (e₂.replace x e') = eval (M.insert x v) e₂ := eval_subst h eval_e'

      unfold Expression.replace eval
      congr 1
      ext1 e₁
      congr 1
    | funcall pos fn args =>
      have IH₁ : eval M (fn.replace x e') = eval (M.insert x v) fn := eval_subst h eval_e'
      have IH₂ : ∀ arg ∈ args, eval M (arg.replace x e') = eval (M.insert x v) arg := λ _ _ ↦ eval_subst h eval_e'

      unfold Expression.replace eval
      congr 1
      · simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
        rw [List.traverse_attach_eq_traverse' (f := λ (y : {x : _ // x ∈ args}) ↦ eval M (Expression.replace (↑y) x e'))]
        congr
        ext1 ⟨_, arg_in⟩
        rw [IH₂ _ arg_in]
      · ext1
        congr
    | access pos e y =>
      have IH : eval M (e.replace x e') = eval (M.insert x v) e := eval_subst h eval_e'

      unfold Expression.replace eval
      congr 1
    | seq pos es =>
      unfold Expression.replace eval
      congr 1
      simp_rw [List.attach_map, List.traverse_map, Function.comp_def]

      have IH : ∀ e ∈ es, eval M (e.replace x e') = eval (M.insert x v) e := λ _ _ ↦ eval_subst h eval_e'

      rw [List.traverse_attach_eq_traverse' (f := λ (y : {x : _ // x ∈ es}) ↦ eval M (Expression.replace (↑y) x e'))]
      congr
      ext ⟨e, e_in⟩ : 1
      apply IH _ e_in
    | opcall pos fn args =>
      unfold Expression.replace eval
      congr 1
      · simp_rw [List.attach_map, List.traverse_map, Function.comp_def]

        have IH₂ : ∀ e ∈ args, eval M (e.replace x e') = eval (M.insert x v) e := λ _ _ ↦ eval_subst h eval_e'

        rw [List.traverse_attach_eq_traverse' (f := λ (y : {x : _ // x ∈ args}) ↦ eval M (Expression.replace (↑y) x e'))]
        congr
        ext1 ⟨e, e_in⟩
        apply IH₂ _ e_in
      · have IH₁ : eval M (fn.replace x e') = eval (M.insert x v) fn := eval_subst h eval_e'
        ext1 args
        congr 1
    | except pos fn upds =>
      unfold Expression.replace eval
      congr 1
      · apply_rules [eval_subst]
      · ext1
        simp_rw [List.attach_map, List.traverse_map, Function.comp_def]

        conv_rhs => rw [← List.traverse_attach_eq_traverse']
        congr 2
        ext1 ⟨⟨_upd, _⟩, _⟩
        congr 1
        · simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
          conv_rhs => rw [← List.traverse_attach_eq_traverse']

          congr 1
          ext1 ⟨⟨_, _⟩, _⟩
          dsimp
          symm
          split using _ | _es _ _ <;> (injections; subst_eqs)
          · rfl
          · symm
            simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
            conv_rhs => rw [← List.traverse_attach_eq_traverse']
            congr 2
            ext1 ⟨⟨_e, _⟩, _⟩
            apply_rules [eval_subst]
        · ext1 _
          congr 1
          apply_rules [eval_subst]
  termination_by e
  decreasing_by
    all_goals simp_wf; try decreasing_trivial
    · rename String × Typ × Expression Typ => f
      calc
        sizeOf f.2.2 < sizeOf f := let ⟨_, _, _⟩ := f; by simp +arith
        _ < sizeOf fields := by decreasing_trivial
        _ < _ := by simp +arith
    · subst_eqs
      apply Nat.le_of_lt
      conv_lhs => change sizeOf (α := List (Expression Typ)) ?_es
      calc
        sizeOf ?_es < sizeOf (Sum.inl (β := String) ?_es) := by decreasing_trivial
        _ < sizeOf _upd.1 := by decreasing_trivial
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by simp +arith
    · calc
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by simp +arith

  theorem eval_subst_of_not_mem_fv_of_eval {M} {x} {e e' : Expression SurfaceTLAPlus.Typ} {v'}
    (x_not_prim : x ∉ prims) (x_not_mem_fv : x ∉ e.freeVars) (eval_e' : M ⊢ e' ⇒ v') :
      eval M (e.replace x e') = eval M e := by
    rw [eval_subst x_not_prim eval_e', eval_not_fv_irrel x_not_mem_fv, AList.erase_insert,
        ← eval_not_fv_irrel x_not_mem_fv]

  theorem eval_subst_of_not_mem_fv {M} {x} {e e' : Expression SurfaceTLAPlus.Typ}
    (x_not_prim : x ∉ prims) (x_not_mem_fv : x ∉ e.freeVars) :
      eval M (e.replace x e') = eval M e := by
    cases e with
    | var pos name =>
      have : x ≠ name := by
        unfold Expression.freeVars at x_not_mem_fv
        exact List.ne_of_not_mem_cons x_not_mem_fv

      unfold Expression.replace
      rw [if_neg ‹x ≠ name›]
    | str pos raw | nat pos raw | bool pos raw =>
      unfold Expression.replace
      rfl
    | set pos es =>
      unfold Expression.replace

      unfold Expression.freeVars at x_not_mem_fv
      rw [List.mem_flatMap] at x_not_mem_fv
      push_neg at x_not_mem_fv

      have IH : ∀ e ∈ es, eval M (e.replace x e') = eval M e := λ e e_in ↦ by
        apply eval_subst_of_not_mem_fv x_not_prim
        apply x_not_mem_fv ⟨_, e_in⟩
        apply List.mem_attach

      unfold eval
      erw [List.attach_map_val' (f := λ e ↦ Expression.replace e x e'), List.traverse_attach_eq_traverse,
           List.traverse_attach_eq_traverse, List.traverse_map,
           ← List.traverse_attach_eq_traverse (xs := es), ← List.traverse_attach_eq_traverse (xs := es)]
      congr 2
      ext ⟨e, e_in⟩ : 1
      apply IH _ e_in
    | record pos fields =>
      unfold Expression.replace

      unfold Expression.freeVars at x_not_mem_fv
      rw [List.mem_flatMap] at x_not_mem_fv
      push_neg at x_not_mem_fv

      have IH : ∀ field ∈ fields, eval M (field.2.2.replace x e') = eval M field.2.2 := λ (n, _τ, e) field_in ↦ by
        apply eval_subst_of_not_mem_fv x_not_prim
        apply x_not_mem_fv ⟨_, field_in⟩
        apply List.mem_attach

      unfold eval
      erw [List.attach_map_val' (f := λ y : _ × _ × _ ↦ (y.1, y.2.1, Expression.replace y.2.2 x e')),
           List.traverse_attach_eq_traverse' (f := λ y : _ × _ × _ ↦ (y.1, ·) <$> eval M y.2.2),
           List.traverse_attach_eq_traverse' (f := λ y : _ × _ × _ ↦ (y.1, ·) <$> eval M y.2.2),
           List.traverse_map,
           ← List.traverse_attach_eq_traverse (xs := fields),
           ← List.traverse_attach_eq_traverse (xs := fields)
           ]
      congr 2
      ext1 ⟨field, field_in_fields⟩
      dsimp [Function.comp]
      congr 1
      apply IH _ field_in_fields
    | «prefix» pos op e =>
      unfold Expression.freeVars at x_not_mem_fv

      have IH : eval M (e.replace x e') = eval M e :=
        eval_subst_of_not_mem_fv x_not_prim x_not_mem_fv

      unfold Expression.replace eval
      congr 1
    | «infix» pos e₁ op e₂ =>
      unfold Expression.freeVars at x_not_mem_fv
      rw [List.mem_union_iff] at x_not_mem_fv
      push_neg at x_not_mem_fv

      have IH₁ : eval M (e₁.replace x e') = eval M e₁ :=
        eval_subst_of_not_mem_fv x_not_prim x_not_mem_fv.1
      have IH₂ : eval M (e₂.replace x e') = eval M e₂ :=
        eval_subst_of_not_mem_fv x_not_prim x_not_mem_fv.2

      unfold Expression.replace eval
      congr 1
      ext1 e₁
      congr 1
    | access pos e y =>
      unfold Expression.replace

      unfold Expression.freeVars at x_not_mem_fv

      have IH : eval M (e.replace x e') = eval M e := by
        apply eval_subst_of_not_mem_fv x_not_prim
        exact x_not_mem_fv

      unfold eval
      rw [IH]
    | seq pos es =>
      unfold Expression.replace

      unfold Expression.freeVars at x_not_mem_fv
      rw [List.mem_flatMap] at x_not_mem_fv
      push_neg at x_not_mem_fv

      have IH : ∀ e ∈ es, eval M (e.replace x e') = eval M e := λ e e_in ↦ by
        apply eval_subst_of_not_mem_fv x_not_prim
        apply x_not_mem_fv ⟨_, e_in⟩
        apply List.mem_attach _ _

      unfold eval
      erw [List.attach_map_val' (f := λ e ↦ Expression.replace e x e'), List.traverse_attach_eq_traverse,
           List.traverse_attach_eq_traverse, List.traverse_map,
           ← List.traverse_attach_eq_traverse (xs := es), ← List.traverse_attach_eq_traverse (xs := es)]
      congr 2
      ext ⟨e, e_in⟩ : 1
      apply IH _ e_in
    | funcall pos fn args | opcall pos fn args =>
      unfold Expression.freeVars at x_not_mem_fv
      rw [List.mem_union_iff, List.mem_flatMap] at x_not_mem_fv
      push_neg at x_not_mem_fv

      unfold Expression.replace eval
      congr 1
      · simp_rw [List.attach_map, List.traverse_map, Function.comp_def]

        have IH₂ : ∀ e ∈ args, eval M (e.replace x e') = eval M e := λ _ _ ↦ eval_subst_of_not_mem_fv x_not_prim (x_not_mem_fv.2 ⟨_, ‹_›⟩ (List.mem_attach _ _))

        rw [List.traverse_attach_eq_traverse' (f := λ (y : {x : _ // x ∈ args}) ↦ eval M (Expression.replace (↑y) x e'))]
        congr
        ext1 ⟨e, e_in⟩
        apply IH₂ _ e_in
      · have IH₁ : eval M (fn.replace x e') = eval M fn := eval_subst_of_not_mem_fv x_not_prim x_not_mem_fv.1
        ext1 args
        congr 1
    | except pos e upds =>
      unfold Expression.replace eval

      unfold Expression.freeVars at x_not_mem_fv
      rw [List.not_mem_union_iff, List.mem_flatMap] at x_not_mem_fv
      push_neg at x_not_mem_fv

      congr 1
      · apply_rules [eval_subst_of_not_mem_fv]
        exact x_not_mem_fv.1
      · ext1
        simp_rw [List.attach_map, List.traverse_map, Function.comp_def]

        replace x_not_mem_fv := x_not_mem_fv.2

        conv_rhs => rw [← List.traverse_attach_eq_traverse']
        congr 2
        ext1 ⟨⟨_upd, _⟩, _⟩

        specialize x_not_mem_fv ⟨_, ‹_ ∈ upds›⟩ (List.mem_attach _ _)
        rw [List.not_mem_union_iff, List.mem_flatMap] at x_not_mem_fv
        push_neg at x_not_mem_fv

        congr 1
        · simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
          conv_rhs => rw [← List.traverse_attach_eq_traverse']

          congr 1
          ext1 ⟨⟨_, _⟩, _⟩
          dsimp
          symm
          split using _ | _es _ _ <;> (injections; subst_eqs)
          · rfl
          · symm
            simp_rw [List.attach_map, List.traverse_map, Function.comp_def]
            conv_rhs => rw [← List.traverse_attach_eq_traverse']
            congr 2
            ext1 ⟨⟨_e, _⟩, _⟩
            apply_rules [eval_subst_of_not_mem_fv]

            replace x_not_mem_fv := x_not_mem_fv.1
            specialize x_not_mem_fv ⟨_, ‹_ ∈ _upd.1›⟩ (List.mem_attach _ _)
            dsimp at x_not_mem_fv
            rw [List.mem_flatMap] at x_not_mem_fv
            push_neg at x_not_mem_fv

            exact x_not_mem_fv ⟨_, ‹_e ∈ _es›⟩ (List.mem_attach _ _)
        · ext1 _
          congr 1
          apply_rules [eval_subst_of_not_mem_fv]

          exact x_not_mem_fv.2
  termination_by e
  decreasing_by
    all_goals simp_wf; subst_vars; try decreasing_trivial
    · rename String × Typ × Expression Typ => f
      calc
        sizeOf e < sizeOf (n, _τ, e) := by simp +arith
        _ < sizeOf fields := by decreasing_trivial
        _ < _ := by simp +arith
    · subst_eqs
      apply Nat.le_of_lt
      conv_lhs => change sizeOf (α := List (Expression Typ)) ?_es
      calc
        sizeOf ?_es < sizeOf (Sum.inl (β := String) ?_es) := by decreasing_trivial
        _ < sizeOf _upd.1 := by decreasing_trivial
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by simp +arith
    · calc
        _ < sizeOf _upd := by let ⟨_, _⟩ := _upd; decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by simp +arith

  theorem neval_subst_of_mem_fv_of_neval.{u} {M : Memory.{u}} {x} {e e' : Expression.{u} Typ}
    (x_in_fv_e : x ∈ e.freeVars) (neval_e' : M ⊢ e' ↯) :
      M ⊢ e.replace x e' ↯ := by
    cases e with
    | var pos name =>
      unfold Expression.freeVars at x_in_fv_e
      cases propext List.mem_singleton ▸ x_in_fv_e
      unfold Expression.replace
      rwa [if_pos rfl]
    | str pos raw | nat pos raw | bool pos raw =>
      unfold Expression.freeVars at x_in_fv_e
      nomatch x_in_fv_e
    | «prefix» pos op e | access pos e x =>
      unfold Expression.freeVars at x_in_fv_e
      unfold Expression.replace eval
      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]
      intros v eval_e_subst
      apply neval_subst_of_mem_fv_of_neval x_in_fv_e at neval_e'
      rw [neval_e'] at eval_e_subst
      contradiction
    | «infix» pos e₁ op e₂ =>
      unfold Expression.freeVars at x_in_fv_e
      rw [List.mem_union_iff] at x_in_fv_e
      unfold Expression.replace eval
      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]
      intros v₁ eval_e₁_subst v₂ eval_e₂_subst
      obtain x_in_fv_e₁|x_in_fv_e₂ := x_in_fv_e
      · apply neval_subst_of_mem_fv_of_neval x_in_fv_e₁ at neval_e'
        rw [neval_e'] at eval_e₁_subst
        contradiction
      · apply neval_subst_of_mem_fv_of_neval x_in_fv_e₂ at neval_e'
        rw [neval_e'] at eval_e₂_subst
        contradiction
    | set pos es | seq pos es =>
      unfold Expression.freeVars at x_in_fv_e
      rw [List.mem_flatMap] at x_in_fv_e

      obtain ⟨⟨e, e_in⟩, -, x_in_fv_e⟩ := x_in_fv_e

      have IH : M ⊢ e.replace x e' ↯ :=
        neval_subst_of_mem_fv_of_neval x_in_fv_e neval_e'

      unfold Expression.replace eval
      rw [List.traverse_attach_eq_traverse, List.traverse_map, Function.comp_def]
      conv in List.traverse _ _ =>
        enter [1];
        change λ y ↦ match y with | ⟨e, _⟩ => eval M (e.replace x e')
      conv_lhs =>
        enter [2];
        apply List.traverse_attach_eq_traverse (f := λ e ↦ eval M (Expression.replace e x e'))

      erw [Option.map_eq_none_iff, List.traverse_eq_none]
      exists _, e_in
    | record pos fields =>
      unfold Expression.freeVars at x_in_fv_e
      rw [List.mem_flatMap] at x_in_fv_e

      obtain ⟨⟨a, a_in⟩, -, a_in_fv_e⟩ := x_in_fv_e

      apply neval_subst_of_mem_fv_of_neval a_in_fv_e at neval_e'

      unfold Expression.replace eval
      -- conv in List.traverse _ _ =>
      --   change List.traverse (λ x : Subtype _ ↦ match x with | ⟨x, _⟩ => (λ y ↦ (x.1, y)) <$> eval M x.2.2) _
      erw [Option.map_eq_none_iff, List.traverse_eq_none, ← List.mem_map,
           List.attach_map, List.map_map, Function.comp_def, List.mem_map]
      exists ⟨⟨a, ?_⟩, ?_⟩, ?_
      · exact List.mem_attach fields ⟨a, a_in⟩
      · exact List.mem_attach fields.attach ⟨_, _⟩
      · erwa [Option.map_eq_none_iff]
    | funcall pos fn args | opcall pos fn args =>
      unfold Expression.freeVars at x_in_fv_e
      rw [List.mem_union_iff, List.mem_flatMap] at x_in_fv_e

      unfold Expression.replace eval
      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff, List.traverse_attach_eq_traverse, List.traverse_map]
      conv in List.traverse _ _ =>
        enter [1];
        change λ y ↦ match y with | ⟨e, _⟩ => eval M (e.replace x e')
      conv =>
        enter [2, 1, 1];
        apply List.traverse_attach_eq_traverse (f := λ e ↦ eval M (Expression.replace e x e'))

      intros v₁ eval_args v₂ eval_fn_subst

      obtain x_in_fv_fn|⟨⟨a, a_in⟩, -, x_in_fv_e⟩ := x_in_fv_e
      · apply neval_subst_of_mem_fv_of_neval x_in_fv_fn at neval_e'
        rw [neval_e'] at eval_fn_subst
        contradiction
      · absurd eval_args
        clear eval_args

        rw [List.traverse_eq_some, List.forall₂_iff_zip]
        push_neg

        intro len_eq
        obtain ⟨b, b_in⟩ := List.exists_mem_zip_right_of_mem_left len_eq a_in
        use a, b, b_in
        · apply neval_subst_of_mem_fv_of_neval x_in_fv_e at neval_e'
          rw [neval_e']
          intro _
          contradiction
    | except pos e upds =>
      unfold Expression.freeVars at x_in_fv_e
      erw [List.mem_union_iff, List.mem_flatMap] at x_in_fv_e

      unfold Expression.replace eval
      simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff,
               List.traverse_eq_some]

      intros v₁ eval_e_subst vss eval_upds
      obtain x_in_fv_e|⟨⟨⟨ess, e⟩, arg_in⟩, -, x_in⟩ := x_in_fv_e
      · rw [neval_subst_of_mem_fv_of_neval x_in_fv_e neval_e'] at eval_e_subst
        contradiction
      · dsimp at x_in
        erw [List.mem_union_iff, List.mem_flatMap] at x_in

        obtain ⟨⟨val|val, _⟩, val_in, x_in_fv⟩|x_in_fv_e := x_in
          <;> try dsimp at x_in_fv
        · rw [List.mem_flatMap] at x_in_fv
          obtain ⟨⟨a, _⟩, _, x_in_fv_a⟩ := x_in_fv

          have IH := neval_subst_of_mem_fv_of_neval x_in_fv_a neval_e'

          let f : List (Expression Typ) ⊕ String → List (Expression Typ) ⊕ String :=
            λ x_1 ↦ match x_1 with
              | Sum.inl es => Sum.inl (List.map (λ e ↦ Expression.replace e x e') es)
              | Sum.inr x => Sum.inr x

          let g : List (Expression.{u} Typ) ⊕ String → Option (List Value ⊕ String) :=
            fun x_2 ↦ match x_2 with
              | Sum.inr x_3 => pure (Sum.inr x_3)
              | Sum.inl es => Sum.inl <$> List.traverse (fun ⟨x, _⟩ ↦ eval M x) es.attach

          have : f (.inl val) ∈ List.map f ess := by
            grind

          obtain ⟨y, y_in⟩ := by
            apply List.exists_mem_zip_right_of_mem_left eval_upds.length_eq
              (x := ⟨⟨List.map f ess, e.replace x e'⟩, ?_⟩)
              (List.mem_attach _ _)

            simp_rw [List.mem_map]
            exists ⟨(ess, e), arg_in⟩, List.mem_attach _ _
            congr 1
            rw [← List.forall₂_eq_eq_eq, List.forall₂_map_right_iff, List.forall₂_map_left_iff]

            dsimp

            unfold List.attach
            apply List.forall₂_of_attachWith'
            rintro (_|_) _ <;> simp [f]

          apply List.rel_of_forall₂_of_mem_zip y_in at eval_upds

          simp_rw [Option.bind_eq_some_iff, List.traverse_eq_some] at eval_upds
          obtain ⟨ys, eval_args, v', -, _|_⟩ := eval_upds

          obtain ⟨z, z_in⟩ := by
            apply List.exists_mem_zip_right_of_mem_left eval_args.length_eq
              (x := ⟨_, ‹f (.inl val) ∈ List.map f ess›⟩)
              (List.mem_attach _ _)

          apply List.rel_of_forall₂_of_mem_zip z_in at eval_args

          erw [Option.map_eq_some_iff] at eval_args
          simp_rw [List.traverse_eq_some] at eval_args
          obtain ⟨_, subst_args, rfl⟩ := eval_args

          obtain ⟨w, w_in⟩ := by
            apply List.exists_mem_zip_right_of_mem_left subst_args.length_eq
              (x := ⟨a.replace x e', ?_⟩)
              (List.mem_attach _ _)

            grind

          apply List.rel_of_forall₂_of_mem_zip w_in at subst_args
          erw [IH] at subst_args
          contradiction
        · contradiction
        · have IH := neval_subst_of_mem_fv_of_neval x_in_fv_e neval_e'

          rw [List.forall₂_iff_zip] at eval_upds
          simp_rw [Option.bind_eq_some_iff] at eval_upds

          obtain ⟨len_eq, eval_upds⟩ := eval_upds
          absurd @eval_upds
          clear eval_upds

          let f : List (Expression Typ) ⊕ String → List (Expression Typ) ⊕ String :=
            λ x_1 ↦ match x_1 with
              | Sum.inl es => Sum.inl (List.map (λ e ↦ Expression.replace e x e') es)
              | Sum.inr x => Sum.inr x

          push_neg
          simp_rw [List.attach_map]

          exists ⟨(List.map f ess, e.replace x e'), ?_⟩
          · simp_rw [List.mem_map]
            exists ⟨(ess, e), arg_in⟩, List.mem_attach _ _
            congr 1
            rw [← List.forall₂_eq_eq_eq, List.forall₂_map_right_iff, List.forall₂_map_left_iff]

            dsimp

            unfold List.attach
            apply List.forall₂_of_attachWith'
            rintro (_|_) _ <;> simp [f]
          · obtain ⟨b, b_in⟩ := List.exists_mem_zip_right_of_mem_left len_eq (x := ⟨(List.map f ess, e.replace x e'), ?_⟩) (List.mem_attach _ _)
            exists b, ?_
            · rw [List.attach_map] at b_in
              assumption
            · intros _ _ _ eval_e_subst
              erw [IH] at eval_e_subst
              contradiction
  termination_by e
  decreasing_by
    all_goals simp_wf; subst_vars; try decreasing_trivial
    · rename String × Typ × Expression Typ => f
      calc
        sizeOf f.2.2 < sizeOf f := let ⟨_, _, _⟩ := f; by simp +arith
        _ < sizeOf fields := by decreasing_trivial
        _ < _ := by simp +arith
    · apply Nat.le_of_lt
      conv_lhs => change sizeOf (α := List (Expression Typ)) ?_es
      calc
        sizeOf ?_es < sizeOf (Sum.inl (β := String) ?_es) := by decreasing_trivial
        _ < sizeOf ess := by decreasing_trivial
        _ < sizeOf (ess, e) := by decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by simp +arith
    · calc
        _ < sizeOf (ess, e) := by decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by simp +arith

  theorem eval_subst_iff.{u} {M : Memory.{u}} {e e' : Expression.{u} Typ} {v} {x} (h : x ∉ prims) :
      M ⊢ e.replace x e' ⇒ v ↔ if x ∈ e.freeVars then ∃ v', M ⊢ e' ⇒ v' ∧ M.insert x v' ⊢ e ⇒ v else M ⊢ e ⇒ v := by
    iff_intro h' h'
    · split_ifs with h''
      · by_cases h''' : ∃ v', M ⊢ e' ⇒ v'
        · obtain ⟨v', eval_e'⟩ := h'''
          exists v', ‹_›
          rwa [← eval_subst h eval_e']
        · push_neg at h'''
          rw [← Option.eq_none_iff_forall_ne_some] at h'''
          apply neval_subst_of_mem_fv_of_neval h'' at h'''
          rw [h'] at h'''
          contradiction
      · rwa [eval_subst_of_not_mem_fv h h''] at h'
    · split_ifs at h' with h''
      · obtain ⟨v', eval_e', h'⟩ := h'
        rwa [eval_subst h eval_e']
      · rwa [eval_subst_of_not_mem_fv h h'']

  theorem eval_det {M : Memory} {e v v'} (h₁ : M ⊢ e ⇒ v) (h₂ : M ⊢ e ⇒ v') : v = v' := by
    simp_all

  theorem eval_or_neval.{u} {M : Memory.{u}} {e : Expression.{u} Typ} :
      M ⊢ e ↯ ∨ (∃ v, M ⊢ e ⇒ v) :=
    Option.eq_none_or_eq_some _

  theorem eval_plus_spec.{u} {M : Memory.{u}} {pos} {e₁ e₂ : Expression.{u} Typ} {v} (h : M ⊢ .infix pos e₁ .«+» e₂ ⇒ v) :
      ∃ n₁ n₂, M ⊢ e₁ ⇒ .int n₁ ∧ M ⊢ e₂ ⇒ .int n₂ ∧ v = .int (n₁ + n₂) := by
    unfold eval at h
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v₁, eval_e₁, v₂, eval_e₂, h⟩ := h
    split at h using n₁ n₂ <;> try contradiction
    cases h
    exists n₁, n₂

  theorem eval_plus_intro.{u} {M : Memory.{u}} {pos} {e₁ e₂} {n₁ n₂} (h₁ : M ⊢ e₁ ⇒ .int n₁) (h₂ : M ⊢ e₂ ⇒ .int n₂) : M ⊢ .infix pos e₁ .«+» e₂ ⇒ .int (n₁ + n₂) := by
    unfold eval
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]
    exists _, h₁, _, h₂

  theorem eval_plus_iff.{u} {M : Memory.{u}} {pos} {e₁ e₂ : Expression.{u} Typ} {v} : M ⊢ .infix pos e₁ .«+» e₂ ⇒ v ↔ ∃ n₁ n₂, M ⊢ e₁ ⇒ .int n₁ ∧ M ⊢ e₂ ⇒ .int n₂ ∧ v = .int (n₁ + n₂) := by
    constructor
    · exact eval_plus_spec
    · rintro ⟨n₁, n₂, h₁, h₂, rfl⟩
      apply eval_plus_intro <;> assumption

  theorem eval_gt_spec.{u} {M : Memory.{u}} {pos} {e₁ e₂} {v} (h : M ⊢ .infix pos e₁ .«>» e₂ ⇒ v) :
      ∃ n₁ n₂, M ⊢ e₁ ⇒ .int n₁ ∧ M ⊢ e₂ ⇒ .int n₂ ∧ v = .bool (decide (n₁ > n₂)) := by
    unfold eval at h
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v₁, eval_e₁, v₂, eval_e₂, h⟩ := h
    split at h using n₁ n₂ <;> try contradiction
    cases h
    exists n₁, n₂

  theorem neval_gt_spec.{u} {M : Memory.{u}} {pos} {e₁ e₂} (h : M ⊢ .infix pos e₁ .«>» e₂ ↯) :
      (∀ v, M ⊢ e₁ ⇒ v → ∀ n, v ≠ .int n) ∨ (∀ v, M ⊢ e₂ ⇒ v → ∀ n, v ≠ .int n) := by
    unfold eval at h
    simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff] at h

    by_contra! h
    obtain ⟨⟨v₁, eval_e₁, n₁, rfl⟩, ⟨v₂, eval_e₂, n₂, rfl⟩⟩ := h
    cases h _ eval_e₁ _ eval_e₂

  theorem eval_gt_intro.{u} {M : Memory.{u}} {pos} {e₁ e₂} {n₁ n₂} (h₁ : M ⊢ e₁ ⇒ .int n₁) (h₂ : M ⊢ e₂ ⇒ .int n₂) : M ⊢ .infix pos e₁ .«>» e₂ ⇒ .bool (decide (n₁ > n₂)) := by
    unfold eval
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]
    exists _, h₁, _, h₂

  theorem neval_gt_intro.{u} {M : Memory.{u}} {pos} {e₁ e₂}
    (h : ∀ v₁ v₂, M ⊢ e₁ ⇒ v₁ → M ⊢ e₂ ⇒ v₂ → ((∀ n₁, v₁ ≠ .int n₁) ∨ (∀ n₂, v₂ ≠ .int n₂))) :
      M ⊢ .infix pos e₁ .«>» e₂ ↯ := by
    unfold eval
    simp_rw [Option.bind_eq_bind, Option.bind_eq_none_iff]
    intros v₁ eval_e₁ v₂ eval_e₂
    split using n₁ n₂ <;> try contradiction
    · obtain h|h := h _ _ eval_e₁ eval_e₂ <;> nomatch h _ rfl
    · rfl

  theorem eval_gt_iff.{u} {M : Memory.{u}} {pos} {e₁ e₂} {v} : M ⊢ .infix pos e₁ .«>» e₂ ⇒ v ↔ ∃ n₁ n₂, M ⊢ e₁ ⇒ .int n₁ ∧ M ⊢ e₂ ⇒ .int n₂ ∧ v = .bool (decide (n₁ > n₂)) := by
    constructor
    · exact eval_gt_spec
    · rintro ⟨n₁, n₂, h₁, h₂, rfl⟩
      apply eval_gt_intro <;> assumption

  theorem eval_nat_spec.{u} {M : Memory.{u}} {pos} {x} {v} (h : M ⊢ .nat pos x ⇒ v) : v = .int x.toInt! := by
    unfold eval at h
    cases h
    rfl

  theorem eval_nat_intro.{u} {M : Memory.{u}} {pos} {x} {n} (h : x.toInt! = n) : M ⊢ .nat pos x ⇒ .int n := by
    unfold eval
    rw [h]
    rfl

  theorem eval_nat_iff.{u} {M : Memory.{u}} {pos} {x} {v} : M ⊢ .nat pos x ⇒ v ↔ v = .int x.toInt! := by
    constructor
    · exact eval_nat_spec
    · rintro rfl
      apply eval_nat_intro
      rfl

  theorem eval_plus_0_eq {pos₁} {M} {e₁ e₂} {n} (h₁ : M ⊢ e₁ ⇒ .int n) (h₂ : M ⊢ e₂ ⇒ .int 0) : eval M (.infix pos₁ e₁ .«+» e₂) = eval M e₁ := by
    conv_lhs => unfold eval
    ext v
    erw [Option.bind_eq_some_iff]
    constructor
    · rw [h₁, h₂]
      rintro ⟨_, _|_, h⟩
      erw [Option.bind_eq_some_iff] at h
      obtain ⟨_, _|_, h⟩ := h
      rw [← h]
      dsimp
      erw [Int.add_zero]
    · rw [h₁, h₂]
      rintro (_|_)
      exists .int n, rfl
      erw [Option.bind_eq_some_iff]
      exists .int 0, rfl
      dsimp
      erw [Int.add_zero]

  theorem eval_plus_gt_eq_gt_minus {pos₁ pos₂} {M} {e₁ e₂ e₃} : eval M (.infix pos₁ (.infix pos₂ e₁ .«+» e₂) .«>» e₃) = eval M (.infix pos₁ e₁ .«>» (.infix pos₂ e₃ .«-» e₂)) := by
    unfold eval
    ext v
    repeat erw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨v', eval_plus_eq_v', h⟩
      erw [Option.bind_eq_some_iff] at h
      obtain ⟨v₃, eval_e₃_eq_v₃, h⟩ := h
      dsimp at h
      split at h using n' n₃ <;> try contradiction
      obtain _|_ := h
      unfold eval at eval_plus_eq_v'
      erw [Option.bind_eq_some_iff] at eval_plus_eq_v'
      obtain ⟨v₁, eval_e₁_eq_v₁, h⟩ := eval_plus_eq_v'
      erw [Option.bind_eq_some_iff] at h
      obtain ⟨v₂, eval_e₂_eq_v₂, h⟩ := h
      dsimp at h
      split at h using n₁ n₂ <;> try contradiction
      obtain _|_ := h
      exists _, eval_e₁_eq_v₁
      erw [Option.bind_eq_some_iff]
      exists .int (n₃ - n₂)
      and_intros
      · unfold eval
        erw [Option.bind_eq_some_iff]
        exists _, eval_e₃_eq_v₃
        erw [Option.bind_eq_some_iff]
        exists _, eval_e₂_eq_v₂
      · dsimp
        congr 3
        simp +arith
    · rintro ⟨v₁, eval_e₁_eq_v₁, h⟩
      erw [Option.bind_eq_some_iff] at h
      obtain ⟨v', eval_minus_eq_v', h⟩ := h
      dsimp at h
      split at h using n₁ n' <;> try contradiction
      unfold eval at eval_minus_eq_v'
      erw [Option.bind_eq_some_iff] at eval_minus_eq_v'
      obtain ⟨v₃, eval_e₃_eq_v₃, h⟩ := eval_minus_eq_v'
      erw [Option.bind_eq_some_iff] at h
      obtain ⟨v₂, eval_e₂_eq_v₂, h⟩ := h
      dsimp at h
      split at h using n₃ n₂ <;> try contradiction
      obtain _|_ := h
      obtain _|_ := h
      exists .int (n₁ + n₂)
      and_intros
      · unfold eval
        erw [Option.bind_eq_some_iff]
        exists _, eval_e₁_eq_v₁
        erw [Option.bind_eq_some_iff]
        exists _, eval_e₂_eq_v₂
      · erw [Option.bind_eq_some_iff]
        exists _, eval_e₃_eq_v₃
        dsimp
        congr 3
        simp +arith

  theorem eval_nat_minus {M} {pos₁ pos₂ pos₃ pos₄} {n₁ n₂ : ℕ} (h : n₁ ≥ n₂) :
      eval M (.infix pos₁ (.nat pos₂ (toString n₁)) .«-» (.nat pos₃ (toString n₂))) = eval M (.nat pos₄ (toString (n₁ - n₂))) := by
    unfold eval eval
    repeat erw [Nat.repr_toInt!]
    grind

  theorem eval_nat_plus {M} {pos₁ pos₂ pos₃ pos₄} {n₁ n₂ : ℕ} :
      eval M (.infix pos₁ (.nat pos₂ (toString n₁)) .«+» (.nat pos₃ (toString n₂))) = eval M (.nat pos₄ (toString (n₁ + n₂))) := by
    unfold eval eval
    repeat erw [Nat.repr_toInt!]
    grind

  theorem eval_infix_congr {M} {pos e₁ e₁' op e₂ e₂'} (h₁ : eval M e₁ = eval M e₁') (h₂ : eval M e₂ = eval M e₂') :
      eval M (.infix pos e₁ op e₂) = eval M (.infix pos e₁' op e₂') := by
    unfold eval
    ext v
    repeat erw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨v₁, eval_e₁_eq_v₁, h⟩
      erw [Option.bind_eq_some_iff] at h
      obtain ⟨v₂, eval_e₂_eq_v₂, h⟩ := h
      split at h <;> {
        split at h using n₁ n₂ <;> first
          | contradiction
          | obtain _|_ := h
            rw [h₁] at eval_e₁_eq_v₁
            rw [h₂] at eval_e₂_eq_v₂
            exists _, eval_e₁_eq_v₁
            erw [Option.bind_eq_some_iff]
            exists _, eval_e₂_eq_v₂
      }
    · rintro ⟨v₁', eval_e₁'_eq_v₁', h⟩
      erw [Option.bind_eq_some_iff] at h
      obtain ⟨v₂', eval_e₂'_eq_v₂', h⟩ := h
      split at h <;> {
        split at h using n₁ n₂ <;> first
          | contradiction
          | obtain _|_ := h
            rw [← h₁] at eval_e₁'_eq_v₁'
            rw [← h₂] at eval_e₂'_eq_v₂'
            exists _, eval_e₁'_eq_v₁'
            erw [Option.bind_eq_some_iff]
            exists _, eval_e₂'_eq_v₂'
      }

  theorem eval_plus_nat_plus {M} {pos₁ pos₂ pos₃ pos₄ pos₅} {e₁} {n₁ n₂ : ℕ} :
      eval M (.infix pos₁ e₁ .«+» (.infix pos₂ (.nat pos₃ (toString n₁)) .«+» (.nat pos₄ (toString n₂)))) =
        eval M (.infix pos₁ e₁ .«+» (.nat pos₅ (toString (n₁ + n₂)))) := by
    apply eval_infix_congr
    · rfl
    · exact eval_nat_plus

  theorem eval_plus_assoc {M} {e₁ e₂ e₃} {pos₁ pos₂} :
      eval M (.infix pos₁ (.infix pos₂ e₁ .«+» e₂) .«+» e₃) = eval M (.infix pos₁ e₁ .«+» (.infix pos₂ e₂ .«+» e₃)) := by
    conv_lhs =>
      unfold eval
      pattern (occs := 1) eval M _
      unfold eval
    conv_rhs =>
      unfold eval
      pattern (occs := 2) eval M _
      unfold eval
    ext v
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨v', ⟨v₁, eval_e₁, v₂, eval_e₂, shape_v₁_v₂⟩, v₃, eval_e₃, shape_v'_v₃⟩
      split at shape_v₁_v₂ using n₁ n₂
      · cases shape_v₁_v₂
        split at shape_v'_v₃ using n₃ h
        · cases shape_v'_v₃
          cases h
          exists .int n₁, ?_, .int (n₂ + n₃), ⟨.int n₂, ?_, .int n₃, ?_, ?_⟩ <;> try trivial
          rw [Int.add_assoc]
          rfl
        · contradiction
      · contradiction
    · rintro ⟨v₁, eval_e₁, v', ⟨v₂, eval_e₂, v₃, eval_e₃, shape_v₂_v₃⟩, shape_v₁_v'⟩
      split at shape_v₁_v' using n₁ _
      · cases shape_v₁_v'
        split at shape_v₂_v₃ using n₂ n₃
        · cases shape_v₂_v₃
          exists .int (n₁ + n₂), ⟨.int n₁, ?_, .int n₂, ?_, rfl⟩, .int n₃, ?_ <;> try trivial
          rw [← Int.add_assoc]
          rfl
        · contradiction
      · contradiction

  theorem eval_Head_to_is_nonempty_seq {M : Memory} {pos} {e} {es} {v} (h₁ : M ⊢ e ⇒ .prim "Head") (h₂ : M ⊢ .opcall pos e es ⇒ v) :
      ∃ (h₃ : es.length = 1), ∃ vs, M ⊢ es[0] ⇒ .seq vs ∧ ∃ vs', vs = v :: vs' := by
    unfold eval at h₂
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h₂
    obtain ⟨_, eval_es, _, eval_e, h₂⟩ := h₂
    rw [eval_det eval_e h₁] at h₂
    change AList.lookup "Head" prims >>= _ = some v at h₂
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h₂
    obtain ⟨f, lookup_Head_eq, Head_eq⟩ := h₂
    rw [prims_Head] at lookup_Head_eq
    cases lookup_Head_eq
    obtain ⟨_, _, rfl, rfl⟩ := Head_spec Head_eq
    rw [List.traverse_eq_some, List.forall₂_singleton_right_iff] at eval_es
    obtain ⟨e, eval_e, es_eq⟩ := eval_es
    apply List.attach_eq_cons at es_eq
    obtain ⟨_, _, rfl, e_eq, nil_eq⟩ := es_eq
    obtain rfl := propext List.attach_eq_nil_iff ▸ List.eq_nil_of_map_eq_nil nil_eq.symm
    rw [← e_eq] at eval_e
    refine ⟨List.length_singleton, _, eval_e, _, rfl⟩

  theorem neval_Head {M : Memory} {pos} {e} {es} (h₁ : M ⊢ e ⇒ .prim "Head") (h₂ : M ⊢ .opcall pos e es ↯) :
      es.length ≠ 1 ∨ (∃ e ∈ es, ∀ v', M ⊢ e ⇒ v' → ∀ v vs, v' ≠ .seq (v :: vs)) := by
    by_contra! h

    obtain ⟨es_singleton, arg_is_seq⟩ := h
    rw [List.length_eq_one_iff] at es_singleton
    obtain ⟨e', rfl⟩ := es_singleton

    specialize arg_is_seq _ List.mem_cons_self
    obtain ⟨v', eval_e', v'', vs'', rfl⟩ := arg_is_seq

    unfold eval at h₂
    simp_rw [List.traverse_attach_eq_traverse', List.traverse_singleton, eval_e', h₁,
             Option.bind_eq_bind, Option.bind_eq_none_iff, Option.map_eq_map, Option.map_eq_some_iff] at h₂
    specialize h₂ [.seq (v'' :: vs'')] ⟨.seq (v'' :: vs''), rfl, rfl⟩ (.prim "Head") rfl
    split at h₂ using h₃ | h₃
    · cases h₃
      erw [prims_Head] at h₂
      change (some Head).bind (λ x ↦ x [.seq (v'' :: vs'')]) = none at h₂
      rw [Option.bind_eq_none_iff] at h₂
      nomatch h₂ _ rfl
    · exact h₃ _ rfl

  theorem eval_Head.{u} {M : Memory.{u}} {pos} : M ⊢ .var pos "Head" ⇒ .prim "Head" := by
    unfold eval
    rfl

  theorem eval_Tail_is_seq {M : Memory} {pos} {e} {es} {v} (h₁ : M ⊢ e ⇒ .prim "Tail") (h₂ : M ⊢ .opcall pos e es ⇒ v) :
      ∃ (h₃ : es.length = 1), ∃ v' vs, M ⊢ es[0] ⇒ .seq (v' :: vs) ∧ v = .seq vs := by
    unfold eval at h₂
    erw [Option.bind_eq_some_iff] at h₂
    obtain ⟨vs, h₃, h₂⟩ := h₂
    erw [Option.bind_eq_some_iff] at h₂
    obtain ⟨_, h₁', h₂⟩ := h₂
    rw [eval_det h₁' h₁] at h₂
    dsimp [Bind.bindLeft] at h₂
    rw [Option.bind_eq_some_iff] at h₂
    obtain ⟨f, h₂, f_vs_eq⟩ := h₂
    rw [prims_Tail] at h₂
    injection h₂; subst f
    obtain ⟨v', vs', rfl, rfl⟩ := Tail_spec f_vs_eq
    conv at h₃ =>
      simp [List.traverse_attach_eq_traverse, List.traverse_eq_some, List.forall₂_cons_right_iff, List.forall₂_nil_right_iff]
    obtain ⟨v, _, rfl⟩ := h₃
    refine ⟨?_, v', vs', ‹_›, rfl⟩
    simp

  theorem neval_Tail {M : Memory} {pos} {e} {es} (h₁ : M ⊢ e ⇒ .prim "Tail") (h₂ : M ⊢ .opcall pos e es ↯) :
      es.length ≠ 1 ∨ (∃ e ∈ es, ∀ v', M ⊢ e ⇒ v' → ∀ v vs, v' ≠ .seq (v :: vs)) := by
    by_contra! h

    obtain ⟨es_singleton, arg_is_seq⟩ := h
    rw [List.length_eq_one_iff] at es_singleton
    obtain ⟨e', rfl⟩ := es_singleton

    specialize arg_is_seq _ List.mem_cons_self
    obtain ⟨v', eval_e', v'', vs'', rfl⟩ := arg_is_seq

    unfold eval at h₂
    simp_rw [List.traverse_attach_eq_traverse', List.traverse_singleton, eval_e', h₁,
             Option.bind_eq_bind, Option.bind_eq_none_iff, Option.map_eq_map, Option.map_eq_some_iff] at h₂
    specialize h₂ [.seq (v'' :: vs'')] ⟨.seq (v'' :: vs''), rfl, rfl⟩ (.prim "Tail") rfl
    split at h₂ using h₃ | h₃
    · cases h₃
      erw [prims_Tail] at h₂
      change (some Tail).bind (λ x ↦ x [.seq (v'' :: vs'')]) = none at h₂
      rw [Option.bind_eq_none_iff] at h₂
      nomatch h₂ _ rfl
    · exact h₃ _ rfl

  theorem eval_Tail.{u} {M : Memory.{u}} {pos} : M ⊢ .var pos "Tail" ⇒ .prim "Tail" := by
    unfold eval
    rfl

  theorem eval_Tail_intro {M : Memory} {pos} {e} {es} {vs} (v) (h₁ : es.length = 1) (h₂ : M ⊢ e ⇒ .prim "Tail") (h₃ : M ⊢ es[0] ⇒ .seq (v :: vs)) :
      M ⊢ .opcall pos e es ⇒ .seq vs := by
    unfold eval
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨[.seq (v :: vs)], ?_, .prim "Tail", ‹_›, ?_⟩
    · rw [List.length_eq_one_iff] at h₁
      obtain ⟨e', rfl⟩ := h₁
      simp_all [List.traverse_cons', List.traverse_nil']
    · simp_rw [prims_Tail, Bind.bindLeft, Option.bind_eq_bind, Option.bind_eq_some_iff]
      exists Tail

  theorem eval_Len_is_int {M : Memory} {pos} {e} {es} {v} (h₁ : M ⊢ e ⇒ .prim "Len") (h₂ : M ⊢ .opcall pos e es ⇒ v) :
      ∃ (h₃ : es.length = 1), ∃ vs, M ⊢ es[0] ⇒ .seq vs ∧ v = .int vs.length := by
    unfold eval at h₂
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h₂
    obtain ⟨vs, vs_eq, v, v_eq, h₂⟩ := h₂
    rw [eval_det v_eq h₁] at h₂
    change AList.lookup "Len" prims >>= _ = some _ at h₂
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff] at h₂
    obtain ⟨_, lookup_Len, app_Len_eq⟩ := h₂
    rw [prims_Len] at lookup_Len
    cases lookup_Len
    apply Len_spec at app_Len_eq
    obtain ⟨_, rfl, rfl⟩ := app_Len_eq
    rw [List.traverse_eq_some, List.forall₂_singleton_right_iff] at vs_eq
    obtain ⟨e, eval_e, es_eq⟩ := vs_eq
    apply List.attach_eq_cons at es_eq
    obtain ⟨_, _, rfl, e_eq, nil_eq⟩ := es_eq
    obtain rfl := propext List.attach_eq_nil_iff ▸ List.eq_nil_of_map_eq_nil nil_eq.symm
    rw [← e_eq] at eval_e
    refine ⟨List.length_singleton, _, eval_e, rfl⟩

  theorem eval_Len_intro {M : Memory} {pos} {e} {es} {vs} {n} (h₁ : es.length = 1) (h₂ : M ⊢ e ⇒ .prim "Len") (h₃ : M ⊢ es[0] ⇒ .seq vs) (h₄ : n = vs.length) :
      M ⊢ .opcall pos e es ⇒ .int n := by
    unfold eval
    simp_rw [Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨[.seq vs], ?_, .prim "Len", ‹_›, ?_⟩
    · rw [List.length_eq_one_iff] at h₁
      obtain ⟨e', rfl⟩ := h₁
      simp_all [List.traverse_cons', List.traverse_nil']
    · simp_rw [prims_Len, Bind.bindLeft, Option.bind_eq_bind, Option.bind_eq_some_iff]
      exists Len, rfl
      unfold Len
      rw [dite_cond_eq_true (eq_true List.length_singleton), h₄]
      rfl

  theorem eval_Len.{u} {M : Memory.{u}} {pos} : M ⊢ .var pos "Len" ⇒ .prim "Len" := by
    unfold eval
    rfl

  theorem eval_var_pos_irrel.{u} {M : Memory.{u}} {pos₁ pos₂} {x} : eval M (.var pos₁ x) = eval M (.var pos₂ x) := by
    unfold eval
    rfl

  theorem eval_var.{u} {M : Memory.{u}} {pos} {x} : eval M (.var pos x) = if h : x ∈ prims.{u} then primFromName x h else M.lookup x := by
    unfold eval
    rfl


  instance {M e v} : Decidable (M ⊢ e ⇒ v) := Option.instDecidableEq.decEq (eval M e) (some v)
  instance {M e} : Decidable (M ⊢ e ↯) := Option.instDecidableEq.decEq (eval M e) none
