module

public import Guarded2Network.Lemmas.Relation
public import Guarded2Network.Lemmas.Trace

@[expose] public section

/-!
  Statement-level refinement: what `Guarded2Network` does to a single action statement, and the two
  transfer lemmas every later proof leans on.

  **Evaluation transfer (plan D1).** The pass introduces exactly one name, `inbox`, and it is fresh
  (`freshName`'s `$` separator makes collision with a source name impossible). So any source
  expression evaluates the same in the target's memory, which differs only at `inbox`. Prior art
  re-derives that fact inline at least eight times, as a five-line `rw`/`apply eval_ext`/
  `List.singleton_disjoint` sandwich. Here it is `relatesTo.eval_iff`, once.

  **Reference arguments (plan D2).** A reference's index path is evaluated by a `List.Forall₂` over
  `EvalStep`, and pushing the transfer under it is what drove prior art's repeated
  `List.forall₂_iff_forall₂_attach`/`attach` gymnastics. Naming that relation — `Ref.EvalArgs` —
  and giving it its own congruence lemma removes the nesting from view entirely.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep)
open GuardedPlusCal (ChanKey EvalStep LocalState')

variable {V : Type} [ExprSemantics V]

/-! ## D1 — evaluation transfer -/

/-- Binding a name the expression cannot read leaves its value alone. The one-name case of
`ExprSemantics.evalLocal`, which is the only case the pass ever needs: it introduces `inbox` and
nothing else. -/
theorem eval_insert_of_fresh {M : Memory V} {x : String} {v' v : V}
    {e : ComputablePlusCal.Expression} (fresh : Expression.FreshIn x e) :
    ((M.insert x v') ⊢ e ⇒ v) ↔ (M ⊢ e ⇒ v) := by
  apply ExprSemantics.evalLocal
  intro y hy
  apply AList.lookup_insert_ne
  rintro rfl
  exact fresh hy

/-- Related states evaluate a source expression to the same values, provided the expression does
not mention `inbox` — which no source expression does, `inbox` being freshly generated. -/
theorem relatesTo.eval_iff {c : ComputableGuardedPlusCal.Ref} {inbox : String}
    {σₛ σₜ : LocalState' V} (h : σₛ ∼[.some (c, inbox)] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} (fresh : Expression.FreshIn inbox e) :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  apply ExprSemantics.evalLocal
  intro y hy
  apply h.mem_agree
  rintro rfl
  exact fresh hy

/-- The same for a process that receives nothing: there the memories are equal outright and the
freshness hypothesis has nothing to say. -/
theorem relatesTo.eval_iff_none {σₛ σₜ : LocalState' V} (h : σₛ ∼[.none] σₜ)
    {e : ComputablePlusCal.Expression} {v : V} :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  rw [h.mem_eq]

/-- Both cases at once, with the freshness hypothesis stated so that it is vacuous when there is no
mailbox — the form a lemma quantified over an arbitrary `mbox` needs. -/
theorem relatesTo.eval_iff' {mbox : Mailbox} {σₛ σₜ : LocalState' V} (h : σₛ ∼[mbox] σₜ)
    {e : ComputablePlusCal.Expression} {v : V}
    (fresh : ∀ c inbox, mbox = .some (c, inbox) → Expression.FreshIn inbox e) :
    ((σₛ.mem ⊢ e ⇒ v)) ↔ ((σₜ.mem ⊢ e ⇒ v)) := by
  match mbox with
  | .none => exact h.eval_iff_none
  | .some (c, inbox) => exact h.eval_iff (fresh c inbox rfl)

/-! ## D2 — reference arguments -/

/-- A reference's index path, evaluated. Named, rather than left as the raw `List.Forall₂` it
unfolds to, so that transferring it between memories is one lemma about `EvalArgs` instead of a
`Forall₂`-induction at every use site. -/
def Ref.EvalArgs (M : Memory V) (r : ComputableGuardedPlusCal.Ref) (path : List (PathStep V)) :
    Prop :=
  List.Forall₂ (EvalStep M) r.args path

/-- A path resolves to at most one value — `EvalStep.path_inj`, at the named relation. -/
theorem Ref.EvalArgs.inj {M : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {path path' : List (PathStep V)} (h : Ref.EvalArgs M r path) (h' : Ref.EvalArgs M r path') :
    path = path' :=
  EvalStep.path_inj h h'

/-- Every index expression of a reference reads only names the reference itself reads. The bridge
from a freshness fact about a `Ref` to one about each of its index expressions, which is what
`congr_of_fresh` needs per `Forall₂` step. -/
theorem Ref.freeVars_of_mem_args {r : ComputableGuardedPlusCal.Ref}
    {e : ComputablePlusCal.Expression} (hmem : Sum.inr e ∈ r.args) {x : String}
    (hx : x ∈ e.freeVars) : x ∈ GuardedPlusCal.Ref.freeVars r := by
  -- once `x` is in the accumulator it stays there, `∪` being monotone in its left argument
  have keep : ∀ (l : List (Finset String)) (acc : Finset String), x ∈ acc →
      x ∈ l.foldl (· ∪ ·) acc := by
    intro l
    induction l with
    | nil => intro _ h; exact h
    | cons hd tl ih => intro acc h; exact ih _ (Finset.mem_union_left _ h)
  have enters : ∀ (l : List (String ⊕ ComputablePlusCal.Expression)) (acc : Finset String),
      Sum.inr e ∈ l → x ∈ (l.map λ seg ↦ match seg with
        | .inl _ => (∅ : Finset String) | .inr e' => e'.freeVars).foldl (· ∪ ·) acc := by
    intro l
    induction l with
    | nil => intro _ hmem; cases hmem
    | cons hd tl ih =>
      intro acc hmem
      rw [List.map_cons, List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact keep _ _ (Finset.mem_union_right _ hx)
      · exact ih _ hmem'
  exact Finset.mem_union_right _ (enters r.args ∅ hmem)

/-- Memories agreeing away from `inbox` resolve a reference's path identically, provided the
reference does not read `inbox`. This is D2's point: the `List.Forall₂` nesting is discharged once,
here, and no later proof sees it. -/
theorem Ref.EvalArgs.congr_of_fresh {M₁ M₂ : Memory V} {r : ComputableGuardedPlusCal.Ref}
    {inbox : String} {path : List (PathStep V)}
    (agree : ∀ x ≠ inbox, M₁.lookup x = M₂.lookup x)
    (fresh : inbox ∉ GuardedPlusCal.Ref.freeVars r) :
    Ref.EvalArgs M₁ r path ↔ Ref.EvalArgs M₂ r path := by
  unfold Ref.EvalArgs
  have step : ∀ (args : List (String ⊕ ComputablePlusCal.Expression))
      (path : List (PathStep V)),
      (∀ e, Sum.inr e ∈ args → Expression.FreshIn inbox e) →
      (List.Forall₂ (EvalStep M₁) args path ↔ List.Forall₂ (EvalStep M₂) args path) := by
    intro args
    induction args with
    | nil =>
      intro path _
      rw [List.forall₂_nil_left_iff, List.forall₂_nil_left_iff]
    | cons hd tl ih =>
      intro path hfresh
      -- the head segment's own agreement, needed in both directions
      have hhead : ∀ (e : ComputablePlusCal.Expression), hd = Sum.inr e →
          ∀ y ∈ e.freeVars, M₁.lookup y = M₂.lookup y := by
        rintro e rfl y hy
        apply agree y
        rintro rfl
        exact hfresh _ (List.mem_cons_self ..) hy
      have htail : ∀ e, Sum.inr e ∈ tl → Expression.FreshIn inbox e :=
        λ e he ↦ hfresh e (List.mem_cons_of_mem _ he)
      constructor
      · intro h
        cases h with
        | cons hstep hrest =>
          refine List.Forall₂.cons ?_ ((ih _ htail).mp hrest)
          cases hstep with
          | field f => exact EvalStep.field f
          | index hv =>
            apply EvalStep.index
            exact (ExprSemantics.evalLocal (hhead _ rfl)).mp hv
      · intro h
        cases h with
        | cons hstep hrest =>
          refine List.Forall₂.cons ?_ ((ih _ htail).mpr hrest)
          cases hstep with
          | field f => exact EvalStep.field f
          | index hv =>
            apply EvalStep.index
            exact (ExprSemantics.evalLocal (hhead _ rfl)).mpr hv
  exact step r.args path (λ e he hx ↦ fresh (Ref.freeVars_of_mem_args he hx))

/-! ## Transferring a memory update

  `assign` (and, on the source side, `receive`) writes through `Memory.update`. Simulating that step
  means running the same update in the other memory and finding the results still related — which
  holds because the two memories agree at the written name, so they read the same old value, compute
  the same new one, and insert it.
-/

/-- An update that succeeds in one memory succeeds in any memory agreeing with it away from `inbox`,
provided the written name is not `inbox` itself, and the results still agree away from `inbox`. -/
theorem Memory.update_transfer {M₁ M₂ M₁' : Memory V} {inbox x : String}
    {path : List (PathStep V)} {v : V}
    (agree : ∀ y ≠ inbox, M₁.lookup y = M₂.lookup y) (hx : x ≠ inbox)
    (h₁ : ComputableTLAPlus.Memory.update M₁ x path v = .some M₁') :
    ∃ M₂', ComputableTLAPlus.Memory.update M₂ x path v = .some M₂' ∧
      ∀ y ≠ inbox, M₁'.lookup y = M₂'.lookup y := by
  unfold ComputableTLAPlus.Memory.update at h₁ ⊢
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h₁ ⊢
  obtain ⟨old, hold, new, hnew, h₁⟩ := h₁
  obtain rfl := Option.some.inj h₁
  refine ⟨M₂.insert x new, ⟨old, ?_, new, hnew, rfl⟩, ?_⟩
  · rw [← agree x hx]
    exact hold
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    rw [AList.lookup_insert, AList.lookup_insert]
  · rw [AList.lookup_insert_ne hyx, AList.lookup_insert_ne hyx]
    exact agree y hy

/-! ## D4 — action statements

  `convertActionStmt` maps each of the seven action constructors to its namesake in the target
  language, and the two `Statement.reducing` definitions agree character-for-character on those
  cases (the only differences in the whole `def` are the type name, one comment, and Guarded's extra
  `receive` case). So the semantics is not merely preserved but *definitionally equal*, and the
  seven-lemma port prior art writes collapses to one `cases … <;> rfl` per semantic component.
-/

theorem convertActionStmt_reducing' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.reducing' (V := V) (convertActionStmt S) =
      GuardedPlusCal.Statement.reducing' (V := V) S := by
  cases S <;> rfl

theorem convertActionStmt_aborting' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.aborting' (V := V) (convertActionStmt S) =
      GuardedPlusCal.Statement.aborting' (V := V) S := by
  cases S <;> rfl

theorem convertActionStmt_diverging' {b : Bool} (S : ComputableGuardedPlusCal.Statement false b) :
    NetworkPlusCal.Statement.diverging' (V := V) (convertActionStmt S) =
      GuardedPlusCal.Statement.diverging' (V := V) S := by
  cases S <;> rfl

end Guarded2Network

end
