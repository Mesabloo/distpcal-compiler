module

meta import CustomPrelude
public import Core.TypedTLAPlus.Coercion
public import Core.ComputableTLAPlus.Syntax
public import Core.ComputableTLAPlus.FreeVars

public section


/-!
  `Coercion.applyComputable` is the second of `Core/TypedTLAPlus/Coercion.lean`'s two structural
  recursions over `TypedTLAPlus.Coercion`, discharging against `ComputableTLAPlus.Expression`
  instead of `TypedTLAPlus.Expression`. Needed because a `receive`'s channel/reference coercion is
  stored unapplied and survives past `Typed2Computable`'s type change: `Guarded2Network` is the
  first pass with a concrete `ComputableTLAPlus.Expression` (the built `Head(inbox)`/`Tail(inbox)`
  expression) to discharge it against, so it can't reuse `Coercion.apply` (fixed at
  `TypedTLAPlus.Expr`).

  Mirrors `Coercion.apply` case-for-case, except `choose`'s domain here is a required `Expression
  α` rather than `Option (Expression α)` — see `Core/ComputableTLAPlus/Syntax.lean`'s module doc.
-/

namespace TypedTLAPlus

/-- Checked TLA⁺ expressions at `ComputableTLAPlus`'s output type — what `Coercion.applyComputable`
transforms. -/
abbrev CExpr := ComputableTLAPlus.Expression ComputableTLAPlus.Typ

/-- Applies a coercion to an already-built `ComputableTLAPlus.Expression` — see the module doc
above for why this can't reuse `Coercion.apply`. Registers every synthesized node at the coerced
expression's own span, for the reason spelled out on `Coercion.apply`. -/
@[expose] def Coercion.applyComputable (c : Coercion) (e : CExpr) : CExpr :=
  let pos := posOf e
  match c with
  | .id => e
  | .strToSeq =>
    .opCall (.var "StrToSeq" (.operator [.str] (.seq .int)) .intrinsic @@ pos) [e] @@ pos
  | .seqToFun τ₀ i =>
    let range : CExpr :=
      .opCall (.var ".." (.operator [.int, .int] (.set .int)) (.module "Naturals") @@ pos)
        [.nat (toString (1 : Nat)) @@ pos,
         .opCall (.var "Len" (.operator [.seq τ₀] .int) (.module "Sequences") @@ pos) [e] @@ pos] @@ pos
    .fn i .int τ₀ range (.fnCall e (.seq τ₀) (.var i .int .binder @@ pos) @@ pos) @@ pos
  | .tupleToSeq n τ _ =>
    .seq ((List.range n).map λ i ↦
      .fnCall e (.tuple (List.replicate n τ)) (.nat (toString (i + 1)) @@ pos) @@ pos) τ @@ pos
  | .set x τ τ' c =>
    .map' (c.applyComputable (.var x τ .binder @@ pos)) x τ τ' e @@ pos
  | .tuple coes τs τs' =>
    (.tuple <| (List.range coes.length).attach.map λ ⟨i, hi⟩ ↦
      (τs'[i]!, (coes[i]'(List.mem_range.mp hi)).applyComputable
        (.fnCall e (.tuple τs) (.nat (toString (i + 1)) @@ pos) @@ pos))) @@ pos
  | .record fields =>
    (.record <| fields.attach.map λ ⟨⟨name, c, τ'ᵢ⟩, _hf⟩ ↦
      (τ'ᵢ, name, c.applyComputable (.recordAccess e name @@ pos))) @@ pos
  | .function x y dom rng dom' rng' cDom cRng =>
    let domainExpr : CExpr :=
      .opCall (.var "DOMAIN" (.operator [.function dom rng] (.set dom)) .intrinsic @@ pos) [e] @@ pos
    let newDomain : CExpr :=
      .map' (cDom.applyComputable (.var x dom .binder @@ pos)) x dom dom' domainExpr @@ pos
    let eqTy : Typ := .operator [dom', dom'] .bool
    let recoveredArg : CExpr :=
      .choose x dom domainExpr
        (.opCall (.var "=" eqTy .intrinsic @@ pos)
          [cDom.applyComputable (.var x dom .binder @@ pos), .var y dom' .binder @@ pos] @@ pos) @@ pos
    .fn y dom' rng' newDomain (cRng.applyComputable (.fnCall e (.function dom rng) recoveredArg @@ pos)) @@ pos
  | .comp c₁ c₂ => c₂.applyComputable (c₁.applyComputable e)
  termination_by sizeOf c
  decreasing_by
    all: simp_wf
    all:
      first
        | omega
        | (have := List.sizeOf_lt_of_mem (List.getElem_mem (List.mem_range.mp ‹_›)); omega)
        | (have h1 := List.sizeOf_lt_of_mem ‹(_, _, _) ∈ _›
           simp only [Prod.mk.sizeOf_spec] at h1
           omega)

end TypedTLAPlus

namespace ComputableTLAPlus

/-! ## `Coercion.applyComputable` and free variables

`freeVars_applyComputable_subset` — a coercion adds no free variable — has to live here rather than
next to the semantics: `fun_induction Coercion.applyComputable` needs that function's induction
principle, which the module system only generates in the module the function is defined in. The
small `mem_freeVars_*` unfoldings it uses are re-exported for the semantics to reuse. -/

variable {z : String}

@[simp] theorem freeVars_var_binder {x : String} {τ : Typ} :
    (Expression.var x τ .binder).freeVars = {x} := by simp only [Expression.freeVars]

@[simp] theorem freeVars_var_intrinsic {x : String} {τ : Typ} :
    (Expression.var x τ .intrinsic).freeVars = ∅ := by simp only [Expression.freeVars]

@[simp] theorem freeVars_var_module {x m : String} {τ : Typ} :
    (Expression.var x τ (.module m)).freeVars = ∅ := by simp only [Expression.freeVars]

@[simp] theorem freeVars_nat {s : String} : (Expression.nat s : Expression Typ).freeVars = ∅ := by
  simp only [Expression.freeVars]

@[simp] theorem freeVars_str {s : String} : (Expression.str s : Expression Typ).freeVars = ∅ := by
  simp only [Expression.freeVars]

theorem mem_freeVars_fn {y : String} {a co : Typ} {dom body : Expression Typ} :
    z ∈ (Expression.fn y a co dom body).freeVars ↔
      z ∈ dom.freeVars ∨ (z ≠ y ∧ z ∈ body.freeVars) := by
  rw [Expression.freeVars, Finset.mem_union, Finset.mem_erase]

theorem mem_freeVars_map' {y : String} {a co : Typ} {dom body : Expression Typ} :
    z ∈ (Expression.map' body y a co dom).freeVars ↔
      z ∈ dom.freeVars ∨ (z ≠ y ∧ z ∈ body.freeVars) := by
  rw [Expression.freeVars, Finset.mem_union, Finset.mem_erase]

theorem mem_freeVars_choose {y : String} {a : Typ} {dom body : Expression Typ} :
    z ∈ (Expression.choose y a dom body).freeVars ↔
      z ∈ dom.freeVars ∨ (z ≠ y ∧ z ∈ body.freeVars) := by
  rw [Expression.freeVars, Finset.mem_union, Finset.mem_erase]

theorem mem_freeVars_fnCall {f e' : Expression Typ} {a : Typ} :
    z ∈ (Expression.fnCall f a e').freeVars ↔ z ∈ f.freeVars ∨ z ∈ e'.freeVars := by
  rw [Expression.freeVars, Finset.mem_union]

/-- A `.fnCall` at a `.nat` index reads only its head. -/
theorem freeVars_fnCall_nat {e : Expression Typ} {τ : Typ} {s : String} :
    (Expression.fnCall e τ (.nat s)).freeVars = e.freeVars := by
  rw [Expression.freeVars]; simp

/-- Field access reads only its subject. -/
theorem freeVars_recordAccess {e : Expression Typ} {n : String} :
    (Expression.recordAccess e n).freeVars = e.freeVars := by simp only [Expression.freeVars]

/-- A coercion adds no free variable: every binder `applyComputable` introduces wraps its own use,
and every splice of `e` sits under an operator (`Len`/`DOMAIN`/`.fnCall`/`.recordAccess`) that
carries `e`'s free variables through unchanged. `ExprSemantics.evalCoerce` needs this to shrink a
`Coercion.FreshFor` hypothesis onto a sub-expression (`.comp`, `.function`). -/
theorem freeVars_applyComputable_subset {c : TypedTLAPlus.Coercion} {e : Expression Typ}
    (hz : z ∈ (TypedTLAPlus.Coercion.applyComputable c e).freeVars) : z ∈ e.freeVars := by
  fun_induction TypedTLAPlus.Coercion.applyComputable c e with
  | case1 => simpa only [TypedTLAPlus.Coercion.applyComputable] using hz
  | case2 =>
      simp only [Expression.mem_freeVars_opCall, freeVars_var_intrinsic, Finset.notMem_empty, false_or,
        List.mem_singleton, exists_eq_left] at hz
      exact hz
  | case3 _ _ _ _ range =>
      -- `fun_induction` keeps the `.seqToFun` arm's `let range` as a case-local definition; `unfold`
      -- it back into the body before the `mem_freeVars_*` rewrites can reach the `1 .. Len(e)` spine.
      unfold range at hz
      simp only [registerSource, mem_freeVars_fn, Expression.mem_freeVars_opCall,
        freeVars_var_module, Finset.notMem_empty, false_or, List.mem_cons, List.not_mem_nil,
        or_false, mem_freeVars_fnCall, freeVars_var_binder, Finset.mem_singleton, ne_eq] at hz
      rcases hz with ⟨e2, (rfl | rfl), hz2⟩ | ⟨hne, h | rfl⟩
      · simp only [freeVars_nat, Finset.notMem_empty] at hz2
      · simpa only [Expression.mem_freeVars_opCall, freeVars_var_module, Finset.notMem_empty,
          false_or, List.mem_singleton, exists_eq_left] using hz2
      · exact h
      · contradiction
  | case4 =>
      simp only [Expression.mem_freeVars_seq, List.mem_map, List.mem_range] at hz
      obtain ⟨_, ⟨a, -, rfl⟩, hz⟩ := hz
      rw [mem_freeVars_fnCall] at hz
      rcases hz with h | h
      · exact h
      · simp only [freeVars_nat, Finset.notMem_empty] at h
  | case5 _ _ x _ _ _ ih =>
      simp only [mem_freeVars_map'] at hz
      rcases hz with h | ⟨hne, h⟩
      · exact h
      · have hzx : z = x := by
          simpa only [registerSource, freeVars_var_binder, Finset.mem_singleton] using ih h
        contradiction
  | case6 _ _ _ _ _ ih =>
      simp only [Expression.mem_freeVars_tuple, List.mem_map, List.mem_attach, true_and,
        Subtype.exists, List.mem_range] at hz
      obtain ⟨e2, ⟨a, ha, rfl⟩, hz2⟩ := hz
      have := ih a (List.mem_range.mpr ha) hz2
      rw [mem_freeVars_fnCall] at this
      rcases this with h | h
      · exact h
      · simp only [registerSource, freeVars_nat, Finset.notMem_empty] at h
  | case7 _ _ _ ih =>
      simp only [Expression.mem_freeVars_record, List.mem_map, List.mem_attach, true_and,
        Subtype.exists] at hz
      obtain ⟨f2, ⟨a, ha, rfl⟩, hz2⟩ := hz
      have := ih a.1 a.2.1 a.2.2 ha hz2
      rwa [freeVars_recordAccess] at this
  | case8 _ _ x _ _ _ _ _ _ _ domainExpr newDomain _eqTy recoveredArg ih_nd _ih_ra ih_r =>
      -- same `let`-lifting as `case3`, for `.function`'s `domainExpr`/`newDomain`/`recoveredArg`.
      unfold newDomain domainExpr at hz
      simp only [registerSource, mem_freeVars_fn, mem_freeVars_map',
        Expression.mem_freeVars_opCall, freeVars_var_intrinsic, Finset.notMem_empty, false_or,
        List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, ne_eq] at hz
      rcases hz with (h | ⟨hnx, h⟩) | ⟨hny, h⟩
      · exact h
      · have hzx : z = x := by
          simpa only [registerSource, freeVars_var_binder, Finset.mem_singleton] using ih_nd h
        contradiction
      · have hr := ih_r h
        rw [mem_freeVars_fnCall] at hr
        rcases hr with hr | hr
        · exact hr
        · unfold recoveredArg domainExpr at hr
          simp only [registerSource, mem_freeVars_choose, Expression.mem_freeVars_opCall,
            freeVars_var_intrinsic, Finset.notMem_empty, false_or, List.mem_cons,
            List.not_mem_nil, or_false, exists_eq_left, or_and_right, exists_or,
            freeVars_var_binder, Finset.mem_singleton, ne_eq] at hr
          rcases hr with hr | ⟨hnx2, hr | rfl⟩
          · exact hr
          · have hzx : z = x := by
              simpa only [registerSource, freeVars_var_binder, Finset.mem_singleton] using ih_nd hr
            contradiction
          · contradiction
  | case9 _ _ _ ih1 ih2 => exact ih1 (ih2 hz)

/-- The `⊆` reading of `freeVars_applyComputable_subset`. -/
theorem freeVars_applyComputable_subset' {c : TypedTLAPlus.Coercion} {e : Expression Typ} :
    (TypedTLAPlus.Coercion.applyComputable c e).freeVars ⊆ e.freeVars :=
  fun _ hz ↦ freeVars_applyComputable_subset hz

end ComputableTLAPlus

end
