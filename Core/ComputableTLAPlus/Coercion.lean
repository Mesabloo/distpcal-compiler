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
    .opCall (.var (.operator [.str] (.seq .int)) (.intrinsic "StrToSeq") @@ pos) [e] @@ pos
  | .seqToFun τ₀ i =>
    let range : CExpr :=
      .opCall (.var (.operator [.int, .int] (.set .int)) (.module "Naturals" "..") @@ pos)
        [.nat (toString (1 : Nat)) @@ pos,
         .opCall (.var (.operator [.seq τ₀] .int) (.module "Sequences" "Len") @@ pos) [e] @@ pos] @@ pos
    .fn i .int τ₀ range
      (.fnCall (ComputableTLAPlus.Expression.liftBound 1 e) (.seq τ₀) (.var .int (.bound 0) @@ pos) @@ pos) @@ pos
  | .tupleToSeq n τ _ =>
    .seq ((List.range n).map λ i ↦
      .fnCall e (.tuple (List.replicate n τ)) (.nat (toString (i + 1)) @@ pos) @@ pos) τ @@ pos
  | .set x τ τ' c =>
    .map' (c.applyComputable (.var τ (.bound 0) @@ pos)) x τ τ' e @@ pos
  | .tuple coes τs τs' =>
    (.tuple <| (List.range coes.length).attach.map λ ⟨i, hi⟩ ↦
      (τs'[i]!, (coes[i]'(List.mem_range.mp hi)).applyComputable
        (.fnCall e (.tuple τs) (.nat (toString (i + 1)) @@ pos) @@ pos))) @@ pos
  | .record fields =>
    (.record <| fields.attach.map λ ⟨⟨name, c, τ'ᵢ⟩, _hf⟩ ↦
      (τ'ᵢ, name, c.applyComputable (.recordAccess e name @@ pos))) @@ pos
  | .function x y dom rng dom' rng' cDom cRng =>
    let eLift : CExpr := ComputableTLAPlus.Expression.liftBound 1 e
    let domainExpr : CExpr :=
      .opCall (.var (.operator [.function dom rng] (.set dom)) (.intrinsic "DOMAIN") @@ pos) [e] @@ pos
    let newDomain : CExpr :=
      .map' (cDom.applyComputable (.var dom (.bound 0) @@ pos)) x dom dom' domainExpr @@ pos
    let eqTy : Typ := .operator [dom', dom'] .bool
    let domainExprLift : CExpr :=
      .opCall (.var (.operator [.function dom rng] (.set dom)) (.intrinsic "DOMAIN") @@ pos) [eLift] @@ pos
    let recoveredArg : CExpr :=
      .choose x dom domainExprLift
        (.opCall (.var eqTy (.intrinsic "=") @@ pos)
          [cDom.applyComputable (.var dom (.bound 0) @@ pos), .var dom' (.bound 1) @@ pos] @@ pos) @@ pos
    .fn y dom' rng' newDomain
      (cRng.applyComputable (.fnCall eLift (.function dom rng) recoveredArg @@ pos)) @@ pos
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

`freeVars_applyComputable_subset` — a coercion adds no free variable — lives here rather than next
to the semantics: it needs `Coercion.applyComputable`'s induction principle, generated only in this
module. The small `mem_freeVars_*` unfoldings it uses are re-exported for the semantics to reuse.

TODO(locally-nameless): re-derive `freeVars_applyComputable_subset` against the de Bruijn
`applyComputable`/`liftBound`; parked with the semantics port. -/

variable {z : String}

@[simp] theorem freeVars_var_free {n : String} {τ : Typ} :
    (Expression.var τ (.free n)).freeVars = {n} := by simp only [Expression.freeVars]

@[simp] theorem freeVars_var_bound {i : Nat} {τ : Typ} :
    (Expression.var τ (.bound i)).freeVars = ∅ := by simp only [Expression.freeVars]

@[simp] theorem freeVars_var_intrinsic {n : String} {τ : Typ} :
    (Expression.var τ (.intrinsic n)).freeVars = ∅ := by simp only [Expression.freeVars]

@[simp] theorem freeVars_var_module {m n : String} {τ : Typ} :
    (Expression.var τ (.module m n)).freeVars = ∅ := by simp only [Expression.freeVars]

@[simp] theorem freeVars_nat {s : String} : (Expression.nat s : Expression Typ).freeVars = ∅ := by
  simp only [Expression.freeVars]

@[simp] theorem freeVars_str {s : String} : (Expression.str s : Expression Typ).freeVars = ∅ := by
  simp only [Expression.freeVars]

theorem mem_freeVars_fn {y : String} {a co : Typ} {dom body : Expression Typ} :
    z ∈ (Expression.fn y a co dom body).freeVars ↔ z ∈ dom.freeVars ∨ z ∈ body.freeVars := by
  rw [Expression.freeVars, Finset.mem_union]

theorem mem_freeVars_map' {y : String} {a co : Typ} {dom body : Expression Typ} :
    z ∈ (Expression.map' body y a co dom).freeVars ↔ z ∈ dom.freeVars ∨ z ∈ body.freeVars := by
  rw [Expression.freeVars, Finset.mem_union]

theorem mem_freeVars_choose {y : String} {a : Typ} {dom body : Expression Typ} :
    z ∈ (Expression.choose y a dom body).freeVars ↔ z ∈ dom.freeVars ∨ z ∈ body.freeVars := by
  rw [Expression.freeVars, Finset.mem_union]

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

/-- A coercion adds no free variable: every binder `applyComputable` introduces refers to itself
by a `.bound` index, `liftBound` never touches a `.free` name, and every splice of `e` sits under
an operator (`Len`/`DOMAIN`/`.fnCall`/`.recordAccess`) that carries `e`'s free variables through
unchanged. `ExprSemantics.evalCoerce` needs this to shrink a `Coercion.FreshFor` hypothesis onto a
sub-expression (`.comp`, `.function`). -/
theorem freeVars_applyComputable_subset {c : TypedTLAPlus.Coercion} {e : Expression Typ}
    (hz : z ∈ (TypedTLAPlus.Coercion.applyComputable c e).freeVars) : z ∈ e.freeVars := by
  -- TODO(locally-nameless): re-derive against the de Bruijn `applyComputable`; the `mem_freeVars_*`
  -- lemmas above are already updated. Parked with the semantics port (item 6).
  sorry

/-- The `⊆` reading of `freeVars_applyComputable_subset`. -/
theorem freeVars_applyComputable_subset' {c : TypedTLAPlus.Coercion} {e : Expression Typ} :
    (TypedTLAPlus.Coercion.applyComputable c e).freeVars ⊆ e.freeVars :=
  fun _ hz ↦ freeVars_applyComputable_subset hz

end ComputableTLAPlus

end
