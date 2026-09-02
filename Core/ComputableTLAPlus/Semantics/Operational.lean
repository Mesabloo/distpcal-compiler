module

meta import CustomPrelude
import Std.Data.String.ToNat
import Mathlib.Data.Set.Finite.Basic
public import Core.ComputableTLAPlus.Semantics.Interface
public import Core.ComputableTLAPlus.Semantics.Value
public import Core.ComputableTLAPlus.FreeVars
public import Core.ComputableTLAPlus.Coercion
public import Core.TypedTLAPlus.Builtins

@[expose] public section

/-!
  The concrete `ExprSemantics Value` instance: TLA⁺ expression evaluation as an inductive relation
  `Eval Ξ Ω M e v`, on the `Value := ZFSet` domain.

  Evaluation is a relation, not a function, because a user-defined operator call re-descends into
  that operator's body — an unrelated syntax tree with no measure a termination checker sees — and
  because "no derivation" is exactly the meaning of "aborts". A genuinely non-terminating
  expression (were `RECURSIVE` ever to return) simply has no finite derivation tree.

  Builtin operators are strict in their argument *kinds*: `e₁ /\ e₂` denotes a boolean only when
  both operands denote booleans, `e₁ + e₂` an integer only when both denote integers, and so on.
  A kind mismatch leaves the call with no value — the type checker is what rules such calls out in
  practice, so this partiality is never exercised on a well-typed program.

  Name resolution follows a `.var` node's `Origin` (see `ExprSemantics.evalVar`): `.binder` reads
  memory, `.module m` consults the operator environment `Ξ` then the model `Ω`, `.intrinsic`
  denotes nothing on its own and only means something as an `opCall` head.
-/

namespace ComputableTLAPlus
namespace Operational

open TypedTLAPlus (BuiltinOp Coercion)

/-! ## Value-level predicates and operations -/

/-- The value is one of the two booleans. -/
def IsBool (v : Value) : Prop := v = Value.tru ∨ v = Value.fls

/-- The value is an integer encoding. -/
def IsInt (v : Value) : Prop := ∃ z : ℤ, v = Value.ofInt z

/-- The value denotes a set, as opposed to a scalar. Under the untagged encoding every value is a
`ZFSet`, so this excludes only the scalar kinds by hand; a non-set `with x ∈ e` aborting is what it
is for. -/
def IsSet (v : Value) : Prop := ¬ IsBool v ∧ ¬ IsInt v

/-- `s` is exactly the canonical sequence value whose elements, in order, are `vs`. -/
def IsSeq (s : Value) (vs : List Value) : Prop := s = Value.ofSeq vs

/-- Function application on a value: the unique `w` paired with `k`, or a junk value when `f` is not
a function or `k` is outside its domain. `Classical.epsilon`, so it is total and deterministic; the
out-of-domain case is imprecise rather than aborting, which the type checker covers. -/
noncomputable def fnApply (f k : Value) : Value :=
  Classical.epsilon (λ w ↦ ZFSet.pair k w ∈ f)

/-- `f` with the key `k` rebound to `w`: drop the pair already at `k`, add `(k, w)`. -/
noncomputable def fnUpdate (f k w : Value) : Value :=
  insert (ZFSet.pair k w) (f \ {ZFSet.pair k (fnApply f k)})

/-- `updatePath old path v` — `old` with the position named by `path` overwritten by `v`, `none`
when a `.inr` index does not resolve. `path = []` overwrites outright. -/
noncomputable def updatePath : Value → List (PathStep Value) → Value → Option Value
  | _, [], v => some v
  | old, .inl fld :: rest, v =>
    (updatePath (fnApply old (Value.ofString fld)) rest v).map (fnUpdate old (Value.ofString fld))
  | old, .inr k :: rest, v =>
    (updatePath (fnApply old k) rest v).map (fnUpdate old k)

/-- Append to a sequence value: succeeds exactly when `s` is a sequence, extending its element
list on the right. -/
noncomputable def seqAppend (s v : Value) : Option Value := by
  classical exact if h : ∃ vs, s = Value.ofSeq vs then some (Value.ofSeq (h.choose ++ [v])) else none

/-! ## Builtin operator evaluation -/

/-- `EvalBuiltin op args v` — the builtin `op`, applied to already-evaluated arguments `args`,
denotes `v`. Strict in argument kinds: an arm exists only for the shapes the operator is defined
on. Covers the operators reachable from a computable algorithm. The `Bags` family,
`Cardinality`/`IsFiniteSet`, and `\prec` have no arm — a call to one of them denotes nothing. -/
-- TODO: I left a few notes for some constructor. To me, it feels like you are not making use of anything that `ZFLean`
-- gives us, although we don't necessarily need much here.
inductive EvalBuiltin : BuiltinOp → List Value → Value → Prop
  -- equality
  | eq_pos {a : Value} : EvalBuiltin .eq [a, a] Value.tru
  | eq_neg {a b : Value} (h : a ≠ b) : EvalBuiltin .eq [a, b] Value.fls
  | neq_pos {a b : Value} (h : a ≠ b) : EvalBuiltin .neq [a, b] Value.tru
  | neq_neg {a : Value} : EvalBuiltin .neq [a, a] Value.fls
  -- propositional
  | and_tt : EvalBuiltin .and [Value.tru, Value.tru] Value.tru
  | and_ff {a b : Value} (ha : IsBool a) (hb : IsBool b) (h : a = Value.fls ∨ b = Value.fls) :
      EvalBuiltin .and [a, b] Value.fls
  | or_tt {a b : Value} (ha : IsBool a) (hb : IsBool b) (h : a = Value.tru ∨ b = Value.tru) :
      EvalBuiltin .or [a, b] Value.tru
  | or_ff : EvalBuiltin .or [Value.fls, Value.fls] Value.fls
  | implies_t {a b : Value} (ha : IsBool a) (hb : IsBool b) (h : a = Value.fls ∨ b = Value.tru) :
      EvalBuiltin .implies [a, b] Value.tru
  | implies_f : EvalBuiltin .implies [Value.tru, Value.fls] Value.fls
  | iff_t {a : Value} (ha : IsBool a) : EvalBuiltin .iff [a, a] Value.tru
  | iff_f {a b : Value} (ha : IsBool a) (hb : IsBool b) (h : a ≠ b) :
      EvalBuiltin .iff [a, b] Value.fls
  | neg_t : EvalBuiltin .neg [Value.tru] Value.fls
  | neg_f : EvalBuiltin .neg [Value.fls] Value.tru
  -- set membership and relations
  | inSet_pos {a S : Value} (h : a ∈ S) : EvalBuiltin .inSet [a, S] Value.tru
  | inSet_neg {a S : Value} (h : a ∉ S) : EvalBuiltin .inSet [a, S] Value.fls
  | notInSet_pos {a S : Value} (h : a ∉ S) : EvalBuiltin .notInSet [a, S] Value.tru
  | notInSet_neg {a S : Value} (h : a ∈ S) : EvalBuiltin .notInSet [a, S] Value.fls
  | subseteq_pos {A B : Value} (h : A ⊆ B) : EvalBuiltin .subseteq [A, B] Value.tru
  | subseteq_neg {A B : Value} (h : ¬ A ⊆ B) : EvalBuiltin .subseteq [A, B] Value.fls
  -- set constructors
  | cup {A B : Value} : EvalBuiltin .cup [A, B] (A ∪ B)
  | cap {A B : Value} : EvalBuiltin .cap [A, B] (A ∩ B)
  | setMinus {A B : Value} : EvalBuiltin .setMinus [A, B] (A \ B)
  | cartesianProduct {A B v : Value}
      (hv : ∀ z, z ∈ v ↔ ∃ a ∈ A, ∃ b ∈ B, z = Value.ofSeq [a, b]) :
      -- TODO: why `ofSeq` and not `ofTuple`? This would be less obscure.
      EvalBuiltin .cartesianProduct [A, B] v
  | domain {f v : Value} (hv : ∀ z, z ∈ v ↔ ∃ w, ZFSet.pair z w ∈ f) :
      -- TODO: why not state `hv` as `∀ z, z ∈ v ↔ z ∈ f.Dom`, other than the fact that it requires an additional `f.IsPFunc` hypothesis which is
      -- perfectly reasonable?
      -- Another way would be to directly specialize `v := f.Dom` rather than using `hv`.
      EvalBuiltin .domain [f] v
  -- integer arithmetic
  | plus {x y : ℤ} : EvalBuiltin .plus [Value.ofInt x, Value.ofInt y] (Value.ofInt (x + y))
  | minus {x y : ℤ} : EvalBuiltin .minus [Value.ofInt x, Value.ofInt y] (Value.ofInt (x - y))
  | unaryMinus {x : ℤ} : EvalBuiltin .unaryMinus [Value.ofInt x] (Value.ofInt (-x))
  | times {x y : ℤ} : EvalBuiltin .times [Value.ofInt x, Value.ofInt y] (Value.ofInt (x * y))
  | intDiv {x y : ℤ} : EvalBuiltin .intDiv [Value.ofInt x, Value.ofInt y] (Value.ofInt (x.fdiv y))
  | mod {x y : ℤ} : EvalBuiltin .mod [Value.ofInt x, Value.ofInt y] (Value.ofInt (x.fmod y))
  | pow {x y : ℤ} : EvalBuiltin .pow [Value.ofInt x, Value.ofInt y] (Value.ofInt (x ^ y.toNat))
  | lt_pos {x y : ℤ} (h : x < y) : EvalBuiltin .lt [Value.ofInt x, Value.ofInt y] Value.tru
  | lt_neg {x y : ℤ} (h : ¬ x < y) : EvalBuiltin .lt [Value.ofInt x, Value.ofInt y] Value.fls
  | gt_pos {x y : ℤ} (h : y < x) : EvalBuiltin .gt [Value.ofInt x, Value.ofInt y] Value.tru
  | gt_neg {x y : ℤ} (h : ¬ y < x) : EvalBuiltin .gt [Value.ofInt x, Value.ofInt y] Value.fls
  | leq_pos {x y : ℤ} (h : x ≤ y) : EvalBuiltin .leq [Value.ofInt x, Value.ofInt y] Value.tru
  | leq_neg {x y : ℤ} (h : ¬ x ≤ y) : EvalBuiltin .leq [Value.ofInt x, Value.ofInt y] Value.fls
  | geq_pos {x y : ℤ} (h : y ≤ x) : EvalBuiltin .geq [Value.ofInt x, Value.ofInt y] Value.tru
  | geq_neg {x y : ℤ} (h : ¬ y ≤ x) : EvalBuiltin .geq [Value.ofInt x, Value.ofInt y] Value.fls
  | range {a b : ℤ} {v : Value}
      (hv : ∀ z, z ∈ v ↔ ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ z = Value.ofInt k) :
      -- TODO: Same comment as for `domain`
      EvalBuiltin .range [Value.ofInt a, Value.ofInt b] v
  -- `Naturals`'s `Nat` and `Integers`'s `Int` are not here: they are never *called* (`Nat()` is not
  -- a term), only referenced by bare name, so they are `Eval` rules on the `.var` node directly
  -- (`Eval.natSet`/`Eval.intSet`), not builtin operators.
  -- sequences
  | len {vs : List Value} : EvalBuiltin .len [Value.ofSeq vs] (Value.ofNat vs.length)
  | head {v : Value} {vs : List Value} : EvalBuiltin .head [Value.ofSeq (v :: vs)] v
  | tail {v : Value} {vs : List Value} :
      EvalBuiltin .tail [Value.ofSeq (v :: vs)] (Value.ofSeq vs)
  | append {vs : List Value} {x : Value} :
      EvalBuiltin .append [Value.ofSeq vs, x] (Value.ofSeq (vs ++ [x]))
  -- strings are already their code-point sequence, so `StrToSeq` is the identity
  | strToSeq {v : Value} : EvalBuiltin .strToSeq [v] v

/-! ## Expression evaluation -/

/-- Substitute a call's actual arguments for its operator's formal parameters. The parameters form a
de Bruijn binder over `body` in declaration order (`Op(a, b)` ⇒ `a` is `.bound 1`, `b` is
`.bound 0`, `Elaborator/Context.lean`), so the arguments are instantiated innermost-first. `params`
is carried only for the arity check at the call rule; capture is impossible — `.bound` and `.free`
are disjoint. -/
def substParams (_params : List (String × Nat)) (args : List (Expression Typ))
    (body : Expression Typ) : Expression Typ :=
  body.instantiate args.reverse

/-- A name free in a fully-applied `substParams` is either free in `body` or free in one of the
arguments substituted in. `evalLocal'`/`evalSubst'` need this for their `opCall_op` case, since the
derivation there recurses into this substituted body rather than a subterm of the call. -/
theorem substParams_freeVars {params : List (String × Nat)} {args : List (Expression Typ)}
    {body : Expression Typ} {z : String} (_hlen : params.length = args.length)
    (hz : z ∈ (substParams params args body).freeVars) :
    z ∈ body.freeVars ∨ ∃ a ∈ args, z ∈ a.freeVars := by
  rcases Expression.freeVars_instantiate hz with h | ⟨a, ha, hza⟩
  · exact .inl h
  · exact .inr ⟨a, List.mem_reverse.mp ha, hza⟩

/-- `subst` pushes through `substParams` when the substituend is locally closed and the operator
body is closed (`Ξ.WellScoped`): it lands on the arguments only. The `opCall_op` step of
`evalSubst'`, whose sub-derivation is on `substParams params args body`, not a call subterm. -/
theorem subst_substParams {x : String} {e' : Expression Typ} (hlc : e'.LC)
    {params : List (String × Nat)} {args : List (Expression Typ)} {body : Expression Typ}
    (hbody : x ∉ body.freeVars) :
    Expression.subst x e' (substParams params args body)
      = substParams params (args.map (Expression.subst x e')) body := by
  rw [substParams, substParams, Expression.subst_instantiate hlc hbody, List.map_reverse]

/-- A builtin call's head origin (`.module`/`.intrinsic`) is untouched by `subst`. -/
theorem subst_var_of_builtin {x : String} {e' : Expression Typ} {τ : Typ} {o : Origin}
    {op : BuiltinOp} (hop : TypedTLAPlus.builtinOpOf? o = some op) :
    Expression.subst x e' (Expression.var τ o) = Expression.var τ o := by
  cases o with
  | free n => simp [TypedTLAPlus.builtinOpOf?] at hop
  | bound i => simp [TypedTLAPlus.builtinOpOf?] at hop
  | «module» m n => exact Expression.subst_var_module
  | intrinsic n => exact Expression.subst_var_intrinsic

mutual
/-- `Eval Ξ Ω M e v` — under operator environment `Ξ`, model `Ω`, and memory `M`, expression `e`
denotes `v`. Mutually defined with `EvalList` (a list of expressions against a list of values) and
`EvalPath` (a reference's syntactic access path against its resolved one); a nested `List.Forall₂`
or `ResolvesPath` cannot carry `Eval` through the kernel's positivity check, so both are inlined as
mutual companions. Every recursive premise mentions `Eval` directly — never wrapped in `And`/
`Exists`/`Iff`, which the kernel rejects when the other arguments carry local variables. -/
inductive Eval (Ξ : OperatorEnv) (Ω : Model Value) : Memory Value → Expression Typ → Value → Prop
  -- literals
  | nat {M : Memory Value} {s : String} {n : ℕ} (hn : s.toNat? = some n) :
      Eval Ξ Ω M (.nat s) (Value.ofNat n)
  | str {M : Memory Value} {s : String} : Eval Ξ Ω M (.str s) (Value.ofString s)
  | tru {M : Memory Value} : Eval Ξ Ω M .true Value.tru
  | fls {M : Memory Value} : Eval Ξ Ω M .false Value.fls
  -- variables, by origin. A `.bound` node never appears here: `Eval` only ever meets a binder body
  -- after `openVar` has replaced its own `.bound 0` with the binder's name hint.
  | var_free {M : Memory Value} {τ : Typ} {name : String} {v : Value} (h : M.lookup name = some v) :
      Eval Ξ Ω M (.var τ (.free name)) v
  | var_op0 {M : Memory Value} {τ : Typ} {m name : String} {body : Expression Typ}
      {v : Value} (hΞ : Ξ m name = some ([], body))
      (hnb : TypedTLAPlus.builtinOpOf? (.module m name) = none) (hb : Eval Ξ Ω M body v) :
      Eval Ξ Ω M (.var τ (.module m name)) v
  | var_const {M : Memory Value} {τ : Typ} {m name : String} {v : Value}
      (hΞ : Ξ m name = none)
      (hnb : TypedTLAPlus.builtinOpOf? (.module m name) = none) (hΩ : Ω m name = some v) :
      Eval Ξ Ω M (.var τ (.module m name)) v
  -- `Nat` / `Int`: bare references to `Naturals`'s and `Integers`'s integer-set families. They are
  -- never *called* (`Nat()` is not a term), so they resolve at the `.var` node directly, by name —
  -- never through `Ξ` (`var_op0`/`var_const` exclude them via `hnb`).
  | natSet {M : Memory Value} {τ : Typ} {v : Value}
      (hv : ∀ z, z ∈ v ↔ ∃ k : ℤ, 0 ≤ k ∧ z = Value.ofInt k) :
      Eval Ξ Ω M (.var τ (.module "Naturals" "Nat")) v
  | intSet {M : Memory Value} {τ : Typ} {v : Value}
      (hv : ∀ z, z ∈ v ↔ ∃ k : ℤ, z = Value.ofInt k) :
      Eval Ξ Ω M (.var τ (.module "Integers" "Int")) v
  -- operator application: user operator, by substitution. `hnb` gates this rule to names the
  -- builtin table does not know: a builtin-module operator (`Naturals`'s `+`/`..`, `Sequences`'s
  -- `Len`, …) is resolved by `opCall_builtin` regardless of `Ξ`, so `Ξ` and `opCall_op` carry
  -- user-declared operators only.
  | opCall_op {M : Memory Value} {τ : Typ} {m name : String} {params : List (String × Nat)}
      {body : Expression Typ} {args : List (Expression Typ)} {v : Value}
      (hΞ : Ξ m name = some (params, body))
      (hnb : TypedTLAPlus.builtinOpOf? (.module m name) = none)
      (hlen : params.length = args.length)
      (hb : Eval Ξ Ω M (substParams params args body) v)
      (hargs : args ≠ []) :
      Eval Ξ Ω M (.opCall (.var τ (.module m name)) args) v
  -- operator application: builtin, by kind-strict value semantics. A builtin's meaning is fixed by
  -- its `Origin` here, not by `Ξ`; `opCall_op`'s `hnb` is the other half of that split.
  | opCall_builtin {M : Memory Value} {τ : Typ} {o : Origin} {op : BuiltinOp}
      {args : List (Expression Typ)} {argVals : List Value} {v : Value}
      (hop : TypedTLAPlus.builtinOpOf? o = some op)
      (hargs : EvalList Ξ Ω M args argVals)
      (hb : EvalBuiltin op argVals v) :
      Eval Ξ Ω M (.opCall (.var τ o) args) v
  -- bounded quantifiers. Each opens `body` with a name `z` drawn from *outside* a finite set `L`
  -- the derivation names — never the binder's own hint. `M.insert z w` then answers for it. `L`
  -- lets a proof demand the witness fresh for its own free-variable bookkeeping (`evalUnique'`
  -- picks a common `z ∉ L₁ ∪ L₂`, `evalSubst'` one avoiding the substituted expression); `body`'s
  -- value at `w` is `z`-independent, so this pins down the same relation as opening with any one
  -- fresh name would.
  | forall_true {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S : Value}
      (L : Finset String)
      (hdom : Eval Ξ Ω M dom S)
      (hall : ∀ z, z ∉ L → ∀ w, w ∈ S → Eval Ξ Ω (M.insert z w) (body.openVar z) Value.tru) :
      Eval Ξ Ω M (.forall x τ dom body) Value.tru
  | forall_false {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S w : Value}
      (L : Finset String)
      (hdom : Eval Ξ Ω M dom S) (hw : w ∈ S)
      (hbody : ∀ z, z ∉ L → Eval Ξ Ω (M.insert z w) (body.openVar z) Value.fls) :
      Eval Ξ Ω M (.forall x τ dom body) Value.fls
  | exists_true {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S w : Value}
      (L : Finset String)
      (hdom : Eval Ξ Ω M dom S) (hw : w ∈ S)
      (hbody : ∀ z, z ∉ L → Eval Ξ Ω (M.insert z w) (body.openVar z) Value.tru) :
      Eval Ξ Ω M (.exists x τ dom body) Value.tru
  | exists_false {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S : Value}
      (L : Finset String)
      (hdom : Eval Ξ Ω M dom S)
      (hall : ∀ z, z ∉ L → ∀ w, w ∈ S → Eval Ξ Ω (M.insert z w) (body.openVar z) Value.fls) :
      Eval Ξ Ω M (.exists x τ dom body) Value.fls
  -- Hilbert choice. `filt w` is what `pred` denotes at `w`; the value is `Classical.epsilon` over
  -- "in `S`, filtered TRUE", which is deterministic and keeps `Eval` out of the `epsilon` predicate.
  | choose {M : Memory Value} {x : String} {τ : Typ} {dom pred : Expression Typ} {S : Value}
      (filt : Value → Value) (L : Finset String)
      (hdom : Eval Ξ Ω M dom S)
      (hfilt : ∀ z, z ∉ L → ∀ w, w ∈ S → Eval Ξ Ω (M.insert z w) (pred.openVar z) (filt w)) :
      Eval Ξ Ω M (.choose x τ dom pred)
        (Classical.epsilon (λ w ↦ w ∈ S ∧ filt w = Value.tru))
  -- set literal
  | set {M : Memory Value} {es : List (Expression Typ)} {τ : Typ} {vs : List Value} {v : Value}
      (hes : EvalList Ξ Ω M es vs)
      (hto : ∀ z ∈ v, z ∈ vs) (hof : ∀ z ∈ vs, z ∈ v) :
      Eval Ξ Ω M (.set es τ) v
  -- set filter. `filt z` is what `pred` denotes at `z`; membership is `filt z = TRUE`. Keeping
  -- the predicate's value (rather than the proposition "pred holds") is what keeps `Eval` out of a
  -- negative position.
  | collect {M : Memory Value} {x : String} {τ : Typ} {dom pred : Expression Typ} {S v : Value}
      (filt : Value → Value) (L : Finset String)
      (hdom : Eval Ξ Ω M dom S)
      (hfilt : ∀ y, y ∉ L → ∀ z, z ∈ S → Eval Ξ Ω (M.insert y z) (pred.openVar y) (filt z))
      (hto : ∀ z ∈ v, z ∈ S ∧ filt z = Value.tru)
      (hof : ∀ z ∈ S, filt z = Value.tru → z ∈ v) :
    -- TODO: why not use `ZFSet.sep`? Are you afraid of indexed inductives?
      Eval Ξ Ω M (.collect x τ dom pred) v
  -- set image. `img` names the mapped value at each point, keeping `Eval` out of an existential.
  | map' {M : Memory Value} {body : Expression Typ} {x : String} {ann cod : Typ}
      {dom : Expression Typ} {S v : Value} (img : Value → Value) (L : Finset String)
      (hdom : Eval Ξ Ω M dom S)
      (himg : ∀ z, z ∉ L → ∀ w, w ∈ S → Eval Ξ Ω (M.insert z w) (body.openVar z) (img w))
      (hto : ∀ z ∈ v, ∃ w ∈ S, z = img w)
      (hof : ∀ w ∈ S, img w ∈ v) :
      Eval Ξ Ω M (.map' body x ann cod dom) v
  -- function application (deterministic via `fnApply`). `hdom` — the argument is in the function's
  -- domain: applying a function outside its domain is undefined, so no derivation exists there.
  | fnCall {M : Memory Value} {f : Expression Typ} {fnTyp : Typ} {arg : Expression Typ}
      {r k : Value} (hf : Eval Ξ Ω M f r) (hk : Eval Ξ Ω M arg k)
      (hdom : ∃ w, ZFSet.pair k w ∈ r) :
      Eval Ξ Ω M (.fnCall f fnTyp arg) (fnApply r k)
  -- function literal (existence law: the graph is characterised, not built)
  | fn {M : Memory Value} {x : String} {ann cod : Typ} {dom body : Expression Typ} {S G : Value}
      (img : Value → Value) (L : Finset String)
      (hdom : Eval Ξ Ω M dom S)
      (himg : ∀ z, z ∉ L → ∀ w, w ∈ S → Eval Ξ Ω (M.insert z w) (body.openVar z) (img w))
      (hto : ∀ z ∈ G, ∃ w ∈ S, z = ZFSet.pair w (img w))
      (hof : ∀ w ∈ S, ZFSet.pair w (img w) ∈ G) :
      Eval Ξ Ω M (.fn x ann cod dom body) G
  -- record literal. `hfne` — a record has at least one field (an all-`.id` coercion collapses to
  -- `.id`, `Elaborator/Subtyping.lean`), and the discharged literal must evaluate its source, which
  -- `evalCoerce`'s right-hand side needs. Same role as `tuple`'s `hets`.
  | record {M : Memory Value} {fs : List (Typ × String × Expression Typ)} {vs : List Value}
      (hfne : fs ≠ []) (hfs : EvalList Ξ Ω M (fs.map (·.2.2)) vs) :
      Eval Ξ Ω M (.record fs) (Value.ofRecord ((fs.map (·.2.1)).zip vs))
  -- record field access (deterministic via `fnApply`). `hdom` — the field is present, same reason
  -- as `fnCall`.
  | recordAccess {M : Memory Value} {e : Expression Typ} {name : String} {r : Value}
      (he : Eval Ξ Ω M e r)
      (hdom : ∃ w, ZFSet.pair (Value.ofString name) w ∈ r) :
      Eval Ξ Ω M (.recordAccess e name) (fnApply r (Value.ofString name))
  -- tuple literal
  | tuple {M : Memory Value} {ets : List (Typ × Expression Typ)} {vs : List Value}
      (hets : ets ≠ []) (hes : EvalList Ξ Ω M (ets.map (·.2)) vs) :
      -- TODO: `ofTuple` not `ofSeq`
      Eval Ξ Ω M (.tuple ets) (Value.ofSeq vs)
  -- sequence literal
  | seq {M : Memory Value} {es : List (Expression Typ)} {τ : Typ} {vs : List Value}
      (hes : EvalList Ξ Ω M es vs) :
      Eval Ξ Ω M (.seq es τ) (Value.ofSeq vs)
  -- one-update EXCEPT
  | except {M : Memory Value} {f : Expression Typ} {τ : Typ}
      {path : List (String ⊕ Expression Typ)} {rhs : Expression Typ}
      {vf vr v : Value} {resolved : List (PathStep Value)}
      (hf : Eval Ξ Ω M f vf) (hpath : EvalPath Ξ Ω M path resolved)
      (hrhs : Eval Ξ Ω M rhs vr) (hv : updatePath vf resolved vr = some v) :
      Eval Ξ Ω M (.except f τ [(path, rhs)]) v
  -- conditional
  | if_true {M : Memory Value} {c t e : Expression Typ} {τ : Typ} {v : Value}
      (hc : Eval Ξ Ω M c Value.tru) (ht : Eval Ξ Ω M t v) :
      Eval Ξ Ω M (.if c t e τ) v
  | if_false {M : Memory Value} {c t e : Expression Typ} {τ : Typ} {v : Value}
      (hc : Eval Ξ Ω M c Value.fls) (he : Eval Ξ Ω M e v) :
      Eval Ξ Ω M (.if c t e τ) v
  -- case, first matching guard wins
  -- TODO: that comment is wrong: any matching guard wins, not necessarily the first one
  | case_hit {M : Memory Value} {bs : List (Expression Typ × Expression Typ)}
      {other : Option (Expression Typ)} {τ : Typ} {i : ℕ} {p q : Expression Typ} {v : Value}
      (hi : bs[i]? = some (p, q))
      (hbefore : ∀ j : ℕ, j < i → ∀ p' q', bs[j]? = some (p', q') → Eval Ξ Ω M p' Value.fls)
      (hp : Eval Ξ Ω M p Value.tru) (hq : Eval Ξ Ω M q v) :
      Eval Ξ Ω M (.case bs other τ) v
  | case_other {M : Memory Value} {bs : List (Expression Typ × Expression Typ)}
      {e : Expression Typ} {τ : Typ} {v : Value}
      (hbefore : ∀ (j : ℕ) p' q', bs[j]? = some (p', q') → Eval Ξ Ω M p' Value.fls)
      (hq : Eval Ξ Ω M e v) :
      Eval Ξ Ω M (.case bs (some e) τ) v

/-- A list of expressions evaluated pointwise. -/
inductive EvalList (Ξ : OperatorEnv) (Ω : Model Value) :
    Memory Value → List (Expression Typ) → List Value → Prop
  | nil {M : Memory Value} : EvalList Ξ Ω M [] []
  | cons {M : Memory Value} {e : Expression Typ} {v : Value} {es : List (Expression Typ)}
      {vs : List Value} (h : Eval Ξ Ω M e v) (hs : EvalList Ξ Ω M es vs) :
      EvalList Ξ Ω M (e :: es) (v :: vs)

/-- A reference's syntactic access path resolved: field segments carry over, index expressions
evaluate. The `EvalPath` companion of `ExprSemantics.ResolvesPath`. -/
inductive EvalPath (Ξ : OperatorEnv) (Ω : Model Value) :
    Memory Value → List (String ⊕ Expression Typ) → List (PathStep Value) → Prop
  | nil {M : Memory Value} : EvalPath Ξ Ω M [] []
  | inl {M : Memory Value} {f : String} {rest : List (String ⊕ Expression Typ)}
      {resolved : List (PathStep Value)} (h : EvalPath Ξ Ω M rest resolved) :
      EvalPath Ξ Ω M (.inl f :: rest) (.inl f :: resolved)
  | inr {M : Memory Value} {e : Expression Typ} {v : Value}
      {rest : List (String ⊕ Expression Typ)} {resolved : List (PathStep Value)}
      (h : Eval Ξ Ω M e v) (hs : EvalPath Ξ Ω M rest resolved) :
      EvalPath Ξ Ω M (.inr e :: rest) (.inr v :: resolved)
end

/-! ## Coercions -/

/-- `coerce c v v'` — the coercion `c` carries `v` to `v'`. Some `<:` witnesses are the identity on
the untagged encoding: a string is already its code-point sequence (`strToSeq`). The rest describe
the built expression's actual effect on `v` — either type-changing work (`set`/`tuple`/`record`/
`function` remapping element types) or a re-view whose result only coincides with `v` when `v` has
the right shape (`tupleToSeq`: `v` must have entries at keys `1..n`; the built `<<v[1], …, v[n]>>`
denotes something else otherwise, and `Eval.fnCall`'s domain premise makes it denote nothing when
an entry is missing). Every `fnApply v k` a case names carries a paired `∃ w, ⟨k, w⟩ ∈ v` alongside
it — the same domain fact `Eval.fnCall` demands, so `evalCoerce` can rebuild the derivation
backwards. -/
-- TODO: this should be an indexed inductive.......
def coerce : Coercion → Value → Value → Prop
  | .id, v, v' => v' = v
  | .strToSeq, v, v' => v' = v
  | .seqToFun _ _, v, v' => (∃ vs, IsSeq v vs) ∧ v' = v
  | .tupleToSeq n _ _, v, v' =>
    (∀ i, i < n → ∃ w, ZFSet.pair (Value.ofNat (i + 1)) w ∈ v) ∧
      v' = Value.ofSeq ((List.range n).map (λ i ↦ fnApply v (Value.ofNat (i + 1))))
  | .set _ _ _ c, v, v' =>
    (∀ w ∈ v, ∃ z, coerce c w z) ∧ (∀ z, z ∈ v' ↔ ∃ w ∈ v, coerce c w z)
  | .tuple coes _ _, v, v' =>
    coes ≠ [] ∧
    ∃ ws : List Value, IsSeq v' ws ∧ ws.length = coes.length ∧
      ∀ i : ℕ, ∀ (_ : i < coes.length) (_ : i < ws.length),
        (∃ w, ZFSet.pair (Value.ofNat (i + 1)) w ∈ v) ∧
        coerce coes[i] (fnApply v (Value.ofNat (i + 1))) ws[i]
  | .record fields, v, v' =>
    fields ≠ [] ∧
    (∀ nc ∈ fields, ∃ w w', ZFSet.pair (Value.ofString nc.1) w' ∈ v ∧ coerce nc.2.1 (fnApply v (Value.ofString nc.1)) w) ∧
    (∀ z, z ∈ v' ↔ ∃ nc, ∃ _h : nc ∈ fields, ∃ w,
      coerce nc.2.1 (fnApply v (Value.ofString nc.1)) w ∧ z = ZFSet.pair (Value.ofString nc.1) w)
  | .function _ _ _ _ _ _ cDom cRng, v, v' =>
    -- `D` is `v`'s domain, `Sd` the coerced domain (`cDom`'s image over `D`); both are named as
    -- sets because `applyComputable` builds a `DOMAIN`/`.map'` that must evaluate to one, and the
    -- untyped value universe has no domain operator to recover them after the fact. `v'`'s value at
    -- a coerced key `w` is `cRng` applied to `v` at *some* preimage of `w` — `applyComputable`
    -- recovers one with `CHOOSE`, matched here by `Classical.epsilon` over the same predicate. Both
    -- totality conjuncts follow `applyComputable`'s `.map'`/`.fn`, which demand every point of the
    -- *built* domain evaluate: `cDom` at every point of `D`, and `cRng` at the recovered preimage
    -- of every point of `Sd` — never at an arbitrary point of `v`.
    ∃ D Sd : Value,
      (∀ z, z ∈ D ↔ ∃ w, ZFSet.pair z w ∈ v) ∧
      (∀ k ∈ D, ∃ w, coerce cDom k w) ∧
      (∀ w, w ∈ Sd ↔ ∃ k ∈ D, coerce cDom k w) ∧
      (∀ w ∈ Sd, ∃ r',
        coerce cRng (fnApply v (Classical.epsilon λ k ↦ k ∈ D ∧ coerce cDom k w)) r') ∧
      ∀ z, z ∈ v' ↔ ∃ w ∈ Sd, ∃ r',
        coerce cRng (fnApply v (Classical.epsilon λ k ↦ k ∈ D ∧ coerce cDom k w)) r' ∧
        z = ZFSet.pair w r'
  | .comp c₁ c₂, v, v' => ∃ mid, coerce c₁ v mid ∧ coerce c₂ mid v'
termination_by c => sizeOf c
decreasing_by
  all:
    first
      | decreasing_trivial
      | (calc
          _ < sizeOf coes := List.sizeOf_get _ _
          _ < _ := by decreasing_trivial)
      | (have hmem : nc ∈ fields := ‹_›
         obtain ⟨nm, cc, ty⟩ := nc
         calc
          _ = sizeOf cc := rfl
          _ < sizeOf (nm, cc, ty) := by decreasing_trivial
          _ < sizeOf fields := List.sizeOf_lt_of_mem hmem
          _ < _ := by decreasing_trivial)

/-! ## The instance -/

/-- `Aborts` in the concrete instance's own vocabulary. -/
abbrev Aborts (Ξ : OperatorEnv) (Ω : Model Value) (M : Memory Value) (e : Expression Typ) : Prop :=
  ¬ ∃ v, Eval Ξ Ω M e v

theorem updatePath_nil' {old v : Value} : updatePath old [] v = some v := rfl

theorem isSeq_inj' {s : Value} {vs ws : List Value} (h : IsSeq s vs) (h' : IsSeq s ws) :
    vs = ws :=
  Value.ofSeq_inj.mp (h ▸ h')

theorem isSeq_tail' {s v : Value} {vs : List Value} (_ : IsSeq s (v :: vs)) :
    ∃ t, IsSeq t vs :=
  ⟨Value.ofSeq vs, rfl⟩

theorem eval_seq_nil' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value} {τ : Typ} :
    ∃ s, Eval Ξ Ω M (.seq [] τ) s ∧ IsSeq s [] :=
  ⟨Value.ofSeq [], .seq EvalList.nil, rfl⟩

theorem seqAppend_isSeq' {s v : Value} {vs : List Value} (h : IsSeq s vs) :
    ∃ s', seqAppend s v = some s' ∧ IsSeq s' (vs ++ [v]) := by
  have hex : ∃ ws, s = Value.ofSeq ws := ⟨vs, h⟩
  have hchoose : hex.choose = vs := Value.ofSeq_inj.mp (hex.choose_spec ▸ h)
  refine ⟨Value.ofSeq (vs ++ [v]), ?_, rfl⟩
  unfold seqAppend
  rw [dif_pos hex, hchoose]

theorem evalVar' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {τ : Typ} {o : Origin} {v : Value} :
    Eval Ξ Ω M (.var τ o) v ↔
      match o with
      | .bound _ => False
      | .free name => M.lookup name = some v
      | .intrinsic _ => False
      | .module m name =>
        match TypedTLAPlus.builtinOpOf? (.module m name) with
        | some .natSet => ∀ z, z ∈ v ↔ ∃ k : ℤ, 0 ≤ k ∧ z = Value.ofInt k
        | some .intSet => ∀ z, z ∈ v ↔ ∃ k : ℤ, z = Value.ofInt k
        | some _ => False
        | none =>
          match Ξ m name with
          | some ([], body) => Eval Ξ Ω M body v
          | some (_ :: _, _) => False
          | none => Ω m name = some v := by
  iff_intro h h
  · cases h with
    | var_free hb => exact hb
    | var_op0 hΞ hnb hb => simp only [hnb, hΞ]; exact hb
    | var_const hΞ hnb hΩ => simp only [hnb, hΞ]; exact hΩ
    | natSet hv => simpa only [TypedTLAPlus.builtinOpOf?] using hv
    | intSet hv => simpa only [TypedTLAPlus.builtinOpOf?] using hv
  · cases o with
    | bound => exact h.elim
    | free name => exact .var_free h
    | intrinsic => exact h.elim
    | module m name =>
      simp only at h
      cases hb : TypedTLAPlus.builtinOpOf? (.module m name) with
      | some op =>
        rw [hb] at h
        cases op with
        | natSet =>
          have hmn := TypedTLAPlus.builtinOpOf?_eq_natSet.mp hb
          injection hmn with hm hn; subst hm; subst hn
          exact .natSet h
        | intSet =>
          have hmn := TypedTLAPlus.builtinOpOf?_eq_intSet.mp hb
          injection hmn with hm hn; subst hm; subst hn
          exact .intSet h
        | _ => exact h.elim
      | none =>
        rw [hb] at h
        cases hΞ : Ξ m name with
        | none => rw [hΞ] at h; exact .var_const hΞ hb h
        | some pb =>
          obtain ⟨p, b⟩ := pb
          cases p with
          | nil => rw [hΞ] at h; exact .var_op0 hΞ hb h
          | cons _ _ => rw [hΞ] at h; exact h.elim

/-- Determinism for the builtin-operator relation: each `(op, args)` pair `EvalBuiltin` is defined
on denotes a single value. `args` is generalized before the case split so that both hypotheses can
be inverted while the shared argument list is still a variable — the value encodings
(`Value.ofInt`, `Value.ofSeq`, `Value.tru`) are not constructor-headed, so `cases` on the second
hypothesis would otherwise stall on an unsolvable index equation. -/
theorem evalBuiltinUnique {op : BuiltinOp} {args : List Value} {v w : Value}
    (h₁ : EvalBuiltin op args v) (h₂ : EvalBuiltin op args w) : v = w := by
  generalize hA : args = A at h₂
  cases h₁ <;> cases h₂ <;>
    simp only [List.cons.injEq, and_true, and_self, Value.ofInt_inj, Value.ofNat_inj,
      Value.ofSeq_inj, Value.tru_ne_fls, Value.fls_ne_tru] at hA ⊢ <;>
    first
      | rfl
      | (exfalso; omega)
      | contradiction
      | (rw [ZFSet.ext_iff]; simp_all)
      | (obtain ⟨rfl, rfl⟩ := hA; first | rfl | contradiction | simp_all)

/-- `Len` denotes only on sequences — inversion. `Value.ofSeq` is not constructor-headed, so
`generalize` the argument before `cases`. -/
theorem evalBuiltin_len_inv {a b : Value} (h : EvalBuiltin .len [a] b) :
    ∃ vs, a = Value.ofSeq vs ∧ b = Value.ofNat vs.length := by
  generalize hA : [a] = A at h
  cases h with
  | len => obtain ⟨rfl, -⟩ := List.cons.injEq .. |>.mp hA; exact ⟨_, rfl, rfl⟩

/-- `..` builds an integer interval — inversion. -/
theorem evalBuiltin_range_inv {a b s : Value} (h : EvalBuiltin .range [a, b] s) :
    ∃ x y : ℤ, a = Value.ofInt x ∧ b = Value.ofInt y ∧
      ∀ z, z ∈ s ↔ ∃ k : ℤ, x ≤ k ∧ k ≤ y ∧ z = Value.ofInt k := by
  generalize hA : [a, b] = A at h
  cases h with
  | range hv =>
    obtain ⟨rfl, rfl, -⟩ := by simpa only [List.cons.injEq, and_true] using hA
    exact ⟨_, _, rfl, rfl, hv⟩

/-- `DOMAIN` denotes the set of keys of a function value — inversion. -/
theorem evalBuiltin_domain_inv {f s : Value} (h : EvalBuiltin .domain [f] s) :
    ∀ z, z ∈ s ↔ ∃ w, ZFSet.pair z w ∈ f := by
  generalize hA : [f] = A at h
  cases h with
  | domain hv => obtain ⟨rfl, -⟩ := List.cons.injEq .. |>.mp hA; exact hv

/-- `=` on values denotes `TRUE` on equal arguments, `FALSE` otherwise — inversion. -/
theorem evalBuiltin_eq_inv {a b c : Value} (h : EvalBuiltin .eq [a, b] c) :
    (a = b ∧ c = Value.tru) ∨ (a ≠ b ∧ c = Value.fls) := by
  generalize hA : [a, b] = A at h
  cases h with
  | eq_pos =>
    obtain ⟨rfl, rfl, -⟩ := by simpa only [List.cons.injEq, and_true] using hA
    exact .inl ⟨rfl, rfl⟩
  | eq_neg hne =>
    obtain ⟨rfl, rfl, -⟩ := by simpa only [List.cons.injEq, and_true] using hA
    exact .inr ⟨hne, rfl⟩

/-- A one-argument builtin call inverts to its argument's value and the builtin step. The
`opCall_op` alternative cannot fire: its `hnb` says the name is not a builtin, contradicting the
premise that it is. -/
theorem evalOpCall1_inv {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {τ : Typ} {o : Origin} {op : BuiltinOp} {arg : Expression Typ} {s : Value}
    (hname : TypedTLAPlus.builtinOpOf? o = some op)
    (h : Eval Ξ Ω M (.opCall (.var τ o) [arg]) s) :
    ∃ a, Eval Ξ Ω M arg a ∧ EvalBuiltin op [a] s := by
  cases h with
  | opCall_op _ hnb _ _ => rw [hname] at hnb; simp at hnb
  | opCall_builtin hop hargs hb =>
    rw [hname] at hop; obtain rfl := Option.some.inj hop
    cases hargs with
    | cons ha htl => cases htl; exact ⟨_, ha, hb⟩

/-- A two-argument builtin call inverts to both argument values and the builtin step. -/
theorem evalOpCall2_inv {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {τ : Typ} {o : Origin} {op : BuiltinOp}
    {a1 a2 : Expression Typ} {s : Value}
    (hname : TypedTLAPlus.builtinOpOf? o = some op)
    (h : Eval Ξ Ω M (.opCall (.var τ o) [a1, a2]) s) :
    ∃ v1 v2, Eval Ξ Ω M a1 v1 ∧ Eval Ξ Ω M a2 v2 ∧ EvalBuiltin op [v1, v2] s := by
  cases h with
  | opCall_op _ hnb _ _ => rw [hname] at hnb; simp at hnb
  | opCall_builtin hop hargs hb =>
    rw [hname] at hop; obtain rfl := Option.some.inj hop
    cases hargs with
    | cons h1 htl => cases htl with | cons h2 htl2 => cases htl2; exact ⟨_, _, h1, h2, hb⟩

/-- Some name outside a given finite set — `String` is infinite. The cofinite binder rules of
`Eval` hand out "for every `z ∉ L`"; a determinism/inversion proof feeds back one `z` chosen
outside the union of both derivations' `L`s. -/
private theorem exists_fresh (s : Finset String) : ∃ z : String, z ∉ s := s.exists_notMem

/-- Evaluation is deterministic: an expression denotes at most one value. Proved through the mutual
recursor `Eval.rec` — `induction` does not fire on a member of a mutual inductive family, so the
`EvalList`/`EvalPath` determinism is threaded in as `motive_2`/`motive_3` and discharged in the same
pass. -/
theorem evalUnique' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {e : Expression Typ} {v w : Value} (h₁ : Eval Ξ Ω M e v) (h₂ : Eval Ξ Ω M e w) : v = w := by
  revert w
  induction h₁ using Eval.rec
    (motive_2 := λ M es vs _ ↦ ∀ ws, EvalList Ξ Ω M es ws → vs = ws)
    (motive_3 := λ M p rs _ ↦ ∀ rs', EvalPath Ξ Ω M p rs' → rs = rs') with
  | nat hn =>
    intro w h₂; cases h₂ with
    | nat hn' => rw [hn] at hn'; exact congrArg Value.ofNat (Option.some.inj hn')
  | str => intro w h₂; cases h₂ with | str => rfl
  | tru => intro w h₂; cases h₂ with | tru => rfl
  | fls => intro w h₂; cases h₂ with | fls => rfl
  | var_free hb =>
    intro w h₂; cases h₂ with | var_free hb' => rw [hb] at hb'; exact Option.some.inj hb'
  | var_op0 hΞ hnb hbdy ihbdy =>
    intro w h₂; cases h₂ with
    | var_op0 hΞ' hnb' hbdy' =>
      simp only [hΞ, Option.some.injEq, Prod.mk.injEq, true_and] at hΞ'
      subst hΞ'
      exact ihbdy hbdy'
    | var_const hΞ' hnb' hΩ' => rw [hΞ] at hΞ'; contradiction
    | natSet _ => simp [TypedTLAPlus.builtinOpOf?] at hnb
    | intSet _ => simp [TypedTLAPlus.builtinOpOf?] at hnb
  | var_const hΞ hnb hΩ =>
    intro w h₂; cases h₂ with
    | var_op0 hΞ' hnb' hbdy' => rw [hΞ] at hΞ'; contradiction
    | var_const hΞ' hnb' hΩ' => rw [hΩ] at hΩ'; exact Option.some.inj hΩ'
    | natSet _ => simp [TypedTLAPlus.builtinOpOf?] at hnb
    | intSet _ => simp [TypedTLAPlus.builtinOpOf?] at hnb
  | natSet hv =>
    intro w h₂
    have hw := evalVar'.mp h₂
    simp only [TypedTLAPlus.builtinOpOf?] at hw
    exact ZFSet.ext λ z ↦ (hv z).trans (hw z).symm
  | intSet hv =>
    intro w h₂
    have hw := evalVar'.mp h₂
    simp only [TypedTLAPlus.builtinOpOf?] at hw
    exact ZFSet.ext λ z ↦ (hv z).trans (hw z).symm
  | opCall_op hΞ hnb hlen hbdy hargs ihbdy =>
    intro w h₂; cases h₂ with
    | opCall_op hΞ' hnb' hlen' hbdy' hargs' =>
      simp only [hΞ, Option.some.injEq, Prod.mk.injEq] at hΞ'
      obtain ⟨rfl, rfl⟩ := hΞ'
      exact ihbdy hbdy'
    | opCall_builtin hop' hargs' hb' =>
      rw [hnb] at hop'
      contradiction
  | opCall_builtin hop hargs hb ihargs =>
    intro w h₂; cases h₂ with
    | opCall_op hΞ' hnb' hlen' hbdy' =>
      rw [hnb'] at hop
      contradiction
    | opCall_builtin hop' hargs' hb' =>
      rw [hop] at hop'
      obtain rfl := Option.some.inj hop'
      obtain rfl := ihargs _ hargs'
      exact evalBuiltinUnique hb hb'
  | forall_true L hdom hall ihdom ihall =>
    intro w h₂; cases h₂ with
    | forall_true L' hdom' hall' => rfl
    | forall_false L' hdom' hw' hbody' =>
      obtain rfl := ihdom hdom'
      obtain ⟨z, hz⟩ := exists_fresh (L ∪ L')
      obtain ⟨hzL, hzL'⟩ := Finset.notMem_union.mp hz
      absurd (ihall z hzL _ hw' (hbody' z hzL'))
      exact Value.tru_ne_fls
  | forall_false L hdom hw hbody ihdom ihbody =>
    intro w h₂; cases h₂ with
    | forall_true L' hdom' hall' =>
      obtain rfl := ihdom hdom'
      obtain ⟨z, hz⟩ := exists_fresh (L ∪ L')
      obtain ⟨hzL, hzL'⟩ := Finset.notMem_union.mp hz
      absurd (ihbody z hzL (hall' z hzL' _ hw))
      exact Value.fls_ne_tru
    | forall_false L' hdom' hw' hbody' => rfl
  | exists_true L hdom hw hbody ihdom ihbody =>
    intro w h₂; cases h₂ with
    | exists_true L' hdom' hw' hbody' => rfl
    | exists_false L' hdom' hall' =>
      obtain rfl := ihdom hdom'
      obtain ⟨z, hz⟩ := exists_fresh (L ∪ L')
      obtain ⟨hzL, hzL'⟩ := Finset.notMem_union.mp hz
      absurd (ihbody z hzL (hall' z hzL' _ hw))
      exact Value.tru_ne_fls
  | exists_false L hdom hall ihdom ihall =>
    intro w h₂; cases h₂ with
    | exists_true L' hdom' hw' hbody' =>
      obtain rfl := ihdom hdom'
      obtain ⟨z, hz⟩ := exists_fresh (L ∪ L')
      obtain ⟨hzL, hzL'⟩ := Finset.notMem_union.mp hz
      absurd (ihall z hzL _ hw' (hbody' z hzL'))
      exact Value.fls_ne_tru
    | exists_false L' hdom' hall' => rfl
  | choose filt L hdom hfilt ihdom ihfilt =>
    intro w h₂; cases h₂ with
    | choose filt' L' hdom' hfilt' =>
      obtain rfl := ihdom hdom'
      obtain ⟨z, hz⟩ := exists_fresh (L ∪ L')
      obtain ⟨hzL, hzL'⟩ := Finset.notMem_union.mp hz
      refine congrArg Classical.epsilon (funext λ u ↦ propext (and_congr_right λ hu ↦ ?_))
      rw [ihfilt z hzL u hu (hfilt' z hzL' u hu)]
  | set hes hto hof ihes =>
    intro w h₂; cases h₂ with
    | set hes' hto' hof' =>
      obtain rfl := ihes _ hes'
      exact ZFSet.ext λ z ↦ ⟨λ hz ↦ hof' z (hto z hz), λ hz ↦ hof z (hto' z hz)⟩
  | collect filt L hdom hfilt hto hof ihdom ihfilt =>
    intro w h₂; cases h₂ with
    | collect filt' L' hdom' hfilt' hto' hof' =>
      obtain rfl := ihdom hdom'
      obtain ⟨y, hy⟩ := exists_fresh (L ∪ L')
      obtain ⟨hyL, hyL'⟩ := Finset.notMem_union.mp hy
      refine ZFSet.ext λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩
      · obtain ⟨hzS, hfz⟩ := hto z hz
        exact hof' z hzS ((ihfilt y hyL z hzS (hfilt' y hyL' z hzS)).symm.trans hfz)
      · obtain ⟨hzS, hfz⟩ := hto' z hz
        exact hof z hzS ((ihfilt y hyL z hzS (hfilt' y hyL' z hzS)).trans hfz)
  | map' img L hdom himg hto hof ihdom ihimg =>
    intro w h₂; cases h₂ with
    | map' img' L' hdom' himg' hto' hof' =>
      obtain rfl := ihdom hdom'
      obtain ⟨y, hy⟩ := exists_fresh (L ∪ L')
      obtain ⟨hyL, hyL'⟩ := Finset.notMem_union.mp hy
      refine ZFSet.ext λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩
      · obtain ⟨u, huS, rfl⟩ := hto z hz
        rw [(ihimg y hyL u huS (himg' y hyL' u huS) : img u = img' u)]
        exact hof' u huS
      · obtain ⟨u, huS, rfl⟩ := hto' z hz
        rw [← (ihimg y hyL u huS (himg' y hyL' u huS) : img u = img' u)]
        exact hof u huS
  | fnCall hf hk hdom ihf ihk =>
    intro w h₂; cases h₂ with
    | fnCall hf' hk' _ => rw [(ihf hf' : _ = _), (ihk hk' : _ = _)]
  | fn img L hdom himg hto hof ihdom ihimg =>
    intro w h₂; cases h₂ with
    | fn img' L' hdom' himg' hto' hof' =>
      obtain rfl := ihdom hdom'
      obtain ⟨y, hy⟩ := exists_fresh (L ∪ L')
      obtain ⟨hyL, hyL'⟩ := Finset.notMem_union.mp hy
      refine ZFSet.ext λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩
      · obtain ⟨u, huS, rfl⟩ := hto z hz
        rw [(ihimg y hyL u huS (himg' y hyL' u huS) : img u = img' u)]
        exact hof' u huS
      · obtain ⟨u, huS, rfl⟩ := hto' z hz
        rw [← (ihimg y hyL u huS (himg' y hyL' u huS) : img u = img' u)]
        exact hof u huS
  | record _ hfs ihfs =>
    intro w h₂; cases h₂ with | record _ hfs' => rw [ihfs _ hfs']
  | recordAccess he hdom ihe =>
    intro w h₂; cases h₂ with | recordAccess he' _ => rw [(ihe he' : _ = _)]
  | tuple _ hes ihes =>
    intro w h₂; cases h₂ with | tuple _ hes' => rw [ihes _ hes']
  | seq hes ihes =>
    intro w h₂; cases h₂ with | seq hes' => rw [ihes _ hes']
  | except hf hpath hrhs hv ihf ihpath ihrhs =>
    intro w h₂; cases h₂ with
    | «except» hf' hpath' hrhs' hv' =>
      obtain rfl := ihf hf'
      obtain rfl := ihpath _ hpath'
      obtain rfl := ihrhs hrhs'
      rwa [hv, Option.some.injEq] at hv'
  | if_true hc ht ihc iht =>
    intro w h₂; cases h₂ with
    | if_true hc' ht' => exact iht ht'
    | if_false hc' he' => absurd (ihc hc'); exact Value.tru_ne_fls
  | if_false hc he ihc ihe =>
    intro w h₂; cases h₂ with
    | if_true hc' ht' => absurd (ihc hc'); exact Value.fls_ne_tru
    | if_false hc' he' => exact ihe he'
  | @case_hit _ _ _ _ i _ _ _ hi hbefore hp hq ihbefore ihp ihq =>
    intro w h₂
    cases h₂ with
    | @case_hit _ _ _ _ i₂ _ _ _ hi₂ hbefore₂ hp₂ hq₂ =>
      rcases lt_trichotomy i i₂ with hlt | rfl | hgt
      · absurd (ihp (hbefore₂ _ hlt _ _ hi)); exact Value.tru_ne_fls
      · rw [hi] at hi₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj hi₂)
        exact ihq hq₂
      · absurd (ihbefore _ hgt _ _ hi₂ hp₂).symm; exact Value.tru_ne_fls
    | case_other hbefore₂ hq₂ =>
      absurd (ihp (hbefore₂ _ _ _ hi)); exact Value.tru_ne_fls
  | case_other hbefore hq ihbefore ihq =>
    intro w h₂; cases h₂ with
    | @case_hit _ _ _ _ i₂ _ _ _ hi₂ hbefore₂ hp₂ hq₂ =>
      absurd (ihbefore _ _ _ hi₂ hp₂).symm; exact Value.tru_ne_fls
    | case_other hbefore₂ hq₂ => exact ihq hq₂
  | cons _ _ ihh ihhs _ hl =>
    cases hl with | cons hh' hhs' => rw [ihh hh', ihhs _ hhs']
  | inl _ ih _ hp =>
    cases hp with | inl hrest' => rw [ih _ hrest']
  | inr _ _ ihv ihrest _ hp =>
    cases hp with | inr hv' hrest' => rw [ihv hv', ihrest _ hrest']
  | _ => next h => cases h; rfl

/-- `EvalList` determinism, standalone: a list of expressions denotes at most one list of values.
Recurses on the expression list; the mutual `Eval` determinism is `evalUnique'`. -/
theorem evalListUnique' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value} :
    ∀ {es : List (Expression Typ)} {vs ws : List Value},
      EvalList Ξ Ω M es vs → EvalList Ξ Ω M es ws → vs = ws
  | [], _, _, h₁, h₂ => by cases h₁; cases h₂; rfl
  | _ :: _, _, _, h₁, h₂ => by
    cases h₁ with
    | cons h hs =>
      cases h₂ with | cons h' hs' => rw [evalUnique' h h', evalListUnique' hs hs']

/-- `EvalPath` determinism, standalone: a syntactic access path resolves to at most one semantic
path. Recurses on the syntactic path. -/
theorem evalPathUnique' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value} :
    ∀ {path : List (String ⊕ Expression Typ)} {rs rs' : List (PathStep Value)},
      EvalPath Ξ Ω M path rs → EvalPath Ξ Ω M path rs' → rs = rs'
  | [], _, _, h₁, h₂ => by cases h₁; cases h₂; rfl
  | .inl _ :: _, _, _, h₁, h₂ => by
    cases h₁ with | inl hrest => cases h₂ with | inl hrest' => rw [evalPathUnique' hrest hrest']
  | .inr _ :: _, _, _, h₁, h₂ => by
    cases h₁ with
    | inr hv hrest =>
      cases h₂ with | inr hv' hrest' => rw [evalUnique' hv hv', evalPathUnique' hrest hrest']

/-- `coerce c v` has at most one image. Every `coerce` case pins `v'` — an equation directly, or an
extensional characterisation whose right-hand side names only `c` and `v` — so determinism follows
without appeal to `Eval`. `.tuple`/`.comp` recurse on a sub-coercion. -/
theorem coerceUnique : ∀ {c : Coercion} {v v₁' v₂' : Value},
    coerce c v v₁' → coerce c v v₂' → v₁' = v₂'
  | .id, _, _, _, h₁, h₂ => by simp only [coerce] at h₁ h₂; exact h₁.trans h₂.symm
  | .strToSeq, _, _, _, h₁, h₂ => by simp only [coerce] at h₁ h₂; exact h₁.trans h₂.symm
  | .seqToFun _ _, _, _, _, h₁, h₂ => by simp only [coerce] at h₁ h₂; exact h₁.2.trans h₂.2.symm
  | .tupleToSeq _ _ _, _, _, _, h₁, h₂ => by
    simp only [coerce] at h₁ h₂; exact h₁.2.trans h₂.2.symm
  | .set _ _ _ _, _, _, _, h₁, h₂ => by
    simp only [coerce] at h₁ h₂; exact ZFSet.ext λ z ↦ (h₁.2 z).trans (h₂.2 z).symm
  | .record _, _, _, _, h₁, h₂ => by
    simp only [coerce] at h₁ h₂; exact ZFSet.ext λ z ↦ (h₁.2.2 z).trans (h₂.2.2 z).symm
  | .function _ _ _ _ _ _ _ _, _, _, _, h₁, h₂ => by
    simp only [coerce] at h₁ h₂
    obtain ⟨D₁, Sd₁, hD₁, -, hSd₁, -, hg₁⟩ := h₁
    obtain ⟨D₂, Sd₂, hD₂, -, hSd₂, -, hg₂⟩ := h₂
    obtain rfl : D₁ = D₂ := ZFSet.ext λ z ↦ (hD₁ z).trans (hD₂ z).symm
    obtain rfl : Sd₁ = Sd₂ := ZFSet.ext λ w ↦ (hSd₁ w).trans (hSd₂ w).symm
    exact ZFSet.ext λ z ↦ (hg₁ z).trans (hg₂ z).symm
  | .tuple coes _ _, _, _, _, h₁, h₂ => by
    simp only [coerce] at h₁ h₂
    obtain ⟨_, ws₁, hseq₁, hlen₁, hcoe₁⟩ := h₁
    obtain ⟨_, ws₂, hseq₂, hlen₂, hcoe₂⟩ := h₂
    change _ = Value.ofSeq ws₁ at hseq₁
    change _ = Value.ofSeq ws₂ at hseq₂
    rw [hseq₁, hseq₂]
    have hlleq : ws₁.length = ws₂.length := by omega
    refine congrArg Value.ofSeq (List.ext_getElem hlleq (λ i hi₁ hi₂ ↦ ?_))
    have hic₁ : i < coes.length := hlen₁ ▸ hi₁
    have hic₂ : i < coes.length := hlen₂ ▸ hi₂
    exact coerceUnique (hcoe₁ i hic₁ hi₁).2 (hcoe₂ i hic₂ hi₂).2
  | .comp _ _, _, _, _, h₁, h₂ => by
    simp only [coerce] at h₁ h₂
    obtain ⟨mid₁, hm₁a, hm₁b⟩ := h₁
    obtain ⟨mid₂, hm₂a, hm₂b⟩ := h₂
    obtain rfl := coerceUnique hm₁a hm₂a
    exact coerceUnique hm₁b hm₂b
termination_by c => sizeOf c
decreasing_by
  2,3: decreasing_trivial
  · calc
      _ < sizeOf coes := List.sizeOf_get _ _
      _ < _ := by decreasing_trivial

/-- The `EvalList` behind `.tupleToSeq`'s discharged `.seq`: a list of index projections
`e[i+1]`, one per `i ∈ L`. Every element re-evaluates the shared `e`, pinned to one `r` by
`evalUnique'`; the `.nat` literal parses back (`Nat.toNat?_repr`); each projection carries its
`fnCall` domain premise. -/
theorem evalList_fnCallNat {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {e : Expression Typ} {fnTyp : Typ} {r : Value} (hr : Eval Ξ Ω M e r) :
    ∀ {L : List ℕ} {vs : List Value},
      EvalList Ξ Ω M (L.map (λ i ↦ Expression.fnCall e fnTyp (.nat (toString (i + 1))))) vs ↔
        vs = L.map (λ i ↦ fnApply r (Value.ofNat (i + 1))) ∧
        ∀ i ∈ L, ∃ w, ZFSet.pair (Value.ofNat (i + 1)) w ∈ r := by
  intro L
  induction L with
  | nil =>
    intro vs
    iff_rintro h ⟨rfl, _⟩
    · cases h; exact ⟨rfl, by simp⟩
    · exact .nil
  | cons i is ih =>
    intro vs
    iff_rintro h ⟨rfl, hdoms⟩
    · cases h with
      | cons hhd htl =>
        cases hhd with
        | fnCall hf hk hdom =>
          obtain rfl := evalUnique' hf hr
          obtain rfl := evalUnique' hk (.nat (Nat.toNat?_repr (i + 1)))
          obtain ⟨htail, hdomtail⟩ := ih.mp htl
          refine ⟨?_, ?_⟩
          · rw [List.map_cons, htail]
          · intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact hdom
            · exact hdomtail j hj
    · rw [List.map_cons]
      refine .cons (.fnCall hr (.nat (Nat.toNat?_repr _)) (hdoms i (List.mem_cons_self ..))) ?_
      exact ih.mpr ⟨rfl, λ j hj ↦ hdoms j (List.mem_cons_of_mem _ hj)⟩

/-- One index projection of a non-empty `.tupleToSeq` list is enough to pin down `e`'s value. -/
theorem evalList_fnCallNat_ex {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {e : Expression Typ} {fnTyp : Typ} {L : List ℕ} {vs : List Value}
    (h : EvalList Ξ Ω M (L.map (λ j ↦ Expression.fnCall e fnTyp (.nat (toString (j + 1))))) vs)
    (hne : L ≠ []) : ∃ r, Eval Ξ Ω M e r := by
  match L, h with
  | [], _ => contradiction
  | _ :: _, h =>
    cases h with
    | cons hhd _ => cases hhd with | fnCall hf _ _ => exact ⟨_, hf⟩

/-- `EvalList` is `List.Forall₂` of `Eval` — the companion inductive undoes what the kernel's
positivity check forced apart in `Eval`'s definition. Stated post hoc, where nesting is fine. -/
theorem evalList_iff_forall₂ {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value} :
    ∀ {es : List (Expression Typ)} {vs : List Value},
      EvalList Ξ Ω M es vs ↔ List.Forall₂ (Eval Ξ Ω M) es vs
  | [], _ => ⟨λ h ↦ by cases h; exact .nil, λ h ↦ by cases h; exact .nil⟩
  | _ :: _, _ => by
    refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
    · cases h with | cons hh hs => exact .cons hh (evalList_iff_forall₂.mp hs)
    · cases h with | cons hh hs => exact .cons hh (evalList_iff_forall₂.mpr hs)

/-- `EvalList` by index: a length equation plus pointwise evaluation. The form the multi-component
coercions (`tuple`/`record`) need, so their induction over components happens once here. -/
theorem evalList_getElem {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {es : List (Expression Typ)} {vs : List Value} :
    EvalList Ξ Ω M es vs ↔
      es.length = vs.length ∧
      ∀ i (h₁ : i < es.length) (h₂ : i < vs.length), Eval Ξ Ω M es[i] vs[i] := by
  simp only [evalList_iff_forall₂, List.forall₂_iff_get, List.get_eq_getElem]

/-- The per-field coercion of a `.record` is a strict subterm — the termination witness for
`evalCoerce'`'s `.record` recursion. `Coercion.record`'s payload nests a `Prod`, so this is not one
of `decreasing_trivial`'s shapes. -/
private theorem sizeOf_record_field {fields : List (String × Coercion × Typ)} {i : ℕ}
    (hi : i < fields.length) : sizeOf fields[i].2.1 < sizeOf (Coercion.record fields) := by
  have h1 : sizeOf fields[i] < sizeOf (Coercion.record fields) :=
    calc sizeOf fields[i] < sizeOf fields := List.sizeOf_lt_of_mem (List.getElem_mem hi)
      _ < _ := by decreasing_trivial
  rcases hf : fields[i] with ⟨nm, cc, ty⟩
  simp only [hf, Prod.mk.sizeOf_spec] at h1
  show sizeOf cc < _
  omega

theorem evalLocal' {Ξ : OperatorEnv} {Ω : Model Value} {M₁ M₂ : Memory Value}
    {e : Expression Typ} {v : Value} (hΞ : Ξ.WellScoped)
    (h : ∀ x ∈ e.freeVars, M₁.lookup x = M₂.lookup x) :
    Eval Ξ Ω M₁ e v ↔ Eval Ξ Ω M₂ e v := by
  have agree_insert : ∀ {N₁ N₂ : Memory Value} {y : String} {w : Value} {S : Finset String},
      (∀ z ∈ S.erase y, N₁.lookup z = N₂.lookup z) →
      ∀ z ∈ S, (N₁.insert y w).lookup z = (N₂.insert y w).lookup z := by
    intro N₁ N₂ y w S hag z hz
    by_cases hzy : z = y
    · subst hzy; rw [Finmap.lookup_insert, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hzy, Finmap.lookup_insert_of_ne _ hzy]
      exact hag z (Finset.mem_erase.mpr ⟨hzy, hz⟩)
  -- Every binder case recurses into `body.openVar x` with `M.insert x w`; the domain agreement
  -- covers `body.freeVars`, and `freeVars_openVar_erase` shrinks `(body.openVar x).freeVars \ {x}`
  -- back onto it. No freshness hypothesis needed.
  have bind : ∀ {N₁ N₂ : Memory Value} {x : String} {w : Value} {dom body : Expression Typ},
      (∀ z ∈ dom.freeVars ∪ body.freeVars, N₁.lookup z = N₂.lookup z) →
      ∀ z ∈ (body.openVar x).freeVars,
        (N₁.insert x w).lookup z = (N₂.insert x w).lookup z := by
    intro N₁ N₂ x w dom body hag
    exact agree_insert (λ z hz ↦
      hag z (Finset.mem_union_right _ (Expression.freeVars_openVar_erase hz)))
  have key : ∀ {N₁ : Memory Value} {e' : Expression Typ} {v' : Value}, Eval Ξ Ω N₁ e' v' →
      ∀ {N₂ : Memory Value}, (∀ x ∈ e'.freeVars, N₁.lookup x = N₂.lookup x) → Eval Ξ Ω N₂ e' v' := by
    intro N₁ e' v' hev
    induction hev using Eval.rec
      (motive_2 := λ N es vs _ ↦ ∀ {N' : Memory Value},
        (∀ e ∈ es, ∀ x ∈ e.freeVars, N.lookup x = N'.lookup x) → EvalList Ξ Ω N' es vs)
      (motive_3 := λ N p rs _ ↦ ∀ {N' : Memory Value},
        (∀ e, Sum.inr e ∈ p → ∀ x ∈ e.freeVars, N.lookup x = N'.lookup x) → EvalPath Ξ Ω N' p rs) with
    | nat hn => exact λ _ ↦ .nat hn
    | str => exact λ _ ↦ .str
    | tru => exact λ _ ↦ .tru
    | fls => exact λ _ ↦ .fls
    | var_free hb =>
      intro N₂ hag
      have hx := hag _ (by rw [Expression.freeVars]; exact Finset.mem_singleton.mpr rfl)
      exact .var_free (hx ▸ hb)
    | var_op0 hΞ' hnb' _ ih =>
      intro N₂ _
      exact .var_op0 hΞ' hnb' (ih (λ z hz ↦ by simp [hΞ _ _ _ _ hΞ'] at hz))
    | var_const hΞ' hnb' hΩ' => exact λ _ ↦ .var_const hΞ' hnb' hΩ'
    | natSet hv => exact λ _ ↦ .natSet hv
    | intSet hv => exact λ _ ↦ .intSet hv
    | opCall_op hΞ' hnb hlen _ hargs ih =>
      intro N₂ hag
      refine .opCall_op hΞ' hnb hlen (ih (λ z hz ↦ ?_)) hargs
      rcases substParams_freeVars hlen hz with hbz | ⟨a, ha, hza⟩
      · simp [hΞ _ _ _ _ hΞ'] at hbz
      · exact hag z (Expression.mem_freeVars_opCall.mpr (.inr ⟨a, ha, hza⟩))
    | opCall_builtin hop _ hb ihargs =>
      intro N₂ hag
      exact .opCall_builtin hop
        (ihargs (λ a haa z hz ↦ hag z (Expression.mem_freeVars_opCall.mpr (.inr ⟨a, haa, hz⟩)))) hb
    | forall_true L _ _ ihdom ihall =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .forall_true L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz)))
        (λ z hz w hw ↦ ihall z hz w hw (bind hag))
    | forall_false L _ ihw _ ihdom ihbody =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .forall_false L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz))) ihw
        (λ z hz ↦ ihbody z hz (bind hag))
    | exists_true L _ ihw _ ihdom ihbody =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .exists_true L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz))) ihw
        (λ z hz ↦ ihbody z hz (bind hag))
    | exists_false L _ _ ihdom ihall =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .exists_false L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz)))
        (λ z hz w hw ↦ ihall z hz w hw (bind hag))
    | choose filt L _ _ ihdom ihfilt =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .choose filt L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz)))
        (λ z hz w hw ↦ ihfilt z hz w hw (bind hag))
    | set _ hto hof ihes =>
      intro N₂ hag
      exact .set (ihes (λ e he z hz ↦ hag z (Expression.mem_freeVars_set.mpr ⟨e, he, hz⟩))) hto hof
    | collect filt L _ _ hto hof ihdom ihfilt =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .collect filt L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz)))
        (λ y hy z hz ↦ ihfilt y hy z hz (bind hag)) hto hof
    | map' img L _ _ hto hof ihdom ihimg =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .map' img L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz)))
        (λ z hz w hw ↦ ihimg z hz w hw (bind hag)) hto hof
    | fnCall _ _ hdom ihf ihk =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .fnCall (ihf (λ z hz ↦ hag z (Finset.mem_union_left _ hz)))
        (ihk (λ z hz ↦ hag z (Finset.mem_union_right _ hz))) hdom
    | fn img L _ _ hto hof ihdom ihbody =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .fn img L (ihdom (λ z hz ↦ hag z (Finset.mem_union_left _ hz)))
        (λ z hz w hw ↦ ihbody z hz w hw (bind hag)) hto hof
    | record hfne _ ihfs =>
      intro N₂ hag
      refine .record hfne (ihfs (λ e he z hz ↦ ?_))
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      exact hag z (Expression.mem_freeVars_record.mpr ⟨f, hf, hz⟩)
    | recordAccess _ hdom ihe =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .recordAccess (ihe hag) hdom
    | tuple hets _ ihes =>
      intro N₂ hag
      refine .tuple hets (ihes (λ e he z hz ↦ ?_))
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      exact hag z (Expression.mem_freeVars_tuple.mpr ⟨p, hp, hz⟩)
    | seq _ ihes =>
      intro N₂ hag
      exact .seq (ihes (λ e he z hz ↦ hag z (Expression.mem_freeVars_seq.mpr ⟨e, he, hz⟩)))
    | «except» _ _ _ hv ihf ihpath ihrhs =>
      intro N₂ hag
      simp only [Expression.mem_freeVars_except_single] at hag
      exact .«except» (ihf (λ z hz ↦ hag z (Or.inl hz)))
        (ihpath (λ e hep z hz ↦ hag z (.inr (.inl ⟨e, hep, hz⟩))))
        (ihrhs (λ z hz ↦ hag z (.inr (.inr hz)))) hv
    | if_true _ _ iht ihc =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .if_true (iht (λ z hz ↦ hag z (Finset.mem_union_left _ (Finset.mem_union_left _ hz))))
        (ihc (λ z hz ↦ hag z (Finset.mem_union_left _ (Finset.mem_union_right _ hz))))
    | if_false _ _ ihc ihe =>
      intro N₂ hag
      rw [Expression.freeVars] at hag
      exact .if_false (ihc (λ z hz ↦ hag z (Finset.mem_union_left _ (Finset.mem_union_left _ hz))))
        (ihe (λ z hz ↦ hag z (Finset.mem_union_right _ hz)))
    | case_hit hi _ _ _ ihbefore ihp ihq =>
      intro N₂ hag
      refine .case_hit hi (λ j hj p' q' hjeq ↦ ihbefore j hj p' q' hjeq (λ z hz ↦ ?_))
        (ihp (λ z hz ↦ hag z (Expression.mem_freeVars_case.mpr
          (.inl ⟨_, List.mem_of_getElem? hi, .inl hz⟩))))
        (ihq (λ z hz ↦ hag z (Expression.mem_freeVars_case.mpr
          (.inl ⟨_, List.mem_of_getElem? hi, .inr hz⟩))))
      exact hag z (Expression.mem_freeVars_case.mpr
        (.inl ⟨(p', q'), List.mem_of_getElem? hjeq, .inl hz⟩))
    | case_other _ _ ihbefore ihe =>
      intro N₂ hag
      refine .case_other (λ j p' q' hjeq ↦ ihbefore j p' q' hjeq (λ z hz ↦ ?_))
        (ihe (λ z hz ↦ hag z (Expression.mem_freeVars_case.mpr (.inr ⟨_, rfl, hz⟩))))
      exact hag z (Expression.mem_freeVars_case.mpr
        (.inl ⟨(p', q'), List.mem_of_getElem? hjeq, .inl hz⟩))
    | cons _ _ ihh ihhs hag =>
      exact .cons (ihh (λ z hz ↦ hag _ List.mem_cons_self z hz))
        (ihhs (λ e he z hz ↦ hag e (List.mem_cons_of_mem _ he) z hz))
    | inl _ ih hag =>
      exact .inl (ih (λ e hep z hz ↦ hag e (List.mem_cons_of_mem _ hep) z hz))
    | inr _ _ ihh ihrest hag =>
      exact .inr (ihh (λ z hz ↦ hag _ List.mem_cons_self z hz))
        (ihrest (λ e hep z hz ↦ hag e (List.mem_cons_of_mem _ hep) z hz))
    | _ => exact .nil
  exact ⟨λ hev ↦ key hev h, λ hev ↦ key hev (λ x hx ↦ (h x hx).symm)⟩

/-- Application of a sequence value at a valid index: the value stored at that position. -/
theorem fnApply_ofSeq {vs : List Value} {j : ℕ} (hj : j < vs.length) :
    fnApply (Value.ofSeq vs) (Value.ofNat (j + 1)) = vs[j] := by
  have hmem : ZFSet.pair (Value.ofNat (j + 1)) vs[j] ∈ Value.ofSeq vs :=
    Value.mem_ofSeq.mpr ⟨j, hj, rfl⟩
  have hspec : ZFSet.pair (Value.ofNat (j + 1))
      (fnApply (Value.ofSeq vs) (Value.ofNat (j + 1))) ∈ Value.ofSeq vs :=
    Classical.epsilon_spec (p := λ w ↦ ZFSet.pair (Value.ofNat (j + 1)) w ∈ Value.ofSeq vs)
      ⟨vs[j], hmem⟩
  obtain ⟨j', hj', heq⟩ := Value.mem_ofSeq.mp hspec
  rw [ZFSet.pair_inj] at heq
  obtain ⟨h1, h2⟩ := heq
  obtain rfl : j = j' := by have := Value.ofNat_inj.mp h1; omega
  exact h2

/-- The `.seqToFun` case of `evalCoerce'`, standalone: it does not recurse on a sub-coercion, only
re-evaluates `e` under the binder the coercion introduces. The cofinite `Eval.fn` rule opens that
binder at a name chosen fresh for `e`, so `evalLocal'` relates the re-evaluation back to `e`'s
ambient value with no freshness hypothesis. The built function `[i ∈ 1 .. Len(e) ↦ e[i]]`
reproduces `e` itself when `e` denotes a sequence — its graph already *is* that indexed family —
and denotes nothing otherwise (`Len` is defined only on sequences), which is exactly what
`coerce (.seqToFun …)` states. -/
theorem evalCoerce'_seqToFun {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {τ : Typ} {i : String} {e : Expression Typ} {v' : Value}
    (hΞ : Ξ.WellScoped) :
    Eval Ξ Ω M (TypedTLAPlus.Coercion.applyComputable (.seqToFun τ i) e) v' ↔
      ∃ v, Eval Ξ Ω M e v ∧ coerce (.seqToFun τ i) v v' := by
  have hloc : ∀ {name : String} {w r : Value}, name ∉ e.freeVars →
      (Eval Ξ Ω (M.insert name w) e r ↔ Eval Ξ Ω M e r) := λ {name w r} hn ↦
    evalLocal' hΞ λ z hz ↦ Finmap.lookup_insert_of_ne _ λ h ↦ hn (h ▸ hz)
  -- The built `.fn`'s body opens (at any fresh name) to `.fnCall e (.seq τ) name`: `e` was
  -- `liftBound`-ed by one when spliced, and `openVar` cancels that exactly.
  have hob : ∀ name : String,
      (Expression.fnCall (Expression.liftBound 1 e) (.seq τ)
          (Expression.var .int (.bound 0) @@ posOf e) @@ posOf e).openVar name
        = Expression.fnCall e (.seq τ) (Expression.var .int (.free name) @@ posOf e) @@ posOf e := by
    intro name
    show Expression.mapVars _ 0 _ = _
    simp only [Expression.mapVars, registerSource]
    exact congrArg (Expression.fnCall · _ _) (Expression.openVar_liftBound_one name e)
  -- the index set of the built function is `{ ofInt k : 1 ≤ k ≤ n }`; `mem` characterises it.
  have hidx : ∀ {n : ℕ} {w : Value}, (∃ k : ℤ, 1 ≤ k ∧ k ≤ (n : ℤ) ∧ w = Value.ofInt k) ↔
      ∃ j : ℕ, j < n ∧ w = Value.ofNat (j + 1) := by
    intro n w
    iff_rintro ⟨k, hk1, hk2, rfl⟩ ⟨j, hj, rfl⟩
    · refine ⟨k.toNat - 1, ?_, ?_⟩
      · omega
      · rw [Value.ofNat, Value.ofInt_inj]; omega
    · refine ⟨(j : ℤ) + 1, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [Value.ofNat, Value.ofInt_inj]; omega
  simp only [TypedTLAPlus.Coercion.applyComputable, coerce, registerSource]
  iff_rintro h ⟨v, he, ⟨vs, rfl⟩, rfl⟩
  · cases h with
    | @fn _ _ _ _ _ _ S G img L hdom himg hto hof =>
      obtain ⟨z, hz⟩ := exists_fresh (L ∪ e.freeVars)
      obtain ⟨hzL, hze⟩ := Finset.notMem_union.mp hz
      replace himg : ∀ w ∈ S, Eval Ξ Ω (M.insert z w)
          (Expression.fnCall e (.seq τ) (Expression.var .int (.free z) @@ posOf e) @@ posOf e)
          (img w) := λ w hw ↦ hob z ▸ himg z hzL w hw
      obtain ⟨vs, he, hSmem⟩ : ∃ vs, Eval Ξ Ω M e (Value.ofSeq vs) ∧
          ∀ w, w ∈ S ↔ ∃ j : ℕ, j < vs.length ∧ w = Value.ofNat (j + 1) := by
        cases hdom with
        | opCall_op _ hnb _ _ => simp [TypedTLAPlus.builtinOpOf?] at hnb
        | opCall_builtin hop hargs hb =>
          simp only [TypedTLAPlus.builtinOpOf?, Option.some.injEq] at hop; subst hop
          cases hargs with
          | cons hnat hrest =>
            cases hrest with
            | cons hlenE hnil =>
              cases hnil
              cases hlenE with
              | opCall_op _ hnb _ _ => simp [TypedTLAPlus.builtinOpOf?] at hnb
              | opCall_builtin hop2 hargs2 hb2 =>
                simp only [TypedTLAPlus.builtinOpOf?, Option.some.injEq] at hop2; subst hop2
                cases hargs2 with
                | cons hee hnil2 =>
                  cases hnil2
                  cases hnat with
                  | @nat _ _ nn hn1 =>
                    obtain rfl : nn = 1 := Option.some.inj (hn1.symm.trans (Nat.toNat?_repr 1))
                    obtain ⟨vs, rfl, rfl⟩ := evalBuiltin_len_inv hb2
                    obtain ⟨x, y, hx, hy, hSraw⟩ := evalBuiltin_range_inv hb
                    rw [Value.ofNat, Value.ofInt_inj, Nat.cast_one] at hx
                    rw [Value.ofNat, Value.ofInt_inj] at hy
                    subst hx; subst hy
                    exact ⟨vs, hee, λ w ↦ (hSraw w).trans (hidx (n := vs.length))⟩
      refine ⟨Value.ofSeq vs, he, ⟨vs, rfl⟩, ?_⟩
      have himg' : ∀ w ∈ S, img w = fnApply (Value.ofSeq vs) w := by
        intro w hw
        obtain ⟨j, hj, rfl⟩ := (hSmem w).mp hw
        have hb := himg _ hw
        generalize hg : img (Value.ofNat (j + 1)) = iw at hb
        cases hb with
        | fnCall hf hk _ =>
          cases hk with
          | var_free hb' =>
            rw [Finmap.lookup_insert, Option.some.injEq] at hb'
            subst hb'
            rw [evalUnique' ((hloc hze).mp hf) he]
      refine ZFSet.ext λ w ↦ ⟨λ hw ↦ ?_, λ hw ↦ ?_⟩
      · obtain ⟨u, hu, rfl⟩ := hto w hw
        obtain ⟨j, hj, rfl⟩ := (hSmem u).mp hu
        rw [himg' _ hu, fnApply_ofSeq hj]
        exact Value.mem_ofSeq.mpr ⟨j, hj, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := Value.mem_ofSeq.mp hw
        have huS : Value.ofNat (j + 1) ∈ S := (hSmem _).mpr ⟨j, hj, rfl⟩
        have := hof _ huS
        rwa [himg' _ huS, fnApply_ofSeq hj] at this
  · set S : Value := Value.ofFinSet ((List.range vs.length).map λ j ↦ Value.ofNat (j + 1))
      with hSdef
    have hSmem : ∀ w, w ∈ S ↔ ∃ j : ℕ, j < vs.length ∧ w = Value.ofNat (j + 1) := by
      intro w
      simp only [hSdef, Value.mem_ofFinSet, List.mem_map, List.mem_range]
      exact ⟨λ ⟨j, hj, h⟩ ↦ ⟨j, hj, h.symm⟩, λ ⟨j, hj, h⟩ ↦ ⟨j, hj, h.symm⟩⟩
    have hrng : EvalBuiltin .range [Value.ofNat 1, Value.ofNat vs.length] S := by
      have h : EvalBuiltin .range [Value.ofInt 1, Value.ofInt (vs.length : ℤ)] S :=
        .range λ w ↦ (hSmem w).trans (hidx (n := vs.length)).symm
      simpa only [Value.ofNat, Nat.cast_one] using h
    have hrangeOp : TypedTLAPlus.builtinOpOf? (.module "Naturals" "..") = some .range := by
      simp [TypedTLAPlus.builtinOpOf?]
    have hlenOp : TypedTLAPlus.builtinOpOf? (.module "Sequences" "Len") = some .len := by
      simp [TypedTLAPlus.builtinOpOf?]
    have hdomDeriv : Eval Ξ Ω M
        (Expression.opCall
          (Expression.var (.operator [.int, .int] (.set .int)) (.module "Naturals" ".."))
          [Expression.nat (toString (1 : Nat)),
           Expression.opCall
             (Expression.var (.operator [.seq τ] .int) (.module "Sequences" "Len")) [e]]) S :=
      .opCall_builtin hrangeOp
        (.cons (.nat (Nat.toNat?_repr 1))
          (.cons (.opCall_builtin hlenOp (.cons he .nil) .len) .nil)) hrng
    refine .fn (λ w ↦ fnApply (Value.ofSeq vs) w) e.freeVars hdomDeriv ?_ ?_ ?_
    · intro z hz w hw
      rw [hob z]
      obtain ⟨j, hj, rfl⟩ := (hSmem w).mp hw
      exact .fnCall ((hloc hz).mpr he) (.var_free (Finmap.lookup_insert _))
        ⟨vs[j], Value.mem_ofSeq.mpr ⟨j, hj, rfl⟩⟩
    · intro w hw
      obtain ⟨j, hj, rfl⟩ := Value.mem_ofSeq.mp hw
      refine ⟨Value.ofNat (j + 1), (hSmem _).mpr ⟨j, hj, rfl⟩, ?_⟩
      rw [fnApply_ofSeq hj]
    · intro w hw
      obtain ⟨j, hj, rfl⟩ := (hSmem w).mp hw
      rw [fnApply_ofSeq hj]
      exact Value.mem_ofSeq.mpr ⟨j, hj, rfl⟩

/-- The `.function` case of `evalCoerce'`, standalone. `ihD`/`ihR` are `evalCoerce'` at the strictly
smaller `cDom`/`cRng` — passed in so this lives outside the `evalCoerce'` recursion block while the
termination checker still sees the calls. -/
theorem evalCoerce'_function {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {x y : String} {dom rng dom' rng' : Typ} {cD cR : Coercion} {e : Expression Typ} {v' : Value}
    (hΞ : Ξ.WellScoped)
    (ihD : ∀ {M : Memory Value} {e : Expression Typ} {v' : Value},
      Eval Ξ Ω M (cD.applyComputable e) v' ↔ ∃ v, Eval Ξ Ω M e v ∧ coerce cD v v')
    (ihR : ∀ {M : Memory Value} {e : Expression Typ} {v' : Value},
      Eval Ξ Ω M (cR.applyComputable e) v' ↔ ∃ v, Eval Ξ Ω M e v ∧ coerce cR v v') :
    Eval Ξ Ω M (TypedTLAPlus.Coercion.applyComputable
        (.function x y dom rng dom' rng' cD cR) e) v' ↔
      ∃ v, Eval Ξ Ω M e v ∧ coerce (.function x y dom rng dom' rng' cD cR) v v' := by classical
  have hloc : ∀ {name : String} {w r : Value}, name ∉ e.freeVars →
      (Eval Ξ Ω (M.insert name w) e r ↔ Eval Ξ Ω M e r) := λ {name w r} hn ↦
    evalLocal' hΞ λ z hz ↦ Finmap.lookup_insert_of_ne _ λ h ↦ hn (h ▸ hz)
  have hdomOp : TypedTLAPlus.builtinOpOf? (.intrinsic "DOMAIN") = some .domain := by
    simp [TypedTLAPlus.builtinOpOf?]
  have heqOp : TypedTLAPlus.builtinOpOf? (.intrinsic "=") = some .eq := by
    simp [TypedTLAPlus.builtinOpOf?]
  -- Opening the binders the coercion introduces, at whatever fresh names the cofinite `Eval`
  -- rules hand out: `newDomain`'s `.map'` body and the recovered-argument `CHOOSE` at `zx`, the
  -- built `.fn`'s body at `zy` (`eLift` collapses to `e`, the injected `.bound 1` becomes
  -- `.free zy`).
  have hR1 : ∀ zx, (cD.applyComputable (Expression.var dom (.bound 0))).openVar zx
      = cD.applyComputable (Expression.var dom (.free zx)) := by
    intro zx
    rw [openVar_applyComputable]
    congr 1
    simp only [Expression.openVar, Expression.mapVars, Expression.openVarLam, registerSource, if_pos]
  have hR2 : ∀ zy, (cR.applyComputable ((Expression.liftBound 1 e).fnCall (.function dom rng)
        (Expression.choose x dom
          ((Expression.var (.operator [.function dom rng] (.set dom)) (.intrinsic "DOMAIN")).opCall
            [Expression.liftBound 1 e])
          ((Expression.var (.operator [dom', dom'] .bool) (.intrinsic "=")).opCall
            [cD.applyComputable (Expression.var dom (.bound 0)),
              Expression.var dom' (.bound 1)])))).openVar zy
      = cR.applyComputable (Expression.fnCall e (.function dom rng)
        (Expression.choose x dom
          ((Expression.var (.operator [.function dom rng] (.set dom)) (.intrinsic "DOMAIN")).opCall [e])
          ((Expression.var (.operator [dom', dom'] .bool) (.intrinsic "=")).opCall
            [cD.applyComputable (Expression.var dom (.bound 0)),
              Expression.var dom' (.free zy)]))) := by
    intro zy
    rw [openVar_applyComputable]
    congr 1
    show Expression.mapVars _ 0 _ = _
    rewrite [Expression.mapVars]
    simp only [registerSource]
    rw [show Expression.mapVars (Expression.openVarLam zy) 0 (Expression.liftBound 1 e) = e from
          Expression.openVar_liftBound_one zy e]
    congr 1
    rewrite [Expression.mapVars]
    simp only [registerSource]
    congr 1
    · rewrite [Expression.mapVars]
      simp only [registerSource, List.attach_map_val, List.map_cons, List.map_nil,
        Expression.mapVars, Expression.openVarLam]
      rw [show Expression.mapVars (Expression.openVarLam zy) 0 (Expression.liftBound 1 e) = e from
            Expression.openVar_liftBound_one zy e]
    · rewrite [Expression.mapVars]
      simp only [registerSource, List.attach_map_val, List.map_cons, List.map_nil]
      rewrite [ComputableTLAPlus.openVar_applyComputable_aux cD zy (Expression.var dom (.bound 0)) 1]
      simp only [Expression.mapVars, Expression.openVarLam, registerSource, reduceIte,
        Nat.reduceEqDiff, Nat.reduceLT]
  have hR3 : ∀ zx zy, ((Expression.var (.operator [dom', dom'] .bool) (.intrinsic "=")).opCall
        [cD.applyComputable (Expression.var dom (.bound 0)),
          Expression.var dom' (.free zy)]).openVar zx
      = (Expression.var (.operator [dom', dom'] .bool) (.intrinsic "=")).opCall
        [cD.applyComputable (Expression.var dom (.free zx)), Expression.var dom' (.free zy)] := by
    intro zx zy
    show Expression.mapVars _ 0 _ = _
    rewrite [Expression.mapVars]
    simp only [registerSource, List.attach_map_val, List.map_cons, List.map_nil]
    rewrite [ComputableTLAPlus.openVar_applyComputable_aux cD zx (Expression.var dom (.bound 0)) 0]
    simp only [Expression.mapVars, Expression.openVarLam, registerSource, reduceIte, Nat.reduceLT]
  simp only [TypedTLAPlus.Coercion.applyComputable, coerce, registerSource]
  iff_rintro h ⟨v, hev, DD, Sd, hDchar, hcDtot, hSdchar, hcRtot, hgraph⟩
  · cases h with
    | @fn _ _ _ _ _ _ SdV _ imgB Lfn hdomND himgBR htoG hofG =>
      obtain ⟨zy, hzy⟩ := exists_fresh (Lfn ∪ e.freeVars)
      obtain ⟨hzyL, hzye⟩ := Finset.notMem_union.mp hzy
      cases hdomND with
      | @map' _ _ _ _ _ _ DV _ imgD Lmap hdomDE himgD htoD hofD =>
        obtain ⟨zx, hzx⟩ := exists_fresh Lmap
        obtain ⟨ve, hev, hbD⟩ := evalOpCall1_inv hdomOp hdomDE
        have hDchar : ∀ z, z ∈ DV ↔ ∃ w, ZFSet.pair z w ∈ ve := evalBuiltin_domain_inv hbD
        have hcoeD : ∀ k ∈ DV, coerce cD k (imgD k) := by
          intro k hk
          have hd := himgD zx hzx k hk
          rw [hR1 zx] at hd
          obtain ⟨vv, hvar, hc⟩ := ihD.mp hd
          simp only [evalVar', Finmap.lookup_insert, Option.some.injEq] at hvar
          subst hvar
          exact hc
        have hcoeR : ∀ w ∈ SdV,
            coerce cR (fnApply ve (Classical.epsilon λ k ↦ k ∈ DV ∧ coerce cD k w)) (imgB w) := by
          intro w hw
          have hbr := himgBR zy hzyL w hw
          rw [hR2 zy] at hbr
          obtain ⟨vv, hcall, hcR⟩ := ihR.mp hbr
          cases hcall with
          | fnCall hf hka _ =>
            obtain rfl := evalUnique' ((hloc hzye).mp hf) hev
            cases hka with
            | @choose _ _ _ _ _ SS filt Lch hdomRA hfilt =>
              obtain ⟨zx2, hzx2⟩ := exists_fresh (Lch ∪ {zy})
              obtain ⟨hzx2L, hzx2y⟩ := Finset.notMem_union.mp hzx2
              rw [Finset.notMem_singleton] at hzx2y
              obtain ⟨ve', hev', hbD'⟩ := evalOpCall1_inv hdomOp hdomRA
              obtain rfl := evalUnique' ((hloc hzye).mp hev') hev
              have hSSDV : SS = DV := evalBuiltinUnique hbD' hbD
              have hpred : (λ k ↦ k ∈ SS ∧ filt k = Value.tru)
                  = (λ k ↦ k ∈ SS ∧ coerce cD k w) := by
                funext k
                by_cases hk : k ∈ SS
                · simp only [hk, true_and]
                  apply propext
                  have hf3 := hfilt zx2 hzx2L k hk
                  rw [hR3 zx2 zy] at hf3
                  obtain ⟨c1, c2, hc1, hc2, heqb⟩ := evalOpCall2_inv heqOp hf3
                  have hc2w : c2 = w := by
                    simp only [evalVar'] at hc2
                    rw [Finmap.lookup_insert_of_ne _ hzx2y.symm, Finmap.lookup_insert] at hc2
                    exact (Option.some.inj hc2).symm
                  subst c2
                  have hcoeck : coerce cD k c1 := by
                    obtain ⟨vv2, hvar2, hc⟩ := ihD.mp hc1
                    simp only [evalVar', Finmap.lookup_insert, Option.some.injEq] at hvar2
                    subst hvar2
                    exact hc
                  rcases evalBuiltin_eq_inv heqb with ⟨he1, hf1⟩ | ⟨hne1, hf1⟩
                  · exact iff_of_true hf1 (he1 ▸ hcoeck)
                  · rw [hf1]
                    exact iff_of_false Value.fls_ne_tru
                      (λ hcw ↦ hne1 (coerceUnique hcoeck hcw))
                · simp only [hk, false_and]
              rwa [hpred, hSSDV] at hcR
        refine ⟨ve, hev, DV, SdV, hDchar, λ k hk ↦ ⟨imgD k, hcoeD k hk⟩, ?_, ?_, ?_⟩
        · intro w
          iff_rintro hw ⟨k, hk, hc⟩
          · obtain ⟨k, hk, rfl⟩ := htoD w hw
            exact ⟨k, hk, hcoeD k hk⟩
          · obtain rfl := coerceUnique hc (hcoeD k hk)
            exact hofD k hk
        · exact λ w hw ↦ ⟨imgB w, hcoeR w hw⟩
        · intro z
          iff_rintro hz ⟨w, hw, r', hcr, rfl⟩
          · obtain ⟨w, hw, rfl⟩ := htoG z hz
            exact ⟨w, hw, imgB w, hcoeR w hw, rfl⟩
          · obtain rfl := coerceUnique hcr (hcoeR w hw)
            exact hofG w hw
  · have hDcoe : ∀ k ∈ DD, coerce cD k (Classical.epsilon λ z ↦ coerce cD k z) :=
      λ k hk ↦ Classical.epsilon_spec (hcDtot k hk)
    refine Eval.fn (S := Sd)
      (λ w ↦ Classical.epsilon λ r' ↦
        coerce cR (fnApply v (Classical.epsilon λ k ↦ k ∈ DD ∧ coerce cD k w)) r')
      e.freeVars ?hdomND ?himgBR ?htoG ?hofG
    case hdomND =>
      refine Eval.map' (S := DD) (λ z ↦ Classical.epsilon λ w ↦ coerce cD z w) ∅ ?_ ?_ ?_ ?_
      · exact Eval.opCall_builtin hdomOp (.cons hev .nil) (EvalBuiltin.domain hDchar)
      · intro zx _ w hw
        rw [hR1 zx]
        refine ihD.mpr ⟨w, evalVar'.mpr ?_, hDcoe w hw⟩
        simp only [Finmap.lookup_insert]
      · intro z hz
        obtain ⟨k, hk, hc⟩ := (hSdchar z).mp hz
        exact ⟨k, hk, coerceUnique hc (hDcoe k hk)⟩
      · intro w hw
        exact (hSdchar _).mpr ⟨w, hw, hDcoe w hw⟩
    case himgBR =>
      intro zy hzy w hw
      rw [hR2 zy]
      have hspec : ∃ k, k ∈ DD ∧ coerce cD k w := (hSdchar w).mp hw
      have hε := Classical.epsilon_spec hspec
      refine ihR.mpr
        ⟨fnApply v (Classical.epsilon λ k ↦ k ∈ DD ∧ coerce cD k w), ?_, ?_⟩
      · refine Eval.fnCall ((hloc hzy).mpr hev) ?_ ((hDchar _).mp hε.1)
        have hfeq : (λ k ↦ k ∈ DD ∧ coerce cD k w)
            = (λ k ↦ k ∈ DD ∧
                (if coerce cD k w then Value.tru else Value.fls) = Value.tru) := by
          funext k
          by_cases hc : coerce cD k w <;> simp [hc, Value.fls_ne_tru]
        rw [show (Classical.epsilon λ k ↦ k ∈ DD ∧ coerce cD k w)
              = Classical.epsilon (λ k ↦ k ∈ DD ∧
                  (if coerce cD k w then Value.tru else Value.fls) = Value.tru)
            from congrArg Classical.epsilon hfeq]
        refine Eval.choose (λ k ↦ if coerce cD k w then Value.tru else Value.fls) {zy} ?_ ?_
        · exact Eval.opCall_builtin hdomOp (.cons ((hloc hzy).mpr hev) .nil) (EvalBuiltin.domain hDchar)
        · intro zx hzx k hk
          rw [Finset.notMem_singleton] at hzx
          rw [hR3 zx zy]
          have hcDx : Eval Ξ Ω ((M.insert zy w).insert zx k)
              (cD.applyComputable (Expression.var dom (.free zx)))
              (Classical.epsilon λ z ↦ coerce cD k z) := by
            refine ihD.mpr ⟨k, evalVar'.mpr ?_, hDcoe k hk⟩
            simp only [Finmap.lookup_insert]
          have hvy : Eval Ξ Ω ((M.insert zy w).insert zx k) (Expression.var dom' (.free zy)) w := by
            refine evalVar'.mpr ?_
            show ((M.insert zy w).insert zx k).lookup zy = some w
            rw [Finmap.lookup_insert_of_ne _ hzx.symm, Finmap.lookup_insert]
          have heqb : EvalBuiltin .eq [Classical.epsilon λ z ↦ coerce cD k z, w]
              (if coerce cD k w then Value.tru else Value.fls) := by
            by_cases hc : coerce cD k w
            · rw [coerceUnique (hDcoe k hk) hc, if_pos hc]
              exact EvalBuiltin.eq_pos
            · rw [if_neg hc]
              exact EvalBuiltin.eq_neg λ h ↦ hc (h ▸ hDcoe k hk)
          exact Eval.opCall_builtin heqOp (.cons hcDx (.cons hvy .nil)) heqb
      · exact Classical.epsilon_spec (hcRtot w hw)
    case htoG =>
      intro z hz
      obtain ⟨w, hw, r', hcr, rfl⟩ := (hgraph z).mp hz
      exact ⟨w, hw, by rw [coerceUnique hcr (Classical.epsilon_spec (hcRtot w hw))]⟩
    case hofG =>
      intro w hw
      exact (hgraph _).mpr ⟨w, hw, _, Classical.epsilon_spec (hcRtot w hw), rfl⟩

/-- Applying a coercion to an expression denotes the coercion applied to that expression's value.
Recurses on `c` through the equation compiler — `Coercion` is a nested inductive, so `induction`
does not fire. Needs `hΞ : Ξ.WellScoped`: the `.seqToFun`/`.function` cases build a `.fn` whose body
re-evaluates `e` under a binder the coercion introduces, and `evalLocal'` relates that back to
`e`'s ambient value — the cofinite `Eval` rules open that binder at a name chosen fresh for `e`, so
no `Coercion.FreshFor` hypothesis is needed. -/
theorem evalCoerce' {Ξ : OperatorEnv} {Ω : Model Value} (hΞ : Ξ.WellScoped) :
    ∀ {c : Coercion} {M : Memory Value} {e : Expression Typ} {v' : Value},
      (Eval Ξ Ω M (TypedTLAPlus.Coercion.applyComputable c e) v' ↔
        ∃ v, Eval Ξ Ω M e v ∧ coerce c v v')
  | .id, _, _, v' => by
    simp only [TypedTLAPlus.Coercion.applyComputable, coerce]
    iff_rintro h ⟨v, hv, rfl⟩
    · exact ⟨v', h, rfl⟩
    · exact hv
  | .strToSeq, M, e, v' => by
    simp only [TypedTLAPlus.Coercion.applyComputable, coerce]
    iff_rintro hev ⟨v, hv, rfl⟩
    · cases hev with
      | opCall_builtin hop hargs hb =>
        simp only [TypedTLAPlus.builtinOpOf?, Option.some.injEq] at hop
        subst hop
        cases hargs with
        | cons he hnil => cases hb with | strToSeq => exact ⟨_, he, rfl⟩
    · exact .opCall_builtin (op := .strToSeq) rfl (.cons hv .nil) .strToSeq
  | .seqToFun τ i, M, e, v' => by
    exact evalCoerce'_seqToFun (i := i) hΞ
  | .tupleToSeq n τ hn, M, e, v' => by
    simp only [TypedTLAPlus.Coercion.applyComputable, coerce, registerSource]
    have hne : List.range n ≠ [] := by
      rw [← List.length_pos_iff, List.length_range]; omega
    iff_rintro hev ⟨r, hr, hdoms, rfl⟩
    · cases hev with
      | seq hes =>
        obtain ⟨r, hr⟩ := evalList_fnCallNat_ex hes hne
        obtain ⟨hvs, hdoms⟩ := (evalList_fnCallNat hr).mp hes
        exact ⟨r, hr, λ i hi ↦ hdoms i (List.mem_range.mpr hi), by rw [hvs]⟩
    · exact .seq ((evalList_fnCallNat hr).mpr ⟨rfl, λ i hi ↦ hdoms i (List.mem_range.mp hi)⟩)
  | .set x τ _ c, M, e, v' => by
    have hob : ∀ zx, (c.applyComputable (Expression.var τ (.bound 0) @@ posOf e)).openVar zx
        = c.applyComputable (Expression.var τ (.free zx) @@ posOf e) := by
      intro zx
      rw [openVar_applyComputable]
      congr 1
      simp only [Expression.openVar, Expression.mapVars, Expression.openVarLam, registerSource,
        if_pos]
    simp only [TypedTLAPlus.Coercion.applyComputable, coerce, registerSource]
    iff_rintro hev ⟨v, hv, htot, hext⟩
    · cases hev with
      | @map' _ _ _ _ _ _ S _ img L hdom himg hto hof =>
        obtain ⟨zx, hzx⟩ := exists_fresh L
        replace himg : ∀ w ∈ S, coerce c w (img w) := by
          intro w hw
          have hi := himg zx hzx w hw
          rw [hob zx] at hi
          obtain ⟨vw, hvar, hc⟩ := (evalCoerce' hΞ).mp hi
          simp only [evalVar', Finmap.lookup_insert, Option.some.injEq] at hvar
          subst hvar
          exact hc
        refine ⟨S, hdom, λ w hw ↦ ⟨img w, himg w hw⟩, λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩⟩
        · obtain ⟨w, hw, rfl⟩ := hto z hz
          exact ⟨w, hw, himg w hw⟩
        · obtain ⟨w, hw, hc⟩ := hz
          obtain rfl := coerceUnique hc (himg w hw)
          exact hof w hw
    · refine .map' (λ w ↦ Classical.epsilon (λ z ↦ coerce c w z)) ∅ hv (λ zx _ w hw ↦ ?_)
        (λ z hz ↦ ?_) (λ w hw ↦ ?_)
      · rw [hob zx]
        refine (evalCoerce' hΞ).mpr ⟨w, evalVar'.mpr ?_, Classical.epsilon_spec (htot w hw)⟩
        simp only [Finmap.lookup_insert]
      · obtain ⟨w, hw, hc⟩ := (hext z).mp hz
        exact ⟨w, hw, coerceUnique hc (Classical.epsilon_spec (htot w hw))⟩
      · exact (hext _).mpr ⟨w, hw, Classical.epsilon_spec (htot w hw)⟩
  | .tuple coes τs τs', M, e, v' => by
    simp only [TypedTLAPlus.Coercion.applyComputable, coerce, registerSource]
    iff_rintro h ⟨v, hv, hcne, ws, hseq, hwslen, IH⟩
    · cases h with
      | @tuple _ _ vs hets hes =>
        obtain ⟨hlen, hget⟩ := evalList_getElem.mp hes
        simp only [List.length_map, List.length_attach, List.length_range] at hlen
        have hcne : coes ≠ [] := by rintro rfl; simp at hets
        have hproj : ∀ i (hi : i < coes.length),
            Eval Ξ Ω M ((coes[i]).applyComputable
              (Expression.fnCall e (.tuple τs) (Expression.nat (toString (i + 1))))) vs[i] := by
          intro i hi
          have hev := hget i
            (by simp only [List.length_map, List.length_attach, List.length_range]; exact hi)
            (hlen ▸ hi)
          simpa only [List.getElem_map, List.getElem_attach, List.getElem_range] using hev
        obtain ⟨r, hr⟩ : ∃ r, Eval Ξ Ω M e r := by
          obtain ⟨w, hw, -⟩ :=
            (evalCoerce' hΞ).mp (hproj 0 (List.length_pos_of_ne_nil hcne))
          cases hw with | fnCall hf _ _ => exact ⟨_, hf⟩
        refine ⟨r, hr, hcne, vs, rfl, hlen.symm, λ i hi₁ hi₂ ↦ ?_⟩
        obtain ⟨w, hw, hc⟩ := (evalCoerce' hΞ).mp (hproj i hi₁)
        cases hw with
        | fnCall hf hk hdom =>
          obtain rfl := evalUnique' hf hr
          obtain rfl := evalUnique' hk (.nat (Nat.toNat?_repr (i + 1)))
          exact ⟨hdom, hc⟩
    · change v' = Value.ofSeq ws at hseq
      subst hseq
      refine .tuple ?_ (evalList_getElem.mpr ⟨?_, λ i h₁ h₂ ↦ ?_⟩)
      · rw [← List.length_pos_iff]
        simp only [List.length_map, List.length_attach, List.length_range]
        exact List.length_pos_of_ne_nil hcne
      · simp only [List.length_map, List.length_attach, List.length_range, hwslen]
      · simp only [List.length_map, List.length_attach, List.length_range] at h₁
        simp only [List.getElem_map, List.getElem_attach, List.getElem_range]
        refine (evalCoerce' hΞ).mpr
          ⟨fnApply v (Value.ofNat (i + 1)), ?_, (IH i h₁ (by omega)).2⟩
        exact .fnCall hv (.nat (Nat.toNat?_repr (i + 1))) (IH i h₁ (by omega)).1
  | .record fields, M, e, v' => by
    simp only [TypedTLAPlus.Coercion.applyComputable, coerce, registerSource]
    iff_rintro h ⟨v, hv, hfne, hcf, hcv⟩
    · cases h with
      | @record _ _ vs hfne hes =>
        obtain ⟨hlen, hget⟩ := evalList_getElem.mp hes
        simp only [List.length_map, List.length_attach] at hlen
        have hfne' : fields ≠ [] := by rintro rfl; simp at hfne
        have hproj : ∀ i (hi : i < fields.length),
            Eval Ξ Ω M ((fields[i].2.1).applyComputable
              (Expression.recordAccess e fields[i].1)) vs[i] := by
          intro i hi
          have hev := hget i
            (by simp only [List.length_map, List.length_attach]; exact hi) (hlen ▸ hi)
          simpa only [List.map_map, List.getElem_map, List.getElem_attach, Function.comp_apply]
            using hev
        obtain ⟨r, hr⟩ : ∃ r, Eval Ξ Ω M e r := by
          have h0 : 0 < fields.length := List.length_pos_of_ne_nil hfne'
          obtain ⟨w, hw, -⟩ := (evalCoerce' hΞ).mp (hproj 0 h0)
          cases hw with | recordAccess hf _ => exact ⟨_, hf⟩
        have hstep : ∀ i (hi : i < fields.length),
            (∃ w', ZFSet.pair (Value.ofString fields[i].1) w' ∈ r) ∧
              coerce fields[i].2.1 (fnApply r (Value.ofString fields[i].1)) vs[i] := by
          intro i hi
          obtain ⟨w, hw, hc⟩ := (evalCoerce' hΞ).mp (hproj i hi)
          cases hw with
          | recordAccess hf hdom => obtain rfl := evalUnique' hf hr; exact ⟨hdom, hc⟩
        refine ⟨r, hr, hfne', λ nc hnc ↦ ?_, λ z ↦ ?_⟩
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hnc
          obtain ⟨⟨w', hw'⟩, hc⟩ := hstep i hi
          exact ⟨vs[i], w', hw', hc⟩
        · rw [Value.ofRecord, Value.mem_recordGraph]
          iff_rintro ⟨k, w, hmem, rfl⟩ ⟨nc, hnc, w, hc, rfl⟩
          · rw [List.mem_iff_getElem] at hmem
            obtain ⟨i, hizip, heq⟩ := hmem
            have hi : i < fields.length := by
              simpa only [List.length_zip, List.length_map, List.length_attach, hlen,
                Nat.min_self] using hizip
            simp only [List.getElem_zip, List.map_map, List.getElem_map, List.getElem_attach,
              Function.comp_apply, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact ⟨fields[i], List.getElem_mem hi, vs[i], (hstep i hi).2, rfl⟩
          · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hnc
            obtain rfl := coerceUnique hc (hstep i hi).2
            refine ⟨fields[i].1, vs[i], ?_, rfl⟩
            rw [List.mem_iff_getElem]
            refine ⟨i, by
              simp only [List.length_zip, List.length_map, List.length_attach, hlen, Nat.min_self]
              omega, ?_⟩
            simp only [List.getElem_zip, List.map_map, List.getElem_map, List.getElem_attach,
              Function.comp_apply]
    · have hw : ∀ nc ∈ fields, ∃ w, coerce nc.2.1 (fnApply v (Value.ofString nc.1)) w := by
        intro nc hnc; obtain ⟨w, _, _, hc⟩ := hcf nc hnc; exact ⟨w, hc⟩
      set vs := fields.attach.map (λ x ↦ Classical.choose (hw x.1 x.2)) with hvs_def
      have hvs_len : vs.length = fields.length := by
        simp only [hvs_def, List.length_map, List.length_attach]
      have hvs_get : ∀ i (hi : i < fields.length),
          coerce fields[i].2.1 (fnApply v (Value.ofString fields[i].1)) (vs[i]'(hvs_len ▸ hi)) := by
        intro i hi
        have hpin : vs[i]'(hvs_len ▸ hi) = Classical.choose (hw fields[i] (List.getElem_mem hi)) := by
          simp only [hvs_def, List.getElem_map, List.getElem_attach]
        rw [hpin]
        exact Classical.choose_spec (hw fields[i] (List.getElem_mem hi))
      have hveq : v' = Value.ofRecord (((fields.attach.map
          (λ x : {y // y ∈ fields} ↦ (x.1.2.2, x.1.1,
            x.1.2.1.applyComputable (Expression.recordAccess e x.1.1)))).map (·.2.1)).zip vs) := by
        refine ZFSet.ext (λ z ↦ ?_)
        rw [hcv z, Value.ofRecord, Value.mem_recordGraph]
        iff_rintro ⟨nc, hnc, w, hc, rfl⟩ ⟨k, w, hmem, rfl⟩
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hnc
          obtain rfl := coerceUnique hc (hvs_get i hi)
          refine ⟨fields[i].1, vs[i], ?_, rfl⟩
          rw [List.mem_iff_getElem]
          refine ⟨i, by
            simp only [List.length_zip, List.length_map, List.length_attach, hvs_len, Nat.min_self]
            omega, ?_⟩
          simp only [List.getElem_zip, List.map_map, List.getElem_map, List.getElem_attach,
            Function.comp_apply]
        · rw [List.mem_iff_getElem] at hmem
          obtain ⟨i, hizip, heq⟩ := hmem
          have hi : i < fields.length := by
            simpa only [List.length_zip, List.length_map, List.length_attach, hvs_len,
              Nat.min_self] using hizip
          simp only [List.getElem_zip, List.map_map, List.getElem_map, List.getElem_attach,
            Function.comp_apply, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨fields[i], List.getElem_mem hi, vs[i], hvs_get i hi, rfl⟩
      rw [hveq]
      refine Eval.record ?_ (evalList_getElem.mpr ⟨?_, λ i h₁ h₂ ↦ ?_⟩)
      · simp only [ne_eq, List.map_eq_nil_iff, List.attach_eq_nil_iff]; exact hfne
      · simp only [List.map_map, List.length_map, List.length_attach, hvs_len]
      · have hi : i < fields.length := by
          simpa only [List.map_map, List.length_map, List.length_attach] using h₁
        have hev : Eval Ξ Ω M ((fields[i].2.1).applyComputable
            (Expression.recordAccess e fields[i].1)) (vs[i]'(hvs_len ▸ hi)) := by
          refine (evalCoerce' hΞ).mpr
            ⟨fnApply v (Value.ofString fields[i].1), ?_, hvs_get i hi⟩
          obtain ⟨ww, ww', hmem, -⟩ := hcf fields[i] (List.getElem_mem hi)
          exact Eval.recordAccess hv ⟨ww', hmem⟩
        simpa only [List.map_map, List.getElem_map, List.getElem_attach, Function.comp_apply]
          using hev
  | .function x y dom rng dom' rng' cD cR, M, e, v' => by
    exact evalCoerce'_function hΞ (evalCoerce' hΞ) (evalCoerce' hΞ)
  | .comp c₁ c₂, M, e, v' => by
    simp only [TypedTLAPlus.Coercion.applyComputable, coerce]
    iff_rintro h ⟨v, hv, mid, hc₁, hc₂⟩
    · obtain ⟨mid, hmid, hc₂⟩ := (evalCoerce' hΞ).mp h
      obtain ⟨v, hv, hc₁⟩ := (evalCoerce' hΞ).mp hmid
      exact ⟨v, hv, mid, hc₁, hc₂⟩
    · exact (evalCoerce' hΞ).mpr ⟨mid, (evalCoerce' hΞ).mpr ⟨v, hv, hc₁⟩, hc₂⟩
  termination_by c => sizeOf c
  decreasing_by
    1,2,9-14: decreasing_trivial
    1-3: calc
           _ < sizeOf coes := List.sizeOf_get _ _
           _ < _ := by decreasing_trivial
    all: exact sizeOf_record_field ‹_›

/-- Close an `evalSubst'` `cases e` arm whose expression constructor cannot match the derivation:
`h : Expression.subst x e' e = <other constructor>` is an equation between distinct constructors,
since `subst` preserves the head. -/
local syntax "subst_ctor_mismatch " ident : tactic
macro_rules
  | `(tactic| subst_ctor_mismatch $h:ident) =>
    `(tactic|
      first
      | (rw [Expression.subst_eq_mapVars] at $h:ident
         simp only [Expression.mapVars, registerSource, reduceCtorEq] at $h:ident)
      | simp only [Expression.subst_case, reduceCtorEq] at $h:ident)

private theorem evalSubst'_fwd {Ξ : OperatorEnv} {Ω : Model Value} {x : String}
    {e' : Expression Typ} (hΞ : Ξ.WellScoped) (hlc : e'.LC) :
    ∀ {N : Memory Value} {e : Expression Typ} {v : Value}, Eval Ξ Ω N e v →
      ∀ {N' : Memory Value},
        (∀ y ∈ e.freeVars, y ≠ x → N.lookup y = N'.lookup y) →
        (∀ w, N.lookup x = some w → Eval Ξ Ω N' e' w) →
        Eval Ξ Ω N' (Expression.subst x e' e) v := by
  have agreeStep : ∀ {N₁ N₂ : Memory Value} {z : String} {w : Value} {D B : Expression Typ},
      (∀ y ∈ D.freeVars ∪ B.freeVars, y ≠ x → N₁.lookup y = N₂.lookup y) →
      ∀ y ∈ (B.openVar z).freeVars, y ≠ x →
        (N₁.insert z w).lookup y = (N₂.insert z w).lookup y := by
    intro N₁ N₂ z w D B hag y hy hyx
    by_cases hyz : y = z
    · subst hyz; rw [Finmap.lookup_insert, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hyz, Finmap.lookup_insert_of_ne _ hyz]
      exact hag y (Finset.mem_union_right _
        (Expression.freeVars_openVar_erase (Finset.mem_erase.mpr ⟨hyz, hy⟩))) hyx
  have xStep : ∀ {N₁ N₂ : Memory Value} {z : String} {w : Value},
      z ≠ x → z ∉ e'.freeVars →
      (∀ u, N₁.lookup x = some u → Eval Ξ Ω N₂ e' u) →
      ∀ u, (N₁.insert z w).lookup x = some u → Eval Ξ Ω (N₂.insert z w) e' u := by
    intro N₁ N₂ z w hzx hze hx u hu
    rw [Finmap.lookup_insert_of_ne _ (Ne.symm hzx)] at hu
    refine (evalLocal' hΞ (λ y hy ↦ ?_)).mp (hx u hu)
    exact (Finmap.lookup_insert_of_ne N₂ (λ h : y = z ↦ hze (h ▸ hy))).symm
  have freshParts : ∀ {z : String} {L : Finset String}, z ∉ L ∪ e'.freeVars ∪ {x} →
      z ∉ L ∧ z ∉ e'.freeVars ∧ z ≠ x := by
    intro z L hz
    obtain ⟨hzLe, hzx⟩ := Finset.notMem_union.mp hz
    obtain ⟨hzL, hze⟩ := Finset.notMem_union.mp hzLe
    exact ⟨hzL, hze, Finset.notMem_singleton.mp hzx⟩
  intro N e v hev
  induction hev using Eval.rec
    (motive_2 := λ N es vs _ ↦ ∀ {N' : Memory Value},
      (∀ e ∈ es, ∀ y ∈ e.freeVars, y ≠ x → N.lookup y = N'.lookup y) →
      (∀ w, N.lookup x = some w → Eval Ξ Ω N' e' w) →
      EvalList Ξ Ω N' (es.map (Expression.subst x e')) vs)
    (motive_3 := λ N p rs _ ↦ ∀ {N' : Memory Value},
      (∀ e, Sum.inr e ∈ p → ∀ y ∈ e.freeVars, y ≠ x → N.lookup y = N'.lookup y) →
      (∀ w, N.lookup x = some w → Eval Ξ Ω N' e' w) →
      EvalPath Ξ Ω N' (p.map λ s ↦ s.map id (Expression.subst x e')) rs) with
  | nat hn => intro N' _ _; rw [Expression.subst_nat]; exact .nat hn
  | str => intro N' _ _; rw [Expression.subst_str]; exact .str
  | tru => intro N' _ _; rw [Expression.subst_true]; exact .tru
  | fls => intro N' _ _; rw [Expression.subst_false]; exact .fls
  | @var_free _ _ name _ hb =>
    intro N' hag hx
    by_cases hnx : name = x
    · subst hnx
      rw [Expression.LC.subst_var_free_eq hlc]
      exact hx _ hb
    · rw [Expression.subst_var_free_ne hnx]
      refine .var_free ?_
      rw [← hag name (by rw [Expression.freeVars]; exact Finset.mem_singleton.mpr rfl) hnx]
      exact hb
  | @var_op0 _ _ m name bodyv _ hΞ' hnb' hbody ihbody =>
    intro N' _ hx
    rw [Expression.subst_var_module]
    have hclosed : bodyv.freeVars = ∅ := hΞ m name [] bodyv hΞ'
    refine .var_op0 hΞ' hnb' ?_
    rw [← Expression.subst_fresh (e' := e') bodyv (by rw [hclosed]; exact Finset.notMem_empty x)]
    exact ihbody (λ y hy _ ↦ absurd hy (by rw [hclosed]; exact Finset.notMem_empty y)) hx
  | var_const hΞ' hnb' hΩ' =>
    intro N' _ _
    rw [Expression.subst_var_module]
    exact .var_const hΞ' hnb' hΩ'
  | natSet hv =>
    intro N' _ _
    rw [Expression.subst_var_module]
    exact .natSet hv
  | intSet hv =>
    intro N' _ _
    rw [Expression.subst_var_module]
    exact .intSet hv
  | @opCall_op _ _ m name params bodyv _ _ hΞ' hnb hlen hbody hargs ihbody =>
    intro N' hag hx
    rw [Expression.subst_opCall, Expression.subst_var_module]
    have hclosed : bodyv.freeVars = ∅ := hΞ m name params bodyv hΞ'
    have hfresh : x ∉ bodyv.freeVars := by rw [hclosed]; exact Finset.notMem_empty x
    refine .opCall_op hΞ' hnb (by rw [List.length_map]; exact hlen) ?_ ?_
    · rw [← subst_substParams hlc hfresh]
      refine ihbody (λ y hy hyx ↦ ?_) hx
      rcases substParams_freeVars hlen hy with h | ⟨a, ha, hya⟩
      · exact (by rw [hclosed]; exact Finset.notMem_empty y : y ∉ bodyv.freeVars) h |>.elim
      · exact hag y (Expression.mem_freeVars_opCall.mpr (.inr ⟨a, ha, hya⟩)) hyx
    · simpa using hargs
  | opCall_builtin hop hargs hb ihargs =>
    intro N' hag hx
    rw [Expression.subst_opCall, subst_var_of_builtin hop]
    refine .opCall_builtin hop ?_ hb
    exact ihargs (λ a ha y hy hyx ↦
      hag y (Expression.mem_freeVars_opCall.mpr (.inr ⟨a, ha, hy⟩)) hyx) hx
  | forall_true L hdom hall ihdom ihall =>
    intro N' hag hx
    rw [Expression.LC.subst_forall hlc]
    rw [Expression.freeVars] at hag
    refine .forall_true (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) ?_
    intro z hz w hw
    obtain ⟨hzL, hze, hzx⟩ := freshParts hz
    rw [Expression.LC.subst_openVar hlc hzx]
    exact ihall z hzL w hw (agreeStep hag) (xStep hzx hze hx)
  | forall_false L hdom hw hbody ihdom ihbody =>
    intro N' hag hx
    rw [Expression.LC.subst_forall hlc]
    rw [Expression.freeVars] at hag
    refine .forall_false (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) hw ?_
    intro z hz
    obtain ⟨hzL, hze, hzx⟩ := freshParts hz
    rw [Expression.LC.subst_openVar hlc hzx]
    exact ihbody z hzL (agreeStep hag) (xStep hzx hze hx)
  | exists_true L hdom hw hbody ihdom ihbody =>
    intro N' hag hx
    rw [Expression.LC.subst_exists hlc]
    rw [Expression.freeVars] at hag
    refine .exists_true (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) hw ?_
    intro z hz
    obtain ⟨hzL, hze, hzx⟩ := freshParts hz
    rw [Expression.LC.subst_openVar hlc hzx]
    exact ihbody z hzL (agreeStep hag) (xStep hzx hze hx)
  | exists_false L hdom hall ihdom ihall =>
    intro N' hag hx
    rw [Expression.LC.subst_exists hlc]
    rw [Expression.freeVars] at hag
    refine .exists_false (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) ?_
    intro z hz w hw
    obtain ⟨hzL, hze, hzx⟩ := freshParts hz
    rw [Expression.LC.subst_openVar hlc hzx]
    exact ihall z hzL w hw (agreeStep hag) (xStep hzx hze hx)
  | choose filt L hdom hfilt ihdom ihfilt =>
    intro N' hag hx
    rw [Expression.LC.subst_choose hlc]
    rw [Expression.freeVars] at hag
    refine .choose filt (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) ?_
    intro z hz w hw
    obtain ⟨hzL, hze, hzx⟩ := freshParts hz
    rw [Expression.LC.subst_openVar hlc hzx]
    exact ihfilt z hzL w hw (agreeStep hag) (xStep hzx hze hx)
  | set hes hto hof ihes =>
    intro N' hag hx
    rw [Expression.subst_set]
    exact .set (ihes (λ a ha y hy hyx ↦
      hag y (Expression.mem_freeVars_set.mpr ⟨a, ha, hy⟩) hyx) hx) hto hof
  | collect filt L hdom hfilt hto hof ihdom ihfilt =>
    intro N' hag hx
    rw [Expression.LC.subst_collect hlc]
    rw [Expression.freeVars] at hag
    refine .collect filt (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) ?_ hto hof
    intro y hy z hz
    obtain ⟨hyL, hye, hyx⟩ := freshParts hy
    rw [Expression.LC.subst_openVar hlc hyx]
    exact ihfilt y hyL z hz (agreeStep hag) (xStep hyx hye hx)
  | map' img L hdom himg hto hof ihdom ihimg =>
    intro N' hag hx
    rw [Expression.LC.subst_map' hlc]
    rw [Expression.freeVars] at hag
    refine .map' img (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) ?_ hto hof
    intro z hz w hw
    obtain ⟨hzL, hze, hzx⟩ := freshParts hz
    rw [Expression.LC.subst_openVar hlc hzx]
    exact ihimg z hzL w hw (agreeStep hag) (xStep hzx hze hx)
  | fnCall hf hk hdom ihf ihk =>
    intro N' hag hx
    rw [Expression.subst_fnCall]
    rw [Expression.freeVars] at hag
    exact .fnCall (ihf (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx)
      (ihk (λ y hy hyx ↦ hag y (Finset.mem_union_right _ hy) hyx) hx) hdom
  | fn img L hdom himg hto hof ihdom ihimg =>
    intro N' hag hx
    rw [Expression.LC.subst_fn hlc]
    rw [Expression.freeVars] at hag
    refine .fn img (L ∪ e'.freeVars ∪ {x})
      (ihdom (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx) ?_ hto hof
    intro z hz w hw
    obtain ⟨hzL, hze, hzx⟩ := freshParts hz
    rw [Expression.LC.subst_openVar hlc hzx]
    exact ihimg z hzL w hw (agreeStep hag) (xStep hzx hze hx)
  | @record _ fs _ hfne hfs ihfs =>
    intro N' hag hx
    rw [Expression.subst_record]
    have hnames : List.map (λ p : Typ × String × Expression Typ ↦ p.2.1)
          (List.map (λ p ↦ (p.1, p.2.1, Expression.subst x e' p.2.2)) fs)
        = List.map (·.2.1) fs := by simp [List.map_map, Function.comp_def]
    rw [← hnames]
    refine .record (λ h ↦ hfne (List.map_eq_nil_iff.mp h)) ?_
    have key := ihfs (λ a ha y hy hyx ↦ by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
        exact hag y (Expression.mem_freeVars_record.mpr ⟨f, hf, hy⟩) hyx) hx
    simpa [List.map_map, Function.comp_def] using key
  | recordAccess he hdom ihe =>
    intro N' hag hx
    rw [Expression.subst_recordAccess]
    rw [Expression.freeVars] at hag
    exact .recordAccess (ihe hag hx) hdom
  | tuple hets hes ihes =>
    intro N' hag hx
    rw [Expression.subst_tuple]
    refine .tuple (λ h ↦ hets (List.map_eq_nil_iff.mp h)) ?_
    have key := ihes (λ a ha y hy hyx ↦ by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        exact hag y (Expression.mem_freeVars_tuple.mpr ⟨p, hp, hy⟩) hyx) hx
    simpa [List.map_map, Function.comp_def] using key
  | seq hes ihes =>
    intro N' hag hx
    rw [Expression.subst_seq]
    exact .seq (ihes (λ a ha y hy hyx ↦
      hag y (Expression.mem_freeVars_seq.mpr ⟨a, ha, hy⟩) hyx) hx)
  | «except» hf hpath hrhs hv ihf ihpath ihrhs =>
    intro N' hag hx
    rewrite [Expression.subst_except_single]
    simp only [Expression.mem_freeVars_except_single] at hag
    exact .«except» (ihf (λ y hy hyx ↦ hag y (.inl hy) hyx) hx)
      (ihpath (λ ee hee y hy hyx ↦ hag y (.inr (.inl ⟨ee, hee, hy⟩)) hyx) hx)
      (ihrhs (λ y hy hyx ↦ hag y (.inr (.inr hy)) hyx) hx) hv
  | if_true hc ht ihc iht =>
    intro N' hag hx
    rw [Expression.subst_if]
    rw [Expression.freeVars, Finset.union_assoc] at hag
    exact .if_true (ihc (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx)
      (iht (λ y hy hyx ↦ hag y (Finset.mem_union_right _ (Finset.mem_union_left _ hy)) hyx) hx)
  | if_false hc he ihc ihe =>
    intro N' hag hx
    rw [Expression.subst_if]
    rw [Expression.freeVars, Finset.union_assoc] at hag
    exact .if_false (ihc (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hx)
      (ihe (λ y hy hyx ↦ hag y (Finset.mem_union_right _ (Finset.mem_union_right _ hy)) hyx) hx)
  | @case_hit _ _ _ _ i pp qq _ hi hbefore hp hq ihbefore ihp ihq =>
    intro N' hag hx
    rw [Expression.subst_case]
    refine .case_hit (i := i) (by rw [List.getElem?_map, hi]; rfl)
      (λ j hj p' q' hjeq ↦ ?_) ?_ ?_
    · obtain ⟨⟨p₀, q₀⟩, hj₀, heq⟩ := by
        have := hjeq; rw [List.getElem?_map] at this
        exact Option.map_eq_some_iff.mp this
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ihbefore j hj p₀ q₀ hj₀ (λ y hy hyx ↦
        hag y (Expression.mem_freeVars_case.mpr
          (.inl ⟨(p₀, q₀), List.mem_of_getElem? hj₀, .inl hy⟩)) hyx) hx
    · exact ihp (λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr
        (.inl ⟨(pp, qq), List.mem_of_getElem? hi, .inl hy⟩)) hyx) hx
    · exact ihq (λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr
        (.inl ⟨(pp, qq), List.mem_of_getElem? hi, .inr hy⟩)) hyx) hx
  | case_other hbefore hq ihbefore ihq =>
    intro N' hag hx
    rw [Expression.subst_case]
    refine .case_other (λ j p' q' hjeq ↦ ?_) ?_
    · obtain ⟨⟨p₀, q₀⟩, hj₀, heq⟩ := by
        have := hjeq; rw [List.getElem?_map] at this
        exact Option.map_eq_some_iff.mp this
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ihbefore j p₀ q₀ hj₀ (λ y hy hyx ↦
        hag y (Expression.mem_freeVars_case.mpr
          (.inl ⟨(p₀, q₀), List.mem_of_getElem? hj₀, .inl hy⟩)) hyx) hx
    · exact ihq (λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr (.inr ⟨_, rfl, hy⟩)) hyx) hx
  | @cons M ee vv es vs hev hevs ihHead hh hhs ihh ihhs =>
    exact .cons (ihHead (λ y hy hyx ↦ ihh ee List.mem_cons_self y hy hyx) ihhs)
      (hh (λ a ha y hy hyx ↦ ihh a (List.mem_cons_of_mem _ ha) y hy hyx) ihhs)
  | @inl M fld rest resolved hp ihRest hhs ihh ihhs =>
    exact .inl (ihRest (λ ee' hee' y hy hyx ↦
      ihh ee' (List.mem_cons_of_mem _ hee') y hy hyx) ihhs)
  | @inr M ee vv rest resolved hev hrest ihHead hh hhs ihh ihhs =>
    exact .inr (ihHead (λ y hy hyx ↦ ihh ee List.mem_cons_self y hy hyx) ihhs)
      (hh (λ ee' hee' y hy hyx ↦ ihh ee' (List.mem_cons_of_mem _ hee') y hy hyx) ihhs)
  | _ => exact .nil

/-- The `e = .var τ₀ o₀` arm of `evalSubst'_bwd`'s per-constructor `cases e`, when the derived
constructor `ê` is not itself a `.var`: only `o₀ = .free x` is possible (the substitution splices
`e'` in outright), closed by determinism against `hev'`. -/
private theorem bwdVar {Ξ : OperatorEnv} {Ω : Model Value} {x : String} {e' : Expression Typ}
    {v' : Value} (hlc : e'.LC) {N N' : Memory Value} {τ₀ : Typ} {o₀ : Origin}
    {ê : Expression Typ} {v : Value} (hcur : Eval Ξ Ω N ê v)
    (hsub : Expression.subst x e' (.var τ₀ o₀) = ê)
    (hN'x : N'.lookup x = some v') (hev' : Eval Ξ Ω N e' v')
    (hnotvar : ∀ τ o, ê ≠ .var τ o) :
    Eval Ξ Ω N' (.var τ₀ o₀) v := by
  cases o₀ with
  | free n =>
    by_cases hn : n = x
    · subst hn
      rw [Expression.LC.subst_var_free_eq hlc] at hsub
      have hvv : v = v' := evalUnique' hcur (hsub ▸ hev')
      subst hvv
      exact .var_free hN'x
    · rw [Expression.subst_var_free_ne hn] at hsub
      absurd hsub.symm
      exact hnotvar _ _
  | «module» m nm =>
    rw [Expression.subst_var_module] at hsub
    absurd hsub.symm
    exact hnotvar _ _
  | bound i =>
    rw [Expression.subst_var_bound] at hsub
    absurd hsub.symm
    exact hnotvar _ _
  | intrinsic nm =>
    rw [Expression.subst_var_intrinsic] at hsub
    absurd hsub.symm
    exact hnotvar _ _

private theorem evalSubst'_bwd {Ξ : OperatorEnv} {Ω : Model Value} {x : String}
    {e' : Expression Typ} {v' : Value} (hΞ : Ξ.WellScoped) (hlc : e'.LC) :
    ∀ {N : Memory Value} {ê : Expression Typ} {v : Value}, Eval Ξ Ω N ê v →
      ∀ {e : Expression Typ} {N' : Memory Value}, Expression.subst x e' e = ê →
        (∀ y ∈ e.freeVars, y ≠ x → N.lookup y = N'.lookup y) →
        N'.lookup x = some v' →
        Eval Ξ Ω N e' v' →
        Eval Ξ Ω N' e v := by
  have agreeStep : ∀ {N₁ N₂ : Memory Value} {z : String} {w : Value} {D B : Expression Typ},
      (∀ y ∈ D.freeVars ∪ B.freeVars, y ≠ x → N₁.lookup y = N₂.lookup y) →
      ∀ y ∈ (B.openVar z).freeVars, y ≠ x →
        (N₁.insert z w).lookup y = (N₂.insert z w).lookup y := by
    intro N₁ N₂ z w D B hag y hy hyx
    by_cases hyz : y = z
    · subst hyz; rw [Finmap.lookup_insert, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hyz, Finmap.lookup_insert_of_ne _ hyz]
      exact hag y (Finset.mem_union_right _
        (Expression.freeVars_openVar_erase (Finset.mem_erase.mpr ⟨hyz, hy⟩))) hyx
  have evStep : ∀ {N₁ : Memory Value} {z : String} {w u : Value},
      z ∉ e'.freeVars → Eval Ξ Ω N₁ e' u → Eval Ξ Ω (N₁.insert z w) e' u := by
    intro N₁ z w u hze he
    exact (evalLocal' hΞ λ y hy ↦
      (Finmap.lookup_insert_of_ne N₁ (λ h : y = z ↦ hze (h ▸ hy))).symm).mp he
  have xStep : ∀ {N₁ : Memory Value} {z : String} {w : Value},
      z ≠ x → N₁.lookup x = some v' → (N₁.insert z w).lookup x = some v' := by
    intro N₁ z w hzx hN'x; rw [Finmap.lookup_insert_of_ne _ (Ne.symm hzx)]; exact hN'x
  have freshParts : ∀ {z : String} {L : Finset String}, z ∉ L ∪ e'.freeVars ∪ {x} →
      z ∉ L ∧ z ∉ e'.freeVars ∧ z ≠ x := by
    intro z L hz
    obtain ⟨hzLe, hzx⟩ := Finset.notMem_union.mp hz
    obtain ⟨hzL, hze⟩ := Finset.notMem_union.mp hzLe
    exact ⟨hzL, hze, Finset.notMem_singleton.mp hzx⟩
  intro N ê v hev
  induction hev using Eval.rec
    (motive_2 := λ N es vs _ ↦ ∀ {es₀ : List (Expression Typ)} {N' : Memory Value},
      es₀.map (Expression.subst x e') = es →
      (∀ e ∈ es₀, ∀ y ∈ e.freeVars, y ≠ x → N.lookup y = N'.lookup y) →
      N'.lookup x = some v' → Eval Ξ Ω N e' v' → EvalList Ξ Ω N' es₀ vs)
    (motive_3 := λ N p rs _ ↦ ∀ {p₀ : List (String ⊕ Expression Typ)} {N' : Memory Value},
      (p₀.map λ s ↦ s.map id (Expression.subst x e')) = p →
      (∀ e, Sum.inr e ∈ p₀ → ∀ y ∈ e.freeVars, y ≠ x → N.lookup y = N'.lookup y) →
      N'.lookup x = some v' → Eval Ξ Ω N e' v' → EvalPath Ξ Ω N' p₀ rs) with
  -- literals
  | nat hn =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | nat s' =>
      rw [Expression.subst_nat] at hsub
      obtain rfl := Expression.nat.inj hsub
      exact .nat hn
    | var τ₀ o₀ => exact bwdVar hlc (.nat hn) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | str =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | str s' => rw [Expression.subst_str] at hsub; obtain rfl := Expression.str.inj hsub; exact .str
    | var τ₀ o₀ => exact bwdVar hlc .str hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | tru =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | true => rw [show Expression.subst x e' (Expression.true) = Expression.true from Expression.subst_true] at hsub; exact .tru
    | var τ₀ o₀ => exact bwdVar hlc .tru hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | fls =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | false => rw [show Expression.subst x e' (Expression.false) = Expression.false from Expression.subst_false] at hsub; exact .fls
    | var τ₀ o₀ => exact bwdVar hlc .fls hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  -- variables
  | @var_free _ _ name val hb =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | var τ₀ o₀ =>
      cases o₀ with
      | free n =>
        by_cases hn : n = x
        · subst hn
          rw [Expression.LC.subst_var_free_eq hlc] at hsub
          have hvv : val = v' := evalUnique' (.var_free hb) (hsub ▸ hev')
          subst hvv
          exact .var_free hN'x
        · rw [Expression.subst_var_free_ne hn] at hsub
          injection hsub with hτ ho; subst hτ; injection ho with hnm; subst hnm
          refine .var_free ?_
          rw [← hag n (by rw [Expression.freeVars]; exact Finset.mem_singleton.mpr rfl) hn]
          exact hb
      | «module» m nm => rw [Expression.subst_var_module] at hsub; simp at hsub
      | bound i => rw [Expression.subst_var_bound] at hsub; simp at hsub
      | intrinsic nm => rw [Expression.subst_var_intrinsic] at hsub; simp at hsub
    | _ => subst_ctor_mismatch hsub
  | @var_op0 _ _ m name bodyv val hΞ' hnb' hbody ihbody =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | var τ₀ o₀ =>
      cases o₀ with
      | free n =>
        by_cases hn : n = x
        · subst hn
          rw [Expression.LC.subst_var_free_eq hlc] at hsub
          have hvv : val = v' := evalUnique' (.var_op0 hΞ' hnb' hbody) (hsub ▸ hev')
          subst hvv
          exact .var_free hN'x
        · rw [Expression.subst_var_free_ne hn] at hsub
          simp at hsub
      | «module» m₀ nm₀ =>
        rw [Expression.subst_var_module] at hsub
        injection hsub with hτv hom; subst hτv; injection hom with hm hn; subst m₀; subst nm₀
        have hcl : bodyv.freeVars = ∅ := hΞ m name [] bodyv hΞ'
        refine .var_op0 hΞ' hnb' ?_
        exact ihbody (Expression.subst_fresh bodyv (by rw [hcl]; exact Finset.notMem_empty x))
          (λ y hy _ ↦ absurd hy (by rw [hcl]; exact Finset.notMem_empty y)) hN'x hev'
      | bound i => rw [Expression.subst_var_bound] at hsub; simp at hsub
      | intrinsic nm => rw [Expression.subst_var_intrinsic] at hsub; simp at hsub
    | _ => subst_ctor_mismatch hsub
  | @var_const _ _ m name val hΞ' hnb' hΩ' =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | var τ₀ o₀ =>
      cases o₀ with
      | free n =>
        by_cases hn : n = x
        · subst hn
          rw [Expression.LC.subst_var_free_eq hlc] at hsub
          have hvv : val = v' := evalUnique' (.var_const hΞ' hnb' hΩ') (hsub ▸ hev')
          subst hvv
          exact .var_free hN'x
        · rw [Expression.subst_var_free_ne hn] at hsub
          simp at hsub
      | «module» m₀ nm₀ =>
        rw [Expression.subst_var_module] at hsub
        injection hsub with hτv hom; subst hτv; injection hom with hm hn; subst m₀; subst nm₀
        exact .var_const hΞ' hnb' hΩ'
      | bound i => rw [Expression.subst_var_bound] at hsub; simp at hsub
      | intrinsic nm => rw [Expression.subst_var_intrinsic] at hsub; simp at hsub
    | _ => subst_ctor_mismatch hsub
  | @natSet _ _ val hv =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | var τ₀ o₀ =>
      cases o₀ with
      | free n =>
        by_cases hn : n = x
        · subst hn
          rw [Expression.LC.subst_var_free_eq hlc] at hsub
          have hvv : val = v' := evalUnique' (.natSet hv) (hsub ▸ hev')
          subst hvv
          exact .var_free hN'x
        · rw [Expression.subst_var_free_ne hn] at hsub
          simp at hsub
      | «module» m₀ nm₀ =>
        rw [Expression.subst_var_module] at hsub
        injection hsub with hτv hom; subst hτv; injection hom with hm hn; subst m₀; subst nm₀
        exact .natSet hv
      | bound i => rw [Expression.subst_var_bound] at hsub; simp at hsub
      | intrinsic nm => rw [Expression.subst_var_intrinsic] at hsub; simp at hsub
    | _ => subst_ctor_mismatch hsub
  | @intSet _ _ val hv =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | var τ₀ o₀ =>
      cases o₀ with
      | free n =>
        by_cases hn : n = x
        · subst hn
          rw [Expression.LC.subst_var_free_eq hlc] at hsub
          have hvv : val = v' := evalUnique' (.intSet hv) (hsub ▸ hev')
          subst hvv
          exact .var_free hN'x
        · rw [Expression.subst_var_free_ne hn] at hsub
          simp at hsub
      | «module» m₀ nm₀ =>
        rw [Expression.subst_var_module] at hsub
        injection hsub with hτv hom; subst hτv; injection hom with hm hn; subst m₀; subst nm₀
        exact .intSet hv
      | bound i => rw [Expression.subst_var_bound] at hsub; simp at hsub
      | intrinsic nm => rw [Expression.subst_var_intrinsic] at hsub; simp at hsub
    | _ => subst_ctor_mismatch hsub
  -- operator / builtin call
  | @opCall_op _ _ m name params bodyv _ _ hΞ' hnb' hlen hbody hargs ihbody =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | opCall f₀ args₀ =>
      rw [Expression.subst_opCall] at hsub
      injection hsub with hf ha
      cases f₀ with
      | var τ₁ o₁ =>
        cases o₁ with
        | «module» m₁ n₁ =>
          rw [Expression.subst_var_module] at hf
          injection hf with _ hom; injection hom with hm hn; subst m₁; subst n₁
          have hcl : bodyv.freeVars = ∅ := hΞ m name params bodyv hΞ'
          have hfr : x ∉ bodyv.freeVars := by rw [hcl]; exact Finset.notMem_empty x
          subst ha
          refine .opCall_op hΞ' hnb' (by rw [List.length_map] at hlen; exact hlen) ?_
            (λ h ↦ hargs (by rw [h, List.map_nil]))
          refine ihbody (subst_substParams hlc hfr) (λ y hy hyx ↦ ?_) hN'x hev'
          rcases substParams_freeVars (by rw [List.length_map] at hlen; exact hlen) hy with h | ⟨a, hain, hya⟩
          · exact ((by rw [hcl]; exact Finset.notMem_empty y : y ∉ bodyv.freeVars) h).elim
          · exact hag y (Expression.mem_freeVars_opCall.mpr (.inr ⟨a, hain, hya⟩)) hyx
        | free n₁ =>
          by_cases hn : n₁ = x
          · subst hn
            rw [Expression.LC.subst_var_free_eq hlc] at hf
            rw [hf] at hev'
            exfalso
            cases hev' with
            | var_op0 hΞ2 _ _ =>
              rw [hΞ'] at hΞ2
              injection hΞ2 with hpb; injection hpb with hp _; subst hp
              simp only [List.length_nil] at hlen
              exact hargs (List.eq_nil_of_length_eq_zero hlen.symm)
            | var_const hΞ2 _ _ => rw [hΞ'] at hΞ2; contradiction
            | natSet _ => simp [TypedTLAPlus.builtinOpOf?] at hnb'
            | intSet _ => simp [TypedTLAPlus.builtinOpOf?] at hnb'
          · rw [Expression.subst_var_free_ne hn] at hf
            injection hf with _ ho; simp at ho
        | bound i =>
          rw [Expression.subst_var_bound] at hf; injection hf with _ ho; simp at ho
        | intrinsic n₁ =>
          rw [Expression.subst_var_intrinsic] at hf; injection hf with _ ho; simp at ho
      | _ => subst_ctor_mismatch hf
    | var τ₀ o₀ => exact bwdVar hlc (.opCall_op hΞ' hnb' hlen hbody hargs) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | opCall_builtin hop hargsL hb ihargs =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | opCall f₀ args₀ =>
      rw [Expression.subst_opCall] at hsub
      injection hsub with hf ha
      cases f₀ with
      | var τ₁ o₁ =>
        cases o₁ with
        | «module» m₁ n₁ =>
          rw [Expression.subst_var_module] at hf
          injection hf with hτ ho; subst hτ; subst ho; subst ha
          exact .opCall_builtin hop
            (ihargs rfl (λ a hain y hy hyx ↦
              hag y (Expression.mem_freeVars_opCall.mpr (.inr ⟨a, hain, hy⟩)) hyx) hN'x hev') hb
        | intrinsic n₁ =>
          rw [Expression.subst_var_intrinsic] at hf
          injection hf with hτ ho; subst hτ; subst ho; subst ha
          exact .opCall_builtin hop
            (ihargs rfl (λ a hain y hy hyx ↦
              hag y (Expression.mem_freeVars_opCall.mpr (.inr ⟨a, hain, hy⟩)) hyx) hN'x hev') hb
        | free n₁ =>
          by_cases hn : n₁ = x
          · subst hn
            rw [Expression.LC.subst_var_free_eq hlc] at hf
            rw [hf] at hev'
            exfalso
            cases hev' with
            | var_free hb' => simp [TypedTLAPlus.builtinOpOf?] at hop
            | var_op0 _ hnb2 _ => rw [hop] at hnb2; contradiction
            | var_const _ hnb2 _ => rw [hop] at hnb2; contradiction
            | natSet _ =>
              simp only [TypedTLAPlus.builtinOpOf?, Option.some.injEq] at hop; subst hop; nomatch hb
            | intSet _ =>
              simp only [TypedTLAPlus.builtinOpOf?, Option.some.injEq] at hop; subst hop; nomatch hb
          · rw [Expression.subst_var_free_ne hn] at hf
            injection hf with _ ho; subst ho
            simp [TypedTLAPlus.builtinOpOf?] at hop
        | bound i =>
          rw [Expression.subst_var_bound] at hf
          injection hf with _ ho; subst ho
          simp [TypedTLAPlus.builtinOpOf?] at hop
      | _ => subst_ctor_mismatch hf
    | var τ₀ o₀ => exact bwdVar hlc (.opCall_builtin hop hargsL hb) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  -- bounded quantifiers
  | forall_true L hdom hall ihdom ihall =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «forall» x'' τ'' D₀ B₀ =>
      rw [Expression.LC.subst_forall hlc] at hsub
      injection hsub with _ hτ hD hB; subst hτ
      rw [Expression.freeVars] at hag
      refine .forall_true (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') ?_
      intro z hz w hw
      obtain ⟨hzL, hze, hzx⟩ := freshParts hz
      refine ihall z hzL w hw ?_ (agreeStep hag) (xStep hzx hN'x) (evStep hze hev')
      rw [← Expression.LC.subst_openVar hlc hzx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.forall_true L hdom hall) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | forall_false L hdom hw hbody ihdom ihbody =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «forall» x'' τ'' D₀ B₀ =>
      rw [Expression.LC.subst_forall hlc] at hsub
      injection hsub with _ hτ hD hB; subst hτ
      rw [Expression.freeVars] at hag
      refine .forall_false (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') hw ?_
      intro z hz
      obtain ⟨hzL, hze, hzx⟩ := freshParts hz
      refine ihbody z hzL ?_ (agreeStep hag) (xStep hzx hN'x) (evStep hze hev')
      rw [← Expression.LC.subst_openVar hlc hzx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.forall_false L hdom hw hbody) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | exists_true L hdom hw hbody ihdom ihbody =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «exists» x'' τ'' D₀ B₀ =>
      rw [Expression.LC.subst_exists hlc] at hsub
      injection hsub with _ hτ hD hB; subst hτ
      rw [Expression.freeVars] at hag
      refine .exists_true (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') hw ?_
      intro z hz
      obtain ⟨hzL, hze, hzx⟩ := freshParts hz
      refine ihbody z hzL ?_ (agreeStep hag) (xStep hzx hN'x) (evStep hze hev')
      rw [← Expression.LC.subst_openVar hlc hzx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.exists_true L hdom hw hbody) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | exists_false L hdom hall ihdom ihall =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «exists» x'' τ'' D₀ B₀ =>
      rw [Expression.LC.subst_exists hlc] at hsub
      injection hsub with _ hτ hD hB; subst hτ
      rw [Expression.freeVars] at hag
      refine .exists_false (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') ?_
      intro z hz w hw
      obtain ⟨hzL, hze, hzx⟩ := freshParts hz
      refine ihall z hzL w hw ?_ (agreeStep hag) (xStep hzx hN'x) (evStep hze hev')
      rw [← Expression.LC.subst_openVar hlc hzx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.exists_false L hdom hall) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | choose filt L hdom hfilt ihdom ihfilt =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «choose» x'' τ'' D₀ B₀ =>
      rw [Expression.LC.subst_choose hlc] at hsub
      injection hsub with _ hτ hD hB; subst hτ
      rw [Expression.freeVars] at hag
      refine .choose filt (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') ?_
      intro z hz w hw
      obtain ⟨hzL, hze, hzx⟩ := freshParts hz
      refine ihfilt z hzL w hw ?_ (agreeStep hag) (xStep hzx hN'x) (evStep hze hev')
      rw [← Expression.LC.subst_openVar hlc hzx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.choose filt L hdom hfilt) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  -- set literal
  | set hes hto hof ihes =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | set es₀ τ₀ =>
      rw [Expression.subst_set] at hsub
      injection hsub with hesq hτ; subst hτ
      exact .set (ihes hesq (λ a ha y hy hyx ↦
        hag y (Expression.mem_freeVars_set.mpr ⟨a, ha, hy⟩) hyx) hN'x hev') hto hof
    | var τ₀ o₀ => exact bwdVar hlc (.set hes hto hof) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | collect filt L hdom hfilt hto hof ihdom ihfilt =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | collect x'' τ'' D₀ B₀ =>
      rw [Expression.LC.subst_collect hlc] at hsub
      injection hsub with _ hτ hD hB; subst hτ
      rw [Expression.freeVars] at hag
      refine .collect filt (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') ?_ hto hof
      intro y hy z hz
      obtain ⟨hyL, hye, hyx⟩ := freshParts hy
      refine ihfilt y hyL z hz ?_ (agreeStep hag) (xStep hyx hN'x) (evStep hye hev')
      rw [← Expression.LC.subst_openVar hlc hyx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.collect filt L hdom hfilt hto hof) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | map' img L hdom himg hto hof ihdom ihimg =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | map' B₀ x'' ann'' cod'' D₀ =>
      rw [Expression.LC.subst_map' hlc] at hsub
      injection hsub with hB _ _ hcod hD
      rw [Expression.freeVars] at hag
      refine .map' img (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') ?_ hto hof
      intro z hz w hw
      obtain ⟨hzL, hze, hzx⟩ := freshParts hz
      refine ihimg z hzL w hw ?_ (agreeStep hag) (xStep hzx hN'x) (evStep hze hev')
      rw [← Expression.LC.subst_openVar hlc hzx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.map' img L hdom himg hto hof) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | fnCall hf hk hdom ihf ihk =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | fnCall f₀ fnTyp₀ k₀ =>
      rw [Expression.subst_fnCall] at hsub
      injection hsub with hfe hfnty hk₀; subst hfnty
      rw [Expression.freeVars] at hag
      exact .fnCall
        (ihf hfe (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev')
        (ihk hk₀ (λ y hy hyx ↦ hag y (Finset.mem_union_right _ hy) hyx) hN'x hev') hdom
    | var τ₀ o₀ => exact bwdVar hlc (.fnCall hf hk hdom) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | fn img L hdom himg hto hof ihdom ihimg =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | fn x'' ann'' cod'' D₀ B₀ =>
      rw [Expression.LC.subst_fn hlc] at hsub
      injection hsub with _ _ hcod hD hB
      rw [Expression.freeVars] at hag
      refine .fn img (L ∪ e'.freeVars ∪ {x})
        (ihdom hD (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev') ?_ hto hof
      intro z hz w hw
      obtain ⟨hzL, hze, hzx⟩ := freshParts hz
      refine ihimg z hzL w hw ?_ (agreeStep hag) (xStep hzx hN'x) (evStep hze hev')
      rw [← Expression.LC.subst_openVar hlc hzx, hB]
    | var τ₀ o₀ => exact bwdVar hlc (.fn img L hdom himg hto hof) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | record hfne hfs ihfs =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | record fs₀ =>
      rw [Expression.subst_record] at hsub
      injection hsub with hfsq
      subst hfsq
      have hnames : List.map (λ p : Typ × String × Expression Typ ↦ p.2.1)
            (List.map (λ p ↦ (p.1, p.2.1, Expression.subst x e' p.2.2)) fs₀)
          = List.map (·.2.1) fs₀ := by simp [List.map_map, Function.comp_def]
      rw [hnames]
      refine .record (λ h ↦ hfne (by rw [h, List.map_nil])) ?_
      have key := ihfs (es₀ := fs₀.map (·.2.2))
        (by simp [List.map_map, Function.comp_def])
        (λ a ha y hy hyx ↦ by
          obtain ⟨f, hfin, rfl⟩ := List.mem_map.mp ha
          exact hag y (Expression.mem_freeVars_record.mpr ⟨f, hfin, hy⟩) hyx) hN'x hev'
      simpa [List.map_map, Function.comp_def] using key
    | var τ₀ o₀ => exact bwdVar hlc (.record hfne hfs) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | recordAccess he hdom ihe =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | recordAccess e₀ nm₀ =>
      rw [Expression.subst_recordAccess] at hsub
      injection hsub with hee hnm; subst hnm
      rw [Expression.freeVars] at hag
      exact .recordAccess (ihe hee hag hN'x hev') hdom
    | var τ₀ o₀ => exact bwdVar hlc (.recordAccess he hdom) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | tuple hets hes ihes =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | tuple ets₀ =>
      rw [Expression.subst_tuple] at hsub
      injection hsub with hetsq
      subst hetsq
      refine .tuple (λ h ↦ hets (by rw [h, List.map_nil])) ?_
      have key := ihes (es₀ := ets₀.map (·.2))
        (by simp [List.map_map, Function.comp_def])
        (λ a ha y hy hyx ↦ by
          obtain ⟨p, hpin, rfl⟩ := List.mem_map.mp ha
          exact hag y (Expression.mem_freeVars_tuple.mpr ⟨p, hpin, hy⟩) hyx) hN'x hev'
      simpa [List.map_map, Function.comp_def] using key
    | var τ₀ o₀ => exact bwdVar hlc (.tuple hets hes) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | seq hes ihes =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | seq es₀ τ₀ =>
      rw [Expression.subst_seq] at hsub
      injection hsub with hesq hτ; subst hτ
      exact .seq (ihes hesq (λ a ha y hy hyx ↦
        hag y (Expression.mem_freeVars_seq.mpr ⟨a, ha, hy⟩) hyx) hN'x hev')
    | var τ₀ o₀ => exact bwdVar hlc (.seq hes) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | «except» hf hpath hrhs hv ihf ihpath ihrhs =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «except» f₀ τ₀ upds₀ =>
      cases upds₀ with
      | cons pu rest =>
        cases rest with
        | cons _ _ =>
          rewrite [Expression.subst_eq_mapVars] at hsub
          simp only [Expression.mapVars, registerSource] at hsub
          injection hsub with _ _ hupds
          simp at hupds
        | nil =>
          obtain ⟨path₀, rhs₀⟩ := pu
          rw [Expression.subst_except_single] at hsub
          injection hsub with hfe hτ hupds; subst hτ
          injection hupds with hpu _
          injection hpu with hpath₀ hrhs₀
          simp only [Expression.mem_freeVars_except_single] at hag
          refine .«except»
            (ihf hfe (λ y hy hyx ↦ hag y (.inl hy) hyx) hN'x hev') ?_
            (ihrhs hrhs₀ (λ y hy hyx ↦ hag y (.inr (.inr hy)) hyx) hN'x hev') hv
          exact ihpath hpath₀
            (λ ee hein y hy hyx ↦ hag y (.inr (.inl ⟨ee, hein, hy⟩)) hyx) hN'x hev'
      | nil =>
        rewrite [Expression.subst_eq_mapVars] at hsub
        simp only [Expression.mapVars, registerSource] at hsub
        injection hsub with _ _ hupds
        simp at hupds
    | var τ₀ o₀ => exact bwdVar hlc (.«except» hf hpath hrhs hv) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | if_true hc ht ihc iht =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «if» c₀ t₀ e₀ τ₀ =>
      rw [Expression.subst_if] at hsub
      injection hsub with hc₀ ht₀ he₀ hτ; subst hτ
      rw [Expression.freeVars, Finset.union_assoc] at hag
      exact .if_true (ihc hc₀ (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev')
        (iht ht₀ (λ y hy hyx ↦ hag y (Finset.mem_union_right _ (Finset.mem_union_left _ hy)) hyx)
          hN'x hev')
    | var τ₀ o₀ => exact bwdVar hlc (.if_true hc ht) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | if_false hc he ihc ihe =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «if» c₀ t₀ e₀ τ₀ =>
      rw [Expression.subst_if] at hsub
      injection hsub with hc₀ ht₀ he₀ hτ; subst hτ
      rw [Expression.freeVars, Finset.union_assoc] at hag
      exact .if_false (ihc hc₀ (λ y hy hyx ↦ hag y (Finset.mem_union_left _ hy) hyx) hN'x hev')
        (ihe he₀ (λ y hy hyx ↦ hag y (Finset.mem_union_right _ (Finset.mem_union_right _ hy)) hyx)
          hN'x hev')
    | var τ₀ o₀ => exact bwdVar hlc (.if_false hc he) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | @case_hit _ bs _ _ i _ _ _ hi hbefore hp hq ihbefore ihp ihq =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «case» bs₀ other₀ τ₀ =>
      rw [Expression.subst_case] at hsub
      injection hsub with hbsq hotherq hτ; subst hτ
      obtain ⟨⟨pp₀, qq₀⟩, hi₀, heqi⟩ :=
        Option.map_eq_some_iff.mp (by rw [← hbsq, List.getElem?_map] at hi; exact hi)
      simp only [Prod.mk.injEq] at heqi; obtain ⟨rfl, rfl⟩ := heqi
      refine .case_hit (i := i) hi₀ (λ j hj p' q' hjeq ↦ ?_) ?_ ?_
      · have hbj : bs[j]? = some (Expression.subst x e' p', Expression.subst x e' q') := by
          rw [← hbsq, List.getElem?_map, hjeq]; rfl
        exact ihbefore j hj _ _ hbj rfl
          (λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr
            (.inl ⟨(p', q'), List.mem_of_getElem? hjeq, .inl hy⟩)) hyx) hN'x hev'
      · exact ihp rfl (λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr
          (.inl ⟨(pp₀, qq₀), List.mem_of_getElem? hi₀, .inl hy⟩)) hyx) hN'x hev'
      · exact ihq rfl (λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr
          (.inl ⟨(pp₀, qq₀), List.mem_of_getElem? hi₀, .inr hy⟩)) hyx) hN'x hev'
    | var τ₀ o₀ => exact bwdVar hlc (.case_hit hi hbefore hp hq) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  | @case_other _ bs _ _ _ hbefore hq ihbefore ihq =>
    intro e N' hsub hag hN'x hev'
    cases e with
    | «case» bs₀ other₀ τ₀ =>
      cases other₀ with
      | none => rw [Expression.subst_case] at hsub; injection hsub with _ ho _; simp at ho
      | some ee₀ =>
        rw [Expression.subst_case] at hsub
        injection hsub with hbsq hotherq hτ; subst hτ
        rw [Option.map_some, Option.some.injEq] at hotherq
        refine .case_other (λ j p' q' hjeq ↦ ?_) (ihq hotherq ?_ hN'x hev')
        · have hbj : bs[j]? = some (Expression.subst x e' p', Expression.subst x e' q') := by
            rw [← hbsq, List.getElem?_map, hjeq]; rfl
          exact ihbefore j _ _ hbj rfl
            (λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr
              (.inl ⟨(p', q'), List.mem_of_getElem? hjeq, .inl hy⟩)) hyx) hN'x hev'
        · exact λ y hy hyx ↦ hag y (Expression.mem_freeVars_case.mpr (.inr ⟨_, rfl, hy⟩)) hyx
    | var τ₀ o₀ => exact bwdVar hlc (.case_other hbefore hq) hsub hN'x hev' (by simp)
    | _ => subst_ctor_mismatch hsub
  -- EvalList / EvalPath companions
  | nil hsub _ _ _ =>
    obtain rfl := List.map_eq_nil_iff.mp hsub
    exact .nil
  | cons _ _ ihHead ihTail hmap hag hN'x hev' =>
    obtain ⟨a, rest, rfl, ha, hrest⟩ := List.map_eq_cons_iff.mp hmap
    exact .cons (ihHead ha (λ y hy hyx ↦ hag a List.mem_cons_self y hy hyx) hN'x hev')
      (ihTail hrest (λ b hb y hy hyx ↦ hag b (List.mem_cons_of_mem _ hb) y hy hyx) hN'x hev')
  | inl _ ih hmap hag hN'x hev' =>
    obtain ⟨s, rest₀, rfl, hh, hrest⟩ := List.map_eq_cons_iff.mp hmap
    cases s with
    | inl fld₀ =>
      simp only [Sum.map_inl, id_eq] at hh
      injection hh with hfld; subst hfld
      exact .inl (ih hrest (λ ee hein y hy hyx ↦
        hag ee (List.mem_cons_of_mem _ hein) y hy hyx) hN'x hev')
    | inr e₀ => simp only [Sum.map_inr, reduceCtorEq] at hh
  | inr _ _ ihHead ihTail hmap hag hN'x hev' =>
    obtain ⟨s, rest₀, rfl, hh, hrest⟩ := List.map_eq_cons_iff.mp hmap
    cases s with
    | inl fld₀ => simp only [Sum.map_inl, reduceCtorEq] at hh
    | inr e₀ =>
      rw [Sum.map_inr] at hh
      injection hh with he₀
      exact .inr (ihHead he₀ (λ y hy hyx ↦ hag e₀ List.mem_cons_self y hy hyx) hN'x hev')
        (ihTail hrest (λ ee hein y hy hyx ↦
          hag ee (List.mem_cons_of_mem _ hein) y hy hyx) hN'x hev')
  | _ =>
    obtain rfl := List.map_eq_nil_iff.mp ‹List.map _ _ = []›
    exact .nil

/-- Substitution is evaluation-under-extended-memory read backwards. `.mp` (forward) is
`evalSubst'_fwd`; `.mpr` (backward) is `evalSubst'_bwd`. Both need `Ξ.WellScoped` (operator bodies
are `freeVars`-closed) and `e'.LC` (the spliced expression has no dangling de Bruijn index, so it
survives being lifted under `e`'s binders). -/
theorem evalSubst' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value} {x : String}
    {e' e : Expression Typ} {v' v : Value} (hΞ : Ξ.WellScoped) (hlc : e'.LC)
    (he' : Eval Ξ Ω M e' v') :
    Eval Ξ Ω (M.insert x v') e v ↔ Eval Ξ Ω M (Expression.subst x e' e) v := by
  iff_intro h h
  · refine evalSubst'_fwd hΞ hlc h (λ y _ hy ↦ Finmap.lookup_insert_of_ne _ hy) ?_
    intro w hw
    rw [Finmap.lookup_insert] at hw
    obtain rfl := Option.some.inj hw
    exact he'
  · refine evalSubst'_bwd hΞ hlc h rfl (λ y hy hyx ↦ (Finmap.lookup_insert_of_ne _ hyx).symm) ?_ he'
    rw [Finmap.lookup_insert]


/-- `ResolvesPath`, stated against the abstract `Eval` parameter, unfolds to `EvalPath`, the mutual
companion `Eval`'s `except` constructor is stated with. The two inductives are the same shape; this
is the only place the interface-level path relation meets the concrete one. -/
theorem resolvesPath_evalPath {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {path : List (String ⊕ Expression Typ)} {resolved : List (PathStep Value)}
    (h : ResolvesPath (Eval Ξ Ω) M path resolved) : EvalPath Ξ Ω M path resolved := by
  induction h with
  | nil => exact .nil
  | inl _ ih => exact .inl ih
  | inr hv _ ih => exact .inr hv ih

theorem evalExcept' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {f rhs : Expression Typ} {τ : Typ} {path : List (String ⊕ Expression Typ)}
    {vf vr v : Value} {resolved : List (PathStep Value)}
    (hf : Eval Ξ Ω M f vf) (hpath : ResolvesPath (Eval Ξ Ω) M path resolved)
    (hrhs : Eval Ξ Ω M rhs vr) :
    Eval Ξ Ω M (.except f τ [(path, rhs)]) v ↔ updatePath vf resolved vr = some v := by
  iff_intro hev hup
  · cases hev with
    | «except» hf' hpath' hrhs' hv' =>
      obtain rfl := evalUnique' hf hf'
      obtain rfl := evalPathUnique' (resolvesPath_evalPath hpath) hpath'
      obtain rfl := evalUnique' hrhs hrhs'
      exact hv'
  · exact .«except» hf (resolvesPath_evalPath hpath) hrhs hup

/-- The concrete TLA⁺ expression evaluator over `Value := ZFSet`. -/
noncomputable instance : ExprSemantics Value where
  Eval := Eval
  tru := Value.tru
  isBool := IsBool
  isSet := IsSet
  mem a b := a ∈ b
  updatePath := updatePath
  updatePath_nil := updatePath_nil'
  seqAppend := seqAppend
  isSeq := IsSeq
  isSeq_inj := isSeq_inj'
  eval_seq_nil := eval_seq_nil'
  seqAppend_isSeq := seqAppend_isSeq'
  isSeq_tail := isSeq_tail'
  coerce := coerce
  evalUnique := evalUnique'
  evalVar := evalVar'
  evalCoerce := λ hΞ _ ↦ evalCoerce' hΞ
  evalLocal := evalLocal'
  evalSubst := evalSubst'
  evalExcept := evalExcept'

end Operational
end ComputableTLAPlus

end
