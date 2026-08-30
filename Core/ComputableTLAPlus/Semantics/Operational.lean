module

meta import CustomPrelude
import Std.Data.String.ToNat
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
  -- integer set families
  | natSet {v : Value} (hv : ∀ z, z ∈ v ↔ ∃ k : ℤ, 0 ≤ k ∧ z = Value.ofInt k) :
      -- TODO: Why not use `v := ZFSet.Nat`?
      EvalBuiltin .natSet [] v
  | intSet {v : Value} (hv : ∀ z, z ∈ v ↔ ∃ k : ℤ, z = Value.ofInt k) :
      -- TODO: Same as `natSet`, why not use `v := ZFSet.Int`?
      EvalBuiltin .intSet [] v
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
  -- TODO(locally-nameless): needs `Expression.freeVars_instantiate`, still to be added to
  -- `FreeVars.lean`, alongside the `evalLocal'`/`evalSubst'` rewrite.
  sorry

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
      {v : Value} (hΞ : Ξ m name = some ([], body)) (hb : Eval Ξ Ω M body v) :
      Eval Ξ Ω M (.var τ (.module m name)) v
  | var_const {M : Memory Value} {τ : Typ} {m name : String} {v : Value}
      (hΞ : Ξ m name = none) (hΩ : Ω m name = some v) :
      Eval Ξ Ω M (.var τ (.module m name)) v
  -- operator application: user operator, by substitution. `hnb` gates this rule to names the
  -- builtin table does not know: a builtin-module operator (`Naturals`'s `+`/`..`, `Sequences`'s
  -- `Len`, …) is resolved by `opCall_builtin` regardless of `Ξ`, so `Ξ` and `opCall_op` carry
  -- user-declared operators only.
  | opCall_op {M : Memory Value} {τ : Typ} {m name : String} {params : List (String × Nat)}
      {body : Expression Typ} {args : List (Expression Typ)} {v : Value}
      (hΞ : Ξ m name = some (params, body))
      (hnb : TypedTLAPlus.builtinOpOf? (.module m name) = none)
      (hlen : params.length = args.length)
      (hb : Eval Ξ Ω M (substParams params args body) v) :
      Eval Ξ Ω M (.opCall (.var τ (.module m name)) args) v
  -- operator application: builtin, by kind-strict value semantics. A builtin's meaning is fixed by
  -- its `Origin` here, not by `Ξ`; `opCall_op`'s `hnb` is the other half of that split.
  | opCall_builtin {M : Memory Value} {τ : Typ} {o : Origin} {op : BuiltinOp}
      {args : List (Expression Typ)} {argVals : List Value} {v : Value}
      (hop : TypedTLAPlus.builtinOpOf? o = some op)
      (hargs : EvalList Ξ Ω M args argVals)
      (hb : EvalBuiltin op argVals v) :
      Eval Ξ Ω M (.opCall (.var τ o) args) v
  -- bounded quantifiers. `body.openVar x` swaps the binder's own `.bound 0` for its name hint `x`,
  -- which `M.insert x w` then answers for; the hint choice is unobservable — α-equal bodies are
  -- syntactically equal under locally-nameless.
  | forall_true {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S : Value}
      (hdom : Eval Ξ Ω M dom S)
      (hall : ∀ w, w ∈ S → Eval Ξ Ω (M.insert x w) (body.openVar x) Value.tru) :
      Eval Ξ Ω M (.forall x τ dom body) Value.tru
  | forall_false {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S w : Value}
      (hdom : Eval Ξ Ω M dom S) (hw : w ∈ S)
      (hbody : Eval Ξ Ω (M.insert x w) (body.openVar x) Value.fls) :
      Eval Ξ Ω M (.forall x τ dom body) Value.fls
  | exists_true {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S w : Value}
      (hdom : Eval Ξ Ω M dom S) (hw : w ∈ S)
      (hbody : Eval Ξ Ω (M.insert x w) (body.openVar x) Value.tru) :
      Eval Ξ Ω M (.exists x τ dom body) Value.tru
  | exists_false {M : Memory Value} {x : String} {τ : Typ} {dom body : Expression Typ} {S : Value}
      (hdom : Eval Ξ Ω M dom S)
      (hall : ∀ w, w ∈ S → Eval Ξ Ω (M.insert x w) (body.openVar x) Value.fls) :
      Eval Ξ Ω M (.exists x τ dom body) Value.fls
  -- Hilbert choice. `filt w` is what `pred` denotes at `w`; the value is `Classical.epsilon` over
  -- "in `S`, filtered TRUE", which is deterministic and keeps `Eval` out of the `epsilon` predicate.
  | choose {M : Memory Value} {x : String} {τ : Typ} {dom pred : Expression Typ} {S : Value}
      (filt : Value → Value)
      (hdom : Eval Ξ Ω M dom S)
      (hfilt : ∀ w ∈ S, Eval Ξ Ω (M.insert x w) (pred.openVar x) (filt w)) :
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
      (filt : Value → Value)
      (hdom : Eval Ξ Ω M dom S)
      (hfilt : ∀ z ∈ S, Eval Ξ Ω (M.insert x z) (pred.openVar x) (filt z))
      (hto : ∀ z ∈ v, z ∈ S ∧ filt z = Value.tru)
      (hof : ∀ z ∈ S, filt z = Value.tru → z ∈ v) :
      Eval Ξ Ω M (.collect x τ dom pred) v
  -- set image. `img` names the mapped value at each point, keeping `Eval` out of an existential.
  | map' {M : Memory Value} {body : Expression Typ} {x : String} {ann cod : Typ}
      {dom : Expression Typ} {S v : Value} (img : Value → Value)
      (hdom : Eval Ξ Ω M dom S)
      (himg : ∀ w ∈ S, Eval Ξ Ω (M.insert x w) (body.openVar x) (img w))
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
      (img : Value → Value)
      (hdom : Eval Ξ Ω M dom S)
      (himg : ∀ w ∈ S, Eval Ξ Ω (M.insert x w) (body.openVar x) (img w))
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
        coerce cRng (fnApply v (Classical.epsilon fun k ↦ k ∈ D ∧ coerce cDom k w)) r') ∧
      ∀ z, z ∈ v' ↔ ∃ w ∈ Sd, ∃ r',
        coerce cRng (fnApply v (Classical.epsilon fun k ↦ k ∈ D ∧ coerce cDom k w)) r' ∧
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
        match Ξ m name with
        | some ([], body) => Eval Ξ Ω M body v
        | some (_ :: _, _) => False
        | none => Ω m name = some v := by
  constructor
  · intro h
    cases h with
    | var_free hb => exact hb
    | var_op0 hΞ hb => simp only [hΞ]; exact hb
    | var_const hΞ hΩ => simp only [hΞ]; exact hΩ
  · intro h
    cases o with
    | bound => exact h.elim
    | free name => exact .var_free h
    | intrinsic => exact h.elim
    | module m name =>
      simp only at h
      cases hΞ : Ξ m name with
      | none => rw [hΞ] at h; exact .var_const hΞ h
      | some pb =>
        obtain ⟨p, b⟩ := pb
        cases p with
        | nil => rw [hΞ] at h; exact .var_op0 hΞ h
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

/-- Evaluation is deterministic: an expression denotes at most one value. Proved through the mutual
recursor `Eval.rec` — `induction` does not fire on a member of a mutual inductive family, so the
`EvalList`/`EvalPath` determinism is threaded in as `motive_2`/`motive_3` and discharged in the same
pass. -/
theorem evalUnique' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {e : Expression Typ} {v w : Value} (h₁ : Eval Ξ Ω M e v) (h₂ : Eval Ξ Ω M e w) : v = w := by
  revert w
  induction h₁ using Eval.rec
    (motive_2 := λ M es vs _ ↦ ∀ ws, EvalList Ξ Ω M es ws → vs = ws)
    (motive_3 := λ M p rs _ ↦ ∀ rs', EvalPath Ξ Ω M p rs' → rs = rs')
  case nat hn =>
    intro w h₂; cases h₂ with
    | nat hn' => rw [hn] at hn'; exact congrArg Value.ofNat (Option.some.inj hn')
  case str => intro w h₂; cases h₂ with | str => rfl
  case tru => intro w h₂; cases h₂ with | tru => rfl
  case fls => intro w h₂; cases h₂ with | fls => rfl
  case var_free hb =>
    intro w h₂; cases h₂ with | var_free hb' => rw [hb] at hb'; exact Option.some.inj hb'
  case var_op0 hΞ hbdy ihbdy =>
    intro w h₂; cases h₂ with
    | var_op0 hΞ' hbdy' =>
      simp only [hΞ, Option.some.injEq, Prod.mk.injEq, true_and] at hΞ'
      subst hΞ'
      exact ihbdy hbdy'
    | var_const hΞ' hΩ' => rw [hΞ] at hΞ'; contradiction
  case var_const hΞ hΩ =>
    intro w h₂; cases h₂ with
    | var_op0 hΞ' hbdy' => rw [hΞ] at hΞ'; contradiction
    | var_const hΞ' hΩ' => rw [hΩ] at hΩ'; exact Option.some.inj hΩ'
  case opCall_op hΞ hnb hlen hbdy ihbdy =>
    intro w h₂; cases h₂ with
    | opCall_op hΞ' hnb' hlen' hbdy' =>
      simp only [hΞ, Option.some.injEq, Prod.mk.injEq] at hΞ'
      obtain ⟨rfl, rfl⟩ := hΞ'
      exact ihbdy hbdy'
    | opCall_builtin hop' hargs' hb' =>
      rw [hnb] at hop'
      contradiction
  case opCall_builtin hop hargs hb ihargs =>
    intro w h₂; cases h₂ with
    | opCall_op hΞ' hnb' hlen' hbdy' =>
      rw [hnb'] at hop
      contradiction
    | opCall_builtin hop' hargs' hb' =>
      rw [hop] at hop'
      obtain rfl := Option.some.inj hop'
      obtain rfl := ihargs _ hargs'
      exact evalBuiltinUnique hb hb'
  case forall_true hdom hall ihdom ihall =>
    intro w h₂; cases h₂ with
    | forall_true hdom' hall' => rfl
    | forall_false hdom' hw' hbody' =>
      obtain rfl := ihdom hdom'
      absurd (ihall _ hw' hbody')
      exact Value.tru_ne_fls
  case forall_false hdom hw hbody ihdom ihbody =>
    intro w h₂; cases h₂ with
    | forall_true hdom' hall' =>
      obtain rfl := ihdom hdom'
      absurd (ihbody (hall' _ hw))
      exact Value.fls_ne_tru
    | forall_false hdom' hw' hbody' => rfl
  case exists_true hdom hw hbody ihdom ihbody =>
    intro w h₂; cases h₂ with
    | exists_true hdom' hw' hbody' => rfl
    | exists_false hdom' hall' =>
      obtain rfl := ihdom hdom'
      absurd (ihbody (hall' _ hw))
      exact Value.tru_ne_fls
  case exists_false hdom hall ihdom ihall =>
    intro w h₂; cases h₂ with
    | exists_true hdom' hw' hbody' =>
      obtain rfl := ihdom hdom'
      absurd (ihall _ hw' hbody')
      exact Value.fls_ne_tru
    | exists_false hdom' hall' => rfl
  case choose filt hdom hfilt ihdom ihfilt =>
    intro w h₂; cases h₂ with
    | choose filt' hdom' hfilt' =>
      obtain rfl := ihdom hdom'
      refine congrArg Classical.epsilon (funext λ u ↦ propext (and_congr_right λ hu ↦ ?_))
      rw [ihfilt u hu (hfilt' u hu)]
  case set hes hto hof ihes =>
    intro w h₂; cases h₂ with
    | set hes' hto' hof' =>
      obtain rfl := ihes _ hes'
      exact ZFSet.ext λ z ↦ ⟨λ hz ↦ hof' z (hto z hz), λ hz ↦ hof z (hto' z hz)⟩
  case collect filt hdom hfilt hto hof ihdom ihfilt =>
    intro w h₂; cases h₂ with
    | collect filt' hdom' hfilt' hto' hof' =>
      obtain rfl := ihdom hdom'
      refine ZFSet.ext λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩
      · obtain ⟨hzS, hfz⟩ := hto z hz
        exact hof' z hzS ((ihfilt z hzS (hfilt' z hzS)).symm.trans hfz)
      · obtain ⟨hzS, hfz⟩ := hto' z hz
        exact hof z hzS ((ihfilt z hzS (hfilt' z hzS)).trans hfz)
  case map' img hdom himg hto hof ihdom ihimg =>
    intro w h₂; cases h₂ with
    | map' img' hdom' himg' hto' hof' =>
      obtain rfl := ihdom hdom'
      refine ZFSet.ext λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩
      · obtain ⟨u, huS, rfl⟩ := hto z hz
        rw [(ihimg u huS (himg' u huS) : img u = img' u)]
        exact hof' u huS
      · obtain ⟨u, huS, rfl⟩ := hto' z hz
        rw [← (ihimg u huS (himg' u huS) : img u = img' u)]
        exact hof u huS
  case fnCall hf hk hdom ihf ihk =>
    intro w h₂; cases h₂ with
    | fnCall hf' hk' _ => rw [(ihf hf' : _ = _), (ihk hk' : _ = _)]
  case fn img hdom himg hto hof ihdom ihimg =>
    intro w h₂; cases h₂ with
    | fn img' hdom' himg' hto' hof' =>
      obtain rfl := ihdom hdom'
      refine ZFSet.ext λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩
      · obtain ⟨u, huS, rfl⟩ := hto z hz
        rw [(ihimg u huS (himg' u huS) : img u = img' u)]
        exact hof' u huS
      · obtain ⟨u, huS, rfl⟩ := hto' z hz
        rw [← (ihimg u huS (himg' u huS) : img u = img' u)]
        exact hof u huS
  case record hfs ihfs =>
    intro w h₂; cases h₂ with | record _ hfs' => rw [ihfs _ hfs']
  case recordAccess he hdom ihe =>
    intro w h₂; cases h₂ with | recordAccess he' _ => rw [(ihe he' : _ = _)]
  case tuple hes ihes =>
    intro w h₂; cases h₂ with | tuple _ hes' => rw [ihes _ hes']
  case seq hes ihes =>
    intro w h₂; cases h₂ with | seq hes' => rw [ihes _ hes']
  case except hf hpath hrhs hv ihf ihpath ihrhs =>
    intro w h₂; cases h₂ with
    | «except» hf' hpath' hrhs' hv' =>
      obtain rfl := ihf hf'
      obtain rfl := ihpath _ hpath'
      obtain rfl := ihrhs hrhs'
      rwa [hv, Option.some.injEq] at hv'
  case if_true hc ht ihc iht =>
    intro w h₂; cases h₂ with
    | if_true hc' ht' => exact iht ht'
    | if_false hc' he' => absurd (ihc hc'); exact Value.tru_ne_fls
  case if_false hc he ihc ihe =>
    intro w h₂; cases h₂ with
    | if_true hc' ht' => absurd (ihc hc'); exact Value.fls_ne_tru
    | if_false hc' he' => exact ihe he'
  case case_hit hi hbefore hp hq ihbefore ihp ihq =>
    intro w h₂
    next _ _ _ _ i _ _ _ =>
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
  case case_other hbefore hq ihbefore ihq =>
    intro w h₂; cases h₂ with
    | @case_hit _ _ _ _ i₂ _ _ _ hi₂ hbefore₂ hp₂ hq₂ =>
      absurd (ihbefore _ _ _ hi₂ hp₂).symm; exact Value.tru_ne_fls
    | case_other hbefore₂ hq₂ => exact ihq hq₂
  case cons =>
    next _ _ ihh ihhs _ hl => cases hl with | cons hh' hhs' => rw [ihh hh', ihhs _ hhs']
  case inl =>
    next _ ih _ hp => cases hp with | inl hrest' => rw [ih _ hrest']
  case inr =>
    next _ _ ihv ihrest _ hp => cases hp with | inr hv' hrest' => rw [ihv hv', ihrest _ hrest']
  all_goals next _ _ h => cases h; rfl

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
    constructor
    · intro h; cases h; exact ⟨rfl, by simp⟩
    · rintro ⟨rfl, _⟩; exact .nil
  | cons i is ih =>
    intro vs
    constructor
    · intro h
      cases h with
      | cons hhd htl =>
        cases hhd with
        | fnCall hf hk hdom =>
          obtain rfl := evalUnique' hf hr
          obtain rfl := evalUnique' hk (.nat (Nat.toNat?_repr (i + 1)))
          obtain ⟨htail, hdomtail⟩ := ih.mp htl
          refine ⟨by rw [List.map_cons, htail], ?_⟩
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hdom
          · exact hdomtail j hj

    · rintro ⟨rfl, hdoms⟩
      rw [List.map_cons]
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
  -- TODO(locally-nameless): binder cases now recurse into `body.openVar x`; needs
  -- `(e.openVar x).freeVars.erase x ⊆ e.freeVars`, still to be added to `FreeVars.lean`.
  sorry

/-- Application of a sequence value at a valid index: the value stored at that position. -/
theorem fnApply_ofSeq {vs : List Value} {j : ℕ} (hj : j < vs.length) :
    fnApply (Value.ofSeq vs) (Value.ofNat (j + 1)) = vs[j] := by
  have hmem : ZFSet.pair (Value.ofNat (j + 1)) vs[j] ∈ Value.ofSeq vs :=
    Value.mem_ofSeq.mpr ⟨j, hj, rfl⟩
  have hspec : ZFSet.pair (Value.ofNat (j + 1))
      (fnApply (Value.ofSeq vs) (Value.ofNat (j + 1))) ∈ Value.ofSeq vs :=
    Classical.epsilon_spec (p := fun w ↦ ZFSet.pair (Value.ofNat (j + 1)) w ∈ Value.ofSeq vs)
      ⟨vs[j], hmem⟩
  obtain ⟨j', hj', heq⟩ := Value.mem_ofSeq.mp hspec
  rw [ZFSet.pair_inj] at heq
  obtain ⟨h1, h2⟩ := heq
  obtain rfl : j = j' := by have := Value.ofNat_inj.mp h1; omega
  exact h2

/-- The `.seqToFun` case of `evalCoerce'`, standalone: it does not recurse on a sub-coercion, only
re-evaluates `e` under the fresh binder `i` (`evalLocal'`, hence `hi : i ∉ e.freeVars`). The built
function `[i ∈ 1 .. Len(e) ↦ e[i]]` reproduces `e` itself when `e` denotes a sequence — its graph
already *is* that indexed family — and denotes nothing otherwise (`Len` is defined only on
sequences), which is exactly what `coerce (.seqToFun …)` states. -/
theorem evalCoerce'_seqToFun {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {τ : Typ} {i : String} {e : Expression Typ} {v' : Value}
    (hΞ : Ξ.WellScoped) (hi : i ∉ e.freeVars) :
    Eval Ξ Ω M (TypedTLAPlus.Coercion.applyComputable (.seqToFun τ i) e) v' ↔
      ∃ v, Eval Ξ Ω M e v ∧ coerce (.seqToFun τ i) v v' := by
  -- TODO(locally-nameless): `openVar`/`liftBound` cancellation + `evalLocal'`; deferred.
  sorry

/-- The `.function` case of `evalCoerce'`, standalone. `ihD`/`ihR` are `evalCoerce'` at the strictly
smaller `cDom`/`cRng` — passed in so this lives outside the `evalCoerce'` recursion block while the
termination checker still sees the calls. -/
theorem evalCoerce'_function {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {x y : String} {dom rng dom' rng' : Typ} {cD cR : Coercion} {e : Expression Typ} {v' : Value}
    (hΞ : Ξ.WellScoped)
    (hfr : y ∉ insert x e.freeVars ∧ Coercion.FreshFor cD {x} ∧
      Coercion.FreshFor cR (insert y e.freeVars))
    (ihD : ∀ {M : Memory Value} {e : Expression Typ} {v' : Value},
      Coercion.FreshFor cD e.freeVars →
        (Eval Ξ Ω M (cD.applyComputable e) v' ↔ ∃ v, Eval Ξ Ω M e v ∧ coerce cD v v'))
    (ihR : ∀ {M : Memory Value} {e : Expression Typ} {v' : Value},
      Coercion.FreshFor cR e.freeVars →
        (Eval Ξ Ω M (cR.applyComputable e) v' ↔ ∃ v, Eval Ξ Ω M e v ∧ coerce cR v v')) :
    Eval Ξ Ω M (TypedTLAPlus.Coercion.applyComputable
        (.function x y dom rng dom' rng' cD cR) e) v' ↔
      ∃ v, Eval Ξ Ω M e v ∧ coerce (.function x y dom rng dom' rng' cD cR) v v' := by
  -- TODO(locally-nameless): `openVar`/`liftBound` cancellation + `evalLocal'`; deferred.
  sorry

/-- Applying a coercion to an expression denotes the coercion applied to that expression's value.
Recurses on `c` through the equation compiler — `Coercion` is a nested inductive, so `induction`
does not fire. Needs `hΞ : Ξ.WellScoped` and `Coercion.FreshFor c e.freeVars`: the `.seqToFun`/
`.function` cases build a `.fn` whose body re-evaluates `e` under a binder the coercion introduces,
and `evalLocal'` relates that back to `e`'s ambient value only when the binder is fresh. -/
theorem evalCoerce' {Ξ : OperatorEnv} {Ω : Model Value} (hΞ : Ξ.WellScoped) :
    ∀ {c : Coercion} {M : Memory Value} {e : Expression Typ} {v' : Value},
      Coercion.FreshFor c e.freeVars →
      (Eval Ξ Ω M (TypedTLAPlus.Coercion.applyComputable c e) v' ↔
        ∃ v, Eval Ξ Ω M e v ∧ coerce c v v')
    := by
  -- TODO(locally-nameless): `.seqToFun`/`.function`/`.set`/… arms build synthesized binders that
  -- re-evaluate `e`; needs `openVar`/`liftBound` metatheory + `evalLocal'`. Deferred.
  intro c M e v' _hfr
  sorry

theorem evalSubst' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value} {x : String}
    {e' e : Expression Typ} {v' v : Value} (he' : Eval Ξ Ω M e' v') :
    Eval Ξ Ω (M.insert x v') e v ↔ Eval Ξ Ω M (Expression.subst x e' e) v := by
  sorry

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
  evalCoerce := fun hΞ hfr ↦ evalCoerce' hΞ hfr
  evalLocal := evalLocal'
  evalSubst := evalSubst'
  evalExcept := evalExcept'

end Operational
end ComputableTLAPlus

end
