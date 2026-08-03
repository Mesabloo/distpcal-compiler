module

public import Core.ComputableTLAPlus.Syntax
public import Core.ComputableTLAPlus.FreeVars
public import Core.ComputableTLAPlus.Subst
public import Core.TypedTLAPlus.Coercion
public import Mathlib.Data.List.AList

@[expose] public section

/-!
  The expression layer that the PlusCal denotational semantics
  (`Core/GuardedPlusCal/Semantics/Denotational.lean` and its `NetworkPlusCal` counterpart) sits on
  top of, kept abstract.

  Statement semantics genuinely need to look inside values — `await`/`assert` compare against
  `TRUE`, `with x ∈ e` picks a member of a set, `assign`/`receive` write into a value along a
  reference's path, `receive` applies the coercion the elaborator recorded. None of that can be
  written against a bare `Value : Type`, so every such operation is a field of `ExprSemantics`
  rather than a definition over known constructors.

  Evaluation is a *relation*, not an `Option`-valued function: a user-defined operator call has to
  re-descend into that operator's body, jumping to an unrelated syntax tree with no measure Lean's
  termination checker can see. A relation needs only strict positivity, and an expression with no
  derivation tree is exactly an expression with no value — which is why `Aborts` below is derived
  from `Eval` rather than being a second parameter.

  Refining this to the real TLA⁺ semantics means providing one `ExprSemantics` instance for a
  concrete value type; nothing downstream of this file changes.
-/

namespace ComputableTLAPlus

/-- A memory: a partial map from names to values. Shared by the process-local and temporary
(`with`-bound) halves of a `LocalState`, which are combined with `∪` at every use site. -/
abbrev Memory (V : Type) : Type := AList λ _ : String ↦ V

/-- One resolved segment of a reference's access path. Mirrors `ElaboratedPlusCal.Ref.args`'s
`List (String ⊕ ε)` with the index expressions already evaluated: `.inl f` is the record field `f`,
`.inr v` is the index `v`. -/
abbrev PathStep (V : Type) : Type := String ⊕ V

/-- `ResolvesPath Eval M path resolved` — every `.inr` index expression in the syntactic path
`path` evaluates (under `Eval`/`M`) to the matching entry of the semantic path `resolved`; every
`.inl` field segment carries over unchanged. What `evalExcept` needs to relate `Expression.except`'s
syntactic update path to `updatePath`'s semantic one. Takes `Eval` as a plain parameter rather than
an `ExprSemantics` instance so it can be stated *before* the class whose field it appears in. -/
inductive ResolvesPath {V : Type} (Eval : Memory V → Expression Typ → V → Prop) (M : Memory V) :
    List (String ⊕ Expression Typ) → List (PathStep V) → Prop
  | nil : ResolvesPath Eval M [] []
  | inl {f path resolved} : ResolvesPath Eval M path resolved →
      ResolvesPath Eval M (.inl f :: path) (.inl f :: resolved)
  | inr {e v path resolved} : Eval M e v → ResolvesPath Eval M path resolved →
      ResolvesPath Eval M (.inr e :: path) (.inr v :: resolved)

/-- Everything the PlusCal semantics needs to know about expressions and the values they denote.
Held abstract here; a concrete TLA⁺ evaluator later supplies one instance. -/
class ExprSemantics (V : Type) where
  /-- Values are compared for equality when used as FIFO index keys. -/
  [decEq : DecidableEq V]
  /-- `Eval M e v` — under memory `M`, expression `e` denotes `v`. Relational rather than
  functional, see this file's module doc. -/
  Eval : Memory V → Expression Typ → V → Prop
  /-- The value of `TRUE`. -/
  tru : V
  /-- The value is a boolean. Only needed to state that a non-boolean guard *aborts*, as opposed to
  merely blocking. -/
  isBool : V → Prop
  /-- The value is a set. Same role for `with x ∈ e`: an empty set blocks, a non-set aborts, and
  `mem` alone cannot tell the two apart. -/
  isSet : V → Prop
  /-- `mem v S` — `v` is a member of the set value `S`. -/
  mem : V → V → Prop
  /-- `updatePath old path v` — `old` with the position named by `path` overwritten by `v`, or
  `none` when `path` does not resolve inside `old`. `path = []` overwrites `old` outright. -/
  updatePath : V → List (PathStep V) → V → Option V
  /-- `seqAppend s v` — `s` with `v` appended on the right, `none` when `s` is not a sequence value.
  TLA⁺'s `Append(s, v)`. Needed by `NetworkPlusCal.Thread.rx`, which drains a channel into a
  process-local sequence. -/
  seqAppend : V → V → Option V
  /-- `coerce c v v'` — applying the coercion `c` to `v` yields `v'`. The value-level counterpart of
  `Coercion.apply`/`Coercion.applyComputable`, which act on expressions. -/
  coerce : TypedTLAPlus.Coercion → V → V → Prop
  /-- Evaluation only depends on the free variables `e` actually reads — agreeing memories give
  agreeing results. Replaces prior art's `eval_ext`/`eval_mem_ext`. -/
  evalLocal {M₁ M₂ : Memory V} {e : Expression Typ} {v : V} :
    (∀ x ∈ e.freeVars, M₁.lookup x = M₂.lookup x) → (Eval M₁ e v ↔ Eval M₂ e v)
  /-- Substitution is evaluation-under-extended-memory, read backwards: binding `x` to `e'`'s
  value and evaluating `e` agrees with evaluating `e`'s `x`-substituted form under the original
  memory. -/
  evalSubst {M : Memory V} {x : String} {e' e : Expression Typ} {v' v : V} :
    Eval M e' v' → (Eval (M.insert x v') e v ↔ Eval M (Expression.subst x e' e) v)
  /-- `[f EXCEPT ![path] = rhs]` denotes `updatePath` applied to `f`'s value, `rhs`'s value, and
  the syntactic path resolved (`ResolvesPath`) against the same memory. Scoped to the one-update
  form — the only shape `Expression.substRef` ever produces. -/
  evalExcept {M : Memory V} {f rhs : Expression Typ} {τ : Typ} {path : List (String ⊕ Expression Typ)}
      {vf vr v : V} {resolved : List (PathStep V)} :
    Eval M f vf → ResolvesPath Eval M path resolved → Eval M rhs vr →
    (Eval M (.except f τ [(path, rhs)]) v ↔ updatePath vf resolved vr = some v)

attribute [reducible, instance] ExprSemantics.decEq

namespace ExprSemantics

variable {V : Type} [ExprSemantics V]

@[inherit_doc ExprSemantics.Eval]
notation:60 M:60 " ⊢ " e:0 " ⇒ " v:60 => ExprSemantics.Eval M e v

/-- `M ⊢ e ↯` — `e` has no value at all under `M`. Derived rather than assumed: with `Eval` a
relation, "no derivation tree" already *is* the meaning of "no value", so nothing links the two
notions that needs stating separately. -/
def Aborts (M : Memory V) (e : Expression Typ) : Prop := ¬ ∃ v, M ⊢ e ⇒ v

@[inherit_doc Aborts]
notation:60 M:60 " ⊢ " e:0 " ↯" => ExprSemantics.Aborts M e

end ExprSemantics

/-- `Memory.update M x path v` — `M` with the position `path` inside `x`'s current value overwritten
by `v`. Fails when `x` is unbound, or when `path` does not resolve inside the value found there.
Note `x` must already be bound: PlusCal assignment updates a declared variable, it never introduces
one. -/
def Memory.update {V : Type} [ExprSemantics V] (M : Memory V) (x : String)
    (path : List (PathStep V)) (v : V) : Option (Memory V) := do
  let old ← M.lookup x
  let new ← ExprSemantics.updatePath old path v
  return M.insert x new

end ComputableTLAPlus

end
