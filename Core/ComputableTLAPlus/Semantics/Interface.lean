module

meta import CustomPrelude
public import Core.ComputableTLAPlus.Syntax
public import Core.ComputableTLAPlus.FreeVars
public import Core.ComputableTLAPlus.Subst
public import Core.ComputableTLAPlus.Coercion
public import Core.TypedTLAPlus.Coercion
public import Mathlib.Data.Finmap

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

/-- A memory: a partial map from names to values.

`Finmap`, not `AList`. An `AList` is a list, so its identity includes the *order* its keys were
inserted in — and `evalLocal` says evaluation depends on a memory only through `lookup`, so that
order is information the semantics provably cannot observe. Keeping it visible makes false goals:
binding two distinct names in the two possible orders gives equal lookups but unequal `AList`s, and
any lemma commuting one write past another (`Guarded2Network/Lemmas/Reorder.lean`) then cannot be
stated as an equation at all. `Finmap` is that quotient, so `Finmap.insert_insert_of_ne` holds and
extensionality is by `lookup`. `FIFOs` is a `Finmap` for the same reason. -/
abbrev Memory (V : Type) : Type := Finmap λ _ : String ↦ V

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
  /-- The empty path overwrites the old value outright, and always succeeds. A law rather than only
  a remark on `updatePath` above, because `Memory.update` routes an *unindexed* assignment (`x := e`,
  where the reference has no `.args`) through `updatePath` too: without this, the memory such an
  assignment produces is not pinned to `M.insert x v`, and no reorder lemma can identify it with the
  memory substitution describes. -/
  updatePath_nil {old v : V} : updatePath old [] v = some v
  /-- `seqAppend s v` — `s` with `v` appended on the right, `none` when `s` is not a sequence value.
  TLA⁺'s `Append(s, v)`. Needed by `NetworkPlusCal.Thread.rx`, which drains a channel into a
  process-local sequence. -/
  seqAppend : V → V → Option V
  /-- `isSeq s vs` — `s` is the sequence value whose elements are `vs`, in order. The link between
  the value world and a `List V`: a sequence-valued local and a FIFO's contents are otherwise two
  unrelated things, and nothing else in this class bridges them.

  A relation rather than a partial function to a list, for the same reason `Eval` is one: it is a
  fact about a value, not a computation, and a value that is not a sequence is simply related to
  no list. Kept element-level (no `isSeq`-vs-`seqAppend` well-formedness field): `seqAppend_isSeq`
  below is the only interaction the semantics needs. -/
  isSeq : V → List V → Prop
  /-- A value is the sequence of at most one element list. -/
  isSeq_inj {s : V} {vs ws : List V} : isSeq s vs → isSeq s ws → vs = ws
  /-- The empty sequence literal has a value, and it is the empty sequence. The one place a *value*
  has to be known to be a sequence from the syntax that produced it rather than from an operation on
  another sequence: `seqAppend` covers every step after the first, and this covers the first.

  Stated as existence for the reason `seqAppend_isSeq` is: *totality* is then part of the law. An
  initial state exists only if every declared initializer evaluates, so an implication would leave a
  `<<>>` initializer free to have no value at all. The implication form is `isSeq_of_eval_seq_nil`
  below, `evalUnique` away. -/
  eval_seq_nil {M : Memory V} {τ : Typ} : ∃ s, Eval M (.seq [] τ) s ∧ isSeq s []
  /-- Appending to a sequence value always succeeds, and appends to its element list. Stated as
  existence rather than as an equation on a given result so that `seqAppend`'s *totality on
  sequences* is part of the law — `Thread.rxBranch` treats a failed append as an abort, which must
  not be reachable when `inbox` really holds a sequence. -/
  seqAppend_isSeq {s v : V} {vs : List V} : isSeq s vs →
    ∃ s', seqAppend s v = some s' ∧ isSeq s' (vs ++ [v])
  /-- Every tail of a sequence is itself a sequence value. The counterpart of `seqAppend_isSeq` on
  the other side: that one says the value world is closed under adding an element, this one that it
  is closed under dropping the first. Needed because `isSeq` is a relation — without it a list could
  have no value representing it, and a compiled `inbox := Tail(inbox)` would be free to abort where
  the source it compiles does not. -/
  isSeq_tail {s v : V} {vs : List V} : isSeq s (v :: vs) → ∃ t, isSeq t vs
  /-- `coerce c v v'` — applying the coercion `c` to `v` yields `v'`. The value-level counterpart of
  `Coercion.apply`/`Coercion.applyComputable`, which act on expressions. -/
  coerce : TypedTLAPlus.Coercion → V → V → Prop
  /-- An expression has at most one value. `Eval` is a relation because evaluation may *fail* to
  have a derivation, not because a TLA⁺ expression could denote two things — non-determinism enters
  the PlusCal semantics through `with x ∈ S` and process scheduling, never through an expression.

  Load-bearing rather than cosmetic: a `Ref`'s index path resolves through `EvalStep`, so without
  this a channel reference could resolve to two different `ChanKey`s at once and no invariant could
  name *the* FIFO a `receive` reads. `EvalStep.path_inj` is that consequence. -/
  evalUnique {M : Memory V} {e : Expression Typ} {v w : V} : Eval M e v → Eval M e w → v = w
  /-- A variable node denotes what the memory binds its name to, and denotes nothing when the name
  is unbound.

  Stated for every `Origin`, not only `.binder`: `Expression.subst` and `Expression.freeVars` both
  match a `.var` on its name alone and ignore its origin, so `evalSubst` below already commits every
  `.var` node to being memory-resolved — a kind-restricted law would contradict a law already here.
  TLA⁺ builtins are unaffected: they occur only as `opCall` callees, and it is the call as a whole
  whose meaning `Eval` fixes. -/
  evalVar {M : Memory V} {x : String} {τ : Typ} {o : Origin} {v : V} :
    Eval M (.var x τ o) v ↔ M.lookup x = some v
  /-- Applying a coercion to an expression denotes the coercion applied to that expression's value.
  `TypedTLAPlus.Coercion.applyComputable` and `coerce` above are the expression-level and
  value-level views of one operation, and this is the only thing connecting them — a pass that
  compiles a coercion into synthesized syntax (`Guarded2Network` does, on a `receive`'s consumption
  assignment) can relate the two only through this law.

  An `↔`: the forward reading turns the target's evaluated right-hand side into the source's
  `coerce` obligation, the backward one builds the target's from the source's. -/
  evalCoerce {M : Memory V} {c : TypedTLAPlus.Coercion} {e : Expression Typ} {v' : V} :
    Eval M (TypedTLAPlus.Coercion.applyComputable c e) v' ↔ ∃ v, Eval M e v ∧ coerce c v v'
  /-- Evaluation only depends on the free variables `e` actually reads — agreeing memories give
  agreeing results. -/
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

/-- `seqAppend_isSeq` read against a result already in hand: `seqAppend` is a function, so its
`some` result is *the* one the law produces. -/
theorem isSeq_of_seqAppend {s v s' : V} {vs : List V} (h : ExprSemantics.isSeq s vs)
    (h' : ExprSemantics.seqAppend s v = some s') : ExprSemantics.isSeq s' (vs ++ [v]) := by
  obtain ⟨s'', happ, hseq⟩ := ExprSemantics.seqAppend_isSeq (v := v) h
  rw [h'] at happ
  obtain rfl := Option.some.inj happ
  exact hseq

/-- `eval_seq_nil` read against a value already in hand: evaluation is deterministic, so *the* value
of `<<>>` is the empty sequence. -/
theorem isSeq_of_eval_seq_nil {M : Memory V} {τ : Typ} {s : V}
    (h : ExprSemantics.Eval M (.seq [] τ) s) : ExprSemantics.isSeq s [] := by
  obtain ⟨s', h', hseq⟩ := ExprSemantics.eval_seq_nil (M := M) (τ := τ)
  rwa [ExprSemantics.evalUnique h' h] at hseq

/-- `M ⊢ e ↯` — `e` has no value at all under `M`. Derived rather than assumed: with `Eval` a
relation, "no derivation tree" already *is* the meaning of "no value", so nothing links the two
notions that needs stating separately. -/
def Aborts (M : Memory V) (e : Expression Typ) : Prop := ¬ ∃ v, M ⊢ e ⇒ v

@[inherit_doc Aborts]
notation:60 M:60 " ⊢ " e:0 " ↯" => ExprSemantics.Aborts M e

/-- `Aborts` transported along an agreement between two evaluations. Every transfer lemma about
`Eval` has an `Aborts` counterpart, and `Aborts` being a negated existential means each one is this
same `not_congr (exists_congr …)` — stating it once keeps the definition's body out of the proofs
that use it. -/
theorem aborts_congr {M₁ M₂ : Memory V} {e₁ e₂ : Expression Typ}
    (h : ∀ v, (M₁ ⊢ e₁ ⇒ v) ↔ (M₂ ⊢ e₂ ⇒ v)) : (M₁ ⊢ e₁ ↯) ↔ (M₂ ⊢ e₂ ↯) :=
  not_congr (exists_congr h)

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

/-! `Memory.update` is a two-step `Option` bind, and taking one apart by hand costs an `unfold` plus
the same `Option.bind_eq_*_iff` rewrite every time. The two equations below are that decomposition,
stated once here where the definition lives so that no proof elsewhere has to reach into the body.
Both are `↔`: consumers need the reading that takes a successful update apart *and* the one that
builds a fresh update at a different memory. -/

/-- An update succeeds exactly when the name is bound and `updatePath` accepts the value found
there; the result is that name rebound to what came back. -/
theorem Memory.update_eq_some_iff {V : Type} [ExprSemantics V] {M M' : Memory V} {x : String}
    {path : List (PathStep V)} {v : V} :
    M.update x path v = some M' ↔
      ∃ old new, M.lookup x = some old ∧ ExprSemantics.updatePath old path v = some new ∧
        M' = M.insert x new := by
  unfold Memory.update
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff]
  iff_rintro ⟨old, hold, new, hnew, h⟩ ⟨old, new, hold, hnew, rfl⟩
  · exact ⟨old, new, hold, hnew, (Option.some.inj h).symm⟩
  · exact ⟨old, hold, new, hnew, rfl⟩

/-- An update fails exactly when the name is unbound, or `updatePath` rejects the value found
there. -/
theorem Memory.update_eq_none_iff {V : Type} [ExprSemantics V] {M : Memory V} {x : String}
    {path : List (PathStep V)} {v : V} :
    M.update x path v = none ↔
      ∀ old, M.lookup x = some old → ExprSemantics.updatePath old path v = none := by
  unfold Memory.update
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff, Option.some_ne_none,
    imp_false, ← Option.eq_none_iff_forall_ne_some]

/-- At the empty path an update is exactly `insert`: `updatePath_nil` says the old value plays no
part. This is what an *unindexed* assignment `x := e` does to the memory, and it is the form
substitution describes — `Expression.substRef` on a reference with no `.args` substitutes `e` for
`x` outright rather than building an `EXCEPT`. -/
theorem Memory.update_nil {V : Type} [ExprSemantics V] {M M' : Memory V} {x : String} {v : V}
    (h : M.update x [] v = some M') : M' = M.insert x v := by
  obtain ⟨_, new, _, hnew, hM'⟩ := Memory.update_eq_some_iff.mp h
  rw [ExprSemantics.updatePath_nil] at hnew
  rw [hM', Option.some.inj hnew]

/-- An update and a binding of some *other* name commute: updating first and then binding `x`
reaches the same memory as binding `x` first and then updating, and either order succeeds exactly
when the other does. `Memory` being a `Finmap` is what makes this an equation rather than only a
`lookup`-wise agreement — see that abbreviation's doc. Both readings are used, one per direction of
`Guarded2Network/Lemmas/Reorder.lean`'s `with` case, where the binding is the `with`'s own. -/
theorem Memory.update_insert_iff {V : Type} [ExprSemantics V] {M M₂ : Memory V} {x y : String}
    {path : List (PathStep V)} {u v : V} (hne : x ≠ y) :
    (∃ M', M.update y path v = some M' ∧ M₂ = M'.insert x u) ↔
      Memory.update (M.insert x u) y path v = some M₂ := by
  iff_rintro ⟨M', hM', rfl⟩ h
  · obtain ⟨old, new, hold, hnew, rfl⟩ := Memory.update_eq_some_iff.mp hM'
    refine Memory.update_eq_some_iff.mpr ⟨old, new, ?_, hnew, ?_⟩
    · rwa [Finmap.lookup_insert_of_ne _ hne.symm]
    · exact (Finmap.insert_insert_of_ne _ hne).symm
  · obtain ⟨old, new, hold, hnew, rfl⟩ := Memory.update_eq_some_iff.mp h
    rw [Finmap.lookup_insert_of_ne _ hne.symm] at hold
    exact ⟨M.insert y new, Memory.update_eq_some_iff.mpr ⟨old, new, hold, hnew, rfl⟩,
      Finmap.insert_insert_of_ne _ hne⟩

/-- `evalSubst` lifted from a name to a *reference*: evaluating in the memory an assignment produced
agrees with evaluating the reference-substituted expression in the memory it started from. This is
the transfer the reorder lemmas run on (`Guarded2Network/Lemmas/Reorder.lean`), and it is derived —
`evalSubst` covers a bare reference directly, while a compound one needs `evalVar` to name the value
being updated and `evalExcept` to say the synthesized `EXCEPT` denotes exactly the `updatePath` the
assignment ran. -/
theorem ExprSemantics.evalSubstRef {V : Type} [ExprSemantics V] {M M' : Memory V}
    {r : ElaboratedPlusCal.Ref Typ (Expression Typ)} {rhs e : Expression Typ} {v w : V}
    {rpath : List (PathStep V)} (hrhs : M ⊢ rhs ⇒ v)
    (hpath : ResolvesPath ExprSemantics.Eval M r.args rpath)
    (hM' : Memory.update M r.name rpath v = some M') :
    (M' ⊢ e ⇒ w) ↔ (M ⊢ Expression.substRef r rhs e ⇒ w) := by
  obtain ⟨old, new, hold, hnew, rfl⟩ := Memory.update_eq_some_iff.mp hM'
  by_cases hargs : r.args = []
  · rw [hargs] at hpath
    cases hpath
    rw [ExprSemantics.updatePath_nil] at hnew
    obtain rfl := Option.some.inj hnew
    rw [Expression.substRef_of_args_nil hargs]
    exact ExprSemantics.evalSubst hrhs
  · rw [Expression.substRef_of_args_ne_nil hargs]
    apply ExprSemantics.evalSubst
    apply (ExprSemantics.evalExcept (ExprSemantics.evalVar.mpr hold) hpath hrhs).mpr
    exact hnew

end ComputableTLAPlus

end
