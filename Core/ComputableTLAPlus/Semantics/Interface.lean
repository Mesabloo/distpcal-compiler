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

  `Eval` also takes an `OperatorEnv` (`Ξ`) and a `Model` (`Ω`), separate from `Memory` — see those
  types' own docs — to resolve a user-defined operator's name and a `CONSTANT`'s value; see `evalVar`
  for how the three environments interact.

  Refining this to the real TLA⁺ semantics means providing one `ExprSemantics` instance for a
  concrete value type; nothing downstream of this file changes.
-/

namespace ComputableTLAPlus

universe u

/-- The operator environment: a static table from a declaring module's name and an operator name in
it to that operator's formal parameters (name paired with arity — `0` for a plain value parameter,
`n > 0` for an `n`-ary higher-order parameter) and its defining body expression. Mirrors
`Declaration.operator`'s own `List (String × Nat) → Expression α` shape, since `Ξ` is populated from
exactly those declarations, one module at a time.

Keyed by module name because `Origin.module name` — the tag a `.var` node referring to an operator
carries, whether the operator lives in the same module or was reached through `EXTENDS` — already
names the module to look in; `evalVar` below consults `Ξ` only for that origin, so a name can never
be ambiguous between two modules'. A `CONSTANT` declaration is not in `Ξ` — it has no defining body —
see `Model` below for how a `CONSTANT`'s `.var` node gets its value instead.

Not indexed by `V`: unlike `Memory`, an unevaluated operator body is a piece of syntax, not a value,
so `Ξ` needs no value type to be well-formed. Kept a plain function rather than a `Finmap` — nothing
in this file's laws ever needs to enumerate or compare two `Ξ`s, only look one name up. -/
abbrev OperatorEnv : Type := String → String → Option (List (String × Nat) × Expression Typ)

/-- Every operator body in `Ξ` reads from memory only its own formal parameters — no stray free
`Origin.binder` variable. `evalLocal`/`evalSubst` need this: a `var_op0`/`opCall_op` step evaluates
a body (or its `substParams` form) that is not a subterm of the call, so agreement on the call's
free variables says nothing about that body unless the body is closed over its parameters. Populated
`Ξ`s satisfy it by construction — an operator definition's body is checked against a scope holding
exactly its parameters plus module-level names, and module-level names are `Origin.module`, which
`freeVars` does not count. -/
def OperatorEnv.WellScoped (Ξ : OperatorEnv) : Prop :=
  ∀ m x params body, Ξ m x = some (params, body) →
    ∀ z ∈ (body.freeVars), z ∈ params.map Prod.fst

/-- `c`'s synthesized binder names avoid `S` — and, through the nested `{x}`/`insert y S`
recursions, each other. The freshness side condition `evalCoerce` needs: `Coercion.applyComputable`
for `.seqToFun` and `.function` wraps the coerced expression `e` in a binder `c` introduces and
re-evaluates `e` underneath it, so unless that binder is fresh for `e` the built term captures and
the law is false. `S` is instantiated to `e.freeVars` at the law; a real compilation discharges it
because every coercion binder is `MonadFresh`-minted and `e`'s names are not.

Only `.seqToFun`/`.function` place `e` under a binder — the other cases keep it in domain or
argument position, so their arms impose nothing on `S` directly and only recurse. `.set`/inner
`.function` recurse against `{x}` rather than `S` because there the sub-expression is the bare
binder node `.var x _ .binder`, not something built over `e`. `.function` also keeps its value
binder `y` off `x`: `applyComputable`'s recovered-argument `CHOOSE` reuses `x`, and the built
`x = y` comparison is only correct when the two are distinct. -/
def _root_.TypedTLAPlus.Coercion.FreshFor : TypedTLAPlus.Coercion → Finset String → Prop
  | .id, _ => True
  | .strToSeq, _ => True
  | .seqToFun _ i, S => i ∉ S
  | .tupleToSeq _ _ _, _ => True
  | .set x _ _ c, _ => c.FreshFor {x}
  | .tuple coes _ _, S => ∀ c ∈ coes, c.FreshFor S
  | .record fields, S => ∀ f ∈ fields, f.2.1.FreshFor S
  | .function x y _ _ _ _ cD cR, S => y ∉ insert x S ∧ cD.FreshFor {x} ∧ cR.FreshFor (insert y S)
  | .comp c₁ c₂, S => c₁.FreshFor S ∧ c₂.FreshFor S
termination_by c => sizeOf c
decreasing_by
  all:
    first
      | decreasing_trivial
      | (have hmem : f ∈ fields := ‹_›
         obtain ⟨nm, cc, ty⟩ := f
         calc
          _ = sizeOf cc := rfl
          _ < sizeOf (nm, cc, ty) := by decreasing_trivial
          _ < sizeOf fields := List.sizeOf_lt_of_mem hmem
          _ < _ := by decreasing_trivial)

/-- `FreshFor` is antitone in the avoided set: fewer names to dodge is a weaker demand. Lets a
recursive `evalCoerce` call at a sub-expression whose free variables have shrunk (they only ever
shrink — `Coercion.applyComputable` adds no free variable) reuse the parent's hypothesis. -/
theorem _root_.TypedTLAPlus.Coercion.FreshFor.mono :
    ∀ {c : TypedTLAPlus.Coercion} {S S' : Finset String},
      TypedTLAPlus.Coercion.FreshFor c S → S' ⊆ S → TypedTLAPlus.Coercion.FreshFor c S'
  | .id, _, _, _, _ => by simp [TypedTLAPlus.Coercion.FreshFor]
  | .strToSeq, _, _, _, _ => by simp [TypedTLAPlus.Coercion.FreshFor]
  | .tupleToSeq _ _ _, _, _, _, _ => by simp [TypedTLAPlus.Coercion.FreshFor]
  | .seqToFun _ _, _, _, h, hsub => by
      simp only [TypedTLAPlus.Coercion.FreshFor] at h ⊢; exact fun hi ↦ h (hsub hi)
  | .set _ _ _ _, _, _, h, _ => by simpa only [TypedTLAPlus.Coercion.FreshFor] using h
  | .tuple coes _ _, _, _, h, hsub => by
      simp only [TypedTLAPlus.Coercion.FreshFor] at h ⊢
      exact fun c hc ↦ (h c hc).mono hsub
  | .record fields, _, _, h, hsub => by
      simp only [TypedTLAPlus.Coercion.FreshFor] at h ⊢
      exact fun f hf ↦ (h f hf).mono hsub
  | .function _ _ _ _ _ _ _ _, _, _, h, hsub => by
      simp only [TypedTLAPlus.Coercion.FreshFor] at h ⊢
      exact ⟨fun hy ↦ h.1 (Finset.insert_subset_insert _ hsub hy), h.2.1,
        h.2.2.mono (Finset.insert_subset_insert _ hsub)⟩
  | .comp _ _, _, _, h, hsub => by
      simp only [TypedTLAPlus.Coercion.FreshFor] at h ⊢
      exact ⟨h.1.mono hsub, h.2.mono hsub⟩
termination_by c => sizeOf c
decreasing_by
  all:
    first
      | decreasing_trivial
      | (have hmem : f ∈ fields := ‹_›
         obtain ⟨nm, cc, ty⟩ := f
         calc
          _ = sizeOf cc := rfl
          _ < sizeOf (nm, cc, ty) := by decreasing_trivial
          _ < sizeOf fields := List.sizeOf_lt_of_mem hmem
          _ < _ := by decreasing_trivial)

/-- The model: an assignment of a value to every `CONSTANT` a run fixes one for, keyed the same way
`Ξ` is (declaring module, then name) since a `CONSTANT`'s `.var` node carries the same `Origin.module`
tag an operator reference does. Kept opaque and partial rather than computed: a `CONSTANT` has no
defining expression to evaluate (`Declaration.constants` carries only a name and a type), so its
value can only ever come from outside — one run's choice of `Model`, not this file's laws. A name
with no entry has no value under `Eval`, same as any other partiality in this class. -/
abbrev Model (V : Type u) : Type u := String → String → Option V

/-- A memory: a partial map from names to values.

`Finmap`, not `AList`. An `AList` is a list, so its identity includes the *order* its keys were
inserted in — and `evalLocal` says evaluation depends on a memory only through `lookup`, so that
order is information the semantics provably cannot observe. Keeping it visible makes false goals:
binding two distinct names in the two possible orders gives equal lookups but unequal `AList`s, and
any lemma commuting one write past another (`Guarded2Network/Lemmas/Reorder.lean`) then cannot be
stated as an equation at all. `Finmap` is that quotient, so `Finmap.insert_insert_of_ne` holds and
extensionality is by `lookup`. `FIFOs` is a `Finmap` for the same reason. -/
abbrev Memory (V : Type u) : Type u := Finmap λ _ : String ↦ V

/-- One resolved segment of a reference's access path. Mirrors `ElaboratedPlusCal.Ref.args`'s
`List (String ⊕ ε)` with the index expressions already evaluated: `.inl f` is the record field `f`,
`.inr v` is the index `v`. -/
abbrev PathStep (V : Type u) : Type u := String ⊕ V

/-- `ResolvesPath Eval M path resolved` — every `.inr` index expression in the syntactic path
`path` evaluates (under `Eval`/`M`) to the matching entry of the semantic path `resolved`; every
`.inl` field segment carries over unchanged. What `evalExcept` needs to relate `Expression.except`'s
syntactic update path to `updatePath`'s semantic one. Takes `Eval` as a plain parameter rather than
an `ExprSemantics` instance so it can be stated *before* the class whose field it appears in. -/
inductive ResolvesPath {V : Type u} (Eval : Memory V → Expression Typ → V → Prop) (M : Memory V) :
    List (String ⊕ Expression Typ) → List (PathStep V) → Prop
  | nil : ResolvesPath Eval M [] []
  | inl {f path resolved} : ResolvesPath Eval M path resolved →
      ResolvesPath Eval M (.inl f :: path) (.inl f :: resolved)
  | inr {e v path resolved} : Eval M e v → ResolvesPath Eval M path resolved →
      ResolvesPath Eval M (.inr e :: path) (.inr v :: resolved)

/-- Everything the PlusCal semantics needs to know about expressions and the values they denote.
Held abstract here; a concrete TLA⁺ evaluator later supplies one instance. -/
class ExprSemantics (V : Type u) where
  /-- Values are compared for equality when used as FIFO index keys. -/
  [decEq : DecidableEq V]
  /-- `Eval Ξ Ω M e v` — under operator environment `Ξ`, model `Ω`, and memory `M`, expression `e`
  denotes `v`. Relational rather than functional, see this file's module doc. -/
  Eval : OperatorEnv → Model V → Memory V → Expression Typ → V → Prop
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
  eval_seq_nil {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V} {τ : Typ} :
    ∃ s, Eval Ξ Ω M (.seq [] τ) s ∧ isSeq s []
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
  evalUnique {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V} {e : Expression Typ} {v w : V} :
    Eval Ξ Ω M e v → Eval Ξ Ω M e w → v = w
  /-- A variable node's meaning is dispatched on its `Origin`, each case denoting from exactly one of
  the three environments:
  - `.binder` — the name is a lexical binder (a PlusCal variable among them): `M.lookup x`.
  - `.intrinsic` — a hardcoded builtin (`=`, `/\`, `DOMAIN`, …) has no value on its own; it only means
    something as the head of an `opCall`, which a concrete `ExprSemantics` instance dispatches off the
    builtin table directly. Bare, it denotes nothing — hence `False`, not a memory lookup: nothing in
    `Memory` could ever legitimately answer for it, so a law delegating to `M.lookup` here would only
    happen to give the right answer by nothing being stored under that name, rather than by construction.
  - `.module m` — looked up in `Ξ`'s entry for `m`. A 0-arity operator/function denotes its body's
    value, evaluated under the *same* `Ξ`/`Ω`/`M` — every free name a well-typed 0-arity body can
    contain is, by construction, one this project's type checker already resolved (a binder inside the
    body itself, an intrinsic, or another `.module`-origined name), so the same three environments
    already carry whatever that resolution needs. A name `Ξ m` has no 0-arity entry for is either a
    higher-order operator referenced bare (only an `opCall` gives one meaning — `False`, same reasoning
    as `.intrinsic`) or a `CONSTANT`, whose value comes from `Ω m x` instead.

  Structurally unambiguous throughout: `Origin` alone selects the case, so no invariant about names or
  shadowing is needed to keep the environments from racing.

  Stated for every `Origin`, not only `.binder`: `Expression.subst` and `Expression.freeVars` both
  match a `.var` on its name alone and ignore its origin, so `evalSubst` below already commits every
  `.var` node to being resolved this way — a kind-restricted law would contradict a law already here. -/
  evalVar {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V} {x : String} {τ : Typ} {o : Origin} {v : V} :
    Eval Ξ Ω M (.var x τ o) v ↔
      match o with
      | .binder => M.lookup x = some v
      | .intrinsic => False
      | .module m =>
        match Ξ m x with
        | some ([], body) => Eval Ξ Ω M body v
        | some (_ :: _, _) => False
        | none => Ω m x = some v
  /-- Applying a coercion to an expression denotes the coercion applied to that expression's value.
  `TypedTLAPlus.Coercion.applyComputable` and `coerce` above are the expression-level and
  value-level views of one operation, and this is the only thing connecting them — a pass that
  compiles a coercion into synthesized syntax (`Guarded2Network` does, on a `receive`'s consumption
  assignment) can relate the two only through this law.

  An `↔`: the forward reading turns the target's evaluated right-hand side into the source's
  `coerce` obligation, the backward one builds the target's from the source's.

  Needs `Ξ.WellScoped` and `Coercion.FreshFor c e.freeVars` for the same reason `evalLocal` needs the
  first: `applyComputable` for `.seqToFun`/`.function` re-evaluates `e` under a binder the coercion
  introduces, and relating that to `e`'s value in the ambient memory is exactly `evalLocal`. -/
  evalCoerce {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V} {c : TypedTLAPlus.Coercion}
      {e : Expression Typ} {v' : V} :
    Ξ.WellScoped → TypedTLAPlus.Coercion.FreshFor c e.freeVars →
      (Eval Ξ Ω M (TypedTLAPlus.Coercion.applyComputable c e) v' ↔ ∃ v, Eval Ξ Ω M e v ∧ coerce c v v')
  /-- Evaluation only depends on the free variables `e` actually reads — agreeing memories give
  agreeing results, for shared `Ξ`/`Ω` (immutable within one evaluation, see this file's module doc,
  so there is nothing to vary them against). Needs `Ξ.WellScoped`: an operator call reads its body
  through `Ξ`, and that body is not part of `e`, so its own free variables have to be confined to
  the operator's parameters for the call's `freeVars` to bound what memory the call depends on. -/
  evalLocal {Ξ : OperatorEnv} {Ω : Model V} {M₁ M₂ : Memory V} {e : Expression Typ} {v : V} :
    Ξ.WellScoped → (∀ x ∈ e.freeVars, M₁.lookup x = M₂.lookup x) →
      (Eval Ξ Ω M₁ e v ↔ Eval Ξ Ω M₂ e v)
  /-- Substitution is evaluation-under-extended-memory, read backwards: binding `x` to `e'`'s
  value and evaluating `e` agrees with evaluating `e`'s `x`-substituted form under the original
  memory. -/
  evalSubst {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V} {x : String} {e' e : Expression Typ}
      {v' v : V} :
    Eval Ξ Ω M e' v' → (Eval Ξ Ω (M.insert x v') e v ↔ Eval Ξ Ω M (Expression.subst x e' e) v)
  /-- `[f EXCEPT ![path] = rhs]` denotes `updatePath` applied to `f`'s value, `rhs`'s value, and
  the syntactic path resolved (`ResolvesPath`) against the same memory. Scoped to the one-update
  form — the only shape `Expression.substRef` ever produces. -/
  evalExcept {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V} {f rhs : Expression Typ} {τ : Typ}
      {path : List (String ⊕ Expression Typ)} {vf vr v : V} {resolved : List (PathStep V)} :
    Eval Ξ Ω M f vf → ResolvesPath (Eval Ξ Ω) M path resolved → Eval Ξ Ω M rhs vr →
    (Eval Ξ Ω M (.except f τ [(path, rhs)]) v ↔ updatePath vf resolved vr = some v)

attribute [reducible, instance] ExprSemantics.decEq

namespace ExprSemantics

variable {V : Type u} [ExprSemantics V]

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
theorem isSeq_of_eval_seq_nil {Ξ : OperatorEnv} {Ω : Model V} {M : Memory V} {τ : Typ} {s : V}
    (h : ExprSemantics.Eval Ξ Ω M (.seq [] τ) s) : ExprSemantics.isSeq s [] := by
  obtain ⟨s', h', hseq⟩ := ExprSemantics.eval_seq_nil (Ξ := Ξ) (Ω := Ω) (M := M) (τ := τ)
  rwa [ExprSemantics.evalUnique h' h] at hseq

/-- `Aborts Ξ Ω M e` — `e` has no value at all under `Ξ`/`Ω`/`M`. Derived rather than assumed: with
`Eval` a relation, "no derivation tree" already *is* the meaning of "no value", so nothing links the
two notions that needs stating separately. -/
def Aborts (Ξ : OperatorEnv) (Ω : Model V) (M : Memory V) (e : Expression Typ) : Prop :=
  ¬ ∃ v, ExprSemantics.Eval Ξ Ω M e v

/-- `Aborts` transported along an agreement between two evaluations. Every transfer lemma about
`Eval` has an `Aborts` counterpart, and `Aborts` being a negated existential means each one is this
same `not_congr (exists_congr …)` — stating it once keeps the definition's body out of the proofs
that use it. -/
theorem aborts_congr {Ξ : OperatorEnv} {Ω : Model V} {M₁ M₂ : Memory V} {e₁ e₂ : Expression Typ}
    (h : ∀ v, ExprSemantics.Eval Ξ Ω M₁ e₁ v ↔ ExprSemantics.Eval Ξ Ω M₂ e₂ v) :
    Aborts Ξ Ω M₁ e₁ ↔ Aborts Ξ Ω M₂ e₂ :=
  not_congr (exists_congr h)

end ExprSemantics

/-- `Memory.update M x path v` — `M` with the position `path` inside `x`'s current value overwritten
by `v`. Fails when `x` is unbound, or when `path` does not resolve inside the value found there.
Note `x` must already be bound: PlusCal assignment updates a declared variable, it never introduces
one. -/
def Memory.update {V : Type u} [ExprSemantics V] (M : Memory V) (x : String)
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
theorem Memory.update_eq_some_iff {V : Type u} [ExprSemantics V] {M M' : Memory V} {x : String}
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
theorem Memory.update_eq_none_iff {V : Type u} [ExprSemantics V] {M : Memory V} {x : String}
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
theorem Memory.update_nil {V : Type u} [ExprSemantics V] {M M' : Memory V} {x : String} {v : V}
    (h : M.update x [] v = some M') : M' = M.insert x v := by
  obtain ⟨_, new, _, hnew, hM'⟩ := Memory.update_eq_some_iff.mp h
  rw [ExprSemantics.updatePath_nil] at hnew
  rw [hM', Option.some.inj hnew]

/-- An update and a binding of some *other* name commute: updating first and then binding `x`
reaches the same memory as binding `x` first and then updating, and either order succeeds exactly
when the other does. `Memory` being a `Finmap` is what makes this an equation rather than only a
`lookup`-wise agreement — see that abbreviation's doc. Both readings are used, one per direction of
`Guarded2Network/Lemmas/Reorder.lean`'s `with` case, where the binding is the `with`'s own. -/
theorem Memory.update_insert_iff {V : Type u} [ExprSemantics V] {M M₂ : Memory V} {x y : String}
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
assignment ran.

`r`'s target is a declared PlusCal variable, `Origin.binder`, so `evalVar`'s `.module`-lookup branch
never applies to it — `evalVar.mpr hold` below goes through unconditionally, no side condition
needed (see `evalVar`'s own doc for why `Origin` alone, not a name-shadowing assumption, decides
this). -/
theorem ExprSemantics.evalSubstRef {V : Type u} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}
    {M M' : Memory V} {r : ElaboratedPlusCal.Ref Typ (Expression Typ)} {rhs e : Expression Typ}
    {v w : V} {rpath : List (PathStep V)} (hrhs : ExprSemantics.Eval Ξ Ω M rhs v)
    (hpath : ResolvesPath (ExprSemantics.Eval Ξ Ω) M r.args rpath)
    (hM' : Memory.update M r.name rpath v = some M') :
    ExprSemantics.Eval Ξ Ω M' e w ↔ ExprSemantics.Eval Ξ Ω M (Expression.substRef r rhs e) w := by
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
