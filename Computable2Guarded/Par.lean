module

public import Core.ComputablePlusCal.Syntax
public import Common.Fresh

public section

/-!
  `𝒞_par`: eliminates parallel assignment (`r1≔e1 ‖ … ‖ rn≔en`) by hoisting every RHS, and every
  compound `Ref`'s own index expressions, into fresh `with`-bound temporaries evaluated up front,
  then re-emitting `n` ordinary single-target assignments in the original order. Same type in,
  same type out (`ComputablePlusCal.Statement`/`.Block`/`.Branches`). The invariant it establishes —
  `GuardedPlusCal.Statement.assign` takes a single `(Ref, Expr)` pair — is a runtime fact about
  `ComputablePlusCal.Statement.assign`'s `List`, maintained by this pass alone rather than by the
  type.

  ```
  𝒞_par(r1≔e1 ‖ … ‖ rn≔en) =
    with v1=e1 do … with vn=en do (
      𝒞_par(r1, λr1. …) … 𝒞_par(rn, λrn. …)
      r1 := v1; … ; rn := vn )
    where 𝒞_par(x, f) = f(x)
          𝒞_par(r[e1,…,en], f) = 𝒞_par(r, λr0. with y1=e1 do … with yn=en do f(r0[y1,…,yn]))
          𝒞_par(r.x, f) = 𝒞_par(r, λr0. f(r0.x))
  ```

  **Reference-recursion, generalized to this project's flat `Ref.args : List (String ⊕
  Expression)`** (the field-access prerequisite, `Core/TypedPlusCal/Syntax.lean`'s module doc):
  walked left to right, a `.inl field` segment passes straight through with no fresh variable
  (the `r.x` case above), a `.inr indexExpr` segment binds one fresh temp (the `r[e]` case) —
  simpler than a recursive-prefix formulation since this project's `Ref` is already flat, no
  nested `Ref`-within-`Ref`.

  **A length-≤1 assignment list passes through untouched.** Aliasing is only a concern between
  *multiple* simultaneous writes; running the general temp-var recipe on a single assignment
  would be correct but pure noise.

  Every synthesized `with` carries its own `ann : Typ` field past this pass: `FlatReord`'s walk
  hands it, unchanged, to `GuardedPlusCal.Statement.with`'s own `ann` field. The outer RHS bindings (`vᵢ`'s type must match `rᵢ`'s own
  result type for `rᵢ := vᵢ` to be well-typed) and the inner index-temp bindings (each index
  expression's own type) both get their real type now, via `Ref.resultType`/`.indexType`
  respectively (`Core/ComputablePlusCal/Syntax.lean`) — cheap structural recomputation from
  `Ref.baseType`, no re-running inference needed (`Ref.baseType`'s own doc comment, `Core/
  TypedPlusCal/Syntax.lean`, explains why).
-/

open ComputablePlusCal (Expression Ref Statement Block Branches Ref.stepType Ref.indexType Ref.resultType)

variable {m : Type → Type} [Monad m] [MonadFresh m]

/-- `𝒞_par`'s per-`Ref` recursion: walks `r.args` left to right, binding one fresh temp per
`.inr` (bracket-index) segment via a `with`, leaving every `.inl` (field-access) segment
untouched, then hands the reconstructed `Ref` to `k`. Threads the type-so-far explicitly
(starting at `r.baseType`, stepped via `Ref.stepType`) so each hoisted index-temp gets its own
correct type (`Ref.indexType`), not the unrelated referenced `Ref`'s own result type. -/
private partial def parRef (pos : SourceSpan) (r : Ref) (k : Ref → m (Block false)) : m (Block false) :=
  go r.baseType r.args []
where
  go (τ : ComputableTLAPlus.Typ) (remaining seen : List (String ⊕ Expression)) : m (Block false) :=
    match remaining with
    | [] => k { r with args := seen.reverse }
    | .inl field :: rest => go (Ref.stepType τ (.inl field)) rest (.inl field :: seen)
    | .inr e :: rest => do
      let idxTy := Ref.indexType τ
      let y ← freshName "idx"
      let body ← go (Ref.stepType τ (.inr e)) rest (.inr (.var idxTy (.free y) @@ pos) :: seen)
      pure ⟨[], .with y idxTy true e body @@ pos⟩

/-- Threads `parRef` across every `(rᵢ, vᵢ)` pair in turn (`r1` outermost, matching the
left-to-right `𝒞_par(r1,f1) … 𝒞_par(rn,fn)` nesting above) to bind *every* `Ref`'s own index temps
first — `k` only runs once all `n` are reconstructed, so no `rᵢ`'s index expression is ever
evaluated after an earlier `rⱼ`'s assignment has already run (the entire point of hoisting: every
read must see the pre-assignment state, not just each ref's own). -/
private partial def parRefsAll (pos : SourceSpan) (rs : List (Ref × String))
    (k : List (Ref × String) → m (Block false)) : m (Block false) :=
  match rs with
  | [] => k []
  | (r, v) :: rest => parRef pos r λ r' => parRefsAll pos rest λ rest' => k ((r', v) :: rest')

/-- The final `r1' := v1; …; rn' := vn` sequence, built only after every `Ref` in the list has
already had its own index temps bound by `parRefsAll`. -/
private def buildAssigns (pos : SourceSpan) : List (Ref × String) → Block false
  | [] => unreachable! -- only ever called from `buildParChain` with `pairs.length ≥ 2`
  | [(r, v)] => ⟨[], .assign [(r, .var (Ref.resultType r) (.free v) @@ pos)] @@ pos⟩
  | (r, v) :: rest =>
    let ⟨begin, «end»⟩ := buildAssigns pos rest
    ⟨(.assign [(r, .var (Ref.resultType r) (.free v) @@ pos)] @@ pos) :: begin, «end»⟩

/-- The outer `with v1=e1 do … with vn=en do body` chain, `v1` outermost — same nested-`⟨[], ·⟩`
idiom `Desugarer/PlusCal.lean`'s `buildWithChain` already uses for a multi-binder surface
`with`. -/
private def valueChain (pos : SourceSpan) : List (String × Ref × Expression) → Block false → Statement false
  | [], _ => unreachable! -- only ever called from `buildParChain` with `pairs.length ≥ 2`
  | [(v, r, e)], body => .with v (Ref.resultType r) true e body @@ pos
  | (v, r, e) :: rest, body => .with v (Ref.resultType r) true e ⟨[], valueChain pos rest body⟩ @@ pos

/-- `𝒞_par` proper, applied to one parallel-assignment statement's own `(Ref × Expr)` list
(`pairs.length ≥ 2` — the length-≤1 case is handled by `Statement.par` before reaching here).
Every node this builds is a rewrite of the one original parallel assignment, so all of them are
registered at that statement's own span (`pos`). -/
private def buildParChain (pos : SourceSpan) (pairs : List (Ref × Expression)) : m (Statement false) := do
  let named ← pairs.mapM λ (r, e) ↦ (·, r, e) <$> freshName "val"
  let body ← parRefsAll pos (named.map λ (v, r, _) ↦ (r, v)) (pure <| buildAssigns pos ·)
  pure (valueChain pos named body)

mutual
  /-- `𝒞_par` over a single statement — an ordinary congruence except at `.assign`, the one case
  this pass actually rewrites. -/
  partial def ComputablePlusCal.Statement.par {b} (s : Statement b) : m (Statement b) :=
    match_source s with
    | .goto l, pos => pure (.goto l @@ pos)
    | .skip, pos => pure (.skip @@ pos)
    | .print e, pos => pure (.print e @@ pos)
    | .assign pairs, pos =>
      if pairs.length ≤ 1 then pure (.assign pairs @@ pos) else buildParChain pos pairs
    | .await e, pos => pure (.await e @@ pos)
    | .assert e, pos => pure (.assert e @@ pos)
    | .send c e, pos => pure (.send c e @@ pos)
    | .multicast c filter, pos => pure (.multicast c filter @@ pos)
    | .receive c r coe, pos => pure (.receive c r coe @@ pos)
    | .with var ann «=|∈» val B, pos => (.with var ann «=|∈» val · @@ pos) <$> Block.par B
    | .either branches, pos => (.either · @@ pos) <$> Branches.par branches
    | .if cond B₁ B₂, pos => (.if cond · · @@ pos) <$> Block.par B₁ <*> Block.par B₂
    | .while cond B, pos => (.while cond · @@ pos) <$> Block.par B

  partial def ComputablePlusCal.Block.par {b} : Block b → m (Block b)
    | ⟨begin, «end»⟩ => do
      let begin' ← begin.mapM Statement.par
      let end' ← Statement.par «end»
      pure ⟨begin', end'⟩

  partial def ComputablePlusCal.Branches.par {b} : Branches b → m (Branches b)
    | .either B => .either <$> Block.par B
    | .or B rest => .or <$> Block.par B <*> Branches.par rest
end

/-- `𝒞_par` over a whole algorithm: applied per `(label, Block)` pair, across every thread of
every process. -/
def ComputablePlusCal.Algorithm.par (algo : ComputablePlusCal.Algorithm) : m ComputablePlusCal.Algorithm := do
  let processes ← algo.processes.mapM λ p ↦ do
    let threads ← p.threads.mapM (·.mapM λ (label, block) ↦ (label, ·) <$> Block.par block)
    pure ({ p with threads } @@ posOf p)
  pure ({ algo with processes } @@ posOf algo)

end
