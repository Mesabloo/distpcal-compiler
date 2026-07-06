import Elaborator.Subtyping

open TypedTLAPlus (Typ MVarId Expr)

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- Needed for the `partial def`s below to type-check at all (an arbitrary `m` isn't otherwise
known nonempty). -/
local instance : Inhabited (m Expr) := ⟨pure default⟩

/--
  `PLAN.md` §5.3's single end-of-check defaulting point, applied to one already-elaborated
  expression: eliminates every `mvar` node inside `e`, walking bottom-up so a nested `mvar` is
  resolved before an outer one that might wrap it. Every metavariable `n` a `mvar` node names
  reached `[Subtype]`'s `.pending` case, which fires only when `n` is still unresolved *and* is
  the check's own *source* type — given `specializeOperator` mints a fresh metavariable per
  operator-call use and each one is only ever the source of exactly the one `subtype` call that
  builds its own `mvar` wrapper, `n`'s `pendingUpperBounds` holds, in every case reachable from
  this checker's own code today, exactly the one bound recorded at that call — there is no
  separate site-tracking table to consult, just this existing context. Guarded rather than
  silently assumed: a metavariable with more than one recorded bound would need genuine per-site
  tracking to substitute soundly (no concrete program has been found that produces one), so that
  case is a loud `todo`, not a guess. A metavariable with *no* recorded bound at all is a real,
  named error — it was never constrained by anything during checking.

  **Only eliminates `Expression.mvar` wrapper nodes — doesn't itself touch `Typ.mvar`
  occurrences embedded *inside* a node's own stored type field.** Those are resolved by
  `resolveMVars` below, as a second pass over this pass's output.
-/
partial def resolveExprMVars (e : Expr) : m Expr := match_source e with
  | .var v τ, pos => return .var v τ @@ pos
  | .nat n, pos => return .nat n @@ pos
  | .str s, pos => return .str s @@ pos
  | .true, pos => return .true @@ pos
  | .false, pos => return .false @@ pos
  | .opCall f args, pos => return .opCall (← resolveExprMVars f) (← args.mapM resolveExprMVars) @@ pos
  | .forall x τ dom body, pos =>
    return .forall x τ (← dom.mapM resolveExprMVars) (← resolveExprMVars body) @@ pos
  | .exists x τ dom body, pos =>
    return .exists x τ (← dom.mapM resolveExprMVars) (← resolveExprMVars body) @@ pos
  | .fforall x τ body, pos => return .fforall x τ (← resolveExprMVars body) @@ pos
  | .eexists x τ body, pos => return .eexists x τ (← resolveExprMVars body) @@ pos
  | .choose x τ dom body, pos =>
    return .choose x τ (← dom.mapM resolveExprMVars) (← resolveExprMVars body) @@ pos
  | .set es τ, pos => return .set (← es.mapM resolveExprMVars) τ @@ pos
  | .collect x τ dom pred, pos =>
    return .collect x τ (← resolveExprMVars dom) (← resolveExprMVars pred) @@ pos
  | .map' body x τ dom, pos => return .map' (← resolveExprMVars body) x τ (← resolveExprMVars dom) @@ pos
  | .fnCall f idx, pos => return .fnCall (← resolveExprMVars f) (← resolveExprMVars idx) @@ pos
  | .fn x τ dom body, pos => return .fn x τ (← resolveExprMVars dom) (← resolveExprMVars body) @@ pos
  | .fnSet dom cod, pos => return .fnSet (← resolveExprMVars dom) (← resolveExprMVars cod) @@ pos
  | .record fields, pos =>
    return .record (← fields.mapM λ (τ, x, e) ↦ return (τ, x, ← resolveExprMVars e)) @@ pos
  | .recordSet fields, pos =>
    return .recordSet (← fields.mapM λ (τ, x, e) ↦ return (τ, x, ← resolveExprMVars e)) @@ pos
  | .except e upds, pos => do
    let e' ← resolveExprMVars e
    let upds' ← upds.mapM λ (path, newVal) ↦ do
      let path' ← path.mapM λ
        | .inl field => return (Sum.inl field : String ⊕ Expr)
        | .inr idx => return .inr (← resolveExprMVars idx)
      return (path', ← resolveExprMVars newVal)
    return .except e' upds' @@ pos
  | .recordAccess e x, pos => return .recordAccess (← resolveExprMVars e) x @@ pos
  | .tuple es, pos => return .tuple (← es.mapM λ (τ, e) ↦ return (τ, ← resolveExprMVars e)) @@ pos
  | .seq es τ, pos => return .seq (← es.mapM resolveExprMVars) τ @@ pos
  | .if c t f, pos => return .if (← resolveExprMVars c) (← resolveExprMVars t) (← resolveExprMVars f) @@ pos
  | .case branches other, pos => do
    let branches' ← branches.mapM λ (p, e) ↦ return (← resolveExprMVars p, ← resolveExprMVars e)
    return .case branches' (← other.mapM resolveExprMVars) @@ pos
  | .stutter e a, pos => return .stutter (← resolveExprMVars e) (← resolveExprMVars a) @@ pos
  | .mvar n e, pos => do
    let e' ← resolveExprMVars e
    match ← assigned? n with
    -- Shouldn't happen per the doc above — defensive fallback: `n`'s value is already known,
    -- nothing further to resolve at this site.
    | some _ => return e'
    | none => match ← pendingUpperBounds n with
      | [] => throw (.unconstrainedMetavariable pos)
      | [b] => do
        assignMVar n b
        match ← subtype b b with
        | .success coe => return coe.apply e'
        | .pending _ | .failure => return e' -- unreachable: `b <: b` always succeeds reflexively
      | _ :: _ :: _ =>
        throw (.todo pos
          "metavariable with more than one recorded upper bound — needs per-site tracking, not seen in practice yet")

private partial def resolveTypeMVars (pos : SourceSpan) : Typ → m Typ
  | .mvar n => do
    match ← assigned? n with
    | some τ' => resolveTypeMVars pos τ'
    | none => throw (.unconstrainedMetavariable pos)
  | .var a => return .var a
  | .bool => return .bool
  | .int => return .int
  | .str => return .str
  | .address => return .address
  | .const c => return .const c
  | .function dom rng => return .function (← resolveTypeMVars pos dom) (← resolveTypeMVars pos rng)
  | .set τ => return .set (← resolveTypeMVars pos τ)
  | .seq τ => return .seq (← resolveTypeMVars pos τ)
  | .channel τ => return .channel (← resolveTypeMVars pos τ)
  | .tuple τs => return .tuple (← τs.mapM (resolveTypeMVars pos))
  | .operator τs τ => return .operator (← τs.mapM (resolveTypeMVars pos)) (← resolveTypeMVars pos τ)
  | .record fs => return .record (← fs.mapM λ (x, τ) ↦ return (x, ← resolveTypeMVars pos τ))

/-- `PLAN.md` §5.3's single end-of-check defaulting point, as actually exposed to callers:
`resolveExprMVars` above eliminates every `Expression.mvar` wrapper node (assigning whatever
metavariables it names along the way), then this second pass walks the result once more
resolving any `Typ.mvar` left behind in a stored type field. Reuses `Expression.traverse`
rather than hand-rolling a second full walk, at the cost of every occurrence sharing one
position (`e`'s own, for the rare unconstrained-metavariable error) instead of a precise
per-occurrence one. -/
partial def resolveMVars (e : Expr) : m Expr := do
  let e' ← resolveExprMVars e
  TypedTLAPlus.Expression.traverse (resolveTypeMVars (posOf e')) e'
