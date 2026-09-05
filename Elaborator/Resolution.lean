module

public import Elaborator.Subtyping

public section

open TypedTLAPlus (Typ MVarId Expr)

variable {m : Type → Type} [Monad m] [MonadElaborator m] [MonadPendingBounds m]

/-- Needed for the `partial def`s below to type-check at all (an arbitrary `m` isn't otherwise
known nonempty). -/
private local instance {α} [Inhabited α] : Inhabited (m α) := ⟨pure default⟩

/--
  Eliminates every `mvar` node inside `e`, walking bottom-up so a nested `mvar` resolves before
  an outer one that might wrap it. Each metavariable defaults to its recorded upper bound, if
  there's exactly one; no recorded bound is an unconstrained-metavariable error, and more than one
  is unsupported (would need per-site tracking to substitute soundly).

  Only eliminates `Expression.mvar` wrapper nodes, not `Typ.mvar` occurrences embedded in a node's
  stored type field — those are resolved by `resolveMVars` below, as a second pass.
-/
partial def resolveExprMVars (e : Expr) : m Expr := match_source e with
  | .var τ o, pos => return .var τ o @@ pos
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
  | .map' body x τ cod dom, pos =>
    return .map' (← resolveExprMVars body) x τ cod (← resolveExprMVars dom) @@ pos
  | .fnCall f fnTyp idx, pos =>
    return .fnCall (← resolveExprMVars f) fnTyp (← resolveExprMVars idx) @@ pos
  | .fn x τ cod dom body, pos =>
    return .fn x τ cod (← resolveExprMVars dom) (← resolveExprMVars body) @@ pos
  | .fnSet dom cod, pos => return .fnSet (← resolveExprMVars dom) (← resolveExprMVars cod) @@ pos
  | .record fields, pos =>
    return .record (← fields.mapM λ (τ, x, e) ↦ return (τ, x, ← resolveExprMVars e)) @@ pos
  | .recordSet fields, pos =>
    return .recordSet (← fields.mapM λ (τ, x, e) ↦ return (τ, x, ← resolveExprMVars e)) @@ pos
  | .except e τ upds, pos => do
    let e' ← resolveExprMVars e
    let upds' ← upds.mapM λ (path, newVal) ↦ do
      let path' ← path.mapM λ
        | .inl field => return (Sum.inl field : String ⊕ Expr)
        | .inr idx => return .inr (← resolveExprMVars idx)
      return (path', ← resolveExprMVars newVal)
    return .except e' τ upds' @@ pos
  | .recordAccess e x, pos => return .recordAccess (← resolveExprMVars e) x @@ pos
  | .tuple es, pos => return .tuple (← es.mapM λ (τ, e) ↦ return (τ, ← resolveExprMVars e)) @@ pos
  | .seq es τ, pos => return .seq (← es.mapM resolveExprMVars) τ @@ pos
  | .if c t f τ, pos =>
    return .if (← resolveExprMVars c) (← resolveExprMVars t) (← resolveExprMVars f) τ @@ pos
  | .case branches other τ, pos => do
    let branches' ← branches.mapM λ (p, e) ↦ return (← resolveExprMVars p, ← resolveExprMVars e)
    return .case branches' (← other.mapM resolveExprMVars) τ @@ pos
  | .stutter e a, pos => return .stutter (← resolveExprMVars e) (← resolveExprMVars a) @@ pos
  | .mvar n e, pos => do
    let e' ← resolveExprMVars e
    match ← assigned? n with
    -- Defensive fallback: `n` is already resolved, nothing further to do at this site.
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
          "metavariable with more than one recorded upper bound — unsupported")

/-- Substitutes every already-assigned metavariable inside `τ`, recursing into whatever
`onUnassigned` returns for one that isn't. Shared by `resolveTypeMVars` (throws: every
metavariable must be resolved by the time a declaration finishes checking) and
`resolveTypeMVarsForDisplay` below (best-effort: an unresolved one is left as `Typ.mvar n`, since
it's only used to make a *thrown* error's carried types as concrete as possible). -/
private partial def resolveTypeMVarsWith (onUnassigned : MVarId → m Typ) : Typ → m Typ
  | .mvar n => do
    match ← assigned? n with
    | some τ' => resolveTypeMVarsWith onUnassigned τ'
    | none => onUnassigned n
  | .var a => return .var a
  | .bool => return .bool
  | .int => return .int
  | .str => return .str
  | .address => return .address
  | .const c => return .const c
  | .function dom rng =>
    return .function (← resolveTypeMVarsWith onUnassigned dom) (← resolveTypeMVarsWith onUnassigned rng)
  | .set τ => return .set (← resolveTypeMVarsWith onUnassigned τ)
  | .seq τ => return .seq (← resolveTypeMVarsWith onUnassigned τ)
  | .channel τ => return .channel (← resolveTypeMVarsWith onUnassigned τ)
  | .tuple τs => return .tuple (← τs.mapM (resolveTypeMVarsWith onUnassigned))
  | .operator τs τ =>
    return .operator (← τs.mapM (resolveTypeMVarsWith onUnassigned)) (← resolveTypeMVarsWith onUnassigned τ)
  | .record fs => return .record (← fs.mapM λ (x, τ) ↦ return (x, ← resolveTypeMVarsWith onUnassigned τ))

private def resolveTypeMVars (pos : SourceSpan) : Typ → m Typ :=
  resolveTypeMVarsWith λ _ ↦ throw (.unconstrainedMetavariable pos)

/-- Best-effort metavariable substitution for a `Typ` about to be embedded in a *thrown*
`TCError`: an already-resolved metavariable (e.g. pinned by an earlier operand in the same call)
is substituted so the error shows a concrete type instead of a raw `?n`; one that's never been
constrained is left as `Typ.mvar n` (rendered `?n`) rather than erroring — display only, not a
checking-correctness concern. -/
def resolveTypeMVarsForDisplay : Typ → m Typ :=
  resolveTypeMVarsWith (pure ∘ .mvar)

/-- Closes out an elaborated expression: `resolveExprMVars` above eliminates every
`Expression.mvar` wrapper node (assigning whatever metavariables it names along the way), then
this second pass walks the result once more resolving any `Typ.mvar` left behind in a stored
type field. -/
partial def resolveMVars (e : Expr) : m Expr := do
  let e' ← resolveExprMVars e
  TypedTLAPlus.Expression.traverse (resolveTypeMVars (posOf e')) e'

end
