import Elaborator.Monad

open TypedTLAPlus (Typ MVarId)

/-- Every distinct `Typ.var` name occurring anywhere in a type. `partial`: recursion over
nested `List Typ`/`List (String × Typ)` fields isn't visibly structurally decreasing to Lean. -/
private partial def typeFreeVars : Typ → List String
  | .var a => [a]
  | .bool | .int | .str | .address | .const _ | .mvar _ => []
  | .function dom rng => typeFreeVars dom ++ typeFreeVars rng
  | .set τ | .seq τ | .channel τ => typeFreeVars τ
  | .tuple τs => τs.flatMap typeFreeVars
  | .operator τs τ => τs.flatMap typeFreeVars ++ typeFreeVars τ
  | .record fs => fs.flatMap (typeFreeVars ∘ Prod.snd)

/-- Substitute every `Typ.var` named in `σ` by the metavariable `σ` maps it to, leaving anything
else (including `Typ.var`s *not* in `σ`) unchanged. -/
private partial def substTypeVars (σ : List (String × MVarId)) : Typ → Typ
  | .var a => match σ.lookup a with
    | some n => .mvar n
    | none => .var a
  | .bool => .bool
  | .int => .int
  | .str => .str
  | .address => .address
  | .const c => .const c
  | .mvar n => .mvar n
  | .function dom rng => .function (substTypeVars σ dom) (substTypeVars σ rng)
  | .set τ => .set (substTypeVars σ τ)
  | .seq τ => .seq (substTypeVars σ τ)
  | .channel τ => .channel (substTypeVars σ τ)
  | .tuple τs => .tuple (τs.map (substTypeVars σ))
  | .operator τs τ => .operator (τs.map (substTypeVars σ)) (substTypeVars σ τ)
  | .record fs => .record (fs.map λ (x, τ) ↦ (x, substTypeVars σ τ))

variable {m : Type → Type} [Monad m] [MonadElaborator m]

/-- Freshen every distinct `Typ.var` in an operator's parameter/return types into its own
metavariable. -/
def specializeOperator (params : List Typ) (ret : Typ) : m (List Typ × Typ) := do
  let vars := ((ret :: params).flatMap typeFreeVars).eraseDups
  let σ ← vars.mapM λ v ↦ return (v, ← mkFreshMVar)
  return (params.map (substTypeVars σ), substTypeVars σ ret)
