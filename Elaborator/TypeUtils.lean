module

public import Elaborator.Monad

public section

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

/-- Freshen every distinct `Typ.var` in `τ` into its own metavariable, sharing one substitution
across all occurrences — e.g. for an `.operator params ret`-shaped `τ`, `params` and `ret` are
freshened consistently by the same substitution. Used at every `Γ`-reference to a *scheme*
binding (`Elaborator/Monad.lean`'s `Binding.isScheme`, `Elaborator/Expressions.lean`'s
`inferExpr`'s `.var` case) — the checker's one instantiation point; `.opCall` needs no separate
specialization step since the callee's type is already specialized once looked up. -/
def specializeType (τ : Typ) : m Typ := do
  let vars := (typeFreeVars τ).eraseDups
  let σ ← vars.mapM λ v ↦ return (v, ← mkFreshMVar)
  return substTypeVars σ τ

end
