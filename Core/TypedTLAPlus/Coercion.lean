import Core.TypedTLAPlus.Syntax

/-!
  `Coercion` — a term-level witness of `<:`, realized as `Expr → Expr`. Lives in `Core/` (not
  `Elaborator/`) so that `CorePlusCal.Statement.receive` can carry a `Coercion` field without
  `Core/` depending on `Elaborator/`. `Elaborator/Subtyping.lean` owns everything *about*
  `Coercion` (the subtyping judgment, every coercion built from one); this file only owns the
  type itself and its `Repr` instance.

  `Repr Coercion` is a placeholder, not a real rendering: `-d dump-typed` output for a `receive`
  statement's coercion is just the literal string `"<coercion>"`.
-/

namespace TypedTLAPlus

/-- Checked TLA⁺ expressions at the checker's own output type — what a `Coercion` transforms. -/
abbrev Expr := Expression Typ

/--
  A coercion, witnessing `τ <: τ'` at the term level. `.id` is its own constructor rather than
  folding identity into `.fn (λ e ↦ e)` so structural subtyping rules can cheaply detect "nothing
  to wrap" by pattern matching alone.
-/
inductive Coercion : Type
  /-- No wrapping needed — the source expression is already of the target type as-is. -/
  | id
  /-- A genuine wrapping transformation, turning an expression of the source type into one of the
  target type. -/
  | fn (f : Expr → Expr)

/-- Apply a coercion to an already-elaborated expression. -/
def Coercion.apply : Coercion → Expr → Expr
  | .id, e => e
  | .fn f, e => f e

/-- A placeholder rendering (module doc). -/
instance : Repr Coercion := ⟨fun _ _ => "<coercion>"⟩

end TypedTLAPlus
