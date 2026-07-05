import Core.TypedTLAPlus.Syntax

/-!
  `Coercion` — a term-level witness of `<:` (§5.3), realized as `Expr → Expr`. Lives in `Core/`
  (not `Elaborator/`, despite being almost entirely the type checker's own concept) purely for
  layering reasons: `Core/CorePlusCal/Syntax.lean`'s `Statement.receive` needs to carry a
  `Coercion` field (`PLAN.md` §5.3's `[Receive]` note — the channel-element-vs-reference-type
  upcast has no expression to apply itself to at check time, so it's stored on the statement node
  and only actually applied once `Guarded2Network` turns a `receive` into a concrete buffered
  read), and `Core/` must never depend on `Elaborator/` (the reverse of every pass's own
  direction, and an outright import cycle here specifically, since `Elaborator/PlusCal.lean`
  itself imports `Core/CorePlusCal/Syntax.lean`). `Elaborator/Subtyping.lean` still owns
  everything *about* `Coercion` (`subtype`'s three-outcome judgment, every structural/axiom
  coercion built from one) — this file only owns the type itself and its `Repr` instance, the two
  things `CorePlusCal.Statement.receive`'s own `deriving Repr` needs to exist beforehand.

  **`Repr Coercion` is a placeholder, not a real rendering.** `Coercion.fn` wraps an opaque
  `Expr → Expr` closure, which has no meaningful `Repr` at all — `-d dump-typed` output for a
  `receive` statement's coercion is just the literal string `"<coercion>"`, not a real
  pretty-print of what the coercion actually does. Good enough for "was one computed at all," not
  enough to inspect what it is; a real rendering would need to reify a coercion into inspectable
  data (e.g. which axiom/structural rule fired) rather than a closure, which
  `Elaborator/Subtyping.lean` doesn't currently do.
-/

namespace TypedTLAPlus

/-- Checked TLA⁺ expressions at the checker's own output type — what a `Coercion` transforms
(`Elaborator/Subtyping.lean` reuses this same abbrev rather than defining its own copy, now that
it lives here so `CorePlusCal.Syntax` can reference `Coercion` without depending on
`Elaborator`). -/
abbrev Expr := Expression Typ

/--
  A coercion, witnessing `τ <: τ'` at the term level (the thesis has no such witness — this
  project's own addition, `PLAN.md` §5.3). `.id` is its own constructor rather than folding
  identity into `.fn (λ e ↦ e)` so structural subtyping rules can cheaply detect "nothing to wrap"
  by pattern matching alone.
-/
inductive Coercion : Type
  /-- No wrapping needed — the source expression is already of the target type as-is. -/
  | id
  /-- A genuine wrapping transformation, turning an expression of the source type into one of the
  target type. -/
  | fn (f : Expr → Expr)

/-- Apply a coercion to an already-elaborated expression — "applying it at a use site is just
ordinary function application," `PLAN.md` §5.3. -/
def Coercion.apply : Coercion → Expr → Expr
  | .id, e => e
  | .fn f, e => f e

/-- A placeholder rendering (module doc) — needed only so `CorePlusCal.Statement`'s `deriving
Repr` (which now has a `receive` case carrying an `Option Coercion`) has something to call. -/
instance : Repr Coercion := ⟨fun _ _ => "<coercion>"⟩

end TypedTLAPlus
