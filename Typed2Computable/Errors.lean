module

public import Common.Errors
public import Core.TypedTLAPlus.Syntax

public section

/-! `Typed2Computable`'s diagnostics — one named error variant per genuinely new restriction this
pass introduces beyond `WellFormedness`, plus a defense-in-depth catch-all for inputs that should
be unreachable by construction. -/

/-- Which non-computable construct `ComputableError.notComputable` reports — the two
`TypedTLAPlus.Expression` constructors `Core/ComputableTLAPlus/Syntax.lean` has no counterpart
for: `fnSet` (`[A -> B]`, the set of *all* functions from `A` to `B`) and `recordSet` (`[a : A,
...]`, the set of all records shaped that way) — both denote sets with no finite runtime
representation. -/
inductive NonComputableConstruct : Type
  /-- `[A -> B]`, the set of *all* functions from `A` to `B`. -/
  | fnSet
  /-- `[a : A, ...]`, the set of all records shaped that way. -/
  | recordSet
  deriving Repr, Inhabited, BEq

/-- `Typed2Computable`'s errors. -/
inductive ComputableError : Type
  /-- The algorithm references `fnSet`/`recordSet` — genuinely not computable under this
  compiler's finite-sets assumption, not previously enforced by `WellFormedness` (whose checks
  ban temporal/action operators and unbounded quantifiers, not these). -/
  | notComputable (pos : SourceSpan) (construct : NonComputableConstruct)
  /-- Defense-in-depth: a construct `WellFormedness/Restrictions.lean`'s check 3 already
  guarantees can't be transitively-reachable-from-the-algorithm (an unbounded `forall`/`exists`/
  `choose` domain, or a bare `fforall`/`eexists`/`stutter`) still turned up, or a pending
  coercion (`mvar`) survived past the type checker's own output despite `Core/TypedTLAPlus/
  Syntax.lean`'s own guarantee that none do. No proof of unreachability exists for any of these
  yet — just facts established by earlier passes — so this stays a runtime check, not
  `absurd`/`nomatch`. -/
  | internalInvariantViolated (pos : SourceSpan) (description : String)
  deriving Repr, Inhabited, BEq

instance : CompilerDiagnostic ComputableError String where
  isError := true
  code
    | .notComputable .. => Diagnostics.notComputable.code
    | .internalInvariantViolated .. => Diagnostics.computableInternalInvariant.code
  posOf
    | .notComputable pos _ => pos
    | .internalInvariantViolated pos _ => pos
  msgOf
    | .notComputable _ .fnSet =>
      "`[A -> B]` (the set of all functions from `A` to `B`) is not computable under this compiler's finite-sets assumption."
    | .notComputable _ .recordSet =>
      "`[a : A, ...]` (the set of all records shaped that way) is not computable under this compiler's finite-sets assumption."
    | .internalInvariantViolated _ description =>
      s!"Internal invariant violated: {description}. This should be unreachable — please report this as a bug."

end
