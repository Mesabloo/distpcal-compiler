# Project layout

Quick map of repo, directory by directory. Not exhaustive — sample of files per directory,
enough to orient. See `PLAN.md` for what each pass actually do. Keep this file in sync
whenever file get added, removed, or moved (`CLAUDE.md`).

## `Common/`
Shared infrastructure used across whole pipeline.
- `Errors.lean` — shared error-reporting typeclasses.
- `Position.lean` — `SourceSpan`/`Located` position tagging.
- `Flags.lean` — CLI flag definitions.
- `Fresh.lean` — hygienic fresh-name generation effect class, used by any pass that
  introduce variable that must not collide with user-written names.
- `Pretty.lean` — `Std.Format` combinators (`infixl`/`infixr`/`infix`/`prefix` with
  precedence-aware parenthesization) shared by various `Pretty.lean` pretty-printers.

## `Extra/`
Vendored, generic (non-domain-specific) data-structure lemmas and instances, reused as-is
from prior art per `CLAUDE.md`.
- `List.lean`, `AssocList.lean`, `Finmap.lean`, `HashMap.lean`, `AList.lean`, `Array.lean`,
  `Fin.lean`, `Finset.lean`, `Nat.lean`, `Option.lean`, `Prod.lean`, `Prop.lean`, `Rel.lean`,
  `Set.lean`, `String.lean`, `Substring.lean`, `Sum.lean`, `Monad.lean` — container/type
  helpers.
- `Mathlib/Tactic/DeriveTraversable.lean` — mechanical `Traversable` derivation.

## `Parser_/`
Lexer/parser, ported from `distpcal-compiler`'s local `Parser_/` (`PLAN.md` §5.1).
- `PlusCal.lean` — PlusCal statement/process parser.
- `TLAPlus.lean` — TLA+ expression parser.
- `Common.lean` — parser combinators shared by both.
- `Monad.lean` — parser's monad stack.
- `Tokens/PlusCal.lean`, `Tokens/TLAPlus.lean` — token definitions.
- `Annotations.lean` — `@type`/`@parameter` annotation parsing.

## `Core/`
- `Declaration.lean` — `Declaration`/`Module`, the shape of a TLA⁺ declaration/module,
  parametrized over the expression former `E` and shared by `SurfaceTLAPlus`/`CoreTLAPlus`/
  `TypedTLAPlus` (each recovers its own via `abbrev`) — used to be duplicated verbatim
  three times.

## `Core/SurfacePlusCal/`, `Core/SurfaceTLAPlus/`
Surface AST — what parser produce, annotations still attached.
- `Syntax.lean` (each) — the AST types.
- `Pretty.lean` (each) — pretty-printers, used for `-d dump-cst`-style debugging.

## `Core/CorePlusCal/`, `Core/CoreTLAPlus/`
Desugared AST — annotations stripped into concrete fields (types, mailbox, parameter flag).
- `Syntax.lean` (each) — the AST types, shared `α`/`β` parameters across `Statement`,
  `Process`, `Declarations`, etc.

## `Core/TypedPlusCal/`, `Core/TypedTLAPlus/`
Typed AST — `Elaborator`'s output, every annotation resolved to concrete `Typ` (no more
`Option Typ`/metavariables).
- `Syntax.lean` (`TypedTLAPlus/`) — the AST types.
- `Syntax.lean` (`TypedPlusCal/`) — `ElaboratedPlusCal.{Ref,MulticastFilter,Statement,Block,
  Branches,Declarations,Process,Algorithm}`, generic over `(τ ε : Type)`, plus `TypedPlusCal`'s
  own pin of that layer at `TypedTLAPlus.Typ`/`Expression` — the shared generic layer
  `Core/ComputablePlusCal/Syntax.lean` pins again at `ComputableTLAPlus`'s types instead.
- `Coercion.lean` (`TypedTLAPlus/` only) — term-level coercions inserted by subtyping (`<:`).
- `Builtins.lean` (`TypedTLAPlus/` only) — the shared builtin-operator table (`BuiltinOp`,
  `builtinOpOf?`, `Expression.recognizeBuiltin?`), keyed by `(Origin, name)`; also
  `reservedTemporalActionNames`. Any pass downstream of type checking recognizing a builtin
  call reuses this instead of keeping its own list.

## `Core/ComputableTLAPlus/`, `Core/ComputablePlusCal/`
`Typed2Computable`'s output AST — `TypedTLAPlus`/`TypedPlusCal` minus the handful of
constructs with no finite runtime representation (`PLAN.md` §5.3).
- `Syntax.lean` (`ComputableTLAPlus/`) — `Expression`, missing `fforall`/`eexists`/`stutter`/
  `mvar`/`fnSet`/`recordSet` relative to `TypedTLAPlus.Expression`; `forall`/`exists`/
  `choose`'s domain is a plain `Expression`, not `Option (Expression)`. `Typ`/`Origin` reused
  directly from `TypedTLAPlus` (not re-copied).
- `Syntax.lean` (`ComputablePlusCal/`) — pins `ElaboratedPlusCal` (`Core/TypedPlusCal/
  Syntax.lean`) at `ComputableTLAPlus`'s types.

## `Desugarer/`
Surface → Core lowering (`PLAN.md` §3.2).
- `PlusCal.lean` — statement/process desugaring, `with`-chain building, well-labelledness
  and wellformedness checks (conflicting assignments, with-bound writes).
- `TLAPlus.lean` — expression desugaring, unary `fnCall`/`except`/`Ref` collapsing.
- `Errors.lean` — `DesugarError` variants.
- `Monad.lean` — desugarer's monad stack.

## `WellFormedness/`
Phase 7 module (`PLAN.md` §5.2a) — well-labelledness, well-scopedness, and the
no-shared-memory/no-bare-temporal restrictions, run against a `TypedModule`'s own
`pcalAlgorithm` right after type checking succeeds (`Driver/Modules.lean`). Assignment-conflict
checking (one of §5.2a's original three checks) still lives ad hoc in `Desugarer/PlusCal.lean`,
ahead of its own phase slot, and isn't duplicated here.
- `Errors.lean` — `WellFormednessError` variants.
- `Monad.lean` — `MonadForeignLookup` (fetch a module's checked declarations by name; the one
  seam into `Driver/`'s module cache), plus generic `StateT`/`ExceptT` lift instances for it.
- `Reachability.lean` — the shared reachability walk, reused by `Restrictions.lean` below and
  by `Typed2Computable`: `ResolvedDecl`/`Decl.resolve`/`resolveInModule` (name resolution
  against a module's declaration list), `ReachabilityClosure` (every `(module, name)` pair
  resolved so far), `Expression`/`Statement`/`Algorithm.walkReachable` (the traversal itself,
  each taking thin per-node callbacks — `Restrictions.lean` supplies its real checks,
  `Typed2Computable` supplies no-ops and just keeps the closure).
- `Labelling.lean` — every `goto` targets a label its process actually defines, or `"Done"`;
  `"Done"` itself is never redefined.
- `WellScoped.lean` — no duplicate/shadowed names in any scope (global, process-local,
  block-local `with`); also `CorePlusCal.WellScoped`, a fresh `Prop` (not yet proved or used)
  modeling the same discipline for a later `GuardedPlusCal` preservation lemma.
- `Declarations.lean` — structural/type-shape checks: no Channel-typed `variables` entry, no
  process-local `channels`/`fifos` (defense-in-depth), no algorithm-level `variables`.
- `Restrictions.lean` — supplies `Reachability.lean`'s shared walk its actual checks (as
  `visitStatement`/`visitExpr` callbacks): no channel value inside an ordinary expression (or
  as `assign`'s/`receive`'s non-channel `Ref` positions, `Statement.checkRefRestrictions`), no
  reference to a module-level `VARIABLE`, no bare/transitive temporal or action operator, no
  unbounded quantifier (`Expression.checkNode`) — transitively, through every operator/
  function the algorithm calls.
- `WellFormedness.lean` — ties the four checks together; `TypedTLAPlus.Module.checkWellFormed`
  is the one entry point `Driver/Modules.lean` calls.

## `Typed2Computable/`
`TypedTLAPlus`/`TypedPlusCal` → `ComputableTLAPlus`/`ComputablePlusCal` (`PLAN.md` §5.3),
run against a `TypedModule` right after well-formedness succeeds (`Driver/Modules.lean`).
- `Errors.lean` — `ComputableError` variants (`notComputable` — `fnSet`/`recordSet`;
  `internalInvariantViolated` — defense-in-depth for constructs earlier passes already
  guarantee can't occur here).
- `TLAPlus.lean` — `TypedTLAPlus.Expression.toComputable`, structural per-constructor
  translation.
- `PlusCal.lean` — the same, over `Ref`/`Statement`/`Block`/`Branches`/`Declarations`/
  `Process`/`Algorithm`, delegating every leaf expression to `TLAPlus.lean`'s translation.
- `Typed2Computable.lean` — the entry point (`TypedTLAPlus.Module.toComputable`): collects
  the reachability closure from the algorithm (`WellFormedness/Reachability.lean`'s shared
  walk, no-op callbacks), drops builtin-sourced entries, translates the rest plus the
  algorithm itself, and returns the flattened output module.

## `Elaborator/`
Bidirectional type checker (`PLAN.md` §3.1, ch. 3.1 of thesis).
- `Monad.lean` — checker's effects: `Γ`, metavariable context, error reporting, fresh names.
- `Context.lean` — `Γ`-extension helpers (`extend`/`extendAll`).
- `Subtyping.lean` — `<:`, `lub`, `glb`, term-level coercion, direction-aware metavariable
  solving (in place of literal `Specialize` rule).
- `Resolution.lean` — metavariable resolution (`resolveMVars`), defaulting each to its
  recorded upper bound.
- `TypeUtils.lean` — type-level helpers (e.g. free-variable collection over `Typ`).
- `Expressions.lean` — bidirectional expression checking, `checkExpr`/`inferExpr`.
- `Declarations.lean` — declaration/module-level checking, threading `Γ` across
  `CONSTANTS`/`VARIABLES`/`ASSUME`/operator/function definitions, plus `builtinContext`.
- `PlusCal.lean` — statement/process/algorithm checking, `CorePlusCal` → `TypedPlusCal`.
- `Elaborator.lean` — ties it together: `CoreTLAPlus.Module.check`, `Module.runChecker`.
- `Errors.lean` — `TCError` variants.

## `Driver/`
Recursive `EXTENDS` module resolution (`PLAN.md` §2/§5.3) — not type-checking rules, but
driver-level orchestration around invoking them: locating/lexing/parsing/desugaring
module, recursing on its own `EXTENDS` list, module cache `Ξ`, and standard-library
operator table. `Fugue.lean` calls into this for main module; calls back into itself
recursively for each dependency.
- `Modules.lean` — the orchestration itself.
- `Errors.lean` — wraps each lower-level pass's error type (including `Typed2Computable`'s
  `ComputableError`, as `.computability`) plus resolution-specific conditions
  (`moduleNotFound`, etc.).
- `Builtins.lean` — standard-library operator table.

## `Typed2Guarded/`
Distributed → Guarded PlusCal desugaring (`PLAN.md` §3.2, ch. 3.2 of thesis) — not yet
started.

## `Guarded2Network/`
Guarded → Network PlusCal, one pass with full refinement proof planned (`PLAN.md` §5.5,
§6.2) — not yet started.

## `Network2Go/`, `Network2JoinCalculus/`
Network PlusCal → Go, and Network PlusCal → Join Calculus backends (`PLAN.md` §8) — not
yet started.

## `VerifiedCompiler/`
Vendored generic proof infrastructure — reused as-is, shouldn't need domain-specific
changes per `CLAUDE.md`.
- `Trace.lean`, `Relation.lean` — generic trace/relation definitions.
- `Denotational/StrongRefinement.lean` — general `StrongRefinement` framework.
- `Denotational/Notations.lean` — notation for above.

## `ProgressBar/`
Vendored CLI progress-bar/spinner infrastructure, reused as-is.
- `Spinner.lean`, `SpinnerData.lean`, `Spinners.lean`.

## `reference/`
Reference material (spec sources, generated API references, mapping docs). File names withheld
here on purpose — see this directory directly for contents.

## `tests/regression/`
Hand-written smoke-test fixtures (`accept_*.tla`/`reject_*.tla`) plus `run.sh`, runner.

## `.claude/`
Agent tooling, not pipeline source.
- `plans/` — plan docs beyond `PLAN.md` itself (e.g. per-feature plan + findings files),
  referenced from `CLAUDE.md`'s working conventions as "other plan files."
- `tasklist.md` — running task list.
- `settings.local.json` — local Claude Code settings.

## Root
- `Fugue.lean` — CLI entry point, wires pipeline together.
- `Desugarer.lean`, `Parser_.lean`, `ProgressBar.lean` — top-level module re-exports for
  corresponding directories.
- `CustomPrelude.lean` — project-wide prelude imports/settings.
- `lakefile.lean` — build configuration, `lean_lib` targets per pass (`Fugue.G2N`, etc.).
- `lean-toolchain`, `lake-manifest.json` — Lean/Lake toolchain pin and dependency lockfile.
- `fugue.sh` — dev-mode CLI wrapper (`CLAUDE.md`).
- `AGENTS.md` — caveman-mode agent config (mirror of `CLAUDE.md`'s caveman rule, for
  non-Claude-Code agents).
