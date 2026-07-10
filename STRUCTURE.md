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
- `Syntax.lean` (each) — the AST types.
- `Coercion.lean` (`TypedTLAPlus/` only) — term-level coercions inserted by subtyping (`<:`).

## `Desugarer/`
Surface → Core lowering (`PLAN.md` §3.2).
- `PlusCal.lean` — statement/process desugaring, `with`-chain building, well-labelledness
  and wellformedness checks (conflicting assignments, with-bound writes).
- `TLAPlus.lean` — expression desugaring, unary `fnCall`/`except`/`Ref` collapsing.
- `Errors.lean` — `DesugarError` variants.
- `Monad.lean` — desugarer's monad stack.

## `WellFormedness/`
Planned Phase 7 module (`PLAN.md` §5.2a) — not yet started; its checks currently live ad
hoc inside `Desugarer/PlusCal.lean` instead.

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
- `Errors.lean` — wraps each lower-level pass's error type plus resolution-specific
  conditions (`moduleNotFound`, etc.).
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
