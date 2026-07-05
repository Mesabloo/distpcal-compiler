# Project layout

Quick map of the repo, directory by directory. Not exhaustive — a sample of files per
directory, enough to orient. See `PLAN.md` for what each pass actually does.

## `Common/`
Shared infrastructure used across the whole pipeline.
- `Errors.lean` — shared error-reporting typeclasses.
- `Position.lean` — `SourceSpan`/`Located` position tagging.
- `Flags.lean` — CLI flag definitions.

## `Extra/`
Vendored, generic (non-domain-specific) data-structure lemmas and instances, reused as-is
from prior art per `CLAUDE.md`.
- `List.lean`, `AssocList.lean`, `Finmap.lean`, `HashMap.lean` — container helpers.
- `Mathlib/Tactic/DeriveTraversable.lean` — mechanical `Traversable` derivation.

## `Parser_/`
Lexer/parser, ported from `distpcal-compiler`'s local `Parser_/` (`PLAN.md` §5.1).
- `PlusCal.lean` — PlusCal statement/process parser.
- `TLAPlus.lean` — TLA+ expression parser.
- `Tokens/PlusCal.lean`, `Tokens/TLAPlus.lean` — token definitions.
- `Annotations.lean` — `@type`/`@parameter` annotation parsing.

## `Core/SurfacePlusCal/`, `Core/SurfaceTLAPlus/`
Surface AST — what the parser produces, annotations still attached.
- `Syntax.lean` (each) — the AST types.
- `Pretty.lean` (each) — pretty-printers, used for `-d dump-cst`-style debugging.

## `Core/CorePlusCal/`, `Core/CoreTLAPlus/`
Desugared AST — annotations stripped into concrete fields (types, mailbox, parameter flag).
- `Syntax.lean` (each) — the AST types, shared `α`/`β` parameters across `Statement`,
  `Process`, `Declarations`, etc.

## `Desugarer/`
Surface → Core lowering (`PLAN.md` §3.2).
- `PlusCal.lean` — statement/process desugaring, `with`-chain building, well-labelledness
  and wellformedness checks (conflicting assignments, with-bound writes).
- `TLAPlus.lean` — expression desugaring, unary `fnCall`/`except`/`Ref` collapsing.
- `Errors.lean` — `DesugarError` variants.
- `Monad.lean` — the desugarer's monad stack.

## `WellFormedness/`
Planned Phase 7 module (`PLAN.md` §5.2a) — not yet started; its checks currently live ad
hoc inside `Desugarer/PlusCal.lean` instead.

## `Elaborator/`
Bidirectional type checker (`PLAN.md` §3.1, ch. 3.1 of the thesis) — not yet started.

## `Driver/`
Recursive `EXTENDS` module resolution (`PLAN.md` §2/§5.3) — not type-checking rules, but the
driver-level orchestration around invoking them: locating/lexing/parsing/desugaring a module,
recursing on its own `EXTENDS` list, the module cache `Ξ`, and the standard-library operator
table. `Fugue.lean` calls into this for the main module; it calls back into itself recursively
for each dependency.

## `Typed2Guarded/`
Distributed → Guarded PlusCal desugaring (`PLAN.md` §3.2, ch. 3.2 of the thesis) — not yet
started.

## `Guarded2Network/`
Guarded → Network PlusCal, the one pass with a full refinement proof planned
(`PLAN.md` §5.5, §6.2) — not yet started.

## `Network2Go/`, `Network2JoinCalculus/`
Network PlusCal → Go, and Network PlusCal → Join Calculus backends (`PLAN.md` §8) — not
yet started.

## `VerifiedCompiler/`
Vendored generic proof infrastructure (`Trace.lean`, `Relation.lean`,
`Denotational/StrongRefinement.lean`) — reused as-is, shouldn't need domain-specific
changes per `CLAUDE.md`.

## `ProgressBar/`
Vendored CLI progress-bar/spinner infrastructure, reused as-is.

## `reference/`
Reference material (spec sources, generated API references, mapping docs). File names withheld
here on purpose — see this directory directly for contents.

## `tests/regression/`
Hand-written smoke-test fixtures (`accept_*.tla`/`reject_*.tla`) plus `run.sh`, the runner.

## Root
- `Fugue.lean` — CLI entry point, wires the pipeline together.
- `Desugarer.lean`, `Parser_.lean`, `ProgressBar.lean` — top-level module re-exports for
  the corresponding directories.
- `CustomPrelude.lean` — project-wide prelude imports/settings.
- `lakefile.lean` — build configuration, `lean_lib` targets per pass (`Fugue.G2N`, etc.).
