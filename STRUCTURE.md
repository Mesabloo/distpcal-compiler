# Project layout

Quick map of repo, directory by directory. Not exhaustive — sample of files per directory,
enough to orient. See `PLAN.md` for what each pass actually do. Keep this file in sync
whenever file get added, removed, or moved (`CLAUDE.md`).

## Root modules
One per `lean_lib` in `lakefile.lean`, each just re-exporting its directory's modules
(`Desugarer.lean`, `Elaborator.lean`, `Core.lean`, …). Nothing in the compiler imports them —
passes import the individual modules they need. They exist so each `lean_lib` target resolves
(making `lake build Fugue.<Lib>` a usable per-library check) and so `doc-gen4` has one entry
point per library. `Fugue.lean` is the exception: it's the actual `lean_exe` root, the CLI.

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

## `Core/GuardedPlusCal/`, `Core/NetworkPlusCal/`
`Computable2Guarded`'s and `Guarded2Network`'s output ASTs, respectively (`PLAN.md` §5.4/§5.5).
- `Syntax.lean` (`GuardedPlusCal/`) — `Statement` flat (10 constructors, no nested `Block`/
  `Branches` — every `if`/`while`/`either` already rewritten into `AtomicBranch`'s precondition/
  action split by this stage), reuses `ElaboratedPlusCal.Ref`/`.MulticastFilter`. Also pins itself
  at `ComputableTLAPlus`'s types as `ComputableGuardedPlusCal`.
- `Syntax.lean` (`NetworkPlusCal/`) — `Statement` identical to `GuardedPlusCal.Statement` minus
  `receive` (compiled into a new `Thread.rx` constructor instead — a real second kind of thread,
  not folded into `.code`); reuses `GuardedPlusCal.Block`/`Ref`/`MulticastFilter`/`Declarations`
  unchanged. Also pins itself at `ComputableTLAPlus`'s types as `ComputableNetworkPlusCal`.

## `Core/Go/`
`Network2Go`'s target AST (`PLAN.md` §5.7) — the Go fragment of thesis §6.6, plus what §7.2's
listings emit. Imports nothing from `Core/`: Go types and expressions are its own, so TLA⁺ types
and expressions are *compiled* into them by the pass rather than carried through as parameters
(unlike prior art's `GoCal`, which had no Go type/expression AST at all).
- `Syntax.lean` — `Typ` (Go types, incl. `named`/`var` for §7.2's generic runtime types),
  `Expression` (annotation carrier `α`, short-circuit `and`/`or` distinct from strict `binary`,
  composite literals), `Ref` (§6.6.11, no type annotation, so `Functor`/`Traversable` not the
  bifunctor pair), `Statement` (blocks are `List Statement`), `SelectClause`/`SwitchClause`,
  `Function`. Instances are `partial def` + explicit instance, `Core/CorePlusCal/Syntax.lean`'s
  shape for a nested statement type. Pins itself as `ComputableGo` — at its *own* `Go.Typ`, not
  at `ComputableTLAPlus`'s.
- `Pretty.lean` — **the code generator**, not a debug dump like every other `Pretty.lean` here:
  the shipped `.go` file is what this prints. Go's own operator precedence, always-breaking
  blocks, and `keywords`/`sanitize` (the one part of prior art's `Pretty.lean` that ports
  verbatim), applied at every identifier-print site.

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
- `WellScoped.lean` — thin re-export of `WellScoped/`, one file per `PlusCal` stage: no
  duplicate/shadowed names in any scope (global, process-local, block-local `with`).
  `WellScoped/TypedPlusCal.lean` is the **executable** check the driver runs;
  `WellScoped/CorePlusCal.lean` and `WellScoped/GuardedPlusCal.lean` are `Prop`-side
  counterparts modeling the same discipline over each of those stages' own ASTs, authored fresh
  and not executed by anything — infrastructure for a future preservation lemma
  (`CorePlusCal.WellScoped`) or proof precondition (`GuardedPlusCal.Algorithm.WellScoped`,
  `Guarded2Network`'s refinement proof, phase 10 item 5).
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

## `Computable2Guarded/`
Distributed → Guarded PlusCal desugaring (`PLAN.md` §5.4, ch. 3.2 of thesis) — **done**
(phase 9).
- `CFlow.lean` — `𝒞_cflow`, rewrites `if`/conditional-`while` into `either`/`await`.
- `Par.lean` — `𝒞_par`, sequentializes parallel assignments.
- `FlatReord.lean` — `𝒞_flat`/`𝒞_reord` merged into one walk straight to
  `GuardedPlusCal.AtomicBranch`; floats `await` **and `receive`** guards to the front of
  each branch (§5.4).
- `Errors.lean` — `GuardedError` variants.
- Entry point: `Computable2Guarded.lean` (top-level re-export).

## `Guarded2Network/`
Guarded → Network PlusCal, one pass with full refinement proof planned (`PLAN.md` §5.5,
§6.2) — **pass implemented, proof still pending** (phase 10, current work). AST landed
(`Core/NetworkPlusCal/Syntax.lean`).
- `PlusCal.lean` — the pass itself (`guarded.toNetwork`), not split into subpasses like
  `Computable2Guarded` — this file is the whole thing.
- `Errors.lean` — `G2NError` variants.
- Entry point: `Guarded2Network.lean` (top-level re-export).
- Still missing: `Semantics/Denotational.lean`/`Semantics/Lemmas.lean` for both
  `GuardedPlusCal`/`NetworkPlusCal` and the `Guarded2Network/Lemmas.lean` refinement proof
  itself (§6.2) — the well-scopedness preservation lemma this proof needs as precondition
  is ported (`WellFormedness/WellScoped/GuardedPlusCal.lean`), the proof consuming it isn't
  written yet.

## `Network2Go/`
Network PlusCal → Go backend (`PLAN.md` §5.7) — in progress (phase 11). Target AST and code
generator landed (`Core/Go/`); the compilation passes themselves aren't written yet.
- `Errors.lean` — `N2GError` variants (currently just the `internalInvariantViolated`
  defense-in-depth catch-all).
- Entry point: `Network2Go.lean` (top-level re-export).
- Still missing: the TLA⁺ → Go type/expression compilation, the PlusCal-side pass
  (`PlusCal.lean`, `network.toGo`), lock inference, and `runtime/tlaplus/`.

## `Network2JoinCalculus/`
Network PlusCal → Join Calculus backend (`PLAN.md` §8) — not yet started.

## `runtime/`
Go, not Lean — the runtime library generated code links against (`PLAN.md` §5.7).
Signatures come from thesis Listings 7.2.1–7.2.11. **The directory itself holds no code**:
every package is a subdirectory, deliberately, so that nothing is `package runtime` — that
name is Go's own, and generated code naming it constantly would read as the stdlib package.

### `runtime/comm/`
Message passing between processes: the endpoints, and who is at the other end.
- `comm.go` — `Sender[T]`/`Receiver[T]` (Listings 7.2.9/7.2.10). Interfaces, not concrete
  types: a Distributed PlusCal channel has no runtime representation of its own (never
  stored or passed as a value), so what generated code holds is an endpoint supplied by
  whoever wires the system — Go channel, Unix socket, TCP connection. `Multicast` lands
  here next to `Sender` once tasklist item 4 settles its signature (§9.5).
- `address.go` — `Address`, deliberately unspecified beyond `tlaplus.Ord`. Here rather than
  in `tlaplus/` because an address exists to name the peer a `Sender` reaches.

### `runtime/locks/`
- `locks.go` — `Lock[T]` (a capacity-1 channel *holding* the guarded value, so it can't be
  read without being held), `MkLock`/`Acquire`/`Release`. Generated code never touches the
  channel directly. Non-reentrancy and acquisition order are lock inference's obligations,
  not enforced here.

### `runtime/tlaplus/`
TLA⁺'s own value types, one file per concept/stdlib module.
- `eq.go` — `Eq[T]` and the derived `Neq`.
- `sequences.go` — `Seq[T]` (`[]T`, 1-indexed with slot 0 unused), with `MkSeq`/
  `Len`/`SeqIndex`/`SeqUpdate`/`Head`/`Tail`/`Append`/`SeqEq`/`SeqCmp`. `SeqUpdate` backs
  `EXCEPT`/`:=` on a sequence. Covers exactly the operators
  `Driver/Builtins.lean`'s `sequencesDeclarations` exports. Sequence literals must be built
  with `MkSeq`.
- `ord.go` — `Ord[T]` (super-interface of `Eq`), with `Le`/`Ge`/`Cmp` derived once
  generically rather than per type.
- `{bool,str}.go` — one file per primitive TLA⁺ type: the `Bool`/`Str` newtypes and
  their `Eq`/`Gt`/`Lt`. Newtypes because Go forbids implementing an interface for a
  non-local type, so `bool`/`string` can't satisfy `Eq` directly.
- `int_big.go`, `int_machine.go` — the two `Int` representations, selected
  by build tag. **`int_big.go` (`math/big`) is the default**; `go build -tags
  fugue_machint` selects the machine-integer one. Each carries `Int`, its `Eq`/`Gt`/`Lt`,
  `MkInt`/`ToInt`, and `Add`/`Sub`/`Neg`/`Mul` — the whole representation-dependent surface,
  so nothing else in the tree varies. See `PLAN.md` §5.7 for why arbitrary precision is the
  default and why `Int` must be a struct.
- `sets.go` — `Set[T]` (`[]T` plus two invariants Go can't express: sorted by the
  element ordering, and duplicate-free), with `MkSet`/`SetIn`/`SetEq`/`SetFilter`/`SetMap`/
  `Choose`. `Choose` returns the smallest satisfying element, not a random pick, so that
  Hilbert's choice stays deterministic. Set literals must be built with `MkSet`.
- `functions.go` — `LazyFunction[T, U]` and `FnConstructor`/`FnOverload`/`FnApply`/
  `MkRecFn`/`Domain`.
- `naturals.go` — `IntRange` (`..`), written against `Le`/`Add` so it holds for
  either `Int` representation. The arithmetic operators live with the representation, in
  `int_big.go`/`int_machine.go`; comparisons in `ord.go`. `Nat` is absent (infinite, §9.15).
- Still missing: `records.go` here, and `comm/multicast.go` (blocked on tasklist item 4).

## `persistent/`
Go, not Lean — data structures the runtime library needs, versioned with the compiler
(`PLAN.md` §5.7). Root `go.mod`, module `github.com/mesabloo/fugue`, covering both this
directory and `runtime/`.
- `treemap/` — persistent (immutable, structurally shared) ordered map with a
  caller-supplied `Compare`, so keys need not be Go-`comparable`. Backs `LazyFunction`'s
  cache in `runtime/tlaplus/functions.go`, where `EXCEPT`'s copy-before-write discipline
  needs `Clone` to be O(1). Weight-balanced (Adams), per
  `.claude/plans/persistent-collections-plan.md`.
  - `node.go` (node type, `insert`/`remove`/`lookup`), `balance.go` (rotations),
    `treemap.go` (public API), `iter.go` (ordered traversal), `treemap_test.go`.

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
