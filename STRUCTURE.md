# Project layout

Directory map. Sample of files per directory, enough to orient — see `PLAN.md` for what each
pass does. Keep in sync when files move.

## Root modules
One per `lean_lib` in `lakefile.lean`, each re-exporting its directory's modules
(`Desugarer.lean`, `Elaborator.lean`, `Core.lean`, …). Nothing in the compiler imports them —
they exist so each `lean_lib` target resolves (`lake build Fugue.<Lib>`) and `doc-gen4` has one
entry point per library. `Fugue.lean` is the `lean_exe` root, the CLI.

## `Common/`
Root module `Common.lean` re-exports the lot, so `lake build Fugue.Common` resolves.
- `Errors.lean` — shared error-reporting typeclasses.
- `Position.lean` — `SourceSpan`/`Located`.
- `Flags.lean` — CLI flag definitions (`FlagsEnv`, supplied per compile as a reader — no global),
  plus where `-d dump-*` artifacts go and how they're written (shared by `Driver/` and
  `Fugue.lean`).
- `Diagnostics/Code.lean` — `Severity`/`DiagnosticCode` (`E0042`), and parsing one back.
- `Diagnostics/Stage.lean` — `Stage`: the pipeline's stages as data, ordered.
- `Diagnostics/Registry.lean` — every code, with its stage, `-W` name, and summary. The one place
  a number is bound to a meaning; `CompilerDiagnostic` instances name entries here.
- `Fresh.lean` — hygienic fresh-name generation effect class, plus its lifts through
  `ReaderT`/`StateT`/`DiagT`. The counter itself is `Driver/`'s, one per compile.
- `Pretty.lean` — `Std.Format` combinators with precedence-aware parenthesization.

## `Extra/`
Vendored generic data-structure lemmas and instances.
- `List.lean`, `AssocList.lean`, `Finmap.lean`, `HashMap.lean`, `AList.lean`, `Array.lean`,
  `Fin.lean`, `Finset.lean`, `Nat.lean`, `Option.lean`, `Prod.lean`, `Prop.lean`, `Rel.lean`,
  `Set.lean`, `String.lean`, `Substring.lean`, `Sum.lean`, `Monad.lean`.
- `Mathlib/Tactic/DeriveTraversable.lean` — mechanical `Traversable` derivation.

## `Parser_/`
Lexer/parser, ported from `distpcal-compiler`'s local `Parser_/` (§5.1).
- `PlusCal.lean`, `TLAPlus.lean` — the two parsers.
- `Common.lean` — shared combinators. `Monad.lean` — parser monad stack.
- `Tokens/PlusCal.lean`, `Tokens/TLAPlus.lean` — token definitions.
- `Annotations.lean` — `@type`/`@parameter` annotation parsing.

## `Core/`
- `Declaration.lean` — `Declaration`/`Module`, parametrized over expression former `E`, shared
  by `SurfaceTLAPlus`/`CoreTLAPlus`/`TypedTLAPlus` (each recovers its own via `abbrev`).

## `Core/SurfacePlusCal/`, `Core/SurfaceTLAPlus/`
Parser output, annotations still attached.
- `Syntax.lean`, `Pretty.lean` (each) — AST types; pretty-printers for `-d dump-parse`.

## `Core/CorePlusCal/`, `Core/CoreTLAPlus/`
Desugared AST — annotations stripped into concrete fields (types, mailbox, parameter flag).
- `Syntax.lean` (each) — shared `α`/`β` parameters across `Statement`, `Process`,
  `Declarations`.

## `Core/TypedPlusCal/`, `Core/TypedTLAPlus/`
`Elaborator`'s output; every annotation resolved to a concrete `Typ`.
- `Syntax.lean` (`TypedTLAPlus/`) — the AST types.
- `Syntax.lean` (`TypedPlusCal/`) — `ElaboratedPlusCal.{Ref,Multicast,Statement,Block,
  Branches,Declarations,Process,Algorithm}`, generic over `(τ ε : Type)`, plus `TypedPlusCal`'s
  pin of that layer at `TypedTLAPlus.Typ`/`Expression`. `Core/ComputablePlusCal/Syntax.lean`
  pins the same generic layer at `ComputableTLAPlus`'s types.
- `Coercion.lean` — term-level coercions inserted by subtyping (`<:`).
- `Builtins.lean` — shared builtin-operator table (`BuiltinOp`, `builtinOpOf?`,
  `Expression.recognizeBuiltin?`), keyed by `(Origin, name)`; also `reservedTemporalActionNames`.
  Every downstream pass recognizing a builtin call reuses this.

## `Core/ComputableTLAPlus/`, `Core/ComputablePlusCal/`
`Typed2Computable`'s output — `Typed*` minus constructs with no finite runtime representation
(§5.3).
- `Syntax.lean` (`ComputableTLAPlus/`) — `Expression`, missing `fforall`/`eexists`/`stutter`/
  `mvar`/`fnSet`/`recordSet`; `forall`/`exists`/`choose`'s domain is a plain `Expression`, not
  `Option`. `Typ`/`Origin` reused directly from `TypedTLAPlus`.
- `Syntax.lean` (`ComputablePlusCal/`) — pins `ElaboratedPlusCal` at `ComputableTLAPlus`'s types.

## `Core/GuardedPlusCal/`, `Core/NetworkPlusCal/`
Outputs of `Computable2Guarded` and `Guarded2Network` (§5.4/§5.5).
- `Syntax.lean` (`GuardedPlusCal/`) — `Statement` flat (10 constructors, no nested `Block`/
  `Branches`; every `if`/`while`/`either` already in `AtomicBranch`'s precondition/action split),
  reuses `ElaboratedPlusCal.Ref`/`.Multicast`. Pins itself as `ComputableGuardedPlusCal`.
- `Syntax.lean` (`NetworkPlusCal/`) — `Statement` identical minus `receive` (compiled into a
  `Thread.rx` constructor, a real second kind of thread); reuses `GuardedPlusCal.Block`/`Ref`/
  `Multicast`/`Declarations`. Pins itself as `ComputableNetworkPlusCal`.

## `Core/Go/`
`Network2Go`'s target AST (§5.7) — the Go fragment of thesis §6.6 plus what §7.2's listings
emit. Imports nothing from `Core/`: Go types and expressions are its own, so TLA⁺ types and
expressions are *compiled* into them rather than carried through as parameters.
- `Syntax.lean` — `Typ` (incl. `named`/`var` for §7.2's generic runtime types), `Expression`
  (annotation carrier `α`, short-circuit `and`/`or` distinct from strict `binary`, composite
  literals), `Ref` (§6.6.11, no type annotation, so `Functor`/`Traversable` rather than the
  bifunctor pair), `Statement` (blocks are `List Statement`), `SelectClause`/`SwitchClause`,
  `Function`, `Declaration` (top-level: a `Function`, the `var x τ = e` §7.2.2 compiles a
  parameter-less operator and every function definition to, or the `type N τ` §7.2.3 needs for the
  `Network` struct). `Statement.expr` covers a call evaluated for its effect, which §6.6 has no
  form for and `Send`/`Release` need. Instances are `partial def` + explicit instance. Pins itself as `ComputableGo` at its own `Go.Typ`.
- `Pretty.lean` — **the code generator**, not a debug dump: the shipped `.go` file is what this
  prints. Go operator precedence, always-breaking blocks, and `keywords`/`sanitize` (ported
  verbatim from prior art) at every identifier-print site.

## `Desugarer/`
Surface → Core lowering (§3.2).
- `PlusCal.lean` — statement/process desugaring, `with`-chain building, well-labelledness and
  wellformedness checks (conflicting assignments, with-bound writes).
- `TLAPlus.lean` — expression desugaring, unary `fnCall`/`except`/`Ref` collapsing.
- `Errors.lean`, `Monad.lean`.

## `WellFormedness/`
§5.2a — well-labelledness, well-scopedness, no-shared-memory/no-bare-temporal restrictions, run
against a `TypedModule`'s `pcalAlgorithm` right after type checking (`Driver/Modules.lean`).
Assignment-conflict checking stays ad hoc in `Desugarer/PlusCal.lean`, not duplicated here.
- `Errors.lean` — `WellFormednessError` variants.
- `Monad.lean` — `MonadForeignLookup` (fetch a module's checked declarations by name; the one
  seam into `Driver/`'s module cache) plus `StateT`/`ExceptT` lift instances.
- `Reachability.lean` — shared reachability walk, reused by `Restrictions.lean` and
  `Typed2Computable`: `ResolvedDecl`/`Decl.resolve`/`resolveInModule`, `ReachabilityClosure`,
  `Expression`/`Statement`/`Algorithm.walkReachable` (thin per-node callbacks —
  `Restrictions.lean` supplies real checks, `Typed2Computable` supplies no-ops).
- `Labelling.lean` — every `goto` targets a label its process defines, or `"Done"`; `"Done"`
  never redefined.
- `WellScoped.lean` — re-export of `WellScoped/`, one file per `PlusCal` stage: no duplicate or
  shadowed names in any scope (global, process-local, block-local `with`).
  `WellScoped/TypedPlusCal.lean` is the **executable** check the driver runs;
  `WellScoped/CorePlusCal.lean` and `WellScoped/GuardedPlusCal.lean` are `Prop`-side
  counterparts over those stages' ASTs, not executed — infrastructure for the future
  preservation lemma and for `Guarded2Network`'s proof precondition.
- `Declarations.lean` — no Channel-typed `variables` entry, no process-local `channels`/`fifos`,
  no algorithm-level `variables`.
- `Restrictions.lean` — supplies `Reachability.lean`'s walk its checks (`visitStatement`/
  `visitExpr`): no channel value inside an ordinary expression (or in `assign`'s/`receive`'s
  non-channel `Ref` positions, `Statement.checkRefRestrictions`), no reference to a module-level
  `VARIABLE`, no bare/transitive temporal or action operator, no unbounded quantifier —
  transitively through every operator/function the algorithm calls.
- `WellFormedness.lean` — ties the four checks together; `TypedTLAPlus.Module.checkWellFormed`
  is the entry point `Driver/Modules.lean` calls.

## `Typed2Computable/`
`Typed*` → `Computable*` (§5.3), run right after well-formedness (`Driver/Modules.lean`).
- `Errors.lean` — `ComputableError` (`notComputable` for `fnSet`/`recordSet`;
  `internalInvariantViolated` as defense-in-depth).
- `TLAPlus.lean` — `TypedTLAPlus.Expression.toComputable`, per-constructor translation.
- `PlusCal.lean` — same over `Ref`/`Statement`/`Block`/`Branches`/`Declarations`/`Process`/
  `Algorithm`, delegating leaf expressions to `TLAPlus.lean`.
- `Typed2Computable.lean` — entry point (`TypedTLAPlus.Module.toComputable`): collects the
  reachability closure from the algorithm, drops builtin-sourced entries, translates the rest
  plus the algorithm, returns the flattened module.

## `Elaborator/`
Bidirectional type checker (§3.1, thesis ch. 3.1).
- `Monad.lean` — `Γ`, metavariable context, error reporting, fresh names.
- `Context.lean` — `Γ`-extension helpers (`extend`/`extendAll`).
- `Subtyping.lean` — `<:`, `lub`, `glb`, term-level coercion, direction-aware metavariable
  solving (in place of a literal `Specialize` rule).
- `Resolution.lean` — `resolveMVars`, defaulting each to its recorded upper bound.
- `TypeUtils.lean` — type-level helpers (free-variable collection over `Typ`).
- `Expressions.lean` — `checkExpr`/`inferExpr`.
- `Declarations.lean` — declaration/module-level checking, threading `Γ` across `CONSTANTS`/
  `VARIABLES`/`ASSUME`/operator/function definitions, plus `builtinContext`.
- `PlusCal.lean` — statement/process/algorithm checking, `CorePlusCal` → `TypedPlusCal`.
- `Elaborator.lean` — `CoreTLAPlus.Module.check`, `Module.runChecker`.
- `Errors.lean` — `TCError` variants.

## `Driver/`
Recursive `EXTENDS` resolution (§2/§5.3) — orchestration around the checking rules: locate/lex/
parse/desugar a module, recurse on its `EXTENDS` list, module cache `Ξ`, stdlib operator table.
`Fugue.lean` calls in for the main module; this calls back into itself per dependency.
- `Modules.lean` — the orchestration, plus `DriverState` (one compile's fresh-name counter,
  source registry, and module cache `Ξ`) and the monad `M` it all runs at.
- `Pipeline.lean` — a whole compile as one function: `Stage`, `PipelineError`/`PipelineResult`,
  `runPipeline`, and the pure diagnostic renderers. `Fugue.lean` and `tests/`'s runner are its
  two consumers; neither reimplements the pass order.
- `Errors.lean` — wraps each lower-level pass's error type (incl. `ComputableError` as
  `.computability`) plus resolution conditions (`moduleNotFound`, etc.).
- `Builtins.lean` — standard-library operator table.

## `Computable2Guarded/`
Distributed → Guarded PlusCal (§5.4, thesis ch. 3.2) — **done** (phase 9).
- `CFlow.lean` — `𝒞_cflow`, rewrites `if`/conditional-`while` into `either`/`await`.
- `Par.lean` — `𝒞_par`, sequentializes parallel assignments.
- `FlatReord.lean` — `𝒞_flat`/`𝒞_reord` merged into one walk straight to
  `GuardedPlusCal.AtomicBranch`; floats `await` **and `receive`** guards to branch front.
- `Errors.lean`, entry point `Computable2Guarded.lean`.

## `Guarded2Network/`
Guarded → Network PlusCal (§5.5, §6.2) — **pass implemented, refinement proof pending** (phase
10, current work).
- `PlusCal.lean` — the pass (`guarded.toNetwork`), not split into subpasses.
- `Errors.lean`, entry point `Guarded2Network.lean`.
- Missing: `Semantics/Denotational.lean`/`Semantics/Lemmas.lean` for `GuardedPlusCal`/
  `NetworkPlusCal`, and `Guarded2Network/Lemmas.lean` itself (§6.2). The well-scopedness
  precondition is ported (`WellFormedness/WellScoped/GuardedPlusCal.lean`).

## `Network2Go/`
Network PlusCal → Go (§5.7) — in progress (phase 11). Target AST and code generator landed
(`Core/Go/`); the TLA⁺ half (types, expressions, definitions) is compiled, the PlusCal half is not.
- `Errors.lean` — `N2GError`: `internalInvariantViolated` and `unsupported`.
- `Naming.lean` — runtime package qualifiers (`tlaplus`/`comm`/`locks`), §7.2.2's capitalization of
  definitions, record fields, tuple `Proj`ections, `ordParamName`, and `goIdent`, the escaping
  (`_`→`__`, `$`→`_`) every source name crosses into Go through, which keeps user-written and
  compiler-synthesized names disjoint by parity: user names produce only even-length underscore
  runs, a fresh name's single `$` makes exactly one odd. On top of it, the renaming that keeps user
  names distinct from *each other* and off Go's vocabulary — `definitionName`/`fieldName` mark
  opposite sides of the capitalization (so `Init` and `from` both stay clean), `binderName` steps
  around `keywords`/`predeclared`. Pure functions, not a collision map: Go types struct fields
  structurally, so a field name must map identically at every occurrence.
- `Typ.lean` — `compileTyp : ComputableTLAPlus.Typ → m Go.Typ` (§7.2.1.1). Primitives go to the
  runtime newtypes; record fields sorted so source order can't change the compiled type;
  `Channel(τ)` throws.
- `Ord.lean` — `ordDict : Typ → m Go.Expression`, the second fold over `Typ`, mirroring
  `compileTyp`: the `tlaplus.Ord[τ]` dictionary every comparing runtime operation is handed.
  Closed expressions for the runtime's own types, an inline literal for records/tuples (anonymous
  structs carry no methods), a parameter for a type variable. Plus `Typ.typeVars`.
- `Expression.lean` — `compileExpr` (§7.2.1.2). Always one expression, never a statement prelude;
  dictionaries threaded at every runtime call site.
- `Definition.lean` — `compileDeclaration` (§7.2.2): parameter-less operator → `var`, parametric
  operator → generic `func` with a dictionary parameter per type parameter, function definition →
  `FnConstructor`/`MkRecFn` depending on whether the body calls itself.
- `PlusCal.lean` — the PlusCal half (§7.2.3). One `bool`-returning function per branch, one
  `Rand`-driven scheduler function per atomic block, one per thread, one per process, plus the
  `Network` struct type. `goto` spawns a goroutine rather than calling, so a block chain cannot
  overflow a stack. Entry point `ComputableNetworkPlusCal.Algorithm.toGo`, outside the namespace
  so dot notation reaches it.
- `Emit.lean` — a compiled declaration list as a `.go` *file*: package clause (`-Xgo-pkg`,
  default `main`), import block, declarations. Imports are computed by walking the AST for
  qualified names, not assumed — Go rejects an unused import, so a specification with no `either`
  (no `sched`) or no process-local variables (no `locks`) must not get one.
- `Locks.lean` — lock inference (§7.1.2, Definition 7.1.3). Pure analysis, emits no Go:
  per-*branch* footprints (`exprFreeVars`/`branchShared`/`processFootprints`), domination, merging,
  locking order. Answers with `ProcessLocks` — the locks in acquisition order plus the
  variable-to-lock map, from which `acquiredBy` derives any code's lock set — which `PlusCal.lean`
  turns into `Lock[struct{…}]` parameters and `Acquire`/`Release` calls. A `Thread.rx` contributes
  a footprint over its `inbox`. No thread-confinement pruning: a lock is also the variable's
  storage.
- Entry point `Network2Go.lean`.
- Missing: the PlusCal-side pass (`PlusCal.lean`, `network.toGo`), lock inference, collision
  renaming.

## `Network2JoinCalculus/`
Network PlusCal → Join Calculus (§8) — not started.

## `runtime/`
Go, not Lean — the library generated code links against (§5.7). Signatures from thesis Listings
7.2.1–7.2.11. **The directory holds no code**: every package is a subdirectory, so nothing is
`package runtime` (that name is Go's own).

### `runtime/comm/`
- `comm.go` — `Sender[T]`/`Receiver[T]` (Listings 7.2.9/7.2.10). Interfaces, not concrete types:
  a Distributed PlusCal channel has no runtime representation of its own, so generated code
  holds an endpoint supplied by whoever wires the system.
- `multicast.go` — `Multicast[T](ch map[Address]Sender[T], to tlaplus.Set[Address], f func(Address) T)`,
  the whole compiled form of a `multicast` statement. Holds the iteration `Network2Go` does not
  emit: the specification fixes no order on the sends, so the choice stays the library's (§5.7).
- `address.go` — `Address`, unspecified beyond its `Eq`/`Lt` methods, plus `AddressOrd` bridging
  them into a `tlaplus.Ord` dictionary. Here rather than `tlaplus/` because an address names the
  peer a `Sender` reaches.

### `runtime/locks/`
- `locks.go` — `Lock[T]` (capacity-1 channel *holding* the guarded value, so it can't be read
  without being held), `MkLock`/`Acquire`/`Release`. Non-reentrancy and acquisition order are
  lock inference's obligations, not enforced here.

### `runtime/sched/`
- `sched.go` — `Rand(lo, hi)`, the branch scheduler's picker (§7.2.3.1). A thin wrapper over
  `math/rand/v2`, deliberately unfair, matching `isFair` being carried through unused. Its own
  package rather than a corner of `locks/` because it is not mutual exclusion, and because a
  fairer picker would go here if fairness ever stops being ignored.

### `runtime/tlaplus/`
One file per TLA⁺ concept/stdlib module.
- `ord.go` — `Ord[T]`, the equality-and-ordering **dictionary struct** (`Eq`/`Lt` fields) every
  comparing operation takes explicitly, with `Neq`/`Gt`/`Le`/`Ge`/`Cmp` derived as methods. A
  struct rather than an interface because Go has no conditional method sets; the dictionary
  keeps every container `[T any]` and composes (`SetOrd(SetOrd(IntOrd))`).
- `sequences.go` — `Seq[T]` (`[]T`, 1-indexed, slot 0 unused), `MkSeq`/`Len`/`SeqIndex`/
  `SeqUpdate`/`Head`/`Tail`/`Append`/`SeqEq`/`SeqCmp`/`SeqOrd`. `SeqUpdate` backs `EXCEPT`/`:=`.
  Covers exactly `Driver/Builtins.lean`'s `sequencesDeclarations`. Literals built with `MkSeq`.
- `{bool,str}.go` — `Bool`/`Str` newtypes and their `BoolOrd`/`StrOrd` dictionaries. `str.go` also
  has `StrToSeq`, what the `Str <: Seq(Int)` coercion compiles to (code points, one `Int` each);
  it lives here rather than in `sequences.go` because that file mirrors `Driver/Builtins.lean`'s
  `sequencesDeclarations` exactly and `StrToSeq` is an intrinsic, not a `Sequences` member.
  `str_test.go` pins the code-point choice and that the result is an ordinary 1-indexed sequence.
- `print.go` — `Print`, what PlusCal's `print` compiles to. Go's builtin `println` takes only
  basic types, and every TLA⁺ value here is a defined type or a struct.
- `int_big.go`, `int_machine.go` — the two `Int` representations, by build tag. **`int_big.go`
  (`math/big`) is the default**; `go build -tags fugue_machint` selects the other. Each carries
  `Int`, `IntOrd`, `MkInt`/`ToInt`, `Add`/`Sub`/`Neg`/`Mul` — the whole representation-dependent
  surface, so nothing else in the tree varies. See §5.7.
- `sets.go` — `Set[T]` (`[]T` plus two invariants Go can't express: sorted by the element
  dictionary's ordering, duplicate-free), `MkSet`/`SetIn`/`SetEq`/`SetCmp`/`SetFilter`/`SetMap`/
  `SetUnion`/`SetIntersect`/`SetDifference`/`SetSubseteq`/`Choose`, and `SetOrd`. `Choose`
  returns the smallest satisfying element so Hilbert's choice stays deterministic. Literals
  built with `MkSet`.
- `functions.go` — `LazyFunction[T, U]`, `FnConstructor`/`FnOverload`/`FnApply`/`MkRecFn`/
  `Domain`, each taking the domain's dictionary. `FnOrd` is a **panicking placeholder** (§5.7).
- `naturals.go` — `IntRange` (`..`), written against `IntOrd.Le`/`Add` so it holds for either
  `Int` representation. `Nat` is absent (infinite, §9.15).
- No `records.go`/`tuples.go`: records and tuples compile to *anonymous* structs with a
  dictionary literal emitted beside each — no library type, no generated one, hence no arity cap
  on tuples. `records_test.go` stands in for generated code, pinning that a dictionary orders an
  unnameable type and that identically-shaped structs are one type.

## `persistent/`
Go, not Lean — data structures the runtime needs (§5.7). Root `go.mod`, module
`github.com/mesabloo/fugue`, covering this directory and `runtime/`.
- `treemap/` — persistent ordered map with a caller-supplied `Compare`, so keys need not be
  Go-`comparable`. Backs `LazyFunction`'s cache, where `EXCEPT`'s copy-before-write needs O(1)
  `Clone`. Weight-balanced (Adams), per `.claude/plans/persistent-collections-plan.md`.
  - `node.go`, `balance.go`, `treemap.go`, `iter.go`, `treemap_test.go`.

## `VerifiedCompiler/`
Vendored generic proof infrastructure.
- `Trace.lean`, `Relation.lean` — trace/relation definitions.
- `Denotational/StrongRefinement.lean`, `Denotational/Notations.lean`.

## `ProgressBar/`
Vendored CLI spinners — `Spinner.lean`, `SpinnerData.lean`, `Spinners.lean`.

## `reference/`

Reference material (spec sources, generated API references, mapping docs). File names withheld
here on purpose — see this directory directly for contents.

## `docs/`
- `diagnostics/<code>.md` — one page per diagnostic code, printed by `fugue explain <code>`.

## `Tests/`
- `regression/` — hand-written fixtures (`Accept*.tla`/`Reject*.tla`), each named after the TLA⁺
  module it contains, as TLA⁺ requires (`EXTENDS Foo` finds only `Foo.tla`), and each with
  an optional `<fixture>.expect.json` sidecar saying which stage must reject it, which code it
  must carry, which warnings must fire, and (`searchPath`) which `-I` directories it needs. Run by `lake test`, not by a script.
- `examples/` — larger worked examples (Ping-Pong, Two-Phase Commit, Lamport mutex).

The runner itself lives at the top of this directory (`lake test -- [FILTER…]`), a `lean_exe`
tagged `@[test_driver]`. It compiles each fixture in-process through `Driver/Pipeline.lean`, so
what it checks is structured rather than an exit code.
- `Expectation.lean` — what a fixture claims: its filename's defaults, with its
  `<fixture>.expect.json` sidecar applied over them and validated against the diagnostic registry.
- `Check.lean` — one function per assertion; a fixture reports all its mismatches at once.
- `Report.lean` — verdicts (`PASS`/`FAIL`/`XFAIL`/`XPASS`/`SKIP`/`TIMEOUT`) and how they print.
- `Main.lean` — fixture discovery, the CLI, and the run loop.

## `.claude/`
- `plans/` — plan docs beyond `PLAN.md`.
- `tasklist.md` — running task list.
- `settings.local.json` — local Claude Code settings.

## Root
- `Fugue.lean` — CLI entry point.
- `Desugarer.lean`, `Driver.lean`, `Parser_.lean`, `ProgressBar.lean` — top-level re-exports.
- `CustomPrelude.lean` — project-wide prelude imports/settings.
- `lakefile.lean` — build config, `lean_lib` per pass (`Fugue.G2N`, etc.). Also where the
  compiler's version is set (`package Fugue`'s `version`), and where `Version.lean` is generated
  from it.
- `.lake/version/Version.lean` — **generated, not in the repo.** Carries `fugueVersion` (a
  `String`) into compiled code for `Fugue.lean`'s `--version`. Written by `lakefile.lean` when it
  is elaborated; claimed by `lean_lib Fugue.Version`, whose `srcDir` points here. Outside
  `.lake/build/` so `lake clean` cannot remove it without also removing the configuration that
  writes it. Delete it by hand and the next build fails until `lakefile.lean` is touched.
- `lean-toolchain`, `lake-manifest.json` — toolchain pin and dependency lockfile.
- `fugue.sh` — dev-mode CLI wrapper.
- `AGENTS.md` — caveman-mode config for non-Claude-Code agents.
