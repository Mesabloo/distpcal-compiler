# Fugue — compiler from Distributed PlusCal to the Join Calculus and Go

**Status:** phases 1–10 done. Backends (phase 11) next. See §7.
**Companion files:** `INSTRUCTIONS.md` (working conventions), `OPEN_QUESTIONS.md`
(open questions, referenced as `§9.x`).

Prior art, three sources, none reused wholesale (§2 carry-over row):
- public mirror `github.com/mesabloo/fugue` — branches `main`, `develop`, `go-semantics`,
  `lock-inference`, `docs`
- private checkout `~/Documents/distpcal-compiler` — origin
  `github.com/mesabloo/distpcal-compiler`, branches `main`, `develop`, `compiler`,
  `go-semantics`, `lock-inference`, plus uncommitted local `typechecker`
- thesis *Generating Distributed Programs from Formal Specifications* (`reference/thesis.pdf`)

Thesis design drives most of plan; its gaps define most open work. §3 = how to read each
source.

---

## 1. Goals and non-goals

**Goal.** Compiler in Lean 4, Distributed PlusCal (TLA+ modules with embedded PlusCal
algorithm using `send`/`receive`/`multicast`/FIFO extensions) → two independent backends:

1. **Join Calculus** — guarded-reaction dialect close to Fournet & Gonthier's original,
   extended with name-server (`register`/`lookup`) for distributed addressing. More
   formally tractable target: reaction semantics line up almost exactly with Network
   PlusCal's atomic blocks. Thesis develops it as a compilation target in its own right,
   not a stepping stone to Go.
2. **Go** — real, runnable, idiomatic-ish Go source: goroutines, channels, small runtime
   library this project owns.

**Guiding ambition.** *Formally verified* compiler — every pass eventually comes with
proof that target behavior refines source behavior, via trace/simulation framework in
`VerifiedCompiler/` (§6). Full end-to-end verification = north star, not milestone.

**Non-goals.**
- Not a general-purpose TLA+/PlusCal tool — only the Distributed PlusCal fragment prior
  art uses (bounded-buffer FIFOs, channels, `multicast`, addresses).
- Not reproducing the domain-theoretic Go denotational semantics (`go-semantics` branch)
  near-term — real, worth returning to, but big (ultrametric spaces, contraction mappings,
  ~20 files topology infra) and orthogonal to a working pipeline. §6.4.
- Not building a JoCaml-compatible un-guarded Join Calculus emitter. Compiler targets the
  guarded dialect; execution stays open, §9.1.

---

## 2. Decisions

| Question | Decision |
|---|---|
| Go / Join Calculus backend relation? | **Independent siblings.** Both compile from `NetworkPlusCal`, two separate pass chains (`Network2Go`, `Network2JoinCalculus`). No sequencing between backends. Matches thesis. |
| How much of prototypes carries over? | **Fresh domain code, reused generic infra, three ported exceptions.** Vendored as scaffold (adapted, not copied blind): `Extra/` (data structure lemmas), `VerifiedCompiler/` (trace + refinement framework), `ProgressBar/` (CLI spinners), `Common/` (positions, diagnostics, pretty-printing). Fresh: most AST definitions, semantics, passes (desugarer, checker, every `*2*` pass but Guarded→Network). Three ported exceptions, all working + non-trivial: **lexer/parser** (§5.1), **Guarded→Network** (§5.5), **well-scopedness checking** (`Core/GuardedPlusCal/Syntax/WellScopedness.lean`, repurposed as proof-side invariant — §5.2a). |
| Verification ambition | **Match prototype's verified surface only.** Reproduce refinement proof for Guarded→Network. Every other pass, both backends: unverified for initial roadmap. Lock inference the one exception needing real design now — without it Go backend semantics undefined, not just unverified. |
| Join Calculus executability | Compiler's job: **emit a Join Calculus source file.** Later execution (interpreter, further lowering) open, §9.1. No interpreter unless asked. |
| Lock inference / Go concurrency safety | **In scope.** Rest of `Network2Go` already works (real goroutine concurrency); lock inference the missing piece. One lock family per process-local variable, from conflict analysis over shared process-local variables across atomic blocks — algorithm §5.7. |
| Example/regression suite | **Real harness, `lake test`.** `tests/regression/` = small hand-written accept/reject `.tla` fixtures, one per confirmed behavior, `Accept<What>.tla`/`Reject<What>.tla` — CamelCase (fixture filename must equal the TLA⁺ module it declares; `EXTENDS Foo` resolves to `Foo.tla` only). Run by `@[test_driver] lean_exe test` driving `Driver/Pipeline.lean` `runPipeline` in-process. Fixture asserts *where* a compile stopped and *what* it reported, not exit code. Per-fixture expectations in optional `<fixture>.expect.json` sidecar (absent ⇒ defaults from filename prefix). Warnings checked strictly (unlisted warning fails; `allowExtraWarnings` opts out); `suppressible` re-compiles under `-Wno-<name>` to check the flag silences it. Fixtures compile under bare flags; exception `searchPath`, a sidecar list of `-I` dirs relative to the fixture's directory (`EXTENDS` resolution is the only behaviour no expression triggers). Checked: outcome, failure stage, error code, reached stage, warnings — under `--timeout` (30 s default). **Not** the error message — code is the identity; a wording regex breaks on every improvement. Verdicts `PASS`/`FAIL`/`XFAIL`/`XPASS`/`SKIP` — `xfail` fixture runs and must fail; one that starts passing reports `XPASS` (counts as failure). Sequential by default: fixture compiles independent for `DriverState`, and `Common/Position.lean`'s span map is a process-global keyed on pointer addresses, never cleared, no two live values share an address. `-j > 1` opt-in because default is conservative, not unsafe. **Write fixtures in PlusCal C-syntax (`{ }`-braced bodies)**, never P-syntax — parser (§5.1) only accepts C-syntax. |
| Source positions | **Out-of-band side map, keyed on pointer address, registered at every construction site.** `Common/Position.lean` `registerSource`/`@@` and `posOf`/`match_source` attach spans to arbitrary values through `IO.Ref (Std.TreeMap USize SourceSpan)`, not a `Located` field per node. Address key makes `@@` free to write at any node without changing its type; every AST stays generic in exactly the parameters the pass needs. `TreeMap` not `HashMap`: ref is a module-`@[init]` global, runtime marks its contents multi-threaded, `modifyGet` re-marks per write — a `HashMap` bucket `Array` then fails `Array.uset`'s exclusivity check and deep-copies whole per `@@`, compile O(nodes²); red-black `insert` path-copies O(log n) regardless of mark state. Cost: a node whose position is never registered is indistinguishable from one whose address a dead node left an entry under; `posOf` answers with the dead span rather than failing. **Registration is an obligation: every pass registers every position-carrying node it builds, at the span of the node it was built from.** Position-carrying kinds: `Expression` (all TLA⁺ stages), `Statement` (all PlusCal stages), `Module`, `Process`, `Algorithm`. `Ref`, `Block`, `Branches`, `Declarations` carry none. Applies to *rebuilding* too — `subst` (`CoreTLAPlus.Expression.subst`, `ComputableTLAPlus.Expression.subst`), coercion discharge (`Coercion.apply`/`.applyComputable`), every `Bifunctor`/`Bitraversable` instance. A synthesized node with no source text takes the span of the construct it stands for (`await` from a rewritten `if`, a `with`-chain link, a `receive`'s consumption assignments); one standing for nothing in source (fall-through `goto`, empty body's `skip`) takes `SourceSpan.placeholder` (line `1`, not `0`, so it renders as a real line). Two inherent limits, not bugs: **nullary constructors** (`Expression.true`, `Statement.skip`) are unboxed scalars sharing one address program-wide, never carry per-occurrence positions (`Parser_/Annotations.lean` gives `Annotation` explicit `pos` fields for this); **compiled-in constants** (`Driver/Builtins.lean` stdlib operator bodies) have no source text, registered at `SourceSpan.placeholder`. Map never cleared between compiles in one process — safe: no two live values share an address, reading a position requires holding the value. |
| Build config format / toolchain | **`lakefile.lean` (Lean DSL), not `lakefile.toml`.** Current stable Lean toolchain — update `mathlib`/`batteries`/other pinned deps to match. Expect real breakage from the bump, including in `Extra/`'s vendored lemmas. |
| CLI shape | **Subcommands.** `fugue compile [FLAGS] <input>` compiles. `fugue explain <code>` prints what a diagnostic code means (`--list` for all, `Common/Diagnostics/Registry.lean`). `fugue help [-d\|-f\|-W\|-X]` prints what names one of `compile`'s table-valued flags accepts, one line per name; with no flag lists the topics. `help` holds the enumerations so `compile --help` stays a screen of one-line flag summaries. `explain` prints a code's page from `Diagnostics.embeddedPages` — every `docs/diagnostics/<code>.md` baked into the binary. `docs/diagnostics/` is canonical (hand-edited, one `<CODE>.md` per code plus `DIAG_STYLE.md`, the template); `lakefile.lean` generates `.lake/diagnostics/DiagnosticPages.lean` from it, `lean_lib Fugue.DiagnosticPages` claims it, same shape as `Fugue.Version`. Two writers because the corpus is a directory, not the config: `run_cmd` writes an empty `DiagnosticPages.lean` when absent (module resolution needs a file to find before any target runs), the `genDiagnosticPages` target fills it and regenerates it whenever the dir's `inputDir` trace changes (`extraDepTargets` / `include_str` alone do **not** trigger a rebuild — only a changed *source file* does, confirmed empirically). `run_cmd` fires only on config elaboration, so a cache-restored `lakefile.olean` skips the bootstrap and the build fails on the missing module — CI passes `-R` to the first `lake` of each job (`ci.yml`) to force re-elaboration. `$FUGUE_DOCS` points `explain` at a `docs/diagnostics` tree instead — edit a page, no rebuild. Not shipped beside the binary; embedding is the delivery. Two `#guard`s in `Fugue.lean` tie the corpus to the registry both ways — a registered code with no `docs/diagnostics/<code>.md`, or a page whose code was never registered, fails the build. `docs/diagnostics/DIAG_STYLE.md` is the page template. Version set in one place — `package Fugue`'s `version` field — reaching compiled code as a **generated source module**: `lakefile.lean` writes `.lake/version/Version.lean` (`abbrev fugueVersion : String`) on elaboration, `lean_lib Fugue.Version` claims it via `srcDir`. Source file, not a Lean option: compiler elaborates with `leanOptions`/`moreLeanArgs`, server with `moreServerOptions`, so an option would make the two disagree about the elaboration environment and overwrite each other's `.olean`s; and a module's build traces only its own source/options/imports/toolchain, so no extra dependency rebuilds anything. Generated outside `.lake/build/` so `lake clean` can't remove it while leaving the config that writes it. |
| CLI flag surface | GCC/Clang-style flags on `leanprover/Cli`, `javac`/`scalac`-style `:` before an option's value (`--help`/`--version` free), all on `compile`: `-d<name>[:<value>]` (debug — AST dumps, `-dtiming` per-pass timing), `-f<name>[:<value>]` (feature toggles, e.g. `-fno-color` — `Common/Errors.lean` `CompilerDiagnostic.pretty` takes `colored`), `-W<name>`/`-Wno-<name>` (per-warning, e.g. `-Wno-fair`), `-X<name>[:<value>]` (backend options; `go-pkg:<name>` sets the Go `package` clause, default `main`), `-o`/`--output` (a **file** not a directory — one Go file per compile, one package compiled as a unit; parent dirs created), `-t`/`--target go\|join`, `-I <path>` (module search path, §5.3). Join Calculus "flavors" open, §9.3. Go package name is `-Xgo-pkg` (property of the output, not of compiler behaviour). `leanprover/Cli` rejects a named flag given twice and parses `Array α`-typed flags as one comma-separated occurrence, so `-d`/`-f`/`-W`/`-X`/`-I` are each one `Array`-typed `ParseableType` flag (`-dname1,name2:value`, `-Idir1,dir2`), not repeatable GCC-style. **Value separator is `:`, not `=`** (per `javac -Xlint:all`, `scalac -Xprint:typer`): Cli claims `=` for its long-flag syntax and splits on it *before* matching short names, so `-ddump-dir=/tmp/x` would parse as a flag named `-ddump-dir`. With `:` attached and separated spellings both work; only the *first* `:` separates, so a value may contain one. `-X` has no long name, Cli requiring every flag one. `-ddump-dir:<path>` (default `.fugue/debug`) sets where `-d dump-<stage>` writes — `<dump-dir>/<input-file-name>-<stage>`, not stdout; value-less `-d dump-dir` is a hard error. `-d dtiming` dumps per-pass timing to `<dump-dir>/time.log`, one line per pass per file, appended across a run. `-d`/`-f`/`-W`/`-X` names validated against allowlists in `Fugue.lean` — unrecognized = hard CLI error. `featureOptionDocs` **derived** from the `Feature` enumeration (`Common/Flags.lean`), the single place a `-f` spelling is written: consumers read through the named accessor (`FlagsEnv.colored`, `.progress`), never a string literal. `debugOptionDocs` **derived** from `Stage`: one `dump-<stage>` per stage whose `Stage.artifact?` names an artifact — one exhaustive match answering both *whether* the stage dumps and *what* it writes — plus `dump-dir`; every dump site goes through `dumpStage`, so flag/file/stage can't disagree. `warningOptionDocs` **derived** from the diagnostic registry's `warningName`s, carrying each warning's code + summary, so `fugue help -W` and `fugue explain <code>` agree. `targetOptionDocs` still hand-maintained: one entry, no registry to derive from — revisit if `-X` grows. `-d` dump flags named after their stage (`dump-lex`, `dump-parse`, `dump-desugar`, `dump-typecheck`, …), not the artifact, so flag/file/stage share one spelling. Each of the four is one `OptionDoc` list — allowlist and help text one table, so an unlistable option is unacceptable. Flag *descriptions* name no individual option; `compile --help` one-liner derived from the same `HelpTopic` (Cli takes an identifier as well as a string literal where a description goes). |
| Diagnostic identity | **`rustc`-shaped code per diagnostic**: `E0042`/`W0003`, four digits, in the header (`error[E0026]: …`). `CompilerDiagnostic.code` has no default, so every error/warning instance must map *every* constructor to a registry entry — a new constructor fails to compile until registered. `Common/Diagnostics/Registry.lean` = single allocator: each entry carries stage, `-W` name if any, one-line summary; instances name entries, not number literals. Numbers permanent — never renumbered, never reused, gaps left where a drafted code turned out unnecessary. Wording free to change; code is the identity a regression fixture, a build-log grep, and `fugue explain` all key on. |
| Go runtime library location | **`runtime/tlaplus/` + top-level `persistent/treemap/` in this repo**, versioned with the compiler, not a separate repo — one file per TLA+ concept/stdlib module (`sequences.go`, `sets.go`, …), not one flat package. §5.7. |
| `Int` representation: machine `int` vs. `math/big` | **Go build tag, not a Fugue flag.** `math/big` default (matches the unbounded integers of the semantics verified against); `go build -tags fugue_machint` opts into machine `int` for speed. Emitted code identical either way — arithmetic through runtime functions, literals through `MkInt` — so the compiler has nothing to dispatch on. Whole compiled output, not per-declaration. §5.7. |
| Name-provenance (which module declared a name) | **Tagged on the AST by the elaborator, not a later side table.** Elaborator resolves every `.var` through `Γ`, already knows there whether it's a binder or top-level declaration and which module the latter came from. `Elaborator/Monad.lean` `Binding` carries `origin : Origin` (`.binder` / `.module name`), tagged at `Γ`-construction time (`Elaborator/Context.lean` `extend`/`extendAll` for binders; `Elaborator/Declarations.lean` own-declaration checking and `Driver/Modules.lean` imported-`Γ₀` fold for top-level names). `TypedTLAPlus.Expression.var` carries `Origin` so it survives past `Γ` into the checked AST — `WellFormedness` (§5.2a checks 2(c)/3) and `Network2Go` (§5.7, resolving whether a builtin-looking operator like `+`/`Naturals` is the real builtin or a user override) read it directly, no lookup. One real `.var`-construction site (`Elaborator/Expressions.lean` `inferExpr`), so this is a same-lookup tag. `lookupForeign : String → m (Option TypedModule)` (`MonadForeignLookup`, `Driver/Modules.lean`-backed) fetches a foreign module's declaration list once its name is known from `origin`. |
| Address visibility / deployment topology | **Accepted limitation.** Distributed PlusCal lets any process know any other's identity, so generated code assumes worst-case full connectivity ("star"). "Minimal needed addresses" static analysis: **not planned** — largely mooted by nameserver-based addressing (§5.6, §5.7). §7 stretch list. |
| Fairness (`isFair`, `fair process`/`fair+`) | **Largely ignored** — no way to insert fairness into target runtimes (neither Go's goroutine scheduler nor Join Calculus reaction-firing nondeterminism is fairness-aware). `isFair` carried through ASTs (parsing → both backends) for round-tripping only; neither backend's compilation scheme (§5.6, §5.7) acts on it. Parser emits a **warning** (§5.1) on any `fair process`/`fair+`. |
| `CONSTANT` values, process-set (`p ∈ S`) cardinality | **Left to the user of the compiled code.** `CONSTANT`s abstract (type + value) to the compiler — concretized only when someone builds an executable from generated code (no `main`, §5.7). No `ASSUME`-pinning requirement, no companion config file. Process set `p ∈ S` does **not** compile to `S`-many spawned goroutines/definitions — each process definition compiles to a **single entry point** (Go function, Join Calculus process definition), parameterized over the process's identity/address; user invokes once per concrete process. §5.3, §5.6, §5.7. |
| When imported modules get processed | **Eagerly and transitively**, right after desugaring, before type checking. Once main module parsed/desugared (§5.1–§5.2), driver recurses on each directly `EXTENDS`ed module — parse → desugar → recurse on *its* imports → type-check — before main module's own type checker (§5.3) starts. By the time main module reaches `[Goto]`/`[Assign]`/etc. rules, `Ξ` is fully populated for everything reachable. (`INSTANCE` out of scope, §8.) §5.3. |
| How `GuardedPlusCal.Algorithm.WellScoped` is established for Guarded→Network | **General preservation lemma, proved once**, not a per-run decision procedure: `CorePlusCal.WellScoped p → GuardedPlusCal.Algorithm.WellScoped (Computable2Guarded (Elaborator p))`, proved as part of `Elaborator`/`Computable2Guarded` verification (§5.5, §6.2), reused unchanged for every compiled program. `CorePlusCal.WellScoped`, the antecedent, authored fresh (§5.2a). |
| Language-subset exclusions for first type checker | **`INSTANCE` and `RECURSIVE` out of scope for now.** Neither in §8's subset, neither prior-art checkout parses them, both need real design before checkable. Revisit if a program needs either. For `RECURSIVE` if picked up: require explicit type annotation on the declaration for every operator in the group, extend `Γ` with all declared sibling types up front, check each body against its own annotation independently — breaks the circularity a mutually-recursive group creates for a bidirectional checker; standard precedent (mutual `def`/`def` in Coq/Agda/Lean always carry signatures); near-necessary for decidability under rank-1 polymorphism if any operator in the group is polymorphic. |
| `Ξ`'s cache: disk persistence and invalidation | **In-memory only for now, no disk persistence.** A disk-backed cache under `~/.local/config/.fugue` raises an invalidation question with no good answer: a compiler-side change (bug fix, stdlib-stub update, toolchain bump) can silently invalidate a cached module's typed form without touching that module's source. In-memory `MonadModuleCache` sidesteps it: nothing persists across runs, nothing goes stale. Disk persistence, once picked up, needs either a cache-key compiler/schema-version component (bumped whenever anything affecting typing output changes) or a global "cache format version" stamp wiping the directory on mismatch — undecided, revisit once checker stabilizes. |
| Pipeline order: well-formedness (§5.2a) vs. type checking (§5.3) | **Type checking runs first.** It already forces variable well-scopedness as a side effect of succeeding (out-of-scope/undeclared reference = `Γ`/`Σ`/`Δ`-lookup failure = type error) — a well-scopedness pre-pass would re-derive that. Well-formedness's other two checks (well-labelledness, no-bare-temporal-operators) have no typing dependency either way. Well-scopedness's "every reference resolves" half becomes redundant defense-in-depth; its "no shadowing / no duplicate names in scope" half is not implied by bidirectional type checking (a shadowed name still type-checks against something) and stays this pass's load-bearing job. §5.2a, §7. |
| Polymorphism instantiation / metavariable resolution | **Direction-aware solving, not naive eager unification** — subtyping axioms are asymmetric coercions, not equivalence. Lower-bound constraints (`T <: ?n`) solve eagerly (coercions run narrow→wide); upper-bound constraints (`?n <: T`) recorded pending, never solved from directly (would foreclose a narrower solution arriving later). Metavariable-vs-metavariable (`?m <: ?n`, both unresolved) must **not** merge into one — unsound, conflates two independently-constrained unknowns; record the link on the lower side, propagate once one side resolves from a real ground bound. A metavariable with no bounds at end of checking — including one whose only bound is an unresolved metavariable — is a hard type error, not a silent default. Full algorithm + counterexamples §5.3. |
| Coercion realization: where coercions live, how a *pending* one resolves | **`Coercion` = closed structural data, not an `Expr → Expr` closure** — a small recursive inductive (`id`, `strToSeq`, `seqToFun`, `tupleToSeq`, `set`, `tuple`, `record`, `function`, `comp` for axiom-chain composition), each constructor carrying exactly the type indices, field names, nested sub-`Coercion`s its structural rule needs, plus any fresh binder name (`x`/`y`/`i`) `Elaborator/Subtyping.lean` generated via `MonadFresh` at construction time (fresh at construction ⇒ fresh at discharge, per the `$`-freshness argument). Necessary because `[Receive]`'s coercion (below) must survive past `Typed2Computable`'s type change (`TypedTLAPlus.Expression` → `ComputableTLAPlus.Expression`) and discharge against the *later* type; a closure fixed at one concrete `Expr` type can't cross that boundary. Two structural recursions consume the same data, one per concrete expression type: `Coercion.apply` (`Core/TypedTLAPlus/Coercion.lean`, called at check time by every ordinary subtyping call site, e.g. `[Send]`'s payload) and `Coercion.applyComputable` (`Core/ComputableTLAPlus/Coercion.lean`, importing `Core.TypedTLAPlus.Coercion` — Computable depends on Typed, never the reverse). `subtype` builds `Coercion` data at each structural rule; all `Expr`-building logic (builtin references, `.map'`/`.tuple`/`.record`/`.fn`/`.choose` construction) lives in `Coercion.apply`/`.applyComputable`'s match arms. On **pending** (upper-bound check against unresolved `?n`), the expression is wrapped in `mvar : MVarId → Expr → Expr`, a node in `TypedTLAPlus`/`TypedPlusCal`'s grammar; checker context keeps, per unresolved `?n`, its pending upper bounds. The moment `?n` resolves, every `mvar` site for it is substituted with `.apply` of the now-computable coercion — part of metavariable resolution, not a separate pass — so `mvar` is fully eliminated before checker output reaches `Computable2Guarded`; downstream passes and both backends never see `mvar`. (The `Coercion` *value* a `receive` carries does survive further — below.) §5.3, §5.5. |
| `[Receive]`'s channel/reference coercion — where, given no expression to apply it to | **Stored on the `receive` statement node, discharged at `Guarded2Network`.** Unlike `[Send]`'s payload (a real sub-expression `Coercion.apply` wraps immediately), a received value isn't an expression at check time — arrives from network at runtime. Checker synthesizes the channel's element type and the destination reference's type, `subtype`s them directly (independent of `Channel <: Channel`'s structural check, which stays identity-only), stores the resulting `Coercion` as a field on the `TypedPlusCal`/`GuardedPlusCal` `receive` node. `Computable2Guarded` (§5.4) carries it unapplied (none of its four subpasses touch `receive`'s shape); `Guarded2Network` (§5.5) is the first pass where a `receive` becomes a concrete buffered read, discharging the coercion against the freshly-built `Head(inbox)`/`Tail(inbox)` `ComputableTLAPlus.Expression` via `Coercion.applyComputable` — no round-trip through `TypedTLAPlus.Expression`. §5.3, §5.5. |
| Diagnostic/error-model shape | **Per-pass error types, unified by a common rendering interface** — not one shared diagnostic sum type. Warning suppression (`-W`/`-Wno-<name>`) handled at emission point or by filtering before rendering — implementer's call. Mechanism exists in `Common/Errors.lean` (§4) — read before designing new. Fine to refactor error style or emission mechanism later if it doesn't hold up. |
| Generated-identifier hygiene | **Resolved by renaming; direction doesn't matter.** Hard requirement: **no shadowing ever introduced in generated code, checked at every pass, not just the final pretty-printer.** Same class as escaping target-language reserved words (PlusCal variable named `type`/`def` colliding with a Go/Join-Calculus keyword) — `Core/Go/Pretty.lean` has `keywords : Std.HashSet String` and `sanitize` (suffixes with `__`), applied at every identifier-print point. **Reserved words only:** Go's *predeclared* identifiers (`int`, `any`, `comparable`, `error`, `len`, `make`, …) are legally shadowable and generated code refers to them constantly, so the printer must not escape them; a user-chosen name colliding with one is renamed by `Network2Go` (the only place knowing provenance), which reads `Core/Go/Pretty.lean`'s exported `predeclared`. Covers compiler-introduced internal names (`recv`, `inbox`, lock variables, label atoms, §5.6/§5.7) and Join Calculus's own reserved surface. §5.2a, §5.6, §5.7. |
| Cross-cutting effects (flags, `Ξ`) vs. the monad-polymorphism convention | **Unified effect stack, not a driver/pass split.** Every function — pass code and CLI driver — written against one `{m : Type _ → Type _} [Monad m]`, every effect (errors, flags, module cache) a typeclass constraint on that same `m`. **(1) Flags = Reader effect.** Flags aren't uniformly `Option String` (boolean `-f`/`-W` vs. valued `-d<name>:<value>` vs. `-o`/`-t`/`-I`'s typed values), and proofs run on `Std.Do.WP`, which can't be instantiated at `IO`, so an opaque action gives the framework nothing to reason about; Reader is the transparent effect it handles. Typed `FlagsEnv` structure (full flag surface above), populated once from `Cli.Parsed`, accessed via `MonadReaderOf FlagsEnv m` + typed accessors (`getDebugFlag`/`getDebugOption`/`getFeatureFlag`/…). CLI hands one `FlagsEnv` to `Driver/Pipeline.lean` `runPipeline`, supplied as a real `ReaderT` layer (`Driver/Modules.lean` `Base`). No global `IO.Ref`: a `FlagsEnv` belongs to one compile, and the regression runner runs many in one process. **(2) `Ξ` = its own effect class**, `MonadModuleCache m` (`lookup`/`store` keyed by source hash), backed by a `DriverState` field threaded as `StateT` *under* `DiagT` (so entries written before a `throw` survive it). Genuine mutable-store effect; only shows up in `Elaborator`, not §6.2's proof surface, so no `Std.Do.WP` question. **(3) Guarded→Network proof, accepted knowingly:** `Algorithm.toNetwork` stays generic (`{m} [Monad m] [MonadFresh m] [MonadDiagnostic Empty G2NError m]` — `MonadDiagnostic`, not bare `MonadExceptOf`, so its `IO` instantiation pairs with `Fugue.lean` `runPassDiag`), not special-cased monomorphic. Refinement theorem proved against whichever concrete instantiation `Std.Do.WP` supports (`m := Id`, or `ReaderT FlagsEnv (DiagT Empty G2NError Id)`) — that, not the `IO`-run one, is the proof target. Running the same term at `m := IO` for CLI execution is a **separate, deliberately unverified step**, documented in `Guarded2Network`'s module docs. **(4) Fresh names get the same `IO.Ref` treatment as `Ξ`**, not a `StateT Nat` layer per pass. `MonadFresh m` (`Common/Fresh.lean`), monotonic counter behind `fresh : m Nat`, first needed by expression desugaring's tuple-pattern/multi-binder collapse (§5.2), recurring at `Computable2Guarded` `𝒞_par` (§5.4) and `Guarded2Network` `inbox`/`rx` naming (§5.5). Names `"<prefix>$<n>"` — `$` can't appear in a TLA⁺ identifier, so no scope-tracking to prove freshness. One counter per compile, in `DriverState` alongside `Ξ` — every pass draws from the *same* counter (strictly stronger hygiene: two passes' compiler-introduced names can't collide either), and no pass entry point (`runChecker`/`runDesugarer`/`toGuarded`/`toNetwork`) threads a `Nat`; `MonadFresh` lifts through `ReaderT`/`StateT`/`DiagT`, so a pass says `[MonadFresh m]` and never learns how the counter is stored. Entry points polymorphic in base monad, `[MonadFresh n]`; driver pins them at `Base`. Not process-wide: a global counter makes generated names depend on how many compiles preceded, wrong for the determinism-checking regression runner. |
| Shared builtin-operator recognizer | **One shared table, `Core/TypedTLAPlus/Builtins.lean`, not a per-pass string list.** Builtins uniform as `.opCall (.var name _ origin) args`, resolved by string name + `Origin` (`.intrinsic` for `builtinContext`'s core operators, `.module "Sequences"`/`.module "Naturals"`/etc. for stdlib stubs). `WellFormedness/Restrictions.lean`'s reserved-temporal-action check and `Typed2Computable`'s computable-builtin question both consult it. **Closed `inductive BuiltinOp`, one constructor per literal builtin** — exhaustiveness-checked `match`es for every consumer, at the cost of a third copy of each name in `builtinContext`/`builtinModules`. `reservedTemporalActionNames` stays a bare name-only list — these eight spellings can never be user-shadowed, so name-only matching is exact. |
| `Typed2Computable`'s two restrictions beyond `WellFormedness` | **`[A -> B]`/`[a:A,...]` (`fnSet`/`recordSet`) rejected outright; `forall`/`exists`/`choose`'s domain becomes structurally mandatory.** Both denote sets/expressions with no finite runtime representation under the finite-sets assumption — `ComputableTLAPlus.Expression` has no constructor for the first two, and the third's domain field is a plain `Expression`, not `Option (Expression)` (`WellFormedness/Restrictions.lean` check 3 already bans an unbounded domain reachable from the algorithm, so this enforces it structurally). Everything else `TypedTLAPlus`/`TypedPlusCal` can express, reachable from the algorithm, translates cleanly. |

---

## 3. Prior art map

Three sources exist; none is "the codebase to continue." Read the relevant one before
touching the corresponding area.

### 3.1 `github.com/mesabloo/fugue` (public mirror)
- `main`: only branch that builds an end-to-end CLI (`pcvc`). Pipeline in `Main.lean`:
  parse TLA+ (`SurfaceTLAPlus`/`SurfacePlusCal`) → resolve annotations →
  `SurfacePlusCal.Algorithm.toGuarded` (fused desugar+typecheck+guard, *not* split) →
  desugar expressions to `CoreTLAPlus` → `toNetwork "inbox"` → `toGoCal` → pretty-print
  Go. Only Go backend; no real type-checking pass (types untracked past annotations).
  `VerifiedCompiler/` here has a working `Trace` + `StrongRefinement` framework;
  `GuardedPlusCal`/`NetworkPlusCal` both carry `Semantics/Denotational.lean` +
  `Semantics/Lemmas.lean` — the hand-verified-pass reference point.
  `GoCal/Semantics/{Denotational,Denotational2}.lean` = two abandoned Go-semantics
  attempts (1640, 1040 lines), dropped in later branches.
- `develop` / `lock-inference` (same commit): restructuring into the module layout this
  plan adopts (§4): `Common`, `Core/*`, `Parser_`, `Desugarer`, `Checker`,
  `Computable2Guarded`, `Guarded2Network`, `Network2Go`, package `Fugue`. Introduces
  explicit `CorePlusCal`, `TypedPlusCal`, `TypedTLAPlus`, `TypedSetTheory` stages absent
  from `main`. Mostly stubs/partial — except `Parser_`, substantial; the local checkout
  (§3.2) has it further along, and is the one to port from.
- `go-semantics`: newest branch, replacing both `GoCal` semantics attempts with a
  metric-space/domain-theory treatment (`Extra/Topology/IMetricSpace*`, Lipschitz maps,
  uniform continuity, closed embeddings — recursive domain equation `P ≅ F(P)` via Banach
  fixpoint). Hard, unfinished research; §6.4.
- `docs`: CI plumbing for `doc-gen4`, no content of interest.

### 3.2 `~/Documents/distpcal-compiler` (private, more current)
Same project, renamed remote, further along in places. Local branch `typechecker`
(uncommitted) has active work on `Checker/Typechecker/*`, `Core/Go/{Syntax,Pretty}.lean`,
`Core/README.md`. Extras not on the public mirror:
- `Core/CorePlusCal/Syntax.lean`: statements/blocks `Bool`-indexed on "terminal" (ends in
  `goto`) at the *type* level, so "all blocks end in an explicit goto" is a structural
  invariant. Carried forward.
- `Parser_/{Annotations,Common,Monad,PlusCal,TLAPlus}.lean` +
  `Parser_/Tokens/{PlusCal,TLAPlus}.lean`: ~2,200 lines, not a stub — supersedes the older
  `SurfaceTLAPlus`/`SurfacePlusCal` `Syntax.lean`/`Tokens.lean` that `fugue main` parses
  with. Already targets the `Core/SurfaceTLAPlus`/`Core/SurfacePlusCal` ASTs in this
  checkout. **This, not `fugue main`'s parser, is the source to port from** (§5.1).
- `lib/{address.go,rand.go,tlaplus.go}`: partial Go runtime library imported by generated
  code (`github.com/mesabloo/distpcal-compiler/lib`), incl. TLA+ value encodings (`Seq`,
  `Set`, functions).
- `tests/{PingPong,TPC,LamportMutex}`: hand-built example algorithms with real generated
  Go and a hand-written nameserver (TCP/UDP address registration + lookup,
  `charmbracelet/log`) to run examples across processes — already-prototyped analogue of
  the Join Calculus chapter's `register`/`lookup`, worth mining for the Go runtime design.
- `Desugarer/TLAPlus.lean` has real code (`Expression.desugar`, `Declaration.desugar`,
  `Module.desugar`) but incomplete against §5.2's four transformations — check coverage,
  don't assume. `Desugarer/PlusCal.lean` is an empty stub — statement-level desugaring
  (Distributed PlusCal → PlusCal with explicit gotos, feeding `cflow`/`par`/`flat`/`reord`)
  has no code anywhere, despite being specified in the thesis.

### 3.3 The thesis (`reference/thesis.pdf`)
Maps onto the pipeline as below. "Stub" = section headers only — treat as *to be
designed*, using surrounding chapters and prior-art code as guidance.

| Thesis chapter | Pipeline stage | Status |
|---|---|---|
| 3.1 | Bidirectional type checker | Fully written (§5.3 reproduces it) |
| 3.2 | Distributed PlusCal → Guarded PlusCal | Fully written, incl. §3.2.3.4 (guard reordering `𝒞_reord`, covering both `await` and `receive` guards) — §5.4 matches |
| 4 | "Compiler verification, denotationally" | Stub (title only) |
| 5 | Guarded PlusCal → Network PlusCal | Stub in thesis — *implemented and proved* in `fugue main`. Read code, not thesis. |
| 6 | Denotational account of Go | Fully written, heavy domain theory. §6.4. |
| 7 | Network PlusCal → Go, lock inference | Fully written: §7.1 (atomicity/lock inference, §5.7); §7.2.1.1 (Go representations of each TLA+ type incl. `Channel(τ)`); §7.2.1.2 (compiling TLA+ expressions — booleans/quantifiers, sets, functions); §7.2.2 (operator/function definitions — non-recursive vs. parametric operators, recursive functions via tie-the-knot `MkRecFn`); §7.2.3.1 (atomic blocks — branch-as-function scheduling loop, lock parameters, `LOCK`/`UNLOCK`, per-construct compilation rules); §7.2.3.2 (threads and whole processes — thread chaining, receive-relay thread, `INIT_LOCKS`, `done`/`done'` channels). §5.7 tracks all of it. **§7.3** = fully worked Go compilation of Ping-Pong `Pong` end to end (lock inference result, every atomic block's function, both threads, process function, concrete `Network` struct) — cross-check §5.7 against it directly, same role as §8.6 for the Join Calculus backend. **§7.4** ("informal correctness proof sketch") states a conjecture (`proc(net, mailbox, self)` refines `P` in isolation, assuming the network is correctly wired) but leaves both the argument and mechanization as future work — a stub for verification, no proof obligation in this project's scope. `Channel(τ)` deliberately unrepresented in the general case; that plus §7.2.3's `.Send`/`mailbox` API surface is the whole of what the compiler owes the wire mechanism — endpoint internals are outside the thesis and outside this compiler. |
| 8 | Network PlusCal → the Join Calculus | Fully written, worked Ping-Pong example. Primary spec for the new backend; §5.6 is the condensed version. |
| 9 | Conclusion | Stub (title only) |

---

## 4. Target project layout

Module structure from `distpcal-compiler`'s `develop` branch, plus two additions for the
Join Calculus backend. Package `Fugue`, executable `fugue`.

```
Fugue/                          (this repo)
├── lakefile.lean                package Fugue; Lean DSL config (not `.toml`); see §2 for toolchain pin
├── lean-toolchain
├── CustomPrelude.lean            vendored, pruned
├── Extra/                        vendored, pruned — data structure lemmas (AList, Finmap, HashMap, …)
├── ProgressBar/                  vendored as-is — CLI spinners for the `fugue` executable
├── VerifiedCompiler/              vendored, extended as passes get proofs
│   ├── Trace.lean                 ordered-monoid trace algebra
│   ├── Relation.lean
│   └── Denotational/
│       ├── Notations.lean
│       └── StrongRefinement.lean  Terminating/Diverging refinement, composable across passes
├── Common/                       vendored, pruned — generic like Extra/VerifiedCompiler/ProgressBar, not domain-specific
│   ├── Position.lean               source positions, `Located`
│   ├── Errors.lean                 shared diagnostic infrastructure
│   └── Pretty.lean                 shared `Std.ToFormat`-style pretty-printing helpers
├── Core/                         fresh — one subfolder per IR, each with Syntax.lean (+ Pretty.lean, + Semantics/ once verified)
│   ├── SurfaceTLAPlus/  SurfacePlusCal/         parser output (CSTs)
│   ├── CoreTLAPlus/     CorePlusCal/            desugared (§5.2)
│   ├── TypedTLAPlus/    TypedPlusCal/           type-checked (§5.3); TypedTLAPlus/Builtins.lean is the shared builtin-operator table (§2)
│   ├── ComputableTLAPlus/ ComputablePlusCal/    output of a separate pass *after* §5.3, not of the checker itself (§5.3); Syntax/WellScopedness.lean ported (§5.2a)
│   ├── GuardedPlusCal/                          guards floated to block-start (§5.4); Syntax/WellScopedness.lean ported (§5.2a)
│   ├── NetworkPlusCal/                          explicit inbox, no receive-guards (§5.5)
│   ├── JoinCalculus/                            NEW — guarded-reaction JC dialect (§5.6)
│   └── Go/                                      Go AST + pretty-printer (§5.7)
├── Parser_/                      ported from prior art, refactored — lexer + parser for TLA+ modules / Distributed PlusCal,
│                                    including annotation parsing + placement checking (§5.1)
│                                    (named `Parser_`, not `Parser` — clashes with the `fgdorais/Parser` package import)
├── Desugarer/                    fresh — Surface → Core, for both TLA+ expressions and PlusCal statements
├── Elaborator/                   fresh — bidirectional type checker, Core → Typed
├── Driver/                       fresh — recursive `EXTENDS` resolution: not type-checking rules, the orchestration around invoking them
│                                    (locate/lex/parse/desugar a module, recurse on its own `EXTENDS`, module cache `Ξ`, stdlib operator table)
├── WellFormedness/               fresh — well-labelledness + variable well-scopedness + no-bare-temporal-op checks over Core ASTs, run after the type checker (§5.2a)
├── Typed2Computable/              fresh — `TypedTLAPlus`/`TypedPlusCal` → `ComputableTLAPlus`/`ComputablePlusCal`, run after well-formedness (§5.3)
├── Computable2Guarded/                fresh — the cflow/par/flat/reord pipeline (§5.4)
├── Guarded2Network/               ported from prior art incl. its proofs (§5.5)
├── Network2JoinCalculus/          NEW (§5.6)
├── Network2Go/                    fresh, incl. LockInference submodule (§5.7)
├── Fugue.lean                     CLI entry point (executable `fugue`)
└── reference/
    └── thesis.pdf                  copied in for implementer reference
```

§3 = pointer-to-prior-art doc; no separate `reference/NOTES.md`.

Each `Core/<Lang>` module owns one AST + its pretty-printer; semantics
(`Semantics/Denotational.lean`, `Semantics/Lemmas.lean`) added only for passes with (or
actively getting) a refinement proof. `lean_lib` targets in `lakefile.lean`: `Fugue.Core`,
`Fugue.Parser`, `Fugue.Desugarer`, `Fugue.WF`, `Fugue.Elaborator`, `Fugue.Driver`,
`Fugue.T2C`, `Fugue.T2G`, `Fugue.G2N`, `Fugue.N2JC`, `Fugue.N2Go`.

---

## 5. The pipeline, stage by stage

Running example: thesis Ping-Pong (§8.6, `tests/PingPong/PingPong.tla` in
`distpcal-compiler`) — two processes exchanging `"Ping"`/`"Pong"` over per-process
mailboxes. Small enough to hand-trace every stage; the thesis's own worked example for the
one fully-specified backend (Join Calculus). First smoke-check target, distinct from the
fixture suite (§2).

### 5.1 Lexing & parsing
**Input:** raw TLA+ module source (`.tla`), embedded Distributed PlusCal algorithm inside a
`(* --algorithm ... *)` comment block, plus `@type`/`@mailbox` annotations in comments
(annotation style: Ping-Pong listing, thesis §8.6).
**Output:** `SurfaceTLAPlus.Module` wrapping a `SurfacePlusCal.Algorithm`.

Ported from the **local** `~/Documents/distpcal-compiler` checkout (§3.2):
`Parser_/{Annotations,Common,Monad,PlusCal,TLAPlus}.lean` +
`Parser_/Tokens/{PlusCal,TLAPlus}.lean` (~2,200 lines, `fgdorais/Parser`-based, hand-rolled
lexer producing `Located` tokens), targeting the `Core/SurfaceTLAPlus`/`Core/SurfacePlusCal`
ASTs. `fugue main`'s parser is at most a secondary reference.

`@rx` is not a source annotation — internal marker for Network PlusCal pretty-printing
(§5.5's output, consumed by §5.6/§5.7). `Annotation` (`Parser_/Annotations.lean`) has only
`@type`/`@mailbox`/`@parameter`; whoever implements Network PlusCal pretty-printing (§5.5
onward) introduces `@rx` there.

Annotations (`@type`, `@mailbox`) parsed as a distinct pass over comments
(`resolveAnnotations`) — TLA+ grammar has no room for them, and comments vs. grammar are
orthogonal. Two jobs: parse the annotation's content (e.g. the type expression inside
`@type`), and check *placement* (a kind appears only where structurally meaningful, e.g.
`@mailbox` only immediately before a `process` declaration).

**`fair process`/`fair+` emits a warning, not an error.** `isFair` parsed and carried
through for round-tripping only (§2); parser emits a warning (`-W` surface, §2) on seeing
`fair process`/`fair+`.

**`ParserWarning.unusedAnnotation` declared, never constructed.** An annotation-shaped
comment (`\* @type: …;`) where nothing consumes it should warn rather than read as prose.
Most PlusCal statement kinds (`skip`, `goto`, `x := e`, `while`, `if`, `receive`, `send`,
`either`, …) never call `tryParseAnnotations` before them — only `with`/`multicast` do — so
a misplaced annotation there is absorbed as an ordinary comment token before it reaches
annotation-parsing. Generic detection = `parseUnlabeledStatement` calling
`tryParseAnnotations` once up front and threading the result into every statement-kind
parser, warning where it's non-empty and the kind doesn't attach it — deferred.
`-Wno-unused-annotation` is already a valid flag (registry-derived), with nothing to
suppress yet.

Syntax errors inside annotations point at a real position: `tryParseAnnotations` resolves
the failing offset in the flat concatenated-comment string back to its owning comment's
span (`commentBoundaries`/`commentIndexOf`) and reports via the outer parser's `posOverride`
— the field for exactly this (a sub-parser's flat-string offset isn't the token-indexed
outer parser's to express otherwise).

`\@` is an escaped literal `@` in comments (`tryParseAnnotations'`, `Parser_/TLAPlus.lean`)
— never starts an annotation, so prose can mention `@type`/`@mailbox`/`@parameter` inertly.

Known parser gaps: §9.2.

### 5.2 Desugaring
**Input:** `SurfaceTLAPlus`/`SurfacePlusCal`. **Output:** `CoreTLAPlus`/`CorePlusCal`.

`Core/CoreTLAPlus/Syntax.lean` and `Core/CorePlusCal/Syntax.lean` written fresh (§2/§4) —
`CoreTLAPlus` is a deliberately simple core (no `prefixCall`/`infixCall`/`postfixCall`, no
separate `bforall`/`forall` pairs, no `@`-referencing case). Only `CorePlusCal.Statement`'s
`Bool`-indexed terminal encoding is carried forward from prior art (§2/§3.2).

Two independent halves:

- **Expression desugaring** (`SurfaceTLAPlus.Expression.desugar`, `Desugarer/TLAPlus.lean`):
  produces `CoreTLAPlus`. Four transformations, against the thesis's formal typing rules
  (§3.1.3):
  - `@` (TLA+ self-reference inside `EXCEPT`) desugars to the expression being `EXCEPT`ed.
    `[x EXCEPT ![1, 2, 3] = @ + 3]` → `@` becomes `x[1, 2, 3]`. `Reader`-based
    (`Option (CoreTLAPlus.Expression α)`, `none` outside any `EXCEPT` update).
  - Conjunction/disjunction *lists* (indentation-sensitive `/\`/`\/`) desugar to binary
    infix `/\`/`\/`.
  - Prefix/postfix/infix operator applications desugar to prefix-style: `1 + 2` → `+(1,
    2)`, `TRUE^*` → `^*(TRUE)`. `CoreTLAPlus.Expression` needs no operator-enum types —
    every builtin operator becomes an ordinary `opCall` with callee
    `Expression.var "<canonical-spelling>"` (`.var "+"`, `.var "\\in"`), same constructor as
    a user-defined name. Sound: no TLA⁺ identifier can be spelled like an operator symbol
    (lexer's `identifierOrKeyword`/`symbol` productions disjoint); matches the thesis's
    formalization (§3.1.3 — operators are pre-populated *names* in Γ, not a syntactic
    category). Canonicalization (`<=`/`=<`/`\leq` → one string) happens once, in
    `Desugarer/TLAPlus.lean` `{Prefix,Infix,Postfix}Operator.canonicalName`. Unary minus
    gets its own spelling `"-."`, distinct from binary `"-"` (same trick as "Specifying
    Systems"); surface syntax unchanged, only the `Γ`-lookup-facing name. Separate
    builtin-module declarations: `"-" : (Int, Int) ⇒ Int` in `Naturals`,
    `"-." : (Int) ⇒ Int` in `Integers`.
  - Every quantifier-like binder (`\A`/`\E`/`\AA`/`\EE`/`CHOOSE`/set-map/set-filter/function
    literals) binds exactly one variable over at most one domain (thesis Figs.
    3.1.2/3.1.3/3.1.5/3.1.6); `CoreTLAPlus`'s quantifier constructors have no
    multi-variable or tuple-pattern case. Two desugaring shapes:
    - tuple-pattern binders (`\A ⟨x, y⟩ ∈ S : P`, `[⟨m,nd⟩ ∈ S ↦ …]`) → one fresh variable
      + substitution (`\A z ∈ S : P[z[1]/x, z[2]/y]`);
    - **multi-variable *quantifiers*** (`\A x, y : P`, `\A x, y ∈ S : P`) → **nested**
      single-variable quantification (`\A x : \A y : P` / `\A x ∈ S : \A y ∈ S : P`, a
      logical equivalence);
    - **multi-binder *function literals/set-maps*** (`[x ∈ A, y ∈ B ↦ e]`, `{e : x ∈ A, y ∈
      B}`) do *not* nest (would build a function of functions) — collapse to *one* fresh
      variable over the **Cartesian product** `A × B` (thesis Fig. 3.1.3, single-variable
      function rule).

    All reuse `CoreTLAPlus.Expression.subst` (`Desugarer/TLAPlus.lean`) — non-capture-
    avoiding, stops at any binder rebinding the target name, sufficient since well-scoped
    programs never shadow (§5.2a). `MonadFresh`/`freshName` (`Common/Fresh.lean`, §2)
    generates fresh names, collision-free via `$` (no TLA⁺ identifier contains it); recurs
    at `Computable2Guarded` `𝒞_par`, §5.4.
- **Statement desugaring** (Distributed PlusCal → PlusCal with explicit gotos,
  `Desugarer/PlusCal.lean`): written fresh. Target: `Core/CorePlusCal/Syntax.lean`'s
  type-indexed `Statement α β (terminal : Bool)` encoding (§3.2). Design points:
  - `Process.threads : List (List (String × Block α β true))` — outer list = parallel
    `{...}` threads, inner list = each thread's labelled blocks. Labels/`goto`s can appear
    *nested* inside `if`/`while`/`either` bodies; only `with` disallows them. Job here =
    **basic-block extraction**: pull each nested labelled sub-block out to its own
    top-level `(label, Block)` entry in the thread, stitch control flow with explicit
    `goto`s. `desugarSegment` walks a thread's statement list with an accumulator of
    already-desugared non-terminal statements; on a label or a nested construct needing
    extraction, closes the current segment as `CorePlusCal.Block ... true` and recurses.
    Fresh loop-back/continuation labels (`"loop$n"`/`"cont$n"`, via `MonadFresh`/
    `freshName`) only when no existing label to reuse. Dispatch between the cheap path
    (`desugarLabelFreeBlock`, always `Block ... false`) and `desugarSegment` is by
    `Statement.needsExtraction`/`List.needsExtraction`, checking **both** "body contains a
    label anywhere" and "body's last statement resolves to a bare `goto`" (first alone
    misses an `either`/`if` branch ending in an explicit `goto` with no nested label).
    `CorePlusCal.Statement.while` constructor: `{b} (cond : β) (B : Block α β b) :
    Statement α β false` — loop body may be terminal (explicit loop-back `goto`), the
    `while` itself stays non-terminal.
  - A `goto` immediately followed by *unlabelled* statements is rejected
    (`gotoNotInTailPosition`) — unreachable dead code (a `goto` followed by a *label* is
    the ordinary "block ends here" case). `with` rejects any nested label (`nestedLabel`).
    **`goto Done` auto-insertion**: a thread's last label running out of statements without
    an explicit terminal gets `goto Done` — `"Done"` is a reserved sentinel needing no
    matching label definition (standard PlusCal convention); well-labelledness (§5.2a)
    exempts `"Done"` from "every `goto` targets a real label".
  - **A `while` must be immediately preceded by a real label, never auto-inserted.** Manual
    §3.2.4/§3.7 (unconditional, unlike `if`/`either` which only need a label *after* them);
    thesis `𝒞_cflow` (§5.4) assumes `while` starts the block. Real PlusCal's default
    translator rejects an unlabelled `while` (auto-insertion is the opt-in `-label` flag).
    Same for `if`/`either`'s "must be followed by a label" (§3.2.2/§3.2.3), no
    auto-synthesis. `desugarSegment`'s `while` case throws `DesugarError.whileNotLabelled`
    whenever the current segment already has content or has no real label to attribute the
    `while` to. `desugarContinuation` throws `DesugarError.notFollowedByLabel` whenever
    what follows a label/`goto`-containing `if`/`either` isn't already labelled.
    `List.needsExtraction` flags *any* `while` in a nested body, unconditionally, so
    `desugarSegment` always checks its labelling.
  - **A `while` may never appear inside a `with` body, at any depth** (Manual §3.2.6, its
    own unconditional restriction — `with`'s one-atomic-step semantics can't provide the
    label a `while` needs). Threaded `insideWith` flag (propagated through `if`/`either`
    sub-bodies), checked on seeing a `while` before recursing; `DesugarError.whileInWith`.
  - **A `with`-bound name can never be a write target** — neither direct assignment
    (`with (x = 3) { x := 9; }`) nor a `receive` into it — a `with`-bound name is a local
    binding to a fixed value, not a process variable. `WithContext.boundVars : List String`
    = names bound by any enclosing `with` (inner `with` prepends its own).
    "Inside a `with` body?" (for `whileInWith`) = `¬ boundVars.isEmpty`; write-rejection =
    `boundVars.contains` against each write's target name (`assign` LHS `Ref`, `receive`
    target `Ref`), throwing `DesugarError.withBoundVarWritten (pos) (name)`. Transitive
    (inner `with` writing an *outer* bound name is rejected too), applies to `assign` and
    `receive`.
  - **Annotations disappear from `CorePlusCal`/`CoreTLAPlus`, leaving only content.**
    Content that fits "the declared-type annotation at whatever checking stage" stays on
    the same `α` `Statement`/`Block`/`Branches`/`MulticastFilter` slot;
    `CorePlusCal.Declarations` shares that `α` (not `Option`-wrapped, not a second type
    parameter) so `Process`/`Algorithm` keep ordinary two-parameter `Bifunctor`/
    `Bitraversable` instances. `Declarations.variables/channels/fifos` entries carry `α`
    directly (`List Annotation` out of statement desugaring, `Option Typ` after
    `CorePlusCal.Algorithm.stripEmbeddedTypeAnnotations`, which also strips
    `MulticastFilter`'s per-bind annotations and a `with`-bound variable's own annotation).
    Content that can't fit this shape (`@mailbox`'s channel name/index expressions,
    `@parameter`'s presence-as-`Bool`) is extracted early as its own concrete field, by
    validation fused into statement desugaring (`Process.desugar`/
    `Declarations.desugarCheck`) — one `CorePlusCal.Algorithm`, always fully checked.
    `CorePlusCal.Process` carries `mailbox : Option (String × List β)` (from ≤ 1
    `@mailbox`, `extractMailbox`); `Declarations.variables` carries `isParameter : Bool`
    (`Declarations.desugarCheck`). `CoreTLAPlus.Expression` needs no AST change — already
    `Bifunctor`/`Bitraversable`-generic, so `Expression (Option Typ)` is a different
    instantiation.
  - **A `with`-bound variable can carry its own `@type`** (`with (* @type: Int; *) x = e {
    … }`). `CorePlusCal`/`SurfacePlusCal Statement.with`'s `vars` has an `α` slot
    (`String × α × Bool × β`); `Parser_/PlusCal.lean` `parseWith` calls
    `tryParseAnnotations` per binder, using a bare `token (.tla .lparen)` (no `lexeme`) for
    the wrapping paren, not `parens` (which would swallow the first binder's annotation
    comment as trailing whitespace) — same workaround `parseFilter` (multicast) uses.
  - `@mailbox`'s filter arguments (`var[e₁, …, eₙ]`) desugared to `CoreTLAPlus.Expression`
    via `SurfaceTLAPlus.Expression.desugar` run inside `Process.desugar`, through a local
    instantiation of the same `ReaderT (Option (CoreTLAPlus.Expression α)) (DiagT
    DesugarWarning DesugarError IO)` stack `SurfaceTLAPlus.Module.runDesugarer` uses
    (`desugarMailboxArg`) — same process-wide fresh-name counter (§2), not a `0`-restarted
    one.
  - **A multi-binder `with` desugars to a chain of single-binder `with`s.** `with (x = e1,
    y ∈ e2, …) { B }` (comma list at surface syntax, unchanged in
    `SurfacePlusCal.Statement.with`) → `with (x = e1) { with (y ∈ e2) { … B } }`.
    `CorePlusCal.Statement.with` has five fields (`var : String`, `ann : α`, `«=|∈» :
    Bool`, `val : β`, body `Block`) — one binder per `with`, at the type level.
    `buildWithChain` folds the list into a right-nested chain: innermost binder wraps the
    desugared original body; every earlier binder wraps the next link in a label-free
    `Block` (`⟨[], ·⟩`). Called by `Statement.desugarLabelFree`'s `.with` case;
    `WithContext` bound-name tracking extends with *every* binder's name for the *whole*
    original body in one step.
  - **A `multicast` filter collapses to a single binder over a set of recipients.**
    `multicast(c, [x₁ ⋈₁ e₁, …, xₙ ⋈ₙ eₙ ↦ v])` reaches every `c[y]` for `y` in the
    **Cartesian product** of the components: `∈`-bind contributes its set, `=`-bind the
    singleton `{e}`. Components name the parts of a recipient *tuple*, do **not** scope
    over one another (a later component mentioning an earlier name = unbound variable,
    reported by the checker with no rule of its own). Any number, any order; `n = 1` is the
    thesis's `[y ∈ e1 ↦ e2]`. `MulticastFilter.collapse` builds one fresh binder over `D₁
    \X … \X Dₙ` and rewrites each original name in `v` to its projection off that binder —
    same `SurfaceTLAPlus.tupleProj`/`cartesianProduct` helpers as multi-binder function
    literals (`collapseToSingleBinder`); `n = 1` passes through untouched.
    `CorePlusCal.Multicast` (`recipient`/`ann`/`set`/`val`) replaces surface
    `MulticastFilter` from `CorePlusCal` down — **no pass after the desugarer reconstructs
    which bind was which**; backends receive a set and a payload. The collapsed binder's
    declared type is the tuple of the components' `@type`s, only when every component
    carries one: partial annotation warns (`partial-multicast-annotation`, W0005) and keeps
    none (recipient's type fixed by the channel's declared domain either way). Empty
    component list unrepresentable — parser reads with `sepBy1`.
  - **Every function call / `EXCEPT` index is unary.** `CoreTLAPlus.Expression.fnCall`/
    `.except` take a single `Expression α` each — a surface multi-index call `f[e₁, …, eₙ]`
    (`n > 1`; same for an `EXCEPT` step `![e₁, …, eₙ]`) desugars to `f[<<e₁, …, eₙ>>]`;
    `f[e]` (`n = 1`) stays `f[e]`, **never** `f[<<e>>]`. `SurfaceTLAPlus.Expression.fnCall`/
    `.except` unchanged (`List`, matching surface comma list); collapse in
    `Desugarer/TLAPlus.lean` `Expression.desugar` via `wrapIndices : List (Expression α) →
    Expression α` (`[e] => e`, `es => .tuple es`), alongside `tupleProj`.
  - **`SurfacePlusCal`/`CorePlusCal.Ref` (assignment target `f[e₁, …, eₙ] := v`, or a
    `receive`/`send` channel argument) gets the same unary treatment plus field-access
    support.** `Ref.args` = `List (String ⊕ List β)` at Surface, `List (String ⊕ β)` past
    desugaring (`CorePlusCal.Ref`, `ElaboratedPlusCal.Ref` shared by
    `TypedPlusCal`/`ComputablePlusCal`) — one entry per path segment, left-to-right, `.inl`
    for a `.field` segment, `.inr` for a `[e₁, …, eₙ]` bracket-index group (same `String ⊕
    _` shape as `ComputableTLAPlus.Expression.except`'s update-path). Unary rule per `.inr`
    group: `f[e₁, …, eₙ] := v` (one group) → `f[<<e₁, …, eₙ>>] := v`; `f[e₁][e₂] := v` (two
    groups) unaffected; `f[e] := v` stays; `r.field := v` = bare `.inl` segment. Each of
    `SurfacePlusCal.Ref`/`CorePlusCal.Ref`/`ElaboratedPlusCal.Ref` maps/traverses only the
    `.inr` side, `.inl` field names passed through. `ElaboratedPlusCal.Ref` carries a
    resolved `baseType : τ` (the *base variable*'s type from `Γ`, before any `.args` step —
    not the result type, which is cheap to recompute via `Ref.stepType`/`.resultType`
    walking the same `stepInto`/`indexInto` step-rule; the reverse isn't possible — an
    intermediate step's type isn't recoverable from the final result type alone) so it uses
    hand-written per-caller mapping rather than a `Functor`/`Traversable` instance.
    `CorePlusCal.Statement.assign`/`.receive`/`.send` reference `CorePlusCal.Ref`.
    Conversion (`SurfacePlusCal.Ref → CorePlusCal.Ref`, `Ref.desugarRef`, reusing
    `SurfaceTLAPlus.wrapIndices` on each `.inr` group via `Sum.map id`) is inline in
    `Statement.desugarLabelFree`'s `.assign`/`.receive`/`.send` cases.
    `Parser_/PlusCal.lean` `parseRef` reuses `SurfaceTLAPlus.Parser.parseExcept`'s `.`-token
    path machinery. `Elaborator/PlusCal.lean` `inferRef` (a `Γ`-lookup on `name` + one step
    per path segment) reuses `Elaborator/Expressions.lean` `stepInto` directly.
    `WellFormedness/Reachability.lean` `walkRefArgs` and `Core/SurfacePlusCal/Pretty.lean`'s
    `Ref` formatter both walk `.inr` entries only (`.inl f` prints as `.f`, `.inr e` as
    `[e]`, interleaved in path order).

### 5.2a Well-formedness checking
**Input/output:** `CoreTLAPlus`/`CorePlusCal` — checking pass, not a transform: accepts or
rejects with a diagnostic, produces no new AST. Runs **after** type checking (§5.3), not
after desugaring (§2 pipeline-order row). Checks purely syntactic — declarations/gotos/
operator shapes already resolved by the time `CorePlusCal`/`CoreTLAPlus` exist.

- **Well-labelledness**, from the PlusCal manual's placement rules
  (`https://lamport.azurewebsites.net/tla/p-manual.pdf` §3.2 statement-by-statement, §3.7
  exhaustive list). Not every rule needs a check here:
  - **Guaranteed by `CorePlusCal`'s type, any producer:** every thread starts with a label
    and every block ends in one terminal statement (`Process.threads : List (List (String
    × Block α β true))` shape — `Statement α β true` has no constructor except `goto`); "an
    `if`/`either` containing a labelled statement or `goto` must be followed by a label"
    (§3.2.2/§3.2.3) — `CorePlusCal.Statement.if`/`.either`'s `Bool` index forces both
    branches to share one terminality, so a terminal branch makes the whole `if`/`either`
    `Statement α β true` and only a block's terminal `end`.
  - **Guaranteed because `Desugarer/PlusCal.lean` (§5.2) is the only producer** — not
    type-encoded, latent risk if that changes: "a `while` must be labeled" (§3.2.4/§3.7,
    desugarer throws `whileNotLabelled`); "`with`'s body cannot contain a labelled
    statement, a `goto`, or a `while`" (§3.2.6, `nestedLabel`/`whileInWith`).
  - **This pass's actual work:**
    - *Every `goto` targets a label that exists* in the enclosing process/thread (or the
      reserved `"Done"` sentinel). §5.3's `[Goto]` does no check of its own (correctly — a
      `String` label name is data).
    - *No two assignments to the same variable within one atomic step, on the same control
      path* (§3.2.1/§3.7) — walk each labelled block, treating `if`/`either` branches as
      separate control paths (different branches assigning the same variable is fine; the
      same branch, or one branch plus what both converge to afterward, is not).
      `CorePlusCal.{Statement,Block,Branches}.checkAssignConflicts` (mutually recursive),
      run from `SurfacePlusCal.Algorithm.runDesugarer` after goto-explicitization, before
      `stripEmbeddedTypeAnnotations`. Tracks writes by *base variable* (`Ref.name`),
      regardless of indexing, from `assign` (every `||`-list entry) and `receive` (**both**
      `Ref`s — channel `c` and target `x`; `receive(x, a); receive(x, b)` errors).
      `x[0] := 3; x[1] := 4` conflicts — deciding whether two indexed writes alias needs
      index comparison, out of scope for a syntactic pass, so any two writes to one base
      variable conflict. `if`/`either` branches checked independently (from the same
      seen-set), writes unioned into what continues; `while`/`with` bodies checked
      sequentially, merged with everything around. `DesugarError.conflictingAssignment
      (pos) (name)`.
    - *The reserved label `"Done"` is never a user-written label* (§3.7). No `"Error"`
      equivalent — no procedures in this subset (§3.4/§8), no implicit `Error` label.
  - **Optional, defense-in-depth:** re-verifying the "guaranteed by the desugarer" bullet
    on `CorePlusCal` — cheap to add; revisit if `CorePlusCal` terms become producible some
    other way.
- **Variable well-scopedness.** Every variable reference resolves to a declared name of the
  right kind (global, channel, process-local, or block-local `with`/`let` — Σ/Δ/Γ/Ξ scope
  classes), every `with`/`let` binder fresh in its scope, no duplicate names within a
  scope. After type checking, the "resolves to a declared name" half is redundant with
  type checking's success (kept for documentation/defense-in-depth). The freshness /
  no-duplicate-names half is **not** implied by type checking (a shadowed name still
  type-checks) and stays load-bearing. `Core/GuardedPlusCal/Syntax/WellScopedness.lean`
  encodes it as Lean `Prop`s (Finset-based scopes, one predicate per scope class, threaded
  through `await`/`with`/`receive`/`send`/assignment). **Ported** (§2), repurposed: not the
  primary rejection mechanism (this pass is), but the formal restatement of the invariant
  at later stages. `GuardedPlusCal.Algorithm.WellScoped` is the standing hypothesis
  Guarded→Network's refinement proof (§5.5) assumes, established via the preservation lemma
  (§2, §5.5). The freshness/hygiene discipline the compiler must maintain at *every* pass:
  the ported `Statement.FreshIn`/`AtomicBranch.FreshIn`/`Process.FreshIn` predicates
  (alongside `WellScopedness.lean`) are the frontend half of the general renaming/hygiene
  mechanism (§5.6, §5.7 = backend half).
- **`CorePlusCal.WellScoped` authored fresh** (not one of the ported files). The
  preservation lemma (§2) is `CorePlusCal.WellScoped p → GuardedPlusCal.Algorithm.WellScoped
  (Computable2Guarded (Elaborator p))` — its antecedent is a `CorePlusCal`-level
  well-scopedness `Prop`, absent from prior art. This pass's executable check (bullet above)
  is the runtime half; `CorePlusCal.WellScoped` is the `Prop` half the lemma needs to
  type-check — modeled on the ported files' shape (Finset-based scope classes, same
  `with`/`let` freshness), adapted to `CorePlusCal`'s pre-`Elaborator` structure.
- **No bare temporal or action operators inside PlusCal-statement expressions.** None of
  `[]`/`<>`/`ENABLED`/`UNCHANGED` (prefix) or `'`/`^+`/`^*`/`^#` (postfix) inside any
  expression embedded directly in a PlusCal statement (`assign`, `await`, `print`,
  `assert`, guard expressions, …) — even though the surrounding TLA+ module may use them.
  **Transitive**: an operator the algorithm calls whose body contains temporal/action
  content is banned too — same no-shared-memory concern as the other checks (an operator
  called from the algorithm shouldn't leak temporal/action content, a global `VARIABLE`
  reference, or a channel value in). Same transitive scoping applies to the
  unbounded-quantifier ban (`WellFormednessError.unboundedQuantifier`, not in the thesis),
  scoped only to what's reachable *from the algorithm*. `Typed2Computable` (§5.3) treats
  both guarantees (temporal/action freedom, bounded quantifiers) as already established:
  `ComputableTLAPlus.Expression` has no temporal/action constructor, and
  `forall`/`exists`/`choose`'s domain field is a plain `Expression`, not
  `Option (Expression)`.

- **One receiving channel per process** (`WellFormednessError.receiveChannelMismatch`, not
  in the thesis). Every `receive` in a process must name that process's declared
  `@mailbox`. Index expressions count — `agt[self]` and `agt[other]` are different
  channels, compared syntactically. **Precondition of `Guarded2Network` (§5.5) being
  correct**, not a style rule: that pass gives a process one shared `inbox` sequence fed by
  one `.rx` thread per channel, so with two channels `x := Head(inbox)` can't tell which
  channel a message arrived on, and `.rx` threads are deduplicated by channel *name*,
  dropping the second of `agt[self]`/`agt[other]`. `reference/jlamp.pdf` §4.1 assumes this
  by construction (`rxₚ` drains `mailboxₚ`), so checking it here lets the refinement proof
  take it as a hypothesis. Process-scoped, not expression-scoped, so it runs as its own
  walk (`TypedPlusCal.Algorithm.checkReceiveChannels`), not a callback of the reachability
  walk (`visitStatement` has no idea which process a statement came from).
- **The `@mailbox` field is made total on receiving processes by the same walk.** Two
  asymmetric halves. `receive` in a process with no `@mailbox` = error
  (`WellFormednessError.receiveWithoutMailbox`): `Guarded2Network`'s per-instance `inbox`
  stands for the declared channel, and reading it off whichever `receive` the walk reached
  first made it statement-order-dependent. `@mailbox` on a process with no `receive` =
  **warning** (`WellFormednessWarning.unusedMailbox`, `W0007`, `-Wno-unused-mailbox`) and
  the field is dropped. Afterwards `p.mailbox = .some c` exactly when the process receives,
  `c` the channel it receives on — the refinement proof reads a process's mailbox off the
  program rather than being handed one (§D8).

  Two plumbing consequences. Dropping makes this a **rewriter**:
  `Process`/`Algorithm.checkReceiveChannels` and `Module.checkWellFormed` return their
  subject, not `Unit`, and `Driver/Pipeline.lean` compiles the module they return. It's the
  first stage past the driver that warns, so its `MonadDiagnostic` warning channel is a real
  type, and `PipelineWarning` is a real sum (`.driver`/`.wellFormedness`), not an alias for
  `DriverWarning`. Later passes still report at `MonadDiagnostic Empty ε`, gaining a
  constructor when they can warn.
- **A process set's channel must be indexed by `self`**
  (`WellFormednessError.mailboxNotIndexedBySelf`). For a `∈`-shaped process (`process (a
  \in Agents)`), the channel every `receive` names must mention `self` in its index path
  (`agt[self]`, not `coord`). An unindexed channel gives every instance of the set the same
  FIFO, so one instance drains messages its siblings were equally entitled to; the
  refinement invariant is then unstateable (the source FIFO would have to equal several
  instances' inboxes concatenated with no fixed order). `chan[self]` resolves to a distinct
  `ChanKey` per instance, making each `inbox` account for exactly its own channel. `=`-shaped
  processes are single instances, exempt.
- **Process names are unique** (`WellFormednessError.duplicateProcessName`, `E0065`).
  Checked by `TypedPlusCal.Algorithm.checkWellScoped` first, before any declaration.
  Process names are a **flat scope of their own** — a process and a variable may share a
  name — so `duplicateName`/`shadowedName` don't look at them and the error is its own.
  Position = the offending process's `id` expression (the name token carries none). Not a
  style rule: an instance is `⟨process name, self⟩`, and both languages'
  `Algorithm.algebra` resolve one by `processes.find? (·.name == name)`, the *first*
  process carrying it — two processes sharing a name give every instance of the second the
  first's code table while `Algorithm.init` contributes instances from both, a state no
  algebra steps correctly. `Algorithm.init_refines` takes it as
  `(algo.processes.map (·.name)).Nodup` (§D8).

  **Process *identifiers* stay assumed.** Whether two instances have distinct `self` values
  is about the `id` expressions' *values* under the constants, which no syntactic pass can
  decide. Distinctness of *keys* is `InitKeys.inj`, a hypothesis, made plausible by
  `mailboxNotIndexedBySelf` (the syntactic condition under which distinct instances get
  distinct keys). Nothing checks identifier distinctness itself.

### 5.3 Type checking
**Input:** `CoreTLAPlus`/`CorePlusCal`. **Output:** `TypedTLAPlus`/`TypedPlusCal`.

`ComputableTLAPlus`/`ComputablePlusCal` (`TypedTLAPlus`/`TypedPlusCal` minus constructs
with no finite runtime representation) is **not** this pass's output — a separate pass,
`Typed2Computable`: given the type-checked *and well-formed* algorithm (`WellFormedness`,
§5.2a, must have passed), collect every constant/variable/operator/function transitively
reachable from the algorithm (own-module or `EXTENDS`-ed, flattened into one output module;
a reference into a builtin/stdlib module is dropped, not translated — backends replace
every stdlib operator at code-generation time) and translate each, plus the algorithm,
into `ComputableTLAPlus`/`ComputablePlusCal`. Doesn't re-derive the temporal/action ban
(§5.2a). Adds: rejects `[A -> B]` (`fnSet`) and `[a:A,...]` (`recordSet`) outright — no
finite runtime representation. Phased separately (§7). Its output is where the ported
`Core/ComputableTLAPlus/Syntax/WellScopedness.lean` (§5.2a) applies.

Specified in thesis §3.1 — implement rules as written, one deviation (polymorphism
instantiation, below):

- **Type grammar** (Apalache "Type System 1", extended): `Bool | Int | Str | τ→τ | Set(τ) |
  Seq(τ) | ⟨τ,...⟩ | (τ,...)⇒τ | Const | a | [x:τ,...]`, plus: `Address`; `Channel(τ)` (not
  just `Seq(τ)` at the type level even though that's its encoding, so channel operations
  restrict to `send`/`receive`/`multicast` and stay out of arbitrary expressions —
  covariant: `τ <: τ' ⟹ Channel(τ) <: Channel(τ')`); metavariables `?n` (distinct from
  rigid `a`) — mutable placeholders polymorphism instantiation resolves during checking,
  never in a fully-elaborated `TypedTLAPlus` term.
- **`<:` is a genuine partial order, not just a preorder** — structural rules
  (SEQ/SET/FUNCTION/TUPLE/RECORD/OPERATOR) can't create cycles, and the three non-structural
  coercions (`Str <: Seq(Int)`, `Seq(τ) <: Int → τ`, `⟨τ,...⟩ <: Seq(τ)` for a uniform
  tuple) are one-directional between distinct constructors, so no `τ <: τ'` and `τ' <: τ`
  for distinct `τ`, `τ'`. **No `⊤`/`⊥`**, so not a full lattice — `lub`/`glb` well-defined
  by `<:` but *partial* (`lub(Bool, Int)` doesn't exist). Polymorphism instantiation needs
  exactly this partial `lub`.
- **`Str <: Seq(Int)` means code points.** A TLA⁺ string = the sequence of its Unicode code
  points, one `Int` each — `Len` counts characters, no index lands inside a character.
  TLA⁺ leaves `STRING`'s elements unspecified and `Str` is primitive here, so the axiom's
  element type is this implementation's to pin. Term-level witness `StrToSeq(e)`, an
  **intrinsic** (`Origin.intrinsic`), not a member of `Sequences`: only
  `Coercion.{apply,applyComputable}` builds the node, `builtinContext`
  (`Elaborator/Declarations.lean`) binds no name for it, no specification can write one.
  `Core/TypedTLAPlus/Builtins.lean` still tables it (that table covers every builtin an
  elaborated term can contain, not only writable ones). Compiles to `tlaplus.StrToSeq`
  (§5.7), where the code-point decision is realized — independent of `StrOrd`'s bytewise
  ordering (which only has to be total and fixed).
- **Discipline:** bidirectional (`Γ ⊢ e ⇐ τ` / synthesis `Γ ⊢ e ⇒ τ`), rank-1 polymorphism
  only (type variables into a prenex `∀`, no first-class schemes). Within an expression,
  annotations required only at binders the algorithm can't otherwise pin down (thesis
  §3.1.1). **Every top-level `operator`/`function` *definition* carries a mandatory
  `@type`** — `Elaborator/Declarations.lean`'s `[Operator/Function definition]` rules are
  checking-only against it (thesis Fig. 3.1.9), so `X == 0` is rejected without one even
  though its body would synthesize (§9.34). `RECURSIVE` out of scope (§2, §8).
- **Polymorphism instantiation — not the thesis's `Specialize` rule.** Instead (per the
  local `Checker/Typechecker/{Convertibility,Rules}.lean`): one fresh metavariable `?n` per
  bound type variable when a polymorphic operator is used, resolved incrementally as
  subtyping checks run, defaulting whatever remains at end-of-check (one defaulting point
  per declaration — rank-1 only, no let-generalization). Direction-aware, not naive eager
  unification:
  - `?n` is **unresolved** (pending upper bounds accumulated) or **resolved** to a monotype.
  - **Lower-bound `T <: ?n`**: `?n` unresolved → solve `?n := T` (coercion `id`), first
    checking `T` against any pending upper bounds (recursively). `?n` resolved to `S` →
    require `T <: S` (recursively), coercion `coerce(T <: S)`. On `T <: S` failure: error
    and require an explicit annotation (standing in for `lub(S, T)`, since a second
    incomparable lower bound is rare without let-generalization).
  - **Upper-bound `?n <: T`**: `?n` unresolved → **do not** solve it to `T`, only record `T`
    as a pending upper bound (running `glb` or the list). `?n` resolved to `S` → check `S
    <: T`, coercion `coerce(S <: T)`.
  - **Asymmetry:** a lower bound tells the *smallest* `?n` can be, safe to commit (axioms
    hand coercions narrow→wide); an upper bound tells the *largest*, committing forecloses a
    narrower solution from a later lower bound.
  - **Metavariable-vs-metavariable (`?m <: ?n`, both unresolved)**: `T` in those rules is
    always ground; no ground type here. **Do not solve `?n := ?m`** — `?m` is a live
    independently-constrained unknown, and `<:` is coercive not equality, so `?m <: ?n` only
    requires `?n` at least as wide as whatever `?m` becomes. (`?m <: ?n` alongside `?m <:
    Str` and `Seq(Int) <: ?n` is satisfiable with `?m := Str`, `?n := Seq(Int)`; merging
    would force `Seq(Int) <: Str`.) **Record `?n` as one of `?m`'s pending upper bounds** (a
    `PendingUpperBounds` entry may itself be a metavariable), leave `?n` untouched; when
    `?m` resolves from a ground lower bound, walk its pending-bounds list and re-fire the
    ordinary rules. Both still unresolved at end-of-check = type error.
  - **Defaulting** at end-of-check: only upper bounds → tightest one (or "ambiguous type");
    **no bounds at all = type error**, never a silent default.
  - **Cost**: no let-generalization ⇒ no MLsub bounds-lattice — a `Map MetaVar (Unresolved
    pendingUpperBounds | Resolved τ)` plus the cases above, "error on a second incomparable
    lower bound" for `lub`.
  - **The judgment** `subtype : Context → Type → Type → SubtypeResult` (threading the
    metavariable-solution context) yields three outcomes: **successful coercion** (concrete
    `Coercion` + updated context), **pending coercion** (check succeeded, coercion depends
    on an unknown metavariable solution — recorded as a pending upper bound), or **failure**.
  - **`Coercion` = closed structural data** (§2), discharged against an already-*elaborated*
    expression by `Coercion.apply`/`.applyComputable`.
  - **`mvar` = expression-level placeholder for a pending coercion.** On pending, the
    elaborated expression is wrapped in `mvar : MVarId → Expr → Expr` (a
    `TypedTLAPlus`/`TypedPlusCal` grammar constructor), tagged by the metavariable it awaits.
  - **Resolving placeholders — against the `pendingUpperBounds` context directly**, no
    separate site-tracking table. `mvar n e`'s wrapped `e` has true type `?n`, and
    `specializeOperator` mints a fresh metavariable per operator-call use, each the source
    of only its own `subtype` call, so `?n`'s `pendingUpperBounds` has *exactly one* entry
    in every case reachable from the checker's code. At end-of-check (end of each
    declaration, `Elaborator/Declarations.lean`): for every `mvar n e`, look up `?n`'s
    `pendingUpperBounds` — `[]` is the "never constrained" error; one entry `b` assigns
    `?n := b`, substitutes `coerce(b <: b) = id`; more than one is a loud named gap
    (`.todo`), not a silent guess. Every `mvar` node is eliminated before checking finishes,
    so `Computable2Guarded` and both backends see `mvar`-free.
- **Statement judgment** `Γ | Ξ ⊩ S ok` (no output type — checked for effects, not typed).
  Asymmetric rules, thesis §3.1.5: `[Assign]` synthesizes LHS type, *checks* RHS against it
  (enables upcasting RHS via subtyping); `[Send]` same (synthesizes channel type to upcast
  the payload); `[Print]` requires a `showable` type (Fig. 3.1.14: everything except
  function/operator/channel types, recursively); `[Goto]` does no type check — label
  existence is well-formedness's job (§5.2a).
- **A channel's declared element type must be `sendable`.** Same shape as `showable`
  (`Operator`/`Channel`/`Const`/rigid type variables, and anything containing one, excluded;
  recurses through `Function`/`Set`/`Seq`/`Tuple`/`Record`) but a separate predicate
  (`Elaborator/PlusCal.lean` `sendable`) — the restrictions coincide today but are distinct;
  `sendable` excludes `Const` because a `CONSTANT` is substituted *after* code generation
  and an unsendable instantiation would silently break the invariant. Checked once in
  `checkChannelDecl` at channel-declaration time, covering `send`/`receive`/`multicast`.
  `TCError.notSendable`. Both `showable` and `sendable` are pure `Typ → Bool` — callers
  resolve pending metavariables first (`resolveTypeMVarsForDisplay`) so `.mvar` means
  "genuinely unresolved". Consequence: `Channel(Channel(τ))` is a hard error, so with
  `Channel`'s reflexivity-only subtyping, well-formedness's `channelInExpression` check can
  no longer be exercised via `receive`'s destination `r` (§9.13).
- **`[Receive]` — channel/reference coercion.** `Channel` is covariant
  (`Elaborator/Subtyping.lean`), but a channel-typed expression's own `Channel(τ) <:
  Channel(τ')` check only ever produces `Coercion.id` — channels never change runtime
  representation between checker and backends, and `TypedTLAPlus.Expression` has no term
  former to wrap an opaque channel value. What needs a real coercion is the **received
  value** — the message's element type `τ` may be narrower than the destination reference's
  `τ'`, with no elaborated sub-expression to hand it to. Synthesize both, `subtype` them
  directly (independent of the `Channel` structural check, identity-only), store the
  `Coercion` on the `TypedPlusCal`/`GuardedPlusCal` `receive` node — carried through
  `Computable2Guarded` (§5.4) unchanged, applied only by `Guarded2Network` (§5.5).
- **`Ξ` is a global cache, not threaded state — in-memory only (§2).** On paper an input to
  the judgment like `Γ`; in practice a `MonadModuleCache m` effect (`lookup`/`store` keyed
  by source hash), so a module isn't re-type-checked every time it's referenced via
  `EXTENDS` within one run.
- **Module resolution + TLA+ standard modules (`EXTENDS Sequences, TLC, ...`).** `-I <path>`
  (§9.3) adds a search path for `.tla` modules referenced via `EXTENDS`. `locate` searches
  the extending module's own directory first, then `-I` entries in order, **dedups by
  canonical path** (`IO.FS.realPath` on each hit, first spelling kept). Two search entries
  naming one file = a duplicate, not an ambiguity (`-I foo` alongside `foo/Main.tla`,
  relative-vs-absolute spelling, `.`/`..` detour, symlinked directory all resolve).
  `ambiguousModule` stays for genuinely distinct files, listing each candidate *as
  spelled*. (`INSTANCE` out of scope — the mechanism only handles `EXTENDS`.) **Resolution
  eager and transitive** (§2) — the whole transitive closure resolves before the main
  module's type checker begins, so every `Ξ` lookup is already populated.

  TLA+'s standard modules (`Sequences`, `TLC`, `Naturals`, `FiniteSets`, …) are **not**
  parsed from the real library — the compiler bundles stubs, enough to type `Len`/`Head`/
  `Append` correctly, not real definitions. `builtinContext` (`Elaborator/Declarations.lean`)
  carries only the ~14 `EXTENDS`-independent intrinsics (`=`, `/=`, `/\`, `\/`, `=>`, `<=>`,
  `\neg`, `\in`, `\notin`, `\subseteq`, `\cup`, `\cap`, `\`, `DOMAIN`, plus temporal ones,
  §9.11). Everything else — `+`/`-`/`*`/`\div`/`%`/`^`/`..`/comparisons/`Nat` (`Naturals`),
  `Int`/`-.` (`Integers`), `Len`/`Head`/`Tail`/`Append` (`Sequences`), populated
  `Bags`/`FiniteSets` — is real declarations in `Driver/Modules.lean`'s
  `builtinModules["Naturals"]` etc. (`naturalsDeclarations`/`sequencesDeclarations`/…),
  seen only via an actual `EXTENDS Naturals`/`EXTENDS Sequences`, through the same
  `Γ₀`-merge machinery `compileModule` uses for ordinary dependencies.

  **`EXTENDS` is transitive, identically for a builtin and a `.tla` file** — `INSTANCE`
  being out of scope leaves `EXTENDS` the only import, so a module with no way to depend on
  another without re-exporting it would have no way to depend at all. `Bar EXTENDS Foo` with
  `Foo EXTENDS Naturals` sees `Naturals`'s `<`; `Sequences` (`«extends» := ["Naturals"]`)
  gives it to whoever extends `Sequences`. Re-exported = the *bindings* a dependency brings
  into scope, **never merged declarations**: `resolveModule`/`compileModule` return a
  `ResolvedDep` storing the module + `inherited` (its own `EXTENDS`'s already-`Origin`-tagged
  bindings), and `ResolvedDep.bindings` derives the export list as
  `inherited ++ mod.ownBindings` — derived, not stored, so the two resolution paths can't
  diverge. Callers concatenate rather than re-derive from a `List Decl` (which can't say who
  declared what): re-deriving would tag `Naturals`'s `<` with whichever module it arrived
  through, and `Origin` is the dispatch key for `TypedTLAPlus.builtinOpOf?` /
  `Network2Go.compileBuiltinCall` — a re-exporting module's name matches no arm, so a
  misattributed builtin type-checks then fails codegen. Merge order: inherited first, own
  last (own shadows inherited of the same name); between sibling `EXTENDS` entries the later
  wins, and since every path to a re-exported operator yields the same `Origin`,
  `EXTENDS Naturals, Sequences` and `EXTENDS Sequences, Naturals` agree. Every module's
  returned `TypedModule` holds exactly its own declarations, so it agrees with what
  `MonadForeignLookup.lookupForeign` answers (read by `WellFormedness/Reachability.lean`).
  On the cached-replay path, `inherited` is rebuilt from the dependency resolutions the
  cache check already performs — a `flatMap`, not another compile.

  Each `«extends»` list mirrors its real module's full top-of-file dependency list,
  `LOCAL INSTANCE` included. A `LOCAL`-declared helper (`Bags`'s `Sum`) stays out of the
  exported declaration list. `RealTime`/`Reals` excluded (out of scope); `TLC` an empty
  stub. One entry, **`Fugue`, has no real counterpart** — this compiler's own module,
  `«extends» := ["Naturals"]` (a downcast's `1..n` domain is otherwise unwritable, so
  `EXTENDS Fugue` alone suffices), holding:
  - `\prec`/`\preceq`/`\succ`/`\succeq : Address × Address → Bool`. Exists because the ends
    of the pipeline disagree about `Address`: the type checker treats it as atomic with
    equality only, generated Go requires an order (`runtime/comm/address.go`'s `Address`
    interface carries `Lt`; sorted address sets, address-keyed functions, `CHOOSE` over
    addresses depend on it). `Network2Go` compiles the four to `comm.AddressOrd`'s
    `Lt`/`Le`/`Gt`/`Ge`. No TLA⁺-side definition — the order is deliberately unspecified.
  - **Representation downcasts** — Apalache operators whose direction `<:` can't give (its
    axioms are all narrow→wide). `FunAsSeq : (Int -> a) => Seq(a)` reads a function back as
    a sequence, `SetAsFun : Set(<<a,b>>) => (a -> b)` a set of pairs back as a function,
    `MkSeq : (Int, (Int -> a)) => Seq(a)` the total constructor `[i ∈ 1..N ↦ F(i)]`.
    `FunAsSeq`/`SetAsFun` are **partial** (`FunAsSeq` needs `DOMAIN f = 1..n`, `SetAsFun` a
    functional pair set) — compiled forms abort on precondition failure, like `Head(<<>>)` —
    and raise `W0008` (`-Wunsafe`) at the reference (`Elaborator/Expressions.lean`
    `inferExpr` `.var` case); `MkSeq` is total, raises nothing. `FunAsSeq`'s `EvalBuiltin`
    rule is `funAsSeq (hf : IsSeqVal f) : EvalBuiltin .funAsSeq [f] f` (identity on a value
    already a sequence); `MkSeq`/`SetAsFun` get no rule (like the `Bags` family).
    `Network2Go` compiles `FunAsSeq`/`SetAsFun` to `tlaplus.FunAsSeq`/`SetAsFun` (the latter
    handed both tuple projections as callbacks); `MkSeq` is `E0061` at `go` until operator
    arguments exist (§9.10). Not a cast: `StrToSeq` stays coercion-only, `"abc"[2]`
    synthesis-position failures stay a known limitation (needs `LET`/`IN`, §9.2).

  Each declaration only needs a name/type binding (`Decl.bindings`) — bodies never
  re-examined (standard-library operators replaced by backend-native implementations at
  codegen). Every builtin body is self-referential (`Op(x) == Op(x)`, `Op == Op` at arity
  0), `Fugue` included; the reachability walk records `(module, name)` and its memo stops
  the one-step self-recursion (§9.33). A top-level `operator`/`function` definition (any
  arity, `builtinContext` entries included) is always a **let-generalized scheme**
  (`Elaborator/Monad.lean` `Binding` carries `Typ` + `isScheme : Bool`), freshened on every
  `Γ`-reference (`Elaborator/TypeUtils.lean` `specializeType`), not just on call.
  `CONSTANT`/`VARIABLE` and every ordinary binder (operator/function parameters,
  quantifiers, `CHOOSE`, `EXCEPT`, PlusCal variables/channels) stay monomorphic —
  `extend`/`extendAll` insert monomorphically by construction.
- **An `EXTENDS`-ed module's own PlusCal algorithm is dropped and warned about** (`W0006`,
  `-Wextends-algorithm`). `EXTENDS` re-exports bindings; an algorithm is not a binding.
  `compileModule` warns right after `mod.extends.mapM resolveModule`, per direct dependency
  with `pcalAlgorithm.isSome`. Reported against the **extending** module: span = the
  dependency's identifier in its own `EXTENDS` clause (`posOf` on the name), so the caret
  lands where the user would make a change. Direct dependencies only. Not re-raised for a
  module replayed from `Ξ`.
- **Process/algorithm judgments** thread `self : Address` into scope, require process-ID
  sets to be `Set(Address)`, require all channel declarations to be functions of addresses
  to `Channel(τ)`.
- **`CONSTANT`s stay abstract through the whole pipeline (§2).** Type-checked (given a
  type, per annotation or inference) like any other name in `Γ`, never given a value by
  this compiler.

### 5.4 Distributed PlusCal → Guarded PlusCal (`Computable2Guarded`)
**Input:** `ComputablePlusCal.Algorithm` (§5.3's `Typed2Computable` output). **Output:**
`GuardedPlusCal` (a restriction where every `await`/`receive`/`with` sits at the very
start of its atomic block).

Thesis §3.2.3: `𝒞_reord ∘ 𝒞_flat ∘ 𝒞_par ∘ 𝒞_cflow` (`𝒞_par`/`𝒞_cflow` order-independent;
the other two order-dependent). Four small independently-testable passes:

1. **`𝒞_cflow`** — rewrite `if`/conditional-`while` into `either`/`await`:
   `while e {B1}; B2; goto l'` (at label `l`) → `l: if e then {B1; goto l} else {B2; goto
   l'}`; `if e then B1 else B2` → `either {await e; B1} or {await ¬e; B2}`. Justified by the
   PlusCal→TLA+ action semantics (`if` ≡ action `(e ∧ 𝓔(B1)) ∨ (¬e ∧ 𝓔(B2))`).
2. **`𝒞_par`** — sequentialize parallel assignments (`r1≔e1 ∥ ... ∥ rn≔en`). Handles
   aliasing (`x[0]≔3 ∥ x[x[0]]≔7`): all RHSs into fresh temporaries, then all LHS *indices*
   into fresh temporaries, then assignments left-to-right using the partially-evaluated
   references. Thesis gives the full recursive definition over reference shapes (`x`,
   `r[e]`, `r.x`).
3. **`𝒞_flat`** — flatten nested `either`s into flat branch lists, distributing sequencing
   over choice (`B; either{B1} or ... or {Bn}; B'` → `either{B;B1;B'} or ...`) + `either`
   associativity. Trades code size for fewer runtime choice points / less rollback
   machinery downstream.
4. **`𝒞_reord`** — float every `await` **and every `receive`** to the front of its branch,
   commuting leftward past `skip`/`print`/`assert`/`send`/`multicast` (guard-independent)
   and past assignments via substitution. Thesis §3.2.3.4, one mirrored equation per
   statement kind, `await`/`receive` symmetric:
   - `assert`/`print`/`skip` commute with both trivially (read-only):
     `𝒞_reord(skip; await e') = await e'; skip`, `𝒞_reord(skip; receive(c,r)) =
     receive(c,r); skip`, same for `print e`/`assert e`.
   - `send`/`multicast` commute with both: channels can't appear in ordinary expressions
     (an `await` guard can't depend on one), and `receive`'s channel `c'` is distinct from
     the `send`/`multicast` channel `c`/`x` by "no two operations on one channel per atomic
     block" (§5.2, `Statement.checkRefRestrictions`), so
     `𝒞_reord(send(c,e); receive(c',r)) = receive(c',r); send(c,e)` is sound.
   - Past an assignment: substitution via `e'[e\r]` (substitute reference `r` by `e` in
     `e'`, `EXCEPT` when `r` has an index) — thesis Two-Phase Commit `c2` (Listings
     3.2.1–3.2.4). `𝒞_reord(r≔e; await e') = await e'[e\r]; r≔e` (plain expression `e'`);
     `𝒞_reord(r≔e; receive(c,r')) = receive(c[e\r], r'[e\r]); r≔e` reuses the same helper
     on `c`/`r'` (both *references*), overloaded to substitute only within the target's
     index positions, never its base variable name. Sound because `r`, `r'` are always
     different base variables (no-repeated-write restriction), so substitution can't turn
     `r'` into `r`.

   Floating `receive` removes most but not all need to undo partial state on a failed
   branch — a receive guard's truth depends on runtime message arrival, resolved fully only
   once `receive` becomes a concrete buffered read in `Guarded2Network` (§5.5).

Worked example: thesis Listings 3.2.1–3.2.4 (Two-Phase Commit `c2`) — hand-verify each
subpass against it.

### 5.5 Guarded PlusCal → Network PlusCal (`Guarded2Network`)
**Input:** `GuardedPlusCal`. **Output:** `NetworkPlusCal` (no `receive` guards; each
process gets an opaque `T_rx(mailbox → inbox)` thread buffering incoming messages into a
process-local `inbox` sequence variable, turning `receive(c, r)` into ordinary
`await Len(inbox) > 0`-guarded reads).

**Also where `[Receive]`'s stored channel/reference coercion (§5.3, §2) is discharged** —
first pass where a `receive(c, r)` becomes a concrete buffered read (`await Len(inbox) > 0`)
with generated code around it. Discharged via `Coercion.applyComputable` (§2) against the
freshly-built `Head(inbox)`/`Tail(inbox)` `ComputableTLAPlus.Expression` — `Coercion` is
closed structural data so this needs no lift back into `TypedTLAPlus.Expression`.

Ported from `fugue main` with its refinement proof
(`PlusCalCompiler/Passes/GuardedToNetwork/{PlusCal,Lemmas}.lean`, against
`{Guarded,Network}PlusCal/Semantics/Denotational.lean`). The ported
`Core/GuardedPlusCal/Syntax/WellScopedness.lean` (§5.2a) supplies the well-scopedness
hypothesis, established via the preservation lemma (§2). Thesis ch. 5 is a stub — **the
code is the spec, not the PDF.** Adapt rather than copy: the source AST
(`TypedPlusCal`/`GuardedPlusCal`) is fresh, so denotational semantics and lemmas re-derive
against the new `Core/GuardedPlusCal/Syntax.lean`, though the proof's mathematical content
transfers. `multicast`'s denotational semantics is still open — no enumeration primitive to
fold a `send` over a set value's members, no prior-art shape — §9.27.

### 5.6 Network PlusCal → the Join Calculus (`Network2JoinCalculus`) — NEW
**Input:** `NetworkPlusCal`. **Output:** `Core/JoinCalculus`, pretty-printed to a `.join`
source file. Thesis ch. 8; no existing code — new implementation top to bottom.

**Target language** (thesis §8.4, Fig. 8.4.1) — extended Join Calculus with guards and a
name server:

```
P ::= x⟨e1,...,en⟩         message                D ::= J if e ⊳ P    guarded local rule
    | P | P                 composition               | D or D          co-definition
    | def D in P             definition             J ::= x⟨x1,...,xn⟩  message pattern
    | 0                     inert process               | J | J          join pattern
    | register a as e; P    name registration
    | let a := lookup e; P  name lookup
```
Operational semantics: RCHAM (Reflexive CHemical Abstract Machine) — heating/cooling
structural rules (`Str-Null`, `Str-Par`, `Str-And`, `Str-Def`) + reaction (`Loc-React`)
for local solutions, `Register`/`Lookup`/`Str-Comm` for distributed global solutions
(named locations `α`, name server `Γ` mapping registered tokens to locations). Thesis Fig.
8.4.2–8.4.3. Not needed for the initial implementation — getting `Network2JoinCalculus` to
compile is the near-term goal; formalizing `Core/JoinCalculus/Semantics/` is low priority,
§9.4.

**Compilation scheme** `𝒞 : NetworkPlusCal.Process → JoinCalculus.Process`:

- **State as atoms.** Each mutable process-local variable `x` becomes a single-token
  reference-cell atom `x⟨v⟩` in the process's local solution. Every reaction reading `x`
  consumes `x⟨v⟩` in its pattern and re-emits `x⟨v'⟩` in its body — block atomicity is free:
  exactly one `x⟨v⟩` token per variable, consumed by one firing reaction at a time.
- **Process skeleton.** `P = self ⋆ x1=e1,...,xn=en ⋆ {T1}...{Tm}` compiles to
  `def p⟨self⟩ ⊳ def recv⟨v⟩|inbox⟨vs⟩ ⊳ inbox⟨vs∷v⟩ in register recv as "{self}";
  x1⟨e1⟩|...|xn⟨en⟩|l_i⟨⟩|...|l_j⟨⟩`, `l_i,...,l_j` each thread's first label. This is the
  process's `T_rx` thread made concrete (`recv` = the mailbox-buffering reaction). Running
  the process = emitting `p⟨α⟩` for some concrete location `α`. A process set `p ∈ S`
  compiles to this **one** definition, not `|S|`-many — parameterized over `self`, up to
  whoever runs the `.join` file to `def p⟨α⟩` once per concrete process (`S`'s membership
  never evaluated, may depend on an unresolved `CONSTANT`).
- **Atomic blocks.** `l: {G1;S1;goto l1} or ... or {Gn;Sn;goto ln}` — each branch compiles
  to `def l⟨⟩ | x_a⟨x_a⟩ | ... | x_g⟨x_g⟩ if ⟨conjunction of Gi's awaits⟩ ⊳ ⟨updated state
  atoms⟩ | ⟨out⟨v⟩ per print⟩ | ⟨let send:=lookup α; send⟨e⟩ per send(c[α],e)⟩ | l_i⟨⟩`.
  The block's own label atom `l⟨⟩` is consumed and *not* re-emitted except by an explicit
  `goto l` — restricts the `either` to firing at most one branch at a time.

Ping-Pong worked through in thesis §8.6 (`rcvPi`/`sndPo` reactions + full process
definition) — first target, by hand before automating.

`isFair` carried through unused: `𝒞` makes reaction-firing nondeterminism no more
fairness-aware (§2).

**Identifier hygiene.** `recv`, `inbox`, per-block label atoms (`l⟨⟩`) are `𝒞`-introduced,
not source names — same collision-avoidance as Go keyword-escaping (§5.7 `sanitize`/
`keywords`), generalized to the guarded-reaction dialect's reserved surface.

`𝒞` is not proven correct, and the emitted dialect (guards on reactions) isn't accepted by
existing Join Calculus implementations (JoCaml has no `if e ⊳`) — the thesis sketches
`def J if e ⊳ P` as `def J ⊳ if e then P else J` but flags it as a performance-losing
workaround. Emitting a well-formed `.join` file faithful to the scheme is the deliverable;
what happens after is §9.1.

### 5.7 Network PlusCal → Go (`Network2Go`) — including lock inference
**Input:** `NetworkPlusCal`. **Output:** `Core/Go`, pretty-printed to `.go`, depending on a
runtime library this project also owns (below).

**Target AST: the thesis's.** `Core/Go/Syntax.lean` implements thesis §6.6 (Defs. 6.6.1,
6.6.11–6.6.20) — real Go types (`int`/`str`/`bool`, `chan τ`, `[]τ`, `[n]τ`, `map[τ₁]τ₂`,
`struct`, `func`), Go expressions, Go references (`_`, `x`, `r[e]`, `r.x`). Prior art's
`GoCal` (no Go type/expression AST, statement layer parameterized over TLA⁺
`TypedSetTheory.Typ`/`Expression`) is reference-only. Differences: (a) blocks are `List
Statement`, not §6.6's `; S` continuations, so `var x τ` and channel `make` are
position-scoped statements; (b) adds composite literals (struct/slice/map, `make`) and
`Typ.named`/`Typ.var` beyond §6.6 for `Lock[τ]`, `Receiver[T]`, `Set[T]`,
`LazyFunction[T,U]`, `Address`, `Network`; (c) generic repo-standard (`(Typ Expr : Type)`
parameters, `Bifunctor`/`Bitraversable`, pinned abbrevs, namespaces `Go`/`ComputableGo`);
(d) compiling TLA⁺ types/expressions *into* those Go ones (§7.2.1/§7.2.2, below) is real
work this pass owns.

`Network2Go/PlusCal.lean` compiles Network PlusCal processes/threads into concurrent Go
(goroutines over channels, `go`, buffered/unbuffered `chan`, `send`/`receive`/`select`) —
**except** synchronizing atomic blocks that touch shared process-local state across
goroutines. Lock inference is the missing piece to port around, not a reason to redesign.
Also reusable: runtime scaffolding in `distpcal-compiler/tests/*/{lib,nameserver}` (TCP/UDP
address resolution + name server — the Go analogue of §5.6's `register`/`lookup`).

**The wire mechanism — settled.** Goroutines over Go's `chan` handle plumbing *within* one
compiled process; `send(c, e)` to a different (possibly remote) process leaves the process.
The compiler's answer is to not answer: `send(c[e₁], e₂)` → `net.c[e₁].Send(e₂)`, and each
compiled process takes `mailbox comm.Receiver[τ]` as a parameter — both interfaces (see
`Channel(τ)` under "Go representations"). Generated code never opens a connection,
serializes anything, picks a capacity, or names a nameserver; connection lifecycle,
serialization format, and how a channel's identity travels with its payload are the
endpoint implementation's business. Thesis's own division (§7.2.3.1 pins the `.Send` call
site, §7.2.3.2 makes `mailbox` caller-supplied; neither specifies internals). Implemented:
`Network2Go/PlusCal.lean` emits exactly this, `runtime/comm/` ships the two interfaces and
nothing behind them.

**Deferred scope: a *reference* transport.** A TCP-or-Unix-socket `Sender`/`Receiver` with
a concrete serialization format and address discovery (natural starting point:
`distpcal-compiler/tests/*/{lib,nameserver}`) is wanted eventually, not built now. Nothing
blocks on it: a specification is runnable today against hand-written endpoints (the
Ping-Pong end-to-end check, §7.3, generated `Proc_Ping`/`Proc_Pong` over Go channels, `go
test -race` clean). Writing one is a scope decision, not an open compilation question — the
only thing it reopens is §9.6's capacity hypothesis for a socket-backed endpoint.

**Lock inference** — thesis §7.1.2's [HFP06]-derived scheme. Locks **per process-local
variable**; a block may acquire *several* (one per variable in its footprint, after
merging):

1. For every **branch** (all branches of the process, not just cross-thread pairs),
   `shared` = process-local variables read or written in it (free variables in expression
   position + all indexed-assignment targets − `with`-bound temporaries).

   **Per branch, where Definition 7.1.2 says per block** — the branch is the unit that
   executes atomically (§7.2.3.1 acquires locks per branch, Remark 7.2.4). A block's
   footprint = union over its branches, so two branches touching disjoint variables are
   reported as joint users of both, those variables dominate each other and merge into one
   lock. Costs concurrency, not correctness (every assignment gives each variable exactly
   one lock).

   A `Thread.rx` contributes a footprint over its `inbox` (it is the second thread writing
   `inbox`), even with no label/branches/statements. Omitting it is a concurrency loss: in
   Ping-Pong's `Ping` every footprint with `inbox` would also have `tmp1`, so `tmp1 ≻
   inbox`, they share a lock, and the receiving thread blocks a `send` touching only
   `tmp1`. It also makes §7.3's `inbox_Pong ≻ tmp2` strict rather than mutual. `self` needs
   no special case — bound by `checkProcess`, not declared, and only declared variables
   count.
2. Domination: `x ⪰ y` iff every footprint containing `y` also contains `x`; `x ≻ y` when
   additionally `x ≠ y`.
3. Lock selection (Definition 7.1.3): one fresh lock `ℓ_x` per variable `x`; for each `x`,
   if some `y ≻ x` exists, redirect *every* variable currently assigned `ℓ_x` to `y`'s lock
   (redirecting every holder, not `x` alone, makes mutual domination settle instead of
   oscillate). Only reduces the distinct-lock count.
4. Total order `<` over the resulting locks (a block may hold several at once; fixed
   acquisition order avoids lock-ordering deadlocks). At each block `B`'s start, acquire
   `shared(B)`'s locks in that order; release (order-free) at the end. The thesis leaves
   the order and the choice among dominators free; both fixed to the process's variable
   declaration order (a compiler grouping locks differently between runs couldn't be
   tested).
5. Pruning pass — a lock used only within one thread could be dropped (blocks in one thread
   are already mutually exclusive). **Not done**: here a lock is also the variable's
   *storage* (§7.2.3.1's branch functions read variables out of the struct the lock
   carries; `INIT_LOCKS` is the only writer of initial values), so a dropped lock leaves
   its variables nowhere to live. Pruning needs thread-confined variables as goroutine-local
   state, which the compilation shape rules out (each atomic block is its own top-level
   function and can't mutate a local of the thread function that started the chain).

Different from a one-lock-per-block scheme: several ordered locks per block, grouped by
variable-level domination not block-level connectivity. Implement against Definition 7.1.3
and Examples 7.1.1/7.1.4/7.1.5.

`isFair` carried through unused: lock inference and Go's goroutine scheduler make no
attempt at fairness (§2).

**Identifier hygiene.** Lock names are `Network2Go`-introduced, no table needed:
`freshName "lock"`, so `goIdent`'s escaping lands them in the odd-underscore-run half of
the parity split, unreachable from any user name (same mechanism as every synthesized name
in this pass). The *user's* names against Go's vocabulary need a table — `binderName`
against `keywords` and `predeclared`.

**Go representations of TLA+ types**, thesis §7.2.1.1:
- `Bool`/`Str` → `bool`/`string`, as local newtypes (one name to emit, a type the runtime
  owns to hang `BoolOrd`/`StrOrd` off). `Str` carries `StrToSeq`, the `Str <: Seq(Int)`
  coercion's runtime half: `[]rune` widened into a 1-indexed `Seq[Int]`, one element per
  Unicode code point.
- `Int` → **`math/big` by default**, machine `int` opt-in. Inverts the thesis (which
  defaults to machine `int` for speed): TLA⁺ integers and the verified-against semantics'
  integers are unbounded, so machine `int` silently wraps where the semantics forbids it,
  making every correctness argument carry an overflow side condition. **Go build tag, not a
  Fugue flag**: `go build -tags fugue_machint`. No `-Xgo-bigint`; emitted code is
  representation-agnostic (arithmetic through `Add`/`Sub`/`Neg`/`Mul`, comparisons through
  `IntOrd`, literals through `MkInt`), only `runtime/tlaplus/int_{big,machine}.go` differ. A
  literal too large for machine `int` is a Go compile error under the machine build.
  `go.mod` can't carry a default build tag, so the untagged (safe) build is the default.
  `Int` is a struct wrapping `*big.Int` (Go forbids methods on a defined pointer type, so
  `type Int *big.Int` couldn't carry `String`); its zero value's nil pointer reads as 0 in
  every operation, since `Go.Statement.var` emits zero-initialized `var x Int`. `ToInt`
  converts back where Go demands a machine integer (slice indices), panicking above that
  range (only callers are indexing operations; a sequence needing such an index can't be
  held in memory anyway).
- Functions `τ → τ'` → lazy maps (wrapping `map[τ]τ'`, not eagerly computing the whole
  graph — like TLC).
- `Set(τ)`/`Seq(τ)` → both `[]τ`; sets additionally carry a no-duplicates invariant (`τ`
  comparable) not at the Go type level. Sequences keep TLA+ 1-indexing by leaving slot 0 of
  the slice unused — a sequence of `n` elements has underlying length `n+1`, and the nil
  slice is a second spelling of the empty sequence so `var s Seq[τ]` needs no initializer.
  `Tail` is a reslice (old first element becomes the new unused slot), which makes `Append`
  copy unconditionally (Tail-produced sequences share a backing array).
- Records/tuples → **anonymous** `struct`; tuples use `proj1`..`projN` field names. Nothing
  named or declared: `Ord` is a struct not an interface, so `ordDict` builds a dictionary
  for an anonymous struct type directly and emits the literal beside the type — removing
  name mangling, per-specification type declarations, and any tuple arity cap. `compileTyp`
  sorting record fields by name is load-bearing: Go identifies anonymous struct types
  *structurally*, so sorting makes two identically-shaped records one Go type and fixes the
  lexicographic order the dictionary compares in. Cost (emitted code only): the struct type
  is spelled at every occurrence and three times per dictionary literal; `ordDict` being a
  pure fold re-emits a record's dictionary per site. Hoisting dictionaries into
  package-level variables would fix both and reintroduce the naming question — waits for
  evidence it matters.
- Operators `(τ1,...,τn) ⇒ τ` → plain Go `func`.
- Type variables → propagated to the nearest enclosing function definition (Go generics).
- Uninterpreted constant types → left as-is (same name), user-supplied (`CONSTANT` scope
  boundary).
- `Address` → an unspecified interface declaring `Eq`/`Lt`, bridged into a dictionary by
  `comm.AddressOrd` (method expressions, receiver-first). Requires an order, not just
  equality: addresses reach sets and function domains in the first real example, and a
  record with an address field would otherwise lose its order. The order is
  integrator-supplied, making `CHOOSE` over a set of addresses implementation-dependent
  (legal — `CHOOSE` is deterministic-but-unspecified — but documented on `Address`). Same
  for any uninterpreted constant type.
- `Channel(τ)` → no general Go value representation: a channel is never stored, passed, or
  put in a data structure, only appears indexed (`c[α]`) at a `send`/`receive` site.
  Generated code holds *endpoints*: `comm.Sender[τ]` (`Send(τ)`, may block, no error result)
  and `comm.Receiver[τ]` (`Recv() (τ, bool)`, blocks while the medium is alive, returns the
  zero value + `false` once it vanishes — lets a receive loop terminate). Interfaces, not
  concrete types: the compiler emits no `main` and takes no position on the medium (Go
  channel, Unix socket, TCP connection all satisfy them). Answers both "what Go type
  represents a channel value" (none) and "what does `send(c, e)` to a different process
  compile to" (an interface call — see "The wire mechanism" above).

**Compiling TLA+ expressions, operators, functions** (thesis §7.2.1.2/§7.2.2; §7.4's
correctness sketch is the chapter's only remaining stub):

- **Equality/ordering: one dictionary, passed explicitly.** Go's `==`/`comparable` can't be
  implemented for custom types and falls short for complex TLA+ types (order-irrelevant set
  equality, sets-of-sets, lazy maps). The thesis uses `Eq[T]`/`Ord[T]` *interfaces*; this
  compiler uses a single `Ord[T]` **struct** of two functions (`Eq`, `Lt`), with
  `Neq`/`Gt`/`Le`/`Ge`/`Cmp` derived as methods, handed to every operation that compares.
  Interfaces can't express the library's own containers: Go has no conditional method sets
  (no `instance Ord a => Ord (Set a)`) and a method's receiver type parameters must repeat
  the declaration's constraints, so `type Set[T any]` can declare no comparison calling
  `T`'s, while `type Set[T Ord[T]]` propagates the constraint and makes a tuple/record with
  a function-typed component *non-representable* — `Set[Set[Int]]` isn't constructible at
  all. Dictionaries keep every container `[T any]`, nesting is composition
  (`SetOrd(SetOrd(IntOrd))`) produced by `ordDict : Typ → …`, structural recursion mirroring
  `compileTyp`. `Gt` becomes derivable (a flip). Only `Eq`/`Lt` primitive, no separate `Eq`
  hierarchy: wherever equality is available an order is too (a lazy function forces its
  domain either way), and types with neither (operators → Go `func`) aren't TLA+ values and
  can't nest inside a set/sequence/record/function domain. **Methods where they work,
  dictionaries where they don't**: hand-written types declare `Eq`/`Lt` as methods and are
  bridged once (`comm.Address` → `AddressOrd`; a user's constant type → compiler emits the
  bridge). Only a rigid type variable needs a dictionary *parameter*, threaded into
  polymorphic definitions at call sites. Dictionaries are passed, never stored in the values
  they order: `Set[T]` stays `[]T`. `persistent/treemap` (`New(cmp func(a, b K) int)`) is
  the precedent.
- **Booleans.** `/\`/`\/` → Go's short-circuiting `&&`/`||` (non-action, non-temporal TLA+
  expressions are pure). `\A x \in S : P`/`\E x \in S : P` → a search over `S` for the first
  counterexample/witness (De Morgan).
- **Sets.** `Set(τ)` is `[]τ` under **two** invariants: sorted ascending by the element
  dictionary's ordering, and duplicate-free. Sortedness is a canonical-representative choice
  making operations cheap — equality is an elementwise walk not a double subset test,
  membership a binary search not a scan, `CHOOSE`'s deterministic pick the first satisfying
  element, dedup falls out of the sort. Cost: an ordering is needed wherever equality alone
  would do (`SetIn`, hence `FnApply`/`FnOverload`) — free, since `Ord` carries both. Which
  dictionary a `Set` was built with isn't recorded; every operation must be handed the same
  one, guaranteed by deriving both from the same `Typ`. `{x \in S : P}`/`{e : x \in S}` →
  `SetFilter`/`SetMap`, copying the slice (TLA+ data immutable). `SetFilter` copies
  unconditionally inside the helper (`slices.DeleteFunc` compacts in place, corrupting a set
  sharing a backing array) and preserves both invariants. `SetMap` preserves neither (a
  mapping function need be neither monotone nor injective), so it takes the *result* type's
  dictionary and renormalizes. Set literals `{e₁, …, eₙ}` → `MkSet(ord, e₁, …, eₙ)`, not a
  bare composite literal (component equality isn't decidable until evaluated, so the literal
  may be unordered/repeat). **Representation swappable**: nothing outside
  `runtime/tlaplus/sets.go` and literal emission depends on `Set` being a slice, so a
  persistent tree-set later changes no generated code. Not planned — access is build-once/
  iterate/compare, favouring contiguous; the one place copy-on-write mattered (function
  `EXCEPT`) is served by `persistent/treemap`. `CHOOSE x \in S : P` (deterministic) returns
  the minimum satisfying element = the first a scan meets on the sorted representation:
  neither builds the filtered set nor searches for a minimum, needs no dictionary at the
  call site, panics on empty. Over an uninterpreted constant type the result is
  implementation-dependent (integrator's order — see `Address`).
- **Functions.** Lazy maps; since Go's `map[T]U` requires `T` `comparable` (which
  dictionary-ordered types aren't), storage is an ordered-map keyed by the domain
  dictionary's `Cmp`: **home-grown persistent `TreeMap[K, V]` in `persistent/treemap/`**
  (weight-balanced, `Compare func(a, b K) int`-parameterized, O(1) `Clone`/O(log n)
  `Insert`/`Delete`/`Get`, no `comparable` constraint). Payoff: `EXCEPT` always clones
  before writing, so `[f EXCEPT ![3] = 7][3] = 7 /\ f[3] # 7` holds, and the clone is O(1)
  via structural sharing not an O(n) copy. `LazyFunction` holds that map **by pointer**
  (it's passed by value, and the cache does two jobs a persistent map splits): application
  memoizes by overwriting the map *header* through the shared pointer (visible to every copy
  of that `LazyFunction`); `EXCEPT` keeps the fresh header `Insert` returns (override scoped
  to the overloaded copy). By value silently loses memoization and makes recursive functions
  exponential. A function's *own* dictionary (`FnOrd`, for a function nested inside a set or
  domain) is a panicking placeholder — the real scheme (TLC forces the graph, compares
  domain then range pointwise) is left for the first specification that needs it.
- **Operator/function definitions.** Parameter-less operators → a plain `var` (mutable in
  Go's type system; "immutable" is a documentation convention) initialized once (Go's
  `const` accepts too small a class of types). Parametric operators → Go functions (Go has
  native mutual recursion); names capitalized (Go public/private convention) regardless of
  original casing, except `LOCAL` definitions. **An operator is never recursive here**:
  `RECURSIVE` is out of the language and `[Operator definition]` checks a body without the
  operator in `Γ`. **Recursive *functions*** need a bootstrap trick (the generator closure
  calls back into the `LazyFunction` it's building): `MkRecFn` allocates the `LazyFunction`
  with a `nil` generator, then overwrites `.gen` with a closure capturing the function by
  reference — ties the knot. A function definition *may* recurse (its name is bound while
  its body is checked), so `FnConstructor` vs. `MkRecFn` is chosen by looking for the
  self-reference, not a keyword; exact, since a definition's own name reads as a binder
  inside its body and a module-level name elsewhere, and the two never collide (binder = Go
  function parameter, top-level name capitalized; a binder spelled exactly like its own
  function is rejected). **Only the parametric-operator form can be polymorphic**: a rigid
  type variable becomes a Go type parameter + dictionary parameter; the other three forms
  are package-level `var`s and Go has no generic `var`. A multi-binder function definition
  is rejected (its domain is a Cartesian product, not a runtime operation). A generated file
  is therefore a list of `func`s and `var`s — the only forms emitted, records/tuples needing
  no type declarations.
- **Name spelling: `_` → `__`, `$` → `_`, at every name crossing into Go.** `$` makes
  `freshName` collision-free (§2) and isn't a legal Go identifier character, so the
  guarantee is re-established in Go's alphabet. Escaping both sides keeps the two
  name-spaces disjoint by **parity**: an underscore run in the output is a sum of
  two-per-`_` + one-per-`$`, odd exactly when it covers an odd number of `$`s. A user name
  has none (all-even); a fresh name has exactly one (one odd run). Escaping fresh names
  alone wouldn't do (`set_1` stays reachable), so definitions, record fields, binders,
  parameters, type variables, constant type names all route through the same function. Not
  injective (`_$` and `$_` coincide) — fine, separating the name-spaces is all that's asked;
  a second `$` in one name would flip a run to even and break it. `ord` is reserved as a
  `freshName` prefix (the dictionary parameter `ord_a` would otherwise be an escaped
  `ord$a`).
- **Renaming is a pure function of the name, not a collision map.** Forced by record fields:
  Go identifies struct types *structurally*, so a field must get the same Go name at every
  occurrence or two identically-shaped records become two types, and the field sorting stops
  making the shapes coincide. A collision map would need every field name in the program
  before anything is emitted, and fields occur in inferred types. Disambiguation mark = one
  appended `_`, composing with the parity split (an escaped name's trailing run is even, so
  adding one lands in the compiler's half). Which side is marked follows each class's source
  convention: definitions must start uppercase and TLA+ definitions are conventionally
  capitalized, so `Init` is clean and `init` marked; record fields must be capitalized too
  but are conventionally lowercase, so `from` → `From`. Package-level names and struct field
  names share no namespace. Uppercasing is Unicode-aware: `élan` → `Élan_`, genuinely
  exported. Binders aren't capitalized (§7.2.2) but are moved off Go's reserved words *and*
  predeclared identifiers (a binder named `len` would capture the `len` a compiled
  quantifier emits beside it).

**Compiling atomic blocks**, thesis §7.2.3.1. `l : either B1 or ... or Bn` compiles to one
scheduler function `l` plus one function per branch `B_i`, named `l_i`:

- **Scheduler `l`** — parameters: locks `ℓ1..ℓk` (typed `Lock[struct{...}]` per the
  shared-variable grouping Definition 7.1.3 assigns, `Lock[τ] := chan τ`), `net Network`,
  `self Address`, `done chan struct{}`. Loops (`for shouldContinue`), each iteration picking
  a uniformly random branch index via `Rand()` and calling `l_i`, continuing iff `l_i`
  returned `false` (guard failed, nothing fired) — an unfair scheduler (a random branch can
  starve), matching the isFair-ignored stance (§2).
- **Branch `l_i`** — same parameters, returns `bool` (`guard`'s final value). Body: `LOCK`
  the branch's locks (per `L[shared(B_i)]`, Definition 7.1.3), run the compiled
  guards/statements, `UNLOCK`, `return guard`. `LOCK`/`UNLOCK` are *formal* notation for one
  `st_i, _ = <-ℓ_i` / `ℓ_i <- st_i` pair per lock in the total order lock inference fixed,
  projecting each acquired struct's fields into locals right after `LOCK` and reassembling
  right before `UNLOCK`. **Generated code does not emit raw channel ops** — thesis §7.3
  calls runtime helpers `Acquire(ℓ)`/`Release(ℓ, structVal)` per lock/unlock site, avoiding
  leaking `Lock[τ]`'s `chan τ` representation (Listing 7.2.11). `Acquire`/`Release` live in
  `runtime/locks/` alongside `MkLock`: `MkLock[T any](init T) Lock[T]`, `Acquire[T any](l
  Lock[T]) T`, `Release[T any](l Lock[T], v T)`, over `type Lock[T any] chan T` at capacity
  1 seeded with `init`. `Release` takes the lock *and* the value (it has to name the channel
  to send back on); `Acquire` returns the guarded struct itself (the worked example projects
  `st1.tmp2` straight out of it). The lock *holds* the guarded value, making "read a
  variable without holding its lock" unrepresentable. Locks are not reentrant — acquiring
  one twice blocks forever — so lock merging keeps a block naming each lock once and the
  total order keeps two blocks from deadlocking; both are lock inference's obligation, not
  runtime-enforced. Release needs **no `defer`**: generated code panics by design on
  undefined TLA⁺ expressions (`FnApply` outside a domain, `CHOOSE` over an empty set,
  out-of-range sequence index), an unrecovered panic terminates the whole Go program, and
  locks are process-local, so no acquirer survives to block on the stranded value — the
  process crashes with a stack trace rather than hanging. Peers then block on a dead
  process, the accepted absence of fault tolerance (§9.6), not a locking defect.
- **Guards** → `guard = guard && <compiled expression>` (`await e`) or a `var` declaration +
  assignment (`with x = τ do e`). **`with x ∈ τ do e` (set-valued `with`) is unsupported**:
  the thesis rejects it outright (no principled way to pick a witness satisfying all
  subsequent guards without a constraint solver), not merely deferred.
- **Statements**: `skip` no-op; `print e`/`assert e`/assignment compile structurally
  (`assert` panics on failure); `send(c[e1], e2)` → `net.c[e1].Send(e2)` (indexed) or
  `net.c.Send(e2)` (non-indexed); `multicast(c, [y ∈ e1 ↦ e2])` → one call
  `comm.Multicast(net.c, e1, func(y comm.Address) τ { return e2 })` (see "Multicast");
  `goto l'` → `done <- struct{}{}` when `l'` is `Done`, else `go { l'(ℓ1, ..., ℓk, net,
  self, done) }` — a fresh goroutine per transition to avoid stack overflow (Go goroutines
  start with a small growable stack; a plain tail call isn't safe here).

**Multicast.** The thesis omits it from §7.2.3.1 ("a simple iterated send", no compiled
form). Compiles to one runtime call `comm.Multicast(ch, to, f)`:
- `ch` = `net.c`, the `Network` field, a `map[comm.Address]comm.Sender[τ]` (a multicast
  target is always an indexed channel).
- `to` = the recipient set `tlaplus.Set[comm.Address]`, from the collapsed filter's `set`
  (§5.2).
- `f` = `func (y comm.Address) τ { return e2 }`, the payload as a function of the recipient
  (the source binds it, the message may mention it).

**No loop emitted**: iteration lives in the library. The specification fixes no send order
and gives no way to observe one, so any order refines it. A recipient with no entry in `ch`
panics (a function indexed outside its domain, like every other undefined TLA⁺ expression).
The payload's function literal is why `ProcEnv` carries channels' element types
(`channelTyps`, gathered algorithm-wide): Go demands a literal state its result type.

**A tuple-domain recipient is rejected** (`unsupported`), like an over-indexed `send`: a
channel over more than one index group has no `map[comm.Address]` field to index.
Multi-component filters (§5.2) produce one, so they compile only once a channel can be
declared with a tuple domain.

**Compiling threads and whole processes**, thesis §7.2.3.2. `T_k` a thread, `l_1` its
first atomic block's label:

- **Thread function `thread_k`** — same parameters as the branch functions (locks, `net`,
  `self`, `done`), body a single call `_ = l_1(ℓ1, ..., ℓk, net, self, done)`. The rest of
  the chaining is `l_i`-to-`l_j` goroutine handoffs via `goto`'s compilation.
- **Receive-relay `thread_rx`** — compiles a `T_rx(mailbox → inbox)` thread (§5.5's
  reception thread, no Network PlusCal code, only semantics). Takes the same lock
  parameters plus `mailbox Receiver[τ]` (`Recv() (T, bool)`, thesis Listing 7.2.10) and
  loops: blocking-receive from `mailbox`, and only on success (`ok`) acquire `inbox`'s
  lock, `Append`, release. Locking only around the append means a `thread_rx` blocked
  waiting for a message never holds `inbox`'s lock.
- **Process function `p`** — named after the process's source name, signature
  `func p(net Network, mailbox Receiver[τ], self Address) (chan struct{})`. `mailbox` is a
  **caller-supplied parameter** (matches "no `main`" below). Body: `INIT_LOCKS` (every
  inferred lock via `MkLock` — thesis Listing 7.2.11, `Lock[T] := chan T` of buffer size 1
  pre-loaded with the variable's initial value; a channel used as a mutex, not a separate
  runtime type); a buffered `done'` channel (capacity = thread count `n`) and an unbuffered
  `done`; one goroutine per user thread (`thread_1`..`thread_n`, all signal `done'` on
  completion) plus `thread_rx` (runs forever, never signals `done'`); an aggregator
  goroutine that reads `done'` exactly `n` times then signals `done`. `p` returns the
  `done` channel immediately (non-blocking). `INIT_LOCKS` example (thesis Example 7.2.7):
  three variables across two locks emit two `var`/`MkLock` pairs, each `MkLock`'s initial
  struct literal built from each variable's declared initial value.

Thread-code block chaining, `Thread.rx` receive-loop compilation, `Process`/`Algorithm`
top-level wiring are direct ports of the schemes above.

**Settled while implementing §7.2.3.**

- **Acquisition is per branch** (Remark 7.2.4), and so is the inference (step 1 above, which
  departs from Definition 7.1.2's block-level phrasing). `ProcessLocks` records the
  variable-to-lock map and derives each acquisition set on demand.
- **Synthesized top-level names are `<Kind>_<parts…>`** — `Blk_`/`Brn_`/`Thr_`/`Rx_`/`Proc_`,
  each part `goIdent`-escaped and process-qualified. §7.3's own spellings can't be used (it
  calls `sndPi`'s scheduler `SndPi`, colliding with a definition named `sndPi`, and names
  the process function after the process — while `PingPongs.tla` has a process `Ping` beside
  a `CONSTANT Ping`). A single underscore only comes from a `$` (no user name has one), so a
  compiler name whose first underscore is followed by more characters is unreachable from
  `definitionName` (whose only single underscore is the trailing mark).
- **`r ≔ e` through a path compiles like `EXCEPT`**, not "compiling each index individually"
  as §7.2.3.1 has it (which assumes a TLA⁺ function is a Go map). Here a function is a
  `LazyFunction` and a sequence is 1-indexed, so `x[i].f := e` goes through the same
  `compileExcept` the expression form uses.
- **`print` → runtime `tlaplus.Print`**, not Go's builtin `println` (which accepts only
  basic types).
- **`Rand` lives in `runtime/sched`**, wrapping `math/rand/v2`. Neither a TLA⁺ value
  operation nor a lock; a fairer picker would go there if `isFair` stops being ignored.
- **`Core/Go/Syntax.lean` has two nodes §6.6 lacks**: `Declaration.typ` for the `Network`
  struct (without a named type, every signature mentioning it spells out the anonymous
  struct), and `Statement.expr` for a call evaluated for its effect (`Send`/`Release` return
  nothing).

**Worked example, thesis §7.3.** Ping-Pong `Pong` end to end (`Ping` a mirror-image
exercise) — the reference to check `Network2Go`'s output against. Pins down: lock inference
merges `tmp2`/`inbox_Pong` under one lock (`inbox_Pong ≻ tmp2`, `self` never locked, being
read-only); `net.Ping.Send(...)`/`net.Pong.Send(...)` call sites; the branch/thread/process
function shapes verbatim; the `Network` struct — one field per channel, named after it, a
non-indexed channel (`ping`) → a plain `Sender[τ]` field (Listing 7.2.9), an
address-indexed channel (`pong[Pongs]`) → a `map[Address]Sender[τ]` field.

**Runtime library.** `Core/Go`'s pretty-printer assumes a companion Go package (prior art
`github.com/mesabloo/distpcal-compiler/lib`, to be furnished under this project's import
path): TLA+ value encodings (`Seq`, `Set`, functions, records), `Address`, the
`Sender`/`Receiver` endpoint interfaces — but *not* address resolution/discovery or any
transport (deferred scope, above). **Lives in `runtime/` in this repo**, versioned with the
compiler: value types in `runtime/tlaplus/`, one file per TLA+ concept/stdlib module
(`sequences.go`, `sets.go`, `functions.go`, `ord.go`, …, mirroring `Driver/Builtins.lean`'s
`builtinModules` split); `Sender`/`Receiver`/`Address`/`Multicast` in `runtime/comm/`;
`Lock`/`MkLock`/`Acquire`/`Release` in `runtime/locks/`; `Ord` and the primitive newtype
dictionaries + composing constructors (`SetOrd`/`SeqOrd`) also here. **No** `records.go` or
`tuples.go` — records and tuples are anonymous structs with dictionary literals beside them.
Top-level `persistent/treemap/` (matching the vendored-directory convention) is the
ordered-map backing store for lazy functions.

**The compiler emits no `main`, no runnable program.** `Network2Go` produces Go source —
types and functions — not a deployable binary. Wiring into something that runs (writing
`main`, deciding how each Network PlusCal process maps to an OS process, bootstrapping how a
process finds the nameserver) is left to whoever uses the generated code.

**Same boundary for `CONSTANT`s and process sets (§2).** `p ∈ S` compiles to a **single**
Go function/type (parameterized over the process's identity/address), not `|S|`-many
goroutines. The caller supplies `CONSTANT` values and invokes each process's entry point
once per concrete process/address.

---

## 6. Verification strategy

### 6.1 Framework
`VerifiedCompiler/Trace.lean` defines `Trace`, an ordered-monoid-typeclass abstraction over
event traces (`τ` with `Monoid`, `PartialOrder`, two compatibility axioms between `≤` and
`*`), making refinement composable regardless of a pass's trace alphabet.
`VerifiedCompiler/Denotational/StrongRefinement.lean` defines simulation relations
`Terminating`/`Diverging`/`Blocking` between source and target *denotational* semantics —
each language's meaning as a `Set (state × trace × state)` relation (per
`Core/*/Semantics/Denotational.lean`), not an operational small-step system — with an
algebra on top: composability (`Terminating.Comp`), monotonicity, identity, arbitrary sups,
an `lfp` induction principle for fixpoint semantics (loops/recursion). Vendored essentially
as-is — generic over source/target languages and traces.

`StrongRefinement` bundles the four behaviours a maximal run can have: terminate, abort,
diverge, block. `Blocking` (refinement obligation for a finite run ending blocked) shares
`Diverging`'s shape (no output state, a matched disjunct at `Rτ`, an abort fallback at
`≼[Rτ]`), so its `Comp`/`Trans`/`Mono`/`Empty`/`union`/`star` lemmas are `Diverging.*` by
definitional equality; only `sup` and `starStutter` are proved directly. What makes it bite
is the *blocking semantics* `⟦·⟧∅` at the algorithm level, where T_rx is in scope — a
positive definition (`AtomicBranch.blocking` inductive, `AtomicBlock.blocking = ⋂ branches`;
a process blocks iff every thread's block blocks, including T_rx's on an empty channel).
`.claude/plans/blocking-clause-plan.md` owns that construction and the rx-thread model
(`L_s = L_t`, virtual `RECEIVE` rule) it builds on.

Two generalizations of the vendored framework, both driven by Guarded→Network (§6.2) needing
them to be provable at all. Same move each: a relation the base definitions held *fixed*
across a diagram becomes one that varies, and every composition lemma says how it combines.

**`Terminating` carries a pre- and a post-relation on states.** One relation before and
after a step is the right shape only for *preservation*. Split: vertical composition reads
`Terminating R S → Terminating S T → Terminating R T` (the single-relation form is `R = S =
T`), and a change of relation is an ordinary factor — `Terminating R S Id ∅ Id` is exactly
`R ⊆ S`. `Aborting`/`Diverging` keep a single relation (neither has a final state).
`Terminating.Id`, `.lfp`, and the `Diverging` fixed-point lemmas require `R = S`.

**`Terminating` also carries a relation between traces**, in place of trace equality. The
source trace is existentially quantified and related to the target's by a `Rτ` the pass
chooses. Vertical and horizontal composition say how two passes' `Rτ`s combine, instead of
forcing every pass in a chain onto one alphabet-level equality.

**Reception is *not* an observable event.** A semantics with a `recv` constructor plus `Rτ`
relaxed to happens-before consistency is unsound, not merely expensive: `Guarded2Network`
defers consumption to the `.rx` thread, so a source block whose guard never holds
(`l: receive(ch, x) ; await FALSE ; goto l'`) emits nothing while the target still pops
`ch` — the mismatch is in the *multiset* of events, not their order, so no reordering
relation relates the two traces. `Behavior` is `print | send`, `.rx` is silent, and what
ties a channel's contents to the target's `inbox` is the refinement invariant `relatesTo`.
The generalized `Rτ` stays (it lets a pass pick its own trace relation); this pass picks
equality (`Trace.instSeq`).

**The expression interface carries four laws and a sequence vocabulary.** `ExprSemantics`
(`Core/ComputableTLAPlus/Semantics/Interface.lean`) holds `evalUnique` (an expression has at
most one value — non-determinism enters through `with x ∈ S` and scheduling, never an
expression), `evalLocal`, `evalSubst`, `evalExcept`, and the value-level sequence pair
`isSeq`/`seqAppend` with `isSeq_inj`/`seqAppend_isSeq`. `evalUnique` makes a channel `Ref`'s
index path resolve to one `ChanKey` (`EvalStep.inj`/`.path_inj`), without which the
Guarded→Network invariant can't name the FIFO a `receive` reads. What a *TLA⁺ builtin* means
stays out of Core: the `Head`/`Tail`/`Len(e) > n`/`<<>>` expressions `Guarded2Network` emits
get their laws from that pass's own `SeqBuiltins` class (`Guarded2Network/Lemmas/Seq.lean`),
taken instance-implicit by the refinement theorems.

**The trace relation is not axiom-free.** Positive position rules out *vacuity*, not
*obligations*. `Trace (εₛ εₜ)` bundles `Rτ : Rel εₛ εₜ` with `Rτ_total : LeftTotal Rτ` and
`Rτ_closed : MulClosed Rτ`. Vertical composition (`.Comp`) needs the second factor's `Rτ`
left-total (the target ran to completion on both factors even when the source aborts in the
first); horizontal composition (`.Trans`, through an intermediate language) needs the first
leg's `Rτ` both left-total *and* closed, via `Trace.scPrefix_rcomp`. `Id` carries equality,
needing neither. Values are threaded as instance-implicit `[T : Trace εₛ εₜ]` wherever laws
are consumed, never a plain explicit class argument, never a global `instance` (a pass's own
`Rτ` would compete with the generic `Rτ := Eq` case for the same list type — opt in locally
with `attribute [local instance] Trace.instList`).

**Divergence needs a third relation law plus two obligations that aren't about the
relation.** The class carries `Rτ_one : Rτ 1 1` (`Rτ_total` supplies *some* source trace
over `1`, nothing forces it to be `1`, while "the first `n` steps' traces are related" needs
`1` as its base case). The other two stay explicit hypotheses of `Diverging.omega`:
`Rτ_omega` (a pointwise-related family of traces has related infinite products) mentions
`OmegaProd.ωProd`, so bundling it would put `[OmegaProd εₛ] [OmegaProd εₜ]` binders on every
lemma taking a `Trace`; `OmegaProd.HasPartialProdDvd εₜ` (every finite prefix of an infinite
product divides it) is a property of the target monoid's product, not the relation. A fourth
hypothesis `abs : semₛ ∘ᵣ₁ semₛ' ≤ semₛ'` places an abort reached after `n` steps in `semₛ'`
itself rather than `semₛⁿ ∘ᵣ₁ semₛ'`; any aborting semantics defined as a least fixed point
of `X ↦ immediate ∪ sem ∘ᵣ₁ X` satisfies it via `map_le_lfp`, and `Algebra.aborting` has
that shape.

The relation and its laws live in `VerifiedCompiler/Trace.lean`. Design reference:
`arxiv.org/pdf/2404.17297` §7 — a source of ideas, not statements; wrong in places.

### 6.2 The Guarded→Network proof
Committed scope (§2): only **Guarded PlusCal → Network PlusCal**, matching prior art's
proof. `Core/{Guarded,Network}PlusCal/Semantics/{Denotational,Lemmas}.lean` plus
`Guarded2Network/Lemmas.lean` establish a `StrongRefinement.Terminating`/`.Diverging`
instance between them, ported and re-derived against the fresh ASTs. The pass's correctness
theorem (`Guarded2Network.correct`) is sorry-free.

The expression layer is **abstract**: `Core/ComputableTLAPlus/Semantics/Interface.lean`'s
`class ExprSemantics (V : Type)` supplies a relational `Eval` plus the value operations the
statement/thread rules need (`tru`/`isBool`/`isSet`/`mem`/`updatePath`/`coerce`/`seqAppend`).
`Eval` is a relation, not an `Option`-valued function: a user-defined operator call
re-descends into that operator's body with no measure the termination checker sees, but an
inductive `Prop` needs only strict positivity, and an expression with no derivation has no
value — so `Aborts` is derived from `Eval`, not assumed alongside it. The real TLA⁺
evaluator arrives later as one instance.

The elaborated `Expression` AST uses **locally-nameless binding**: an expression-level
binder (`\A`/`\E`/`CHOOSE`/set-builder/`map'`/`fn`, operator parameters) puts a de Bruijn
index in its body (`Origin.bound`); a `Memory`-keyed name (PlusCal
`variables`/`channels`/`fifos`, `self`, a statement `with`) is `Origin.free`. α-equivalent
expressions are then syntactically equal, so substitution never captures and
`evalSubst`/`evalLocal`/`evalCoerce` carry no freshness side condition.
`.claude/plans/locally-nameless.md` owns the construction.

`isBool`/`isSet` keep *aborting* distinct from *blocking*: a non-boolean guard aborts where
a false one blocks; a non-set `with x ∈ e` aborts where an empty set blocks. Membership
alone can't separate those.

The semantics are plain definitions, not `Reduce`/`Abort`/`Diverge` instances: those take
their second argument as an `outParam`, and the value type occurs only there — nothing in a
`Statement`/`AtomicBranch` mentions it — so no synthesization order exists while the
expression layer is abstract. `StrongRefinement` takes the relations as plain `Set`s.

Both languages share one state space (`Behavior`, `ChanKey`, `FIFOs`, `LocalState`),
declared once in `GuardedPlusCal`. `Guarded2Network` touches neither memories nor channels
(it moves a `receive` out of guard position into a `Thread.rx`), so sharing lets the
refinement be stated over one state type. `Semantics/Lemmas.lean` also carries a flat
encoding `LocalState'` where the terminality index becomes an `Option String` field —
`StrongRefinement`'s relation is over one fixed type, can't be indexed.

**`reference/jlamp.pdf` §3.3 is authoritative for these semantics.** `LocalState` is the
paper's `LState = (Var → Value) × (Var → Value*)`: memory and channels, nothing else — no
component for `with`-bound temporaries (a syntactic property `WellFormedness/` establishes
on the way in; keeping it would force every transcribed lemma through a state-shape
translation).

**`Memory` and `FIFOs` are `Finmap`, not `AList`.** An `AList`'s key insertion order is part
of its identity, but `evalLocal` makes evaluation depend on a memory only through `lookup`,
so any lemma commuting one write past another (`Guarded2Network/Lemmas/Reorder.lean`) can't
be an equation over `AList`. `Finmap` is the quotient; `Finmap.insert_insert_of_ne` is the
commutation, extensionality is by `lookup`. A channel update is `insert`, not
`AList.replace` — every rule establishes `F.lookup k = some _` before writing `k`, and
`insert` has the usable equation.

**The reorder pair is one equation and one inclusion.** Commuting an assignment past a guard
(D5, `Guarded2Network/Lemmas/Reorder.lean`) is an *equation* on `reducing` (both orders take
the same two silent steps to the same state). On `aborting` it is only `≤` (compiled order
inside source order): a guard can **block** where an assignment can't, so a state where the
assignment aborts and the substituted guard blocks is a source abort with no target
counterpart. `assign` having no blocking outcome is what makes the inclusion provable
(`assign_aborts_or_steps`, classical twice over — `Eval` is a relation).

**One state relation, composite target.** `relatesTo` is both pre- and post-relation
throughout the Guarded→Network proof. The precondition looks like a counterexample and is
not: between the compiled precondition and the consumption assignments the source has
written k refs and popped k messages while the target has done neither, so `relatesTo` fails
*there* — but the target side is the composite `⟦B'⟧* ∘ᵣ₂ ⟦assigns⟧*` and `StrongRefinement`
only quantifies a composite's endpoints, both `relatesTo` (the drained prefix `vs`
existential inside). A `.rx` relay moves a value from `F₂[c]` to `inbox`, growing `vs`
exactly as `F₂[c]` shrinks, so `F₁[c] = vs ++ F₂[c]` is untouched.

**Two prefix roles; one is a parameter.** `relatesTo` takes `pref : ChanKey V → List V`
beside `mbox`. Keys *other* than this process's channel carry `pref k` (other instances'
inboxes, unobservable here). It is a **parameter**, not an existential: the algorithm level
must know those keys come back unchanged after a block runs, and "the same `pref` on both
sides" is the only way to state that (an existential would let `Terminating R R` re-witness
on the right, `R σₛ' σₜ'` unable to mention the pre-witness). This process's *own* channel
keeps its existential `vs` (it is the one prefix the process changes); keeping it out of
`pref` leaves `relatesTo` closed under `receive`, so branch and block stay single-relation
`StrongRefinement`s. `.claude/plans/item7-refinement-proof.md` has the alternative weighed
(existential `pref` + a frame lemma on the source block).

**One state per instance is definitional.** `Instances ι V` is `ι → Option (ProcState V)` —
a function, not a set — so one state per instance is not an invariant to carry or prove.

**Divergence needs a measure, not a `star` collapse.** `Terminating`/`Aborting` lift by
instantiating the framework law at `semₛ := Relation.star stepₛ` and collapsing `R**` with
`Relation.star.star_eq`. Divergence has no such collapse — `Relation.omega (Relation.star R)
≤ Relation.omega R` is **false** (an infinite sequence of empty runs witnesses the former,
nothing in the latter). The shape that works is CompCert's — per target step the source
takes one step, or none with a well-founded measure decreasing, or aborts —
`algRelatesTo.step_or_stutter` (`Lemmas/Algorithm.lean`, with `terminating` derived from
it). Measure = `GuardedPlusCal.FIFOs.size`: a relay moves a message out of a channel, only
a `send` puts one back (a code step, which does move the source).
`StrongRefinement.Diverging.omegaStutter` is the framework law at that shape;
`algRelatesTo.refines` assembles all three components at the closed forms. The stutter
branch requires the *target's* trace to be `1` there, keeping the reindexing one-sided
(`Rτ_omega` applies pointwise at the original indices, only the source's run compressed) —
compression is `Relation.omega.of_idle` over `Stream'.Seq.ωProduct_comp_of_ones`. No
fairness condition needed: the drain measure rules out infinite `.rx` runs. Silent
divergence through code steps (`l: goto l`) is why the trace side can't instead assume
infinitely many non-`1` factors.

**An instance's channel must exist** — the third clause of `algRelatesTo`, for soundness.
The target's receiving thread *aborts* on a channel resolving to no FIFO and the source has
none to answer with, so where an instance's key is absent, `Aborting` is false. The other
three cases of `Thread.rxBranchAborting` are excluded by clauses `procRelatesTo` carries
(resolved `cpath`, `inbox` bound, `inbox` holding a sequence via `seqAppend_isSeq`); only
channel presence had no home. Nothing removes a key (`send` writes only at a key it has just
read), so it rides along (`NetworkPlusCal.AtomicBranch.reducing'_fifos_mem`); established
initially by `Algorithm.init`.

**A stuttering source needs `Terminating.starStutter`, not `sequentialOmega`.**
`sequentialOmega`'s terminating hypothesis answers one target step with one *source step*;
this pass can't (an `.rx` thread's step has no source counterpart, answered with the empty
run). `starStutter` is the `semₛ := Relation.star stepₛ` instantiation
(`Terminating.star`'s), with `Relation.star.star_eq` collapsing the `R**`, so the conclusion
stays at `star stepₛ`; its absorption side condition arrives starred too
(`Relation.star.star_lcomp₁_absorb`). The `Aborting`/`Diverging` halves of `sequentialOmega`
want the same treatment; divergence unattempted (§6.3).

**The algorithm level's dispatch is D8's specification, inlined.** No interface between pass
and proof: per instance and per owned *target* label it's either a code label (block
compiled from the source block at the same label, branches pairwise `BranchRefines` at every
`pref`) or an `.rx` label (block is `Thread.rxBranch` on the instance's own channel),
resolved inline where each consumer needs it — `step_or_stutter` and `immediateAbort`
dispatch on `ProcessRefines.label_cases` directly. Establishing the dispatch is a question
about `Thread.toNetwork` (D8), not the proof. `inbox_ne_self` is load-bearing:
`CodeTable.procReducing` requires the memory to bind `selfName`, and source agrees with
target only away from the generated `inbox`.

**Label agreement is a hypothesis.** A target process's label set is the source's plus its
`.rx` threads' — `procRelatesTo` carries `L₂ = L₁ ∪ rx` and `Disjoint L₁ rx`. It survives a
block step only given two syntactic facts about the *compiled* process, which the algorithm
level can't see and takes as hypotheses (`algRelatesTo.block_step`): the scheduled label is
a source label, and the branch's terminal `goto` targets a source label. Both are `freshName`
facts about `Thread.toNetwork` (D8). Same shape as the key-stability obligation
(`Guarded2Network/Lemmas/Locality.lean`): the algorithm-level invariant is *false*, not
merely unprovable, if a code thread could be scheduled at an `.rx` label.

**D8 climbs one rung per syntactic level; the top two rungs carry the content.** Branch,
block, thread: `BranchRefines`, `BlockRefines`, `ThreadRefines`/`RxOnly`
(`Guarded2Network/Lemmas/Thread.lean`), each the one below it under `Spec.mapM_list`
(plumbing). Two things don't lift that way. `pref` stays a theorem binder at every rung and
gets its `∀` only at the top (a `run = ok algo'` hypothesis pins the output independently);
pushing `∀ pref` down leaves `mvcgen` with a VC of type `ChanKey V → List V` with no right
answer. And the `freshName` obligations (`inbox` fresh for `BranchesFresh` and
`inbox_ne_self`; each `.rx` label distinct from every source block label for
`not_rx`/`exits`) first arise at the *process* rung, `Thread.toNetwork` being handed its
`inbox` rather than choosing it.

**Freshness is two-sided, meeting at `Generated`.** `Process.toNetwork` invents its `inbox`,
so a hypothesis about that name can't be stated at it. `Guarded2Network/Lemmas/Monad.lean`'s
`Generated namePrefix s` (`∃ n, s = s!"{prefix}${n}"`) is what both sides meet at. The pass
proves it (`freshName_spec`; `RxOnly` carries it per `.rx` label, established at
`stepBranch`). The front end's obligations are `¬ Generated "rx" l` over source labels,
discharged by the lexer for every counter value at once (`$` not being an identifier
character). Hypotheses about generated names are quantified over the name (`ProcessFresh`),
so no proof computes on characters.

`Algebra` is `String × V → CodeTable V`, `self` is `p.2` — no record, no `owned`, no
`self_eq`. A compiled process still owes `name_eq`: `Algorithm.algebra` resolves `table` by
process name, so one compiled under a different name resolves to the wrong table.

**A receive-free process needs `mb = .none`; one construct forces `.some`.** `Mailbox`'s
`none` case is forced, not spare generality: `stepBranch` declares the `inbox` local only
when a branch receives, so a receive-free compiled process never binds `inbox`, while
`relatesTo (.some (c, inbox))` requires `σₜ.mem.lookup inbox = .some sv` — false at
`Algorithm.init`.

`action_refines`/`guard_refines` are mailbox-polymorphic and `Fresh .none` is vacuous, so
`mbox` is a parameter of the whole ladder (`WalkInv` through `AlgorithmFresh`). **Exactly
one construct forces `.some`**: a `receive`, via `BranchesFresh.mbox_some` (`∀ c r coe,
receive c r coe ∈ … → mbox = .some (c₀, inbox)`), discharged in `stepStatement_spec`'s
`receive` case and nowhere else. `BranchesFresh.none_of_no_receive` /
`ProcessFresh.none_of_no_receive` give the `.none` bundle from "no receives" alone (making
that mailbox reachable, not merely statable). `ProcessFresh` takes the mailbox as a function
of the generated name — which mailbox a process gets is settled before the pass runs, the
name filling `.some` is not.

**Which mailbox comes from the source, not the proof.** A process declares its `@mailbox`
(`GuardedPlusCal.Process.mailbox`), `Process.toNetwork` copies the field, so `procMailbox
algo'` reads it off the compiled process — passed to `algRelatesTo`, not chosen by whoever
invokes the proof. Sound because the front-end normalization (§5.2a) rejects a `receive`
without a declaration and drops a declaration with no `receive`, so `p.mailbox` means "the
channel this process receives on, if any". A receive-free process with a `.some` mailbox
isn't unsound (its branch refinements hold vacuously) but makes `algRelatesTo` unsatisfiable
at `Algorithm.init`. `Guarded2Network/Lemmas/Algorithm.lean`'s `procMailbox` still reads the
mailbox off a compiled `.rx` thread (backwards; becomes `p'.mailbox` when D8 is assembled).

**Label disjointness splits the same way** — two facts meeting at `Generated`. The pass's
half is `ProcessRefines.rxLabels_generated`: every label in `rxLabels p'` came from
`freshName` (`stepBranch` is the only maker; every code thread is `.code` by
`ThreadRefines`). The front end's half is `LabelsHygienic p`: no source block label, and no
branch's terminal `goto` target, is `Generated "rx"`. `rx_disjoint`/`exit_not_rx` are the
corollaries; `goto` being the only terminal statement constructor lets the second field be
stated syntactically (`Br.action.last`). `ProcessRefines.ownedLabels_eq` makes the split an
*equation* (`NetworkPlusCal.Process.ownedLabels p' = rxLabels p' ∪
GuardedPlusCal.Process.ownedLabels p`); `label_cases` packages it with the disjointness for
`step_or_stutter`/`immediateAbort`. Exhaustive + exclusive make `ownedLabels p'` a genuine
disjoint union, matching `procRelatesTo`'s `L₂ = L₁ ∪ rx` / `Disjoint L₁ rx`.

**A label's branches are a concatenation, so `refines` is `BranchesRefine`, not `Forall₂`.**
`Process.codeTable` lets a label denote the union of every block carrying it, and
`WellFormedness/Labelling.lean` checks only that `goto` targets exist, never that labels are
unique. So `srcBranchesAt`/`tgtBranchesAt` concatenate over all blocks at a label with no
positional pairing. `CodeLabelRefines.refines` is `∀ Br' ∈ brs', ∃ Br ∈ brs, …`, exactly
what its only consumer (`blockRefines_step`, via `exists_left`) spends; assuming label
uniqueness would be an unverified precondition since no pass checks it. `BlockRefines` keeps
its `Forall₂` (per block it is positional). Non-enforcement of uniqueness is a real gap (a
`goto` naming a duplicated label is silently non-deterministic choice) — **§9.29**; the
proof doesn't depend on closing it.

**"Receives ⟹ a thread was registered" is a ghost-carrying walk.** `procMailbox` reads the
mailbox off an `.rx` thread, so the pass owes the forward direction: a receiving source
process compiles to one with a thread draining its channel. `RxOnly` gives the converse free
(it forces `mbox = .some` on every registered thread). The fact is established at
`stepBranch` (the only writer of `rxThreads`) and carried per rung, conditioned on
`BranchReceives`/`BlockReceives`/`ThreadReceives`/`ProcessReceives`. Each step case needs "a
non-empty list stays non-empty", which relates pre- to post-state — a Hoare postcondition
can't mention the pre-state, and `Std.Do` has no primitive for it — so it enters as a
universally quantified ghost, `Registered (H : Prop) st := H → st.rxThreads ≠ []`, with pre
`Registered H st` and post `Registered (H ∨ ‹this receives›) st'`. Confined to the three
walks under one `ThreadState`, collapsing at `mapM_stepBlock_spec_run` (walk starts at `{}`,
`H` is `False`); above that the accumulator is the result list and `++` supplies
monotonicity. `ProcessRefines.threads` ends `∧ (ProcessReceives p → rxs ≠ [])`, spent by
`procMailbox_eq` (`mb` is *computed* from the compiled algorithm, which the dispatch
obligations need — they take `mb : ι → Mailbox` as a parameter). The front-end half is
`MailboxUsed` (`∀ p ∈ algo.processes, ∀ inbox, mbox p.name inbox ≠ .none → ProcessReceives
p`), established by `checkReceiveChannels` rejecting a receive without a mailbox (§9.30).

**No interface layer between dispatch and pass correctness** — no `AlgebraRefines`.
`algRelatesTo.step_or_stutter`/`.immediateAbort` resolve the instance and dispatch on
`ProcessRefines.label_cases` directly. `find?_refines` turns an instance into a related
process pair; `src_algebra_table`/`tgt_algebra_table` get past `Algorithm.algebra`'s
`Option.elim` to the bare `Process.codeTable` the field lemmas are stated at. Four
hypotheses: the pass's `ProcessesRefine`, and `MailboxUsed`/`AlgorithmFresh`/`LabelsHygienic`
(front end's).

**The pass's correctness theorem is proved.** `Guarded2Network.Algorithm.toNetwork_refines`:
compiling an algorithm yields one whose algebra refines the source's under `algRelatesTo`,
at `procMailbox`/`procRxLabels`. Three hypotheses, all the front end's — `AlgorithmFresh`,
`MailboxUsed`, `LabelsHygienic`. It is `Algorithm.toNetwork_spec` (the four walks) composed
with `algRelatesTo.refines` (the refinement argument).

**`pref`'s `∀` is a five-line lemma.** A spec supplies one prefix function per instantiation
and `Std.Do` has no infinitary conjunctivity (`PredTrans` is binary), but `G2NM` is
deterministic (`wp⟦x⟧ Q n` is a match on what `x` returns at `n`, the same whatever `Q` is),
so `triple_forall` (`Guarded2Network/Lemmas/Monad.lean`) proves the infinitary version
directly by unfolding `wp` — the one place in this development that does.

**The declared `@mailbox` field can't serve as the `Mailbox`.** Two of the three things a
`Mailbox` holds are missing: the generated `inbox` is not in it (the pass writes it into the
threads/local, never the field), and the channel is `Option (String × List Expr)` where a
`Mailbox` holds a `ComputableGuardedPlusCal.Ref` (no `baseType`, `args` without the `String
⊕ ·` summand `relatesTo` evaluates with `EvalStep`). Reading the receiving thread is the
only place the generated name exists. Worth revisiting: `relatesTo` uses only `c.name` and
`c.args`, so `Mailbox`'s `Ref` is wider than anything reads.

**The initial states are related.** `Guarded2Network.Algorithm.init_refines`: every
`NetworkPlusCal.Algorithm.init` state of the compiled algorithm has a related
`GuardedPlusCal.Algorithm.init` state of the source under `algRelatesTo`, at the same
`procMailbox`/`procRxLabels` — keeps `toNetwork_refines` from being vacuous. The source
state is built on the *target's own* FIFO map: `Algorithm.toNetwork_spec` reports
`algo'.globalState = algo.globalState`, so the two `init`s' channel clauses are the same
statement, `pref` is `λ _ ↦ []`, the FIFO equation reflexivity. The instances are the
target's own with the pass's three differences undone: `ProcessRefines.inits_eq` strips the
`inbox` initializer off the memory, `.entryLabels_eq` strips the receiving threads off the
label set, `InitKeys` says what the inbox accounts for.

**`init` is a characterization of membership, not an existence claim.** "For each declared
instance some state exists" doesn't pin down which. One state per instance is not a clause
to derive (`Instances` is a function), but the *value* is only characterized, so
`ExprSemantics` states `evalUnique`: the initializers pin their values, so `InitProc` pins
the state.

**Front-end obligations the initial state adds** — two beyond the three
`Algorithm.toNetwork_refines` carries.

- **Process names are unique** (`(algo.processes.map (·.name)).Nodup`). Not bookkeeping: both
  `Algorithm.algebra`s resolve an instance by `find?` on its process name, so two processes sharing
  one would have every instance of the second running the first's code. It is what pins `find?` to
  the process an instance came from, on both sides — the target's names are the source's pointwise by
  `ProcessRefines.name_eq`. The front end checks it: `duplicateProcessName`, §5.2a.
- **`InitKeys`**, three clauses about the key a receiving instance starts on: the mailbox channel's
  index expressions *evaluate* in that instance's own initial memory, the resulting key names a FIFO
  that exists, and distinct instances get distinct keys. None is anything the pass decides. The third
  is the well-formedness condition that a process set's mailbox is indexed by `self` — without it one
  FIFO would be accounted against two inboxes and no relation of `algRelatesTo`'s shape could hold.

**`ExprSemantics.eval_seq_nil` is stated as existence**, `∃ s, Eval M (.seq [] τ) s ∧ isSeq
s []` (like `seqAppend_isSeq` — totality is part of the law). A compiled instance has an
initial state only if every initializer evaluates, and `<<>>` for the `inbox` is the only
initializer the pass invents. Implication form: `isSeq_of_eval_seq_nil`, `evalUnique` away.

**The pass is packaged as `Compiler.Correctness`** (`Guarded2Network.correct`).
`VerifiedCompiler/Denotational/Correctness.lean` states "this pass is correct" for any pass:
the target's initial states are covered by related source ones, and its behaviour refines
the source's.

**Both halves live in one Hoare triple, the relation indexed by both programs.**
`algRelatesTo`'s mailbox and receiving labels are read off the *compiled* algorithm and
mention an `inbox` name the pass invents — no relation written before the pass runs can name
it, no outer `∀` can bind it (the compiled algorithm exists only under `C x`). Same for
`isInit`/`isInit'`.

**Composition needs the relation forgotten.** A chain's simulation relation is `R₁ x y ∘ᵣ R₂
y z` at the intermediate program `y`, which exists only inside the first triple, and can't
be recovered by quantifying `y` inside the relation (`StrongRefinement` takes its relation as
both pre- and post-relation, `Terminating R R …`, monotone in neither direction).
`Compiler.Correct` is `Correctness` with the relation existentially quantified inside the
triple; `Correctness.toCorrect` and `Correct.comp` are the two lemmas that need.

**The source program type carries the front end's facts.** `Guarded2Network.SourceProgram`
bundles an algorithm with its `mbox`/`c₀` and a `FrontEnd` record of the five conditions.
`Correctness` quantifies over *every* program of its source type, so hoisting them into `∀
algo, AlgorithmFresh mbox c₀ algo` would ask one mailbox assignment to be fresh for every
algorithm at once — vacuous. `TargetProgram V` is a phantom index (like the framework's
`Reduce`/`Abort`/`Diverge` `outParam`: the program type must determine the value universe).

**Threads have no denotation.** A process state is a memory plus a *set of labels*, at most
one per thread; a step picks an enabled label, runs its atomic block, replaces it with the
label the block's terminal `goto` reached. A thread contributes only the labels it owns
(`NetworkPlusCal.Thread.labels`) and the block behind each.
`Core/GuardedPlusCal/Semantics/Process.lean` carries that layer, parameterized by a
`CodeTable` (label → what its block does) and per-process owned labels — mentions neither
language's AST, both instantiate it. Processes indexed by an arbitrary `ι` (the paper uses
`P` only as a name).

The three algorithm-level semantics are **closed forms over the algorithm step, not fixed
points**. The framework proves one preservation law per operator (§6.1), so no downstream
proof unfolds a fixed point; `VerifiedCompiler/ClosedForm.lean` carries the identities with
the corresponding least fixed points as checks.
- `Algebra.reducing` = `step*` (`Relation.star`) — every finite sequence of steps with the
  concatenated trace. A *reachability* relation, not a denotation on its own: it overlaps
  `Algebra.blocking` at the endpoint and contains every finite prefix of a divergent run.
  The empty execution is the zero-length run (`μX. Id ∪ (X ∘ᵣ₂ step)` would need an explicit
  disjunct or its lfp is `∅`).
- `⟦A⟧⁺` (`Algebra.terminating`) = `Algebra.reducing` cut to runs whose final configuration
  is `Algebra.isDone` (every process at a sentinel, `L ∩ owned = ∅`) — the paper's `isDone`
  endpoint, making it *terminating* rather than "reachable configs". The paper's `init`
  restriction is **not** in the set (below).
- `⟦A⟧⊥` = `step* ∘ᵣ₁ immediateAbort` ("some process goes wrong now") — finitely many steps,
  then an abort. Prefix is `step*` (reachability), not `⟦A⟧⁺` (a run to an abort need not
  pass through done configs).
- `⟦A⟧∞` = `step^∞` (`Relation.omega`): infinitely many steps, each paired with the infinite
  product of the traces. **Not** a greatest fixed point — `νX. step ∘ᵣ₁ X` overshoots (a
  step emitting the empty trace makes it non-contractive; at `step = {(σ, 1, σ)}` its gfp is
  `⊤`). Silent divergence isn't a corner case: `Behavior` observes only `print`/`send`, so
  `while TRUE { x := x + 1 }` is an infinite chain of trace-`1` steps. The paper's closed
  form `νX. Y ∪ R ∘ᵣ₁ X = (R* ∘ᵣ₁ Y) ∪ R^∞` is `Relation.gfp_eq_closedForm` — a
  characterization: `⊇` holds unconditionally, `⊆` needs `Relation.Productive R` (no infinite
  silent chain), which `Algebra.step` doesn't satisfy.

Initial states are a **relation**, not a function: local variables come from initializer
expressions and evaluation is relational, so an algorithm with a meaningless initializer has
no initial state rather than a junk one. The paper's four sets fix `σ_A = init(A)`; the four
here do **not**. `Compiler.Correctness` carries the initial states as a separate coverage
conjunct (every initial state of the compiled algorithm covered by a related source one)
because `StrongRefinement.Terminating` is `∀ σₛ, R σₛ σₜ → …` and reuses `σₛ` as the source
run's start, so an `init` filter on the *source* set would demand `init` of an arbitrary
`R`-related state. Restricting the *target* sets would be sound and free; not currently done.
The `isDone` endpoint on `⟦A⟧⁺` is in the set (both sides), transported backward by
`procDoneTransfer` (`Terminating.restrictEnd`).

The pass's correctness theorem is stated **on `Algebra`**, over the four closed forms
(`terminating`/`aborting`/`diverging`/`blocking`), not over individual atomic blocks.
Per-block refinement is an intermediate lemma — it can't say anything about the `.rx` thread
(a target-side label with no source counterpart, meaningful only once labels are scheduled).
`StrongRefinement.sequential` lifts a one-step refinement plus an immediate-abort and an
immediate-divergence one to the three-component refinement at `step*`/`step* ∘ᵣ₁
immediate`/`(step* ∘ᵣ₁ Y) ∪ step^∞`. The algorithm layer has no immediate divergence
(`CodeTable.procDiverging` is `∅`), so it applies `sequentialOmega`, the `Y = ∅` corollary.

Proofs pin the pass's monad to `ExceptT G2NError (StateT Nat Id)` rather than the pass's own
`[MonadDiagnostic Empty G2NError m] [MonadFresh m]` polymorphism: `mvcgen`/`mspec` need
`Std.Do.WP` instances, which Std supplies for `ExceptT`/`StateT`/`Id` and not for
`Common/Errors.lean`'s `DiagT`. Nothing lost — the pass's warning type is `Empty`, so `List
Empty` has one inhabitant and the `MonadWriter` half of `MonadDiagnostic` is trivial. A `WP`
instance for `DiagT` is the generalization if a pass that actually warns gets proved.

**A proof reaches the pass's internals with `import all`, not by widening its API.**
`stepStatement`/`processPrecondition`/`ReceiveState` stay `private` in
`Guarded2Network/PlusCal.lean`; `Guarded2Network/Lemmas/Precondition.lean` says `import all
Guarded2Network.PlusCal` (also un-hiding bodies, so no `@[expose]` needed). Cost: theorems
mentioning private names are private, and each proof file up the chain needs `import all` of
the one below. Only what the deliverable's *statement* mentions is public —
`substGuardStmt`/`convertActionStmt`.

**`mvcgen` covers `for` loops; every walk in this pass is a `mapM`.**
`Std.Do.Triple.SpecLemmas` ships specs for `forIn`/`forIn'`/`foldlM` (what `for` elaborates
to), none for `List.mapM`. `Extra/Do.lean`'s `Spec.mapM_list` closes that (from
`Spec.foldlM_list` through `List.mapM_eq_reverse_foldlM_cons`), `@[spec]` so `mvcgen` picks
it up. **Every theorem about the pass is a Hoare triple, never an equation about a `.run`.**
A run equation forces reading the pass *backwards* through its binds (which `mvcgen` can't
do, and which needs a per-stack adequacy + bind-inversion lemma); the refinement is carried
forward in the loop invariant instead. `Std.Do.WP.Basic`'s `of_wp_run_eq` exists per
*primitive* stack only, so adequacy for the three-layer `G2NM` gets written if the
deliverable ever needs it, not on speculation.

`Thread.rx` is not special: the paper defines its meaning to *be* that of the atomic block
`rxₚ : receive(mailboxₚ, tmpₚ) ; inboxₚ := Append(inboxₚ, tmpₚ) ; goto rxₚ`, "although
without the temporary variable `tmpₚ` assigned to". Draining the channel into `inboxₚ` is
one transition (a single atomic block); the self-`goto` makes it loop. `Thread.rx` carries
the label `rxₚ` (load-bearing — schedulable and self-referencing) and not `tmpₚ` (never
assigned). Both `freshName`-minted, so the label gets the `$`-hygiene that keeps it distinct
from every user-written `AtomicBlock.label`.

**`GuardedPlusCal.Algorithm.WellScoped` carries the two receive restrictions**, not only
binder scoping: `GuardedPlusCal.PreconditionReceives` states "one channel per process" and
"no `receive` target indexes its own channel" as `Prop`s — what §5.2a's executable checks
exist to justify. Concrete over `ComputableGuardedPlusCal` (because `Ref.freeVars` is). §2's
preservation lemma's antecedent grows by the same two conditions. The pass's *generated*
`inbox` is deliberately not covered (no well-scopedness statement can name a name absent from
the source); `freshName`'s `$` hygiene is argued lexically in `Common/Fresh.lean` with no
`Prop`, so inbox-freshness stays an explicit hypothesis discharged at `Thread.toNetwork`.

**A block's semantics is its statement list's.** `Block.reducing f B` is `Block.listReducing
f B.begin ∘ᵣ₂ f B.last`, `.aborting`/`.diverging` likewise — one `foldr` underneath. The list
form and `Block.reducing` are not interchangeable (a block's `last` may be terminal, so
`Block.reducing` is dependent in the guard index where the list form is homogeneous), but
that costs one composition, not a second recursion. `Block.diverging` *is* `Block.aborting`
(same body), so its lemmas are transports.

**Reordering a guard past pending assignments is two proofs.** The reducing half is an
*equation* (`reorder_assigns_guard'`, `reorder_pairs_lenGt`), the aborting half only an
*inclusion* (`reorder_assigns_guard_abort'`, `reorder_pairs_lenGt_abort`) in the direction
`emitted ≤ adjacent` (what `StrongRefinement.Mono` wants — it shrinks a target). Equality is
false: a guard can block where an assignment can't. Both applied *per step* inside
`stepStatement_spec`, not to a whole block: the pair a `receive` contributes is moved past
each following guard by the step that compiles that guard. The aborting half needs no second
semantic argument about the compiled guards: a `Len(inbox) > n` is a no-op where it fires,
and where it aborts its own consumption pair aborts too (`Len` has a value iff the inbox
holds a sequence, and then `Head(inbox)` does too), so the far side's index is never reached
and the `n + 1 → n` bookkeeping doesn't recur — what's left is one algebraic step
(`Relation.lcomp₁.commute_step`), shared by all four inductions. `SeqBuiltins` characterizes
only *evaluation* of the sequence builtins, so the abort argument goes through `assign`'s own
totality (aborts or steps, no third outcome) instead, and no abort law is added to the class.

**These definitions are deliberately stronger than the paper's**, which leaves several
failure modes to well-formedness conditions it assumes rather than states: `⟦receive(c,r)⟧⊥ =
∅` outright, and `await` on a non-boolean, `with x ∈ e` on a non-set, an assignment to an
unbound target, and a channel that resolves to nothing all merely block. Each aborts here.
Cost: the proof discharges cases the paper's never raise; gain: the semantics says something
about malformed programs rather than presupposing they don't arise.

### 6.3 What's explicitly deferred
Everything else — parser correctness, desugarer semantics-preservation, type-checker
soundness, Distributed→Guarded (`Computable2Guarded`) *behavioral* correctness (full
denotational refinement proof against `TypedPlusCal`'s semantics, the same `StrongRefinement`
sense §6.2 commits to for Guarded→Network), both new backends. "Deferred" = **not committed
for this initial roadmap, not abandoned** — proving `Computable2Guarded` correct in full is a
real eventual target. Meanwhile: a bug in `𝒞_reord` (§5.4, fully specified in the thesis but
unproven here) could silently miscompile with no proof to catch it. Treat *type-level*
invariants baked into the ASTs (`CorePlusCal`'s terminal-statement indexing, §3.2/§5.2) as
the first line of defense where full semantic proofs aren't attempted.

The well-scopedness preservation lemma (§2, §5.2a/§5.5) is a narrow *syntactic* structural
fact, lighter than the behavioral correctness deferred here — the first slice of
`Computable2Guarded`'s eventual correctness work, landing early because Guarded→Network's
proof needs it as a precondition.

### 6.4 Go's denotational semantics — not started here
The `go-semantics` branch's domain-theoretic account of Go (thesis ch. 6: solving `P ≅
F(P)` over a complete ultrametric space, via ~20 files from-scratch topology — `IMetricSpace`,
Lipschitz maps, uniform continuity, closed embeddings, Banach fixpoints) is real,
substantial, unfinished. Not near-term scope: verification is scoped to Guarded→Network only
(§2), and `Network2Go` (§5.7), once anyone proves it, is expected to reach correctness by
relating its lock-protected execution model back to `NetworkPlusCal`'s semantics directly,
not through a standalone Go domain model. Revisit once `Network2Go` exists and there's
appetite to prove it.

### 6.5 Verification method during development

Prefer `lean-lsp` MCP tools (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`,
…) over raw `lake build` for the file-by-file edit loop. Not a perfect substitute: run a
real `lake build` on the touched modules at least once before calling a file done.

Per-phase checkpoints: after scaffolding, vendored modules build clean. After the parser,
it lexes/parses a real `.tla` file (Ping-Pong, §8.6, or
`distpcal-compiler/tests/PingPong/PingPong.tla`) end-to-end through the CLI. After each
subsequent pass, its modules stay clean and a `#eval`/`#guard_msgs` smoke check exercises it
against Ping-Pong or Two-Phase-Commit (distinct from the fixture suite, §2). After
Guarded→Network, the refinement proof compiles with no `sorry`. Once both backends exist, a
hand-traced Ping-Pong compilation matches the thesis worked example (§8.6) for Join
Calculus, and a visually-sane idiomatic Go file for Go.

---

## 7. Suggested phasing

Not a schedule — a dependency-respecting order. Each phase produces something buildable
(`lake build`), even if incomplete/unverified. Wait for explicit approval after every phase
before starting the next — each is large enough (real time, a prior-art port or new design)
to warrant its own check-in.

**Current status: phases 1–10 done. Backends (phase 11) next.**

1. **Scaffolding — done.** `lakefile.lean` (package `Fugue`, targets per §4, current stable
   Lean toolchain), vendored `Extra`/`VerifiedCompiler`/`ProgressBar`/`Common`, `CLAUDE.md`,
   `reference/thesis.pdf`.
2. **Frontend ASTs + pretty-printers — done.** `Core/SurfaceTLAPlus`, `Core/SurfacePlusCal`
   syntax + `Std.ToFormat` instances (§5.1's parser targets these exact ASTs).
3. **CLI wiring — done** (`Fugue.lean`). `leanprover/Cli`-based parsing of the flag surface
   (§2), `FlagsEnv` built once from `Cli.Parsed` and handed to `Driver/Pipeline.lean`
   `runPipeline`, every pass querying it via `MonadReaderOf FlagsEnv m` accessors. The CLI
   is flag parsing, spinner hooks, printing, exit code; the compile is `runPipeline`'s.
   Target selection complete only once phase 11 exists. Two flag details open, §9.3.
4. **Lexer + parser — done** (§5.1). Ported from `distpcal-compiler`'s `Parser_/`, wired
   into the CLI: lex, optionally dump tokens/CST, parse, resolve annotations, report
   `fair`-process warnings subject to `-W`. Known gaps: §9.2.
5. **Desugarer — done** (§5.2). `CoreTLAPlus.Syntax.lean`/`CorePlusCal.Syntax.lean` fresh;
   expression desugaring (`Desugarer/TLAPlus.lean`) and statement desugaring
   (`Desugarer/PlusCal.lean`, basic-block extraction into the `Bool`-indexed terminal
   encoding), both wired into the CLI.
6. **Type checker — done** (§5.3): bidirectional rules from thesis §3.1, with the
   direction-aware metavariable-solving deviation (§2). `Ξ` as a `MonadModuleCache m`-backed
   in-memory cache, eager/transitive `EXTENDS` resolution, cycle detection. Sequenced ahead
   of phase 7 (§2, §5.2a).
7. **Well-formedness checking — done** (§5.2a): well-labelledness, variable
   well-scopedness, no-bare-temporal/action-operator check, over `CoreTLAPlus`/`CorePlusCal`
   — purely syntactic, runs after phase 6. Only the freshness/no-duplicate-names half of
   well-scopedness is load-bearing here. The two `WellScopedness.lean` files ported here
   (proof-support at phases 9–10); `CorePlusCal.WellScoped` authored fresh.
8. **`Typed2Computable` — done** (§5.3): separate from the type checker — collects every
   constant/variable/operator/function transitively reachable from the algorithm and
   translates each, plus the algorithm. Depends on phase 7 (treats its temporal/action-freedom
   and bounded-quantifier guarantees as established); rejects only `fnSet`/`recordSet`.
9. **`Computable2Guarded` — done** (§5.4): the `Ref` field-access prerequisite
   (`Ref.args : List (String ⊕ ε)`) and the same-atomic-step assignment-conflict tightening,
   ahead of the four subpasses (`𝒞_cflow`/`𝒞_par` unchanged-type `ComputablePlusCal.Algorithm`
   rewrites; `𝒞_flat`/`𝒞_reord` merged into one `Computable2Guarded/FlatReord.lean` walk
   straight to `GuardedPlusCal.AtomicBranch`). Hand-verified per-subpass against the thesis
   examples, incl. Two-Phase Commit `c2` (`tests/examples/TwoPhaseCommit.tla`) against Listing
   3.2.4. CLI: `-d dump-guarded`.
10. **`Guarded2Network` — done** (§5.5, §6.2): pass + refinement proof ported and re-derived
    against the fresh ASTs. `Guarded2Network.correct` (`Compiler.Correctness`), sorry-free;
    the well-scopedness preservation lemma is proved as its precondition. Front-end
    obligations (`AlgorithmFresh`, `MailboxUsed`, `LabelsHygienic`, process-name `Nodup`,
    `InitKeys`) are what §5.2a's checks exist to discharge.
11. **Backends, either order (independent siblings, §2):**
    - **`Network2JoinCalculus`** (§5.6): new implementation, validate against the Ping-Pong
      worked example by hand first. Resolve during this phase: §9.5 (multicast scheme).
    - **`Network2Go`** (§5.7): port the pass + lock inference + a runtime library skeleton
      (value encodings + `Address` + `Sender`/`Receiver`; no transport, §5.7). Resolve
      during this phase: §9.6 (numeric representation). Completes CLI target selection.
12. **Stretch, out of committed scope:** Join Calculus execution strategy (§9.1); verified
    coverage beyond §6.2; Go denotational semantics (§6.4); a real example/regression suite;
    a static "minimal needed addresses" analysis pass (§2), if nameserver-based addressing
    is revisited enough to make it worthwhile.

---

## 8. Language subset for v1

From the type-checking rules specified (thesis Figs. 3.1.13/3.1.15/3.1.16) — what
"Distributed PlusCal" concretely means here:

Statements: `goto`, `skip`, `await e`, `receive(c, r)`, `r ≔ e`, `with x = e do B` / `with x
∈ e do B`, `send(c, e)`, `assert e`, `print e`, `either B1 or ... or Bn`, `while e do B`,
`if e then B1 else B2`, `multicast(x, [y ∈ e1 ↦ e2])`. Processes: uniform process sets `p ∈
S ⋆ x1=e1,...,xm=em ⋆ T1...Tn` (single-process `process(x=e)` is sugar for `process(x ∈
{e})`, thesis §3.1.5 — desugared away early). Algorithms: `fifos c1:τ1,...; P1 ∥ ... ∥ Pn`.

`INSTANCE` and `RECURSIVE` are out of scope (§2). `LAMBDA` is out of scope (§9.10). Most
temporal/action operators aren't parsed (§9.11).

---

## 9. Open questions

In `OPEN_QUESTIONS.md`, same `9.x` numbering.
