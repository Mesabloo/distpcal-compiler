# Fugue — a compiler from Distributed PlusCal to the Join Calculus and Go

**Status:** planning document, written before any code exists in this repository.
**Audience:** Claude Code (or any implementer) picking this project up.
**Companion file:** `CLAUDE.md`, for day-to-day working conventions.

This plan was written jointly with the project owner after studying three sources of prior
art: the public prototype at `github.com/mesabloo/fugue` (branches `main`, `develop`,
`go-semantics`, `lock-inference`, `docs`), the more advanced private checkout at
`~/Documents/distpcal-compiler` (origin `github.com/mesabloo/distpcal-compiler`, branches
`main`, `develop`, `compiler`, `go-semantics`, `lock-inference`, plus an uncommitted local
`typechecker` branch), and the thesis `Generating Distributed Programs from Formal
Specifications` (copied into this repo at `reference/thesis.pdf`). None of that code is
being reused wholesale — see "What carries over" below — but its design is the main input
to this plan, and its gaps define most of the open work.

Where this plan is silent or a design genuinely has two reasonable answers, that is
intentional: the corresponding open question is listed in §9 rather than decided
unilaterally. Anyone implementing a phase who hits an unlisted ambiguity should add it to
§9 and ask, rather than guess.

---

## 1. Goals and non-goals

**Goal.** A compiler, written in Lean 4, from Distributed PlusCal (TLA+ modules with an
embedded PlusCal algorithm using Distributed PlusCal's `send`/`receive`/`multicast`/FIFO
extensions) to two independent backends:

1. **The Join Calculus** — a guarded-reaction dialect close to Fournet & Gonthier's
   original calculus, extended with a name-server (`register`/`lookup`) for distributed
   addressing. This is the more "formally tractable" target: its reaction semantics line
   up almost exactly with Network PlusCal's atomic blocks, which is why the thesis
   develops it as a compilation target in its own right rather than as a stepping stone
   to Go.
2. **Go** — real, runnable, idiomatic-ish Go source using goroutines and channels,
   depending on a small runtime library this project also owns.

**Guiding ambition.** The end goal is a *formally verified* compiler: every pass should
ultimately come with a proof that target-program behavior refines source-program
behavior, using the trace/simulation framework already sketched in `VerifiedCompiler/`
(see §6). Full end-to-end verification is explicitly **not** expected to be reached by
this plan — it is a north star, not a milestone.

**Non-goals for this plan.**
- Not a general-purpose TLA+ or PlusCal tool; only the Distributed PlusCal fragment used
  by prior art (bounded-buffer FIFOs, channels, `multicast`, addresses) is in scope.
- Not reproducing the domain-theoretic Go denotational semantics research
  (`go-semantics` branch) as near-term work — that effort is real and worth returning to,
  but it is large (ultrametric spaces, contraction mappings, ~20 files of topology
  infrastructure) and orthogonal to getting a working, testable pipeline. See §6.4.
- Not building a JoCaml-compatible, un-guarded Join Calculus emitter. The compiler
  targets the guarded dialect described in the thesis; how (or whether) that gets executed
  is an open question, §9.1.

---

## 2. Decisions already made

These were resolved with the project owner before this plan was written; implementers
should treat them as settled unless something concrete forces a revisit (in which case,
ask before overturning).

| Question | Decision |
|---|---|
| How do the Go and Join Calculus backends relate? | **Independent siblings.** Both compile directly from `NetworkPlusCal`, via two separate pass chains (`Network2Go`, `Network2JoinCalculus`). No sequencing between the two backends. This also matches the thesis, whose Join Calculus chapter targets Network PlusCal directly, not Go. |
| How much of the existing prototypes carries over? | **Fresh domain code, reused generic infrastructure — plus three ported exceptions.** `Extra/` (data structure lemmas), `VerifiedCompiler/` (trace + refinement framework), `ProgressBar/` (CLI spinners), and `Common/` (positions, diagnostics, pretty-printing helpers — genuinely generic, not tied to any one AST) are vendored in as a starting scaffold (adapted, not copied blindly — check what's still needed). Most AST definitions, semantics, and compiler passes (desugarer, checker, and every `*2*` pass other than Guarded→Network) are written fresh, using the prototypes purely as a design reference. The **lexer/parser** (§5.1), **Guarded→Network** (§5.5), and **well-scopedness checking** (`Core/GuardedPlusCal/Syntax/WellScopedness.lean` and `Core/TypedSetTheory/Syntax/WellScopedness.lean`, repurposed as proof-side invariants rather than the primary checking mechanism — §5.2a) are the three exceptions: all are working, non-trivial, and worth porting and refactoring/cleaning up rather than rewriting from zero. |
| Verification ambition for this plan | **Match the prototype's already-verified surface only.** Concretely: aim to reproduce a refinement proof for Guarded→Network (the one pass with a complete proof in prior art), and treat every other pass — including both new backends — as unverified for the initial roadmap. Lock inference is the one exception explicitly called out as needing real design work now (see below), because without it the Go backend's semantics are simply undefined, not just unverified. |
| Join Calculus executability | The compiler's job is to **emit a Join Calculus source file**; whether/how that file is later executed (custom interpreter, further lowering, etc.) is explicitly left open — see §9.1. Don't build an interpreter as part of this plan unless asked. |
| Lock inference / Go concurrency safety | **In scope.** The rest of `Network2Go` already works (real, goroutine-based concurrency); lock inference is the one missing piece, not a reason to redesign the backend. Concretely: one lock per atomic block, derived from a conflict analysis over which blocks share process-local variables — see §5.7 for the algorithm as specified by the project owner. |
| Example/regression suite | **A *formal*, automated test harness is still deprioritized** — the prototype's `tests/PingPong`, `tests/TPC`, `tests/LamportMutex` examples exist and are useful reading, but building test infrastructure is not a near-term milestone; the Ping-Pong example from the thesis is used informally throughout this plan as a running illustration only. **Resolves §9.5's open question, though:** the project owner has asked for a concrete, lightweight home for the small hand-written accept/reject `.tla` smoke tests written while developing/correcting each pass (not a maintained, harnessed suite) — `tests/regression/`, one small `.tla` file per confirmed behavior, named `accept_<what>.tla`/`reject_<what>.tla` so the expected outcome is legible from the filename alone. **Always write these in this project's actual supported concrete syntax — PlusCal's *C-syntax* (`{ }`-braced bodies), never the p-manual's own P-syntax (`do … end while`/`end if`) — the parser (§5.1) only accepts the former** (confirmed the hard way: an early attempt at hand-writing P-syntax test input failed to parse until rewritten in C-syntax). No runner/harness is implied — these exist for a human (or a future, still-deprioritized harness) to point the CLI at individually. |
| Build config format / toolchain version | **`lakefile.lean` (Lean DSL), not `lakefile.toml`** — same kind of config prior art uses. **Bump the Lean toolchain** rather than pinning to prior art's stale `v4.29.0-rc1`: start on the current stable release when implementation begins, updating `mathlib`/`batteries`/other pinned deps to match. **Expect real breakage from this, not just cosmetic fixes**, and not only in the three ported exceptions (§2) — `Extra/`'s vendored data-structure lemmas are exposed to the same API drift and should be expected to need real repair work too. This cuts both ways: some currently-broken `Extra/` theorems may become provable again once a partial API change elsewhere is fixed by the bump (e.g. string-related lemmas broken by a partial API change), not purely a one-directional cost. |
| CLI flag surface | **Settled**, GCC/Clang-style flag naming on top of `leanprover/Cli` (still the underlying framework, as in prior art — `--help`/`--version` come free from it): `-d<name>[=<value>]` (debugging options generally — AST dumps, but also e.g. `-dtiming` for per-pass timing, not just dumps), `-f<name>[=<value>]` (feature/config toggles, e.g. `-fno-color` to disable ANSI-colored diagnostic output — implemented, `Common/Errors.lean`'s `CompilerDiagnostic.pretty` takes a `colored` flag threaded from this), `-W<name>`/`-Wno-<name>` (per-warning control — e.g. `-Wno-fair` suppresses the `fair process`/`fair+`-ignored warning, §5.1), `-o`/`--output`, `-t`/`--target go|join`, `-I <path>` (add a module search path, see §5.3). Two details still open — Join Calculus "flavors" and where the Go `-p` package name lives — see §9.3. **Concrete invocation syntax, pinned down during Phase 2 (CLI wiring):** `leanprover/Cli` rejects the same named flag being given more than once (`duplicateFlag`) and parses `Array α`-typed flags as a single comma-separated occurrence, not true repetition — so each of `-d`/`-f`/`-W`/`-I` is one Cli flag of an `Array`-typed `ParseableType` (`-d name1,name2=value`, `-I dir1,dir2`, `-W name,no-other`), not literally repeatable GCC-style (`-dfoo -dbar`). This is a mechanical consequence of the library, not a design choice, and doesn't change the settled semantics above. **`-d dump-dir=<path>`** (default `.fugue/debug`; prior art's own default was `.pcvc`, changed since this is a fresh project with its own name) sets where `-d dump-tokens`/`-d dump-cst` write their output — as in prior art, dumps go to `<dump-dir>/<input-file-name>-tokens`/`-cst` files, not stdout; `-d dump-dir` without a value is a hard error. **`-d dtiming`** dumps per-pass timing to `<dump-dir>/time.log`, one line per pass per input file — file name plus pass plus elapsed time — appended across passes/files in one run rather than one file per pass, unlike `dump-tokens`/`dump-cst`. **`-d`/`-f`/`-W` names are validated against a hardcoded allowlist** (`knownDebugOptions`/`knownFeatures`/`knownWarnings`, `Fugue.lean`) — an unrecognized name is a hard CLI error, not silently accepted (a misspelled `-d`/`-f`/`-W` option previously landed in `FlagsEnv`'s map unnoticed, since nothing ever looked it up). Extend these three arrays by hand as later phases add dump points/features/warnings — no registration mechanism beyond that, deliberately, since the current set is small enough not to warrant one. |
| Go runtime library location | **Settled: `runtime/go/` in this repo**, versioned alongside the compiler that targets it, not a separate repo (unlike prior art's implicit `github.com/mesabloo/distpcal-compiler/lib`). See §5.7. |
| `Int` representation dispatch: machine `int` vs. `math/big` (Go backend, §5.7/§9.7) | **A compiler flag, target-specific to the Go backend** — not a per-`CONSTANT`/per-declaration type annotation. Resolves §9.21: the flag picks one of the two Go encodings the thesis's second July 2026 revision commits to (default machine `int`, opt-in `math/big`) for the whole compiled output, rather than deciding per-value or per-module. **Exact flag name not yet chosen** — see §9.3's third bullet for the naming detail still open. |
| Name-provenance (which module declared a name) | **Tagged on the AST by the elaborator itself, not reconstructed later as a `Driver/Modules.lean` side table.** Resolves §9.22 (corrected after further review — an earlier pass at this decision proposed a `Driver/Modules.lean`-level `CacheEntry.provenance : Std.HashMap String String`, superseded before implementation started). Both `WellFormedness` (§5.2a, checks 2(c)/3) and `Network2Go` (§5.7, resolving whether a builtin-looking operator like `+`/`Naturals`, §9.19, is the real builtin or a user override) need to know which module declared a referenced name — but the elaborator already resolves every `.var` reference through `Γ`, and already knows at that point whether it's a binder or a top-level declaration and which module the latter came from. `Elaborator/Monad.lean`'s `Binding` gains an `origin : Origin` field (`.binder` / `.module name`), tagged at `Γ`-construction time (`Elaborator/Context.lean`'s `extend`/`extendAll` for binders; `Elaborator/Declarations.lean`'s own-declaration checking and `Driver/Modules.lean`'s imported-`Γ₀` fold for top-level names, both already knowing the relevant module name for free); `TypedTLAPlus.Expression.var` widens to carry that `Origin` so it survives past `Γ` (discarded after checking) into the checked AST, where downstream passes read it directly with no lookup. Only one real `.var`-construction site exists (`Elaborator/Expressions.lean`'s `inferExpr`), so this is a same-lookup tag, not an extra pass — smaller than the table-based design it replaces. A plain `lookupForeign : String → m (Option TypedModule)` (`MonadForeignLookup`, `Driver/Modules.lean`-backed) is still needed, only to fetch a foreign module's declaration list once its name is already known from `origin` — for checks 2(c)/3's "what kind of declaration is this / keep walking its body" half, not for provenance itself. |
| Address visibility / deployment topology | **Accepted limitation, not fixed by this plan.** Distributed PlusCal lets any process know any other process's identity, so generated code can't principally avoid assuming worst-case full connectivity ("star" topology) between processes. A "minimal needed addresses" static analysis was considered but is **not planned work** — it's largely mooted by the nameserver-based addressing already settled for both backends (§5.6, §5.7). See §7's stretch list. |
| Fairness (`isFair`, `fair process`/`fair+`) | **Largely ignored by the compiler** — there's no way to insert fairness into the target languages' runtimes (neither the generated Go's goroutine scheduler nor the Join Calculus's reaction-firing nondeterminism are made fairness-aware by this plan). `isFair` is still carried through the ASTs (parsing → both backends) for round-tripping/documentation purposes, but neither backend's compilation scheme (§5.6, §5.7) does anything with it. The parser emits a **warning** (§5.1) whenever a `fair process` / `fair+` annotation is encountered, telling the user it will be ignored. |
| `CONSTANT` values, and process-set (`p ∈ S`) cardinality | **Left to the user of the compiled code, deliberately.** `CONSTANT`s are genuinely abstract entities (both their type and their value) as far as this compiler is concerned — they only get concretized when someone builds a real executable program out of the generated code, matching the existing "the compiler doesn't emit `main`" scope boundary (§5.7). No `ASSUME`-pinning requirement, no companion config file. Correspondingly, a process set `p ∈ S` does **not** compile to `S`-many spawned goroutines/definitions — each process definition compiles to a **single entry point** (a Go function, a Join Calculus process definition), parameterized over the process's own identity/address; the user is responsible for invoking that entry point once per concrete process they want running, with whatever address they choose. See §5.3, §5.6, §5.7. |
| When imported modules get processed | **Eagerly and transitively, recursively invoking the compiler driver right after desugaring, before type checking.** Every module reachable from the main module's `EXTENDS` list gets fully processed up front, not lazily on first `Ξ` miss: once the main module itself is parsed and desugared (§5.1–§5.2), the driver recurses on each directly `EXTENDS`ed module — parse → desugar → recurse on *its* own imports the same way → type-check — before the main module's own type checker (§5.3) starts. By the time the main module reaches `[Goto]`/`[Assign]`/etc. typing rules, `Ξ` is already fully populated for everything it can reference. (`INSTANCE` is out of scope for now, §2/§9.8.) See §5.3. |
| Well-scopedness: how `GuardedPlusCal.Algorithm.WellScoped` gets established for Guarded→Network | **A general preservation lemma, proved once**, not a per-run decision procedure: `CorePlusCal.WellScoped p → GuardedPlusCal.Algorithm.WellScoped (Typed2Guarded (Elaborator p))` (roughly), proved as part of `Elaborator`/`Typed2Guarded`'s verification work (§5.5, §6.2) and reused unchanged for every program the compiler processes. Per the project owner, this fits the compiler's overall verification aesthetic better than re-deciding the `Prop` computationally on each concrete compiled algorithm. **Note:** `CorePlusCal.WellScoped`, the lemma's antecedent, is not one of the ported files — it doesn't exist in prior art at all and must be authored fresh (§5.2a). See §5.2a, §5.5. |
| Language-subset exclusions for the first type checker (§5.3, Phase 5/6) | **`INSTANCE` and `RECURSIVE` are both out of scope for now.** Neither is in §8's language subset, neither prior-art checkout's parser recognizes them, and both need real, non-trivial design work before they could be checked at all — `INSTANCE`'s parameter-substitution semantics (does substitution happen during desugaring, per instantiation site, or does `Ξ`/the checker track substitution environments directly?) and `RECURSIVE`'s annotation-seeded checking rule (§9.9, preserved there for whenever this is picked up) aren't needed to get a first type checker landed against the language subset §8 already describes. Revisit either if a program actually needs it. See §9.8, §9.9. |
| `Ξ`'s cache: disk persistence and invalidation (§5.3, Phase 5/6) | **In-memory only for now, no disk persistence.** §5.3's original description called for a persistent, disk-backed cache under `~/.local/config/.fugue`, but that immediately raises an invalidation question (§9.11) with no good answer yet — a compiler-side change (bug fix, standard-module-stub update, toolchain bump) can silently invalidate a cached module's typed form without touching that module's own source, and nothing currently detects that. Since the checker itself is still under active development (i.e. exactly the kind of compiler-side change §9.11 worries about, happening constantly), an in-memory `MonadModuleCache` sidesteps the problem entirely for now — nothing persists across runs, so nothing can go stale. Disk persistence, and picking one of §9.11's two invalidation schemes, becomes its own later, explicitly-scoped addition once the checker has stabilized. See §9.11. |
| Pipeline order: well-formedness checking (§5.2a) vs. type checking (§5.3) | **Type checking runs first — inverted from an earlier draft of this plan, which had well-formedness immediately after desugaring.** The project owner's observation: type checking already forces variable well-scopedness as a side effect of succeeding (an out-of-scope or undeclared reference is a `Γ`/`Σ`/`Δ`-lookup failure, i.e. a type error on its own, independent of any dedicated check), so running a separate well-scopedness pre-pass before type checking re-derives a fact type checking would catch anyway. Well-formedness's other two checks (well-labelledness, no-bare-temporal-operators) have no dependency on typing in either direction, so nothing is lost by deferring them. **Consequence, not a further decision:** the well-scopedness sub-check itself doesn't disappear — its "every reference resolves" half becomes redundant defense-in-depth, but its "no shadowing / no duplicate names in a scope" half is not implied by ordinary bidirectional type checking (shadowing still type-checks against *something*) and remains this pass's real, load-bearing job. See §5.2a, §7 (phases 6–7). |
| Polymorphism-instantiation / metavariable resolution mechanics | **Direction-aware solving, not naive eager unification** — since the subtyping axioms here are asymmetric coercions, not an equivalence. Lower-bound constraints (`T <: ?n`) solve eagerly, because coercions only ever run narrow→wide; upper-bound constraints (`?n <: T`) only ever get recorded as pending, never solved from directly, since doing so would foreclose a narrower solution arriving later. Metavariable-vs-metavariable constraints (`?m <: ?n`, both unresolved) must **not** be resolved by merging/unioning the two variables into one — that's unsound in general, since it conflates two independently-constrained unknowns and forces equality where `<:` only ever demanded a directional relationship; instead, record the link on the lower side and propagate once one side resolves from a real ground bound. A metavariable left with no bounds at the end of checking — including one whose only recorded bound is another metavariable that itself never resolved — is a hard type error, not a silent default. Full algorithm, with the counterexamples motivating each rule, in §5.3. |
| Coercion realization: where do coercions live, and how does a *pending* one get resolved? | `Coercion := Expr → Expr` — applied by ordinary function application to the elaborated expression in hand once `subtype` yields a **successful** coercion. When it yields **pending** instead (an upper-bound check against an unresolved `?n`), the expression is wrapped in a new `mvar : MVarId → Expr → Expr` node added to `TypedTLAPlus`/`TypedPlusCal`'s grammar; the checker's context keeps, per unresolved `?n`, its pending upper bounds and the `mvar` sites created alongside them in lockstep (same length, by construction). The moment `?n` resolves, every one of its `mvar` sites is substituted with the now-computable coercion applied to the wrapped expression — this happens as part of the metavariable-resolution algorithm itself, not a separate pass, so `mvar` is fully eliminated before the checker's output reaches `Typed2Guarded`; downstream passes and both backends never see it. See §5.3. |
| `[Receive]`'s channel/reference coercion — where does it live, given there's no expression to apply it to? | **Stored on the `receive` statement node itself, discharged only at `Guarded2Network`.** Unlike `[Send]`'s payload (a real sub-expression `Coercion.apply` can wrap immediately), a received value doesn't exist as an expression at check time — it arrives from the network at runtime. So the checker synthesizes both the channel's element type and the destination reference's type, `subtype`s them directly (independent of `Channel <: Channel`'s own structural check, which stays identity-only — no general term former exists to wrap an opaque channel value, and none is needed), and stores the resulting `Coercion` as a new field on the `TypedPlusCal`/`GuardedPlusCal` `receive` node. `Typed2Guarded` (§5.4) carries it through unapplied (none of its four subpasses touch `receive`'s shape); `Guarded2Network` (§5.5) is the first pass where a `receive` becomes a concrete buffered read with real generated code to splice the coercion into. See §5.3, §5.5, §9.15. |
| Diagnostic/error-model shape | **Per-pass error types, unified by a common rendering interface** — not one shared diagnostic sum type. Warning suppression (`-W`/`-Wno-<name>`, §2) is handled either at the point a warning is emitted or by filtering after the fact, before rendering — either is fine, implementer's call. Per the project owner, this mechanism (per-pass errors, common rendering, some form of warning filtering) is expected to already exist in `Common/Errors.lean` (§4), just not necessarily well-documented — read that file before designing something new rather than assuming a gap that isn't there. It's explicitly fine to later refactor either the error style or the warning/error emission mechanism if either doesn't hold up in practice. **Known bug to watch for when porting:** the project owner has observed a rendering bug somewhere in this diagnostic-printing code where, in some circumstances not yet pinned down, one character in the offending source line gets duplicated in the printed output — worth tracking down and fixing during the port rather than carrying it forward silently. |
| Generated-identifier hygiene | **Resolved by renaming; direction doesn't matter.** Whether a user-chosen name or a compiler-introduced one is the one that gets renamed on collision is irrelevant — the only hard requirement is that **no shadowing is ever introduced in the generated code, checked at every pass, not just the final pretty-printer.** This is the same class of problem as escaping target-language reserved words (a PlusCal variable literally named `type` or `def` colliding with a Go/Join-Calculus keyword), which prior art already partially handles: `Core/Go/Pretty.lean` has a `keywords : Std.HashSet String` table and a `sanitize` function (suffixes a colliding name with `__`) applied at every point an identifier gets printed. **Port and generalize this mechanism** — to cover compiler-introduced internal names (`recv`, `inbox`, lock variables, label atoms, §5.6/§5.7) and the Join Calculus's own reserved surface, not just Go keywords — rather than treating it as a Go-only concern. See §5.2a, §5.6, §5.7. |
| Flags, and `Ξ` (§9.10, now resolved): how do these cross-cutting effects fit the monad-polymorphism convention? | **Unified effect stack, not a driver/pass split.** Every function — pass code and the CLI driver alike — is written against one abstract `{m : Type _ → Type _} [Monad m]`, with every effect (errors, flags, module cache) as a typeclass constraint on that same `m`, rather than confining `IO`-flavored effects to an outer driver layer. Concretely: (1) **Flags are a contextual (Reader) effect, not an opaque action.** A single `getFlag : String → m (Option String)` was tried and rejected — flags aren't uniformly `Option String` (boolean `-f`/`-W` flags vs. valued `-d<name>=<value>` options vs. `-o`/`-t`/`-I`'s own typed values each need their real type, not a stringly-typed lookup every caller re-parses), and separately, this project's proofs run on `Std.Do.WP`, which cannot be instantiated at `IO` at all — an opaque, unconstrained action gives that framework nothing to reason about, whereas Reader is exactly the transparent, structural effect it already handles. So: a concrete, typed `FlagsEnv` structure (covering the full settled flag surface above), populated once by the CLI driver from `Cli.Parsed`, accessed via `MonadReaderOf FlagsEnv m` plus small typed accessor helpers (`getDebugFlag`/`getDebugOption`/`getFeatureFlag`/…) built on `read`, not new typeclasses per flag. `instance : MonadReaderOf FlagsEnv IO` reads from an `IO.Ref` populated once at CLI startup, replacing prior art's ad hoc `DebugOptions.from` + closure-capture pattern. (2) **`Ξ` gets its own effect class**, `MonadModuleCache m` (`lookup`/`store` keyed by source hash), with an `IO` instance backed by an in-memory `IO.Ref` — **disk persistence is deferred** (§2, §9.11: the checker is still under active development, so a persisted cache would need a real invalidation story this project isn't ready to commit to yet; an in-memory cache sidesteps the question entirely rather than answering it, and can simply not survive past one compiler run for now) — a genuine mutable-store effect, unlike flags, but it only shows up in `Elaborator`, which isn't part of §6.2's committed proof surface, so it doesn't hit the `Std.Do.WP`-compatibility question flags did; revisit its shape if `Elaborator` itself ever becomes a proof target. (3) **Consequence for §6.2's Guarded→Network proof, accepted knowingly:** `Guarded2Network.compile` stays generic (`{m} [Monad m] [MonadReaderOf FlagsEnv m] [MonadExceptOf G2NError m]`, same shape as every other pass) rather than being special-cased monomorphic. The refinement theorem is proved against whichever concrete instantiation `Std.Do.WP` actually supports (e.g. `m := Id`, or a `ReaderT FlagsEnv (Except G2NError)` stack) — that instantiation, not the `IO`-run one, is the real proof target. Running the same polymorphic term at `m := IO` for actual CLI execution is a **separate, deliberately unverified step** — same source term, same typeclass contract, believed equivalent by construction but not formally connected to the proof; this gap is to be documented explicitly in `Guarded2Network`'s own module docs once written. (4) **Fresh-name generation gets the same treatment as `Ξ`**, resolved during Phase 4: `MonadFresh m` (`Common/Fresh.lean`), a monotonic counter behind `fresh : m Nat`, first needed by expression desugaring's tuple-pattern/multi-binder-collapse transformations (§5.2) and expected to recur at `Typed2Guarded`'s `𝒞_par` (§5.4). Names are generated as `"<prefix>$<n>"` — `$` cannot appear in a TLA⁺ identifier, so no scope-tracking is needed to prove freshness, unlike a general capture-avoiding-substitution setup. |

---

## 3. Prior art map

Three things exist; none of them is "the codebase to continue," but all three are worth
reading before touching the corresponding area of the new project.

### 3.1 `github.com/mesabloo/fugue` (public mirror)
- `main`: the only branch that actually builds an end-to-end CLI (`pcvc`). Pipeline
  wired in `Main.lean`: parse TLA+ (`SurfaceTLAPlus`/`SurfacePlusCal`) → resolve
  annotations → `SurfacePlusCal.Algorithm.toGuarded` (fused desugar+typecheck+guard,
  *not* split into separate stages) → desugar expressions to `CoreTLAPlus` → `toNetwork
  "inbox"` → `toGoCal` → pretty-print Go. Only the Go backend exists; no type-checking
  pass in the wired-up sense (types are basically untracked past annotations).
  `VerifiedCompiler/` here has a working `Trace` + `StrongRefinement` framework, and
  `GuardedPlusCal`/`NetworkPlusCal` both carry `Semantics/Denotational.lean` +
  `Semantics/Lemmas.lean` — this is the "hand-verified pass" the project owner mentioned.
  `GoCal/Semantics/{Denotational,Denotational2}.lean` are two abandoned attempts at Go's
  semantics (1640 and 1040 lines), both dropped in later branches.
- `develop` / `lock-inference` (same commit): a from-scratch restructuring into the
  module layout this plan adopts (see §4): `Common`, `Core/*`, `Parser_`, `Desugarer`,
  `Checker`, `Typed2Guarded`, `Guarded2Network`, `Network2Go`, package renamed `Fugue`.
  Introduces explicit `CorePlusCal`, `TypedPlusCal`, `TypedTLAPlus`, `TypedSetTheory`
  stages absent from `main`. Many of these are empty stubs or partial — but not
  `Parser_`, which is substantial here too; the local checkout (§3.2) has it further
  along still, and is the one to actually port from.
- `go-semantics`: the newest branch (June 2026), abandoning both old `GoCal` denotational
  semantics attempts in favor of a serious metric-space / domain-theory treatment
  (`Extra/Topology/IMetricSpace*`, Lipschitz maps, uniform continuity, closed
  embeddings — solving a recursive domain equation `P ≅ F(P)` via Banach fixpoint). This
  is real, hard, unfinished research; see §6.4.
- `docs`: CI plumbing for `doc-gen4`, no content of interest.

### 3.2 `~/Documents/distpcal-compiler` (private, more current)
Same project, different/renamed remote, further along in places. Local branch
`typechecker` (uncommitted) has active work on `Checker/Typechecker/*`,
`Core/Go/{Syntax,Pretty}.lean`, and `Core/README.md`. Notable extras not on the public
mirror:
- `Core/CorePlusCal/Syntax.lean`: a genuinely nice piece of design — statements/blocks
  are indexed by a `Bool` tracking whether they're "terminal" (end in `goto`) at the
  *type* level, so "all blocks end in an explicit goto" is a structural invariant, not a
  runtime check. Worth carrying the pattern forward.
- `Parser_/{Annotations,Common,Monad,PlusCal,TLAPlus}.lean` +
  `Parser_/Tokens/{PlusCal,TLAPlus}.lean`: substantial, real code (~2,200 lines total),
  not a stub — despite superseding (and deleting) the older `SurfaceTLAPlus`/
  `SurfacePlusCal` `Syntax.lean`/`Tokens.lean` files that the public `fugue` mirror's
  `main` branch still parses with. It already targets the `Core/SurfaceTLAPlus` and
  `Core/SurfacePlusCal` ASTs present in this same checkout. **This, not `fugue main`'s
  parser, is the source to port from** — it's the more current version of the same
  rewrite (§5.1).
- `lib/{address.go,rand.go,tlaplus.go}`: the actual (partial) Go runtime library imported
  by generated code (`github.com/mesabloo/distpcal-compiler/lib`), including TLA+ value
  encodings (`Seq`, `Set`, functions).
- `tests/{PingPong,TPC,LamportMutex}`: hand-built example algorithms with real generated
  Go and a **hand-written nameserver** (TCP/UDP address registration + lookup,
  `charmbracelet/log` for logging) used to actually run the examples across processes.
  This nameserver is the practical, already-prototyped analogue of the Join Calculus
  chapter's `register`/`lookup` — worth mining for the Go backend's runtime design even
  though the examples themselves aren't being adopted as a formal suite right now.
- `Desugarer/TLAPlus.lean` has real code (`Expression.desugar`, `Declaration.desugar`,
  `Module.desugar`) but is **not complete against the four confirmed transformations
  in §5.2** — check what's actually implemented against that list rather than assuming
  coverage. `Desugarer/PlusCal.lean` is an empty stub — i.e. statement-level desugaring
  (Distributed PlusCal → PlusCal with explicit gotos, feeding the `cflow`/`par`/`flat`/
  `reord` pipeline) has no code anywhere, despite being mathematically specified in the
  thesis. Both halves need real implementation work, not a clean port — see §5.2 for
  what's known to be missing on the expression side.

### 3.3 The thesis (`reference/thesis.pdf`)
Maps onto the pipeline as follows. Chapters marked "stub" contain only section headers in
the current draft — treat their content as *to be designed*, using the surrounding
chapters and prior-art code as the only real guidance.

| Thesis chapter | Pipeline stage | Status in thesis |
|---|---|---|
| 3.1 | Bidirectional type checker | Fully written (§5.3 below reproduces it) |
| 3.2 | Distributed PlusCal → Guarded PlusCal | **Now fully written, including §3.2.2.4 (guard reordering)** — updated as of the July 2026 thesis revision. §5.4 below has been updated to match. |
| 4 | "Compiler verification, denotationally" | Stub (title only) — unchanged |
| 5 | Guarded PlusCal → Network PlusCal | Stub in the thesis — but *implemented and proved* in the `fugue` repo's `main` branch. Read the code, not the thesis, for this pass. Unchanged in the July 2026 revision. |
| 6 | Denotational account of Go | Fully written; heavy domain theory. See §6.4. Unchanged. |
| 7 | Network PlusCal → Go, lock inference | **Filled in further still by a third July 2026 revision (commit `c2bbf8f`, 2026-07-11)**, on top of the second revision's changes. §7.1 (atomicity/lock inference) unchanged, still fully written (§9.20). §7.2 has been renumbered as it's filled in: §7.2.1.1 (Go representations of each TLA+ type, incl. the `Channel(τ)` resolution below) and **§7.2.1.2 (compiling TLA+ *expressions* — booleans/quantifiers, sets, functions) are now both fully written**, and a **new §7.2.2 ("Compiling operator and function definitions")** has been split out and is also fully written (non-recursive vs. parametric operators, recursive functions via a tie-the-knot `MkRecFn`). What was previously called "§7.2.2" (statement-level Network PlusCal → Go compilation) is renumbered **§7.2.3** and remains a stub — one framing paragraph, no content. §7.3 (correctness sketch) is still a stub (header only), same as before. **The `Channel(τ)` open task is now resolved in the thesis itself**: "channels are not first-class citizens in Distributed PlusCal, [so] we do not (need to) represent `Channel(τ)` in the general case" — narrows but doesn't close §9.12 (see there). See §5.7 below for the full digest of the new §7.2.1.2/§7.2.2 content. |
| 8 | Network PlusCal → the Join Calculus | Fully written, including a worked Ping-Pong example. This is the primary spec for the new backend; §5.6 below is a condensed version. Unchanged in the July 2026 revision. |
| 9 | Conclusion | Stub (title only) — unchanged |

---

## 4. Target project layout

Adopting the module structure already converged on in `distpcal-compiler`'s `develop`
branch, with two additions for the Join Calculus backend. Package name `Fugue`,
executable `fugue`.

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
│   ├── TypedTLAPlus/    TypedPlusCal/           type-checked (§5.3)
│   ├── TypedSetTheory/                          output of a separate check *after* §5.3, not of the checker itself (§5.3); Syntax/WellScopedness.lean ported (§5.2a)
│   ├── GuardedPlusCal/                          guards floated to block-start (§5.4); Syntax/WellScopedness.lean ported (§5.2a)
│   ├── NetworkPlusCal/                          explicit inbox, no receive-guards (§5.5)
│   ├── JoinCalculus/                            NEW — guarded-reaction JC dialect (§5.6)
│   └── Go/                                      Go AST + pretty-printer (§5.7)
├── Parser_/                      ported from prior art, refactored/cleaned up — lexer + parser for TLA+ modules / Distributed PlusCal,
│                                    including annotation parsing + placement checking (§5.1)
│                                    (named `Parser_`, not `Parser` — clashes with the `fgdorais/Parser` package import)
├── Desugarer/                    fresh — Surface → Core, for both TLA+ expressions and PlusCal statements
├── Elaborator/                   fresh — bidirectional type checker, Core → Typed
├── Driver/                       fresh — recursive `EXTENDS` resolution: not type-checking rules, the orchestration around invoking them
│                                    (locate/lex/parse/desugar a module, recurse on its own `EXTENDS`, module cache `Ξ`, stdlib operator table)
├── WellFormedness/               fresh — well-labelledness + variable well-scopedness + no-bare-temporal-op checks over Core ASTs, run after the type checker (§5.2a)
├── Typed2Guarded/                fresh — the cflow/par/flat/reord pipeline (§5.4)
├── Guarded2Network/               ported from prior art incl. its proofs (§5.5)
├── Network2JoinCalculus/          NEW (§5.6)
├── Network2Go/                    fresh, incl. LockInference submodule (§5.7)
├── Fugue.lean                     CLI entry point (executable `fugue`)
└── reference/
    └── thesis.pdf                  copied in for implementer reference
```

No separate `reference/NOTES.md` is planned — §3 above already is "pointers to the two
prior-art repos and how to read them," and a second copy of the same content in its own
file would just be one more place to keep in sync. If that changes (e.g. a per-file
reading guide grows too large for §3), add it back here explicitly rather than assuming
it exists.

Each `Core/<Lang>` module owns exactly one AST plus its pretty-printer; semantics
(`Semantics/Denotational.lean`, `Semantics/Lemmas.lean`) are added only for passes that
have (or are actively getting) a refinement proof, to avoid maintaining semantics nobody
is using. `Fugue.Core`, `Fugue.Parser`, `Fugue.Desugarer`, `Fugue.WF`, `Fugue.Elaborator`,
`Fugue.Driver`, `Fugue.T2G`, `Fugue.G2N`, `Fugue.N2JC`, `Fugue.N2Go` are the corresponding
`lean_lib` targets in `lakefile.lean`, mirroring the `distpcal-compiler` naming scheme.

---

## 5. The pipeline, stage by stage

Running example throughout: the thesis's Ping-Pong algorithm (thesis §8.6, and present as
`tests/PingPong/PingPong.tla` in `distpcal-compiler`) — two processes exchanging `"Ping"`
/`"Pong"` messages over per-process mailboxes. It is small enough to hand-trace through
every stage and is used in the thesis to illustrate the one backend that's fully
specified (Join Calculus), which makes it the natural first target for "does the pipeline
work at all" smoke-checking once each stage exists — without that turning into a formal
regression suite (deprioritized per §2).

### 5.1 Lexing & parsing
**Input:** raw TLA+ module source (`.tla`), containing an embedded Distributed PlusCal
algorithm inside a `(* --algorithm ... *)` comment block, plus `@type`/`@mailbox`
annotations in comments (see the Ping-Pong listing in thesis §8.6 for the annotation
style).
**Output:** `SurfaceTLAPlus.Module` wrapping a `SurfacePlusCal.Algorithm`.

**`@rx`, resolved (was previously miswritten into this section as a third source-level
annotation kind):** per the project owner, `@rx` is not a source annotation the parser
ever handles at all — it's purely an internal marker used later, during **pretty-printing
of the Network PlusCal variant** (§5.5's output, consumed by §5.6/§5.7's backends), not
something `Parser_`/`resolveAnnotations` needs to parse or represent. `Annotation`
(`Parser_/Annotations.lean`) correctly has only `@type`/`@mailbox`/`@parameter` — no
`@rx` case — matching prior art exactly; this was the parser being right and this
document's prose being wrong, not a gap to fix in Phase 3. Whoever implements Network
PlusCal pretty-printing (§5.5 onward) should introduce `@rx` there, not retrofit it into
this section's annotation set.

Per §2, this is one of the two passes ported from prior art rather than written fresh —
and specifically ported from the **local** `~/Documents/distpcal-compiler` checkout
(§3.2), not the public `fugue` mirror. That checkout's `Parser_/{Annotations,Common,
Monad,PlusCal,TLAPlus}.lean` + `Parser_/Tokens/{PlusCal,TLAPlus}.lean` (~2,200 lines,
`fgdorais/Parser`-based, with a hand-rolled lexer producing `Located` tokens) is the
current, more-advanced iteration of the same rewrite that `fugue`'s public `develop`/
`go-semantics` branches started and left further behind; it already targets the
`Core/SurfaceTLAPlus`/`Core/SurfacePlusCal` ASTs present in that same local checkout,
which this project's own `Core/SurfaceTLAPlus`/`Core/SurfacePlusCal` should stay close
to. `fugue main`'s older, `SurfaceTLAPlus/Tokens.lean`-based parser is superseded by this
and is at most a secondary reference (e.g. for the handful of gaps §9.2 found — none of
which block starting). §9.2 has the audit findings and the one check (an actual
`lake build`) still outstanding.

Annotations (`@type`, `@mailbox`) are parsed as a distinct pass over comments
(`resolveAnnotations` in prior art) since TLA+'s own grammar has no room for them; this
should stay a separate, explicit step rather than folded into the main parser, both for
error-reporting clarity and because it's genuinely orthogonal (comments vs. grammar).
This pass does two things, not just one: it parses the annotation's own content (e.g.
the type expression inside `@type`), and it checks *placement* — that a given annotation
kind appears only where it's structurally meaningful (e.g. `@mailbox` only immediately
before a `process` declaration, not attached to an arbitrary statement). Both belong in
this pass rather than being deferred to the type checker or elsewhere.

**`fair process` / `fair+` emits a warning, not an error.** Per §2, this compiler doesn't
act on fairness anywhere downstream — neither backend's runtime can be made
fairness-aware — so `isFair` is parsed and carried through the ASTs purely for
round-tripping/documentation, and the parser should emit a warning (ties into the `-W`
flag surface, §2) the moment it sees `fair process` or `fair+`, telling the user the
annotation will be ignored.

**Known ergonomics gap, not a near-term priority:** in prior art, syntax errors inside
annotations are poor, because positions aren't tracked within comments — an annotation
error currently can't point at more than roughly "somewhere in this comment." This is
made worse by annotations that span multiple comments. Fixing it properly means
threading real source positions through comment/annotation parsing, which is a
genuinely fiddly bit of surface area (not a quick fix) — worth doing for usability
eventually, but not blocking the pipeline getting built.

**Real bug found and fixed while scoping Phase 5's annotation-placement prerequisite:**
`Parser_/TLAPlus.lean`'s `Annotations` namespace previously parsed a run of adjacent
comment-tokens by concatenating them into a hand-rolled `Parser.Stream (Stream.OfList
Substring.Raw) Char` instance — meant to let several comments be parsed as one logical
unit while still recovering which original comment a given match fell in. Its
`setPosition` (the file carried its own `FIXME` acknowledging doubt about this) rewound
the `past`/`next` split by *element count* only, without correctly reconstructing a
partially-consumed element's own inner position. Confirmed by hand (`comments.size=2`,
but only 1 result out of the parser): two adjacent, argument-less annotations of the
same kind (e.g. two bare `@parameter`) collapsed into a single parsed result, because
parsing a bare annotation always probes for optional `(...)`/`: ...;` before giving up,
and that failed, boundary-crossing lookahead corrupted the position on the way back.
Every annotation kind with an explicit terminator (`@type: ...;`, `@mailbox(...)`) was
unaffected, since its own parse always ends at a definite delimiter rather than via a
failed lookahead. **Fixed** by dropping the custom multi-element stream entirely:
comments in one run are now concatenated into a single flat `String` up front and
parsed with the same, already-correct `Parser.Stream String.Slice Char` instance
`parseType'` already relies on elsewhere in this file (`Position := String.Pos.Raw`,
`setPosition` just re-slices — no custom bookkeeping to get wrong); a plain,
non-parser-involved lookup over cumulative byte lengths (`commentIndexOf`) maps a
match's flat position back to which original comment it fell in, purely to recover that
comment's own `SourceSpan` for tagging. Verified: the two-`@parameter` case now
correctly yields two results, and both the four external fixtures and the full
`tests/regression/` suite pass unchanged. This is unrelated to §9.13 (`first`/`orElse`
not rolling back monad state on backtrack, blocking a *different*, still-deferred
warning) — that limitation is about the base parser combinators' own backtracking
semantics; this one was a local bug in one hand-rolled stream instance built
specifically for annotation-parsing.

**Second real bug found and fixed:** a `@type` annotation on a module's very first
declaration (no `EXTENDS` clause, no other declaration before it) failed to attach —
its `ann` field resolved to `none` even though the comment was present and well-formed.
Cause: `parseModule'` (`Parser_/TLAPlus.lean`) consumed the module header's closing
`----` with a plain, non-backtracking `lexeme`, whose trailing `ws` unconditionally
drops any immediately-following comment tokens as blank whitespace — discarding them
before `parseExtends`/`parseDeclaration` ever got a chance to run `tryParseAnnotations`
over them. This only bit when the annotation comment directly abutted the header with
nothing between (no `EXTENDS`, no preceding declaration), because in every other case
some earlier production's own comment-skip already consumed the gap harmlessly.
**Fixed** by dropping that unconditional swallow and giving `parseExtends` the same
backtrackable comment-skip `parseConstants`/`parseVariables` already used (`withBacktracking
<| lexeme (pure ()) *> token .extends`) — so if no `EXTENDS` keyword follows, the
comment-skip (and the comments themselves) fully reverts instead of committing.
Regression fixture: `tests/regression/accept_type_annotation_on_first_declaration.tla`.

**Follow-on gap found while writing that fixture, now fixed:** there was no way to
write the literal substring `@type`/`@mailbox`/`@parameter` in a comment without it
being parsed as a real (and, if malformed, hard-erroring) annotation attempt — existing
fixtures' prose mentioning `@type` only worked by accident, relying on an intervening
keyword (`CONSTANTS`, etc.) to swallow the prose comment separately from the real
annotation comment run. Per project owner's decision, `\@` is now an escaped, literal
`@` in comments (`tryParseAnnotations'` in `Parser_/TLAPlus.lean`) — it never starts an
annotation, so prose can write e.g. `` \@type `` to mention the keyword inertly.

### 5.2 Desugaring — done (Phase 4)
**Input:** `SurfaceTLAPlus`/`SurfacePlusCal`. **Output:** `CoreTLAPlus`/`CorePlusCal`.

Both `Core/CoreTLAPlus/Syntax.lean` and `Core/CorePlusCal/Syntax.lean` were **written fresh**
in Phase 4 (per §2/§4, `CoreTLAPlus`/`CorePlusCal` are fresh, not ported) — prior art's own
`Core/CoreTLAPlus/Syntax.lean` predates the confirmed transformation list below and still
carries `prefixCall`/`infixCall`/`postfixCall`, separate `bforall`/`forall` pairs, and an
`@`-referencing case, none of which survive in the actual target shape (only prior art's
`CorePlusCal.Statement`'s `Bool`-indexed terminal encoding was carried forward, per §2/§3.2).

Two independent halves, both implemented:

- **Expression desugaring** (`SurfaceTLAPlus.Expression.desugar`, `Desugarer/TLAPlus.lean`):
  produces `CoreTLAPlus`, a deliberately simple core language for the checker (§5.3) and
  everything downstream to work against, rather than TLA+'s full surface grammar. The four
  confirmed transformations (confirmed with the project owner directly, and cross-checked
  against the thesis's own formal typing rules, §3.1.3 — treat this list as authoritative,
  superseding the shorter gloss in `Core/README.md`):
  - `@`, TLA+'s self-reference inside `EXCEPT`, desugars to the expression being
    `EXCEPT`ed. In `[x EXCEPT ![1, 2, 3] = @ + 3]`, `@` becomes `x[1, 2, 3]`. Implemented via
    prior art's own `Reader`-based approach (`Option (CoreTLAPlus.Expression α)`, `none`
    outside any `EXCEPT` update) — a small, already-solved piece of design worth reusing as-is
    (`CLAUDE.md`).
  - Conjunction/disjunction *lists* (TLA+'s indentation-sensitive `/\`/`\/` lists)
    desugar to the binary infix operators `/\`/`\/`.
  - Prefix, postfix, and infix operator applications desugar to ordinary (prefix-style)
    operator applications: `1 + 2` becomes the application `+(1, 2)`, `TRUE^*` becomes
    `^*(TRUE)`, and likewise for every mixfix operator. **Resolved during implementation
    (the project owner's own simplification, not something this plan anticipated):**
    `CoreTLAPlus.Expression` needs *no* dedicated operator-enum types or value constructors at
    all for this — every builtin operator becomes an ordinary `opCall` whose callee is
    `Expression.var "<canonical-spelling>"` (e.g. `.var "+"`, `.var "\\in"`), reusing the exact
    same constructor as any user-defined name. This is sound (no TLA⁺ identifier can ever be
    spelled like an operator symbol — the lexer's `identifierOrKeyword` and `symbol`
    productions are disjoint) and matches the thesis's own formalization verbatim: "1 + 2 is
    treated as (+) 1 2 … we may assume that `+ : (Int, Int) ⇒ Int` is present in the typing
    context Γ" (§3.1.3) — operators are pre-populated *names* in Γ, not a distinct syntactic
    category. Canonicalizing every alternative spelling (e.g. `<=`/`=<`/`\leq`) to one string
    happens once, in `Desugarer/TLAPlus.lean`'s `{Prefix,Infix,Postfix}Operator.canonicalName`.
  - Every quantifier-like binder (`\A`/`\E`/`\AA`/`\EE`/`CHOOSE`/set-map/set-filter/function
    literals) binds exactly one variable over at most one domain — confirmed not just by
    example but against the thesis's own formal typing rules (Figures 3.1.2/3.1.3/3.1.5/3.1.6),
    every one of which is single-variable; `CoreTLAPlus`'s quantifier constructors have no
    multi-variable or tuple-pattern case to represent at all. Two distinct desugaring shapes
    are needed, confirmed against real usage in `distpcal-compiler/tests/LamportMutex{3,4}.tla`
    (both hit): tuple-pattern binders (`\A ⟨x, y⟩ ∈ S : P`, and `[⟨m,nd⟩ ∈ S ↦ …]`) desugar via
    one fresh variable and substitution (`\A z ∈ S : P[z[1]/x, z[2]/y]`); **multi-variable
    *quantifiers*** (`\A x, y : P`, `\A x, y ∈ S : P`) desugar to **nested** single-variable
    quantification (`\A x : \A y : P` / `\A x ∈ S : \A y ∈ S : P`) since that's a genuine
    logical equivalence — but **multi-binder *function literals/set-maps*** (`[x ∈ A, y ∈ B ↦
    e]`, `{e : x ∈ A, y ∈ B}`) do *not* nest the same way (nesting would build a function of
    functions, not a function over pairs) — they collapse to *one* fresh variable over the
    **Cartesian product** `A × B` instead, confirmed against the thesis's Fig. 3.1.3 function
    rule (single-variable only) and standard TLA⁺ semantics for this exact sugar. Both cases
    reuse the same substitution helper (`CoreTLAPlus.Expression.subst`, `Desugarer/
    TLAPlus.lean`) — a simple, non-capture-avoiding substitution that stops at any binder
    rebinding the target name, sufficient given well-scoped programs never shadow (§5.2a). A
    new shared `MonadFresh`/`freshName` effect (`Common/Fresh.lean`, alongside `FlagsEnv`'s
    `MonadReaderOf`/`Ξ`'s `MonadModuleCache` as a cross-cutting effect class, §2/§9.10)
    generates these fresh names, guaranteed collision-free via a `$` character no TLA⁺
    identifier can contain — expected to recur at `Typed2Guarded`'s `𝒞_par`, §5.4.
- **Statement desugaring** (Distributed PlusCal → PlusCal with explicit gotos,
  `Desugarer/PlusCal.lean`): designed and written from the ground up, as anticipated (prior
  art's own version was an empty stub in every branch). Target shape is `Core/CorePlusCal/
  Syntax.lean`'s type-indexed `Statement α β (terminal : Bool)` encoding (§3.2), carried
  forward from prior art per §2/§3.2 — **with two fixes**, one confirmed necessary by the
  thesis's own account of Network PlusCal, one a correction caught by the project owner after
  an initial wrong design (both documented honestly, not just the final state, in
  `iridescent-enchanting-sparkle-findings.md`'s Phase 4 entry):
  - **`Process.threads` labelling fix** (thesis §8.3, "Each thread of the process is a list of
    labelled atomic blocks"): prior art's `Process.threads : List (Block α β true)` had no way
    to attach a label to each block at all. Fixed to `List (List (String × Block α β true))`
    (outer = parallel `{...}` threads, inner = the thread's own sequence of labelled blocks).
  - **Basic-block extraction, corrected after an initially wrong design.** Real Distributed
    PlusCal allows labels and `goto`s to appear *nested* inside `if`/`while`/`either` bodies —
    only `with` genuinely disallows them (its binding only makes sense within one atomic step,
    so execution can never pause/reschedule mid-`with`). The first implementation wrongly
    rejected any label nested inside `if`/`while`/`either` and any `goto` not in tail position;
    the project owner corrected this with a concrete before/after example (a labelled `print`
    nested inside a `while` body) and clarified that the desugarer's actual job is **basic-block
    extraction**: pull each nested labelled sub-block out to become its own top-level
    `(label, Block)` entry in the thread, and stitch control flow back together with explicit
    `goto`s (the extracted block ends with a `goto` back to whatever continues after it; the
    point it was extracted from becomes a `goto` to the new label). This is now implemented as
    `desugarSegment` in `Desugarer/PlusCal.lean`: it walks a thread's statement list carrying an
    accumulator of already-desugared non-terminal statements, and on hitting a label, or a
    nested construct that itself needs extraction, closes off the current segment as a
    `CorePlusCal.Block ... true` and recurses. Fresh loop-back/continuation labels are
    synthesized via `MonadFresh`/`freshName` (`"loop$n"`/`"cont$n"`) only when there's no
    existing label to reuse (e.g. a `while`'s own label is reused as its loop-back target when
    the loop starts the segment cleanly); this keeps generated output compact instead of
    always minting new names. Dispatch between the "cheap" path (`desugarLabelFreeBlock`,
    statically known to always produce a non-terminal `Block ... false`) and the "expensive"
    extraction-capable path (`desugarSegment`) is decided by `Statement.needsExtraction`/
    `List.needsExtraction`, which must check **both** "does this body contain a label anywhere"
    **and** "does this body's own last statement resolve to a bare `goto`" — checking only the
    first missed the case of an `either`/`if` branch ending in an explicit `goto` with no nested
    label at all, which was a real regression caught by re-running the test fixtures after the
    initial fix. `CorePlusCal.Statement.while`'s constructor was generalized from
    `(cond : β) (B : Block α β false)` to `{b} (cond : β) (B : Block α β b) : Statement α β
    false` to allow the loop body to be genuinely terminal (ending in an explicit loop-back
    `goto`) once extraction can produce that; the `while` statement itself stays non-terminal
    regardless, since falling out of the loop always continues normally.
  - **Retained from the original design, not corrected:** a `goto` immediately followed by
    further *unlabelled* statements is still rejected (`gotoNotInTailPosition`) — that's
    genuinely unreachable dead code, not something to route around (a `goto` immediately
    followed by a *label* is the ordinary "this block ends here" case and is fine). `with`
    still rejects any nested label (`nestedLabel`, now documented as `with`-specific rather
    than a general "no nested labels" rule). The **`goto Done` auto-insertion convention**
    for thread termination is unchanged: if a thread's last label runs out of statements
    without an explicit terminal, `goto Done` is auto-inserted — `"Done"` is a reserved
    sentinel that never needs a matching label definition (standard PlusCal's official
    translator convention; whoever implements well-labelledness, §5.2a, must keep `"Done"`
    exempt from "every `goto` targets a real label").
  - **Two more gaps found by cross-checking the PlusCal manual's §3 label/`goto` placement
    rules directly** (project owner's request, after the corrections above — the manual's
    §3.7 "Labels" is the exhaustive rule list; §5.2a's well-labelledness check is built on
    the same rules, but some of them are precondition-like enough that desugaring itself must
    already guarantee them, not just defer everything to §5.2a). Neither of these was
    previously tested: none of the four fixture files exercise `while` at all (confirmed by
    grepping them), so both gaps were fully latent.
    - **A `while` must always be immediately preceded by a real label — and, corrected after
      an initially wrong fix (see below), this compiler does not invent one if it's missing.**
      The manual states the labeling requirement unconditionally (§3.2.4/§3.7: "A while
      statement must be labeled" — unlike `if`/`either`, which only need a label *after* them,
      and only when they themselves contain something requiring one), independently confirmed
      by the thesis's own `𝒞_cflow` rewrite rule (§5.4 below): its pattern
      `while e {B1}; B2; goto l'` *at label `l`* already assumes the `while` starts the block.
    - **A `while` may never appear inside a `with` body, at any nesting depth, independent of
      `nestedLabel`.** The manual (§3.2.6) lists this as its own, unconditional restriction —
      a `while` is illegal inside `with` even with no label anywhere near it, since `with`'s
      one-atomic-step semantics can never provide the label a `while` always needs. Previously
      unenforced: `Statement.desugarLabelFree` accepted a `while` inside `with`'s body without
      question. Fixed via a threaded `insideWith` flag (propagated through `if`/`either`'s own
      sub-bodies, both legal inside `with`, but checked immediately on seeing a `while` before
      even recursing into its body) and a new `DesugarError.whileInWith`.
  - **Fourth correction, a reversal caught by the project owner while reviewing the generated
    `tests/regression/` fixtures (below):** the *first* fix for "a `while` must always be
    labeled" (just above) auto-synthesized a fresh label (`"loop$N"`) whenever a `while`
    lacked one, mirroring how nested-label extraction already synthesizes `"cont$N"` for
    `if`/`either` continuations. The project owner pointed out this is wrong: real PlusCal's
    *default* translator behavior (no `-label` flag) **rejects** an unlabelled `while` outright
    — auto-insertion is what the *opt-in* `-label` flag does, not the default, and this
    compiler should match the default. The same correction applies symmetrically to
    `if`/`either`'s "must be followed by a label" requirement (§3.2.2/§3.2.3): the `"cont$N"`
    synthesis was *also* wrong for the same reason and is likewise now a hard error. Concretely:
    - `desugarSegment`'s `while` case now throws `DesugarError.whileNotLabelled` (new) whenever
      the current segment already has content, or has no real label to attribute the `while`
      to, instead of minting `"loop$N"`.
    - `desugarContinuation` now throws `DesugarError.notFollowedByLabel` (new) whenever what
      follows a label/`goto`-containing `if`/`either` isn't itself already labelled, instead of
      minting `"cont$N"`.
    - A related, independent bug surfaced during this fix: `List.needsExtraction` treated a
      `while` as "safe, no extraction needed" whenever it was the first element of a *nested*
      `if`/`either` branch's own list — but being first inside a brace-delimited branch was
      never the same thing as being immediately preceded by a real label (that label belongs to
      the *enclosing* `if`, not to the `while` nested inside one of its branches). Fixed by
      making `List.needsExtraction` flag *any* `while` found anywhere in a nested body,
      unconditionally, so `desugarSegment` always gets a chance to check it's properly labelled.
    - The now-unused `MonadFresh`/`Common.Fresh` dependency was removed from this file entirely
      (still needed, unrelated, by `Desugarer/TLAPlus.lean`'s expression desugaring).
    - Verified against all four fixture files (still pass unchanged) plus a larger
      `tests/regression/` suite (13 hand-written `.tla` files, `accept_`/`reject_`-prefixed,
      C-syntax only, checked by `tests/regression/run.sh`) covering: a `while` preceded by
      other statements in the same segment (now correctly *rejected*, not extracted), a
      `while` already labelled at its own enclosing label (accepted, reuses that label as its
      loop-back target), a `while` nested inside `with` (rejected), a `while` as the sole,
      unlabelled content of an `if`-branch (now correctly *rejected*, alongside its properly
      labelled counterpart which is accepted), an `if`/`either` with a nested label but an
      unlabelled continuation (now correctly *rejected*, alongside its properly labelled
      counterpart which is accepted), and the project owner's original nested-labelled-step
      example (unaffected, since every label in it was always user-written). See
      `iridescent-enchanting-sparkle-findings.md`'s Phase 4 entry for the full trail, including
      the reasoning that led to (then away from) auto-synthesis.
  - **Fifth addition, a new restriction identified by the project owner, not a correction of a
    prior mistake: a `with`-bound name can never be the target of a write** — neither a direct
    assignment (`with (x = 3) { x := 9; }`) nor a `receive` whose target it is
    (`with (x = "") { receive(ch, x); }`, which writes the received value into `x` the same way
    `assign` writes into its target) — a `with`-bound name is a local binding to a fixed value
    for the duration of its body, not a process variable with state to update; it was never
    declared in `variables` and has nothing for either construct to overwrite. Implemented per
    the project owner's own suggested design: `WithContext`'s single `insideWith : Bool` field
    became `boundVars : List String`, the list of names currently bound by any enclosing `with`
    (accumulated across nesting — an inner `with` prepends its own names onto whatever the
    outer one(s) already bound, rather than replacing them). "Are we inside a `with` body at
    all?" (needed by the existing `whileInWith` check, §5.2 above) is now simply
    `boundVars.isEmpty`; the new check itself is `boundVars.contains` against each write's
    target name (an `assign`'s LHS `Ref`, or a `receive`'s target `Ref`), throwing a new
    `DesugarError.withBoundVarWritten (pos) (name)` on a hit. Applies transitively — an inner
    `with`'s body writing to an *outer* `with`'s bound name is rejected too, exactly like the
    accumulated-list design implies. **`receive` was initially left unchecked** (the project
    owner's original request and example were specifically about `:=`), flagged here as an open
    question rather than silently extended or silently left out — the project owner then
    confirmed the same restriction applies to `receive` too, so it was added immediately after.
    Verified via four `tests/regression/` fixtures: a direct `assign` hit
    (`reject_assign_to_with_bound.tla`), a nested-`with` hit against the outer binding
    (`reject_assign_to_outer_with_bound.tla`), a `receive` hit
    (`reject_receive_into_with_bound.tla`), and an accept case confirming a `with`-bound name
    may still be freely *read* and that writing to an unrelated variable from within the same
    `with` body is unaffected (`accept_with_assign_other_var.tla`) — all 17 regression fixtures
    (13 prior + these 4) and all four external fixtures still pass unchanged.
  - **Sixth addition: annotations disappear from `CorePlusCal`/`CoreTLAPlus` entirely, leaving
    only their content.** Originally (while scoping Phase 5's annotation-placement
    prerequisite, above) annotation checking was a separate, validate-only pass run after
    statement desugaring, over an still-generic-in-annotation-type `CorePlusCal.Algorithm`.
    Per the project owner, that pass now genuinely *transforms* the AST instead of just
    validating it.

    **Content that fits uniformly into "the declared-type annotation at whatever stage of
    checking it's currently at" stays on the very same `α` `Statement`/`Block`/`Branches`/
    `MulticastFilter` already had — `CorePlusCal.Declarations` shares it too, rather than
    getting its own, separately-evolving type-of-types parameter.** (An earlier attempt gave
    `Declarations` a second parameter `τ`, `Option`-wrapped only in its own fields; the project
    owner corrected this twice — `τ` shouldn't be `Option`-wrapped at the field level any more
    than `with`'s own binder slot is, and it should be *the same variable* as `Statement`'s `α`,
    not a second one. Both together are what let `Process`/`Algorithm` stay ordinary,
    unambiguous two-parameter `Bifunctor`/`Bitraversable` instances — the first attempt's three
    parameters made `bimap`/`bitraverse` unable to infer which two of the three to curry on.)
    Concretely: `Declarations.variables/channels/fifos` entries carry `α` directly (`List
    Annotation` fresh out of statement desugaring, `Option Typ` after the same later, still-
    independent `CorePlusCal.Algorithm.stripEmbeddedTypeAnnotations` pass that already stripped
    `MulticastFilter`'s per-bind annotations and — a new addition, see below — a `with`-bound
    variable's own annotation) — `Declarations` needed **no bespoke early extraction for its
    declared-type content at all**, since it's swept up for free by the exact same
    `Bitraversable` walk. Content that genuinely *can't* fit this uniform shape — `@mailbox`'s
    channel name/index expressions, `@parameter`'s presence-as-a-`Bool` — is instead extracted
    early, as its own concrete field, by bespoke validation fused directly into statement
    desugaring (`Process.desugar`/`Declarations.desugarCheck`, `Desugarer/PlusCal.lean`, rather
    than kept as a second, separately-named "raw, still-generic" `CorePlusCal`-shaped type
    purely to bridge the gap between structural desugaring and this bespoke validation — a real
    fork, resolved by asking: two coexisting shapes, e.g. a `CorePlusCal.Unchecked` namespace or
    a suffixed `CheckedAlgorithm` name, were explicitly rejected in favor of there only ever
    being one `CorePlusCal.Algorithm`, always fully checked): `CorePlusCal.Process.ann : α`
    became a concrete `mailbox : Option (String × List β)` field (from at most one `@mailbox`,
    `extractMailbox`); `Declarations.variables` gained a genuinely separate `isParameter : Bool`
    field (from `@parameter`'s mere *presence*, `Declarations.desugarCheck`) alongside its
    ordinary `α` slot. `CoreTLAPlus.Expression` (TLA⁺ side) needed no structural AST change at
    all for this — it was already `Bifunctor`/`Bitraversable`-generic in its annotation type, so
    `Expression (Option Typ)` (formerly `Expression (List Annotation)`) is just a different
    instantiation of the same type.

    **Second new feature, discovered as a natural consequence of unifying `Declarations`' and
    `Statement`'s `α`: a `with`-bound variable can now carry its own `@type` annotation**
    (`with (* @type: Int; *) x = e { … }`) — previously impossible, since `SurfacePlusCal.
    Statement.with`'s binder tuple had no annotation slot at all. `CorePlusCal`/`SurfacePlusCal
    Statement.with`'s `vars` gained an `α` slot (`String × α × Bool × β`, matching every other
    binder-like site), and `Parser_/PlusCal.lean`'s `parseWith` now calls `tryParseAnnotations`
    per binder. **A real parser bug found while testing this, same class as the one `parseFilter`
    (multicast) already works around:** wrapping the whole binder list in `parens` swallows the
    *first* binder's own annotation, since `parens`'s `lexeme (token (.tla .lparen))` treats a
    comment sitting immediately after `(` as ordinary trailing whitespace to skip, before that
    binder's own `tryParseAnnotations` call ever runs — confirmed via `-d dump-cst`
    (`("x", [], …)`, empty, for the first binder; a *second* binder, after a `;`/`,`, correctly
    captured `[("type", …)]`). **Fixed** by not using `parens` at all — a bare `token (.tla
    .lparen)` (no `lexeme`), exactly `parseFilter`'s own established workaround for the identical
    problem.

    **A genuine, previously-latent gap found and fixed along the way:** `@mailbox`'s filter
    arguments (`var[e₁, …, eₙ]`) were never actually desugared to `CoreTLAPlus.Expression` at
    all before this — `Module.desugar`'s own traversal (`Desugarer/TLAPlus.lean`) treats every
    annotation as opaque, untouched payload (`f = pure` over the annotation type), so these
    arguments stayed raw `SurfaceTLAPlus.Expression` values forever, and the pre-fusion
    `checkMailboxOnly` never even looked at them (compared only the channel name, since
    `SurfaceTLAPlus.Expression` has no `BEq`). This was invisible before because nothing
    downstream ever consumed a mailbox's filter arguments at all; it became a hard type error
    the moment `CorePlusCal.Process` gained a real `mailbox : Option (String × List β)` field
    those arguments have to actually inhabit. Fixed by running `SurfaceTLAPlus.Expression.
    desugar` over them directly inside `Process.desugar`, through a throwaway local instantiation
    of the same `ReaderT (Option (CoreTLAPlus.Expression α)) (StateT Nat (Except DesugarError))`
    stack `SurfaceTLAPlus.Module.runDesugarer` already uses at the top level (`desugarMailboxArg`).

    Verified: full `lake build` clean, and `-d dump-desugared` on fixtures covering a `@mailbox`,
    a `@type`/`@parameter`-annotated variable, and a `with`-binder `@type` annotation (including
    one sitting immediately after `with`'s opening `(`) all show genuinely concrete content —
    `mailbox := some ("ch", [])`, `fifos := [("ch", some (Typ.channel (Typ.str)), [])]`,
    `variables := [("x", some (Typ.str), true, some (false, …))]`,
    `Statement.with "x" (some (Typ.int)) false … …` — no `Annotation`/`CommentAnnotation`
    value anywhere in a `CorePlusCal` value any more. All 26 `tests/regression/` fixtures (25
    prior + 1 new, `accept_with_binder_type_annotation.tla`) and all four external fixtures
    still pass.
  - **Seventh addition: a multi-binder `with` desugars to a chain of single-binder `with`s.**
    `with (x = e1, y ∈ e2, …) { B }` (a genuine comma list at the surface syntax level,
    unchanged in `SurfacePlusCal.Statement.with`) now desugars to `with (x = e1) { with (y ∈
    e2) { … B } }` — per the project owner, since real PlusCal's own `with` binds exactly one
    variable at a time and every downstream backend should be able to rely on that directly
    rather than re-deriving it from a list. `CorePlusCal.Statement.with` changed from `(vars :
    List (String × α × Bool × β))` to five separate fields (`var : String`, `ann : α`, `«=|∈» :
    Bool`, `val : β`, plus the body `Block`) — this project's convention of encoding a
    structural invariant at the type level rather than a runtime check or a comment (`CLAUDE.md`,
    `Core/CorePlusCal/Syntax.lean`'s `Bool`-indexed terminal/non-terminal split is the
    precedent) — one binder per `with`, full stop, no `List` to be non-empty or singleton by
    convention. `Desugarer/PlusCal.lean`'s new `buildWithChain` (mirroring the existing
    `buildBranches`'s "fold a list into a right-nested chain" shape) does the flattening: the
    innermost binder wraps the already-desugared original body directly; every binder before it
    wraps the next link in the chain inside a label-free `Block` of its own (`⟨[], ·⟩`, no
    leading statements) — `Statement.desugarLabelFree`'s `.with` case calls it in place of the
    old direct `.with vars` construction, with the `WithContext` reader's bound-name tracking
    unchanged (still extends with *every* binder's name for the *whole* original body in one
    step, since the write-rejection rule doesn't care how the final AST groups the bindings).
    Verified: `-d dump-desugared` on a fixture with three binders (`x = 3, y ∈ {1,2}, z = 5`)
    shows the exact nested shape; new regression fixture
    `accept_multi_binder_with_desugars_to_chain.tla`; all 27 `tests/regression/` fixtures (26
    prior + this one) pass.
  - **Eighth addition: every function call/`EXCEPT` index is unary.** `CoreTLAPlus.Expression.
    fnCall`/`.except` changed from `Expression α → List (Expression α) → …`/an `.inr`-case
    carrying `List (Expression α)` to a single `Expression α` each — a surface multi-index call
    `f[e₁, …, eₙ]` (`n > 1`, same for an `EXCEPT` path step `![e₁, …, eₙ]`) desugars to the
    tuple-application `f[<<e₁, …, eₙ>>]`; a single-index call `f[e]` (`n = 1`) stays exactly
    that — **never** `f[<<e>>]`, per the project owner's explicit correction (an earlier version
    of this change wrapped every call, single-index included). `SurfaceTLAPlus.Expression.
    fnCall`/`.except` are unchanged (still `List`, matching the genuine surface-syntax comma
    list) — the collapse happens entirely in `Desugarer/TLAPlus.lean`'s `Expression.desugar`, via
    a new `wrapIndices : List (Expression α) → Expression α` helper (`[e] => e`, `es => .tuple
    es`) alongside the pre-existing `tupleProj`. Verified:
    `-d dump-desugared` shows `f[1]` unchanged and `f[1, 2]` becoming `fnCall (var "f") (tuple
    [nat "1", nat "2"])`, same for both `EXCEPT` forms; new regression fixture
    `accept_multi_index_function_call_desugars_to_tuple.tla`; all 28 `tests/regression/`
    fixtures (27 prior + this one) pass.
  - **Ninth addition: `SurfacePlusCal`/`CorePlusCal.Ref` (a PlusCal assignment target,
    `f[e₁, …, eₙ] := v`) gets the same unary treatment — corrects the previous bullet's
    "untouched by this change," per the project owner.** `SurfaceTLAPlus.Expression.fnCall`/
    `.except` and `SurfacePlusCal.Ref` were never actually the same representation — `Ref.args :
    List (List β)` (one entry per *bracket group*, `x[i][j]` vs. `x[i, j]`), not `List β` — but
    the same "always unary, `n > 1` wraps in a tuple" rule applies per bracket group: `f[e₁, …,
    eₙ] := v` (`n > 1`, one group) desugars to `f[<<e₁, …, eₙ>>] := v`; `f[e₁][e₂] := v` (two
    separate groups) is unaffected either way, each group still single-index; `f[e] := v` stays
    exactly that. Unlike `fnCall`/`.except`, `Ref` was previously *shared verbatim* between
    `SurfacePlusCal` and `CorePlusCal` (`open SurfacePlusCal (Ref …)`, no separate `CorePlusCal`
    version at all) — introduced a genuine `CorePlusCal.Ref (β : Type)` (`args : List β`, unary
    per group) distinct from `SurfacePlusCal.Ref (β : Type)` (`args : List (List β)`, unchanged,
    matching real surface syntax), with its own `Functor`/`Traversable` instance (so `Statement`'s
    existing generic `bimap`/`bitraverse` code over `Ref β` fields keeps working unchanged,
    now resolving to the new instance). `CorePlusCal.Statement.assign`/`.receive`/`.send`
    reference `CorePlusCal.Ref` (previously `SurfacePlusCal.Ref`, since it was the only one).
    The actual conversion (`SurfacePlusCal.Ref → CorePlusCal.Ref`, `Desugarer/PlusCal.lean`'s new
    `Ref.desugarRef`, reusing `SurfaceTLAPlus.wrapIndices` — made non-`private` for this) happens
    inline in `Statement.desugarLabelFree`'s `.assign`/`.receive`/`.send` cases, which — since
    `wrapIndices` is only meaningful once `β` is concretely `CoreTLAPlus.Expression` — required
    fixing `β` concretely (a new `private abbrev CoreExpr`) throughout the whole goto-
    explicitization chain that constructs or passes through these cases (`Statement.
    desugarLabelFree`/`desugarLabelFreeBlock`/`Branches.desugarLabelFree`/`desugarSegment`/
    `Thread.desugar`), mirroring how `Process.desugar`/`Algorithm.desugar` were already fixed —
    these functions were never actually called at any other `β` in practice, so this drops
    unused genericity rather than losing any. Verified: `-d dump-desugared` on a fixture with
    `f[1] := 0`, `f[1, 2] := 9`, `f[1][2] := 3` (each its own labelled step) shows exactly
    `args := [nat 1]`, `args := [tuple [nat 1, nat 2]]`, `args := [nat 1, nat 2]` respectively;
    new regression fixture `accept_multi_index_ref_desugars_to_tuple.tla`; all 36
    `tests/regression/` fixtures (35 prior + this one) pass.

### 5.2a Well-formedness checking (NEW)
**Input/output:** `CoreTLAPlus`/`CorePlusCal` — this is a checking pass, not a
transform: it either accepts the term or rejects it with a diagnostic, and produces no
new AST. Runs after type checking (§5.3), not immediately after desugaring (§5.2) as an
earlier draft of this plan had it — **reordered on the project owner's observation that
type checking already forces variable well-scopedness as a side effect of succeeding**
(a reference to an undeclared or out-of-scope name is a `Γ`-lookup failure, i.e. a type
error, regardless of whether anything upstream checked for it), so gating type checking on
a separate pre-pass that re-derives the same fact is redundant work with no payoff. The
other two checks here (well-labelledness, no-bare-temporal-operators) have no dependency on
typing either way — they're checked on `CoreTLAPlus`/`CorePlusCal` structure that typing
doesn't touch — so nothing is lost by running them after the type checker instead of
before it; see the well-scopedness bullet below for exactly which part of that check
genuinely becomes redundant and which part doesn't.

Per the project owner, this concern is "a combination of syntactical and typing
assumptions, but mostly syntactical," should **not be dropped** (only cleaned up), and in
practice should be *discharged* as an early syntactic check right after parsing/
desugaring, rather than carried deep into the pipeline as an unproven assumption. All
three checks below are purely syntactic at this point — no typing is needed, since
declarations, gotos, and operator shapes are all already resolved by the time
`CorePlusCal`/`CoreTLAPlus` exist:

- **Well-labelledness**, grounded directly in the PlusCal manual's own placement rules
  (`https://lamport.azurewebsites.net/tla/p-manual.pdf`, §3.2's statement-by-statement rules
  and §3.7's exhaustive list — the project owner's explicit source for this pass, cross-
  checked directly against the implementation rather than re-derived from memory or prose
  summaries; the same cross-check is what caught the two `while`-placement gaps fixed in
  §5.2 above). Every restriction the manual states is part of what "well-labelled" *means*
  here, but they don't all need a *fresh* check in this pass — some are already impossible
  to violate by the time a term reaches `CorePlusCal`, for two different reasons worth
  telling apart (a genuine type-level guarantee is stronger than "the one producer we have
  happens to respect it"):
  - **Guaranteed by `CorePlusCal`'s type itself, for any term of that type regardless of
    what constructed it:** every thread starts with a label and every block ends in exactly
    one terminal statement (`Process.threads : List (List (String × Block α β true))`'s own
    shape, §3.2/§8.3 — `Statement α β true` has no constructor except `goto`, so a `goto` can
    only ever be a `Block`'s own `end`, never mid-list); "an `if`/`either` that contains a
    labelled statement or `goto` anywhere within it must be followed by a label" (§3.2.2/
    §3.2.3) — `CorePlusCal.Statement.if`/`.either`'s `Bool` index forces *both* branches to
    share one terminality, so if extraction made either branch terminal (ends in `goto`), the
    whole `if`/`either` is itself `Statement α β true` and can therefore *only* be a block's
    own terminal `end` — meaning whatever follows it, by the same argument as above, has no
    choice but to start a fresh labelled block.
  - **Guaranteed today because `Desugarer/PlusCal.lean` (§5.2) is the *only* producer of
    `CorePlusCal` terms in this pipeline and now correctly enforces it — not encoded in the
    type, so a latent risk if that ever stops being true (e.g. a second frontend, or
    hand-built `CorePlusCal` test fixtures) rather than a structural impossibility:** "a
    `while` statement must be labeled," i.e. must be the first statement of whatever `Block`
    contains it (§3.2.4/§3.7 — `CorePlusCal.Statement.while` carries no such restriction in
    its own type, unlike `if`/`either` above; enforced by the desugarer *throwing*
    `whileNotLabelled` rather than auto-inserting a label, per the fourth correction in §5.2);
    "`with`'s body cannot contain a labelled statement, a `goto`, or a `while`" (§3.2.6 —
    likewise enforced by the desugarer *throwing* `nestedLabel`/`whileInWith` rather than by
    anything `CorePlusCal.Statement.with`'s type itself rules out).
  - **Not guaranteed by anything upstream — this pass's actual, new work:**
    - *Every `goto` targets a label that actually exists* in the enclosing process/thread (or
      is the reserved `"Done"` sentinel). §5.3's `[Goto]` rule deliberately performs no check
      of its own (correctly — this isn't a typing concern, and a `String` label name is just
      data, not an index into "labels that exist," so nothing about `CorePlusCal`'s type can
      possibly guarantee this), on the assumption that something upstream does; this pass is
      that something.
    - *No two assignments to the same variable within one atomic step, on the same control
      path* (§3.2.1/§3.7) — walk each labelled block's statements, treating an `if`/`either`'s
      separate branches as separate control paths (two *different* branches assigning to the
      same variable is fine; the same branch doing so, or one branch and whatever both
      branches converge to afterward, is not). Not previously listed in this plan at all;
      added from the same manual cross-check that caught the `while` fixes above.

      **Implemented ahead of this pass's own Phase 7 slot, per the project owner** (`Desugarer/
      PlusCal.lean`'s `CorePlusCal.{Statement,Block,Branches}.checkAssignConflicts`, mutually
      recursive over the same three types, run from `SurfacePlusCal.Algorithm.runDesugarer`
      right after goto-explicitization, before `stripEmbeddedTypeAnnotations`) — matching how
      the sibling `with`-bound-write-rejection check (§5.2 above) was already added ad hoc
      during statement-desugaring rather than deferred to `WellFormedness/`. Tracks only
      *bare* variable writes (`Ref.args` empty) from `assign` (every entry of a `||`-list) and
      `receive`'s — **both** `Ref`s, the channel `c` as well as the target `x`
      (`receive(x, a); receive(x, b)` errors, same as re-assigning/re-receiving into `x`
      itself — added per the project owner after the initial pass only tracked the target);
      **explicitly does not track indexed writes at all** (`x[0] := …`
      never conflicts with anything, per the project owner — deciding whether two indexed
      writes actually conflict needs to compare the indices, out of scope for this purely
      syntactic pass). `if`/`either` branches are checked independently (starting from the same
      already-seen set) but their writes are unioned into what continues past them, so a write
      in either branch still conflicts with one afterward in the same block; `while`/`with`
      bodies don't fork execution, so they're checked sequentially, merged with everything
      around them. New `DesugarError.conflictingAssignment (pos) (name)`.

      **A second real, previously-latent parser bug found while testing this against the
      project owner's own `x := 3 || x := 4` example:** it silently parsed as one assignment
      with a garbled right-hand side (`(3 || x) := 4`-shaped) instead of two `||`-separated
      clauses — `.barbar` (`Parser_/Tokens/PlusCal.lean`'s own token for `||`, "the multi-
      assignment separator") was declared and referenced by `parseAssign`'s `sepNoEndBy1 (token
      .barbar)`, but **nothing ever actually lexed it** — `SurfacePlusCal.Lexer.symbol` (the
      PlusCal-specific lexer, tried before falling through to the general TLA⁺ lexer) had no
      rule producing it, so `||` always fell through to TLA⁺'s own generic infix-operator
      token instead, and `parseExpression` (parsing the first clause's right-hand side) happily
      consumed `3 || x` as one ordinary TLA⁺ expression before `sepNoEndBy1` ever got a chance
      to split on a `.barbar` that was never going to appear. Multi-assignment via `||`
      essentially never worked at all, for any input, until this fix — not something introduced
      this session. **Fixed** by adding `.barbar <$ chars "||"` to `symbol`, which — since
      `SurfacePlusCal.Lexer.lexToken` already tries `located symbol` *before*
      `patchTLALexer lexTLAToken` — now wins over the TLA⁺ lexer's own `||` unconditionally
      within a PlusCal algorithm block (matching how PlusCal already reserves several
      TLA⁺-lexed identifier keywords, e.g. `if`/`while`, exclusively for its own use there).

      Verified: full `lake build` clean; all five of the project owner's own worked examples
      (`x := 3 || x := 4` rejected; `x := 3; y := 4` accepted; `x := 4; x := 0` rejected;
      `x[0] := 1; x[0] := 5` accepted; `x := 3; receive(c, x)` rejected) match exactly, plus two
      more covering `if`-branch exclusivity (two different branches writing the same variable
      accepted; one branch writing, then code after the `if` writing again, rejected), plus one
      more (added with the channel-argument extension) covering `receive(x, a); receive(x, b)`
      (same channel twice, rejected). New regression fixtures:
      `reject_parallel_assign_same_variable.tla`,
      `accept_assign_different_variables.tla`, `reject_sequential_assign_same_variable.tla`,
      `accept_repeated_indexed_assign.tla`, `reject_assign_then_receive_same_variable.tla`,
      `accept_if_branches_same_variable.tla`, `reject_if_branch_then_after_same_variable.tla`,
      `reject_receive_same_channel_twice.tla` — all 37 `tests/regression/` fixtures (28 prior +
      these 8, oldest-to-newest across both rounds) pass.
    - *The reserved label `"Done"` is never redefined as an actual, user-written label*
      (§3.7) — `"Error"`'s equivalent restriction doesn't apply here (no procedures exist in
      this language subset, §3.4/§8, so there's no implicit `Error` label to collide with).
  - **Optional, defense-in-depth:** re-verifying the "guaranteed by the desugarer" bullet
    directly on `CorePlusCal` (rather than trusting `Desugarer/PlusCal.lean` unconditionally,
    given it's *not* type-enforced) isn't required for this pipeline as it stands — but is
    cheap to add here if that assurance is wanted regardless; revisit if `CorePlusCal` terms
    ever start being producible some other way.
- **Variable well-scopedness.** Every variable reference resolves to a declared name of
  the right kind (global, channel, process-local, or block-local `with`/`let` binding —
  matching prior art's Σ/Δ/Γ/Ξ scope classes), every `with`/`let` binder is fresh in its
  scope, and there are no duplicate names within a scope. **Now that this pass runs after
  type checking (§5.3), the first half of that ("every reference resolves to a declared
  name of the right kind") is redundant with type checking's own success** — the type
  checker's `Γ`/`Σ`/`Δ` lookups already fail closed on any unresolvable reference, so a
  program that reached this pass already has that property and re-deriving it here is a
  no-op check kept mainly for documentation/defense-in-depth, not load-bearing. **The
  second half — every binder fresh, no duplicate names in one scope — is *not* implied by
  type checking and stays this pass's genuine, load-bearing work:** ordinary bidirectional
  type checking has no reason to reject shadowing (a shadowed name still resolves to
  *something* and still type-checks against it), so this pass is still where shadowing
  and duplicate declarations actually get caught, regardless of where it sits in the
  pipeline. This is exactly what the
  prototype's `Core/GuardedPlusCal/Syntax/WellScopedness.lean` and
  `Core/TypedSetTheory/Syntax/WellScopedness.lean` encode as Lean `Prop`s (Finset-based
  scopes, one predicate per scope class, threaded through `await`/`with`/`receive`/
  `send`/assignment). **Correcting an earlier draft of this plan:** there is no
  `Core/CoreTLAPlus/Syntax/WellScopedness.lean` in the local `distpcal-compiler`
  checkout — confirmed absent both on disk and in its git history; only the two files
  above exist there, and only at already-elaborated stages (`GuardedPlusCal`, after
  `Typed2Guarded`; `TypedSetTheory`, after the pass described in §5.3), not at
  `CoreTLAPlus`. **Port both files** (with cleanup) as the third ported-not-fresh
  exception alongside the lexer/parser and Guarded→Network (§2) — but repurpose them:
  rather than being the primary mechanism that rejects malformed programs (this new pass
  does that, on `CorePlusCal`, well before either `GuardedPlusCal` or `TypedSetTheory`
  exist), they become the formal restatement of the same invariant at those later stages.
  In particular, `GuardedPlusCal.Algorithm.WellScoped` is the natural standing hypothesis
  for the Guarded→Network refinement proof (§5.5) to assume, established via a **general
  preservation lemma** (§2, §5.5) — well-scopedness on `CorePlusCal`, as established
  here, implies `GuardedPlusCal.Algorithm.WellScoped` after `Elaborator`/`Typed2Guarded`
  run — proved once as part of this project's verification work, rather than re-decided
  per compiled program. This "no duplicate names /
  every binder fresh" discipline is also, per §2, exactly the freshness/hygiene property
  the compiler must maintain at *every* pass, not just here — the ported
  `Statement.FreshIn`/`AtomicBranch.FreshIn`/`Process.FreshIn` predicates (alongside
  `WellScopedness.lean` itself) are prior art's version of that same check and are worth
  porting together with it, as the frontend half of the general renaming/hygiene
  mechanism (§5.6, §5.7 have the backend half).
- **`CorePlusCal.WellScoped` itself is *not* one of the two ported files, and has to be
  authored fresh.** The preservation lemma (§2) is literally stated as
  `CorePlusCal.WellScoped p → GuardedPlusCal.Algorithm.WellScoped (Typed2Guarded
  (Elaborator p))` — its antecedent is a `CorePlusCal`-level well-scopedness `Prop`, and no
  such file exists in prior art at any stage (only the two already-elaborated
  `GuardedPlusCal`/`TypedSetTheory` versions exist, per the correction above). This
  pass's actual, executable well-scopedness check (this bullet) is the *runtime*
  half of the story; `CorePlusCal.WellScoped` is the *Prop* half that the preservation
  lemma's statement needs to even type-check — design it new, closely modeled on the two
  ported files' shape (Finset-based scope classes, the same `with`/`let` freshness
  discipline), but adapted to `CorePlusCal`'s own (pre-`Elaborator`, pre-`Typed2Guarded`)
  structure rather than copied from either.
- **No bare temporal or action operators inside PlusCal-statement expressions.** None of
  `[]`/`<>`/`ENABLED`/`UNCHANGED` (prefix) or `'`/`^+`/`^*`/`^#` (postfix) may appear
  inside any expression embedded directly in a PlusCal statement (`assign`, `await`,
  `print`, `assert`, guard expressions, …) — Distributed PlusCal's own statement-level
  expressions have no business using temporal/action syntax, even though the surrounding
  TLA+ module may, elsewhere.

  **Updated once this pass was actually implemented** (`WellFormedness/Restrictions.lean`,
  task 8 of `.claude/plans/jolly-chasing-book.md`): the paragraph above described the
  *original*, narrower scope of this check — direct-only, deferring the transitive case (an
  operator the algorithm calls, whose own body is where the temporal/action content actually
  lives) to §5.3's later `TypedTLAPlus → TypedSetTheory` pass. **That's no longer the
  split.** The project owner asked for the transitive walk to land *here* instead, motivated
  by the same no-shared-memory concern driving §5.2a's other two checks (2(c)/2(d)): an
  operator called from the algorithm shouldn't be able to leak temporal/action content (or a
  global `VARIABLE` reference, or a channel value) into the algorithm any more than writing
  it directly would. Consequently:
  - **Phase 8's `TypedSetTheory` pass, whenever built, should treat "every expression
    reachable from the algorithm is already free of temporal/action operators" as an
    already-established invariant**, not something it needs to re-derive by walking the same
    call graph again — matching how well-scopedness's "resolves to a declared name" half is
    already documented elsewhere in this plan as redundant post-reorder, for the same
    underlying reason (a fact this earlier pass already guarantees).
  - **Phase 8 will still need its own unbounded-quantifier handling** for content it
    processes that this pass's own scope doesn't reach: this pass's unbounded-quantifier ban
    (`WellFormednessError.unboundedQuantifier`, new relative to this section's original
    text — not in the thesis, added per the project owner's own no-shared-memory reasoning)
    is scoped identically to the temporal/action ban, i.e. only to what's reachable
    *from the algorithm*; anything Phase 8 processes outside that reach (e.g. ordinary TLA⁺
    operators the algorithm never calls, if `TypedSetTheory` ever covers those too) isn't
    this pass's concern and needs its own check if Phase 8 wants the same restriction there.
    This was flagged as a TODO in the implementing plan file and needed to land here, in
    `PLAN.md` itself, per `CLAUDE.md`'s plan-sync rule — done.

### 5.3 Type checking
**Input:** `CoreTLAPlus`/`CorePlusCal`. **Output:** `TypedTLAPlus`/`TypedPlusCal`.

`TypedSetTheory` (`TypedTLAPlus` minus temporal operators and actions) is *not* an
output of this pass, despite the layout in §4 sitting it next to
`TypedTLAPlus`/`TypedPlusCal` — it's a separate, subsequent pass: given the already
type-checked algorithm, translate every expression actually used within the PlusCal
algorithm (and every operator defined earlier in the module that those expressions
depend on) into `TypedSetTheory` by removing all actions and temporal formulas (the
prefix `[]`/`<>`/`ENABLED`/`UNCHANGED` and postfix `'`/`^+`/`^*`/`^#` operators, per the
`TypedTLAPlus` grammar), which doubles as the check that none of those constructs were
there illegitimately in the first place — Distributed PlusCal's own expressions have no
business using temporal operators or actions even though the surrounding TLA+ module
they're embedded in may elsewhere. Design this as its own small pass downstream of the
type checker (§7 phases it separately), not as a second thing the checker itself
produces. Its output is also where the ported `Core/TypedSetTheory/Syntax/
WellScopedness.lean` (§5.2a) applies — the same variable-scoping discipline
`GuardedPlusCal` gets, restated over `TypedSetTheory`'s (typed) expressions.

Fully specified in thesis §3.1 — implement the rules essentially as written, with one
deliberate deviation from the literal presentation (polymorphism instantiation, see
below):

- **Type grammar** (Apalache "Type System 1", extended): `Bool | Int | Str | τ→τ | Set(τ)
  | Seq(τ) | ⟨τ,...⟩ | (τ,...)⇒τ | Const | a | [x:τ,...]`, plus three implementation-level
  extensions beyond the thesis's grammar: two Distributed-PlusCal-specific additions,
  `Address` and `Channel(τ)` (channels are deliberately *not* just `Seq(τ)` at the type
  level, even though that's their encoding, so that channel operations can be restricted
  to `send`/`receive`/`multicast` and kept out of arbitrary expressions — `Channel` is
  covariant: `τ <: τ' ⟹ Channel(τ) <: Channel(τ')`), and metavariables `?n` (`n` a
  natural number, distinct from the rigid, universally-quantified `a`) — the mutable
  placeholders that polymorphism instantiation (below) resolves during checking, and
  that should never appear in a fully-elaborated `TypedTLAPlus` term.
- **`<:` is a genuine partial order here, not just a preorder** — the type grammar's
  structural rules (SEQ, SET, FUNCTION, TUPLE, RECORD, OPERATOR) can't create cycles on
  their own, and the three non-structural coercions (`Str <: Seq(Int)`, `Seq(τ) <: Int →
  τ`, and `⟨τ,...⟩ <: Seq(τ)` for a uniform tuple — one whose components are all `τ`)
  are one-directional between syntactically distinct constructors, so there's no way
  to derive both `τ <: τ'` and `τ' <: τ` for distinct `τ`, `τ'`. There is **no `⊤`/`⊥`**
  in this grammar, though (no universal super-/sub-type), so it isn't a full lattice —
  `lub`/`glb` are both still well-defined by `<:` in the standard way, but as *partial*
  functions (e.g. `lub(Bool, Int)` simply doesn't exist). Polymorphism instantiation
  (below) needs exactly this partial `lub`, not a full lattice.
- **Discipline:** bidirectional (checking `Γ ⊢ e ⇐ τ` / synthesis `Γ ⊢ e ⇒ τ`), rank-1
  polymorphism only (type variables collected into a prenex `∀`, no first-class schemes).
  Annotations required only at binders the algorithm can't otherwise pin down (thesis
  §3.1.1). **`RECURSIVE` operator declarations are out of scope for this pass** (§2,
  §9.9) — not in §8's language subset, not parsed by either prior-art checkout; the
  annotation-seeded design for whenever this is picked up is preserved in §9.9.
- **Polymorphism instantiation — do not implement the thesis's `Specialize` rule as
  written.** Instead, per the existing local `Checker/Typechecker/` code
  (`Convertibility.lean`, `Rules.lean`, etc. — read it before implementing this part):
  generate one fresh metavariable `?n` per bound type variable when a polymorphic
  operator is used, and resolve those metavariables incrementally as subtyping checks
  run against them, finishing with whatever resolution remains outstanding at the very
  end of the type-checking algorithm (there is exactly one defaulting point, precisely
  *because* the type system has no let-generalization — rank-1 polymorphism only, per
  "Discipline" above — unlike ML-style systems where generalization can happen at every
  `let`). Concretely, this means **direction-aware solving**, not naive eager
  unification, because the subtyping axioms here are asymmetric coercions (e.g.
  `Str <: Seq(Int)`, `Seq(τ) <: Int → τ`), not an equivalence — solving a metavariable
  eagerly from the wrong direction is unsound:
  - A metavariable `?n` is tracked as either **unresolved** (with a set of pending upper
    bounds accumulated so far) or **resolved** to a concrete monotype.
  - **Lower-bound constraint `T <: ?n`** (`?n` is asked to be *at least* `T`): if `?n` is
    unresolved, solve `?n := T` immediately (coercion at this site is `id` — `T` becomes
    `?n`'s value), first checking `T` against any pending upper bounds already recorded
    on `?n` (recursively, via the same judgment). If `?n` is already resolved to `S`,
    require `T <: S` (recursively) instead — `S` must still be wide enough to cover the
    new lower bound; the coercion at this use site is the resulting `coerce(T <: S)`
    term. If `T <: S` doesn't hold, the principled fix is widening `?n`'s solution to
    `lub(S, T)` (the *partial* least-upper-bound operation `<:` induces, per "Type
    grammar" above — no full lattice needed, since there's no `⊤`/`⊥`), but the
    pragmatic, cheaper option — reasonable given how rare a
    second, incomparable lower bound is without let-generalization — is to just error
    and require an explicit annotation instead of implementing `lub`.
  - **Upper-bound constraint `?n <: T`** (`?n` is asked to be *at most* `T`): if `?n` is
    unresolved, do **not** solve it to `T` yet — only record `T` as a pending upper
    bound (keeping either the running `glb` of all bounds seen so far, or the list, to
    check against once `?n` does get resolved from below). If `?n` is already resolved
    to `S`, just check `S <: T` directly, with coercion `coerce(S <: T)` at that site.
  - **Why the asymmetry is the right one:** a lower bound tells you the *smallest* `?n`
    can be, and it's always safe to commit to it immediately, because the direction your
    axioms actually hand you coercions in is narrow→wide (`Str <: Seq(Int)` gives you a
    `Str`-to-`Seq(Int)` coercion, never the reverse) — anything else can be coerced up to
    that solution later. An upper bound tells you the *largest* `?n` can be; committing
    to it immediately would foreclose a narrower solution arriving later from a lower
    bound that hasn't been seen yet.
  - **Metavariable-vs-metavariable constraints (`?m <: ?n`, both unresolved) do *not*
    reduce to either base case above** — `T` in those two rules is always a ground type;
    there's no ground type here yet. **Do not solve `?n := ?m`** (i.e. do not merge the
    two into one shared cell/union-find representative), even though `?m` is playing the
    role of a lower bound on `?n`: unlike a ground `T`, `?m` is a *live, independently
    constrained* unknown, and merging conflates its own constraint set with `?n`'s. Since
    `<:` is genuine coercive subtyping here (not mere equality, unlike the
    higher-rank-polymorphism systems where this exact trick — e.g. Dunfield &
    Krishnaswami's existential-existential instantiation — is safe), `?m <: ?n` only
    requires `?n` to be *at least as wide as whatever `?m` becomes*, not that they end up
    identical; there are legitimately satisfying assignments where they diverge to
    different (but `<:`-related) monotypes. Concretely: `?m <: ?n` alongside an unrelated
    `?m <: Str` and an unrelated `Seq(Int) <: ?n` is satisfiable with `?m := Str`,
    `?n := Seq(Int)` (both stay separate) — merging them the moment `?m <: ?n` is seen
    would force `Seq(Int) <: Str` to also hold (false), spuriously rejecting a program
    that type-checks. **Instead: record `?n` as one of `?m`'s pending upper bounds (a
    `PendingUpperBounds` entry can itself be a metavariable, not just a ground type) and
    leave `?n` completely untouched.** When `?m` later resolves (from a real ground lower
    bound elsewhere), walk its pending-bounds list and re-fire the ordinary rules against
    each entry — a still-unresolved `?n` gets the base lower-bound rule applied to it in
    turn (falling straight back into the first case above); an already-resolved `?n`
    gets the ordinary resolved-case check. This is a watch-list/propagation step layered
    on the existing two rules, not a third kind of resolution.
  - **A consequence, not a new rule:** a stray `?m <: ?n` where *both* remain unresolved
    at the end-of-check defaulting point (below) is a type error, for exactly the reason
    "no bounds at all" already is one — `?n` was left with an empty bound set by design
    (nothing was ever recorded on it), so it hits that case directly; `?m`'s only
    recorded bound was the metavariable `?n` itself, which carries no concrete
    information once `?n` has errored, so `?m` transitively has nothing to default from
    either and must error too, rather than "defaulting" to an unresolved metavariable.
  - **Defaulting**, at the single end-of-check point above: a metavariable with only
    upper bounds recorded defaults to the tightest one (or errors "ambiguous type" if
    erring toward forcing an annotation instead); one with **no bounds at all is a type
    error** — it means the metavariable was never actually constrained by anything, i.e.
    checking failed to solve it, not a case to silently default away.
  - **Implementation cost**: given no let-generalization, this does *not* need a full
    MLsub-style bounds-lattice implementation — a `Map MetaVar (Unresolved
    pendingUpperBounds | Resolved τ)` plus the cases above, with "error on a second
    incomparable lower bound" standing in for a real `lub`, is enough. Each case above
    determines exactly which coercion to emit (`id`, or a real `coerce(A <: B)` term)
    and where, so term-level elaboration falls directly out of which branch fires.
  - **The underlying judgment** driving every `require`/recursive check above is the
    same one used everywhere else in the checker — `subtype : Context → Type → Type →
    SubtypeResult` — threading the metavariable-solution context (since checking
    `A <: B` may itself resolve metavariables nested inside `A`/`B`) and yielding one of
    **three** outcomes, not a plain success/failure: a **successful coercion** (a
    concrete `Coercion`, see below, plus the updated context), a **pending coercion**
    (the check succeeded, but the coercion can't be pinned down yet — e.g. it was only
    recorded as a pending upper bound on an unresolved `?n`, per the upper-bound rule
    above — because it depends on a metavariable solution that isn't known yet), or
    **failure** (a real type error, no coercion). A `require A <: B` occurring above is
    shorthand for a call into this same judgment used in "checking mode" (validating an
    already-fixed solution — e.g. checking a new lower bound against an existing resolved
    value, or checking `S <: T` once `?n` is already resolved to `S`) rather than
    "instantiating mode" (choosing a brand-new solution).
  - **`Coercion := Expr → Expr`** — a coercion is a function on already-*elaborated*
    expressions: it verifiably turns an elaborated expression of type `A` into one of
    type `B`. When `subtype` yields a **successful** coercion, applying it at a use site
    is just ordinary function application to the elaborated expression in hand, producing
    the next elaborated expression directly — no AST node involved.
  - **`mvar`: an expression-level placeholder for a *pending* coercion.** When `subtype`
    yields **pending** (the upper-bound rule fired on an unresolved `?n`), the elaborated
    expression at that use site isn't dropped or left uncoerced — it's wrapped in a new
    constructor, `mvar : MVarId → Expr → Expr`, added to `TypedTLAPlus`/`TypedPlusCal`'s
    expression grammar (the "`.coerce` node" from the earlier draft of this question,
    renamed: `mvar` rather than `coerce` because it's tagged by *which metavariable* it's
    waiting on, not by a fixed coercion — worth keeping as a distinct, nameable node
    rather than folding it into `Coercion` itself, since other future uses of
    "elaboration waiting on a not-yet-resolved metavariable" can reuse the same
    constructor).
  - **Resolving the placeholders — implemented against the *existing* `pendingUpperBounds`
    context directly, not a separate lockstep site-tracking table (an earlier draft of
    this section proposed one; dropped once actually implemented, `Elaborator/
    Expressions.lean`'s `resolveMVars`, after the project owner flagged this whole piece
    as missing).** `mvar n e`'s wrapped `e`'s *true* type is exactly `?n`, and — given
    `specializeOperator` mints a fresh metavariable per operator-call *use* and each one
    is only ever the *source* of the one `subtype` call that builds its own `mvar`
    wrapper — in every case reachable from the checker's own code, `?n`'s
    `pendingUpperBounds` list has *exactly one* entry: the type that one call was checked
    against. So resolution doesn't need a second table at all: at the single end-of-check
    point (now: the end of each declaration, `Elaborator/Declarations.lean`, not deferred
    all the way to whole-module completion), for every `mvar n e` actually found in that
    declaration's own elaborated expressions, look up `?n`'s existing `pendingUpperBounds`
    — `[]` is the genuine "never constrained by anything" error; a single entry `b`
    assigns `?n := b` and substitutes `coerce(b <: b) = id` (trivially — `?n`'s value *is*
    its own sole bound); **more than one entry is a loud, named gap, not a guess** (`.todo`,
    not a silent pick) — real per-site tracking would be needed to substitute soundly in
    that case, and no concrete program has produced one yet. This is a deliberate,
    reviewed simplification over "keep a lockstep list of every `mvar` site," not an
    oversight — revisit if a real program ever hits the multi-bound `.todo`. By the time
    one declaration's checking finishes, every `mvar` node it introduced is eliminated
    (or checking has already failed with a real error), so no `mvar` node survives past a
    single declaration's own boundary — what `Typed2Guarded` and the backends (§5.6, §5.7)
    eventually see is still `mvar`-free.
- **Statement judgment** `Γ | Ξ ⊩ S ok` (no output type — statements are checked for
  effects, not typed). Notable asymmetric rules, worth preserving exactly as justified in
  the thesis (§3.1.5): `[Assign]` synthesizes the LHS type and *checks* the RHS against
  it (not the reverse — enables upcasting the RHS via subtyping); `[Send]` is asymmetric
  the same way (synthesizes the channel type to allow upcasting the payload — the payload
  is a genuine sub-expression, so any coercion `subtype` yields applies immediately, same
  as `[Assign]`'s RHS); `[Print]` requires a `showable` type (Fig. 3.1.14: everything
  except function/operator/channel types, recursively); `[Goto]` performs no type check at
  all — label existence is checked separately, by the well-formedness pass (§5.2a, now
  sequenced after this one, §7), not the type checker's job.
- **A channel's declared element type must be `sendable` (new, not in the thesis — the
  project owner's own addition, found missing while writing well-formedness fixtures,
  §5.2a task 11).** Same restriction as `showable` (`Operator`/`Channel`/`Const`/rigid type
  variables, and anything containing one, excluded; recurses through `Function`/`Set`/
  `Seq`/`Tuple`/`Record` otherwise) — a genuinely separate predicate (`Elaborator/
  PlusCal.lean`'s `sendable`, not a reuse of `showable` itself, since the two represent
  distinct restrictions that only happen to coincide today — but literally identical in
  shape, including excluding `Const`: the project owner's reasoning is that a `CONSTANT` is
  substituted by the user *after* code generation, and an unsendable instantiation would
  silently break the invariant if `Const` were allowed through. Checked once, in
  `checkChannelDecl`, at channel-declaration time — covers `send`/`receive`/`multicast`
  uniformly, rather than re-checking at every individual call site. New error variant
  `TCError.notSendable`. Both `showable` and `sendable` are pure, non-monadic `Typ → Bool`
  predicates — callers must resolve pending metavariables first (`resolveTypeMVarsForDisplay`)
  so `.mvar` only means "genuinely still unresolved," not "already pinned to something that
  happens to be showable/sendable"; `showable`'s own call site (`[Print]`, above) had this
  exact latent gap until fixed alongside adding `sendable` — a `print`ed expression's
  synthesized type isn't always resolved by the point it's tested (many expression shapes,
  e.g. `.opCall`, don't store their own overall type anywhere `resolveMVars` would have
  already walked). **One consequence worth flagging**: this makes a channel-of-channels
  (`Channel(Channel(τ))`) declaration a hard error — combined with `Channel`'s
  reflexivity-only subtyping (§9.15/above), this means well-formedness's own
  `channelInExpression` check can no longer be exercised via `receive`'s destination `r`
  resolving to a channel-shaped type (the only way to get a channel-shaped `r` past type
  checking in the first place needed a channel-of-channels source) — see `PLAN.md` §9.25,
  updated to note this alongside its other two now-unreachable checks.
- **`[Receive]` — channel/reference coercion, and why it can't apply eagerly (settled,
  §9.15's discussion moved here).** `Channel` is covariant (`Elaborator/Subtyping.lean`),
  but a channel-typed expression's own `Channel(τ) <: Channel(τ')` check only ever
  produces `Coercion.id` in practice — `TypedTLAPlus.Expression` has no general term
  former to wrap an opaque channel value with (`Elaborator/Subtyping.lean`'s own module
  doc), and this project doesn't need one: channels never change runtime representation
  between the checker and either backend the way, say, `Str`/`Seq(Int)` might. What
  *does* need a real coercion is the **received value itself** — the incoming message's
  element type `τ` may be narrower than the destination reference's own type `τ'`
  (`τ <: τ'`), and unlike `[Send]`'s payload, there is no elaborated sub-expression to
  hand that coercion to: `receive` produces a value at *runtime*, from the network, not
  from any expression this checker ever elaborates. Synthesize both the channel's element
  type and the reference's type, `subtype` them directly (independent of the `Channel`
  vs. `Channel` structural check above, which stays identity-only), and **store the
  resulting `Coercion` on the `TypedPlusCal`/`GuardedPlusCal` `receive` statement node
  itself** (a new field, `Elaborator/PlusCal.lean`'s to add, §5.3 task list) — carried
  through `Typed2Guarded` (§5.4) unchanged, since none of its four subpasses touch
  `receive`'s own shape, and only actually *applied* (spliced into the generated
  read-and-coerce code) by `Guarded2Network` (§5.5), the first pass where a receive
  becomes a concrete buffered read (`await Len(inbox) > 0`) with real generated code to
  coerce.
- **`Ξ` is a global cache, not threaded state — in-memory only for now, no disk
  persistence (§2, §9.11).** On paper it's an input to the judgment like `Γ`, but in
  practice it's implemented as a `MonadModuleCache m` effect (`lookup`/`store` keyed by a
  hash of each module's source) rather than passed around explicitly through every rule,
  so a module doesn't get fully re-type-checked from scratch every time it's referenced
  (e.g. repeatedly, via `EXTENDS`, within one compiler run). Disk persistence — and
  picking one of §9.11's two invalidation schemes — is deferred to a later, explicitly-
  scoped addition once the checker itself has stabilized; until then, the cache simply
  doesn't survive past one run, which sidesteps the invalidation question entirely rather
  than answering it.
- **Module resolution and TLA+ standard modules (`EXTENDS Sequences, TLC, ...`) —
  settled architecture and timing (§2).** `-I <path>` (see §9.3) adds a search path
  for locating `.tla` modules referenced via `EXTENDS`. (`INSTANCE` is out of scope for
  now, §2/§9.8 — not parsed, not resolved, not type-checked; the search-path/caching
  mechanism below only needs to handle `EXTENDS`.)
  **Resolution is eager and transitive, not lazy.** Once the main module is parsed and
  desugared (§5.1–§5.2), and before its own type checker runs, the compiler driver
  recurses on every module the main module `EXTENDS`s: parse → desugar →
  recurse the same way on *that* module's own imports → type-check, bottoming out once a
  module has no further unresolved imports (or a cache hit short-circuits the recursion
  entirely) — the recursion needs to track modules currently being resolved so that a
  cyclic `EXTENDS` is rejected with a real error instead of looping forever, a
  standard requirement for any recursive resolver rather than a further design choice.
  Only once that whole transitive closure is resolved does the main module's
  own type checker (below) begin, so every `Ξ` lookup it performs is guaranteed to
  already be populated — never a live miss triggering resolution mid-check. TLA+'s
  actual standard modules (`Sequences`, `TLC`,
  `Naturals`, `FiniteSets`, etc.) are **not** parsed from the real standard library —
  the compiler bundles its own stub versions, containing only enough to get operators
  like `Len`, `Head`, `Append` correctly typed, not real definitions. How those stubs
  are represented is an implementation detail, not a further decision needed here: either
  a builtin operator table in Lean code, or actual bundled `.tla` "dummy module" files
  with well-typed placeholder definitions, the way Apalache does it (referenced already
  in §5.3's type-grammar background) — whichever is more convenient to implement against
  the parser and checker as they exist.
- **Process/algorithm judgments** thread `self : Address` into scope, require process-ID
  sets to be `Set(Address)`, and require all channel declarations to be functions of
  addresses to `Channel(τ)`.
- **`CONSTANT`s stay abstract through the whole pipeline (§2).** They're type-checked
  (given a type, per annotation or inference) like any other name in `Γ`, but never given
  a value by this compiler — concretizing them is the user's job when they build a real
  program from the generated output, not something `Elaborator` or either backend resolves.

### 5.4 Distributed PlusCal → Guarded PlusCal (`Typed2Guarded`)
**Input:** `TypedPlusCal`. **Output:** `GuardedPlusCal` (a restriction where every
`await`/`receive`/`with` sits at the very start of its atomic block).

Defined in the thesis (§3.2.2) as `𝒞_reord ∘ 𝒞_flat ∘ 𝒞_par ∘ 𝒞_cflow` (order between
`𝒞_par` and `𝒞_cflow` doesn't matter; the other two are order-dependent). Implement as
four small, independently-testable passes composed in this order:

1. **`𝒞_cflow`** — rewrite `if`/conditional-`while` into `either`/`await`:
   `while e {B1}; B2; goto l'` (at label `l`) ⟶ `l: if e then {B1; goto l} else {B2; goto l'}`,
   and `if e then B1 else B2` ⟶ `either {await e; B1} or {await ¬e; B2}`. Justified by
   the actual PlusCal→TLA+ action semantics (an `if` compiles to an action equivalent to
   `(e ∧ 𝓔(B1)) ∨ (¬e ∧ 𝓔(B2))`).
2. **`𝒞_par`** — sequentialize parallel assignments (`r1≔e1 ∥ ... ∥ rn≔en`). Must handle
   aliasing correctly (`x[0]≔3 ∥ x[x[0]]≔7`): evaluate all RHSs into fresh temporaries
   first, then all LHS *indices* into fresh temporaries, then perform the assignments
   left-to-right using the partially-evaluated references. The thesis gives the full
   recursive definition over reference shapes (`x`, `r[e]`, `r.x`) — implement exactly
   that, it's already handling the tricky cases.
3. **`𝒞_flat`** — flatten nested `either`s into flat lists of branches, by distributing
   sequencing over choice (`B; either{B1} or ... or {Bn}; B'` ⟶ `either{B;B1;B'} or ...`)
   and using associativity of `either`. Trades code size for fewer runtime choice points
   / less need for transactional rollback machinery downstream.
4. **`𝒞_reord`** — float every `await` to the front of its branch by commuting it leftward
   past `skip`/`print`/`assert`/`send`/`multicast` (all of which are guard-independent),
   and past assignments via substitution (`𝒞_reord(r≔e; await e') = await e'[e\r]; r≔e`,
   substituting `r` by `e` in `e'`, using `EXCEPT` when `r` has an index). **Updated: §3.2.2.4
   is no longer a stub as of the July 2026 thesis revision** — it's now fully written and
   confirms the substitution rule exactly as already assumed above, plus gives the
   correctness argument that was previously missing: `assert`/`print`/`skip` commute with
   `await` trivially because they never affect the program state (variables are only read,
   never written, so neither statement's truth value can be affected by reordering);
   `send`/`multicast` commute because channels are explicitly forbidden from appearing in
   any expression (so no guard can ever depend on one), which is exactly why `await` may be
   freely floated above them. The assignment case is the one requiring genuine substitution,
   since the assignment can influence `e'`'s valuation — worked through in the thesis via the
   Two-Phase Commit `c2` example (Listings 3.2.1–3.2.4), matching this plan's own
   description. `receive` is explicitly *not* handled by `𝒞_reord` (deferred to §5.5 — Network
   PlusCal is where receive-guards disappear entirely).

Worked example available in thesis Listings 3.2.1–3.2.4 (the Two-Phase Commit `c2`
block) — good first target to hand-verify the implementation against once each subpass
exists.

### 5.5 Guarded PlusCal → Network PlusCal (`Guarded2Network`)
**Input:** `GuardedPlusCal`. **Output:** `NetworkPlusCal` (no `receive` guards; each
process gets an opaque `T_rx(mailbox → inbox)` thread that buffers incoming messages into
a process-local `inbox` sequence variable, turning `receive(c, r)` into ordinary
`await Len(inbox) > 0`-guarded reads).

**This is also where `[Receive]`'s stored channel/reference coercion (§5.3, §2) finally
gets discharged** — the first pass where a `receive(c, r)` becomes a concrete buffered
read (`await Len(inbox) > 0`) with actual generated code around it to splice the coercion
into, rather than an abstract guard. Every earlier pass (the checker itself, all four of
`Typed2Guarded`'s subpasses, §5.4) just carries the `Coercion` value through unapplied on
the `receive` node.

This is the one pass with a complete implementation *and* a completed refinement proof in
prior art (`fugue` `main`: `PlusCalCompiler/Passes/GuardedToNetwork/{PlusCal,Lemmas}.lean`,
against `GuardedPlusCal/Semantics/Denotational.lean` and
`NetworkPlusCal/Semantics/Denotational.lean`). The ported `Core/GuardedPlusCal/Syntax/
WellScopedness.lean` (§5.2a) supplies the well-scopedness hypothesis this proof needs as
a precondition, established via a **general preservation lemma** (§2) proved once over
`Elaborator`/`Typed2Guarded` — fitting the project's overall verification aesthetic better
than re-deciding it per compiled program, per the project owner.
The thesis chapter for this pass (ch. 5) is
itself just a stub — **the code is the spec here, not the PDF.** Port the pass and, per
§2's verification decision, actively port the proof too (this is the one pass this plan
commits to keeping verified). Expect to adapt rather than copy verbatim, since the source
AST (`TypedPlusCal`/`GuardedPlusCal`) is being rewritten fresh in this project (§5.2–5.4
didn't exist as real code in prior art), so the denotational semantics and lemmas will
need re-deriving against the new `Core/GuardedPlusCal/Syntax.lean`, even though the
mathematical content of the proof should transfer. The ported proofs will likely need
some cleanup (prior art's proof style predates some of this project's conventions) — that
cleanup is tracked as its own, independent effort, not a blocker for landing the ported
pass.

### 5.6 Network PlusCal → the Join Calculus (`Network2JoinCalculus`) — NEW
**Input:** `NetworkPlusCal`. **Output:** `Core/JoinCalculus`, pretty-printed to a `.join`
(or similar) source file. Fully specified in thesis ch. 8; no existing code anywhere —
this is new implementation work top to bottom.

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
Operational semantics: the Reflexive CHemical Abstract Machine (RCHAM) — heating/cooling
structural rules (`Str-Null`, `Str-Par`, `Str-And`, `Str-Def`) plus reaction (`Loc-React`)
for local solutions, and `Register`/`Lookup`/`Str-Comm` for distributed global solutions
(named locations `α`, a name server `Γ` mapping registered tokens to locations). Full
rules in thesis Fig. 8.4.2–8.4.3. Not needed for the initial implementation — having
`Network2JoinCalculus` actually compile is the near-term goal; formalizing
`Core/JoinCalculus/Semantics/` is low priority for now, see §9.4.

**Compilation scheme**, `𝒞 : NetworkPlusCal.Process → JoinCalculus.Process`:

- **State as atoms.** Each mutable process-local variable `x` becomes a single-token
  "reference cell" atom `x⟨v⟩` floating in the process's local solution. Every reaction
  reading `x` must consume `x⟨v⟩` in its pattern and re-emit `x⟨v'⟩` (updated or
  unchanged) in its body — atomicity of a Network PlusCal block falls out for free,
  because exactly one `x⟨v⟩` token exists per variable and it can only be consumed by one
  firing reaction at a time.
- **Process skeleton.** `P = self ⋆ x1=e1,...,xn=en ⋆ {T1}...{Tm}` compiles to
  `def p⟨self⟩ ⊳ def recv⟨v⟩|inbox⟨vs⟩ ⊳ inbox⟨vs∷v⟩ in register recv as "{self}";
  x1⟨e1⟩|...|xn⟨en⟩|l_i⟨⟩|...|l_j⟨⟩`, where `l_i,...,l_j` are each thread's first label
  (this is the process's `T_rx` thread, made concrete: `recv` is the reaction that
  implements mailbox buffering) — running the process later means emitting `p⟨α⟩` for
  some concrete location `α`. Per §2, a process set `p ∈ S` compiles to this **one**
  definition, not `|S|`-many — `p` is a single reusable definition parameterized over
  `self`, and it's up to whoever runs the emitted `.join` file to `def p⟨α⟩` once per
  concrete process they want live, choosing `α` themselves (`S`'s actual membership is
  never evaluated by this compiler, since `S` may depend on an unresolved `CONSTANT`).
- **Atomic blocks.** `l: {G1;S1;goto l1} or ... or {Gn;Sn;goto ln}` — each branch compiles
  to `def l⟨⟩ | x_a⟨x_a⟩ | ... | x_g⟨x_g⟩ if ⟨conjunction of Gi's awaits⟩ ⊳ ⟨updated state
  atoms⟩ | ⟨out⟨v⟩ per print⟩ | ⟨let send:=lookup α; send⟨e⟩ per send(c[α],e)⟩ | l_i⟨⟩`.
  The block's own label atom `l⟨⟩` is consumed and *not* re-emitted except by an explicit
  `goto l` in some branch — this is what restricts the whole `either` to firing at most
  one branch at a time.

Ping-Pong worked all the way through in thesis §8.6 (both the `rcvPi`/`sndPo` reactions
and the full process definition) — use it as the implementation's first target, by hand
before automating, to validate the compiled shape before trusting the general pass.

`isFair` is carried through unused: nothing about `𝒞` makes reaction-firing nondeterminism
fairness-aware, per §2's decision that fairness isn't acted on by this compiler.

**Identifier hygiene.** `recv`, `inbox`, and per-block label atoms (`l⟨⟩`) are names `𝒞`
introduces, not names from the source module — per §2, these need the same
collision-avoidance treatment as Go keyword-escaping (§5.7's `sanitize`/`keywords`
precedent), generalized to whatever the guarded-reaction dialect's own reserved surface
turns out to be, so that a user's own PlusCal variable or channel named `recv` or `inbox`
can't shadow the ones `𝒞` emits.

**Explicitly open, per the thesis's own "Future Work" (§8.7) and confirmed out of scope
for this plan (§2):** correctness of `𝒞` is *not proven anywhere*, and the emitted dialect
(guards on reactions) isn't accepted by existing Join Calculus implementations (JoCaml
etc. don't support `if e ⊳`) — the thesis sketches an encoding (`def J if e ⊳ P` as `def J
⊳ if e then P else J`) but flags it as a performance-losing workaround, not a real answer.
Emitting a well-formed `.join` file that is faithful to this compilation scheme is the
actual deliverable for this stage; what happens to that file afterwards is §9.1.

### 5.7 Network PlusCal → Go (`Network2Go`) — including lock inference
**Input:** `NetworkPlusCal`. **Output:** `Core/Go`, pretty-printed to `.go`, depending on
a runtime library this project also owns (see below).

**As of the July 2026 thesis revision, ch. 7.1 (atomicity/lock inference) is no longer a
stub**, and per the project owner (resolving the former §9.20), this section now follows
the thesis's [HFP06]-derived algorithm rather than the earlier connected-component scheme
— see "Lock inference, concretely" below, updated accordingly. §7.2/§7.3 (the actual
expression/statement compilation and correctness sketch) remain stubs. The
`lock-inference` branch itself still got no further than a FIXME comment — that's the
*written-up design*, not the actual code.
`Network2Go/PlusCal.lean` itself is real, working code, and per the project owner it
already gets essentially everything right — it compiles Network PlusCal processes/threads
into genuinely concurrent Go (goroutines communicating over channels, using
`Core/Go/Syntax.lean`'s `go`, unbuffered/buffered `chan`, and `send`/`receive`/`select`
with `SelectClause.receive`/`send`/`default`) — **except** for synchronizing atomic
blocks that touch shared process-local state when they run concurrently on different
goroutines. Lock inference is the one missing piece to port around, not a reason to
redesign the backend from a simplified baseline; don't reinvent the rest of the pass.
Also directly reusable: the hand-written runtime scaffolding in
`distpcal-compiler/tests/*/{lib,nameserver}` (TCP/UDP address resolution + a name server
process for cross-machine address discovery — the practical, already-prototyped Go
analogue of §5.6's `register`/`lookup`).

**Caveat to "essentially everything right": that almost certainly covers *intra-process*
concurrency only, not `send`/`receive`'s actual cross-process wire mechanism.** The
"goroutines communicating over channels" described above is Go's own native `chan` used
for plumbing *within* one compiled process (e.g. a thread and its `T_rx` counterpart
passing buffered messages to each other locally) — genuinely a solved, portable concern.
But Distributed PlusCal's own `send(c, e)`, once `c` is addressed to a different
(possibly remote) process, has to leave the process entirely: nothing in this plan
actually describes that compilation scheme, and it is not confirmed to already be solved
by the ported pass — see §9.12.

**Lock inference, concretely (resolved: follow thesis §7.1.2's [HFP06]-derived scheme,
superseding the earlier connected-component design).** Unlike the earlier one-lock-per-block
approach, locks are assigned **per process-local variable**, and a block may need to
acquire *several* locks (one per variable in its footprint, after merging):

1. For every atomic block `B` (not just cross-thread pairs — computed over *all* blocks of
   the process), let `shared(B)` be the set of process-local variables read from or written
   to in `B` (free variables in expression position, plus all indexed-assignment targets,
   minus any `with`-bound temporaries).
2. Define domination: `x ⪰ y` iff every block with `y ∈ shared(B)` also has `x ∈ shared(B)`;
   `x ≻ y` (strict domination) when additionally `x ≠ y`.
3. Lock selection (Definition 7.1.3): start with one fresh lock `ℓ_x` per variable `x`. Then
   for each variable `x`, if some `y ≻ x` exists, merge — redirect every variable currently
   assigned `ℓ_x` to `y`'s lock instead. This can only reduce the number of distinct locks
   below one-per-variable, never increase it.
4. Pick any total order `<` over the resulting set of locks (needed because a block may now
   hold more than one lock at once — a fixed acquisition order across all blocks avoids
   lock-ordering deadlocks). At the start of each block `B`, acquire the locks of
   `shared(B)` in that order; release them (order doesn't matter) at the end.
5. Final pruning pass: any lock that ends up used only within a single thread can be
   dropped entirely — blocks within one thread are already mutually exclusive by
   construction (Network PlusCal only ever runs one block of a given thread at a time), so
   there's nothing left for that lock to protect against.

This is a genuinely different design from the discarded connected-component scheme: this
one holds potentially several locks per block (ordered to avoid deadlock) rather than
exactly one, and groups by variable-level domination rather than by block-level graph
connectivity. Implement steps 1–5 directly against Definition 7.1.3 and Examples
7.1.1/7.1.4/7.1.5 in the thesis — they're worked examples good for hand-verifying the
implementation.

`isFair` is carried through unused: lock inference and Go's goroutine scheduler make no
attempt at fairness, per §2's decision that fairness isn't acted on by this compiler.

**Identifier hygiene, and the existing precedent to generalize (§2).** Per-block lock
variable names are `Network2Go`-introduced, not user names, and need the same
collision-avoidance treatment described in §2 — prior art already has a real, working
mechanism for the adjacent problem (a PlusCal name colliding with a **Go keyword**, not a
compiler-internal name): `Core/Go/Pretty.lean` keeps a `keywords : Std.HashSet String`
table and a `sanitize` function that suffixes any colliding name with `__`, applied at
every point an identifier gets printed (record fields, struct-literal keys, variable
references, field access). Port this and extend its `keywords` table to also cover every
name `Network2Go` itself introduces (lock variables and anything else added once lock
inference lands), so the same one mechanism handles both directions of collision.

**Go representations of TLA+ types, per thesis §7.2.1.1 (new as of the second July 2026
revision).** The thesis now settles most of the type-representation question `lib/tlaplus.go`
only gestured at:
- `Bool`/`Int`/`Str` → `bool`/`int`/`string`. **This narrows, but doesn't fully close,
  §9.7's open numeric-representation question**: the thesis's own default is to restrict
  to a fragment of TLA+ where integers are refined to *machine* integers (Go's `int`,
  32/64-bit per the Go spec), for efficiency — not `math/big` by default — while also
  committing to *additionally* exposing the slower `math/big`-backed `Int` for specs that
  actually need unbounded arithmetic. That's two representations, not one — **resolved
  (§2/§9.21): a whole-program compiler flag, target-specific to the Go backend, picks
  between them**, not a per-declaration annotation. Flag's exact name still undecided,
  see §9.3.
- Functions `τ → τ'` → lazy maps (wrapping `map[τ]τ'`, avoiding eagerly computing the
  whole graph at declaration time — mirrors what TLC does).
- `Set(τ)`/`Seq(τ)` → both `[]τ`; sets additionally carry a no-duplicates invariant (so
  `τ` must be comparable) not tracked at the Go type level. Sequences keep TLA+'s
  1-indexing by leaving slot 0 of the underlying slice unused/unobserved.
- Records/tuples → `struct`; tuples use `proj1`..`projN` field names (a tuple is sugar for
  a specific record shape).
- Operators `(τ1,...,τn) ⇒ τ` → plain Go `func`.
- Type variables → propagated to the nearest enclosing function definition (Go generics).
- Uninterpreted constant types → left as-is (same name), expected to be supplied by the
  user — consistent with the `CONSTANT` scope boundary above.
- `Address` → an unspecified interface, decaying to a constrained generic argument in
  generated code.
- `Channel(τ)` → **resolved as of the third July 2026 revision (commit `c2bbf8f`)**: "since
  channels are not first-class citizens in Distributed PlusCal, we do not (need to)
  represent `Channel(τ)` in the general case" — i.e. there's no general-purpose Go value
  representation to design, because a channel is never stored in a variable, passed
  around, or put in a data structure as an ordinary TLA+ value; it only ever appears
  indexed (`c[α]`) at a `send`/`receive` site. **This narrows, but doesn't close, §9.12**:
  it answers "what Go *type* represents a channel value" (answer: none needed), not "what
  does `send(c, e)` to a different process actually compile to on the wire" (still open —
  see §9.12).

**§7.2.1.2 and §7.2.2, both new as of the third July 2026 revision (commit `c2bbf8f`,
2026-07-11) — compiling TLA+ expressions, operators, and functions.** Both are now fully
written (superseding the earlier "almost entirely unwritten" state); §7.2.3 (statement-level
Network PlusCal → Go compilation, the section this plan previously called "§7.2.2" before
the renumbering — see §3.3) and §7.3 (correctness sketch) remain stubs, so the actual
process/thread/atomic-block compilation scheme is still undesigned. Digest of the new
material:

- **Equality/ordering.** Go's builtin `==`/`comparable` can't be implemented for custom
  types and falls short for the complex TLA+ types anyway (order-irrelevant set equality,
  sets-of-sets needing deep order-irrelevance, lazy maps not comparing all entries). The
  thesis defines its own `Eq[T]`/`Ord[T]` interfaces (`Ord` extends `Eq`, adds `Gt`/`Lt`,
  with `Le`/`Ge`/`Cmp` derived generically) and has every wrapper type implement them —
  including primitive types, which need a local newtype (`type Bool bool`, etc.) since Go
  interfaces can't be implemented for non-local types. Port `Eq`/`Ord` as part of the
  runtime library (below), and every generated type implements them, not just the ones
  that happen to need comparison at a given use site.
- **Booleans.** `/\`/`\/` compile to Go's short-circuiting `&&`/`||` (sound because
  non-action, non-temporal TLA+ expressions are pure — no observable side effect from
  skipping evaluation of one side). `\A x \in S : P`/`\E x \in S : P` compile to a search
  over `S` for the first counterexample/witness (via De Morgan equivalence between the
  two).
- **Sets.** `{x \in S : P}`/`{e : x \in S}` compile via `SetFilter`/`SetMap` helpers,
  copying the underlying slice rather than mutating `S` in place (TLA+ data is immutable).
  `CHOOSE x \in S : P` — needing to be *deterministic* (`CHOOSE x \in S : P` always picks
  the same element for the same `S`/`P`) — compiles to filter-then-take-minimum-by-`Ord`
  (`SetFilter` then `slices.MinFunc` against `Cmp`), not a random pick; this only requires
  an `Ord` (not just `Eq`) constraint on the element type at `CHOOSE`'s own call site, not
  everywhere a `Set(τ)` is used, since Go generics resolve constraints per call site.
  Panics on an empty result set.
- **Functions.** Still lazy maps (§7.2.1.1), but since Go's builtin `map[T]U` requires `T`
  to implement `comparable` (which the custom `Eq`/`Ord` interfaces don't satisfy), the
  thesis switches the underlying storage away from `map[T]U` to an ordered-map structure
  keyed by a comparator derived from `Ord.Lt`. The thesis's own text gestures at the
  external `github.com/igrmk/treemap` package for this, but **per the project owner, this
  plan does not take that dependency — see `.claude/plans/persistent-collections-plan.md`,
  a home-grown, persistent (immutable, structurally-shared) `TreeMap[K, V]` in
  `persistent/treemap/`** (weight-balanced tree, `Compare func(a, b K) int`-parameterized,
  O(1) `Clone`/O(log n) `Insert`/`Delete`/`Get`, no `comparable` constraint). This isn't
  just a not-invented-here swap: `EXCEPT` (function overloading) always clones the
  underlying map before writing, so `[f EXCEPT ![3] = 7][3] = 7 /\ f[3] # 7` holds — with a
  genuinely persistent tree, that clone is O(1) via structural sharing rather than an O(n)
  full copy, which a mutable external map would force. See the runtime library paragraph
  below.
- **Operator/function definitions (§7.2.2, a newly-split-out section — see §3.3).**
  Parameter-less operators compile to a plain (mutable, in Go's
  own type system — "immutable" is a documentation convention here, not
  compiler-enforced, since most TLA+ value types aren't in Go's small set of `const`-eligible
  types) `var`, initialized once. Parametric operators — recursive or not, Go supports
  mutually-recursive top-level functions natively — compile straightforwardly to Go
  functions; names are capitalized in the generated code (Go's own public/private
  convention) regardless of original casing, except `LOCAL` definitions. **Recursive
  *functions*** (as opposed to recursive operators) need a bootstrapping trick, since the
  generator closure has to call back into the very `LazyFunction` it's building: `MkRecFn`
  allocates the `LazyFunction` first with a `nil` generator, then overwrites `.gen` with a
  closure capturing the function itself by reference (Go closures capture variables, not
  values) — "ties the knot" so the closure can call back into its own cache once invoked,
  without ever being invoked before construction completes.

None of this changes anything already decided elsewhere in this plan — it doesn't touch
§9.7's already-settled numeric-dispatch question (§9.21) or reopen anything in §2.

**Runtime library.** `Core/Go`'s pretty-printer assumes a companion Go package (prior art:
`github.com/mesabloo/distpcal-compiler/lib`, which will need to be furnished for this
project's own import path — not something already sitting there ready to import)
providing: TLA+ value encodings (`Seq`,
`Set`, functions, records — `lib/tlaplus.go` is a working reference), `Address`
(`lib/address.go`), and address resolution/discovery for cross-process `send`
(generalize the hand-written `nameserver` package found under `distpcal-compiler/tests/*/`
into a proper, reusable runtime component rather than per-example copies). This library
is part of this project's deliverables, not an external dependency — **settled: lives in
`runtime/go/` in this repo**, alongside the Lean sources, versioned together with the
compiler that targets it. **New concrete requirement, from the third July 2026 revision's
§7.2.1.2/§7.2.2 (above):** the `Eq`/`Ord` interfaces and their implementations for every
generated wrapper/newtype belong here too, and lazy functions need an ordered-map backing
store in place of `map[T]U` (since `T` is constrained by the custom `Ord`, not Go's builtin
`comparable`). **Settled per the project owner: no external dependency for this** — use the
home-grown persistent `persistent/treemap` package instead of the thesis's own suggestion
of the external `github.com/igrmk/treemap`, per
`.claude/plans/persistent-collections-plan.md` (see the "Functions" bullet above for why
persistence specifically, not just ordering, is the actual payoff).

**The compiler does not emit a `main` function, or a runnable program on its own.**
`Network2Go` produces Go source — types and functions — not a deployable binary; the
`runtime/go/` library supplies the pieces those generated functions depend on (value
encodings, `Address`, the nameserver client), but wiring everything into something that
actually runs — writing `main`, deciding how (or whether) each Network PlusCal process
maps to a separate OS process, and bootstrapping how a process finds the nameserver in
the first place — is explicitly left to whoever is using the generated code, not
something this project's deliverable handles. Expect real, non-trivial boilerplate on
the user's side; this is a deliberate scope boundary, not a gap to close later.

**Same scope boundary applies to `CONSTANT`s and process sets (§2).** A process set
`p ∈ S` compiles to a **single** Go function/type (parameterized over the process's own
identity/address), not `|S|`-many spawned goroutines — `S`'s membership is never
evaluated by this compiler (it may depend on an unresolved `CONSTANT` in the first
place). The caller's boilerplate (already expected to write `main`, per above) is also
responsible for supplying `CONSTANT` values and for invoking each process's entry point
once per concrete process/address it wants running.

---

## 6. Verification strategy

### 6.1 Framework
`VerifiedCompiler/Trace.lean` defines `Trace`, an ordered-monoid-typeclass abstraction
over event traces (`τ` with `Monoid`, `PartialOrder`, and two compatibility axioms between
`≤` and `*`), used to make refinement composable regardless of what a given pass's trace
alphabet actually looks like. `VerifiedCompiler/Denotational/StrongRefinement.lean`
defines simulation relations `Terminating`/`Diverging` between a source and target
language's *denotational* semantics — each language's meaning given directly as a
`Set (state × trace × state)` relation (a program denotes the set of input/trace/output
triples it can produce, which is how non-determinism is represented denotationally here,
per `Core/*/Semantics/Denotational.lean`), not as an operational small-step transition
system — with a genuinely useful algebra on top:
composability across passes (`Terminating.Comp`), monotonicity, identity, arbitrary sups,
and a `lfp` (least-fixed-point) induction principle for semantics defined as fixpoints
(needed for anything with loops/recursion). This is worth vendoring essentially as-is —
it's generic over the source/target languages and traces, doesn't depend on any of the
domain-specific AST code being rewritten.

### 6.2 What gets a proof in this plan
Per §2: only **Guarded PlusCal → Network PlusCal**, matching prior art's existing proof.
Concretely this means: `Core/GuardedPlusCal/Semantics/Denotational.lean`,
`Core/NetworkPlusCal/Semantics/Denotational.lean`, and a `Guarded2Network/Lemmas.lean`
establishing a `StrongRefinement.Terminating`/`.Diverging` instance between them, ported
and re-derived against the fresh ASTs.

### 6.3 What's explicitly deferred
Everything else — parser correctness, desugarer semantics-preservation, type-checker
soundness, Distributed→Guarded (`Typed2Guarded`) *behavioral* correctness (a full
denotational refinement proof against `TypedPlusCal`'s semantics, in the same
`StrongRefinement` sense §6.2 commits to for Guarded→Network), and both new backends.
"Deferred" means **not committed for this initial roadmap, not abandoned** — proving
`Typed2Guarded` correct in that full sense is a real, intended eventual target, just not
one this plan schedules now. This is a real limitation in the meantime, not an
oversight: it means, for instance, that a bug in `𝒞_reord` (§5.4, itself flagged as
under-specified in the thesis) could silently produce a miscompiled program with no
proof to catch it. Treat the *type-level* invariants baked into the ASTs (e.g.
`CorePlusCal`'s terminal-statement indexing, §3.2/§5.2) as the first line of defense
where full semantic proofs aren't attempted yet — get the types to rule out as many
wrong programs as possible even where behavior isn't proved.

**This is not in tension with §2's well-scopedness preservation lemma.** That lemma
(`Elaborator`/`Typed2Guarded` preserve well-scopedness, §5.2a/§5.5) is a narrow, *syntactic*
structural fact, categorically lighter than the full behavioral correctness this section
defers — it's best understood as the first slice of `Typed2Guarded`'s eventual
correctness work landing early, because Guarded→Network's committed proof needs it as a
precondition now, not as scope creep into work this section says is unverified.

### 6.4 Go's denotational semantics — deliberately not started here
The `go-semantics` branch's domain-theoretic account of Go (ch. 6: solving a domain
equation `P ≅ F(P)` over a complete ultrametric space to get a denotational semantics that
handles unbounded recursion/goroutines properly, via ~20 files of from-scratch topology:
`IMetricSpace`, Lipschitz maps, uniform continuity, closed embeddings, Banach fixpoints)
is real, substantial, unfinished work, and is **not** part of this plan's near-term scope:
per §2, verification for this plan is scoped to Guarded→Network only, and `Network2Go`
(§5.7) is expected to reach correctness, once anyone attempts to prove it, by relating
its lock-protected execution model back to `NetworkPlusCal`'s own semantics directly,
not through a standalone Go domain model. Revisit once `Network2Go` (lock inference
included) exists and there's appetite to prove it correct.

---

## 7. Suggested phasing

Not a schedule — a dependency-respecting order. Each phase should produce something
buildable (`lake build`), even if incomplete/unverified.

1. **Scaffolding.** `lakefile.lean` (package `Fugue`, targets per §4, current stable
   Lean toolchain per §2), vendor `Extra`/`VerifiedCompiler`/`ProgressBar`/`Common`,
   `CLAUDE.md`, copy `reference/thesis.pdf` in. Resolve §9.2 (auditing `Parser_` as the
   port source) before or during this phase.
2. **Frontend ASTs + pretty-printers.** `Core/SurfaceTLAPlus`, `Core/SurfacePlusCal`
   syntax + `Std.ToFormat` instances, no parser yet — lets later phases be tested by
   hand-constructing ASTs before parsing exists.
3. **CLI wiring** (`Fugue.lean`). Build the executable skeleton early rather than at the
   end: argument parsing, input file handling, debug-dump flags, progress-spinner UX per
   prior art's `pcvc`/`fugue.sh` (§9.3 for the remaining open flag details) — wired up
   against whatever passes exist so far, and extended incrementally as each later phase
   lands. "Both backends reachable, target
   selectable" only becomes true once phase 10 exists, but the CLI shell itself, and the
   ability to dump intermediate ASTs as each pass is built, is worth having from here on.
4. **Lexer + parser** (§5.1). First point at which real `.tla` source can be fed in
   through the CLI built in phase 3.
5. **Desugarer** (§5.2): port expression desugaring, design + implement statement
   desugaring (`CorePlusCal`'s explicit-goto normalization) from scratch.
6. **Type checker** (§5.3): implement the bidirectional rules from thesis §3.1
   essentially verbatim. Sequenced ahead of well-formedness checking (phase 7) —
   **inverted from an earlier draft of this plan** — because type checking already
   forces variable well-scopedness as a side effect of succeeding (an out-of-scope or
   undeclared reference is a `Γ`-lookup failure, i.e. a type error on its own), so there's
   no reason to gate it behind a separate pre-pass re-deriving the same fact; see §5.2a.
7. **Well-formedness checking** (§5.2a): well-labelledness, variable well-scopedness, and
   the no-bare-temporal/action-operator check, over `CoreTLAPlus`/`CorePlusCal` — purely
   syntactic, and has no dependency on the type checker (phase 6) either way, so it's free
   to run after it. Of the well-scopedness sub-check, only the freshness/no-duplicate-names
   half is still genuinely load-bearing at this point — variable-reference resolution is
   already guaranteed by having gotten through phase 6 (see §5.2a for the detailed
   breakdown). Port the two `WellScopedness.lean` files here too (§2), even though their
   primary use shifts to proof-support at phases 8 and 9.
8. **`TypedTLAPlus` → `TypedSetTheory`** (§5.3): a separate pass from the type checker
   itself — translate every expression used in the PlusCal algorithm (and every operator
   defined earlier in the module that those expressions depend on) by stripping out
   actions and temporal formulas, which doubles as checking none were illegitimately
   present. Depends on phase 6, but is its own small pass, not part of it.
9. **`Typed2Guarded`** (§5.4): the four subpasses, in order, each independently
   testable against the thesis's Two-Phase Commit worked example.
10. **`Guarded2Network`** (§5.5): port pass + proof from prior art.
11. **Backends, in either order (independent siblings, §2):**
    - **`Network2JoinCalculus`** (§5.6): new implementation, validate against the
      Ping-Pong worked example by hand first.
    - **`Network2Go`** (§5.7): port the pass (already real, goroutine-based codegen),
      plus the lock inference algorithm described there, plus a runtime library skeleton
      (value encodings + address/nameserver primitives). Once both backends exist, the
      CLI's target selection (phase 3) is complete.
12. **Stretch, explicitly out of this plan's committed scope but worth flagging as
    natural next milestones:** Join Calculus execution strategy (§9.1); broadening
    verified coverage beyond §6.2; revisiting Go's denotational semantics (§6.4); a real
    example/regression suite; a static "minimal needed addresses" analysis pass to avoid
    assuming full process-to-process connectivity (§2), if the nameserver-based
    addressing design ever gets revisited enough to make it worthwhile again.

---

## 8. Language subset for v1

Derived from the type-checking rules actually specified (thesis Fig. 3.1.13, 3.1.15,
3.1.16) — this is what "Distributed PlusCal" concretely means for this project:

Statements: `goto`, `skip`, `await e`, `receive(c, r)`, `r ≔ e` (assign), `with x = e do
B` / `with x ∈ e do B`, `send(c, e)`, `assert e`, `print e`, `either B1 or ... or Bn`,
`while e do B`, `if e then B1 else B2`, `multicast(x, [y ∈ e1 ↦ e2])`. Processes: uniform
process sets `p ∈ S ⋆ x1=e1,...,xm=em ⋆ T1...Tn` (single-process `process(x=e)` is sugar
for `process(x ∈ {e})`, per thesis §3.1.5 — worth actually implementing it as sugar,
i.e. desugaring it away early, rather than duplicating rules/cases downstream).
Algorithms: `fifos c1:τ1,...; P1 ∥ ... ∥ Pn`.

---

## 9. Open questions

Flagged throughout the plan above; collected here so nothing gets silently decided during
implementation. Ask before resolving any of these unilaterally if they turn out to matter
more than expected.

### 9.1 Join Calculus: what happens after emission?
§2/§5.6: this plan's committed scope is "emit a syntactically well-formed `.join` file
implementing the thesis's compilation scheme." Left open: does this project eventually
need (a) an interpreter for the guarded dialect (closest to "formally verified compiler"
in spirit — much easier to relate an interpreter's semantics to a Lean model than real Go
concurrency), (b) a further lowering to something existing tooling runs (JoCaml-compatible
encoding, with the performance caveat the thesis flags), or (c) nothing at all, treating
the Join Calculus output purely as a verification artifact? Revisit once §5.6 exists and
it's clearer what "done" should mean for this backend.

### 9.2 Parser implementation — ported and confirmed building (Phase 3, done)
Audited during planning (static read-through, see below for what changed once actually
built), then ported for real in Phase 3 into this repo's `Parser_/{Annotations,Common,
Monad,PlusCal,TLAPlus}.lean` + `Parser_/Tokens/{PlusCal,TLAPlus}.lean` +
`Parser_.lean`. **The outstanding check from planning — an actual `lake build` — is now
done**: `Fugue.Parser` builds clean, and the `fugue` executable lexes/parses a real
`.tla` file end-to-end (`tests/PingPong/PingPong.tla`, thesis §8.6's worked example)
through the CLI built in Phase 2. See `.claude/plans/iridescent-enchanting-sparkle-
findings.md`'s Phase 3 entry for the four real bugs testing surfaced in total (a missing
`return` in `parseMailbox`; an out-of-bounds panic in `parseModule`'s EOF-error path; the
long-known duplicated-character rendering bug in `CompilerDiagnostic.pretty`; and
`parseAtom` never handling the `.true`/`.false` tokens at all) and the toolchain-bump
deprecations fixed along the way — none of it "no sorry, no panic!"-level static reading
could have caught, confirming the planning-time caveat that a static read-through isn't a
substitute for a real build. The last two of these were found only after the project
owner pushed back on an initial, too-hasty "Phase 3 done" claim that had wrongly written
off `tests/TPC/{TPC,TPC2}.tla` as out-of-scope fixtures rather than real inputs — see the
correction later in this section.

The **`fair process`/`fair+` → warning** requirement (§2, §5.1) is implemented via a
`ParserWarning` type and a `ParserWarningM := StateT (List ParserWarning) Id` base monad
for `TLAPlusParser`/`PlusCalParser` (`Parser_/Common.lean`, `Parser_/Monad.lean`) —
warnings are collected out-of-band during parsing and returned alongside a successful
`parseModule` result, filtered/rendered by the CLI driver (which has `FlagsEnv`) rather
than checked mid-parse. `lexModule`/`parseModule`/`resolveAnnotations` themselves keep
prior art's concrete `Except`/`Sum`-returning shape unchanged, per the project owner's
explicit confirmation that only these entry points need to stay non-monad-polymorphic —
the underlying `ParserT`/`SimpleParserT` combinators were already `m`-polymorphic before
this project touched them (`fgdorais/Parser`'s own design), so this is simply the one
concrete instantiation the compiler runs them at, not new abstraction.

Known, bounded gaps found by the read-through (worth triaging, not blockers, and
confirmed still present after the real port — none hit by the Ping-Pong exit criterion):
- `TODO`s for: an incomplete TLA⁺ reserved-word list (`TLAPlus.lean:62`), no
  binary/octal/hex number literals (`TLAPlus.lean:376`), and no handling of junk before
  the module start / after the module end (`TLAPlus.lean:1135`).
- PlusCal `macro`/`procedure`/`define` sections are explicitly unsupported
  (`PlusCal.lean:387`) — `Core/SurfacePlusCal/Syntax.lean` doesn't even have AST nodes
  for them yet. **Not a blocker**: none of these appear in the v1 language subset (§8),
  which matches the thesis's own typing rules never mentioning them either. Confirmed by
  testing: `distpcal-compiler/tests/LamportMutex/LamportMutex.tla` fails on exactly this
  (a `define { ... }` block) — expected, not a regression.
- `TLAPlus.lean:935`'s `-- TODO: parse annotations` comment on `parseQuantifierBound`
  looks stale on inspection — the code right below it already calls
  `tryParseAnnotations` for every binder — but worth a quick confirming look rather than
  trusting that read.
- **New, found by testing:** `parseChannels`/`parseFifos` (`PlusCal.lean`) only accept a
  single bracket-index group (`chan[S]`), unlike `Ref.args : List (List β)` which
  supports the multi-dimensional form (`x[i][j]`) used elsewhere (e.g. `parseRef`). Found
  via `LamportMutex.tla`'s `fifos network[Nodes][Nodes];` — moot for that specific file
  (it also uses an unsupported `define` block), but a real, narrow grammar gap for any
  future v1-subset program wanting a multi-dimensional channel/fifo declaration. Not
  fixed in Phase 3 (out of scope: no `define`-free test program hits it), left for
  whoever next touches `parseChannels`/`parseFifos`.
- **Correction (the project owner caught this): `distpcal-compiler/tests/TPC/{TPC,TPC2}.tla`
  are NOT out of scope** — an earlier draft of this entry wrongly assumed the appended
  plain-TLA⁺ definitions after the algorithm comment (`a1(self) == ...`, `pc' = ...`) were
  leftover output from the *old* pipeline never meant to feed back through this compiler.
  That was wrong: the whole module, appended definitions included, is expected to parse.
  The real cause was two genuine parser bugs, both found and fixed once actually pressed
  on (see `iridescent-enchanting-sparkle-findings.md`'s Phase 3 entry for the debugging
  trail): (1) the known duplicated-character rendering bug (`Common/Errors.lean`, fixed —
  two compounding off-by-ones in `CompilerDiagnostic.pretty`'s column math, not just the
  underline-width mismatch originally suspected), and (2) `parseAtom`
  (`Parser_/TLAPlus.lean`) never had cases for the `.true`/`.false` tokens at all — `TRUE`/
  `FALSE` lex to their own dedicated token constructors (not `.identifier`), so any bare
  boolean literal was unparseable as an expression, which is exactly what TPC2.tla's
  generated `/\ TRUE` conjuncts hit. Both fixed; **`tests/TPC/TPC2.tla` now parses fully
  end-to-end.** `tests/TPC/TPC.tla` (the older variant) still fails, but for an unrelated,
  legitimate reason confirmed by testing, not a parser bug: it uses a pre-Apalache-format
  `@type` annotation dialect (`Channel[{type: string, agent: T}]`, square brackets and
  lowercase generic names) that predates this project's settled "same format as Apalache"
  decision (§2) — `TPC2.tla` uses the current syntax (`Channel({type: Str, agent:
  Address})`) and is the fixture to prefer.
- **New, found by the same testing pass:** `Expression.choose` (CHOOSE) and `LET`/`IN`
  are lexed (`.choose`/`.let`/`.in` tokens exist and are produced) but have no parser rule
  at all in `Parser_/TLAPlus.lean` — same shape of gap as the `.true`/`.false` one above,
  just not yet fixed since none of the current test fixtures (`PingPong`, `PingPongs`,
  `TPC`, `LamportMutex`) exercise CHOOSE or LET-IN. Worth a real implementation pass
  before trusting any input that uses either, not a quick two-line fix like `.true`/
  `.false` was.

### 9.3 CLI / UX — two remaining details
The flag surface is settled (§2). Two details the project owner flagged as genuinely
still open:
- **Join Calculus "flavors"** (e.g. `-t join[jocaml]`, `-t join[jerlang]`) — a possible
  way to select between different lowerings/encodings of the guarded-reaction dialect for
  different existing Join Calculus runtimes, tying into §9.1's open question about what
  happens after emission. Explicitly flagged as possibly not worth the complexity — don't
  build this unless asked.
- **`-p` (Go package name)** — whether this stays its own flag or gets folded into
  something like `-t go[package=...]`, or specified another way entirely, is still open.
- **`Int` machine-`int`-vs-`math/big` flag name** (mechanism resolved, §2/§9.21) — the
  project owner has settled that this is a compiler flag, target-specific to the Go
  backend, not a per-declaration annotation, but hasn't picked a concrete name yet. Likely
  fits the existing `-f<name>` (feature/config toggle) category alongside `-fno-color`,
  but pin down the actual spelling (and whether it's a boolean toggle or takes a value)
  before implementing — don't invent one silently.

Also unresolved: whether `-o`/`--output` names a file or a directory — matters more once
there are two backends with potentially different output shapes (Go may eventually emit
more than one file).

### 9.4 Join Calculus operational semantics — low priority
§5.6 points at where `Core/JoinCalculus/Semantics/` (RCHAM heating/cooling + reaction
rules, thesis Fig. 8.4.2–8.4.3, for both local and distributed solutions) would go, but
explicitly doesn't ask for it now: getting `Network2JoinCalculus` to actually compile is
the near-term goal, and having the compiler is enough on its own for the time being.
Formalizing the target language's own operational semantics only starts to matter once
there's appetite to prove something about that pass (a prerequisite for the correctness
question raised in thesis §8.7/this plan's §9.1) — revisit then, not before.

### 9.5 Minimal per-pass sanity-checking discipline — resolved, moved to §2
Resolved: `tests/regression/` holds small, hand-written, `accept_`/`reject_`-prefixed `.tla`
smoke tests (C-syntax only) per confirmed pass behavior, distinct from — and not a
replacement for — the still-deprioritized *formal, harnessed* example/regression suite. See
§2's "Example/regression suite" row for the decision and rationale.

### 9.6 Multicast compilation is undescribed for both backends
`multicast(x, [y ∈ e1 ↦ e2])` is explicitly part of the v1 language subset (§8), yet
neither backend's compilation scheme actually shows how it's compiled. §5.6's Join
Calculus scheme (the "Atomic blocks" bullet) only shows a single `send(c[α],e)` folded into
a reaction body — there's no bullet for emitting to a whole filtered set of recipients, and
it's unclear whether that means one atom per recipient (needing some encoding of a bounded
loop/comprehension inside a reaction body, which the target calculus doesn't obviously
support) or something else entirely. §5.7 says `Network2Go/PlusCal.lean` "already gets
essentially everything right" except lock inference, but doesn't say whether multicast
codegen is included in that "everything" or still needs new work — worth confirming by
reading the actual pass before assuming either way.

### 9.7 Runtime value representation in Go: numeric representation is the real open piece
TLA+ `Int`/`Nat` are unbounded, and FIFOs are (as far as this plan's grammar, §8, says)
uncapacitated; Go's integer types and channels are inherently bounded (`int64` wraps on
overflow; a Go `chan` is either unbuffered/synchronous or has a fixed capacity — never
truly unbounded). Per the project owner, **the numeric side is the genuinely open piece
here**: unbounded `Int`/`Nat` need an arbitrary-precision representation (e.g. a
`math/big`-backed encoding) to actually be sound relative to the TLA+ model. This is
solvable, but as a real library-level decision to make and implement once, consistently,
not something to leave implicit or default to native `int64` on. `lib/tlaplus.go` is
described (§5.7) as a "working reference" for `Seq`/`Set`/function/record encodings, but
doesn't settle what backs `Int`.

**Partially narrowed by the second July 2026 thesis revision (§5.7's new "Go
representations of TLA+ types" subsection):** the thesis itself now picks machine `int`
as the *default* `Int` encoding (for efficiency), with `math/big`'s `Int` offered as an
opt-in for specs that need genuine unbounded arithmetic. That settles that both
representations are wanted; the dispatch mechanism itself is now resolved (§2/§9.21): a
whole-program compiler flag, target-specific to the Go backend, not a per-declaration
choice. Exact flag name still undecided (§9.3).

The channel-capacity side is less clear-cut than an earlier draft of this plan made it
sound, and is flagged by the project owner as an unverified hypothesis rather than a
settled non-issue: because the lock-inference design (§5.7) already serializes atomic
blocks that touch shared state, a `send` blocking on a bounded Go channel shouldn't
change *which* transitions are actually enabled — at worst it should only slow execution
down, not alter behavior or invalidate whatever the source spec was checked or proved
against. Worth confirming once a concrete backend exists to actually test the claim
against, rather than assuming either way.

**Note this paragraph's "bounded Go channel" is doing double duty and may not mean what
it sounds like.** It's clearest for a same-process channel realized as a literal Go
`chan`, where blocking-vs-capacity is exactly the native Go semantics. But per §9.12,
`send(c, e)` to a *different* process almost certainly isn't a literal shared Go `chan`
at all (that can't span OS processes/machines) — it's a network send, whose "capacity"/
blocking behavior is a property of a socket and whatever buffering the runtime library
puts around it, not of Go's `chan` construct. This paragraph's reasoning (blocking only
slows one process down, doesn't change enabled-ness) may still hold either way, but it
was reasoned about the local-`chan` case; re-check it once §9.12 pins down what a
cross-process `Channel(τ)` actually compiles to.

**Known, accepted risk worth spelling out explicitly:** a block that blocks on a channel
op *while holding its component's lock* (§5.7) freezes every other block sharing that
lock — potentially including the process's own `T_rx` thread — for as long as the send
stays blocked. Per the project owner, this stays **local to the one process (agent)**
that's stuck; it isn't a cascading, system-wide deadlock, because what actually unblocks
it is the peer's own (user-written) code eventually processing/receiving the
corresponding message. So the real-world failure mode is "one process goes locally
unresponsive until its peer gets around to draining the channel," not "the whole
distributed system wedges" — still worth keeping in mind as a genuine, accepted
consequence of the locking design, distinct from the numeric-representation question
above.

### 9.8 `INSTANCE` support — resolved, out of scope for now, moved to §2
Resolved: `INSTANCE` is out of scope for the initial type checker (Phase 5/6, §7). See
§2's "Language-subset exclusions for the first type checker" row for the decision and
rationale; revisit if/when a program actually needs it.

### 9.9 `RECURSIVE` operator declarations — resolved, out of scope for now, moved to §2
Resolved: `RECURSIVE` is out of scope for the initial type checker (Phase 5/6, §7), same
row as §9.8 above. The annotation-seeded design below is preserved for whenever this is
picked up, but isn't being implemented now:

> If it's in scope, the natural design (worked through informally, but never written in
> until now) is to **require an explicit type annotation on the `RECURSIVE` declaration
> itself**, for every operator in the group: extend `Γ` with all the declared sibling
> types up front, then check each operator's body against its own annotation
> independently. This breaks the circularity a mutually-recursive group would otherwise
> create for a bidirectional checker with no other way to know `g`'s type while checking
> `f`'s body (and vice versa) — no constraint propagation or guessing across the
> recursive calls is needed, since each body just needs to match its own declared type.
> This is standard precedent (mutual `def`/`def` blocks in Coq/Agda/Lean always carry
> signatures; ML's `let rec ... and ...` is kept monomorphic for the same reason), and
> under this plan's rank-1-polymorphism discipline (no let-generalization, §5.3), it's
> close to *necessary* for decidability if any operator in the group is itself
> polymorphic, not just a convenience. If picked up: add the surface syntax (parser
> work, since neither prior-art checkout has it), add it to §8's language subset, and add
> this checking rule to §5.3.

### 9.11 `Ξ`'s disk cache — resolved, deferred entirely for now, moved to §2
Resolved: `Ξ` is in-memory only for the initial type checker (Phase 5/6, §7) — no disk
persistence, so no stale-cache correctness risk to invalidate in the first place. See
§2's "`Ξ`'s cache: disk persistence and invalidation" row for the decision and
rationale. The invalidation-scheme question below is preserved for whenever disk
persistence is actually added:

> §5.3's persistent, disk-backed `Ξ` cache (as originally described) would be keyed by a
> hash of each module's own source — which invalidates correctly when the *module*
> changes, but not when the *compiler* changes underneath it. Concretely: a bug fix in
> the checker, an updated standard-module stub (`Sequences`/`TLC`/`Naturals`/
> `FiniteSets`, §5.3), or the toolchain bump §2 already commits to could all change what
> a given module *should* type-check to, without touching that module's own source at
> all — so its cache entry's hash stays the same, and the stale, pre-change typed form
> keeps getting served on every subsequent run with no trigger to recompute it. Needs a
> decision when this is picked up: does the cache key grow a compiler/schema-version
> component (e.g. a version string or a hash of the checker's own relevant sources,
> bumped whenever anything that affects typing output changes), forcing a full cache
> invalidation on every such change? Or is there a lighter-weight alternative (e.g. a
> single global "cache format version" the whole `~/.local/config/.fugue` directory is
> stamped with, wiped wholesale on mismatch, rather than tracked per-entry)?

### 9.12 `send(c, e)`'s actual Go compilation scheme is unknown

**Partially narrowed by the third July 2026 thesis revision (commit `c2bbf8f`,
2026-07-11):** the thesis now explicitly resolves the adjacent question of whether
`Channel(τ)` needs a general-purpose Go value representation — it doesn't, because
channels "are not first-class citizens in Distributed PlusCal" (§5.7, §3.3). That answers
"what Go type does a channel value have" (none — a channel is never stored, passed
around, or put in a data structure the way an ordinary TLA+ value is; it only appears
indexed, `c[α]`, at a `send`/`receive` site). It does **not** answer this section's actual
open question, which is about wire mechanics, not representation: connection lifecycle,
serialization format, and how a channel's identity travels alongside its payload once
`send(c, e)` targets a different process. Everything below remains open.

§5.7 describes `Network2Go/PlusCal.lean` as "already gets essentially everything right"
except lock inference, and separately lists the hand-written `tests/*/{lib,nameserver}`
scaffolding (TCP/UDP address resolution, a name-server process) as directly reusable —
but nowhere does this plan actually say how these two things connect: what `send(c, e)`
concretely compiles to once `c` is addressed to a *different* process, possibly on a
different machine.

The natural shape, sketched here but **not confirmed against the actual pass or
committed to as a decision**: look up the target address (the `α` in `c[α]`, per §5.3's
`Channel(τ)` covariance) via the nameserver client; obtain a network connection to that
address (new per message, or pooled/persistent — unspecified); serialize the channel's
identity together with the payload `e` (the receiver may have several distinct channels,
so the identity has to travel with the message, not just the raw value); transmit it; on
the receiving end, some listener — the Go analogue of §5.6's Join Calculus `T_rx`
reaction — accepts the connection, deserializes, and appends the payload to the *local*
`inbox` variable for that channel, which is what `receive` already reduces to reading
from (§5.5). None of connection lifecycle, wire format/serialization, or how a channel's
identity is encoded on the wire is decided.

This also means `Channel(τ)`'s Go runtime representation is genuinely two different
things depending on which side of a `send` you're standing on: for the *receiver*, a
channel is (or feeds) a real local `inbox` sequence — the kind of thing a literal Go
`chan`/queue can realize, matching §5.3's "channels are encoded as `Seq(τ)`" framing. For
the *sender*, addressing a remote process's channel can't be a shared Go `chan` value at
all (that cannot cross OS processes, let alone machines) — it has to go through the
nameserver-plus-network path above instead. §9.7's Go-channel-capacity discussion should
be re-read with this split in mind (flagged there too): its reasoning was worked out
assuming a literal Go `chan`, which is at best only half the picture.

### 9.13 A "floating annotation" warning is blocked by the parser combinator library's backtracking, deferred

While scoping the annotation-placement-checking prerequisite for Phase 5 (§5.1, §2), a
warning for an annotation-shaped comment with *no* designated consuming site anywhere
nearby (as opposed to a real annotation attached to the *wrong specific role* at a real
site, §2/§5.1, which stays in scope and doesn't have this problem) was found to be
blocked by a genuine limitation in how `Parser_/Common.lean`'s `first` — and the vendored
`fgdorais/Parser` library's `first`/`orElse` it's built on — actually backtrack.

**The mechanism:** `ParserT ε σ τ m α := σ → m (Parser.Result ε σ α)`. `orElse`/`first`'s
failure branch only ever resets `Stream.Position` (an explicit field of `ParserT`'s own
type) — never anything inside the base monad `m`. Concretely: `first [parseAssume,
parseConstants, parseVariables, parseOperator, ...]` (`parseDeclaration`,
`Parser_/TLAPlus.lean`) tries `parseConstants`/`parseVariables` before reaching the
correct `parseOperator` alternative; both of the first two use `lexeme (pure ()) *>
token .constants`/`(.variable <|> .variables)` — i.e. they generically skip past
(`lexeme`/`ws`) whatever comment sits there *before* checking their own keyword and
failing. Any `m`-side-effect performed during that skip (e.g. an accumulated warning)
survives even though the *stream position* is correctly rolled back for the next
alternative to retry — because `first`'s reset only touches `σ`, not `m`. This isn't
specific to `MonadState` vs. `MonadWriter`: both are built over base monad `Id`, which
has no failure/short-circuit semantics of its own for either to be discarded against: 
`m`'s effects are fully executed as an ordinary part of running `p s`, before `first`'s
`.ok`/`.error` match on the *result* even happens. **Confirmed this generic `lexeme (pure
())`-before-keyword skip is load-bearing, not an oversight** — per the project owner, it
is what allows comments to legally appear between/before declarations at all without
risking being mistaken for consumed annotations; removing it isn't an option.

Fixing this properly would mean giving `first`/`orElse` real "commit" semantics (a
failure after any input has been consumed propagates immediately rather than retrying
sibling alternatives, unlike today's unconditional-reset backtracking) — a change to the
core parsing combinators themselves, not a narrow fix, and one that risks breaking other
grammar productions that currently rely on retry-after-partial-consumption. **Deferred,
per the project owner: not attempted now.** The annotation-placement prerequisite for
Phase 5 proceeds with only the structural-role-mismatch half (a real annotation captured
at a real site but attached to the wrong specific role there — e.g. `@parameter` on a
quantifier binder — which runs on the already-successfully-parsed AST and has none of
this problem, §2/§5.1) — the "nothing consumes this at all" half is out of scope until
`first`/`orElse`'s backtracking semantics are revisited.

### 9.14 Warnings that precede a hard error within the same pass call are lost

`Driver/Modules.lean`'s `compileModule` now accumulates every stage's warnings into one
local list and flushes them all at once, at the point a module's outcome
(`Built`/`Replayed`/`Failed`) becomes known — matching `lake build`'s own timing instead
of printing warnings as they're produced, interleaved before that point.

This only fixes ordering *across* stages/modules: warnings from an already-finished stage
correctly survive a *later* stage's failure (or a dependency's failure) and still get
shown. It does **not** fix loss *within* a single stage: `parseModule`
(`Parser_/TLAPlus.lean`) and `algo.runDesugarer` (the PlusCal desugarer,
`Desugarer/PlusCal.lean`) both return `Error ⊕ (Value × List Warning)` — the error
branch carries no warnings at all, so any warnings that same call accumulated
(internally, via `ParserWarningM`/the desugarer's own `StateT (List DesugarWarning)`)
before hitting a fatal error in the *same* call are structurally unreachable from the
driver, no matter how `compileModule` threads its own local list around the call. This is
visible directly from the shape of the match arms in `compileModule` itself (`.inl e =>
throw ...` binds nothing but `e`; `.inr (v, ws) => ...` is the only branch with access to
`ws`) — confirmed, not just suspected, by reading `parseModule`'s own definition, which
does compute `warnings` unconditionally (the `StateT` always runs to completion) but
discards it on the `.inl` branch rather than pairing it with the error.

Fixing this for real needs `parseModule`/`algo.runDesugarer`'s own signatures changed so
warnings ride alongside *both* outcomes — e.g. `(Unexpected e ⊕ Module) × List
ParserWarning` instead of `Unexpected e ⊕ (Module × List ParserWarning)` — plus updating
`compileModule`'s match arms to pull warnings out of both branches. **Deferred, per the
project owner: filed as a longer-term issue, not fixed now.** A module whose source has
both a warning-worthy construct and a later hard parse/desugar error in the same pass
call will not show that warning until this is revisited.

### 9.15 `[Receive]`'s channel/reference coercion — resolved, moved to §5.3/§2

Surfaced while implementing `Elaborator/Subtyping.lean`: `Channel` is covariant, but
channel-typed *expressions* only ever get an identity coercion in practice (no general
term former exists to wrap one, and none is needed — channels never change runtime
representation the way `Str`/`Seq(Int)` might). The real question was the **received
value**: its type may be narrower than the destination reference's, and unlike
`[Send]`'s payload, there's no elaborated expression at check time to hand a coercion to
— `receive` produces its value at runtime, from the network, not from any sub-expression
this checker elaborates. **Resolved:** synthesize both types, `subtype` them directly,
and store the resulting `Coercion` on the `receive` statement node itself, carried
unapplied through `Typed2Guarded` (§5.4, none of whose four subpasses touch `receive`'s
shape) and only actually spliced into generated code by `Guarded2Network` (§5.5), the
first pass where a `receive` becomes a concrete buffered read with real code around it.
See §5.3, §5.5, §2.

### 9.16 `LAMBDA` — designed, not implemented; filed here after being found only in scratch-plan form

Surfaced while implementing `Elaborator/Expressions.lean` (§5.3): the thesis has typing
rules for `LAMBDA` (Fig. 3.1.4), but neither `SurfaceTLAPlus.Expression` nor
`CoreTLAPlus.Expression` has a constructor for it, and the lexer has no `LAMBDA` token
(`Parser_/TLAPlus.lean` has only a dangling `-- LAMBDA` comment). A full design for this
already exists — worked out during Phase-5 planning, in `/Users/ghilain/.claude/plans/
fuzzy-drifting-karp.md`, but never migrated here nor implemented — recorded below so it
isn't scratch-file-only. **Decision for now (confirmed with the project owner while
implementing `Elaborator/Expressions.lean`): `LAMBDA` stays out of scope. `Expressions.lean`
ships with no `LAMBDA` case** (there is no AST node to match on anyway); revisit as its
own, separately-scoped addition if a program actually needs it — implementing it for real
means touching `Parser_/TLAPlus.lean`, `Core/SurfaceTLAPlus/Syntax.lean`,
`Core/CoreTLAPlus/Syntax.lean`, and `Desugarer/TLAPlus.lean`, all in phases §7 already
marks done, not just the checker.

The design, preserved for whenever this is picked up:
- **Checking-only without an annotation** (matches the thesis, Fig. 3.1.4) — `Γ, x1:τ1,
  ..., xn:τn ⊢ e ⇓ τ ⟹ Γ ⊢ LAMBDA x1,...,xn : e ⇓ (τ1,...,τn)⇒τ`, requiring the whole
  `LAMBDA`'s expected type to already be known.
- **Gains a synthesis form once every binder carries a `@type` annotation** — mirroring
  unbounded quantification's own trick (an annotated binder is what unlocks synthesis,
  not merely a hint): `(LAMBDA (* @type: Int; *) x : x + 2)(3)` should synthesize, even
  though the thesis's own unannotated example (p. 10) still can't (rewritable via
  `LET`-`IN` instead — except this project's AST has no `LET`-`IN` node either, confirmed
  absent, so that specific rewrite-workaround doesn't apply here regardless).
- **New AST work needed:** a `.lambda (binders : List (String × α)) (body : Expression α)`
  constructor on both `SurfaceTLAPlus.Expression`/`CoreTLAPlus.Expression`, a per-binder
  annotation slot so `tryParseAnnotations` can attach `@type` per binder (matching
  `parseQuantifierBound`'s existing pattern), a new lexer token, a new parser rule, a
  pass-through desugarer case, and both the checking and (conditional) synthesis rules in
  `Elaborator/Expressions.lean`.

Separately, this file's own `Operator`-vs-`Operator` structural subtyping rule
(`Elaborator/Subtyping.lean`, Fig. 3.1.8) already only ever produces an identity coercion,
precisely *because* there's no `LAMBDA`-equivalent (or any) way to eta-expand into a new
first-class operator value — so this gap has already surfaced as a concrete limitation
once, not just a hypothetical.

### 9.17 Most temporal/action operators aren't parsed yet — `WF_`/`SF_` specifically need a lexer change

Surfaced while implementing `Elaborator/Expressions.lean` (§5.3): confirmed that
`UNCHANGED`/`ENABLED`/prime (`'`)/`~>`/`-+>`/`[]`/`<>` already have real surface syntax
(`Core/SurfaceTLAPlus/Syntax.lean`'s `Prefix`/`Infix`/`PostfixOperator` enums) and desugar
to plain `opCall`s onto builtin `var`s (`Desugarer/TLAPlus.lean`), so `Elaborator/
Expressions.lean`'s generic `OPERATOR CALL` rule already covers them with no dedicated
case. **But most temporal/action operators are not actually parsed yet** — per the
project owner, weak/strong fairness (`WF_e(A)`/`SF_e(A)`, thesis Fig. 3.1.5) are the
concrete example, and are a genuinely non-trivial lexing problem, not just an unwritten
parser rule: `WF_e` needs to lex as **two** tokens (a fixed `WF_` keyword, then the
identifier `e`), but ordinary maximal-munch identifier lexing would otherwise swallow
`WF_e` whole as one identifier token.

**Idea recorded here, not implemented (deferred, per the project owner):** modify the
lexer's keyword checker so that, given an identifier-shaped token starting with `WF_` or
`SF_`, if there are leftover characters after that prefix that don't themselves start
with `_` or a digit (i.e. the leftover still looks like a valid identifier start), split
it into the `WF_`/`SF_` keyword token followed by a separate identifier token for the
remainder, rather than emitting one combined identifier token.

Left as **future work, not started** — revisit whenever a program actually needs
`WF_`/`SF_` (or the other still-unparsed temporal/action operators) checked.

### 9.18 Unary minus and binary minus share one canonical spelling — resolved, moved to §5.3

Surfaced while writing `Elaborator/Declarations.lean`'s builtin prelude (§5.3 task 7):
`Desugarer/TLAPlus.lean`'s `PrefixOperator.canonicalName`/`InfixOperator.canonicalName`
both collapsed to the identical string `"-"` for unary (`-x`) and binary (`x - y`) minus,
and `Γ` maps a name to exactly *one* type, so `builtinContext` couldn't seed both arities
at once. **Resolved per the project owner**: give unary minus its own canonical spelling,
`"-."` — the same disambiguating trick "Specifying Systems" itself uses to tell the two
apart. **Surface syntax is unchanged** — `-x` still parses exactly as it did before this
fix (the project owner was explicit that the parser itself is not to change); only the
*internal*, `Γ`-lookup-facing name `PrefixOperator.canonicalName` produces for it changed,
from `"-"` to `"-."`. `Elaborator/Declarations.lean`'s `builtinContext` now carries both:
`"-" : (Int, Int) ⇒ Int` (binary) and `"-." : (Int) ⇒ Int` (unary), no collision.

### 9.19 `builtinContext`'s operators eventually belong in real `EXTENDS`-gated builtin modules — resolved

Raised by the project owner right after `Elaborator/Declarations.lean`'s `builtinContext`
landed (§5.3 task 7). That prelude was a deliberately flat, always-on approximation —
`+`/`-`/`-.`/`*`/`..`/comparisons/`Nat` properly belong to TLA⁺'s `Naturals` module, and
`Len`/`Head`/`Tail`/`Append` properly belong to `Sequences`, both real `EXTENDS`-gated
modules in the actual language rather than always-present primitives.

**Resolved**: these operators now live as real declarations in `Driver/Modules.lean`'s
`builtinModules["Naturals"]`/`builtinModules["Sequences"]` entries (`naturalsDeclarations`/
`sequencesDeclarations`) instead of in `builtinContext`, which now only carries genuinely
`EXTENDS`-independent operators (equality, boolean connectives, core set theory). A module
only sees `+`/`Len`/… via an actual `EXTENDS Naturals`/`EXTENDS Sequences`, resolved through
the same `Γ₀`-merge machinery `compileModule` already uses for ordinary dependencies.
Verified against the four hand-verification fixtures (§5.3 tasks 9/10): `LamportMutex3.tla`/
`TPC2.tla` both `EXTENDS Naturals, Sequences` directly, so gating didn't regress either.
Each declaration only needs a name/type binding (`Decl.bindings`, what the `Γ`-merge step
actually consults) — bodies are never re-examined, since standard-library operators get
replaced by backend-native implementations at code-generation time regardless of what their
"definition" says. Still, each body is a genuinely well-typed value of its own operator's
return type where one exists (`intZero`/`emptySetInt`/`emptySeqOfVarA`, `Driver/Modules.lean`),
not an arbitrary placeholder — the one exception is `Head`'s bare `a` return, a rigid type
variable with no witness value at all, so it keeps a (harmless, never-checked) fake `Int` body.

**Follow-up, also resolved**: builtin-`EXTENDS`ing-builtin (`Sequences` itself `EXTENDS
Naturals`, matching real TLA⁺). This section originally assumed `resolveModule`'s existing
recursion "already generalizes" to this for free — false: its `.builtin` case returned a
builtin candidate directly without ever resolving *its own* `extends` field. Fixed by making
`.builtin` resolve `mod.extends` the same way `.file` does (recursing into `resolveModule`
for each dependency, merging `depMod.declarations₁ ++ depMod.declarations₂` into the
returned module's own `declarations₁`), and giving `Sequences`'s table entry
`«extends» := ["Naturals"]`. A module that only `EXTENDS Sequences` (not separately
`Naturals`) now correctly sees `Naturals`'s operators too, transitively.
`Bags`/`TLC`/`FiniteSets` remain genuinely empty stubs — populate the same way once real
test input needs a specific operator from one of them.

**Second follow-up, also resolved**: `Bags`, `FiniteSets`, and `Integers` are now populated too
(`bagsDeclarations`/`finiteSetsDeclarations`/`integersDeclarations`, `Driver/Builtins.lean`),
cross-checked against the real modules'
[source](https://github.com/jameshfisher/tlaplus/tree/master/org.lamport.tla.toolbox/StandardModules).
`RealTime`/`Reals` are deliberately excluded (never ported, out of scope). `TLC` deliberately
stays an empty stub. Each new module's `«extends»` mirrors its real module's *full*
top-of-file dependency list, `LOCAL INSTANCE` included, not just plain `EXTENDS` — corrected
after an initial pass wrongly treated `LOCAL INSTANCE` as "not a dependency of this table" by
analogy with real TLA⁺'s re-export rule; the project owner clarified `«extends»` here should
track every declared dependency regardless of `LOCAL`. So `FiniteSets` `«extends» :=
["Naturals", "Sequences"]` and `Bags` `«extends» := ["TLC", "Naturals"]`, both `LOCAL`-only
in the real module. A `LOCAL`-*declared* helper (`Bags`'s `Sum`, a definition, not an import) is
still excluded from the exported declaration list, matching how `Sequences`/`FiniteSets` never
export their own `LOCAL` definitions either — that exclusion is unaffected by this fix. One
genuine gap surfaced along the way, initially accepted as a known limitation, since resolved
(third follow-up below): `EmptyBag` is 0-ary and polymorphic in real TLA⁺, but this project's
checker only froze a `Typ.var` on an operator *call* (`specializeOperator`) — a bare 0-ary
declaration was bound in `Γ` at its literal declared type with no generalization step at all
(`Elaborator/Declarations.lean`'s `[], retTy` case in `checkDeclaration`). So `EmptyBag :
Function(a, Int)` was rigid: it resolved fine the first time it pinned some metavariable, but
failed if used where that metavariable was already pinned to a different concrete element type
by another operand in the same expression (e.g. `SetToBag(S) (+) EmptyBag`).

**Third follow-up, also resolved**: the `EmptyBag` gap above, by unifying let-generalization at
`Γ`-reference instead of at operator-call. `Elaborator/Monad.lean`'s `Context` now maps each name
to a `Binding` (a `Typ` plus `isScheme : Bool`) rather than a bare `Typ`. A top-level
`operator`/`function` *definition* — any arity, `EmptyBag` included, `builtinContext`'s entries
included — is always a scheme; `CONSTANT`/`VARIABLE` declarations and every ordinary binder
(operator/function parameters, quantifiers, `CHOOSE`, `EXCEPT`, PlusCal variables/channels,
`extend`/`extendAll`) stay monomorphic, matching prior behavior exactly (`Elaborator/
Context.lean`). `Elaborator/Expressions.lean`'s `inferExpr`'s `.var` case now does the one
freshening step, for any scheme reference, called or not
(`Elaborator/TypeUtils.lean`'s new `specializeType`, replacing `specializeOperator`); `.opCall`
no longer needs its own specialization step, since the callee's type is already specialized by
the time `inferExpr` returns it — a simplification, not just a fix, since the two mechanisms
were doing the same freshening at two different points for two different subsets of
declarations. `Driver/Modules.lean`'s `Decl.bindings` computes `isScheme` from a declaration's
own arity (`true` for every `.operator`/`.function`), so `EmptyBag` becomes a scheme with zero
changes needed to `Driver/Builtins.lean` itself. The key risk considered and traced by hand: an
ordinary binder like `x` in `Id(x) == x` must never be marked a scheme (it's fixed for the scope
of `Id`'s own body — conflating the two would risk mvar-to-mvar comparisons that could leave a
metavariable stuck unconstrained) — `extend`/`extendAll` are hardcoded to always insert
monomorphically, so this can't happen by construction.

**Fourth follow-up, also resolved**: `EmptyBag (+) EmptyBag` (both operands *consistently*
annotated at the same rigid type, e.g. `@type: a -> Int; x == EmptyBag (+) EmptyBag`) was still
wrongly rejected right after the third follow-up landed, with `metavariable with more than one
recorded upper bound — not yet supported` — caught by the project owner questioning why this
case, which should trivially resolve (`a` is rigid and consistent across both operands), didn't.
Root cause: a genuine bug in `Elaborator/Subtyping.lean`'s `subtype`, pre-existing but newly
exposed by the third follow-up (every `.var` reference, not just an `opCall`'s callee, now
independently freshens its own metavariable, so two now-distinct-but-equal-target metavariables
being compared against a *third*, shared one — e.g. two separate `EmptyBag` references both
checked against `(+)`'s own single freshened parameter type — became far more common). `subtype`
's `.mvar a, .mvar b` case never checked `a == b` before falling into its `none, none` branch, so
comparing a metavariable against *itself* while still unresolved (which is exactly what happens
resolving `Elaborator/Resolution.lean`'s `resolveExprMVars`'s `.mvar n e` reflexivity check,
`subtype b b`, once `b` is itself an unresolved `.mvar`) spuriously recorded a fresh,
self-referential pending bound instead of trivially succeeding — contradicting that very call
site's own comment ("`b <: b` always succeeds reflexively... unreachable"), which assumed this
case couldn't arise. Two such spurious self-bounds accumulating (one per `EmptyBag` reference)
on top of the one genuine bound (the outer annotation's `a`) tripped the "more than one bound"
guard. **Fix**: `subtype`'s `.mvar a, .mvar b` case now checks `a == b` first and returns
`.success .id` immediately, before ever consulting `assigned?`/adding any bound. Verified this
doesn't just paper over the case: a *genuine* element-type conflict (`SetToBag` over an `Int`
set `(+)` a `SetToBag` over a `Bool` set) still correctly fails, with a clean `Expected type
..., got ..., no coercion exists` error, not the "more than one bound" message — the fix only
short-circuits the truly-reflexive case.

Separately noticed while confirming the conflict case above still fails correctly: its error
message read `Expected type (?0) -> Int, got (?2) -> Int`, showing raw metavariable ids instead
of `Int`/`Bool` even though both were already resolved by the time the error was thrown (each
pinned by its own `SetToBag` call before the conflicting comparison ran) — `TCError`'s
`Typ`-carrying variants are never substituted against the metavariable context before being
embedded, since `msgOf`'s pretty-printing is a pure function with no access to it.
`Elaborator/Resolution.lean` gained `resolveTypeMVarsForDisplay` (a non-throwing sibling of the
existing `resolveTypeMVars`, factored through a shared `resolveTypeMVarsWith`, that leaves a
genuinely-unresolved metavariable as `?n` instead of erroring), applied at the two
`.failedToConvertTypes` throw sites (`Elaborator/Expressions.lean`'s `[Subtype]` fallback,
`Elaborator/PlusCal.lean`'s `.receive` case) — the conflict case above now correctly reads
`Expected type Int -> Int, got Bool -> Int`. The same raw-metavariable-id risk exists in
principle for every other `Typ`-carrying `TCError` variant (`notASetType`, `notAnOperatorType`,
…), but none of those were actually observed to hit it, so they're left as-is for now rather
than speculatively touched.

### 9.20 Lock inference (`Network2Go`, §5.7) — resolved, moved to §5.7

Surfaced by cross-checking the July 2026 `reference/thesis.pdf` revision against this plan:
thesis §7.1 (previously a stub) turned out to specify a materially different lock-inference
algorithm ([HFP06]-derived, per-variable locks with domination-based merging) than the
connected-component, one-lock-per-block scheme §5.7 had already committed to. Asked the
project owner directly; **resolved: switch to the thesis's algorithm**, now that it's
written up as the primary spec. §5.7 has been rewritten to describe it in full; this entry
is kept only as a pointer to that decision.

### 9.21 `Int` machine-int vs. `math/big` dispatch mechanism — resolved, moved to §2

Surfaced by the second July 2026 `reference/thesis.pdf` revision (§7.2.1.1, folded into
§5.7 above): the thesis commits to *two* Go encodings for TLA+ `Int` — machine `int` by
default, `math/big`'s `Int` as an opt-in for specs needing genuine unbounded arithmetic —
but didn't say what selects between them. Asked the project owner directly; **resolved: a
compiler flag, target-specific to the Go backend** (whole-program, not per-declaration) —
see §2's new row. The flag's concrete name is still undecided, tracked as the third bullet
of §9.3 rather than as its own entry here. Still applies: this flag interacts with §9.7's
channel-capacity discussion and with `lib/tlaplus.go`'s existing `Seq`/`Set`/function
encodings, which would need to be generic over (or duplicated across) both numeric
backings if a single spec is ever allowed to mix them — that composition question isn't
resolved by picking the flag mechanism, only by-value-vs-by-flag was.

### 9.22 Name-provenance: `Driver`-level side table, or tagged on the AST by the elaborator? — resolved, moved to §2

Surfaced while starting the well-formedness checking implementation (§5.2a, task 1):
`~/.claude/plans/jolly-chasing-book.md`'s first pass at provenance plumbing
(`CacheEntry.provenance`, `MonadForeignLookup` returning a `Std.HashMap`) was written up
purely to serve checks 2(c)/3's cross-module lookup need, reconstructed in `Driver/Modules.
lean` *after* type checking. The project owner first pointed out `Network2Go` (§5.7) needs
the exact same fact later — given a builtin-looking operator call like `+`, whether it
resolves to the real `Naturals` builtin (§9.19) or a user override declared in the compiled
module itself, which decides native-Go-operator vs. call-into-user-code codegen — then, once
that generalization was underway, raised the sharper objection: the elaborator already
resolves every `.var` through `Γ` and already knows, right there, whether a name is a binder
or a top-level declaration and which module the latter came from, so reconstructing it again
afterward as a side table duplicates work already done, with strictly less information
available (no operator/function body, worse error messages). Asked the project owner
directly; **resolved: tag `Binding` with its origin at `Γ`-construction time and bake that
origin onto `TypedTLAPlus.Expression.var` itself**, so it survives past `Γ` (discarded after
checking) into the checked AST — see §2's new row for the concrete shape. Superseded the
`CacheEntry.provenance`/table-based design before any of it was implemented.

### 9.23 Three regression fixtures parked as `skip_*`, pending parser/desugarer fixes — open

Found while confirming `PLAN.md` §9.22's origin-tagging work didn't regress anything: running
`tests/regression/run.sh` (its own `skip_*` convention — a file with that prefix is skipped and
reported yellow, never run, excluded from the pass/fail tally) turned up three fixtures broken
for reasons unrelated to origin-tagging (confirmed by failure category — parse-time and
desugaring-stage errors, both entirely upstream of anything origin-tagging touches). Renamed
from `accept_*` to `skip_*` rather than left failing or deleted, pending an actual fix:
- `skip_function_definition_multi_arg_tuple_domain.tla` — parser rejects
  `f[x \in S, y \in T] == ...`'s multi-arg function-literal domain syntax
  (`unexpected identifier f`).
- `skip_unbounded_choose_with_expected_type.tla` — parser rejects a bare
  `CHOOSE m : m = m` used as a `with`/variable initializer (`unexpected keyword 'CHOOSE'`).
- `skip_function_literal_cartesian_product_binder.tla` — `\X` (Cartesian product) is either
  not desugared to its canonical operator name, or that name is missing from
  `builtinContext`/`Naturals`'s declarations (`Unbound variable` \`\X\`).

Not investigated further yet — first two look like `Parser_/TLAPlus.lean` gaps, third looks
like a `Desugarer/TLAPlus.lean`/`Driver/Builtins.lean` gap, but neither confirmed by tracing the
actual code. TODO: fix each at the root (parser/desugarer/builtins), rename back to `accept_*`,
re-run the full suite once done — don't just patch the fixture unless it turns out to encode an
unsupported/wrong construct (check against this plan's language subset first).

### 9.24 `^+`/`^*`/`^#` (postfix action-closure operators) have no documented typing rule — open

Surfaced while implementing `WellFormedness/Restrictions.lean` (§5.2a, task 8): giving
`[]`/`<>`/`ENABLED`/`UNCHANGED`/`'` real `builtinContext` entries (so the no-bare-temporal check
can actually fire, rather than these names just hitting `unboundVariable` first) needed their
typing rules — found in `reference/thesis.pdf` §3.1.3.4/3.1.3.5 (Figures 3.1.4/3.1.5) for all
five. `^+`/`^*`/`^#` (`Core/SurfaceTLAPlus/Syntax.lean`'s `PostfixOperator`) have **no typing
rule anywhere** — not in the thesis, not standard TLA⁺ as far as traced. Asked the project
owner directly; **resolved for now: leave them unbound in `builtinContext`** — referencing one
still fails at `unboundVariable`, same as today, no regression. Their canonical names are still
included in `WellFormedness/Restrictions.lean`'s check-3 name list for forward-compatibility,
but that coverage is currently inert (unreachable) for the same reason check 3 itself was
inert before this task added the other five bindings. Matches how `WF_`/`SF_` are already
deferred, unlexed, per §9.17 — revisit alongside that whenever a program actually needs one of
these three checked (or their real meaning is tracked down).

### 9.25 Three well-formedness checks (well, two and a half) are currently unreachable — the *rule* is right, only the parser/type-checker can't produce the input yet

Surfaced while writing `tests/regression/` fixtures for `WellFormedness/Restrictions.lean`/
`WellScoped.lean` (§5.2a, task 11) — confirmed by reading the parser, not just guessing:
- **Check 2(b)'s `nonEmptyLocalChannels`** (a process's own `localState.channels`/`.fifos` must
  be empty): `Parser_/PlusCal.lean`'s `parseProcess` hardcodes `channels := []`/`fifos := []`
  when building a process's `localState` — it never even attempts to parse `channels`/`fifos`
  syntax at process level, only `variables`. No fixture can exercise the reject side of this
  check; it stays defense-in-depth only, exactly as `PLAN.md` §5.2a's own task list anticipated
  for this specific check ("first confirm whether the parser can even produce this shape").
- **Check 3's `unboundedQuantifier`**: an unbounded `\A x : P`/`\E x : P` is parseable but its
  bound variable's type can *never* reach an annotation under the current grammar
  (`parseQuantifier`'s unbounded branch is bare `parseIdentifier`, no `tryParseAnnotations`
  call) — confirmed by `reject_unbounded_forall_missing_annotation.tla`, an existing fixture
  whose own comment already states this ("every unbounded `\A`/`\E` without a domain is a
  guaranteed type error under the current grammar"). So it always fails at
  `TCError.expectedTypeAnnotation`, before well-formedness ever runs, *except* unbounded
  `CHOOSE x : P` in a checking position (`Elaborator/Expressions.lean:146`'s `[Unbounded
  choice]` rule *does* succeed there, ignoring any annotation and using the expected type
  instead) — but `CHOOSE` has **no parser rule constructing it at all** (confirmed: `CHOOSE` is
  only ever a lexer token in `Parser_/TLAPlus.lean`, never consumed by any expression-parsing
  rule), matching `skip_unbounded_choose_with_expected_type.tla`'s already-filed gap (§9.23) —
  same root cause, not a new one. So `unboundedQuantifier` has no reachable trigger today at
  all, on either quantifier form.
- **Check 1's `channelInExpression`, specifically via `receive`'s destination `r`** (not the
  check as a whole — `reject_channel_in_expression.tla`'s `assert ch = ch;` still exercises it
  directly). Surfaced *after* this section was first written, once `sendable` landed (§5.3,
  above): the only way to get `r` itself typed as Channel-shaped past type-checking at all was
  a channel-of-channels source (`Channel(Channel(τ))`, needed for `Channel`'s reflexivity-only
  subtyping to accept the `receive`), which `sendable` now rejects outright, at declaration
  time, before a `receive` statement referencing it is ever reached. The original
  `reject_receive_into_channel.tla` fixture was repurposed into
  `reject_channel_element_channel.tla` (testing `sendable`'s channel-exclusion directly, no
  `receive` needed) rather than kept pretending to exercise well-formedness.

Not a bug in any of these three checks' own logic — all are exercised and confirmed correct via
direct calls during testing, just not through a real `.tla` fixture end-to-end. No fixtures were
written for the first two (`reject_local_process_channel.tla`, `reject_unbounded_quantifier.tla`,
both skipped rather than force-fit); the third has no dedicated fixture of its own for the same
reason, but the check itself remains exercised via other inputs. Revisit once: (a) the parser
gains process-level `channels`/`fifos` parsing (probably never worth doing, given check 2(b) is
explicitly "defense-in-depth" and the restriction is already unconditional), (b) `§9.23`'s
`CHOOSE`-parsing gap is fixed (which would also make unbounded `CHOOSE` reachable) or unbounded
`\A`/`\E` gains annotation support (a real grammar change, bigger than §9.23's fix), or (c) some
other route to a channel-shaped `receive` destination `r` is found that doesn't require an
unsendable channel-of-channels declaration (none currently known — `Channel`'s reflexivity-only
subtyping and the lack of any other channel-shaped-type constructor make this look structurally
unlikely, not just unimplemented, but not proven impossible).

### 9.26 Should intrinsic operators get dedicated AST constructors instead of `opCall`? — open

Surfaced while planning the `Typed2Computable` pass (`ComputableTLAPlus`/
`ComputablePlusCal`, dev-plan Phase 7, `.claude/plans/nifty-jumping-anchor.md`). Every
builtin operator, intrinsic or stdlib, is represented uniformly as `.opCall (.var name _
origin) args` — no dedicated `Expression` constructor per operator. This keeps the
type checker's op-call rule uniform (one generic rule plus a `Γ`/`builtinContext` lookup,
not one typing rule per builtin), but pushes every downstream pass that needs to
special-case a builtin into re-deriving its own string/`Origin` match against the same
representation — `WellFormedness/Restrictions.lean`'s `reservedTemporalActionNames`
today, `Typed2Computable`'s own computability classification tomorrow, and (per
`Driver/Builtins.lean`'s own module doc) both backends unconditionally, since
stdlib operators "get replaced by backend-native implementations at code-generation time
regardless of what their 'definition' says." A shared recognizer table
(`Core/TypedTLAPlus/Builtins.lean`, tasklist item 1 of the `Typed2Computable` work) is
the near-term fix, decided and in progress — this question is about whether that's
enough long-term, or whether it's worth going further.

**Scope of the question, per the project owner: intrinsics only** — `builtinContext`'s
own ~14 genuinely `EXTENDS`-independent entries (`=`, `/=`, `/\`, `\/`, `=>`, `<=>`,
`\neg`, `\in`, `\notin`, `\subseteq`, `\cup`, `\cap`, `\`, `DOMAIN`, plus the temporal
ones tracked separately in §9.24) — **not** operators declared via vendored stdlib
modules (`Naturals`/`Sequences`/`Bags`/`FiniteSets`/etc., §9.19's `builtinModules`
table). The two groups differ in exactly the way that matters here: intrinsics are a
small, closed, permanent set baked into every module regardless of `EXTENDS`, while
stdlib operators are open-ended declarations in an ordinary (if hardcoded) `Module` —
giving *those* dedicated constructors would mean a constructor per `Len`/`Head`/`+`/…,
undermining the whole point of representing them as ordinary declarations (§9.19) rather
than special-cased primitives.

Not resolved — revisit once `Typed2Computable`'s shared recognizer (task 1 above) is
built and its shape (closed enum vs. category-tagged table, also undecided) is known;
that'll make the actual remaining pain (if any) concrete rather than hypothetical.

