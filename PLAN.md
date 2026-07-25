# Fugue — a compiler from Distributed PlusCal to the Join Calculus and Go

**Status:** phases 1–9 done, phase 10 (`Guarded2Network`) in progress — pass ported,
refinement proof pending. See §7.
**Companion files:** `INSTRUCTIONS.md` (working conventions), `OPEN_QUESTIONS.md`
(open questions, referenced below as `§9.x`).

Three sources of prior art: public mirror `github.com/mesabloo/fugue` (branches `main`,
`develop`, `go-semantics`, `lock-inference`, `docs`), private checkout
`~/Documents/distpcal-compiler` (origin `github.com/mesabloo/distpcal-compiler`, branches
`main`, `develop`, `compiler`, `go-semantics`, `lock-inference`, plus uncommitted local
`typechecker`), and thesis `Generating Distributed Programs from Formal Specifications`
(`reference/thesis.pdf`). None reused wholesale (§2's carry-over row), but its design drives
most of this plan and its gaps define most open work. §3 says how to read each source.

---

## 1. Goals and non-goals

**Goal.** Compiler, written in Lean 4, from Distributed PlusCal (TLA+ modules with
embedded PlusCal algorithm using Distributed PlusCal's `send`/`receive`/`multicast`/FIFO
extensions) to two independent backends:

1. **Join Calculus** — guarded-reaction dialect close to Fournet & Gonthier's original
   calculus, extended with name-server (`register`/`lookup`) for distributed addressing.
   More "formally tractable" target: reaction semantics line up almost exactly with
   Network PlusCal's atomic blocks, which is why the thesis develops it as a compilation
   target in its own right, not a stepping stone to Go.
2. **Go** — real, runnable, idiomatic-ish Go source, goroutines and channels, depending
   on a small runtime library this project owns.

**Guiding ambition.** End goal: *formally verified* compiler — every pass eventually
comes with proof that target-program behavior refines source-program behavior, using
trace/simulation framework sketched in `VerifiedCompiler/` (§6). Full end-to-end
verification not expected within this plan — north star, not milestone.

**Non-goals.**
- Not a general-purpose TLA+/PlusCal tool — only the Distributed PlusCal fragment prior
  art uses (bounded-buffer FIFOs, channels, `multicast`, addresses) in scope.
- Not reproducing the domain-theoretic Go denotational semantics research
  (`go-semantics` branch) as near-term work — real, worth returning to, but big
  (ultrametric spaces, contraction mappings, ~20 files topology infra) and orthogonal to
  a working, testable pipeline. See §6.4.
- Not building JoCaml-compatible, un-guarded Join Calculus emitter. Compiler targets the
  guarded dialect the thesis describes; how (or whether) that gets executed stays open,
  §9.1.

---

## 2. Decisions

| Question | Decision |
|---|---|
| Go and Join Calculus backend relation? | **Independent siblings.** Both compile directly from `NetworkPlusCal`, two separate pass chains (`Network2Go`, `Network2JoinCalculus`). No sequencing between backends. Matches thesis: Join Calculus chapter targets Network PlusCal directly, not Go. |
| How much of existing prototypes carries over? | **Fresh domain code, reused generic infra, three ported exceptions.** `Extra/` (data structure lemmas), `VerifiedCompiler/` (trace + refinement framework), `ProgressBar/` (CLI spinners), `Common/` (positions, diagnostics, pretty-printing — generic, not tied to one AST) vendored as scaffold, adapted not copied blind. Most AST definitions, semantics, compiler passes (desugarer, checker, every `*2*` pass but Guarded→Network) written fresh, prototypes used only as design reference. Three ported exceptions: **lexer/parser** (§5.1), **Guarded→Network** (§5.5), **well-scopedness checking** (`Core/GuardedPlusCal/Syntax/WellScopedness.lean`, `Core/TypedSetTheory/Syntax/WellScopedness.lean`, repurposed as proof-side invariants, not primary check mechanism — §5.2a) — all working, non-trivial, worth porting/cleaning rather than rewrite. |
| Verification ambition | **Match prototype's already-verified surface only.** Reproduce refinement proof for Guarded→Network (only pass with complete proof in prior art); every other pass, including both new backends, unverified for initial roadmap. Lock inference the one exception needing real design now — without it Go backend semantics undefined, not just unverified. |
| Join Calculus executability | Compiler's job: **emit a Join Calculus source file**. Whether/how it later executes (custom interpreter, further lowering) left open, §9.1. No interpreter built as part of this plan unless asked. |
| Lock inference / Go concurrency safety | **In scope.** Rest of `Network2Go` already works (real goroutine-based concurrency); lock inference is the missing piece, not a reason to redesign backend. One lock family per process-local variable, derived from conflict analysis over shared process-local variables across atomic blocks — full algorithm §5.7. |
| Example/regression suite | **Real harness, `lake test`.** Prototype's `tests/PingPong`, `tests/TPC`, `tests/LamportMutex` are useful reading; Ping-Pong used informally as running illustration throughout this plan. `tests/regression/` holds small hand-written accept/reject `.tla` fixtures, one file per confirmed behavior, named `accept_<what>.tla`/`reject_<what>.tla`, run by a `@[test_driver] lean_exe test` that drives `Driver/Pipeline.lean`'s `runPipeline` in-process — so what a fixture asserts is *where* a compile stopped and *what* it reported, not just an exit code. Per-fixture expectations live in an optional `<fixture>.expect.json` sidecar (absent ⇒ defaults from the filename prefix); warnings are checked strictly, with a per-fixture opt-out. **Always write these in PlusCal's C-syntax (`{ }`-braced bodies)**, never P-syntax (`do … end while`/`end if`) — parser (§5.1) only accepts C-syntax. |
| Build config format / toolchain | **`lakefile.lean` (Lean DSL), not `lakefile.toml`.** Current stable Lean toolchain, not a stale pin — update `mathlib`/`batteries`/other pinned deps to match. Expect real breakage from the bump, not just cosmetic, including in `Extra/`'s vendored lemmas. |
| CLI shape | **Subcommands**: `fugue compile [FLAGS] <input>` compiles, `fugue explain <code>` prints what a diagnostic code means (`--list` for all of them, `Common/Diagnostics/Registry.lean`). `explain` finds its `docs/diagnostics/<code>.md` corpus by walking up from the *executable's* own path (`docs/diagnostics`, or `share/fugue/diagnostics` when installed), never from the working directory, which has no reason to be near the compiler; `$FUGUE_DOCS` overrides. |
| CLI flag surface | GCC/Clang-style flags on `leanprover/Cli` (`--help`/`--version` free), all on `compile`: `-d<name>[=<value>]` (debug options — AST dumps, `-dtiming` per-pass timing), `-f<name>[=<value>]` (feature toggles, e.g. `-fno-color` disables ANSI diagnostics — `Common/Errors.lean`'s `CompilerDiagnostic.pretty` takes `colored` flag), `-W<name>`/`-Wno-<name>` (per-warning control, e.g. `-Wno-fair`), `-X<name>[=<value>]` (target-specific backend options; the category exists but its allowlist is currently empty — see §9.3), `-o`/`--output`, `-t`/`--target go|join`, `-I <path>` (module search path, §5.3). Two details open — Join Calculus "flavors", Go `-p` package name — see §9.3. `leanprover/Cli` rejects a named flag given twice and parses `Array α`-typed flags as one comma-separated occurrence, not true repetition, so `-d`/`-f`/`-W`/`-X`/`-I` are each one Cli flag of `Array`-typed `ParseableType` (`-d name1,name2=value`, `-I dir1,dir2`, `-W name,no-other`), not literally repeatable GCC-style. `-d dump-dir=<path>` (default `.fugue/debug`) sets where `-d dump-tokens`/`-d dump-cst` write output — `<dump-dir>/<input-file-name>-tokens`/`-cst`, not stdout; value-less `-d dump-dir` is a hard error. `-d dtiming` dumps per-pass timing to `<dump-dir>/time.log`, one line per pass per input file, appended across passes/files in one run. `-d`/`-f`/`-W`/`-X` names validated against hardcoded allowlists (`knownDebugOptions`/`knownFeatures`/`knownWarnings`/`knownTargetOptions`, `Fugue.lean`) — unrecognized name is a hard CLI error. Extend these arrays by hand as later phases add dump points/features/warnings/target-options — no registration mechanism, set stays small. |
| Diagnostic identity | **A `rustc`-shaped code per diagnostic**: `E0042`/`W0003`, four digits, rendered in the header (`error[E0026]: …`). `CompilerDiagnostic.code` has no default, so every error/warning instance must map *every* constructor to a registry entry — a new constructor fails to compile until it is registered. `Common/Diagnostics/Registry.lean` is the single allocator: each entry carries its stage, its `-W` name if it has one, and a one-line summary, and instances name entries rather than writing number literals, so a code in use but unregistered cannot exist. Numbers are permanent — never renumbered, never reused, gaps left where a drafted code turned out unnecessary. Wording is free to change; the code is the identity a regression fixture, a build-log grep, and `fugue explain` all key on. |
| Go runtime library location | **`runtime/tlaplus/` + top-level `persistent/treemap/` in this repo**, versioned with the compiler targeting it, not a separate repo — one file per TLA+ concept/stdlib module (`sequences.go`, `sets.go`, etc.), not one flat package. See §5.7. |
| `Int` representation dispatch: machine `int` vs. `math/big` | **Go build tag, not a Fugue flag.** `math/big` is the default (matches the unbounded integers of the semantics being verified against); `go build -tags fugue_machint` opts into machine `int` for speed. Emitted code is identical either way — arithmetic goes through runtime functions, literals through `MkInt` — so the compiler has nothing to dispatch on. Whole compiled output, not per-declaration. See §5.7. |
| Name-provenance (which module declared a name) | **Tagged on the AST by the elaborator, not reconstructed later as a side table.** Elaborator resolves every `.var` reference through `Γ` and already knows there whether it's a binder or top-level declaration and which module the latter came from. `Elaborator/Monad.lean`'s `Binding` gets `origin : Origin` field (`.binder` / `.module name`), tagged at `Γ`-construction time (`Elaborator/Context.lean`'s `extend`/`extendAll` for binders; `Elaborator/Declarations.lean`'s own-declaration checking and `Driver/Modules.lean`'s imported-`Γ₀` fold for top-level names). `TypedTLAPlus.Expression.var` widens to carry `Origin` so it survives past `Γ` into the checked AST — both `WellFormedness` (§5.2a, checks 2(c)/3) and `Network2Go` (§5.7, resolving whether a builtin-looking operator like `+`/`Naturals` is the real builtin or a user override) read it directly, no lookup. Only one real `.var`-construction site (`Elaborator/Expressions.lean`'s `inferExpr`), so this is a same-lookup tag, not extra pass. A plain `lookupForeign : String → m (Option TypedModule)` (`MonadForeignLookup`, `Driver/Modules.lean`-backed) still fetches a foreign module's declaration list once its name is known from `origin`. |
| Address visibility / deployment topology | **Accepted limitation, not fixed here.** Distributed PlusCal lets any process know any other's identity, so generated code can't avoid assuming worst-case full connectivity ("star" topology). "Minimal needed addresses" static analysis considered, **not planned work** — largely mooted by nameserver-based addressing (§5.6, §5.7). See §7's stretch list. |
| Fairness (`isFair`, `fair process`/`fair+`) | **Largely ignored by compiler** — no way to insert fairness into target runtimes (neither Go's goroutine scheduler nor Join Calculus's reaction-firing nondeterminism made fairness-aware). `isFair` carried through ASTs (parsing → both backends) for round-tripping only, neither backend's compilation scheme (§5.6, §5.7) acts on it. Parser emits **warning** (§5.1) on any `fair process`/`fair+` annotation, tells user it's ignored. |
| `CONSTANT` values, process-set (`p ∈ S`) cardinality | **Left to the user of the compiled code.** `CONSTANT`s are abstract entities (type and value) as far as compiler concerned — concretized only when someone builds a real executable from generated code (compiler doesn't emit `main`, §5.7). No `ASSUME`-pinning requirement, no companion config file. A process set `p ∈ S` does **not** compile to `S`-many spawned goroutines/definitions — each process definition compiles to a **single entry point** (Go function, Join Calculus process definition), parameterized over process's own identity/address; user invokes it once per concrete process. See §5.3, §5.6, §5.7. |
| When imported modules get processed | **Eagerly and transitively**, recursively invoking driver right after desugaring, before type checking. Every module reachable from main module's `EXTENDS` list gets fully processed up front: once main module parsed/desugared (§5.1–§5.2), driver recurses on each directly `EXTENDS`ed module — parse → desugar → recurse on *its* imports → type-check — before main module's own type checker (§5.3) starts. By the time main module reaches `[Goto]`/`[Assign]`/etc. typing rules, `Ξ` already fully populated for everything reachable. (`INSTANCE` out of scope, §8.) See §5.3. |
| How `GuardedPlusCal.Algorithm.WellScoped` gets established for Guarded→Network | **General preservation lemma, proved once**, not a per-run decision procedure: `CorePlusCal.WellScoped p → GuardedPlusCal.Algorithm.WellScoped (Computable2Guarded (Elaborator p))`, proved as part of `Elaborator`/`Computable2Guarded`'s verification work (§5.5, §6.2), reused unchanged for every compiled program. Fits the compiler's verification aesthetic better than re-deciding the `Prop` computationally per program. `CorePlusCal.WellScoped`, the lemma's antecedent, doesn't exist in prior art — authored fresh (§5.2a). See §5.2a, §5.5. |
| Language-subset exclusions for first type checker | **`INSTANCE` and `RECURSIVE` both out of scope for now.** Neither in §8's subset, neither prior-art checkout parses them, both need real design work before checkable — `INSTANCE`'s parameter-substitution semantics and `RECURSIVE`'s annotation-seeded checking rule aren't needed for a first type checker against §8's subset. Revisit if a program needs either. For `RECURSIVE`, if picked up: require explicit type annotation on the `RECURSIVE` declaration for every operator in the group, extend `Γ` with all declared sibling types up front, check each body against its own annotation independently — breaks circularity a mutually-recursive group would otherwise create for a bidirectional checker, standard precedent (mutual `def`/`def` blocks in Coq/Agda/Lean always carry signatures), near-necessary for decidability under this plan's rank-1-polymorphism discipline if any operator in the group is polymorphic. |
| `Ξ`'s cache: disk persistence and invalidation | **In-memory only for now, no disk persistence.** A disk-backed cache under `~/.local/config/.fugue` raises an invalidation question with no good answer yet: a compiler-side change (bug fix, stdlib-stub update, toolchain bump) can silently invalidate a cached module's typed form without touching that module's own source. Checker itself still under active development, exactly the kind of change that would trip this — in-memory `MonadModuleCache` sidesteps it: nothing persists across runs, nothing goes stale. Disk persistence, once picked up, needs either a cache-key compiler/schema-version component (bumped whenever anything affecting typing output changes) or a lighter global "cache format version" stamp wiping the whole directory on mismatch — undecided, revisit once checker stabilizes. |
| Pipeline order: well-formedness checking (§5.2a) vs. type checking (§5.3) | **Type checking runs first.** Type checking already forces variable well-scopedness as a side effect of succeeding (out-of-scope/undeclared reference is a `Γ`/`Σ`/`Δ`-lookup failure, i.e. a type error on its own) — a separate well-scopedness pre-pass before type checking would re-derive a fact type checking catches anyway. Well-formedness's other two checks (well-labelledness, no-bare-temporal-operators) have no dependency on typing either way, nothing lost deferring them. Well-scopedness's "every reference resolves" half becomes redundant defense-in-depth this way; its "no shadowing/no duplicate names in scope" half is not implied by ordinary bidirectional type checking (a shadowed name still type-checks against something) and stays this pass's real, load-bearing job. See §5.2a, §7. |
| Polymorphism-instantiation / metavariable resolution mechanics | **Direction-aware solving, not naive eager unification** — subtyping axioms here are asymmetric coercions, not equivalence. Lower-bound constraints (`T <: ?n`) solve eagerly (coercions only run narrow→wide); upper-bound constraints (`?n <: T`) only get recorded as pending, never solved from directly (would foreclose a narrower solution arriving later). Metavariable-vs-metavariable constraints (`?m <: ?n`, both unresolved) must **not** be resolved by merging the two into one — unsound, conflates two independently-constrained unknowns; record the link on the lower side, propagate once one side resolves from a real ground bound. A metavariable with no bounds at end of checking — including one whose only bound is another metavariable that never resolved — is a hard type error, not a silent default. Full algorithm with counterexamples in §5.3. |
| Coercion realization: where do coercions live, how does a *pending* one resolve? | **`Coercion` is closed structural data, not an opaque `Expr → Expr` closure** — a small recursive inductive (`id`, `strToSeq`, `seqToFun`, `tupleToSeq`, `set`, `tuple`, `record`, `function`, `comp` for axiom-chain composition), each constructor carrying exactly the type indices, field names, and nested sub-`Coercion`s its structural rule needs, plus any fresh binder name (`x`/`y`/`i`) `Elaborator/Subtyping.lean` generated via `MonadFresh` at construction time — baked in once, since a name fresh at construction remains fresh at discharge (§2's `$`-based freshness argument). Necessary because `[Receive]`'s coercion (below) must survive past `Typed2Computable`'s type change (`TypedTLAPlus.Expression` → `ComputableTLAPlus.Expression`) and get discharged against the *later* type; a closure fixed at one concrete `Expr` type can't cross that boundary. Two small structural recursions consume the same data, one per concrete expression type: `Coercion.apply` (`Core/TypedTLAPlus/Coercion.lean`, called immediately at check time by every ordinary subtyping call site, e.g. `[Send]`'s payload) and `Coercion.applyComputable` (`Core/ComputableTLAPlus/Coercion.lean`, importing `Core.TypedTLAPlus.Coercion` for the data type — Computable depends on Typed, never the reverse). `subtype` builds `Coercion` data directly at each structural rule; all `Expr`-building logic (builtin references, `.map'`/`.tuple`/`.record`/`.fn`/`.choose` construction) lives in `Coercion.apply`/`.applyComputable`'s match arms. When `subtype` yields **pending** (upper-bound check against unresolved `?n`), expression wrapped in new `mvar : MVarId → Expr → Expr` node added to `TypedTLAPlus`/`TypedPlusCal`'s grammar; checker context keeps, per unresolved `?n`, its pending upper bounds and the `mvar` sites created alongside them in lockstep. The moment `?n` resolves, every `mvar` site for it is substituted with the now-computable coercion (`.apply`) applied to the wrapped expression — part of metavariable-resolution itself, not a separate pass, so `mvar` fully eliminated before checker output reaches `Computable2Guarded`; downstream passes and both backends never see `mvar` itself (the `Coercion` *value* a `receive` carries does, deliberately, survive further — see below). See §5.3, §5.5. |
| `[Receive]`'s channel/reference coercion — where does it live, given no expression to apply it to? | **Stored on the `receive` statement node itself, discharged only at `Guarded2Network`.** Unlike `[Send]`'s payload (a real sub-expression `Coercion.apply` wraps immediately), a received value doesn't exist as an expression at check time — arrives from network at runtime. Checker synthesizes both channel's element type and destination reference's type, `subtype`s them directly (independent of `Channel <: Channel`'s own structural check, stays identity-only), stores resulting `Coercion` as new field on `TypedPlusCal`/`GuardedPlusCal` `receive` node. `Computable2Guarded` (§5.4) carries it unapplied (none of its four subpasses touch `receive`'s shape); `Guarded2Network` (§5.5) is first pass a `receive` becomes concrete buffered read, discharging the coercion directly against the freshly-built `Head(inbox)`/`Tail(inbox)` `ComputableTLAPlus.Expression` via `Coercion.applyComputable` (above) — no lift/lower round-trip through `TypedTLAPlus.Expression` needed. See §5.3, §5.5. |
| Diagnostic/error-model shape | **Per-pass error types, unified by common rendering interface** — not one shared diagnostic sum type. Warning suppression (`-W`/`-Wno-<name>`) handled either at emission point or by filtering before rendering — implementer's call. Mechanism (per-pass errors, common rendering, some warning filtering) already exists in `Common/Errors.lean` (§4) — read before designing new. Fine to later refactor either error style or emission mechanism if it doesn't hold up. |
| Generated-identifier hygiene | **Resolved by renaming; direction doesn't matter.** Whether a user-chosen or compiler-introduced name gets renamed on collision is irrelevant — hard requirement is **no shadowing ever introduced in generated code, checked at every pass, not just final pretty-printer.** Same class as escaping target-language reserved words (PlusCal variable literally named `type`/`def` colliding with Go/Join-Calculus keyword) — `Core/Go/Pretty.lean` has a `keywords : Std.HashSet String` table and `sanitize` (suffixes colliding name with `__`), applied at every identifier-print point. **Reserved words only:** Go's *predeclared* identifiers (`int`, `any`, `comparable`, `error`, `len`, `make`, …) are legally shadowable ordinary identifiers, and the generated code refers to them by name constantly, so the printer must not escape them — a combined table (prior art's) emits `int__`/`comparable__`. Renaming a *user-chosen* name that collides with one is `Network2Go`'s job, the only place knowing a name's provenance; `Core/Go/Pretty.lean` exports `predeclared` for it. Generalize to cover compiler-introduced internal names (`recv`, `inbox`, lock variables, label atoms, §5.6/§5.7) and Join Calculus's own reserved surface too, not just Go keywords. See §5.2a, §5.6, §5.7. |
| Flags, `Ξ`: how do cross-cutting effects fit the monad-polymorphism convention | **Unified effect stack, not a driver/pass split.** Every function — pass code and CLI driver alike — written against one abstract `{m : Type _ → Type _} [Monad m]`, every effect (errors, flags, module cache) a typeclass constraint on that same `m`, not confined to an outer `IO`-flavored driver layer. (1) **Flags are a contextual (Reader) effect.** Flags aren't uniformly `Option String` (boolean `-f`/`-W` vs. valued `-d<name>=<value>` vs. `-o`/`-t`/`-I`'s own typed values each need their real type) — and this project's proofs run on `Std.Do.WP`, which can't be instantiated at `IO` at all, so an opaque action gives that framework nothing to reason about, whereas Reader is exactly the transparent effect it handles. Concrete, typed `FlagsEnv` structure (covering the full flag surface above), populated once by CLI driver from `Cli.Parsed`, accessed via `MonadReaderOf FlagsEnv m` plus typed accessor helpers (`getDebugFlag`/`getDebugOption`/`getFeatureFlag`/…) built on `read`. The CLI builds one `FlagsEnv` from `Cli.Parsed` and hands it to `Driver/Pipeline.lean`'s `runPipeline`, which supplies it as a real `ReaderT` layer (`Driver/Modules.lean`'s `Base`). No global `IO.Ref`: a `FlagsEnv` belongs to one compile, and two compiles in the same process (the regression runner runs many) must not share one. (2) **`Ξ` gets its own effect class**, `MonadModuleCache m` (`lookup`/`store` keyed by source hash), instance backed by a field of `DriverState`, the per-compile state `Base` threads as a `StateT` layer *under* `DiagT` (so entries written before a `throw` survive it) — disk persistence deferred (see `Ξ`'s cache row above) — genuine mutable-store effect, unlike flags, but only shows up in `Elaborator`, not part of §6.2's committed proof surface, so doesn't hit the `Std.Do.WP`-compatibility question flags did. (3) **Consequence for §6.2's Guarded→Network proof, accepted knowingly:** `Algorithm.toNetwork` stays generic (`{m} [Monad m] [MonadFresh m] [MonadDiagnostic Empty G2NError m]`, same shape as every other pass — `MonadDiagnostic`, not a bare `MonadExceptOf`, so its concrete `IO` instantiation pairs directly with `Fugue.lean`'s `runPassDiag`), not special-cased monomorphic. Refinement theorem proved against whichever concrete instantiation `Std.Do.WP` supports (e.g. `m := Id`, or `ReaderT FlagsEnv (DiagT Empty G2NError Id)`) — that instantiation, not the `IO`-run one, is the real proof target. Running the same polymorphic term at `m := IO` for CLI execution is a **separate, deliberately unverified step**, documented explicitly in `Guarded2Network`'s module docs. (4) **Fresh-name generation gets the same `IO.Ref` treatment as `Ξ`, not a `StateT Nat` layer threaded through each pass's own concrete monad instantiation.** `MonadFresh m` (`Common/Fresh.lean`), monotonic counter behind `fresh : m Nat`, first needed by expression desugaring's tuple-pattern/multi-binder-collapse transforms (§5.2), recurring at `Computable2Guarded`'s `𝒞_par` (§5.4) and `Guarded2Network`'s `inbox`/`rx` naming (§5.5). Names generated as `"<prefix>$<n>"` — `$` can't appear in a TLA⁺ identifier, so no scope-tracking needed to prove freshness. One counter per compile, held in `DriverState` alongside `Ξ`, not a separate `0`-restarted counter per pass — every pass draws from the *same* counter for the whole compile (strictly stronger hygiene: two different passes' compiler-introduced names can never collide with each other either, not just with user-written ones), and no pass's own entry point (`runChecker`/`runDesugarer`/`toGuarded`/`toNetwork`) needs to thread a `Nat` through its own return type or its caller's `.run`/`.run'` chain — `MonadFresh` lifts through `ReaderT`/`StateT`/`DiagT` (`Common/Fresh.lean`), so a pass says `[MonadFresh m]` and never learns how the counter is stored. Consequence: those entry points are polymorphic in their base monad, constrained to `[MonadFresh n]`; the driver pins them at `Base`. Deliberately not process-wide: a global counter makes a compile's generated names depend on how many compiles preceded it, which is invisible with one compile per process and wrong for the regression runner, which checks output for determinism. |
| Shared builtin-operator recognizer | **One shared table, `Core/TypedTLAPlus/Builtins.lean`, not a per-pass string list.** Builtins represented uniformly as `.opCall (.var name _ origin) args`, resolved by string name + `Origin` (`.intrinsic` for `builtinContext`'s core operators, `.module "Sequences"`/`.module "Naturals"`/etc. for stdlib stubs). `WellFormedness/Restrictions.lean`'s reserved-temporal-action check and `Typed2Computable`'s own computable-builtin question both consult it instead of keeping independent copies. **Closed `inductive BuiltinOp`, one constructor per literal builtin** — exhaustiveness-checked `match`es for every downstream consumer, at the cost of duplicating each name already listed in `builtinContext`/`builtinModules` a third time. `reservedTemporalActionNames` stays a bare name-only list (not derived from this `Origin`-keyed table) — these eight spellings can never be user-shadowed, so name-only matching is exact. |
| `Typed2Computable`'s two new restrictions, beyond `WellFormedness` | **`[A -> B]`/`[a:A,...]` (`fnSet`/`recordSet`) rejected outright; `forall`/`exists`/`choose`'s domain becomes structurally mandatory.** Both denote sets/expressions with no finite runtime representation under this compiler's finite-sets assumption — `ComputableTLAPlus.Expression` has no constructor for the first two, and the third's domain field is a plain `Expression`, not `Option (Expression)` (`WellFormedness/Restrictions.lean`'s check 3 already bans an unbounded domain transitively-reachable-from-the-algorithm, so this enforces an already-established invariant structurally). Everything else `TypedTLAPlus`/`TypedPlusCal` can express, reachable from the algorithm, translates cleanly. |

---

## 3. Prior art map

Three things exist; none is "the codebase to continue," all worth reading before touching
the corresponding area.

### 3.1 `github.com/mesabloo/fugue` (public mirror)
- `main`: only branch that actually builds an end-to-end CLI (`pcvc`). Pipeline wired in
  `Main.lean`: parse TLA+ (`SurfaceTLAPlus`/`SurfacePlusCal`) → resolve annotations →
  `SurfacePlusCal.Algorithm.toGuarded` (fused desugar+typecheck+guard, *not* split into
  separate stages) → desugar expressions to `CoreTLAPlus` → `toNetwork "inbox"` →
  `toGoCal` → pretty-print Go. Only Go backend exists; no type-checking pass in the
  wired-up sense (types basically untracked past annotations). `VerifiedCompiler/` here
  has a working `Trace` + `StrongRefinement` framework, and `GuardedPlusCal`/
  `NetworkPlusCal` both carry `Semantics/Denotational.lean` + `Semantics/Lemmas.lean` —
  the "hand-verified pass" reference point. `GoCal/Semantics/{Denotational,
  Denotational2}.lean` are two abandoned attempts at Go's semantics (1640, 1040 lines),
  both dropped in later branches.
- `develop` / `lock-inference` (same commit): from-scratch restructuring into the module
  layout this plan adopts (§4): `Common`, `Core/*`, `Parser_`, `Desugarer`, `Checker`,
  `Computable2Guarded`, `Guarded2Network`, `Network2Go`, package renamed `Fugue`. Introduces
  explicit `CorePlusCal`, `TypedPlusCal`, `TypedTLAPlus`, `TypedSetTheory` stages absent
  from `main`. Many empty stubs or partial — but not `Parser_`, substantial here too; the
  local checkout (§3.2) has it further along, and is the one to port from.
- `go-semantics`: newest branch, abandoning both old `GoCal` denotational semantics
  attempts for a serious metric-space/domain-theory treatment
  (`Extra/Topology/IMetricSpace*`, Lipschitz maps, uniform continuity, closed embeddings —
  solving a recursive domain equation `P ≅ F(P)` via Banach fixpoint). Real, hard,
  unfinished research; see §6.4.
- `docs`: CI plumbing for `doc-gen4`, no content of interest.

### 3.2 `~/Documents/distpcal-compiler` (private, more current)
Same project, different/renamed remote, further along in places. Local branch
`typechecker` (uncommitted) has active work on `Checker/Typechecker/*`,
`Core/Go/{Syntax,Pretty}.lean`, `Core/README.md`. Notable extras not on public mirror:
- `Core/CorePlusCal/Syntax.lean`: statements/blocks indexed by a `Bool` tracking whether
  they're "terminal" (end in `goto`) at the *type* level, so "all blocks end in an
  explicit goto" is a structural invariant, not a runtime check. Worth carrying forward.
- `Parser_/{Annotations,Common,Monad,PlusCal,TLAPlus}.lean` +
  `Parser_/Tokens/{PlusCal,TLAPlus}.lean`: substantial (~2,200 lines), not a stub —
  supersedes (deletes) the older `SurfaceTLAPlus`/`SurfacePlusCal` `Syntax.lean`/
  `Tokens.lean` files the public `fugue` mirror's `main` branch still parses with.
  Already targets the `Core/SurfaceTLAPlus`/`Core/SurfacePlusCal` ASTs present in this
  same checkout. **This, not `fugue main`'s parser, is the source to port from** (§5.1).
- `lib/{address.go,rand.go,tlaplus.go}`: actual (partial) Go runtime library imported by
  generated code (`github.com/mesabloo/distpcal-compiler/lib`), including TLA+ value
  encodings (`Seq`, `Set`, functions).
- `tests/{PingPong,TPC,LamportMutex}`: hand-built example algorithms with real generated
  Go and a hand-written nameserver (TCP/UDP address registration + lookup,
  `charmbracelet/log` for logging) to actually run examples across processes. Practical,
  already-prototyped analogue of the Join Calculus chapter's `register`/`lookup` — worth
  mining for the Go backend's runtime design.
- `Desugarer/TLAPlus.lean` has real code (`Expression.desugar`, `Declaration.desugar`,
  `Module.desugar`) but is not complete against the four confirmed transformations in
  §5.2 — check what's actually implemented rather than assume coverage.
  `Desugarer/PlusCal.lean` is an empty stub — statement-level desugaring (Distributed
  PlusCal → PlusCal with explicit gotos, feeding the `cflow`/`par`/`flat`/`reord`
  pipeline) has no code anywhere, despite being mathematically specified in the thesis.

### 3.3 The thesis (`reference/thesis.pdf`)
Maps onto the pipeline as follows. Chapters marked "stub" contain only section headers —
treat their content as *to be designed*, using surrounding chapters and prior-art code as
guidance.

| Thesis chapter | Pipeline stage | Status |
|---|---|---|
| 3.1 | Bidirectional type checker | Fully written (§5.3 reproduces it) |
| 3.2 | Distributed PlusCal → Guarded PlusCal | Fully written, including §3.2.3.4 (guard reordering, `𝒞_reord` — now covers `receive` guards too, not just `await`) — §5.4 matches |
| 4 | "Compiler verification, denotationally" | Stub (title only) |
| 5 | Guarded PlusCal → Network PlusCal | Stub in thesis — but *implemented and proved* in `fugue` `main`. Read code, not thesis. |
| 6 | Denotational account of Go | Fully written, heavy domain theory. See §6.4. |
| 7 | Network PlusCal → Go, lock inference | §7.1 (atomicity/lock inference) fully written (§5.7). §7.2.1.1 (Go representations of each TLA+ type, incl. `Channel(τ)` resolution) and §7.2.1.2 (compiling TLA+ expressions — booleans/quantifiers, sets, functions) fully written. §7.2.2 ("Compiling operator and function definitions") fully written (non-recursive vs. parametric operators, recursive functions via tie-the-knot `MkRecFn`). **§7.2.3.1 ("Compiling atomic blocks") and §7.2.3.2 ("Compiling threads and whole processes") both fully written** — branch-as-function scheduling loop, lock parameters, `LOCK`/`UNLOCK`, per-construct statement/guard compilation rules, thread chaining, the receive-relay thread, full process wiring (`INIT_LOCKS`, `done`/`done'` channels); see §5.7. **§7.3 is a fully worked Go compilation of the Ping-Pong example** (the Pong process end to end: lock inference result, every atomic block's generated function, both threads, the process function, the concrete `Network` struct) — cross-check §5.7's implementation against it directly, same role as §8.6's worked example for the Join Calculus backend. §7.4 ("informal correctness proof sketch") states a named conjecture (`proc(net, mailbox, self)` refines `P` in isolation, assuming the network is correctly wired) but explicitly leaves both the informal argument and any mechanization as future work — still effectively a stub for verification purposes, no proof obligation added to this project's scope. `Channel(τ)`: "channels are not first-class citizens in Distributed PlusCal, we do not (need to) represent `Channel(τ)` in the general case" — narrows but doesn't close §9.7. See §5.7. |
| 8 | Network PlusCal → the Join Calculus | Fully written, worked Ping-Pong example. Primary spec for new backend; §5.6 is condensed version. |
| 9 | Conclusion | Stub (title only) |

---

## 4. Target project layout

Module structure converged on in `distpcal-compiler`'s `develop` branch, plus two
additions for the Join Calculus backend. Package name `Fugue`, executable `fugue`.

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

§3 is the pointer-to-prior-art doc; no separate `reference/NOTES.md`.

Each `Core/<Lang>` module owns exactly one AST plus its pretty-printer; semantics
(`Semantics/Denotational.lean`, `Semantics/Lemmas.lean`) added only for passes that have
(or are actively getting) a refinement proof — avoids maintaining semantics nobody uses.
`Fugue.Core`, `Fugue.Parser`, `Fugue.Desugarer`, `Fugue.WF`, `Fugue.Elaborator`,
`Fugue.Driver`, `Fugue.T2C`, `Fugue.T2G`, `Fugue.G2N`, `Fugue.N2JC`, `Fugue.N2Go` are the
corresponding `lean_lib` targets in `lakefile.lean`, mirroring `distpcal-compiler`'s
naming scheme.

---

## 5. The pipeline, stage by stage

Running example throughout: the thesis's Ping-Pong algorithm (thesis §8.6, present as
`tests/PingPong/PingPong.tla` in `distpcal-compiler`) — two processes exchanging
`"Ping"`/`"Pong"` messages over per-process mailboxes. Small enough to hand-trace through
every stage, and the thesis's own worked example for the one fully-specified backend
(Join Calculus) — natural first smoke-check target without turning into a formal
regression suite (deprioritized, §2).

### 5.1 Lexing & parsing
**Input:** raw TLA+ module source (`.tla`), embedded Distributed PlusCal algorithm inside
a `(* --algorithm ... *)` comment block, plus `@type`/`@mailbox` annotations in comments
(see Ping-Pong listing, thesis §8.6, for annotation style).
**Output:** `SurfaceTLAPlus.Module` wrapping a `SurfacePlusCal.Algorithm`.

`@rx` is not a source annotation the parser handles — internal marker used later, during
pretty-printing of the Network PlusCal variant (§5.5's output, consumed by §5.6/§5.7's
backends). `Annotation` (`Parser_/Annotations.lean`) has only `@type`/`@mailbox`/
`@parameter` — no `@rx` case. Whoever implements Network PlusCal pretty-printing (§5.5
onward) introduces `@rx` there.

Ported from the **local** `~/Documents/distpcal-compiler` checkout (§3.2), not the public
mirror. That checkout's `Parser_/{Annotations,Common,Monad,PlusCal,TLAPlus}.lean` +
`Parser_/Tokens/{PlusCal,TLAPlus}.lean` (~2,200 lines, `fgdorais/Parser`-based, hand-rolled
lexer producing `Located` tokens) is the current iteration; it already targets the
`Core/SurfaceTLAPlus`/`Core/SurfacePlusCal` ASTs present in that same checkout, which this
project's own versions should stay close to. `fugue main`'s older parser is at most a
secondary reference.

Annotations (`@type`, `@mailbox`) parsed as a distinct pass over comments
(`resolveAnnotations`) since TLA+'s own grammar has no room for them — separate, explicit
step, both for error-reporting clarity and because it's genuinely orthogonal (comments vs.
grammar). Does two things: parses the annotation's own content (e.g. the type expression
inside `@type`), and checks *placement* (a given annotation kind appears only where
structurally meaningful, e.g. `@mailbox` only immediately before a `process` declaration).

**`fair process`/`fair+` emits a warning, not an error.** Compiler doesn't act on
fairness anywhere downstream, so `isFair` parsed and carried through purely for
round-tripping — parser emits a warning (ties into `-W` flag surface, §2) the moment it
sees `fair process`/`fair+`.

**Known ergonomics gap:** syntax errors inside annotations are poor — positions aren't
tracked within comments, an annotation error can't point at more than roughly "somewhere
in this comment," worse across multiple comments. Fixing means threading real source
positions through comment/annotation parsing, fiddly, worth doing eventually, not
blocking pipeline construction.

`\@` is an escaped, literal `@` in comments (`tryParseAnnotations'`,
`Parser_/TLAPlus.lean`) — never starts an annotation, so prose can mention `@type`/
`@mailbox`/`@parameter` inertly.

Known parser gaps: see §9.2.

### 5.2 Desugaring
**Input:** `SurfaceTLAPlus`/`SurfacePlusCal`. **Output:** `CoreTLAPlus`/`CorePlusCal`.

Both `Core/CoreTLAPlus/Syntax.lean` and `Core/CorePlusCal/Syntax.lean` written fresh
(§2/§4) — prior art's own `Core/CoreTLAPlus/Syntax.lean` isn't the target shape (carries
`prefixCall`/`infixCall`/`postfixCall`, separate `bforall`/`forall` pairs, an
`@`-referencing case, none of which survive; only prior art's `CorePlusCal.Statement`'s
`Bool`-indexed terminal encoding was carried forward, §2/§3.2).

Two independent halves:

- **Expression desugaring** (`SurfaceTLAPlus.Expression.desugar`, `Desugarer/TLAPlus.lean`):
  produces `CoreTLAPlus`, a deliberately simple core language for the checker (§5.3) and
  everything downstream. Four confirmed transformations, cross-checked against the
  thesis's own formal typing rules (§3.1.3) — authoritative, supersedes shorter gloss in
  `Core/README.md`:
  - `@`, TLA+'s self-reference inside `EXCEPT`, desugars to the expression being
    `EXCEPT`ed. In `[x EXCEPT ![1, 2, 3] = @ + 3]`, `@` becomes `x[1, 2, 3]`. Implemented
    via a `Reader`-based approach (`Option (CoreTLAPlus.Expression α)`, `none` outside any
    `EXCEPT` update).
  - Conjunction/disjunction *lists* (TLA+'s indentation-sensitive `/\`/`\/` lists)
    desugar to binary infix operators `/\`/`\/`.
  - Prefix, postfix, infix operator applications desugar to ordinary (prefix-style)
    operator applications: `1 + 2` becomes `+(1, 2)`, `TRUE^*` becomes `^*(TRUE)`, same
    for every mixfix operator. `CoreTLAPlus.Expression` needs no dedicated operator-enum
    types or value constructors — every builtin operator becomes an ordinary `opCall`
    whose callee is `Expression.var "<canonical-spelling>"` (e.g. `.var "+"`,
    `.var "\\in"`), reusing the exact same constructor as a user-defined name. Sound: no
    TLA⁺ identifier can ever be spelled like an operator symbol (lexer's
    `identifierOrKeyword` and `symbol` productions disjoint), matches thesis's own
    formalization verbatim ("1 + 2 is treated as (+) 1 2 … we may assume that
    `+ : (Int, Int) ⇒ Int` is present in the typing context Γ", §3.1.3) — operators are
    pre-populated *names* in Γ, not a distinct syntactic category. Canonicalizing every
    alternative spelling (e.g. `<=`/`=<`/`\leq`) to one string happens once, in
    `Desugarer/TLAPlus.lean`'s `{Prefix,Infix,Postfix}Operator.canonicalName`. Unary minus
    gets its own canonical spelling, `"-."`, distinct from binary minus's `"-"` — same
    disambiguating trick "Specifying Systems" itself uses. Surface syntax unchanged (`-x`
    parses exactly as always); only the internal `Γ`-lookup-facing name changed.
    `Elaborator/Declarations.lean`'s `builtinContext` carries both: `"-" : (Int, Int) ⇒
    Int` (binary), `"-." : (Int) ⇒ Int` (unary), no collision.
  - Every quantifier-like binder (`\A`/`\E`/`\AA`/`\EE`/`CHOOSE`/set-map/set-filter/
    function literals) binds exactly one variable over at most one domain — confirmed
    against the thesis's own formal typing rules (Figures 3.1.2/3.1.3/3.1.5/3.1.6), every
    one single-variable; `CoreTLAPlus`'s quantifier constructors have no multi-variable or
    tuple-pattern case. Two desugaring shapes needed, confirmed against real usage in
    `distpcal-compiler/tests/LamportMutex{3,4}.tla`: tuple-pattern binders (`\A ⟨x, y⟩ ∈ S
    : P`, `[⟨m,nd⟩ ∈ S ↦ …]`) desugar via one fresh variable and substitution (`\A z ∈ S :
    P[z[1]/x, z[2]/y]`); **multi-variable *quantifiers*** (`\A x, y : P`, `\A x, y ∈ S :
    P`) desugar to **nested** single-variable quantification (`\A x : \A y : P` / `\A x ∈
    S : \A y ∈ S : P`, a genuine logical equivalence) — but **multi-binder *function
    literals/set-maps*** (`[x ∈ A, y ∈ B ↦ e]`, `{e : x ∈ A, y ∈ B}`) do *not* nest the
    same way (would build a function of functions, not a function over pairs) — collapse
    to *one* fresh variable over the **Cartesian product** `A × B` instead, confirmed
    against the thesis's Fig. 3.1.3 function rule (single-variable only) and standard
    TLA⁺ semantics. Both cases reuse the same substitution helper
    (`CoreTLAPlus.Expression.subst`, `Desugarer/TLAPlus.lean`) — simple, non-capture-
    avoiding substitution stopping at any binder rebinding the target name, sufficient
    given well-scoped programs never shadow (§5.2a). Shared `MonadFresh`/`freshName`
    effect (`Common/Fresh.lean`, §2) generates these fresh names, collision-free via a `$`
    character no TLA⁺ identifier can contain; recurs at `Computable2Guarded`'s `𝒞_par`, §5.4.
- **Statement desugaring** (Distributed PlusCal → PlusCal with explicit gotos,
  `Desugarer/PlusCal.lean`): written fresh (prior art's own version is an empty stub in
  every branch). Target shape: `Core/CorePlusCal/Syntax.lean`'s type-indexed
  `Statement α β (terminal : Bool)` encoding (§3.2). Notable design points:
  - `Process.threads : List (List (String × Block α β true))` — outer list is parallel
    `{...}` threads, inner list is each thread's own sequence of labelled blocks. Labels
    and `goto`s can appear *nested* inside `if`/`while`/`either` bodies — only `with`
    genuinely disallows them (its binding only makes sense within one atomic step).
    Desugarer's job here is **basic-block extraction**: pull each nested labelled
    sub-block out to become its own top-level `(label, Block)` entry in the thread, stitch
    control flow back together with explicit `goto`s. Implemented as `desugarSegment`
    (`Desugarer/PlusCal.lean`): walks a thread's statement list carrying an accumulator of
    already-desugared non-terminal statements, on hitting a label or a nested construct
    needing extraction, closes off the current segment as a `CorePlusCal.Block ... true`
    and recurses. Fresh loop-back/continuation labels synthesized via `MonadFresh`/
    `freshName` (`"loop$n"`/`"cont$n"`) only when no existing label to reuse. Dispatch
    between the cheap path (`desugarLabelFreeBlock`, statically known to always produce
    non-terminal `Block ... false`) and the extraction-capable path (`desugarSegment`) is
    decided by `Statement.needsExtraction`/`List.needsExtraction`, which checks **both**
    "does this body contain a label anywhere" **and** "does this body's own last statement
    resolve to a bare `goto`" (checking only the first misses an `either`/`if` branch
    ending in an explicit `goto` with no nested label). `CorePlusCal.Statement.while`'s
    constructor is `{b} (cond : β) (B : Block α β b) : Statement α β false` — allows the
    loop body itself to be terminal (ending in an explicit loop-back `goto`), while the
    `while` statement itself stays non-terminal (falling out of the loop always continues
    normally).
  - A `goto` immediately followed by further *unlabelled* statements is rejected
    (`gotoNotInTailPosition`) — genuinely unreachable dead code (a `goto` immediately
    followed by a *label* is the ordinary "block ends here" case, fine). `with` rejects
    any nested label (`nestedLabel`, `with`-specific). **`goto Done` auto-insertion**: if a
    thread's last label runs out of statements without an explicit terminal, `goto Done`
    is auto-inserted — `"Done"` is a reserved sentinel needing no matching label
    definition (standard PlusCal translator convention); well-labelledness (§5.2a) keeps
    `"Done"` exempt from "every `goto` targets a real label".
  - **A `while` must always be immediately preceded by a real label, never auto-inserted.**
    Manual states the labeling requirement unconditionally (§3.2.4/§3.7 — unlike `if`/
    `either`, which only need a label *after* them, and only when they contain something
    requiring one), independently confirmed by the thesis's own `𝒞_cflow` rewrite rule
    (§5.4): pattern `while e {B1}; B2; goto l'` at label `l` already assumes the `while`
    starts the block. Real PlusCal's default translator (no `-label` flag) **rejects** an
    unlabelled `while` outright — auto-insertion is what the opt-in `-label` flag does,
    not the default. Same for `if`/`either`'s "must be followed by a label" requirement
    (§3.2.2/§3.2.3) — no auto-synthesis there either. Concretely: `desugarSegment`'s
    `while` case throws `DesugarError.whileNotLabelled` whenever the current segment
    already has content, or has no real label to attribute the `while` to.
    `desugarContinuation` throws `DesugarError.notFollowedByLabel` whenever what follows a
    label/`goto`-containing `if`/`either` isn't itself already labelled.
    `List.needsExtraction` flags *any* `while` found anywhere in a nested body,
    unconditionally, so `desugarSegment` always gets a chance to check it's properly
    labelled (a `while` first inside a nested `if`/`either` branch is not the same as
    being immediately preceded by a real label — that label belongs to the enclosing
    `if`).
  - **A `while` may never appear inside a `with` body, at any nesting depth, independent
    of `nestedLabel`.** Manual (§3.2.6) lists this as its own unconditional restriction —
    `with`'s one-atomic-step semantics can never provide the label a `while` always needs.
    Enforced via a threaded `insideWith` flag (propagated through `if`/`either`'s own
    sub-bodies, both legal inside `with`, checked immediately on seeing a `while` before
    recursing into its body) and `DesugarError.whileInWith`.
  - **A `with`-bound name can never be the target of a write** — neither direct assignment
    (`with (x = 3) { x := 9; }`) nor a `receive` whose target it is (`with (x = "")
    { receive(ch, x); }`) — a `with`-bound name is a local binding to a fixed value for
    the body's duration, not a process variable with state to update. `WithContext`'s
    field is `boundVars : List String`, names currently bound by any enclosing `with`
    (accumulated across nesting — inner `with` prepends its own names onto whatever outer
    one(s) already bound). "Inside a `with` body at all?" (needed by `whileInWith` above)
    is `boundVars.isEmpty`; the write-rejection check is `boundVars.contains` against each
    write's target name (an `assign`'s LHS `Ref`, or a `receive`'s target `Ref`), throwing
    `DesugarError.withBoundVarWritten (pos) (name)`. Applies transitively — an inner
    `with`'s body writing to an *outer* `with`'s bound name is rejected too. Applies to
    both `assign` and `receive`.
  - **Annotations disappear from `CorePlusCal`/`CoreTLAPlus` entirely, leaving only their
    content.** Content that fits uniformly into "the declared-type annotation at whatever
    stage of checking" stays on the same `α` `Statement`/`Block`/`Branches`/
    `MulticastFilter` already had — `CorePlusCal.Declarations` shares the same `α`
    variable as `Statement`'s (not `Option`-wrapped, not a second separate type
    parameter) — keeps `Process`/`Algorithm` ordinary, unambiguous two-parameter
    `Bifunctor`/`Bitraversable` instances. Concretely: `Declarations.variables/channels/
    fifos` entries carry `α` directly (`List Annotation` fresh out of statement
    desugaring, `Option Typ` after `CorePlusCal.Algorithm.stripEmbeddedTypeAnnotations`,
    which also strips `MulticastFilter`'s per-bind annotations and a `with`-bound
    variable's own annotation). Content that can't fit this uniform shape (`@mailbox`'s
    channel name/index expressions, `@parameter`'s presence-as-`Bool`) is extracted early
    as its own concrete field, by bespoke validation fused into statement desugaring
    (`Process.desugar`/`Declarations.desugarCheck`) — one `CorePlusCal.Algorithm`, always
    fully checked, no coexisting "raw, still-generic" shape. `CorePlusCal.Process` carries
    `mailbox : Option (String × List β)` (from at most one `@mailbox`, `extractMailbox`);
    `Declarations.variables` carries `isParameter : Bool` (from `@parameter`'s presence,
    `Declarations.desugarCheck`). `CoreTLAPlus.Expression` needs no AST change — already
    `Bifunctor`/`Bitraversable`-generic in its annotation type, so `Expression (Option Typ)`
    is just a different instantiation.
  - **A `with`-bound variable can carry its own `@type` annotation**
    (`with (* @type: Int; *) x = e { … }`). `CorePlusCal`/`SurfacePlusCal Statement.with`'s
    `vars` has an `α` slot (`String × α × Bool × β`, matching every other binder-like
    site), `Parser_/PlusCal.lean`'s `parseWith` calls `tryParseAnnotations` per binder —
    using a bare `token (.tla .lparen)` (no `lexeme`) for the wrapping paren, not `parens`
    (which would swallow the first binder's own annotation comment as trailing
    whitespace) — same workaround `parseFilter` (multicast) already uses for the identical
    problem.
  - `@mailbox`'s filter arguments (`var[e₁, …, eₙ]`) are desugared to
    `CoreTLAPlus.Expression` via `SurfaceTLAPlus.Expression.desugar` run directly inside
    `Process.desugar`, through a throwaway local instantiation of the same
    `ReaderT (Option (CoreTLAPlus.Expression α)) (DiagT DesugarWarning DesugarError IO)`
    stack `SurfaceTLAPlus.Module.runDesugarer` already uses at the top level
    (`desugarMailboxArg`) — draws from the same process-wide fresh-name counter as
    everything else (§2's Flags/`Ξ` decision row), not an isolated `0`-restarted one.
  - **A multi-binder `with` desugars to a chain of single-binder `with`s.**
    `with (x = e1, y ∈ e2, …) { B }` (a genuine comma list at surface syntax, unchanged in
    `SurfacePlusCal.Statement.with`) desugars to `with (x = e1) { with (y ∈ e2) { … B } }`
    — real PlusCal's own `with` binds exactly one variable at a time and every downstream
    backend can rely on that directly. `CorePlusCal.Statement.with` has five separate
    fields (`var : String`, `ann : α`, `«=|∈» : Bool`, `val : β`, plus body `Block`) — one
    binder per `with`, full stop, encoded at the type level (same convention as
    `Statement`'s `Bool`-indexed terminal/non-terminal split). `Desugarer/PlusCal.lean`'s
    `buildWithChain` (mirrors `buildBranches`'s "fold a list into a right-nested chain")
    does the flattening: innermost binder wraps the already-desugared original body
    directly; every binder before it wraps the next link in the chain inside a
    label-free `Block` of its own (`⟨[], ·⟩`). `Statement.desugarLabelFree`'s `.with` case
    calls it; `WithContext`'s
    bound-name tracking extends with *every* binder's name for the *whole* original body
    in one step regardless.
  - **Every function call/`EXCEPT` index is unary.** `CoreTLAPlus.Expression.fnCall`/
    `.except` take a single `Expression α` each (not `List (Expression α)`) — a surface
    multi-index call `f[e₁, …, eₙ]` (`n > 1`, same for an `EXCEPT` path step
    `![e₁, …, eₙ]`) desugars to tuple-application `f[<<e₁, …, eₙ>>]`; a single-index call
    `f[e]` (`n = 1`) stays exactly that — **never** `f[<<e>>]`. `SurfaceTLAPlus.Expression.
    fnCall`/`.except` unchanged (still `List`, matching real surface-syntax comma list) —
    collapse happens in `Desugarer/TLAPlus.lean`'s `Expression.desugar`, via
    `wrapIndices : List (Expression α) → Expression α` (`[e] => e`, `es => .tuple es`)
    alongside the pre-existing `tupleProj`.
  - **`SurfacePlusCal`/`CorePlusCal.Ref` (a PlusCal assignment target, `f[e₁, …, eₙ] :=
    v`, or a `receive`/`send`'s channel argument) gets the same unary treatment, plus real
    field-access support.** `Ref.args` is `List (String ⊕ List β)` at the Surface layer
    and `List (String ⊕ β)` everywhere past desugaring (`CorePlusCal.Ref`,
    `ElaboratedPlusCal.Ref` shared by `TypedPlusCal`/`ComputablePlusCal`) — one entry per
    path segment, in left-to-right textual order, `.inl` for a `.field` segment and `.inr`
    for a `[e₁, …, eₙ]` bracket-index group (mirroring the same `String ⊕ _` shape
    `ComputableTLAPlus.Expression.except`'s update-path already uses, rather than
    inventing a different one). The same "always unary, `n > 1` wraps in a tuple" rule
    applies per `.inr` group: `f[e₁, …, eₙ] := v` (`n > 1`, one group) desugars to
    `f[<<e₁, …, eₙ>>] := v`; `f[e₁][e₂] := v` (two groups) unaffected either way, each
    group still single-index; `f[e] := v` stays exactly that; `r.field := v` is a bare
    `.inl` segment, no unary treatment needed. `SurfacePlusCal.Ref`/`CorePlusCal.Ref`/
    `ElaboratedPlusCal.Ref` each keep their own `Functor`/`Traversable` instance (or, for
    `ElaboratedPlusCal.Ref`, hand-written per-caller mapping — it carries its own resolved
    `baseType : τ` field (the *base variable*'s own type, from `Γ`, before any `.args`
    segment is applied — not the reference's final/result type, which is always cheap to
    recompute from `baseType` plus `args` via `Ref.stepType`/`.resultType`, walking the same
    structural step-rule `stepInto`/`indexInto` use at check time, and which the reverse
    direction can't do: an intermediate step's own type isn't recoverable from just the
    final result type without the base type to begin with) so isn't itself `Functor`/
    `Traversable`), mapping/traversing only the `.inr` side, `.inl` field names passed
    through untouched. `CorePlusCal.Statement.
    assign`/`.receive`/`.send` reference `CorePlusCal.Ref`. The conversion
    (`SurfacePlusCal.Ref → CorePlusCal.Ref`, `Desugarer/PlusCal.lean`'s `Ref.desugarRef`,
    reusing `SurfaceTLAPlus.wrapIndices` on each `.inr` group via `Sum.map id`) happens
    inline in `Statement.desugarLabelFree`'s `.assign`/`.receive`/`.send` cases.
    `Parser_/PlusCal.lean`'s `parseRef` parses `.`-segments interleaved with bracket
    groups by reusing the same `.`-token machinery `SurfaceTLAPlus.Parser.parseExcept`'s
    own path parser already has. `Elaborator/PlusCal.lean`'s `inferRef` (the `Ref`-typing
    judgment, a `Γ`-lookup on `name` followed by one step per path segment) reuses
    `Elaborator/Expressions.lean`'s `stepInto` directly — the same `.inl`
    record-field-access/`.inr` index-into dispatch `EXCEPT` paths already use — rather
    than duplicating that rule. `WellFormedness/Reachability.lean`'s `walkRefArgs` and
    `Core/SurfacePlusCal/Pretty.lean`'s `Ref` formatter both walk `.inr` entries only,
    rendering/recursing into a `.inl` field name being meaningless (`.inl f` prints as
    `.f`, `.inr e` as `[e]`, interleaved in path order).

### 5.2a Well-formedness checking
**Input/output:** `CoreTLAPlus`/`CorePlusCal` — checking pass, not a transform: accepts
the term or rejects it with a diagnostic, produces no new AST. Runs **after** type
checking (§5.3), not immediately after desugaring (§5.2) — see §2's pipeline-order
decision for why. All three checks below are purely syntactic — no typing needed,
declarations/gotos/operator shapes already resolved by the time `CorePlusCal`/
`CoreTLAPlus` exist.

- **Well-labelledness**, grounded in the PlusCal manual's placement rules
  (`https://lamport.azurewebsites.net/tla/p-manual.pdf`, §3.2's statement-by-statement
  rules, §3.7's exhaustive list). Not every rule needs a fresh check here — some are
  already impossible to violate by the time a term reaches `CorePlusCal`:
  - **Guaranteed by `CorePlusCal`'s type itself, for any term of that type regardless of
    producer:** every thread starts with a label and every block ends in exactly one
    terminal statement (`Process.threads : List (List (String × Block α β true))`'s own
    shape — `Statement α β true` has no constructor except `goto`); "an `if`/`either`
    that contains a labelled statement or `goto` anywhere within it must be followed by a
    label" (§3.2.2/§3.2.3) — `CorePlusCal.Statement.if`/`.either`'s `Bool` index forces
    both branches to share one terminality, so if extraction made either branch terminal
    the whole `if`/`either` is itself `Statement α β true` and can only be a block's own
    terminal `end`.
  - **Guaranteed today because `Desugarer/PlusCal.lean` (§5.2) is the only producer of
    `CorePlusCal` terms and correctly enforces it** — not type-encoded, so a latent risk
    if that ever stops being the only producer: "a `while` statement must be labeled"
    (§3.2.4/§3.7 — `CorePlusCal.Statement.while` carries no such restriction in its own
    type, enforced by the desugarer throwing `whileNotLabelled`); "`with`'s body cannot
    contain a labelled statement, a `goto`, or a `while`" (§3.2.6 — enforced by
    `nestedLabel`/`whileInWith`).
  - **Not guaranteed by anything upstream — this pass's actual, new work:**
    - *Every `goto` targets a label that actually exists* in the enclosing process/thread
      (or is the reserved `"Done"` sentinel). §5.3's `[Goto]` rule performs no check of
      its own (correctly — a `String` label name is just data, not something
      `CorePlusCal`'s type can guarantee resolves).
    - *No two assignments to the same variable within one atomic step, on the same
      control path* (§3.2.1/§3.7) — walk each labelled block's statements, treating an
      `if`/`either`'s separate branches as separate control paths (two *different*
      branches assigning to the same variable is fine; the same branch doing so, or one
      branch and whatever both converge to afterward, is not). Implemented in
      `Desugarer/PlusCal.lean`'s `CorePlusCal.{Statement,Block,Branches}.
      checkAssignConflicts`, mutually recursive over the three types, run from
      `SurfacePlusCal.Algorithm.runDesugarer` right after goto-explicitization, before
      `stripEmbeddedTypeAnnotations`. Tracks writes by *base variable* (`Ref.name`),
      regardless of indexing, from `assign` (every entry of a `||`-list) and `receive`'s —
      **both** `Ref`s, the channel `c` as well as the target `x` (`receive(x, a);
      receive(x, b)` errors, same as re-assigning/re-receiving into `x` itself).
      `x[0] := 3; x[1] := 4` conflicts under this rule even though the two writes touch
      different elements — deciding whether two indexed writes actually alias needs index
      comparison, out of scope for this purely syntactic pass, so it conservatively treats
      any two writes to the same base variable as a conflict regardless of indexing.
      `if`/`either` branches checked independently (starting from the same already-seen
      set) but their writes unioned into what continues past them. `while`/`with` bodies
      checked sequentially, merged with everything around them. New `DesugarError.
      conflictingAssignment (pos) (name)`.
    - *The reserved label `"Done"` is never redefined as an actual, user-written label*
      (§3.7) — `"Error"`'s equivalent restriction doesn't apply (no procedures exist in
      this language subset, §3.4/§8, no implicit `Error` label to collide with).
  - **Optional, defense-in-depth:** re-verifying the "guaranteed by the desugarer" bullet
    directly on `CorePlusCal` isn't required as things stand — cheap to add if wanted;
    revisit if `CorePlusCal` terms ever start being producible some other way.
- **Variable well-scopedness.** Every variable reference resolves to a declared name of
  the right kind (global, channel, process-local, or block-local `with`/`let` binding —
  matching prior art's Σ/Δ/Γ/Ξ scope classes), every `with`/`let` binder fresh in its
  scope, no duplicate names within a scope. Running after type checking makes the first
  half ("resolves to a declared name") redundant with type checking's own success (a
  no-op check kept mainly for documentation/defense-in-depth). The second half — every
  binder fresh, no duplicate names in one scope — is **not** implied by type checking and
  stays this pass's genuine, load-bearing work: ordinary bidirectional type checking has
  no reason to reject shadowing. Exactly what the prototype's
  `Core/GuardedPlusCal/Syntax/WellScopedness.lean` and
  `Core/TypedSetTheory/Syntax/WellScopedness.lean` encode as Lean `Prop`s (Finset-based
  scopes, one predicate per scope class, threaded through `await`/`with`/`receive`/
  `send`/assignment). **Port both files** (with cleanup) as the third ported-not-fresh
  exception alongside the lexer/parser and Guarded→Network (§2) — repurposed: rather than
  the primary mechanism rejecting malformed programs (this new pass does that, well
  before `GuardedPlusCal`/`TypedSetTheory` exist), they become the formal restatement of
  the same invariant at those later stages. `GuardedPlusCal.Algorithm.WellScoped` is the
  standing hypothesis Guarded→Network's refinement proof (§5.5) assumes, established via
  the general preservation lemma (§2, §5.5). This freshness/hygiene discipline is also,
  per §2, exactly what the compiler must maintain at *every* pass — the ported
  `Statement.FreshIn`/`AtomicBranch.FreshIn`/`Process.FreshIn` predicates (alongside
  `WellScopedness.lean` itself) are prior art's version, worth porting together as the
  frontend half of the general renaming/hygiene mechanism (§5.6, §5.7 have the backend
  half).
- **`CorePlusCal.WellScoped` itself is not one of the two ported files, authored fresh.**
  Preservation lemma (§2) is literally `CorePlusCal.WellScoped p → GuardedPlusCal.
  Algorithm.WellScoped (Computable2Guarded (Elaborator p))` — its antecedent is a
  `CorePlusCal`-level well-scopedness `Prop`, no such file exists in prior art at any
  stage. This pass's actual, executable well-scopedness check (bullet above) is the
  *runtime* half; `CorePlusCal.WellScoped` is the *Prop* half the preservation lemma's
  statement needs to even type-check — design new, closely modeled on the two ported
  files' shape (Finset-based scope classes, same `with`/`let` freshness discipline), but
  adapted to `CorePlusCal`'s own (pre-`Elaborator`, pre-`Computable2Guarded`) structure.
- **No bare temporal or action operators inside PlusCal-statement expressions.** None of
  `[]`/`<>`/`ENABLED`/`UNCHANGED` (prefix) or `'`/`^+`/`^*`/`^#` (postfix) may appear
  inside any expression embedded directly in a PlusCal statement (`assign`, `await`,
  `print`, `assert`, guard expressions, …) — Distributed PlusCal's own statement-level
  expressions have no business using temporal/action syntax, even though the surrounding
  TLA+ module may, elsewhere. **This check is transitive, not direct-only**: an operator
  the algorithm calls, whose own body contains temporal/action content, is banned too —
  same no-shared-memory concern as this pass's other two checks (2(c)/2(d)): an operator
  called from the algorithm shouldn't leak temporal/action content (or a global
  `VARIABLE` reference, or a channel value) into the algorithm any more than writing it
  directly would. `Typed2Computable` (§5.3) treats "every expression reachable from the
  algorithm is already free of temporal/action operators" as an already-established
  invariant, not something it re-derives. Same transitive scoping applies to this pass's
  unbounded-quantifier ban (`WellFormednessError.unboundedQuantifier`, not in the thesis)
  — scoped identically to the temporal/action ban, only to what's reachable *from the
  algorithm*. `Typed2Computable`'s own scope turned out to be exactly this same
  reachability closure, never anything wider — it treats both guarantees (temporal/action
  freedom, bounded quantifiers) as already established: no temporal/action constructor
  exists in `ComputableTLAPlus.Expression` at all, and `forall`/`exists`/`choose`'s domain
  field is a plain `Expression`, not `Option (Expression)` — enforced structurally.

### 5.3 Type checking
**Input:** `CoreTLAPlus`/`CorePlusCal`. **Output:** `TypedTLAPlus`/`TypedPlusCal`.

`ComputableTLAPlus`/`ComputablePlusCal` (`TypedTLAPlus`/`TypedPlusCal` minus the handful
of constructs with no finite runtime representation) is **not** an output of this pass,
despite sitting next to `TypedTLAPlus`/`TypedPlusCal` in §4's layout — separate,
subsequent pass, `Typed2Computable`: given the already type-checked *and well-formed*
algorithm (`WellFormedness`, §5.2a, must already have run and passed), collect every
constant/variable/operator/function transitively reachable from the algorithm (own-module
or `EXTENDS`-ed, flattened into one output module regardless of origin — a reference into
a builtin/stdlib module is dropped outright rather than translated, since backends
replace every stdlib operator at code-generation time regardless of what its stub
"definition" says) and translate each, plus the algorithm itself, into
`ComputableTLAPlus`/`ComputablePlusCal`. Doesn't re-derive the temporal/action ban (see
§5.2a's transitive-scope note). What `Typed2Computable` *does* add, genuinely new: rejects
`[A -> B]` (`fnSet`) and `[a:A,...]` (`recordSet`) outright — no finite runtime
representation under this compiler's finite-sets assumption. Designed as its own small
pass downstream of the type checker (§7 phases it separately). Its output is where the
ported `Core/ComputableTLAPlus/Syntax/WellScopedness.lean` (§5.2a) applies, restated over
`ComputableTLAPlus`'s typed expressions.

Fully specified in thesis §3.1 — implement rules essentially as written, one deliberate
deviation (polymorphism instantiation, below):

- **Type grammar** (Apalache "Type System 1", extended): `Bool | Int | Str | τ→τ | Set(τ)
  | Seq(τ) | ⟨τ,...⟩ | (τ,...)⇒τ | Const | a | [x:τ,...]`, plus three implementation-level
  extensions: `Address` and `Channel(τ)` (channels deliberately not just `Seq(τ)` at the
  type level, even though that's their encoding, so channel operations restrict to
  `send`/`receive`/`multicast` and stay out of arbitrary expressions — `Channel` is
  covariant: `τ <: τ' ⟹ Channel(τ) <: Channel(τ')`), and metavariables `?n` (distinct from
  rigid, universally-quantified `a`) — mutable placeholders polymorphism instantiation
  (below) resolves during checking, never appearing in a fully-elaborated `TypedTLAPlus`
  term.
- **`<:` is a genuine partial order here, not just a preorder** — structural rules (SEQ,
  SET, FUNCTION, TUPLE, RECORD, OPERATOR) can't create cycles on their own, and the three
  non-structural coercions (`Str <: Seq(Int)`, `Seq(τ) <: Int → τ`, `⟨τ,...⟩ <: Seq(τ)`
  for a uniform tuple) are one-directional between syntactically distinct constructors, so
  no way to derive both `τ <: τ'` and `τ' <: τ` for distinct `τ`, `τ'`. **No `⊤`/`⊥`** in
  this grammar (no universal super-/sub-type), so not a full lattice — `lub`/`glb` are
  still well-defined by `<:` in the standard way, but as *partial* functions (e.g.
  `lub(Bool, Int)` doesn't exist). Polymorphism instantiation needs exactly this partial
  `lub`, not a full lattice.
- **Discipline:** bidirectional (checking `Γ ⊢ e ⇐ τ` / synthesis `Γ ⊢ e ⇒ τ`), rank-1
  polymorphism only (type variables collected into a prenex `∀`, no first-class schemes).
  Annotations required only at binders the algorithm can't otherwise pin down (thesis
  §3.1.1). `RECURSIVE` operator declarations out of scope (§2, §8).
- **Polymorphism instantiation — do not implement the thesis's `Specialize` rule as
  written.** Instead (per the local `Checker/Typechecker/` code — `Convertibility.lean`,
  `Rules.lean`, read before implementing): generate one fresh metavariable `?n` per bound
  type variable when a polymorphic operator is used, resolve incrementally as subtyping
  checks run against them, defaulting whatever remains at the very end of checking (one
  defaulting point per declaration, precisely because rank-1 only, no let-generalization).
  Direction-aware solving, not naive eager unification — subtyping axioms are asymmetric
  coercions:
  - A metavariable `?n` is tracked **unresolved** (with pending upper bounds accumulated)
    or **resolved** to a concrete monotype.
  - **Lower-bound constraint `T <: ?n`**: if `?n` unresolved, solve `?n := T` immediately
    (coercion `id`), first checking `T` against any pending upper bounds already recorded
    (recursively). If `?n` resolved to `S`, require `T <: S` (recursively) — coercion at
    this site is `coerce(T <: S)`. If `T <: S` fails: principled fix is widening `?n`'s
    solution to `lub(S, T)`, pragmatic option (used here, given how rare a second
    incomparable lower bound is without let-generalization) is to error and require an
    explicit annotation instead of implementing `lub`.
  - **Upper-bound constraint `?n <: T`**: if `?n` unresolved, do **not** solve it to `T`
    yet — only record `T` as a pending upper bound (keeping either the running `glb` of
    all bounds seen so far, or the list). If `?n` resolved to `S`, check `S <: T` directly,
    coercion `coerce(S <: T)`.
  - **Why the asymmetry:** a lower bound tells the *smallest* `?n` can be, safe to commit
    immediately, since axioms hand coercions narrow→wide. An upper bound tells the
    *largest* `?n` can be; committing immediately would foreclose a narrower solution
    arriving later from a lower bound not yet seen.
  - **Metavariable-vs-metavariable constraints (`?m <: ?n`, both unresolved) don't reduce
    to either base case** — `T` in those rules is always ground; no ground type here yet.
    **Do not solve `?n := ?m`** (merge into one shared cell) — `?m` is a live,
    independently constrained unknown, merging conflates its constraint set with `?n`'s;
    since `<:` is genuine coercive subtyping (not equality), `?m <: ?n` only requires
    `?n` at least as wide as whatever `?m` becomes, not identical — legitimate satisfying
    assignments can diverge to different (but `<:`-related) monotypes. Example: `?m <: ?n`
    alongside unrelated `?m <: Str` and `Seq(Int) <: ?n` is satisfiable with `?m := Str`,
    `?n := Seq(Int)` (both stay separate) — merging on sight of `?m <: ?n` would spuriously
    force `Seq(Int) <: Str`. **Instead: record `?n` as one of `?m`'s pending upper bounds**
    (a `PendingUpperBounds` entry can itself be a metavariable) and leave `?n` untouched.
    When `?m` later resolves from a real ground lower bound, walk its pending-bounds list
    and re-fire the ordinary rules against each entry. A stray `?m <: ?n` where *both*
    remain unresolved at end-of-check is a type error, same reason "no bounds at all" is
    one.
  - **Defaulting**, at the single end-of-check point: a metavariable with only upper
    bounds recorded defaults to the tightest one (or errors "ambiguous type"); one with
    **no bounds at all is a type error** — never checking-failed-to-solve-silently.
  - **Implementation cost**: no let-generalization means no full MLsub-style
    bounds-lattice needed — a `Map MetaVar (Unresolved pendingUpperBounds | Resolved τ)`
    plus the cases above, "error on a second incomparable lower bound" standing in for a
    real `lub`, is enough.
  - **The underlying judgment** — `subtype : Context → Type → Type → SubtypeResult`,
    threading the metavariable-solution context, yields **three** outcomes: a
    **successful coercion** (concrete `Coercion`, plus updated context), a **pending
    coercion** (check succeeded but coercion depends on a not-yet-known metavariable
    solution — recorded as a pending upper bound), or **failure**.
  - **`Coercion` is closed structural data, not a closure** (§2) — discharged against an
    already-*elaborated* expression by `Coercion.apply`/`.applyComputable`, turning a value
    of type `A` into one of type `B`.
  - **`mvar`: an expression-level placeholder for a pending coercion.** When `subtype`
    yields pending, the elaborated expression at that use site is wrapped in a new
    constructor, `mvar : MVarId → Expr → Expr`, added to `TypedTLAPlus`/`TypedPlusCal`'s
    expression grammar — tagged by which metavariable it's waiting on.
  - **Resolving placeholders — against the existing `pendingUpperBounds` context
    directly, no separate lockstep site-tracking table.** `mvar n e`'s wrapped `e`'s true
    type is exactly `?n`, and since `specializeOperator` mints a fresh metavariable per
    operator-call use and each is only ever the source of the one `subtype` call that
    builds its own `mvar` wrapper, in every case reachable from the checker's own code
    `?n`'s `pendingUpperBounds` list has *exactly one* entry. Resolution at the
    end-of-check point (end of each declaration, `Elaborator/Declarations.lean`): for
    every `mvar n e` found in that declaration's elaborated expressions, look up `?n`'s
    `pendingUpperBounds` — `[]` is the genuine "never constrained" error; a single entry
    `b` assigns `?n := b`, substitutes `coerce(b <: b) = id`; **more than one entry is a
    loud, named gap** (`.todo`), not a silent guess — real per-site tracking would be
    needed to substitute soundly, no concrete program has produced one yet. By the time
    one declaration's checking finishes, every `mvar` node it introduced is eliminated,
    so what `Computable2Guarded` and both backends eventually see is `mvar`-free.
- **Statement judgment** `Γ | Ξ ⊩ S ok` (no output type — statements checked for effects,
  not typed). Notable asymmetric rules, thesis §3.1.5: `[Assign]` synthesizes LHS type,
  *checks* RHS against it (not reverse — enables upcasting RHS via subtyping); `[Send]`
  asymmetric the same way (synthesizes channel type to allow upcasting the payload);
  `[Print]` requires a `showable` type (Fig. 3.1.14: everything except function/operator/
  channel types, recursively); `[Goto]` performs no type check at all — label existence
  checked separately, by well-formedness (§5.2a), not the type checker.
- **A channel's declared element type must be `sendable`.** Same restriction shape as
  `showable` (`Operator`/`Channel`/`Const`/rigid type variables, and anything containing
  one, excluded; recurses through `Function`/`Set`/`Seq`/`Tuple`/`Record` otherwise) — a
  genuinely separate predicate (`Elaborator/PlusCal.lean`'s `sendable`, not a reuse of
  `showable`, distinct restrictions that happen to coincide today, including excluding
  `Const`: a `CONSTANT` is substituted by the user *after* code generation, and an
  unsendable instantiation would silently break the invariant if `Const` were allowed
  through). Checked once, in `checkChannelDecl`, at channel-declaration time — covers
  `send`/`receive`/`multicast` uniformly. New error variant `TCError.notSendable`. Both
  `showable` and `sendable` are pure, non-monadic `Typ → Bool` predicates — callers
  resolve pending metavariables first (`resolveTypeMVarsForDisplay`) so `.mvar` only means
  "genuinely still unresolved." **One consequence**: a channel-of-channels
  (`Channel(Channel(τ))`) declaration is a hard error — combined with `Channel`'s
  reflexivity-only subtyping, means well-formedness's `channelInExpression` check can no
  longer be exercised via `receive`'s destination `r` resolving to a channel-shaped type
  (see §9.13).
- **`[Receive]` — channel/reference coercion.** `Channel` is covariant
  (`Elaborator/Subtyping.lean`), but a channel-typed expression's own
  `Channel(τ) <: Channel(τ')` check only ever produces `Coercion.id` in practice —
  `TypedTLAPlus.Expression` has no general term former to wrap an opaque channel value
  with, and doesn't need one: channels never change runtime representation between the
  checker and either backend. What *does* need a real coercion is the **received value
  itself** — the incoming message's element type `τ` may be narrower than the destination
  reference's own type `τ'` (`τ <: τ'`), and there's no elaborated sub-expression to hand
  that coercion to. Synthesize both the channel's element type and the reference's type,
  `subtype` them directly (independent of the `Channel` vs. `Channel` structural check
  above, stays identity-only), store the resulting `Coercion` on the
  `TypedPlusCal`/`GuardedPlusCal` `receive` statement node — carried through
  `Computable2Guarded` (§5.4) unchanged, only actually applied by `Guarded2Network` (§5.5).
- **`Ξ` is a global cache, not threaded state — in-memory only for now, no disk
  persistence (§2).** On paper an input to the judgment like `Γ`, in practice a
  `MonadModuleCache m` effect (`lookup`/`store` keyed by a hash of each module's source)
  rather than passed around explicitly, so a module doesn't get fully re-type-checked from
  scratch every time it's referenced (e.g. repeatedly, via `EXTENDS`, within one compiler
  run).
- **Module resolution and TLA+ standard modules (`EXTENDS Sequences, TLC, ...`).**
  `-I <path>` (§9.3) adds a search path for locating `.tla` modules referenced via
  `EXTENDS`. (`INSTANCE` out of scope — not parsed, not resolved, not type-checked; the
  search-path/caching mechanism only needs to handle `EXTENDS`.) **Resolution is eager and
  transitive, not lazy** — see §2's row on this. Only once the whole transitive closure is
  resolved does the main module's own type checker begin, so every `Ξ` lookup it performs
  is guaranteed already populated. TLA+'s actual standard modules (`Sequences`, `TLC`,
  `Naturals`, `FiniteSets`, etc.) are **not** parsed from the real standard library — the
  compiler bundles its own stub versions, only enough to get operators like `Len`, `Head`,
  `Append` correctly typed, not real definitions. `builtinContext`
  (`Elaborator/Declarations.lean`) carries only the ~14 genuinely `EXTENDS`-independent
  intrinsics (`=`, `/=`, `/\`, `\/`, `=>`, `<=>`, `\neg`, `\in`, `\notin`, `\subseteq`,
  `\cup`, `\cap`, `\`, `DOMAIN`, plus the temporal ones, §9.11). Everything else —
  `+`/`-`/`-.`/`*`/`..`/comparisons/`Nat` (`Naturals`), `Len`/`Head`/`Tail`/`Append`
  (`Sequences`), and populated entries for `Bags`/`FiniteSets`/`Integers` — lives as real
  declarations in `Driver/Modules.lean`'s `builtinModules["Naturals"]` etc.
  (`naturalsDeclarations`/`sequencesDeclarations`/`bagsDeclarations`/
  `finiteSetsDeclarations`/`integersDeclarations`, cross-checked against the real
  standard-module sources); a module only sees `+`/`Len`/… via an actual
  `EXTENDS Naturals`/`EXTENDS Sequences`, resolved through the same `Γ₀`-merge machinery
  `compileModule` uses for ordinary dependencies. Builtin-`EXTENDS`ing-builtin works too
  (`Sequences` itself `EXTENDS Naturals`, matching real TLA⁺, `«extends» := ["Naturals"]`
  on its table entry) — `resolveModule`'s `.builtin` case resolves `mod.extends`
  recursively the same way its `.file` case does, merging dependency declarations in.
  Each `«extends»` list mirrors its real module's full top-of-file dependency list,
  `LOCAL INSTANCE` included, not just plain `EXTENDS`. A `LOCAL`-declared helper (e.g.
  `Bags`'s `Sum`) stays excluded from the exported declaration list. `RealTime`/`Reals`
  deliberately excluded (out of scope); `TLC` deliberately stays an empty stub. Each
  declaration only needs a name/type binding (`Decl.bindings`) — bodies never re-examined,
  since standard-library operators get replaced by backend-native implementations at
  code-generation time. A top-level `operator`/`function` definition — any arity,
  `builtinContext`'s entries included — is always a **let-generalized scheme**
  (`Elaborator/Monad.lean`'s `Binding` carries a `Typ` plus `isScheme : Bool`); freshened
  on every `Γ`-reference (`Elaborator/TypeUtils.lean`'s `specializeType`), not just on
  call. `CONSTANT`/`VARIABLE` declarations and every ordinary binder (operator/function
  parameters, quantifiers, `CHOOSE`, `EXCEPT`, PlusCal variables/channels) stay
  monomorphic — `extend`/`extendAll` hardcoded to insert monomorphically, by construction.
- **Process/algorithm judgments** thread `self : Address` into scope, require process-ID
  sets to be `Set(Address)`, require all channel declarations to be functions of
  addresses to `Channel(τ)`.
- **`CONSTANT`s stay abstract through the whole pipeline (§2).** Type-checked (given a
  type, per annotation or inference) like any other name in `Γ`, never given a value by
  this compiler.

### 5.4 Distributed PlusCal → Guarded PlusCal (`Computable2Guarded`)
**Input:** `ComputablePlusCal.Algorithm` (§5.3's `Typed2Computable` output). **Output:**
`GuardedPlusCal` (a restriction where every `await`/`receive`/`with` sits at the very
start of its atomic block).

Defined in the thesis (§3.2.3) as `𝒞_reord ∘ 𝒞_flat ∘ 𝒞_par ∘ 𝒞_cflow` (order between
`𝒞_par` and `𝒞_cflow` doesn't matter; the other two are order-dependent). Four small,
independently-testable passes composed in this order:

1. **`𝒞_cflow`** — rewrite `if`/conditional-`while` into `either`/`await`:
   `while e {B1}; B2; goto l'` (at label `l`) ⟶ `l: if e then {B1; goto l} else {B2; goto
   l'}`, and `if e then B1 else B2` ⟶ `either {await e; B1} or {await ¬e; B2}`. Justified
   by the actual PlusCal→TLA+ action semantics (an `if` compiles to an action equivalent
   to `(e ∧ 𝓔(B1)) ∨ (¬e ∧ 𝓔(B2))`).
2. **`𝒞_par`** — sequentialize parallel assignments (`r1≔e1 ∥ ... ∥ rn≔en`). Handles
   aliasing correctly (`x[0]≔3 ∥ x[x[0]]≔7`): evaluate all RHSs into fresh temporaries
   first, then all LHS *indices* into fresh temporaries, then perform assignments
   left-to-right using the partially-evaluated references. Thesis gives full recursive
   definition over reference shapes (`x`, `r[e]`, `r.x`) — implement exactly that.
3. **`𝒞_flat`** — flatten nested `either`s into flat lists of branches, by distributing
   sequencing over choice (`B; either{B1} or ... or {Bn}; B'` ⟶ `either{B;B1;B'} or ...`)
   and using associativity of `either`. Trades code size for fewer runtime choice points /
   less need for transactional rollback machinery downstream.
4. **`𝒞_reord`** — float every `await` **and every `receive`** to the front of its branch,
   commuting each leftward past `skip`/`print`/`assert`/`send`/`multicast` (all
   guard-independent) and past assignments via substitution. Fully specified in thesis
   §3.2.3.4, one mirrored equation per statement kind, `await`/`receive` treated
   symmetrically throughout:
   - `assert`/`print`/`skip` commute with both `await` and `receive` trivially — none of
     the three ever affects program state (read-only), so reordering changes nothing
     observable: `𝒞_reord(skip; await e') = await e'; skip`, `𝒞_reord(skip; receive(c,r)) =
     receive(c,r); skip`, same shape for `print e`/`assert e` in place of `skip`.
   - `send`/`multicast` commute with both for the same reason as each other: channels are
     forbidden from appearing in any ordinary expression (so an `await`'s guard can never
     depend on one), and `receive`'s own channel `c'` is guaranteed distinct from the
     `send`/`multicast`'s channel `c`/`x` by the existing "no two operations on the same
     channel in one atomic block" restriction (§5.2, `Statement.checkRefRestrictions`) — so
     `𝒞_reord(send(c,e); receive(c',r)) = receive(c',r); send(c,e)` is sound precisely
     because `c ≠ c'` is already structurally guaranteed going in.
   - Past an assignment, both require genuine substitution, via the same helper
     `e'[e\r]` (substitute reference `r` by `e` in `e'`, using `EXCEPT` when `r` has an
     index) — worked through in the thesis via the Two-Phase Commit `c2` example (Listings
     3.2.1–3.2.4): `𝒞_reord(r≔e; await e') = await e'[e\r]; r≔e` substitutes into the
     *plain expression* `e'`. `𝒞_reord(r≔e; receive(c,r')) = receive(c[e\r], r'[e\r]);
     r≔e` reuses the identical helper, but applied to `c`/`r'` — both *references*, not
     plain expressions — where `e'[e\r]` is overloaded to substitute only within the
     target reference's own index positions, never its base variable name (a channel name
     or receive-destination can't itself be an arbitrary substituted expression). Sound
     because `r` and `r'` are always different base variables already (the existing
     no-repeated-write-to-one-variable-per-atomic-block restriction), so the substitution
     can never turn `r'` into `r` itself.

   Floating `receive` to the front removes most, but not all, of the need to undo partial
   state on a failed branch — `receive`'s own special case (a receive guard's truth depends
   on runtime message arrival, not just current-state evaluation like `await`) is carried
   forward and only fully resolved once `receive` becomes a concrete buffered read in
   `Guarded2Network` (§5.5), matching `GuardedPlusCal`'s existing invariant that every
   `await`/`receive`/`with` sits at the very start of its atomic block.

Worked example: thesis Listings 3.2.1–3.2.4 (the Two-Phase Commit `c2` block) — good first
target to hand-verify each subpass against.

### 5.5 Guarded PlusCal → Network PlusCal (`Guarded2Network`)
**Input:** `GuardedPlusCal`. **Output:** `NetworkPlusCal` (no `receive` guards; each
process gets an opaque `T_rx(mailbox → inbox)` thread buffering incoming messages into a
process-local `inbox` sequence variable, turning `receive(c, r)` into ordinary
`await Len(inbox) > 0`-guarded reads).

**This is also where `[Receive]`'s stored channel/reference coercion (§5.3, §2) finally
gets discharged** — first pass where a `receive(c, r)` becomes a concrete buffered read
(`await Len(inbox) > 0`) with actual generated code around it to splice the coercion into.
Every earlier pass just carries the `Coercion` value through unapplied on the `receive`
node. Discharged via `Coercion.applyComputable` (§2) directly against the freshly-built
`Head(inbox)`/`Tail(inbox)` `ComputableTLAPlus.Expression` — `Coercion` is closed structural
data specifically so this cross-stage discharge needs no lift back into
`TypedTLAPlus.Expression`.

One pass with a complete implementation *and* completed refinement proof in prior art
(`fugue` `main`: `PlusCalCompiler/Passes/GuardedToNetwork/{PlusCal,Lemmas}.lean`, against
`GuardedPlusCal/Semantics/Denotational.lean` and `NetworkPlusCal/Semantics/
Denotational.lean`). The ported `Core/GuardedPlusCal/Syntax/WellScopedness.lean` (§5.2a)
supplies the well-scopedness hypothesis this proof needs, established via the general
preservation lemma (§2) proved once over `Elaborator`/`Computable2Guarded`. Thesis chapter for
this pass (ch. 5) is itself a stub — **the code is the spec here, not the PDF.** Port the
pass and the proof (§2's one committed verified pass). Expect to adapt rather than copy
verbatim, since the source AST (`TypedPlusCal`/`GuardedPlusCal`) is being rewritten fresh
in this project, so denotational semantics and lemmas need re-deriving against the new
`Core/GuardedPlusCal/Syntax.lean`, though the mathematical content of the proof should
transfer.

### 5.6 Network PlusCal → the Join Calculus (`Network2JoinCalculus`) — NEW
**Input:** `NetworkPlusCal`. **Output:** `Core/JoinCalculus`, pretty-printed to a `.join`
(or similar) source file. Fully specified in thesis ch. 8; no existing code anywhere —
new implementation top to bottom.

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
for local solutions, `Register`/`Lookup`/`Str-Comm` for distributed global solutions
(named locations `α`, a name server `Γ` mapping registered tokens to locations). Full
rules in thesis Fig. 8.4.2–8.4.3. Not needed for the initial implementation — having
`Network2JoinCalculus` actually compile is the near-term goal; formalizing
`Core/JoinCalculus/Semantics/` is low priority, see §9.4.

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
  some concrete location `α`. A process set `p ∈ S` compiles to this **one** definition,
  not `|S|`-many — `p` is a single reusable definition parameterized over `self`, up to
  whoever runs the emitted `.join` file to `def p⟨α⟩` once per concrete process they
  want live, choosing `α` themselves (`S`'s actual membership never evaluated by this
  compiler, since `S` may depend on an unresolved `CONSTANT`).
- **Atomic blocks.** `l: {G1;S1;goto l1} or ... or {Gn;Sn;goto ln}` — each branch compiles
  to `def l⟨⟩ | x_a⟨x_a⟩ | ... | x_g⟨x_g⟩ if ⟨conjunction of Gi's awaits⟩ ⊳ ⟨updated state
  atoms⟩ | ⟨out⟨v⟩ per print⟩ | ⟨let send:=lookup α; send⟨e⟩ per send(c[α],e)⟩ | l_i⟨⟩`.
  The block's own label atom `l⟨⟩` is consumed and *not* re-emitted except by an explicit
  `goto l` in some branch — restricts the whole `either` to firing at most one branch at a
  time.

Ping-Pong worked all the way through in thesis §8.6 (both `rcvPi`/`sndPo` reactions and
the full process definition) — implementation's first target, by hand before automating.

`isFair` carried through unused: nothing about `𝒞` makes reaction-firing nondeterminism
fairness-aware (§2).

**Identifier hygiene.** `recv`, `inbox`, and per-block label atoms (`l⟨⟩`) are names `𝒞`
introduces, not source names — need the same collision-avoidance treatment as Go
keyword-escaping (§5.7's `sanitize`/`keywords` precedent), generalized to whatever the
guarded-reaction dialect's own reserved surface turns out to be.

Correctness of `𝒞` is not proven anywhere, and the emitted dialect (guards on reactions)
isn't accepted by existing Join Calculus implementations (JoCaml etc. don't support
`if e ⊳`) — the thesis sketches an encoding (`def J if e ⊳ P` as `def J ⊳ if e then P else
J`) but flags it as a performance-losing workaround, not a real answer. Emitting a
well-formed `.join` file faithful to this compilation scheme is the actual deliverable;
what happens to that file afterwards is §9.1.

### 5.7 Network PlusCal → Go (`Network2Go`) — including lock inference
**Input:** `NetworkPlusCal`. **Output:** `Core/Go`, pretty-printed to `.go`, depending on a
runtime library this project also owns (below).

**Target AST: the thesis's, not prior art's.** `Core/Go/Syntax.lean` implements thesis §6.6
(Definitions 6.6.1, 6.6.11–6.6.20) — real Go types (`int`/`str`/`bool`, `chan τ`, `[]τ`,
`[n]τ`, `map[τ₁]τ₂`, `struct`, `func`), Go expressions, and Go references (`_`, `x`, `r[e]`,
`r.x`). Prior art's `GoCal` diverged: it has no Go type or expression AST at all,
parameterizing its statement layer over TLA⁺ `TypedSetTheory.Typ`/`Expression` directly (both
that repo's `typechecker` and `go-semantics` branches carry the same version) — reference-only
here. Consequences: (a) blocks are `List Statement`, not §6.6's `; S` continuations, so
`var x τ` and channel `make` are position-scoped statements; (b) the AST adds composite
literals (struct/slice/map, `make`) and `Typ.named`/`Typ.var` beyond §6.6, since §7.2's
listings need `Lock[τ]`, `Receiver[T]`, `Set[T]`, `LazyFunction[T,U]`, `Address`, `Network`;
(c) generic in the repo-standard way — `(Typ Expr : Type)` parameters, `Bifunctor`/
`Bitraversable` instances, pinned abbrevs, namespaces `Go`/`ComputableGo`; (d) compiling TLA⁺
types and expressions *into* those Go ones (§7.2.1/§7.2.2, below) is real work this pass owns
— prior art got it for free by parameterization.

`Network2Go/PlusCal.lean` is real, working code — compiles Network PlusCal
processes/threads into genuinely concurrent Go (goroutines communicating over channels,
`go`, unbuffered/buffered `chan`, `send`/`receive`/`select`) — **except** for synchronizing
atomic blocks that touch shared process-local state when they run concurrently on different
goroutines.
Lock inference is the one missing piece to port around, not a reason to redesign the
backend. Also directly reusable: hand-written runtime scaffolding in
`distpcal-compiler/tests/*/{lib,nameserver}` (TCP/UDP address resolution + a name server
process for cross-machine address discovery — the practical, already-prototyped Go
analogue of §5.6's `register`/`lookup`).

**Caveat: that covers *intra-process* concurrency only, not `send`/`receive`'s
cross-process wire mechanism.** Goroutines over Go's native `chan` handle plumbing *within*
one compiled process (a thread and its `T_rx` counterpart passing buffered messages). But
`send(c, e)` addressed to a different, possibly remote process has to leave the process
entirely — that compilation scheme is undescribed, §9.7.

**Lock inference, concretely** — follows thesis §7.1.2's [HFP06]-derived scheme. Locks
are assigned **per process-local variable**, and a block may need to acquire *several*
locks (one per variable in its footprint, after merging):

1. For every atomic block `B` (computed over *all* blocks of the process, not just
   cross-thread pairs), let `shared(B)` be the set of process-local variables read from
   or written to in `B` (free variables in expression position, plus all
   indexed-assignment targets, minus any `with`-bound temporaries).
2. Define domination: `x ⪰ y` iff every block with `y ∈ shared(B)` also has
   `x ∈ shared(B)`; `x ≻ y` (strict domination) when additionally `x ≠ y`.
3. Lock selection (Definition 7.1.3): start with one fresh lock `ℓ_x` per variable `x`.
   For each variable `x`, if some `y ≻ x` exists, merge — redirect every variable
   currently assigned `ℓ_x` to `y`'s lock instead. This can only reduce the number of
   distinct locks below one-per-variable, never increase it.
4. Pick any total order `<` over the resulting set of locks (needed since a block may now
   hold more than one lock at once — a fixed acquisition order across all blocks avoids
   lock-ordering deadlocks). At the start of each block `B`, acquire the locks of
   `shared(B)` in that order; release them (order doesn't matter) at the end.
5. Final pruning pass: any lock used only within a single thread can be dropped entirely —
   blocks within one thread are already mutually exclusive by construction (Network
   PlusCal only ever runs one block of a given thread at a time).

Different design from a simpler one-lock-per-block scheme: this one holds potentially
several locks per block (ordered to avoid deadlock) rather than exactly one, groups by
variable-level domination rather than block-level connectivity. Implement steps 1–5
directly against Definition 7.1.3 and Examples 7.1.1/7.1.4/7.1.5 in the thesis.

`isFair` carried through unused: lock inference and Go's goroutine scheduler make no
attempt at fairness (§2).

**Identifier hygiene.** Per-block lock variable names are `Network2Go`-introduced, need
the same collision-avoidance treatment as §2 describes — `Core/Go/Pretty.lean` already
has a real, working mechanism for the adjacent problem (a PlusCal name colliding with a
Go keyword): `keywords : Std.HashSet String` table and a `sanitize` function suffixing any
colliding name with `__`, applied at every identifier-print point (record fields,
struct-literal keys, variable references, field access). Extend `keywords` to also cover
every name `Network2Go` itself introduces (lock variables and anything else lock inference
adds). The printer escapes reserved words only; renaming user-chosen names off Go's
*predeclared* identifiers is this pass's own job, against `Core/Go/Pretty.lean`'s exported
`predeclared` set — see §2's hygiene row for why the two can't be one table.

**Go representations of TLA+ types**, per thesis §7.2.1.1:
- `Bool`/`Str` → `bool`/`string`, as local newtypes (one name for the compiler to emit, and
  a type this runtime owns to hang the `BoolOrd`/`StrOrd` dictionaries off).
- `Int` → **`math/big`-backed by default**, machine `int` opt-in. This inverts the thesis,
  which defaults to machine integers for efficiency. Reason: TLA⁺ integers are unbounded
  and so are the integers of the denotational semantics this compiler is verified against,
  so a machine `int` silently wraps where the semantics says it must not — every
  correctness argument would then carry an overflow side condition on each arithmetic step.
  Paying allocation to avoid that is the right trade here; efficiency is the opt-in.
  **Selected by a Go build tag, not a Fugue flag**: `go build -tags fugue_machint`.
  There is no `-Xgo-bigint` and nothing representation-specific in emitted code — arithmetic
  goes through `Add`/`Sub`/`Neg`/`Mul` rather than Go's operators, comparisons through
  `IntOrd`, and literals through `MkInt`, so both representations present one surface and
  `runtime/tlaplus/int_{big,machine}.go` are the only files that differ. A literal too
  large for a machine `int` is a Go compile error under the machine build, which is that
  representation's restriction surfacing where it should. `go.mod` cannot carry a default
  build tag (its directives are `module`/`go`/`toolchain`/`godebug`/`require`/`exclude`/
  `replace`/`retract`/`tool`), so the untagged build is the safe one and speed is explicit.
  Consequences: `Int` is a struct wrapping `*big.Int` — forced, since Go forbids methods on
  a defined pointer type, so `type Int *big.Int` could not carry `String` — and its zero
  value holds a nil pointer, read as 0 by every operation, because `Go.Statement.var` emits
  zero-initialized `var x Int`. `ToInt` converts back for the places Go demands a machine
  integer (slice indices), panicking above that range; the only callers are indexing
  operations, and a sequence needing such an index cannot be held in memory anyway.
- Functions `τ → τ'` → lazy maps (wrapping `map[τ]τ'`, avoiding eagerly computing the
  whole graph at declaration time — mirrors what TLC does).
- `Set(τ)`/`Seq(τ)` → both `[]τ`; sets additionally carry a no-duplicates invariant (so
  `τ` must be comparable) not tracked at the Go type level. Sequences keep TLA+'s
  1-indexing by leaving slot 0 of the underlying slice unused/unobserved — so a sequence of
  `n` elements has underlying length `n+1`, with the nil slice admitted as a second
  spelling of the empty sequence so that a generated `var s Seq[τ]` needs no initializer.
  `Tail` is a reslice (the old first element becomes the new unused slot, shifting every
  index for free), which makes `Append` copy unconditionally: sequences produced by `Tail`
  share a backing array, and appending in place would write into it.
- Records/tuples → **anonymous** `struct`; tuples use `proj1`..`projN` field names (a tuple
  is sugar for a specific record shape). Nothing is named and nothing is declared: a
  dictionary can be built for an anonymous struct type directly, since `Ord` is a struct
  rather than an interface, and `ordDict` emits that literal beside the type. Named types
  were only ever wanted as somewhere to hang methods, so with the dictionary design they
  buy nothing — which removes name mangling, the per-specification type declarations, and
  any arity cap on tuples in one go. `compileTyp` sorting record fields by name stays
  load-bearing for a different reason than before: Go identifies anonymous struct types
  *structurally*, so sorting is what makes two identically-shaped records one Go type, and
  it fixes the lexicographic order the dictionary compares in. Cost, on emitted code only:
  the struct type is spelled at every occurrence and three times per dictionary literal, and
  `ordDict` being a pure fold re-emits a record's dictionary at each site that needs it.
  Hoisting dictionaries into package-level variables would fix both and reintroduce the
  naming question, so it waits for evidence that it matters.
- Operators `(τ1,...,τn) ⇒ τ` → plain Go `func`.
- Type variables → propagated to the nearest enclosing function definition (Go generics).
- Uninterpreted constant types → left as-is (same name), supplied by the user (matches
  the `CONSTANT` scope boundary).
- `Address` → an unspecified interface declaring `Eq`/`Lt` methods, bridged into a
  dictionary by `comm.AddressOrd` (method expressions, receiver-first). It requires an
  order, not just equality: addresses reach sets and function domains in the first real
  example, and a record with an address field would otherwise lose its order too. The order
  is arbitrary and integrator-supplied, which makes `CHOOSE` over a set of addresses
  implementation-dependent — legal, `CHOOSE` being deterministic-but-unspecified, but
  documented on `Address` since the behaviour then rests on a decision the specification did
  not make. The same holds for any uninterpreted constant type.
- `Channel(τ)` → no general Go value representation needed: "channels are not
  first-class citizens in Distributed PlusCal" — a channel is never stored, passed
  around, or put in a data structure as an ordinary TLA+ value, only ever appears indexed
  (`c[α]`) at a `send`/`receive` site. What generated code holds instead are *endpoints*:
  `channels.Sender[τ]` (`Send(τ)`, may block, no error result — a specification has no
  vocabulary for medium failure) and `channels.Receiver[τ]` (`Recv() (τ, bool)`, blocks
  while the medium is alive, returns the zero value and `false` once it has vanished, which
  is what lets a receive loop terminate). Interfaces, not concrete types, since the compiler
  emits no `main` and takes no position on the medium — Go channel, Unix socket, TCP
  connection all satisfy them, and the choice belongs to whoever wires the system together.
  Answers "what Go type represents a channel value" (none needed) — doesn't answer "what
  does `send(c, e)` to a different process actually compile to on the wire," still open,
  §9.7.

**Compiling TLA+ expressions, operators, functions** (thesis §7.2.1.2/§7.2.2; §7.4's
correctness sketch is the chapter's only remaining stub):

- **Equality/ordering: one dictionary, passed explicitly.** Go's builtin `==`/`comparable`
  can't be implemented for custom types and falls short for complex TLA+ types anyway
  (order-irrelevant set equality, sets-of-sets needing deep order-irrelevance, lazy maps not
  comparing all entries). The thesis answers with `Eq[T]`/`Ord[T]` *interfaces*; this
  compiler uses a single `Ord[T]` **struct** of two functions (`Eq`, `Lt`), with
  `Neq`/`Gt`/`Le`/`Ge`/`Cmp` derived once as methods on it, handed to every operation that
  compares.
  The interface version cannot express the library's own containers. Go has no conditional
  method sets — no `instance Ord a => Ord (Set a)` — and a method's receiver type parameters
  must repeat the declaration's constraints exactly, so `type Set[T any]` can declare no
  comparison that calls `T`'s, while `type Set[T Ord[T]]` propagates the constraint into
  every use and makes a tuple or record with a function-typed component *non-representable*
  rather than merely non-comparable. Concretely: under interfaces `Set[Set[Int]]` is not
  constructible at all. Dictionaries keep every container `[T any]`, and nesting is
  composition — `SetOrd(SetOrd(IntOrd))` — produced compiler-side by `ordDict : Typ → …`,
  the structural recursion mirroring `compileTyp` constructor for constructor. `Gt` becomes
  derivable in the move, being a flip of two arguments rather than a method on one.
  Only `Eq` and `Lt` are primitive, and there is no separate `Eq` hierarchy: no type splits
  the two, since wherever equality is available an order is available at the same price
  (a lazy function must force its domain either way), and the types with neither —
  operators, compiling to Go `func` — are not TLA+ values and so cannot nest inside a set,
  sequence, record or function domain.
  **Methods where they work, dictionaries where they don't.** The problem is generic
  containers specifically, so hand-written types keep declaring their obligation as methods
  and are bridged once: `comm.Address` spells `Eq`/`Lt` and the runtime bridges it
  (`AddressOrd`); a user's constant type does the same and the compiler emits the bridge.
  Only a rigid type variable needs a genuine dictionary *parameter*, threaded into
  polymorphic definitions at their call sites.
  Dictionaries are passed, never stored in the values they order: `Set[T]` stays `[]T`, so
  its sorted-and-duplicate-free invariant remains a property of the value alone.
  `persistent/treemap` was already built this way (`New(cmp func(a, b K) int)`) and is the
  precedent this generalizes.
- **Booleans.** `/\`/`\/` compile to Go's short-circuiting `&&`/`||` (sound: non-action,
  non-temporal TLA+ expressions are pure). `\A x \in S : P`/`\E x \in S : P` compile to a
  search over `S` for the first counterexample/witness (De Morgan equivalence between the
  two).
- **Sets.** `Set(τ)` is `[]τ` under **two** representation invariants: sorted ascending by
  the element dictionary's ordering, and duplicate-free. TLA+ sets have no order, so
  sortedness is a choice of canonical representative, made because it's what makes the
  operations cheap — equality is an elementwise walk instead of a double subset test,
  membership a binary search instead of a scan, `CHOOSE`'s deterministic pick the first
  satisfying element instead of a search for the minimum, and deduplication falls out of the
  same sort. Cost: an ordering is needed wherever equality alone would have done (`SetIn`,
  and hence `FnApply`/`FnOverload`), which costs nothing extra since `Ord` carries both.
  Which dictionary a given `Set` was built with is not recorded in it — every operation on
  that set must be handed the same one, guaranteed compiler-side by deriving both from the
  same `Typ`. Every constructor establishes both invariants; every consumer may rely on them.
  `{x \in S : P}`/`{e : x \in S}` compile via `SetFilter`/`SetMap`, copying the underlying
  slice rather than mutating `S` in place (TLA+ data is immutable) — `SetFilter` copies
  unconditionally, inside the helper, since `slices.DeleteFunc` compacts in place and would
  otherwise corrupt a set sharing a backing array; filtering preserves both invariants, so
  it needs no renormalization. `SetMap` preserves neither (a mapping function need be
  neither monotone nor injective — `{x % 2 : x ∈ {1,2,3}}` is two elements from three), so
  it takes the *result* type's dictionary and renormalizes. Set literals `{e₁, …, eₙ}`
  compile to `MkSet(ord, e₁, …, eₙ)`, not a bare composite literal: whether two components
  denote the same value generally isn't decidable until they're evaluated, so the literal
  may be unordered and may repeat an element.
  **Representation is swappable.** Nothing outside `runtime/tlaplus/sets.go` and 2b's
  literal emission depends on `Set` being a slice, so moving to a persistent tree-set later
  (for specs that build large sets by repeated insertion, where slices are O(n²)) changes
  no generated code. Not planned: the dominant access patterns here are build-once,
  iterate, compare, which favour a contiguous representation, and the one place
  copy-on-write genuinely mattered is function `EXCEPT`, already served by
  `persistent/treemap`. `CHOOSE x \in S : P` — needing to be *deterministic* (always picks the
  same element for the same `S`/`P`) — returns the minimum satisfying element, not a random
  pick, and since the representation is sorted that is the first one a scan meets: it
  neither builds the filtered set nor searches it for a minimum, and so needs no dictionary
  of its own at the call site. Panics on an empty result set. Over an uninterpreted constant
  type the *result* is implementation-dependent, resting on the arbitrary order the
  integrator supplied — legal, but recorded on `Address` above.
- **Functions.** Still lazy maps, but since Go's builtin `map[T]U` requires `T`
  `comparable` (which the dictionary-ordered types don't satisfy), underlying storage is an
  ordered-map structure keyed by the domain dictionary's `Cmp`. **Home-grown,
  persistent (immutable, structurally-shared) `TreeMap[K, V]` in `persistent/treemap/`**
  (weight-balanced tree, `Compare func(a, b K) int`-parameterized, O(1) `Clone`/O(log n)
  `Insert`/`Delete`/`Get`, no `comparable` constraint) — not an external dependency. Real
  payoff: `EXCEPT` (function overloading) always clones the underlying map before writing,
  so `[f EXCEPT ![3] = 7][3] = 7 /\ f[3] # 7` holds — with a genuinely persistent tree,
  that clone is O(1) via structural sharing rather than an O(n) full copy a mutable
  external map would force. `LazyFunction` holds that map **by pointer**, which matters
  because `LazyFunction` is passed by value and the cache does two jobs a persistent map
  splits apart: application memoizes by overwriting the map *header* through the shared
  pointer (persistence lives in the nodes, so replacing a header is cheap and disturbs no
  map derived from it), making the computed value visible to every copy of that
  `LazyFunction`; `EXCEPT` instead keeps the fresh header `Insert` returns, so an override
  stays scoped to the overloaded copy and never leaks back. Holding the map *by value*
  silently loses memoization — the write dies with the callee's copy — and makes recursive
  functions exponential.
  A function's *own* dictionary (`FnOrd`, for a function nested inside a set or a domain)
  is a panicking placeholder. The real scheme is known — TLC forces the graph and compares
  domain then range pointwise — and forcing a whole domain is the price; it is left for the
  first specification that needs it, so that nothing pays for a path nothing exercises.
- **Operator/function definitions.** Parameter-less operators compile to a plain
  (mutable, in Go's own type system — "immutable" is a documentation convention here, not
  compiler-enforced) `var`, initialized once. Parametric operators — recursive or not, Go
  supports mutually-recursive top-level functions natively — compile straightforwardly to
  Go functions; names capitalized in generated code (Go's public/private convention)
  regardless of original casing, except `LOCAL` definitions. **Recursive *functions***
  (as opposed to recursive operators) need a bootstrapping trick, since the generator
  closure has to call back into the very `LazyFunction` it's building: `MkRecFn` allocates
  the `LazyFunction` first with a `nil` generator, then overwrites `.gen` with a closure
  capturing the function itself by reference (Go closures capture variables, not values)
  — "ties the knot."

**Compiling atomic blocks**, per thesis §7.2.3.1. Let `l : either B1 or ... or Bn` be an
atomic block. Compiles to one
scheduler function named `l` plus one function per branch `B_i`, named `l_i`:

- **Scheduler function `l`** — parameters are the locks `ℓ1..ℓk` (typed
  `Lock[struct{...}]` per the shared-variable grouping Definition 7.1.3 assigns each
  lock, `Lock[τ] := chan τ`), `net Network`, `self Address`, `done chan struct{}`. Body
  loops (`for shouldContinue`), each iteration picking a uniformly random branch index
  via `Rand()` and calling that branch's `l_i`, continuing the loop iff `l_i` returned
  `false` (branch's guard failed, nothing fired) — an unfair scheduler (a random branch
  can starve arbitrarily long), matching §7.1's isFair-is-ignored stance already in this
  plan.
- **Branch function `l_i`** — same parameter list as the scheduler, returns `bool`
  (`guard`'s final value). Body: `LOCK` the branch's locks (per `L[shared(B_i)]`,
  Definition 7.1.3) — `LOCK`/`UNLOCK` are the *formal* notation for one `st_i, _ = <-ℓ_i`
  (acquire) / `ℓ_i <- st_i` (release) pair per lock, in the total order fixed by lock
  inference; project each acquired struct's fields into local variables right after
  `LOCK`, reassemble the struct verbatim right before `UNLOCK` — then run the branch's
  compiled guards/statements, then `UNLOCK`, then `return guard`. **Generated code itself
  should not emit these as raw channel ops** — thesis §7.3's worked example (below) instead
  calls runtime-library helpers `Acquire(ℓ)`/`Release(ℓ, structVal)` at every lock/unlock
  site, precisely to avoid leaking `Lock[τ]`'s `chan τ` representation into generated code
  (Listing 7.2.11, "Constructing locks without leaking their API"). `Acquire`/`Release`
  live in `runtime/locks/` alongside `MkLock`, wrapping the raw channel receive/send pair
  the formal `LOCK`/`UNLOCK` notation describes. Signatures: `MkLock[T any](init T)
  Lock[T]`, `Acquire[T any](l Lock[T]) T`, `Release[T any](l Lock[T], v T)`, over
  `type Lock[T any] chan T` created at capacity 1 and seeded with `init`. `Release` takes
  the lock *and* the value: it has to name the channel to send back on, and `Acquire`
  returns the guarded struct itself (the worked example projects `st1.tmp2` straight out of
  it), not a handle that could carry the lock along. The lock holds the guarded value rather
  than sitting beside it, which is what makes "read a variable without holding its lock"
  unrepresentable instead of merely discouraged. Locks are not reentrant — acquiring one
  twice from a goroutine blocks forever — so lock merging is what keeps a block naming each
  of its locks once, and the total order is what keeps two blocks from deadlocking on the
  same pair. Neither is enforced by the runtime; both are lock inference's obligation.
  Release needs **no `defer`**, even though generated code panics by design on undefined
  TLA⁺ expressions (`FnApply` outside a domain, `CHOOSE` over an empty set, an out-of-range
  sequence index): an unrecovered panic in any goroutine terminates the whole Go program,
  and locks are process-local, so no acquirer survives to block on the stranded value. The
  process crashes with a stack trace rather than hanging. Peers then block waiting on a dead
  process, which is the accepted absence of fault tolerance (§9.6), not a locking defect.
- **Guards** compile to `guard = guard && <compiled expression>` (`await e`) or a `var`
  declaration + assignment (`with x = τ do e`) — **`with x ∈ τ do e` (set-valued `with`)
  is explicitly unsupported**: the thesis rejects it outright (no principled way to pick
  a witness satisfying all subsequent guards without turning compilation into a
  constraint solver), not merely deferred.
- **Statements**: `skip` is a no-op; `print e`/`assert e`/assignment compile structurally
  (`assert` panics on failure); `send(c[e1], e2)` compiles to `net.c[e1].Send(e2)`
  (indexed channel) or `net.c.Send(e2)` (non-indexed) — multicast is explicitly *not*
  covered here, thesis treats it as "a simple iterated send" in prose only, no compiled
  form given (§9.5 stays open); `goto l'` compiles to `done <- struct{}{}` when `l'` is
  the special label `Done`, otherwise to `go { l'(ℓ1, ..., ℓk, net, self, done) }` —
  spawning a fresh goroutine per transition specifically to avoid stack overflow (Go
  goroutines start with a small growable stack, a plain tail call wouldn't be safe here).

**Compiling threads and whole processes**, per thesis §7.2.3.2. Let `T_k` be a thread of a
process, `l_1` the label of its syntactically-first atomic block:

- **Thread function `thread_k`** — same parameter list as the branch functions above
  (locks, `net`, `self`, `done`), body is a single call `_ = l_1(ℓ1, ..., ℓk, net, self,
  done)`. The rest of the thread's chaining already happens through `goto`'s
  goroutine-spawning compilation (above) — `thread_k` only needs to kick off the first
  block, everything after is `l_i`-to-`l_j` goroutine handoffs.
- **Receive-relay thread function `thread_rx`** — compiles a `T_rx(mailbox → inbox)`
  thread (§5.5's reception thread, no Network PlusCal-level equivalent code, only
  well-defined semantics). Takes the same lock parameters as any other thread plus
  `mailbox Receiver[τ]` (`Receiver[T]` — `Recv() (T, bool)`, thesis Listing 7.2.10) and
  loops: blocking-receive from `mailbox`, and only if the receive succeeded (`ok`),
  acquire `inbox`'s lock, `Append` the received value, release. Locking only around the
  append (not around the whole blocking `Recv` call) means a `thread_rx` permanently
  blocked waiting for a message never holds `inbox`'s lock — the rest of the process stays
  fully live even if no message ever arrives.
- **Process function `p`** — named after the process's own source-level name, signature
  `func p(net Network, mailbox Receiver[τ], self Address) (chan struct{})`. `mailbox` is
  a **caller-supplied parameter**, not something the generated code constructs or listens
  on itself — matches this plan's existing "compiler does not emit `main`" scope boundary
  below: whoever wires the final binary together is responsible for producing a
  `Receiver[τ]` that's actually backed by a real socket/queue. Body: `INIT_LOCKS`
  (constructs every inferred lock via `MkLock` — thesis Listing 7.2.11 ("Constructing
  locks without leaking their API"), `Lock[T] := chan T` of buffer size 1, pre-loaded with
  the variable's initial value — confirming `Lock[τ] := chan τ` really is just "a channel
  used as a mutex," not a separate runtime type; that same listing is also where
  `Acquire`/`Release` belong, per the branch-function bullet above); a buffered `done'`
  channel (capacity = thread count `n`) and an unbuffered
  `done`; one goroutine per user thread (`thread_1`..`thread_n`, all signal `done'` on
  completion) plus one for `thread_rx` (runs forever, never itself signals `done'`); a
  final aggregator goroutine that reads `done'` exactly `n` times then signals `done`;
  `p` itself returns the `done` channel immediately (non-blocking) so the caller can await
  process completion on its own schedule. Worked example of `INIT_LOCKS` (thesis Example
  7.2.7): three variables split across two locks emit two `var`/`MkLock` pairs, one per
  merged lock, each `MkLock` call's initial struct literal built from each variable's own
  declared initial value.

Thread-code block chaining, `Thread.rx` receive-loop compilation, and `Process`/`Algorithm`
top-level wiring are all direct ports of the schemes above, not fresh design.

**Worked example, thesis §7.3.** The Ping-Pong `Pong` process end to end (`Ping` left as a
mirror-image exercise) — the reference to check `Network2Go`'s output against, same role as
§8.6's worked example for the Join Calculus backend. Pins down: lock inference merges
`tmp2`/`inbox_Pong` under one lock (`inbox_Pong ≻ tmp2`, `self` never locked, being
read-only); `net.Ping.Send(...)`/`net.Pong.Send(...)` call sites; the branch/thread/process
function shapes above, verbatim. Also pins down the concrete shape of the `Network`
struct type `Network2Go` must generate: one field per channel, named after the channel;
a non-indexed channel (`ping`) gets a plain `Sender[τ]` field (Listing 7.2.9); an
address-indexed channel (`pong[Pongs]`) gets a `map[Address]Sender[τ]` field instead — the
per-address fan-out `net.c[e1].Send(e2)` (§9.7) resolves against.

**Runtime library.** `Core/Go`'s pretty-printer assumes a companion Go package (prior
art: `github.com/mesabloo/distpcal-compiler/lib`, needs furnishing under this project's
own import path) providing: TLA+ value encodings (`Seq`, `Set`, functions, records),
`Address`, address resolution/discovery for cross-process `send` (generalize the
hand-written `nameserver` package under `distpcal-compiler/tests/*/`, if it turns out to
still fit once `send`'s wire mechanism is pinned down, §9.7). Part of this project's
deliverables — **lives in `runtime/` in this repo**, versioned with the compiler: value
types in `runtime/tlaplus/`, one file per TLA+ concept/stdlib module (`sequences.go`,
`sets.go`, `functions.go`, `ord.go`, …, mirroring `Driver/Builtins.lean`'s `builtinModules`
split rather than one flat file); `Sender`/`Receiver`/`Address`/`Multicast` in
`runtime/comm/`; `Lock`/`MkLock`/`Acquire`/`Release` in `runtime/locks/`. The `Ord` dictionary, the primitive newtypes' dictionaries and the composing
constructors (`SetOrd`/`SeqOrd`) belong here too. There is **no** `records.go` and no
`tuples.go`: records and tuples are anonymous structs with dictionary literals emitted
beside them, so there is neither a library type nor a generated one to hold. The top-level
`persistent/treemap/` (matching `Extra/`/`VerifiedCompiler/`/`ProgressBar/`'s existing
vendored-directory convention) is the ordered-map backing store for lazy functions.

**The compiler does not emit a `main` function, or a runnable program on its own.**
`Network2Go` produces Go source — types and functions — not a deployable binary; the
`runtime/tlaplus/` library supplies the pieces those generated functions depend on (value
encodings, `Address`, the nameserver client), but wiring everything into something that
actually runs — writing `main`, deciding how (or whether) each Network PlusCal process
maps to a separate OS process, bootstrapping how a process finds the nameserver — is
explicitly left to whoever uses the generated code. Deliberate scope boundary.

**Same scope boundary applies to `CONSTANT`s and process sets (§2).** A process set
`p ∈ S` compiles to a **single** Go function/type (parameterized over the process's own
identity/address), not `|S|`-many spawned goroutines. The caller's boilerplate is
responsible for supplying `CONSTANT` values and invoking each process's entry point once
per concrete process/address wanted.

---

## 6. Verification strategy

### 6.1 Framework
`VerifiedCompiler/Trace.lean` defines `Trace`, an ordered-monoid-typeclass abstraction
over event traces (`τ` with `Monoid`, `PartialOrder`, two compatibility axioms between
`≤` and `*`), used to make refinement composable regardless of a given pass's trace
alphabet. `VerifiedCompiler/Denotational/StrongRefinement.lean` defines simulation
relations `Terminating`/`Diverging` between source and target language *denotational*
semantics — each language's meaning given directly as a `Set (state × trace × state)`
relation (a program denotes the set of input/trace/output triples it can produce, how
non-determinism is represented here, per `Core/*/Semantics/Denotational.lean`), not as an
operational small-step system — with a useful algebra on top: composability across passes
(`Terminating.Comp`), monotonicity, identity, arbitrary sups, a `lfp` induction principle
for semantics defined as fixpoints (needed for loops/recursion). Worth vendoring
essentially as-is — generic over source/target languages and traces, no dependency on the
domain-specific AST code being rewritten.

### 6.2 What gets a proof in this plan
Per §2: only **Guarded PlusCal → Network PlusCal**, matching prior art's existing proof.
Concretely: `Core/GuardedPlusCal/Semantics/Denotational.lean`,
`Core/NetworkPlusCal/Semantics/Denotational.lean`, and a `Guarded2Network/Lemmas.lean`
establishing a `StrongRefinement.Terminating`/`.Diverging` instance between them, ported
and re-derived against the fresh ASTs.

### 6.3 What's explicitly deferred
Everything else — parser correctness, desugarer semantics-preservation, type-checker
soundness, Distributed→Guarded (`Computable2Guarded`) *behavioral* correctness (full
denotational refinement proof against `TypedPlusCal`'s semantics, same
`StrongRefinement` sense §6.2 commits to for Guarded→Network), both new backends.
"Deferred" means **not committed for this initial roadmap, not abandoned** — proving
`Computable2Guarded` correct in the full sense is a real, intended eventual target, not
scheduled now. Real limitation in the meantime: a bug in `𝒞_reord` (§5.4, fully specified in
the thesis but unproven here) could silently produce a miscompiled program with no proof to
catch it.
Treat *type-level* invariants baked into the ASTs (e.g. `CorePlusCal`'s terminal-statement
indexing, §3.2/§5.2) as the first line of defense where full semantic proofs aren't
attempted yet.

The well-scopedness preservation lemma (§2, §5.2a/§5.5) is a narrow, *syntactic*
structural fact, categorically lighter than the full behavioral correctness this section
defers — first slice of `Computable2Guarded`'s eventual correctness work landing early, because
Guarded→Network's committed proof needs it as a precondition now.

### 6.4 Go's denotational semantics — deliberately not started here
The `go-semantics` branch's domain-theoretic account of Go (ch. 6: solving a domain
equation `P ≅ F(P)` over a complete ultrametric space to get a denotational semantics
handling unbounded recursion/goroutines properly, via ~20 files from-scratch topology:
`IMetricSpace`, Lipschitz maps, uniform continuity, closed embeddings, Banach fixpoints)
is real, substantial, unfinished work, not part of this plan's near-term scope: per §2,
verification scoped to Guarded→Network only, and `Network2Go` (§5.7) is expected to reach
correctness, once anyone attempts to prove it, by relating its lock-protected execution
model back to `NetworkPlusCal`'s own semantics directly, not through a standalone Go
domain model. Revisit once `Network2Go` (lock inference included) exists and there's
appetite to prove it correct.

### 6.5 Verification method during development

Prefer `lean-lsp` MCP tools (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`,
etc.) over raw `lake build` for the file-by-file iterative loop while writing/fixing a
module — faster feedback. Not a perfect substitute for a real build, though: use the LSP
for the tight edit loop, but run a real `lake build` on the touched modules at least once
before calling a file done — a closing check, not skippable on a clean LSP report alone.

Per-phase checkpoints: after scaffolding, vendored modules build clean (LSP + confirming
`lake build` per module). After the parser lands, it lexes/parses a real `.tla` file
(thesis's Ping-Pong listing, §8.6, or `distpcal-compiler/tests/PingPong/PingPong.tla`)
end-to-end through the CLI. After each subsequent pass, its modules stay clean and a small
hand-written `#eval`/`#guard_msgs` smoke check exercises it against the Ping-Pong or
Two-Phase-Commit examples (distinct from the deprioritized formal regression suite, §2).
After Guarded→Network, the refinement proof compiles with no `sorry`. Once both backends
exist, a hand-traced compilation of Ping-Pong through each produces output matching the
thesis's worked example (§8.6) for Join Calculus, and a visually-sane, idiomatic Go file
for Go.

---

## 7. Suggested phasing

Not a schedule — a dependency-respecting order. Each phase should produce something
buildable (`lake build`), even if incomplete/unverified. Wait for explicit approval after
every phase before starting the next one, regardless of whether that phase has an open §9
item riding on it — each is large enough (spans real time, touches a prior-art port or
lands new design) to warrant its own check-in.

**Current status: phases 1–9 done. Phase 10 (`Guarded2Network`) is next.**

1. **Scaffolding — done.** `lakefile.lean` (package `Fugue`, targets per §4, current
   stable Lean toolchain per §2), vendored `Extra`/`VerifiedCompiler`/`ProgressBar`/
   `Common`, `CLAUDE.md`, `reference/thesis.pdf` copied in. All vendored modules build
   clean.
2. **Frontend ASTs + pretty-printers — done.** `Core/SurfaceTLAPlus`, `Core/SurfacePlusCal`
   syntax + `Std.ToFormat` instances, staying close to the local `distpcal-compiler`
   checkout's shape (§5.1's parser targets these exact ASTs) — lets later phases be
   tested by hand-constructing ASTs before parsing exists.
3. **CLI wiring — done** (`Fugue.lean`). Executable skeleton: `leanprover/Cli`-based
   parsing of the settled flag surface (§2), `FlagsEnv` built from `Cli.Parsed` once
   at startup and handed to `Driver/Pipeline.lean`'s `runPipeline`, every pass querying it
   via `MonadReaderOf FlagsEnv m`'s typed accessors per §2's unified effect stack. The CLI
   itself is flag parsing, spinner hooks, printing, and the exit code — the compile is
   `runPipeline`'s. Progress-spinner UX per
   prior art's `pcvc`/`fugue.sh`. "Both backends reachable, target selectable" only
   becomes fully true once phase 11 exists; the CLI shell itself, and the ability to dump
   intermediate ASTs as each pass lands, is wired incrementally from here on. Two flag
   details stay open, §9.3.
4. **Lexer + parser — done** (§5.1). Ported from the local `distpcal-compiler` checkout's
   `Parser_/` largely verbatim, wired into the Phase 3 CLI: reads input, lexes, optionally
   dumps tokens/CST, parses, resolves annotations, reports collected `fair`-process
   warnings subject to `-W`. Known parser gaps that don't block §8's language subset are
   tracked in §9.2.
5. **Desugarer — done** (§5.2). Both `CoreTLAPlus.Syntax.lean`/`CorePlusCal.Syntax.lean`
   written fresh; expression desugaring (`Desugarer/TLAPlus.lean`) and statement
   desugaring (`Desugarer/PlusCal.lean`, basic-block extraction into `CorePlusCal`'s
   `Bool`-indexed terminal encoding) both implemented and wired into the CLI.
6. **Type checker — done** (§5.3): bidirectional rules from thesis §3.1 implemented
   essentially verbatim, with the direction-aware metavariable-solving deviation (§2).
   `Ξ` as a `MonadModuleCache m`-backed in-memory cache (§2), eager/transitive module
   resolution over `EXTENDS` only, cycle detection. Sequenced ahead of well-formedness
   checking (phase 7) since type checking already forces variable well-scopedness as a
   side effect of succeeding — see §2, §5.2a.
7. **Well-formedness checking — done** (§5.2a): well-labelledness, variable
   well-scopedness, the no-bare-temporal/action-operator check, over
   `CoreTLAPlus`/`CorePlusCal` — purely syntactic, no dependency on the type checker
   (phase 6) either way, runs after it. Of the well-scopedness sub-check, only the
   freshness/no-duplicate-names half is genuinely load-bearing here (reference
   resolution already guaranteed by phase 6 — see §5.2a's breakdown). The two
   `WellScopedness.lean` files ported here too, primary use as proof-support at phases 9
   and 10. `CorePlusCal.WellScoped` authored fresh — it doesn't exist in prior art at any
   stage.
8. **`TypedTLAPlus`/`TypedPlusCal` → `ComputableTLAPlus`/`ComputablePlusCal` — done**
   (`Typed2Computable`, §5.3): separate pass from the type checker itself — collects every
   constant/variable/operator/function transitively reachable from the algorithm and
   translates each, plus the algorithm itself. Depends on phase 7, not just phase 6: its
   temporal/action-freedom and bounded-quantifier guarantees are already established
   transitively by phase 7's own check 3, so this pass treats both as already-guaranteed
   invariants, rejects only what `WellFormedness` doesn't already cover
   (`fnSet`/`recordSet`, no finite runtime representation).
9. **`Computable2Guarded` — done** (§5.4): the `Ref` field-access prerequisite (`.field` segments
   interleaved with bracket-index groups, `Core/TypedPlusCal/Syntax.lean`'s `Ref.args : List
   (String ⊕ ε)`) and the same-atomic-step assignment-conflict tightening, both ahead of the
   four subpasses proper (`𝒞_cflow`/`𝒞_par` unchanged-type `ComputablePlusCal.Algorithm`
   rewrites; `𝒞_flat`/`𝒞_reord` merged into one `Computable2Guarded/FlatReord.lean` walk straight to
   `GuardedPlusCal.AtomicBranch`, no intermediate staging type). Hand-verified per-subpass
   against the thesis's own worked examples, culminating in the Two-Phase Commit `c2` block
   (`tests/examples/TwoPhaseCommit.tla`) against Listing 3.2.4. Wired into the CLI as
   `-d dump-guarded`.
10. **`Guarded2Network` — next up** (§5.5): port pass + proof from prior art. Prove the
    well-scopedness preservation lemma from phase 7 as this proof's precondition.
11. **Backends, in either order (independent siblings, §2):**
    - **`Network2JoinCalculus`** (§5.6): new implementation, validate against the
      Ping-Pong worked example by hand first. Must resolve during this phase: §9.5
      (multicast compilation scheme).
    - **`Network2Go`** (§5.7): port the pass (already real, goroutine-based codegen), plus
      the lock inference algorithm described there, plus a runtime library skeleton
      (value encodings + address/nameserver primitives, generalizing
      `distpcal-compiler/tests/*/{lib,nameserver}`). Must resolve during this phase:
      §9.6/§9.7 (numeric representation, `send`'s wire mechanism), §9.5 (multicast
      codegen). Once both backends exist, the CLI's target selection (phase 3) is
      complete.
12. **Stretch, out of this plan's committed scope, natural next milestones:** Join
    Calculus execution strategy (§9.1); broadening verified coverage beyond §6.2;
    revisiting Go's denotational semantics (§6.4); a real example/regression suite; a
    static "minimal needed addresses" analysis pass to avoid assuming full
    process-to-process connectivity (§2), if the nameserver-based addressing design ever
    gets revisited enough to make it worthwhile again.

---

## 8. Language subset for v1

Derived from the type-checking rules actually specified (thesis Fig. 3.1.13, 3.1.15,
3.1.16) — this is what "Distributed PlusCal" concretely means for this project:

Statements: `goto`, `skip`, `await e`, `receive(c, r)`, `r ≔ e` (assign), `with x = e do
B` / `with x ∈ e do B`, `send(c, e)`, `assert e`, `print e`, `either B1 or ... or Bn`,
`while e do B`, `if e then B1 else B2`, `multicast(x, [y ∈ e1 ↦ e2])`. Processes: uniform
process sets `p ∈ S ⋆ x1=e1,...,xm=em ⋆ T1...Tn` (single-process `process(x=e)` is sugar
for `process(x ∈ {e})`, per thesis §3.1.5 — implement it as sugar, desugaring it away
early, rather than duplicating rules/cases downstream). Algorithms: `fifos c1:τ1,...; P1
∥ ... ∥ Pn`.

`INSTANCE` and `RECURSIVE` are out of scope (§2). `LAMBDA` is out of scope (§9.10). Most
temporal/action operators aren't parsed (§9.11).

---

## 9. Open questions

In `OPEN_QUESTIONS.md`, same `9.x` numbering.
