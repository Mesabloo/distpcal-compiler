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
| Example/regression suite | **Deprioritized.** The prototype's `tests/PingPong`, `tests/TPC`, `tests/LamportMutex` examples exist and are useful reading, but building a test harness is not a near-term milestone. The Ping-Pong example from the thesis is used informally throughout this plan as a running illustration only. |
| Build config format / toolchain version | **`lakefile.lean` (Lean DSL), not `lakefile.toml`** — same kind of config prior art uses. **Bump the Lean toolchain** rather than pinning to prior art's stale `v4.29.0-rc1`: start on the current stable release when implementation begins, updating `mathlib`/`batteries`/other pinned deps to match. **Expect real breakage from this, not just cosmetic fixes**, and not only in the three ported exceptions (§2) — `Extra/`'s vendored data-structure lemmas are exposed to the same API drift and should be expected to need real repair work too. This cuts both ways: some currently-broken `Extra/` theorems may become provable again once a partial API change elsewhere is fixed by the bump (e.g. string-related lemmas broken by a partial API change), not purely a one-directional cost. |
| CLI flag surface | **Settled**, GCC/Clang-style flag naming on top of `leanprover/Cli` (still the underlying framework, as in prior art — `--help`/`--version` come free from it): `-d<name>[=<value>]` (debugging options generally — AST dumps, but also e.g. `-dtiming` for per-pass timing, not just dumps), `-f<name>[=<value>]` (feature/config toggles, e.g. `-fno-progress`), `-W<name>`/`-Wno-<name>` (per-warning control), `-o`/`--output`, `-t`/`--target go|join`, `-I <path>` (add a module search path, see §5.3). Two details still open — Join Calculus "flavors" and where the Go `-p` package name lives — see §9.3. **Concrete invocation syntax, pinned down during Phase 2 (CLI wiring):** `leanprover/Cli` rejects the same named flag being given more than once (`duplicateFlag`) and parses `Array α`-typed flags as a single comma-separated occurrence, not true repetition — so each of `-d`/`-f`/`-W`/`-I` is one Cli flag of an `Array`-typed `ParseableType` (`-d name1,name2=value`, `-I dir1,dir2`, `-W name,no-other`), not literally repeatable GCC-style (`-dfoo -dbar`). This is a mechanical consequence of the library, not a design choice, and doesn't change the settled semantics above. |
| Go runtime library location | **Settled: `runtime/go/` in this repo**, versioned alongside the compiler that targets it, not a separate repo (unlike prior art's implicit `github.com/mesabloo/distpcal-compiler/lib`). See §5.7. |
| Address visibility / deployment topology | **Accepted limitation, not fixed by this plan.** Distributed PlusCal lets any process know any other process's identity, so generated code can't principally avoid assuming worst-case full connectivity ("star" topology) between processes. A "minimal needed addresses" static analysis was considered but is **not planned work** — it's largely mooted by the nameserver-based addressing already settled for both backends (§5.6, §5.7). See §7's stretch list. |
| Fairness (`isFair`, `fair process`/`fair+`) | **Largely ignored by the compiler** — there's no way to insert fairness into the target languages' runtimes (neither the generated Go's goroutine scheduler nor the Join Calculus's reaction-firing nondeterminism are made fairness-aware by this plan). `isFair` is still carried through the ASTs (parsing → both backends) for round-tripping/documentation purposes, but neither backend's compilation scheme (§5.6, §5.7) does anything with it. The parser emits a **warning** (§5.1) whenever a `fair process` / `fair+` annotation is encountered, telling the user it will be ignored. |
| `CONSTANT` values, and process-set (`p ∈ S`) cardinality | **Left to the user of the compiled code, deliberately.** `CONSTANT`s are genuinely abstract entities (both their type and their value) as far as this compiler is concerned — they only get concretized when someone builds a real executable program out of the generated code, matching the existing "the compiler doesn't emit `main`" scope boundary (§5.7). No `ASSUME`-pinning requirement, no companion config file. Correspondingly, a process set `p ∈ S` does **not** compile to `S`-many spawned goroutines/definitions — each process definition compiles to a **single entry point** (a Go function, a Join Calculus process definition), parameterized over the process's own identity/address; the user is responsible for invoking that entry point once per concrete process they want running, with whatever address they choose. See §5.3, §5.6, §5.7. |
| When imported modules get processed | **Eagerly and transitively, recursively invoking the compiler driver right after desugaring, before type checking.** Every module reachable from the main module's `EXTENDS`/`INSTANCE` list gets fully processed up front, not lazily on first `Ξ` miss: once the main module itself is parsed and desugared (§5.1–§5.2), the driver recurses on each directly `EXTENDS`ed/`INSTANCE`d module — parse → desugar → recurse on *its* own imports the same way → type-check — before the main module's own type checker (§5.3) starts. By the time the main module reaches `[Goto]`/`[Assign]`/etc. typing rules, `Ξ` is already fully populated for everything it can reference. See §5.3. |
| Well-scopedness: how `GuardedPlusCal.Algorithm.WellScoped` gets established for Guarded→Network | **A general preservation lemma, proved once**, not a per-run decision procedure: `CorePlusCal.WellScoped p → GuardedPlusCal.Algorithm.WellScoped (Typed2Guarded (Checker p))` (roughly), proved as part of `Checker`/`Typed2Guarded`'s verification work (§5.5, §6.2) and reused unchanged for every program the compiler processes. Per the project owner, this fits the compiler's overall verification aesthetic better than re-deciding the `Prop` computationally on each concrete compiled algorithm. **Note:** `CorePlusCal.WellScoped`, the lemma's antecedent, is not one of the ported files — it doesn't exist in prior art at all and must be authored fresh (§5.2a). See §5.2a, §5.5. |
| Polymorphism-instantiation / metavariable resolution mechanics | **Direction-aware solving, not naive eager unification** — since the subtyping axioms here are asymmetric coercions, not an equivalence. Lower-bound constraints (`T <: ?n`) solve eagerly, because coercions only ever run narrow→wide; upper-bound constraints (`?n <: T`) only ever get recorded as pending, never solved from directly, since doing so would foreclose a narrower solution arriving later. Metavariable-vs-metavariable constraints (`?m <: ?n`, both unresolved) must **not** be resolved by merging/unioning the two variables into one — that's unsound in general, since it conflates two independently-constrained unknowns and forces equality where `<:` only ever demanded a directional relationship; instead, record the link on the lower side and propagate once one side resolves from a real ground bound. A metavariable left with no bounds at the end of checking — including one whose only recorded bound is another metavariable that itself never resolved — is a hard type error, not a silent default. Full algorithm, with the counterexamples motivating each rule, in §5.3. |
| Coercion realization: where do coercions live, and how does a *pending* one get resolved? | `Coercion := Expr → Expr` — applied by ordinary function application to the elaborated expression in hand once `subtype` yields a **successful** coercion. When it yields **pending** instead (an upper-bound check against an unresolved `?n`), the expression is wrapped in a new `mvar : MVarId → Expr → Expr` node added to `TypedTLAPlus`/`TypedPlusCal`'s grammar; the checker's context keeps, per unresolved `?n`, its pending upper bounds and the `mvar` sites created alongside them in lockstep (same length, by construction). The moment `?n` resolves, every one of its `mvar` sites is substituted with the now-computable coercion applied to the wrapped expression — this happens as part of the metavariable-resolution algorithm itself, not a separate pass, so `mvar` is fully eliminated before the checker's output reaches `Typed2Guarded`; downstream passes and both backends never see it. See §5.3. |
| Diagnostic/error-model shape | **Per-pass error types, unified by a common rendering interface** — not one shared diagnostic sum type. Warning suppression (`-W`/`-Wno-<name>`, §2) is handled either at the point a warning is emitted or by filtering after the fact, before rendering — either is fine, implementer's call. Per the project owner, this mechanism (per-pass errors, common rendering, some form of warning filtering) is expected to already exist in `Common/Errors.lean` (§4), just not necessarily well-documented — read that file before designing something new rather than assuming a gap that isn't there. It's explicitly fine to later refactor either the error style or the warning/error emission mechanism if either doesn't hold up in practice. **Known bug to watch for when porting:** the project owner has observed a rendering bug somewhere in this diagnostic-printing code where, in some circumstances not yet pinned down, one character in the offending source line gets duplicated in the printed output — worth tracking down and fixing during the port rather than carrying it forward silently. |
| Generated-identifier hygiene | **Resolved by renaming; direction doesn't matter.** Whether a user-chosen name or a compiler-introduced one is the one that gets renamed on collision is irrelevant — the only hard requirement is that **no shadowing is ever introduced in the generated code, checked at every pass, not just the final pretty-printer.** This is the same class of problem as escaping target-language reserved words (a PlusCal variable literally named `type` or `def` colliding with a Go/Join-Calculus keyword), which prior art already partially handles: `Core/Go/Pretty.lean` has a `keywords : Std.HashSet String` table and a `sanitize` function (suffixes a colliding name with `__`) applied at every point an identifier gets printed. **Port and generalize this mechanism** — to cover compiler-introduced internal names (`recv`, `inbox`, lock variables, label atoms, §5.6/§5.7) and the Join Calculus's own reserved surface, not just Go keywords — rather than treating it as a Go-only concern. See §5.2a, §5.6, §5.7. |
| Flags, and `Ξ` (§9.10, now resolved): how do these cross-cutting effects fit the monad-polymorphism convention? | **Unified effect stack, not a driver/pass split.** Every function — pass code and the CLI driver alike — is written against one abstract `{m : Type _ → Type _} [Monad m]`, with every effect (errors, flags, module cache) as a typeclass constraint on that same `m`, rather than confining `IO`-flavored effects to an outer driver layer. Concretely: (1) **Flags are a contextual (Reader) effect, not an opaque action.** A single `getFlag : String → m (Option String)` was tried and rejected — flags aren't uniformly `Option String` (boolean `-f`/`-W` flags vs. valued `-d<name>=<value>` options vs. `-o`/`-t`/`-I`'s own typed values each need their real type, not a stringly-typed lookup every caller re-parses), and separately, this project's proofs run on `Std.Do.WP`, which cannot be instantiated at `IO` at all — an opaque, unconstrained action gives that framework nothing to reason about, whereas Reader is exactly the transparent, structural effect it already handles. So: a concrete, typed `FlagsEnv` structure (covering the full settled flag surface above), populated once by the CLI driver from `Cli.Parsed`, accessed via `MonadReaderOf FlagsEnv m` plus small typed accessor helpers (`getDebugFlag`/`getDebugOption`/`getFeatureFlag`/…) built on `read`, not new typeclasses per flag. `instance : MonadReaderOf FlagsEnv IO` reads from an `IO.Ref` populated once at CLI startup, replacing prior art's ad hoc `DebugOptions.from` + closure-capture pattern. (2) **`Ξ` gets its own effect class**, `MonadModuleCache m` (`lookup`/`store` keyed by source hash), with an `IO` instance backed by the disk-persisted cache (§5.3) — a genuine mutable-store effect, unlike flags, but it only shows up in `Checker`, which isn't part of §6.2's committed proof surface, so it doesn't hit the `Std.Do.WP`-compatibility question flags did; revisit its shape if Checker itself ever becomes a proof target. (3) **Consequence for §6.2's Guarded→Network proof, accepted knowingly:** `Guarded2Network.compile` stays generic (`{m} [Monad m] [MonadReaderOf FlagsEnv m] [MonadExceptOf G2NError m]`, same shape as every other pass) rather than being special-cased monomorphic. The refinement theorem is proved against whichever concrete instantiation `Std.Do.WP` actually supports (e.g. `m := Id`, or a `ReaderT FlagsEnv (Except G2NError)` stack) — that instantiation, not the `IO`-run one, is the real proof target. Running the same polymorphic term at `m := IO` for actual CLI execution is a **separate, deliberately unverified step** — same source term, same typeclass contract, believed equivalent by construction but not formally connected to the proof; this gap is to be documented explicitly in `Guarded2Network`'s own module docs once written. |

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
| 3.2 | Distributed PlusCal → Guarded PlusCal | Fully written except §3.2.2.4 (guard reordering), which is a stub |
| 4 | "Compiler verification, denotationally" | Stub (title only) |
| 5 | Guarded PlusCal → Network PlusCal | Stub in the thesis — but *implemented and proved* in the `fugue` repo's `main` branch. Read the code, not the thesis, for this pass. |
| 6 | Denotational account of Go | Fully written; heavy domain theory. See §6.4. |
| 7 | Network PlusCal → Go, lock inference | Stub |
| 8 | Network PlusCal → the Join Calculus | Fully written, including a worked Ping-Pong example. This is the primary spec for the new backend; §5.6 below is a condensed version. |

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
├── WellFormedness/               fresh — well-labelledness + variable well-scopedness + no-bare-temporal-op checks over Core ASTs (§5.2a)
├── Checker/                      fresh — bidirectional type checker, Core → Typed
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
is using. `Fugue.Core`, `Fugue.Parser`, `Fugue.Desugarer`, `Fugue.WF`, `Fugue.Checker`,
`Fugue.T2G`, `Fugue.G2N`, `Fugue.N2JC`, `Fugue.N2Go` are the corresponding `lean_lib`
targets in `lakefile.lean`, mirroring the `distpcal-compiler` naming scheme.

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
algorithm inside a `(* --algorithm ... *)` comment block, plus `@type`/`@mailbox`/`@rx`
annotations in comments (see the Ping-Pong listing in thesis §8.6 for the annotation
style).
**Output:** `SurfaceTLAPlus.Module` wrapping a `SurfacePlusCal.Algorithm`.

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

Annotations (`@type`, `@mailbox`, `@rx`) are parsed as a distinct pass over comments
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

### 5.2 Desugaring
**Input:** `SurfaceTLAPlus`/`SurfacePlusCal`. **Output:** `CoreTLAPlus`/`CorePlusCal`.

Two independent halves:

- **Expression desugaring** (`SurfaceTLAPlus.Expression.desugar`): produces
  `CoreTLAPlus`, a deliberately simple core language for the checker (§5.3) and
  everything downstream to work against, rather than TLA+'s full surface grammar. The
  concrete transformations (confirmed with the project owner directly — treat this list
  as authoritative, superseding the shorter gloss in `Core/README.md`):
  - `@`, TLA+'s self-reference inside `EXCEPT`, desugars to the expression being
    `EXCEPT`ed. In `[x EXCEPT ![1, 2, 3] = @ + 3]`, `@` becomes `x[1, 2, 3]`.
  - Conjunction/disjunction *lists* (TLA+'s indentation-sensitive `/\`/`\/` lists)
    desugar to the binary infix operators `/\`/`\/`.
  - Prefix, postfix, and infix operator applications desugar to ordinary
    (prefix-style) operator applications: `1 + 2` becomes the application `+(1, 2)`,
    `TRUE^*` becomes `^*(TRUE)`, and likewise for every mixfix operator.
  - Every quantifier binds exactly one variable over at most one domain. Tuple-pattern
    binders desugar via a fresh variable: `\A ⟨x, y⟩ ∈ S : P` becomes
    `\A z ∈ S : P[z[0]\x, z[1]\y]` for some `z` fresh in both `S` and `P`.
    Multi-variable binders desugar to nested single-variable quantifiers:
    `\A x, y : P` becomes `\A x : \A y : P` (and likewise for `\E`, and the other
    binder forms).

  **This is only partially implemented** in `distpcal-compiler`'s
  `Desugarer/TLAPlus.lean` as of this plan being written — don't assume the existing
  code covers all four transformations above; check what's actually there against this
  list rather than treating any part of it as a finished port.
- **Statement desugaring** (Distributed PlusCal → PlusCal with explicit gotos): **no
  existing implementation** — `Desugarer/PlusCal.lean` is an empty stub in every branch
  checked. This needs to be designed and written from the ground up. The target shape is
  `Core/CorePlusCal/Syntax.lean`'s type-indexed `Statement α β (terminal : Bool)`
  encoding (§3.2) — carry that pattern forward, it buys "every block ends in exactly one
  terminal statement" for free as a type invariant instead of a side condition to
  maintain by hand. The actual normalization (turning implicit fallthrough into explicit
  `goto`, per PlusCal's own manual, referenced in thesis §3.2.2.1) is comparatively
  mechanical once the target type is right.

### 5.2a Well-formedness checking (NEW)
**Input/output:** `CoreTLAPlus`/`CorePlusCal` — this is a checking pass, not a
transform: it either accepts the term or rejects it with a diagnostic, and produces no
new AST. Runs immediately after desugaring (§5.2), before type checking (§5.3).

Per the project owner, this concern is "a combination of syntactical and typing
assumptions, but mostly syntactical," should **not be dropped** (only cleaned up), and in
practice should be *discharged* as an early syntactic check right after parsing/
desugaring, rather than carried deep into the pipeline as an unproven assumption. All
three checks below are purely syntactic at this point — no typing is needed, since
declarations, gotos, and operator shapes are all already resolved by the time
`CorePlusCal`/`CoreTLAPlus` exist:

- **Well-labelledness.** Every `goto` targets a label that actually exists in the
  enclosing process/procedure. §5.3's `[Goto]` rule deliberately performs no check of its
  own (correctly — this isn't a typing concern), on the assumption that something
  upstream already guarantees it; this pass is that something.
- **Variable well-scopedness.** Every variable reference resolves to a declared name of
  the right kind (global, channel, process-local, or block-local `with`/`let` binding —
  matching prior art's Σ/Δ/Γ/Ξ scope classes), every `with`/`let` binder is fresh in its
  scope, and there are no duplicate names within a scope. This is exactly what the
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
  here, implies `GuardedPlusCal.Algorithm.WellScoped` after `Checker`/`Typed2Guarded`
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
  (Checker p))` — its antecedent is a `CorePlusCal`-level well-scopedness `Prop`, and no
  such file exists in prior art at any stage (only the two already-elaborated
  `GuardedPlusCal`/`TypedSetTheory` versions exist, per the correction above). This
  pass's actual, executable well-scopedness check (this bullet) is the *runtime*
  half of the story; `CorePlusCal.WellScoped` is the *Prop* half that the preservation
  lemma's statement needs to even type-check — design it new, closely modeled on the two
  ported files' shape (Finset-based scope classes, the same `with`/`let` freshness
  discipline), but adapted to `CorePlusCal`'s own (pre-`Checker`, pre-`Typed2Guarded`)
  structure rather than copied from either.
- **No bare temporal or action operators inside PlusCal-statement expressions.** None of
  `[]`/`<>`/`ENABLED`/`UNCHANGED` (prefix) or `'`/`^+`/`^*`/`^#` (postfix) may appear
  inside any expression embedded directly in a PlusCal statement (`assign`, `await`,
  `print`, `assert`, guard expressions, …) — Distributed PlusCal's own statement-level
  expressions have no business using temporal/action syntax, even though the surrounding
  TLA+ module may, elsewhere. A purely syntactic tree-walk over `CoreTLAPlus.Expression`
  (the six operators are already ordinary prefix/postfix nodes post-desugaring, §5.2).
  This does **not** replace §5.3's later `TypedTLAPlus → TypedSetTheory` pass, which
  performs the equivalent check (and strip) over the module's *typed* expressions more
  broadly, including ones reachable through operators the algorithm calls but that aren't
  themselves PlusCal statements; this early check exists so the common case (a stray `'`
  or `ENABLED` typo'd directly into a statement) gets a fast, precise, pre-typing error
  instead of surfacing three stages later.

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
  §3.1.1). **`RECURSIVE` operator declarations are not otherwise accounted for anywhere
  in this plan** (not in §8's language subset, not parsed by either prior-art checkout) —
  see §9.9 for whether they're in scope and, if so, the annotation requirement they'd
  need.
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
    constructor). The checker's context records, per unresolved metavariable `?n`,
    **two lists kept in lockstep**: the pending upper bounds already tracked (the
    "Upper-bound constraint" rule above), and the `mvar` sites created at each such check
    — one new pending upper bound recorded always means exactly one new `mvar`-wrapped
    expression recorded alongside it, so the two lists never drift apart in length.
  - **Resolving the placeholders**: the moment `?n` resolves to a concrete `S` (whether
    from a lower bound arriving, per the existing rules, or at the final defaulting
    point), walk `?n`'s two lists together — for each `(T, mvar site)` pair, compute the
    real coercion `coerce(S <: T)` (or fail, if `S <: T` doesn't hold) and substitute that
    `mvar` node with the result of applying the coercion to its wrapped expression. This
    substitution is part of the metavariable-resolution algorithm itself, not a separate
    pass: by the time type-checking finishes (defaulting included), every `mvar` node
    introduced during elaboration has been eliminated, so the checker's actual output —
    what `Typed2Guarded` and the backends (§5.6, §5.7) see — is still `mvar`-free. The
    node exists only transiently, inside the checker, while a metavariable it's tagged
    with remains unresolved.
- **Statement judgment** `Γ | Ξ ⊩ S ok` (no output type — statements are checked for
  effects, not typed). Notable asymmetric rules, worth preserving exactly as justified in
  the thesis (§3.1.5): `[Assign]` synthesizes the LHS type and *checks* the RHS against
  it (not the reverse — enables upcasting the RHS via subtyping); `[Send]`/`[Receive]` are
  deliberately asymmetric the same way (`send` synthesizes the channel type to allow
  upcasting the payload; `receive` checks the channel type against the synthesized
  reference type, exploiting `Channel`'s covariance); `[Print]` requires a `showable`
  type (Fig. 3.1.14: everything except function/operator/channel types, recursively);
  `[Goto]` performs no type check at all — label existence is checked earlier, by the
  well-formedness pass (§5.2a), not the type checker's job.
- **`Ξ` is a global map in the implementation, not threaded state.** On paper it's an
  input to the judgment like `Γ`, but in practice it should be implemented as a global
  cache rather than passed around explicitly through every rule. This will need some
  form of caching — storing each module's encoded (typed) form keyed by a hash of its
  source — so that a module doesn't get fully re-type-checked from scratch every time
  it's referenced (e.g. repeatedly, via `EXTENDS`, across a session).
- **Module resolution and TLA+ standard modules (`EXTENDS Sequences, TLC, ...`) —
  settled architecture and timing (§2).** `-I <path>` (see §9.3) adds a search path
  for locating `.tla` modules referenced via `EXTENDS`/`INSTANCE`. By default,
  resolved/type-checked modules are cached persistently on disk (e.g. under
  `~/.local/config/.fugue`, per the project owner — confirm exact location when
  implementing), keyed so that re-running the compiler doesn't re-resolve or re-typecheck
  modules it's already seen, tying directly into the `Ξ`-caching note above. **Keyed by
  source hash alone, with no compiler-version component in the key** — see §9.11 for why
  that's worth revisiting before relying on it.
  **Resolution is eager and transitive, not lazy.** Once the main module is parsed and
  desugared (§5.1–§5.2), and before its own type checker runs, the compiler driver
  recurses on every module the main module `EXTENDS`/`INSTANCE`s: parse → desugar →
  recurse the same way on *that* module's own imports → type-check, bottoming out once a
  module has no further unresolved imports (or a cache hit short-circuits the recursion
  entirely) — the recursion needs to track modules currently being resolved so that a
  cyclic `EXTENDS`/`INSTANCE` is rejected with a real error instead of looping forever, a
  standard requirement for any recursive resolver rather than a further design choice.
  Only once that whole transitive closure is resolved does the main module's
  own type checker (below) begin, so every `Ξ` lookup it performs is guaranteed to
  already be populated — never a live miss triggering resolution mid-check. `INSTANCE`
  is new scope beyond what the rest of this plan (including §8's language subset)
  previously accounted for — its parameter-substitution semantics (`INSTANCE M WITH
  x <- e, ...`) are not the same problem as plain `EXTENDS` and need their own design
  pass; see §9.8. TLA+'s actual standard modules (`Sequences`, `TLC`,
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
  program from the generated output, not something `Checker` or either backend resolves.

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
   substituting `r` by `e` in `e'`, using `EXCEPT` when `r` has an index). The thesis
   leaves the formal treatment of this step as a stub (§3.2.2.4 "Describe reordering of
   guards" is marked incomplete even in the written-out chapters) — the substitution rule
   itself is given and is enough to implement it, but the surrounding correctness
   argument (does floating awaits past assignments always preserve the enabled-ness
   pattern of the whole `either`?) needs to be worked out during implementation, not
   assumed. `receive` is explicitly *not* handled by `𝒞_reord` (deferred to §5.5 — Network
   PlusCal is where receive-guards disappear entirely).

Worked example available in thesis Listings 3.2.1–3.2.4 (the Two-Phase Commit `c2`
block) — good first target to hand-verify the implementation against once each subpass
exists.

### 5.5 Guarded PlusCal → Network PlusCal (`Guarded2Network`)
**Input:** `GuardedPlusCal`. **Output:** `NetworkPlusCal` (no `receive` guards; each
process gets an opaque `T_rx(mailbox → inbox)` thread that buffers incoming messages into
a process-local `inbox` sequence variable, turning `receive(c, r)` into ordinary
`await Len(inbox) > 0`-guarded reads).

This is the one pass with a complete implementation *and* a completed refinement proof in
prior art (`fugue` `main`: `PlusCalCompiler/Passes/GuardedToNetwork/{PlusCal,Lemmas}.lean`,
against `GuardedPlusCal/Semantics/Denotational.lean` and
`NetworkPlusCal/Semantics/Denotational.lean`). The ported `Core/GuardedPlusCal/Syntax/
WellScopedness.lean` (§5.2a) supplies the well-scopedness hypothesis this proof needs as
a precondition, established via a **general preservation lemma** (§2) proved once over
`Checker`/`Typed2Guarded` — fitting the project's overall verification aesthetic better
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

Thesis ch. 7 is a stub (headers only, no content) and the `lock-inference` branch got no
further than a FIXME comment — but that's the *written-up design*, not the actual code.
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

**Lock inference, concretely (per the project owner):** one lock per atomic block, sized
to block every other *concurrently-reachable* atomic block that touches a variable in
common from executing at the same time. Mechanically: for each pair of atomic blocks
that can run concurrently (i.e. blocks belonging to different threads of the same
process — blocks within a single thread are already mutually exclusive by construction,
since Network PlusCal only ever runs one block of a given thread at a time), compute
whether their variable footprints (the process-local variables each block reads or
writes) intersect; if they do, the two blocks conflict and must be prevented from
executing concurrently, via that one lock. The raw conflict relation isn't itself transitive (A conflicting with B, and B with C,
doesn't by itself mean A conflicts with C) — but each block is only allowed one lock, and
B's single lock must simultaneously exclude both A (which conflicts with B) and C (which
also conflicts with B). Since that's necessarily the *same* lock object, A and C end up
sharing it too, transitively, even though they may not conflict directly. So: group
blocks by *connected component* of the conflict graph, and every block in a component
shares that component's one lock. This keeps the "at most one lock per atomic block"
invariant while still making every conflict, direct or transitive, mutually exclusive.

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
compiler that targets it.

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
(`Checker`/`Typed2Guarded` preserve well-scopedness, §5.2a/§5.5) is a narrow, *syntactic*
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
6. **Well-formedness checking** (§5.2a): well-labelledness, variable well-scopedness, and
   the no-bare-temporal/action-operator check, over `CoreTLAPlus`/`CorePlusCal` — purely
   syntactic, no dependency on the type checker (phase 7). Port the two
   `WellScopedness.lean` files here too (§2), even though their primary use shifts to
   proof-support at phases 8 and 9.
7. **Type checker** (§5.3): implement the bidirectional rules from thesis §3.1
   essentially verbatim.
8. **`TypedTLAPlus` → `TypedSetTheory`** (§5.3): a separate pass from the type checker
   itself — translate every expression used in the PlusCal algorithm (and every operator
   defined earlier in the module that those expressions depend on) by stripping out
   actions and temporal formulas, which doubles as checking none were illegitimately
   present. Depends on phase 7, but is its own small pass, not part of it.
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

### 9.2 Parser implementation — audited, one real check still outstanding
Audited during planning (static read-through of `Parser_.lean` +
`Parser_/{Annotations,Common,Monad,PlusCal,TLAPlus}.lean` +
`Parser_/Tokens/{PlusCal,TLAPlus}.lean`, ~2,200 lines): no `sorry`, no `panic!`. It has
real, complete top-level entry points — `SurfaceTLAPlus.Lexer.lexModule`,
`SurfaceTLAPlus.Parser.parseModule`, `resolveAnnotations` — matching exactly the shape
already wired into `fugue main`'s working CLI, and a commented-out `#eval` at the bottom
of `TLAPlus.lean` reading and parsing `tests/TPC/TPC2.tla`, consistent with the project
owner's own account of having gotten this building and working in earlier attempts.
**No Lean toolchain is available in the environment planning happened in** (no `lake`,
and the sandbox's network allowlist blocks `elan`/toolchain downloads), so this plan
could not itself run `lake build` to give a from-scratch confirmation — treat the above
as strong circumstantial evidence, not a build log. Whoever starts implementation should
run `lake build` (or `./fugue.sh`) against `Fugue.Parser` first, before assuming this
audit substitutes for it.

Known, bounded gaps found by the read-through (worth triaging, not blockers to starting):
- `TODO`s for: an incomplete TLA⁺ reserved-word list (`TLAPlus.lean:62`), no
  binary/octal/hex number literals (`TLAPlus.lean:376`), and no handling of junk before
  the module start / after the module end (`TLAPlus.lean:1135`).
- PlusCal `macro`/`procedure`/`define` sections are explicitly unsupported
  (`PlusCal.lean:387`) — `Core/SurfacePlusCal/Syntax.lean` doesn't even have AST nodes
  for them yet. **Not a blocker**: none of these appear in the v1 language subset (§8),
  which matches the thesis's own typing rules never mentioning them either.
- `TLAPlus.lean:935`'s `-- TODO: parse annotations` comment on `parseQuantifierBound`
  looks stale on inspection — the code right below it already calls
  `tryParseAnnotations` for every binder — but worth a quick confirming look rather than
  trusting that read.

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

### 9.5 Minimal per-pass sanity-checking discipline
§2 deprioritizes a maintained example/regression suite, which is a decision about scope,
not about hygiene — it doesn't say anything about how an implementer should sanity-check
a single pass while building it, distinct from a maintained `tests/` suite. Worth a
lightweight convention (e.g. a few `#eval`/`#guard_msgs` smoke checks per pass, checked
in alongside the pass itself) even without committing to the bigger regression-suite
effort §2 defers.

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

### 9.8 `INSTANCE` support and its parameter-substitution semantics
Resolving §2's module-import-timing decision surfaced that `INSTANCE` (TLA+ module
instantiation, e.g. `I == INSTANCE M WITH x <- e1, y <- e2`) is in scope for module
resolution alongside `EXTENDS` — but this plan doesn't otherwise account for it: not in
§8's language subset, and not in the parser discussion (§5.1), where the actual code
(`Parser_`, the port source) doesn't currently support it. Its typing rules **are**
described in the thesis's type-checking chapter (ch. 3.1) — this plan's §5.3 just doesn't
summarize them yet, unlike the rest of that chapter's rules. Unlike `EXTENDS` (which just
makes another module's declarations visible
as-is), `INSTANCE` substitutes actual parameters for the instantiated module's declared
`CONSTANT`s/`VARIABLE`s (the `WITH x <- e1, ...` clause) — resolving and type-checking an
instantiated module isn't just "parse it and cache it" the way a plain `EXTENDS`ed module
is, since the same module can be instantiated multiple times with different substitutions
within one file. Needs its own design pass: is `INSTANCE` in scope for v1 at all (§8
currently implies no), and if so, does substitution happen during desugaring (producing a
substituted copy of the instantiated module's declarations per instantiation site) or does
`Ξ`/the checker need to track substitution environments directly?

### 9.9 `RECURSIVE` operator declarations — in scope, and if so, how are they checked?

TLA+'s `RECURSIVE f(_, _)` construct (declaring an operator's arity up front so its own
definition, or a mutually-recursive group's definitions, can refer to each other) isn't
accounted for anywhere in this plan: it's not in §8's language subset, neither prior-art
checkout's parser recognizes the keyword (confirmed by grepping both — no hits beyond
the English word "recursive" appearing incidentally in unrelated comments/vendored
Mathlib code), and §5.3 doesn't give it a typing rule.

If it's in scope for v1, the natural design (worked through informally already, outside
this plan, but never written in) is to **require an explicit type annotation on the
`RECURSIVE` declaration itself**, for every operator in the group: extend `Γ` with all
the declared sibling types up front, then check each operator's body against its own
annotation independently. This breaks the circularity a mutually-recursive group would
otherwise create for a bidirectional checker with no other way to know `g`'s type while
checking `f`'s body (and vice versa) — no constraint propagation or guessing across the
recursive calls is needed, since each body just needs to match its own declared type.
This is standard precedent (mutual `def`/`def` blocks in Coq/Agda/Lean always carry
signatures; ML's `let rec ... and ...` is kept monomorphic for the same reason), and
under this plan's rank-1-polymorphism discipline (no let-generalization, §5.3), it's
close to *necessary* for decidability if any operator in the group is itself polymorphic,
not just a convenience.

Open: is `RECURSIVE` in scope for v1 at all (§8 doesn't currently mention it either way)?
If yes: add the surface syntax (parser work, since neither prior-art checkout has it),
add it to §8's language subset, and add the annotation-seeded checking rule above to
§5.3.

### 9.11 `Ξ`'s disk cache has no invalidation story for compiler-side changes

§5.3's persistent, disk-backed `Ξ` cache is keyed by a hash of each module's own source —
which invalidates correctly when the *module* changes, but not when the *compiler*
changes underneath it. Concretely: a bug fix in the checker, an updated standard-module
stub (`Sequences`/`TLC`/`Naturals`/`FiniteSets`, §5.3), or the toolchain bump §2 already
commits to could all change what a given module *should* type-check to, without
touching that module's own source at all — so its cache entry's hash stays the same, and
the stale, pre-change typed form keeps getting served on every subsequent run with no
trigger to recompute it. This is a real correctness gap, not just a staleness
inconvenience: a silently-wrong cached `Ξ` entry means a module downstream can look
type-correct against an encoding the current compiler would no longer actually produce.

Needs a decision: does the cache key grow a compiler/schema-version component (e.g. a
version string or a hash of the checker's own relevant sources, bumped whenever anything
that affects typing output changes), forcing a full cache invalidation on every such
change? Or is there a lighter-weight alternative (e.g. a single global "cache format
version" the whole `~/.local/config/.fugue` directory is stamped with, wiped wholesale on
mismatch, rather than tracked per-entry)? Either is workable, but right now nothing
invalidates the cache on a compiler-side change at all, which is the part that actually
needs fixing before the cache can be trusted.

### 9.12 `send(c, e)`'s actual Go compilation scheme is unknown

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

