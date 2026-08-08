# Lean style

Rules for **every** Lean in this project — theorems, definitions, `have` bodies, one-liners.
Canonical: `INSTRUCTIONS.md` and memory point here, not the other way round.

Vendored `Extra/Mathlib/**` exempt — upstream code, upstream style.

Checker: `scripts/lean-style [FILE…]`. Runs on `Stop`, after proof compile. Style is finishing
concern, never blocks mid-proof iteration.

Citation after rule = real occurrence in this repo. Marked ✗ = violation, still unfixed.

---

## Part A — Rules

### Proof style

- **No deep `exact` nests.** `exact f (g (h x))` hide proof shape, give one useless unification
  error for whole term. Write `apply` chain, one lemma per line, innermost last. `apply` chain
  fail at line actually wrong. Anonymous constructor `exact ⟨a, b, c⟩` fine — literal, not chain.
- **`by classical` on one line.** Not `by`, then `classical` next line.
- **`contradiction`, not `Option.noConfusion`.** `noConfusion` need its implicits line up, fail
  `Application type mismatch` when they don't.
- **`by_cases! h : p`**, not `by_cases h : p` then `push_neg at h`. `!` do `push_neg` itself. Same
  for `by_contra!`. `VerifiedCompiler/Denotational/StrongRefinement.lean:339`,
  `VerifiedCompiler/ClosedForm.lean:192`
- **No `exact absurd x y`.** Use `absurd` tactic (`absurd x`, then supply negation), or `nomatch h`
  when `h` itself impossible equation. ✗ `Guarded2Network/Lemmas/Statement.lean:226`
- **Aesop terminal or not at all** (plan §3 T1). Non-terminal aesop leave whatever search stopped
  at — same instability as non-terminal `simp`, worse, because later steps written against fixed
  goal order. `Core/NetworkPlusCal/Semantics/Lemmas.lean:460`
  **One exception: under `mvcgen`.** `sem_side` registered as its VC-discharge hook, and `mvcgen`
  keep only what it close — so non-terminal is the point there. `Guarded2Network/Lemmas.lean:50`
- **Lemma in `sem` rule set: never apply by hand.** `sem_side` already discharge it. Query
  membership: `scripts/facts s <name>` show `aesop:sem`.

### Language conventions

Set in `lakefile.lean`, not negotiable per-file:

- **`autoImplicit` off.** Every implicit explicit, in `variable` block or signature.
  `lakefile.lean:35`
- **`pp.unicode.fun` on — write `λ x ↦ y`, never `fun x => y`.** `lakefile.lean:36`
  ✗ `Core/ComputableTLAPlus/FreeVars.lean:86`, `Core/TypedTLAPlus/Coercion.lean:121`,
  `WellFormedness/WellScoped/GuardedPlusCal.lean:62`, `:98`, `CustomPrelude.lean:139`
- **`linter.missingDocs` on by default.** Toggleable for fast iteration; not left off when module
  "done". `lakefile.lean:31`
- **Adopt prior-art idioms:** `Located α` with `match_source`/`@@` pair, `Bifunctor`/`Bitraversable`
  on every two-parameter AST, type-level encoding of structural invariants where cheap.
- **Pass naming `<Source>2<Target>`**, matching `lean_lib` shorthand in `lakefile.lean`.
- **Compilation functions monad-polymorphic** — abstract `{m : Type _ → Type _}` plus the
  typeclasses the pass actually needs, never fixed `ReaderT`/`ExceptT` stack.

### Module system

- **Definition another module must *reason about* — not merely call — needs `@[expose]`.** Plain
  `public section` export signature, not body. Symptom: `cases S <;> rfl` fail "not definitionally
  equal", or simp report "Expected a definition with an exposed body". Cost two debugging sessions
  already. `Guarded2Network/PlusCal.lean`, `Extra/Rel.lean:23`
- **`@@` position tag never obstacle to defeq.** `registerSource` is
  `abbrev registerSource (x) (_ : SourceSpan) := x` with side map via `@[implemented_by]`, so
  `x @@ pos` defeq `x`, reduce away free. Don't work around it. `Common/Position.lean`
- **New proof file checked only once something import it.** `lake build` with no target build
  `lean_exe fugue` alone; module outside that closure get stale olean replayed *silently* — build
  report success over source that no longer compile. Wire new proof file into its pass's
  `Lemmas.lean` as you create it. `Guarded2Network/Lemmas.lean`

---

## Part B — Tactic playbook

### Project's own — 15, none are Mathlib's

Full list + docstrings: `scripts/facts t`.

| Situation | Reach for | Defined |
|---|---|---|
| `Statement.reducing` membership goal | `sem_red`, then `sem_side` | `Core/NetworkPlusCal/Semantics/Lemmas.lean:437`, `:460` |
| `StrongRefinement` matching disjunct | `refines_match σ, ε` — two-arg form | `VerifiedCompiler/Denotational/Tactics.lean:41` |
| Source aborted instead | `refines_abort ε` | `:50` |
| Source diverges too | `refines_diverge ε` | `:57` |
| `Rτ ε' ε` goal | `trace_rel` | `:62` |
| `ε' ≼[Rτ] ε` goal | `trace_pfx` | `:66` |
| `erw` then `assumption` | `erwa` | `CustomPrelude.lean:70` |
| `split` needing named hypotheses | `split … using n \| n _` | `:75` |
| `injections` needing names | `injections with a b` | `:81` |
| Build `Iff` from two directions | `iff_intro x y` / `iff_rintro p q` | `:84`, `:86` |
| `trans` with subgoals reversed | `trans'` | `:89` |
| Different tactic per subgoal | `t <;> [t₁ \| t₂]` | `:93` |
| Tactic on a *range* of subgoals, Rocq style | `1-3 : tac`, `all : tac` | `:110` |

### Style already decided — old vs new

The project made these calls; they are not open.

- **`Statement.reducing` goal → `sem_red`/`sem_side`.** Not manual `exact ⟨M, F, v, p, rfl, rfl,
  hv, hp, rfl⟩` naming every field by hand. One line of tactic each, against a several-line term.
  `Guarded2Network/Lemmas.lean:72`
- **Monotonicity in `∘ᵣ₁`/`∘ᵣ₂` → `gcongr`.** Not explicit `Relation.lcomp₁.mono h₁ h₂`, not a
  `rw` chain through `right_union_eq_union`/`left_lcomp₂_eq` to massage both sides. `gcongr` find
  the tagged congruence lemma and reduce to the component inequalities itself.
  `Guarded2Network/Lemmas.lean:84`; tags at `Extra/Rel.lean:34`, `:44`
  ✗ old style still at `VerifiedCompiler/ClosedForm.lean:118`, `:249`
- **Monadic `G2NM` goal → `mvcgen`.** `sem_side` already wired in as its VC-discharge hook, so
  cheap side conditions never surface as named verification conditions.
  `Guarded2Network/Lemmas.lean:60`, hook at `:54`

### Available, unused here, worth reaching for

Zero occurrences in this project. Checked against the pinned toolchain's tactic set.

| Situation | Tactic |
|---|---|
| Find the lemma that closes goal | `exact?` / `apply?` / `rw?` — use while developing, paste the found term |
| Inaccessible hypothesis `h✝` after `rintro`/`cases` | `expose_names` — repo currently hand-fixes with `rename_i` |
| Case-split following a function's own equations | `fun_cases` — non-recursive twin of `fun_induction`, which repo *does* use |
| Rewrite under `≤`/`⊆` rather than `=` | `grw` / `grewrite` — natural fit for `Extra/Rel.lean`'s whole vocabulary |
| Rewrite only the *n*th occurrence | `nth_rw` / `nth_rewrite` — 354 `rw` in repo, zero `nth_rw` |
| Congruence at a chosen subterm | `congrm` / `congr!` |
| Strip matching binders off goal *and* hypothesis | `peel` |
| Several consecutive `· exact` bullets | `exacts [a, b, c]` — 16 such runs in repo |
| Factor a `have` into a standalone lemma | `extract_goal` |
| Generalize before `induction` | `revert` — zero uses, notable for a repo with 105 `induction` |
| Symmetric cases proved once | `wlog` |

Already in use, keep using: `grind` (`Extra/List.lean:720`), `omega`, `gcongr`, `mono`,
`fun_induction`, `plausible`, `positivity`, `solve_by_elim`.

### Not relevant here

Algebra/analysis/number-theory families — `abel`, `ring`, `linarith`/`nlinarith`, `field_simp`,
`polyrith`, `measurability`, `continuity`, `fun_prop`, `bv_decide`, `norm_num`, `qify`/`rify`/`zify`.
This is a compiler development over relations, sets, lists and options. Reaching for them is a
signal the goal was mis-stated, not that the tactic was missing.
