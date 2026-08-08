# Lean style

Rules for **every** Lean in this project — theorems, definitions, `have` bodies, one-liners.
Canonical: `INSTRUCTIONS.md` and memory point here, not the other way round.

Vendored `Extra/Mathlib/**` exempt — upstream code, upstream style.

Checker: `scripts/lean-style [FILE…]`. Runs on `Stop`, after proof compile. Style is finishing
concern, never blocks mid-proof iteration.

Citation after rule = real occurrence in this repo, as an example. Marked ✗ = counterexample.
Citations illustrate the rule; this file is not a list of things to fix.

---

## Part A — Rules

### Proof style

- **No deep `exact` nests.** `exact f (g (h x))` hide proof shape, give one useless unification
  error for whole term. Write `apply` chain, one lemma per line, innermost last. `apply` chain
  fail at line actually wrong. Anonymous constructor `exact ⟨a, b, c⟩` fine — literal, not chain,
  **but only while it fit one line.** Multi-line `⟨…⟩` lose the same readability the nesting rule
  protect it.

  Anonymous constructor stay fine for **short** components, and for **existential
  instantiation** at any length — `⟨w, proof⟩` name the witness, which is the point. Reach for
  `constructor` + one bullet per field only when a **structure** goal get long: nested
  applications inside the `⟨…⟩`, or it spill across lines. Then each field arrive with its
  expected type shown instead of being positioned by hand.
  In term mode the `where` form beat both — fields by name, no positional counting at all.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:759` (`constructor`), `:824` (`where`)
  ✗ `VerifiedCompiler/ClosedForm.lean:183`, `Denotational/StrongRefinement.lean:753`, `:783`
- **No `rw [show … by …]`.** Inline `show`-by-tactic inside a rewrite hide a real proof step in a
  rewrite argument. State it as a `have` and rewrite with that.
  ✗ `VerifiedCompiler/ClosedForm.lean:179`, `Extra/Seq.lean:123`
- **Avoid `(by …)` term arguments.** Same reason: a tactic proof passed as an argument is a step
  with no name and no goal displayed. Prefer a named `have`. Not absolute — `(by omega)` on a
  side condition is tolerable — and too common to mechanize, so not in the checker.
- **Leave no live compiler warning.** Unused binder gets `_`, not a name. Unused section variable
  gets `omit`. `<;>` where `;` suffice gets `;`. Warnings accumulate until nobody reads them, and
  the real one arrives unnoticed. Not in `scripts/lean-style` — needs a build.
  ✗ `VerifiedCompiler/ClosedForm.lean:331` (unused binder), `VerifiedCompiler/Relation.lean:141`
  (`<;>` for `;`), `Guarded2Network/Lemmas/Statement.lean:533` (unused section variable).
  `mvcgen`'s experimental banner is expected, not a warning to chase.
- **Merge `rw [...]` into a following `simp only [...]`.** Rewrite lemmas go straight into the
  `simp only` set — two traversals become one, and the intermediate goal nobody looks at stops
  existing. ✗ `VerifiedCompiler/Denotational/StrongRefinement.lean:335`, `:384`,
  `Guarded2Network/Lemmas/Statement.lean:397`, `Extra/Seq.lean:243`
- **Prefer backward mode over a forward `have` chain.** Build the goal with `refine f ?_ ?_` and
  discharge the pieces in bullets, rather than naming every intermediate with `have` and closing
  with `exact f h₁ h₂`. Each subgoal then arrives with its expected type displayed instead of
  having to be guessed and stated. Same reason `apply` chains beat nested `exact`.
  ✗ `VerifiedCompiler/Denotational/StrongRefinement.lean:387` — `exact abs (Relation.lcomp₁.intro
  hstep_i hrest)` with `hstep_i`/`hrest` hoisted above it, where `refine abs
  (Relation.lcomp₁.intro ?_ ?_)` needs neither.

  **Exception: rewriting.** When the massaging targets a *hypothesis*, forward is the honest
  shape — `have h := lemma …` then `rwa [...] at h`. Aiming the same rewrite at the right
  occurrence in the goal is more cumbersome, not less.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:846`
- **A `have` re-derived in more than one proof is a lemma.** Hoist it, next to the class or
  definition it is about. Repeated `have`s drift apart under refactor and each copy has to be
  re-checked. `mulmono` is `T.Rτ_closed` repackaged and belongs beside the `Trace` class.
  Applies to whole proofs too, not just `have`s: two blocks with identical statements mean a
  diagnostic against one is a diagnostic against both, which is the cost the rule is about.
  ✗ `VerifiedCompiler/Denotational/StrongRefinement.lean:169` (`mulmono`),
  `Guarded2Network/Lemmas/Statement.lean:344` (`hfe`), `StrongRefinement.lean:429` (twin proofs)
- **Name introduced hypotheses in signature order.** `rintro`/`intro` names should run in the order
  the binders appear, so a reader can match them without counting. Out-of-order naming reads as a
  slip even when deliberate. ✗ `VerifiedCompiler/Denotational/StrongRefinement.lean:550` —
  `rintro ref₁ ref₃ ref₂`, where `ref₃` is the second hypothesis
- **Delete `have`/`haveI` the proof does not use.** Lean's linter does not catch an unused
  `haveI`, so a dead instance survives every refactor that made it dead.
  Checking a deletion needs a forced rebuild — delete the `.olean` first, else `lake build` replays
  the cache and reports success over the unchanged source.
  ✗ `VerifiedCompiler/ClosedForm.lean:150` — `haveI : Nonempty α := ⟨σ⟩`, unused by `choose!`
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
- **Signature indentation: binders 2, statement 4.** Continuation line carrying binders/hypotheses
  indent 2; line carrying the statement itself — after the top-level `:` — indent 4. Statement
  stay visually distinct from what it quantify over. Go-forward rule: most existing signatures put
  binders at 4. Not in `scripts/lean-style` — telling a binder line from a wrapped statement
  continuation need real parsing, and a crude version flag hundreds of conforming lines.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:91` ✗ `VerifiedCompiler/ClosedForm.lean:126`

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
- **`Iff` goal whose both sides open with `intro`/`rintro` → `iff_intro` / `iff_rintro`.** Never
  `constructor` there. `iff_intro x y` take two idents, `iff_rintro p q` two rintro patterns, and
  both fold the `intro` into the split. `constructor` is right for an `Iff` only when the branches
  do *not* start by introducing. Applies after `ext` too, where the `Iff` only appears once the
  `ext` has run. ✗ `VerifiedCompiler/Trace.lean:142`, `VerifiedCompiler/ClosedForm.lean:76`
  (post-`ext`), `Extra/Rel.lean:128`
- **Need a stronger induction hypothesis → `induction x generalizing y z`.** Not a hoisted
  `have main : ∀ …` re-quantifying the arguments by hand and proving it by an inner `induction`.
  Hypotheses that would clutter the IH: `clear` them before the `induction`, not restate the goal
  around them. `VerifiedCompiler/Relation.lean:52`, `Extra/List.lean:67`
  ✗ `VerifiedCompiler/ClosedForm.lean:223`, `Denotational/StrongRefinement.lean:173` — a
  `have main : ∀ (n : ℕ) …` whose body opens `intro n; induction n`

### Available, unused here, worth reaching for

Not yet used here, checked against the pinned toolchain's tactic set. Consider them before
hand-rolling the equivalent.

| Situation | Tactic |
|---|---|
| Find the lemma that closes goal | `exact?` / `apply?` / `rw?` — use while developing, paste the found term |
| Is this step leaning on defeq? | `#defeq_abuse in <tac>` — runs `tac` at both `backward.isDefEq.respectTransparency` settings, names the `isDefEq` checks that only pass at the loose one. Needs `import Mathlib.Tactic.DefEqAbuse`. Experimental; tactic still runs, so the proof stays valid while debugging. Use before deleting a `rw`/`change` that looks redundant — e.g. `rw [Set.mem_sUnion] at h` before an `obtain h` |
| Inaccessible hypothesis `h✝` after `rintro`/`cases` | `expose_names`, rather than hand-fixing with `rename_i` |
| Case-split following a function's own equations | `fun_cases` — non-recursive twin of `fun_induction` |
| Rewrite under `≤`/`⊆` rather than `=` | `grw` / `grewrite` — fits `Extra/Rel.lean`'s vocabulary |
| Rewrite only the *n*th occurrence | `nth_rw` / `nth_rewrite` |
| Congruence at a chosen subterm | `congrm` / `congr!` |
| Strip matching binders off goal *and* hypothesis | `peel` |
| Factor a `have` into a standalone lemma | `extract_goal` |
| Generalize before `induction` | `revert` |
| Symmetric cases proved once | `wlog` |

Already in use, keep using: `grind` (`Extra/List.lean:720`), `omega`, `gcongr`, `mono`,
`fun_induction`, `plausible`, `positivity`, `solve_by_elim`.

### Not relevant here

Algebra/analysis/number-theory families — `abel`, `ring`, `linarith`/`nlinarith`, `field_simp`,
`polyrith`, `measurability`, `continuity`, `fun_prop`, `bv_decide`, `norm_num`, `qify`/`rify`/`zify`.
This is a compiler development over relations, sets, lists and options. Reaching for them is a
signal the goal was mis-stated, not that the tactic was missing.
