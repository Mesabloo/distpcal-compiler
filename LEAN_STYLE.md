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
  `VerifiedCompiler/Denotational/StrongRefinement.lean:710` (`constructor`), `:785` (`where`)
- **Existential goal: `exists`, not `refine ⟨…⟩`.** `exists w₁, w₂` supply the witnesses and leave
  what is left as the goal, no `?_` to count and no closing `⟩` to match. It descend through `∧`
  and finish with `trivial`, so a component already in context need not be named at all.
  Applies whenever the holes are **trailing** — hole nested inside a term (`Or.inr ?_`,
  `λ i ↦ ?_`) stay `refine`, `exists` having no way to spell that.
  `Extra/Seq.lean:226`, `VerifiedCompiler/Denotational/StrongRefinement.lean:73`
  ✗ `VerifiedCompiler/Denotational/StrongRefinement.lean:77`, `:248` — legitimately `refine`,
  the hole sit under `Or.inr`
- **Bullet every subgoal.** A tactic that split the goal is followed by one `·` per branch, always —
  never one bullet and then the next branch's tactics written unindented at the bullet's own column.
  Unbulleted, nothing marks where one branch ends and the next begins, and a later edit to the first
  branch silently changes which goal the rest applies to. Only a combinator (`<;>`, `all_goals`)
  is exempt, being explicit about applying to every goal.
  `Guarded2Network/Lemmas/Statement.lean:193` (a two-hole `refine`),
  `VerifiedCompiler/Denotational/StrongRefinement.lean:345` (an `obtain` whose second branch runs to
  the end of the proof — bulleted anyway)
- **No `rw [show … by …]`.** Inline `show`-by-tactic inside a rewrite hide a real proof step in a
  rewrite argument. State it as a `have` and rewrite with that.
  `Extra/Seq.lean:125` — `have hm : m = 0 := by omega`, then `rwa [hm] at h`
- **Avoid `(by …)` term arguments.** Same reason: a tactic proof passed as an argument is a step
  with no name and no goal displayed. Prefer a named `have`. Not absolute — `(by omega)` on a
  side condition is tolerable — and too common to mechanize, so not in the checker.
- **Leave no live compiler warning.** Unused binder gets `_`, not a name. Unused section variable
  gets `omit`. `<;>` where `;` suffice gets `;`. Warnings accumulate until nobody reads them, and
  the real one arrives unnoticed. Not in `scripts/lean-style` — needs a build.
  `Guarded2Network/Lemmas/Statement.lean:537` (`omit [ExprSemantics V] in`, which must go *above*
  the doc comment — after it, the parser reports `unexpected token 'omit'`).
  `mvcgen`'s experimental banner is expected, not a warning to chase.
- **`have x : Y := z` for a bare name `z` is never right.** Two cases, both with a better form.
  `z` a hypothesis: retyping by defeq is `change Y at z` — the `have` leaves two names for one
  thing and hides that nothing was proved. `z` a nullary global: inline it at its use site instead
  of naming it, unless it is used several times or the name genuinely reads better than the term.
  `Guarded2Network/Lemmas/Monad.lean:68`. `scripts/lean-style` checks the one-line form.
- **`rw` then `exact <hypothesis>` is `rwa`.** Whenever the tactic after a rewrite is `exact h` for
  a name already in context, the rewrite absorbs it: `rw [foo] at h; exact h` is `rwa [foo] at h`,
  and `rw [foo]; exact h` is `rwa [foo]`. Same for `erw`/`erwa`. Applies whichever side the rewrite
  targets — the pattern is "rewrite, then close by assumption", and `rwa` *is* that pattern.
  `Guarded2Network/Lemmas/Monad.lean:56`
- **Merge `rw [...]` into a following `simp only [...]`.** Rewrite lemmas go straight into the
  `simp only` set — two traversals become one, and the intermediate goal nobody looks at stops
  existing. `VerifiedCompiler/Denotational/StrongRefinement.lean:316`, `:368`

  Same for a following `grind`: try folding the lemma in as `grind [= X]` first.

  **Where the merge does not go through, use `rewrite`, not `rw`.** `simp only` rewrites everywhere
  and repeatedly where `rw` rewrites the first match once, so the merged set can loop or overshoot —
  `Extra/Seq.lean:244` hits `maximum recursion depth`, `Guarded2Network/Lemmas/Statement.lean:403`
  leaves the goal unsolved, and `grind only [= List.length_pos_iff, …]` fails at
  `Extra/List.lean:701`. Keeping the two steps separate is then right, but `rw`'s closing `rfl`
  attempt is dead work when a `simp`/`grind` follows — and a *failing* `rfl` at that. `rewrite` is
  the same tactic without it. `Extra/Seq.lean:244`, `Extra/List.lean:701`,
  `Guarded2Network/Lemmas/Statement.lean:403`
- **Prefer backward mode over a forward `have` chain.** Build the goal with `refine f ?_ ?_` and
  discharge the pieces in bullets, rather than naming every intermediate with `have` and closing
  with `exact f h₁ h₂`. Each subgoal then arrives with its expected type displayed instead of
  having to be guessed and stated. Same reason `apply` chains beat nested `exact`.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:369`, where two hoisted `have`s became
  `refine abs (Relation.lcomp₁.intro (b := σs (i + 1)) ?_ ?_)` and two bullets.

  **Name the intermediate the goal does not fix.** A composition lemma's middle state occurs in
  neither side of the conclusion, so `refine` cannot infer it and reports "don't know how to
  synthesize implicit argument" — supply it as `(b := …)` rather than falling back to forward mode.
  The forward `have`s were pinning it down implicitly; the named argument says so out loud.

  **And `_` the ones it does fix.** The mirror rule. A witness Lean can read off a *later*
  component of the same `refine` carries no information at the point it is written, and spelling it
  out buries the components that do. Write `_` there. Only spell a witness out when nothing else
  pins it down — the previous paragraph's case — or when the reader needs to see the choice.
  `Guarded2Network/Lemmas/Precondition.lean:475`, where
  `refine ⟨(M, F, .none), 1, 1, (await_lenGt_iff hsv hseq).mpr ⟨rfl, rfl, ?_⟩, hpair, ?_⟩` became
  `refine ⟨_, _, _, (await_lenGt_iff hsv hseq).mpr ⟨rfl, rfl, ?_⟩, hpair, ?_⟩` — the state and both
  traces are determined by the two membership proofs that follow them.

  Same test applies to a long explicit witness tuple: if a hypothesis already in context *is* the
  component, pass it. The same `refine` re-spelled a 17-field `consumption_pair_iff` witness that
  was exactly `hpair`, already in scope.

  **Exception: rewriting.** When the massaging targets a *hypothesis*, forward is the honest
  shape — `have h := lemma …` then `rwa [...] at h`. Aiming the same rewrite at the right
  occurrence in the goal is more cumbersome, not less.
  `VerifiedCompiler/ClosedForm.lean:197`
- **`unfold f` / `simp [f]` only inside a proof *about* `f`.** A definition's body belong to the file
  that define it. Downstream proof that unfold reach past the API into the body, and every such site
  break together the day the body change — the duplication is invisible because no two of them share
  a name. Characterize the definition once, beside it, one lemma per outcome and `↔` where both
  readings get used; downstream then `rw`/`obtain` against that name. Same rule as the `have` one
  below, one level up: the repeated thing is a *decomposition*, not a fact.
  `Core/ComputableTLAPlus/Semantics/Interface.lean` (`Memory.update_eq_some_iff`/`.update_eq_none_iff`
  /`.update_nil`), which replaced three copies of `unfold Memory.update` + `simp only
  [Option.bind_eq_some_iff]` + `obtain` in `Guarded2Network/Lemmas/Statement.lean`.
  Not in `scripts/lean-style` — deciding whether a file "is about" the constant it unfolds needs
  more than the text of one line.
- **A `have` re-derived in more than one proof is a lemma.** Hoist it, next to the class or
  definition it is about. Repeated `have`s drift apart under refactor and each copy has to be
  re-checked. `mulmono` is `T.Rτ_closed` repackaged and belongs beside the `Trace` class.
  Applies to whole proofs too, not just `have`s: two blocks with identical statements mean a
  diagnostic against one is a diagnostic against both, which is the cost the rule is about.
  `VerifiedCompiler/Trace.lean:60` (`MulClosed.rmul_le`, four copies of `mulmono`),
  `Guarded2Network/Lemmas/Statement.lean:259` (`fresh_split`, four copies of `hfe`/`hfr`),
  `VerifiedCompiler/Denotational/StrongRefinement.lean:666` — `Aborting.star`, forty lines of
  induction twinned with `Diverging.star`, now derived from it through `Diverging.toAborting`
- **Name introduced hypotheses in signature order.** `rintro`/`intro` names should run in the order
  the binders appear, so a reader can match them without counting. Out-of-order naming reads as a
  slip even when deliberate. Naming by role rather than by position is the usual cause:
  `VerifiedCompiler/Denotational/StrongRefinement.lean:543` used to read `rintro ref₁ ref₃ ref₂`
  because `ref₃` was "the aborting one".
- **Delete `have`/`haveI` the proof does not use.** Lean's linter does not catch an unused
  `haveI`, so a dead instance survives every refactor that made it dead.
  Checking a deletion needs a forced rebuild — delete the `.olean` first, else `lake build` replays
  the cache and reports success over the unchanged source. The one this repo had was
  `haveI : Nonempty α := ⟨σ⟩` in front of a `choose!`, which does not need it.
- **`by classical` on one line.** Not `by`, then `classical` next line.
- **`contradiction`, not `Option.noConfusion`.** `noConfusion` need its implicits line up, fail
  `Application type mismatch` when they don't.
- **`by_cases! h : p`**, not `by_cases h : p` then `push_neg at h`. `!` do `push_neg` itself. Same
  for `by_contra!`. `VerifiedCompiler/Denotational/StrongRefinement.lean:319`,
  `VerifiedCompiler/ClosedForm.lean:193`
- **No `exact absurd x y`.** Use `absurd` tactic (`absurd x`, then supply negation), `nomatch h`
  when `h` itself impossible equation, or — when the absurdity is an equation between distinct
  constructors — name it with a `have` and let `contradiction` find it.
  `Extra/Seq.lean:71` (`absurd` tactic), `Guarded2Network/Lemmas/Statement.lean:226`
  (`have habs := …` then `contradiction`)
- **Aesop terminal or not at all** (plan §3 T1). Non-terminal aesop leave whatever search stopped
  at — same instability as non-terminal `simp`, worse, because later steps written against fixed
  goal order. `Core/NetworkPlusCal/Semantics/Lemmas.lean:449`
  **One exception: under `mvcgen`.** `sem_side` registered as its VC-discharge hook, and `mvcgen`
  keep only what it close — so non-terminal is the point there. `Guarded2Network/Lemmas.lean:50`
- **Lemma in `sem` rule set: never apply by hand.** `sem_side` already discharge it. Query
  membership: `scripts/facts s <name>` show `aesop:sem`.
- **Signature indentation: binders 2, statement 4.** Continuation line carrying binders/hypotheses
  indent 2; line carrying the statement itself — after the top-level `:` — indent 4. Statement
  stay visually distinct from what it quantify over. Go-forward rule: most existing signatures put
  binders at 4. Not in `scripts/lean-style` — telling a binder line from a wrapped statement
  continuation need real parsing, and a crude version flag hundreds of conforming lines.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:91` ✗ `VerifiedCompiler/ClosedForm.lean:127`

### Language conventions

Set in `lakefile.lean`, not negotiable per-file:

- **`autoImplicit` off.** Every implicit explicit, in `variable` block or signature.
  `lakefile.lean:35`
- **`pp.unicode.fun` on — write `λ x ↦ y`, never `fun x => y`.** `lakefile.lean:36`. Holds in
  metaprogramming too, where the surrounding code is Lean's own: `CustomPrelude.lean:139`
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
| `Statement.reducing` membership goal | `sem_red`, then `sem_side` | `Core/NetworkPlusCal/Semantics/Lemmas.lean:426`, `:449` |
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

  **An `OrderHom`'s `monotone'` field needs `beta_reduce` first** — the goal is a beta-redex against
  the `toFun` just given, and `gcongr` reports "did not make progress" until it is reduced.
  `VerifiedCompiler/ClosedForm.lean:116`, `:251`

  **`gcongr` matches the relation syntactically**, so `≤` and `⊆` are different keys even on `Set`.
  Mathlib tags union at `⊆` only and this project's composition lemmas at `≤`, so a goal mixing the
  two matched neither; `Set.union_le_union` (`Extra/Rel.lean:59`) is the missing `≤` form.
- **Monadic `G2NM` goal → `mvcgen`.** `sem_side` already wired in as its VC-discharge hook, so
  cheap side conditions never surface as named verification conditions.
  `Guarded2Network/Lemmas.lean:60`, hook at `:54`
- **`Iff` goal whose both sides open with `intro`/`rintro` → `iff_intro` / `iff_rintro`.** Never
  `constructor` there. `iff_intro x y` take two idents, `iff_rintro p q` two rintro patterns, and
  both fold the `intro` into the split. `constructor` is right for an `Iff` only when the branches
  do *not* start by introducing. Applies after `ext` too, where the `Iff` only appears once the
  `ext` has run. `VerifiedCompiler/ClosedForm.lean:76` (post-`ext`), `Extra/Rel.lean:136`

  **One pattern per side, no more.** `iff_rintro` takes exactly one `rintroPat` on each side, so
  `intro h n` becomes `iff_intro h …` with the second `intro n` left in the bullet
  (`Extra/Seq.lean:158`). A pattern that itself splits — `(h|⟨…⟩)` — yields two goals for that side,
  so the bullets that follow are four siblings at one level, not two nested pairs.
  `Core/NetworkPlusCal/Semantics/Lemmas.lean:363`

  Both tactics live in `CustomPrelude`, reached by `meta import CustomPrelude`; it is not
  transitive, so a file using them needs that import of its own.
- **Need a stronger induction hypothesis → `induction x generalizing y z`.** Not a hoisted
  `have main : ∀ …` re-quantifying the arguments by hand and proving it by an inner `induction`.
  Hypotheses that would clutter the IH: `clear` them before the `induction`, not restate the goal
  around them. `VerifiedCompiler/Relation.lean:52`, `Extra/List.lean:67`,
  `VerifiedCompiler/ClosedForm.lean:228`,
  `VerifiedCompiler/Denotational/StrongRefinement.lean:172`

  Destructure *first*, then generalize: the run's `σs`/`es` only exist once the hypothesis is
  taken apart, so the `rintro`/`obtain` comes before the `induction`.
  **The IH's argument order is Lean's, not yours** — `generalizing` reverts in context order, and
  the resulting telescope need not follow the order you listed. Read it off the first
  "Application type mismatch" rather than guessing; that unpredictability is the one thing the
  hoisted `have main` did better, and it is not worth a hand-restated goal.

  Genuinely auxiliary facts stay `have`s. The rule is about a `have` that re-quantifies the
  *enclosing goal's* own variables — not about `have hstab : ∀ m, n ≤ m → …`
  (`Extra/Seq.lean:251`), whose statement is nothing the surrounding proof is trying to prove.

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
