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
  `VerifiedCompiler/Denotational/StrongRefinement.lean:713` (`constructor`), `:781` (`where`)
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
  branch silently changes which goal the rest applies to. Only a combinator (`<;>`, `all:`)
  is exempt, being explicit about applying to every goal.
  `Guarded2Network/Lemmas/Statement.lean:193` (a two-hole `refine`),
  `VerifiedCompiler/Denotational/StrongRefinement.lean:349` (an `obtain` whose second branch runs to
  the end of the proof — bulleted anyway)
- **Goal selectors are Rocq-style, not `all_goals`/`on_goal`.** `CustomPrelude.lean` defines a
  `tac_selector` syntax: `all: tac` instead of `all_goals tac`, `3: tac` instead of
  `on_goal 3 => tac`, and ranges/unions on top of that — `1,3-5,9-12: tac`. Works in `conv` too.
  Use it; the stdlib spellings are longer and cover less. Needs `meta import CustomPrelude` — add
  the import rather than fall back to `all_goals`.
- **No `by assumption` as a term argument.** Write `‹_›`, or `‹T›` when the type is short enough to
  read. `f (by assumption)` opens a tactic block to do what a term already says, and hides which
  hypothesis is meant. `VerifiedCompiler/Denotational/Tactics.lean:69`,
  `Guarded2Network/Lemmas/AtomicBranch.lean:186`
- **`mvcgen`'s `invariants` and `with` go on their own lines, and their `|` alternatives are not
  indented** — same shape as a `match`. The alternatives are siblings of the keyword, not arguments
  to it, and indenting them reads as if they were.
  ```
  mvcgen [stepBlock, stepBranch_spec]
  invariants
  | inv1 => ⇓? ⟨cur, res⟩ st => ⌜…⌝
  with
  | vc4 | vc6 | vc5 | vc7 => intro _ _ _; assumption
  ```
  `Guarded2Network/Lemmas/AtomicBlock.lean:80`
- **Grouping a tactic sequence: `{ … }` when it must close the goal, `( … )` when it need not.**
  `{ … }` errors if anything is left open, so it is the one to reach for wherever the block is
  supposed to finish the goal — it turns a silent leftover into a failure. `( … )` only groups.
  A block that spans lines keeps its opening brace/paren on the line that opens it, puts the first
  tactic on the next line indented under it, and closes with `}`/`)` alone on the last line dedented
  back to that line's column. One-liners stay one-liners — `(tac₁; tac₂)` is fine. Where this comes
  up: a tactic taking a *single* tactic argument (`mvcgen … with`) whose argument is really a
  sequence — `Guarded2Network/Lemmas/AtomicBranch.lean:174`. Ungrouped, the sequence silently
  truncates to its first tactic and the rest applies to whatever goal happens to be first.
- **No `rw [show … by …]`.** Inline `show`-by-tactic inside a rewrite hide a real proof step in a
  rewrite argument. State it as a `have` and rewrite with that.
  `Extra/Seq.lean:125` — `have hm : m = 0 := by omega`, then `rwa [hm] at h`
- **No `(by …)` in argument position.** Same reason: a tactic proof passed as an argument is a step
  with no name and no goal displayed. Two replacements, in this order.

  **A term, when one exists** — and usually one does, because the side condition is a hypothesis
  already in context up to defeq. `n < m` *is* `n + 1 ≤ m` and `i + 0` *is* `i`, so `hm_min n
  (by omega)` is `hm_min n hn` and `have him : i = m := by omega` over `hi : i + 0 = m` is
  `obtain rfl : i = m := hi`. A bridging lemma is the same mistake one step later:
  `Nat.lt_of_lt_of_eq hn rfl` and `Nat.succ_inj.mp (congrArg Nat.succ hi)` are longer spellings of
  `hn` and `hi`. Where the step is real, name it — `ih (Nat.le_of_succ_le hn)`.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:346`, `:361`, `:384`, `:385`

  **Otherwise a `?_` and the next line.** `exact f (g (by tac))` is `refine f (g ?_)` then `tac`;
  `exact f x (by tac)` is `apply f x` then `tac`. The side goal gets displayed and gets its own
  line, and `omega` on it is then fine — the objection was to the position, not the tactic. `:373`,
  `:375`, where two `(by omega)`s became `simp +arith [← hi]` under their own `refine`/`apply`.

  Too common to mechanize, so not in the checker.
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
- **A proof-local definition is a `let`, never a `set`.** `set` exists to abstract a term that
  *already occurs* in goal or context; a name for something new is `let`. Three things follow, all
  at `VerifiedCompiler/Denotational/StrongRefinement.lean:308`–`:314`, where four `set`s became four
  `let`s:

  **Binders on the left of `:=`.** `let cont (i : ℕ) (σ : α) : Prop := …`, not
  `set cont : ℕ → α → Prop := λ i σ ↦ …`. Parameters read as parameters, the annotation shrinks to
  the result type, and the body stops being a lambda nobody applied.

  **Then eta-reduce what is left.** `let σs : ℕ → α := Nat.rec σₛ (λ i s ↦ (nextp i s).1)` (`:313`) —
  the old form bound `n` only to hand it straight through. Binder form when the body uses the
  binder, arrow type and point-free body when it does not.

  **And drop the `with h` equation.** A `let` *is* its body: `rfl` proves `σs 0 = σₛ` (`:316`),
  `change` retypes the goal against it, `unfold cont` opens it by name (`:322`). `set`'s `with h`
  is only there to undo `set`'s own abstraction — three equation names died with the `set`s and
  nothing needed them. Naming the equation is not a reason to reach back for `set` either:
  `let (eq := h) x := e` does it, giving `h : e = x` (body first, like `set … with ← h`).

  What survives as `set` is the bare form over a closed term, `set m := Nat.find hall` (`:339`).
  Even there `set` and `let` both produce a local definition, so with nothing to abstract the two
  differ in name only.
- **`have` takes binders too, and usually no type.** `have hm_min i (hi : i < m) :=
  not_not.mp (Nat.find_min hall hi)` (`:341`), not
  `have hm_min : ∀ i, i < m → cont i (σs i) := λ i hi ↦ …`. Binder syntax and inference between them
  delete a restated `∀`/`→` telescope and the `λ` that re-introduces it; what is left is the one
  thing a reader cannot recover, the proof. Ascribe the type when it is the point of the `have` —
  when inference would land somewhere unhelpful, or the statement is what the next step reads.
- **Defeq massaging is `change`, not `simp only` over `rfl`-`have`s.** `have : x = y := rfl` followed
  by `simp only [this, …]` states the new goal *and* pays a traversal to arrive at it. `change`
  states it once, and the traversal was never doing anything. `:320` replaced
  `have : σs (i + 1) = (nextp i (σs i)).1 := rfl` plus `simp only [this, hes, hnextp, dif_pos h]`
  with a `change`, an `unfold nextp`, and `repeat rw [dif_pos h]` — three lines, each naming which
  of the three things it does. `unfold` reaches a local `let` by name, so no equation is needed for
  that step either. Same rule as the bare-name `have` above, one level out: a `rfl`-`have` consumed
  by a single `simp only` is a `change`.
- **Never pack a term only to unpack it.** `obtain ⟨a, b, c⟩ : ∃ …, … := ⟨x, y, z⟩` builds an
  existential out of components that already have names and destructures it on the same line; the
  ascription then restates types those components already carried. Write the `have`s.
  `:339`–`:341`, where an `obtain` of `∃ m, ¬cont m (σs m) ∧ ∀ i, i < m → cont i (σs i)` against
  `⟨Nat.find hex, Nat.find_spec hex, λ i hi ↦ …⟩` became a `set` and two `have`s.

  `obtain ⟨…⟩ : T := by tac` is a different tactic and stays fine — there the ascription is the
  tactic block's goal, which it genuinely needs.

  Mirror case, in the same hunk: `obtain ⟨n, hn⟩ := hall` and then `⟨n, hn⟩` reassembled *is*
  `hall`. Destructure only what stays destructured.
- **`obtain rfl : a = b := proof`, not `have h : a = b := …` then `rw [h]`.** Substitution collapses
  the two names and takes the equation out of context; `rw` leaves `h` behind and only fires where
  it was aimed. `:361`
- **`rw` then `exact <hypothesis>` is `rwa`.** Whenever the tactic after a rewrite is `exact h` for
  a name already in context, the rewrite absorbs it: `rw [foo] at h; exact h` is `rwa [foo] at h`,
  and `rw [foo]; exact h` is `rwa [foo]`. Same for `erw`/`erwa`. Applies whichever side the rewrite
  targets — the pattern is "rewrite, then close by assumption", and `rwa` *is* that pattern.
  `Guarded2Network/Lemmas/Monad.lean:56`
- **`have h := e` then `simp only [S] at h` then `exact h` is `simpa only [S] using e`.** Same
  absorption as `rwa`, one tactic over: the hypothesis exists only to be simplified and handed
  over, so it needs no name and no line.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:394`. Three riders:

  **Name the lemmas — `simpa only [S]`, not `simpa`.** Same reason terminal `simp` is a liability.
  `:362`, where `simpa using hea_mem` became `simpa only [Monoid.partialProd_zero, one_mul]`.

  **Drop `using` when the term is already a hypothesis.** Bare `simpa only [S]` simplifies the goal
  and closes with `assumption`, so a name in context need not be repeated. `:362` again.

  **`using!` when closing needs a local `let` unfolded.** `simpa … using e` matches at *reducible*
  transparency, which does not see through a local definition; `using!` matches at the ambient one.
  At `:394` the goal is about `σₛ` and the term about `σs 0` — defeq only after `σs` unfolds, so
  plain `using` fails there.
- **`intro …` then a closing `simp` is `simp_intro …`.** When a subgoal is `intro`'d only to be
  finished by a bare `simp`, `simp_intro` does both — it introduces the binders and simplifies as
  each arrives. `simp_intro ..` introduces every remaining binder. Name the lemmas
  (`simp_intro x [S]`) when the `simp` needs them, for the same reason a terminal `simp` is a
  liability. `Guarded2Network/Lemmas/Precondition.lean:1297`
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
  `VerifiedCompiler/Denotational/StrongRefinement.lean:372`, where two hoisted `have`s became
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

  **Exception: rewriting.** When the massaging targets a *hypothesis* the proof goes on to use,
  forward is the honest shape — `have h := lemma …` then `rwa [...] at h`. Aiming the same rewrite
  at the right occurrence in the goal is more cumbersome, not less.
  `VerifiedCompiler/ClosedForm.lean:197`

  The exception stops where the hypothesis does. A `have` massaged and then immediately spent on
  the goal is the `rwa`/`simpa … using` pattern under another name, and gets written that way —
  see those two rules above. `VerifiedCompiler/Denotational/StrongRefinement.lean:394`
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
  `VerifiedCompiler/Denotational/StrongRefinement.lean:663` — `Aborting.star`, forty lines of
  induction twinned with `Diverging.star`, now derived from it through `Diverging.toAborting`
- **Name introduced hypotheses in signature order.** `rintro`/`intro` names should run in the order
  the binders appear, so a reader can match them without counting. Out-of-order naming reads as a
  slip even when deliberate. Naming by role rather than by position is the usual cause:
  `VerifiedCompiler/Denotational/StrongRefinement.lean:542` used to read `rintro ref₁ ref₃ ref₂`
  because `ref₃` was "the aborting one".
- **Delete `have`/`haveI` the proof does not use.** Lean's linter does not catch an unused
  `haveI`, so a dead instance survives every refactor that made it dead.
  Checking a deletion needs a forced rebuild — delete the `.olean` first, else `lake build` replays
  the cache and reports success over the unchanged source. The one this repo had was
  `haveI : Nonempty α := ⟨σ⟩` in front of a `choose!`, which does not need it.
- **Never `rename_i`, never `expose_names`.** Both reach for a hypothesis by *position* in the
  context — the one thing that changes under every edit to the tactic above them, silently and
  without a type error. The replacements, in order:

  **`next x y => tac`.** Selects the next goal *and* names its trailing inaccessibles, so the names
  arrive attached to the branch that has them rather than as a separate line. This is what a
  `· rename_i h` bullet always meant. `Guarded2Network/Lemmas/Precondition.lean:718`, three
  post-`mvcgen` goals whose loop invariant has no other name.

  **Or name it where it is bound** — an `rintro`/`obtain` pattern, or a `case`/`with` alternative.
  A hypothesis is inaccessible because something upstream declined to name it; naming it there is
  strictly better than renaming it here.

  **Or do not need the name.** A binder inaccessible in an induction case usually means the proof
  should not be mentioning it. `Walk.reorder_aborting`'s `receive` case wanted `st.i` for a
  `← Nat.zero_add st.i`; `st` was inaccessible, and `simpa only [Nat.zero_add] using …` under a
  `refine`'s `?_` says the same thing without naming anything.

  The escape hatch is a syntax quotation: `CustomPrelude.lean:78`, `:82` build `rename_i` *into*
  `split … using` and `injections with`, which exist so that no proof has to write it.
  `scripts/lean-style` checks for it outside quotations.
- **`by classical` on one line.** Not `by`, then `classical` next line.
- **`contradiction`, not `Option.noConfusion`.** `noConfusion` need its implicits line up, fail
  `Application type mismatch` when they don't.
- **`by_cases! h : p`**, not `by_cases h : p` then `push_neg at h`. `!` do `push_neg` itself. Same
  for `by_contra!`. `VerifiedCompiler/Denotational/StrongRefinement.lean:326`,
  `VerifiedCompiler/ClosedForm.lean:193`
- **No `exact absurd x y`.** Use `absurd` tactic (`absurd x`, then supply negation), `nomatch h`
  when `h` itself impossible equation, or — when the absurdity is an equation between distinct
  constructors — name it with a `have` and let `contradiction` find it.
  `Extra/Seq.lean:71` (`absurd` tactic), `Guarded2Network/Lemmas/Statement.lean:226`
  (`have habs := …` then `contradiction`)
- **Never `native_decide`, never `decide +native`.** Hard rule, no exceptions. `native_decide`
  compiles the goal to native code and trusts the result — it widens the trusted base past the
  kernel and past `Decidable` instances the kernel can actually run, and a miscompile or an
  `@[implemented_by]` mismatch becomes an unsound proof with no diagnostic. `decide` (kernel
  reduction) is fine when it terminates; when it does not, the fix is a real proof, not `+native`.
  A stuck `decide` on a non-exposed definition is a `@[expose]` or an inversion lemma away, not a
  `native_decide` away.
- **Aesop terminal or not at all** (plan §3 T1). Non-terminal aesop leave whatever search stopped
  at — same instability as non-terminal `simp`, worse, because later steps written against fixed
  goal order. `Core/NetworkPlusCal/Semantics/Lemmas.lean:449`
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
| `StrongRefinement` matching disjunct | `refines_match σ, ε` — two-arg form | `VerifiedCompiler/Denotational/Tactics.lean:41` |
| Source aborted instead | `refines_abort ε` | `:50` |
| Source diverges too | `refines_diverge ε` | `:57` |
| `Rτ ε' ε` goal | `trace_rel` | `:62` |
| `ε' ≼[Rτ] ε` goal | `trace_pfx` | `:66` |
| Rewrite blocked only by unfolding | `erw` — `erwa` when it then closes by `assumption` | `CustomPrelude.lean:70` |
| `split` needing named hypotheses | `split … using n \| n _` | `:75` |
| `injections` needing names | `injections with a b` | `:81` |
| Build `Iff` from two directions | `iff_intro x y` / `iff_rintro p q` | `:84`, `:86` |
| `trans` with subgoals reversed | `trans'` | `:89` |
| Different tactic per subgoal | `t <;> [t₁ \| t₂]` | `:93` |
| Tactic on a *range* of subgoals, Rocq style | `1-3 : tac`, `all : tac` | `:110` |

### Style already decided — old vs new

The project made these calls; they are not open.

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
- **Monadic `G2NM` goal → `mvcgen`.** Runs stock `mvcgen_trivial` — no custom VC-discharge hook.
  One was registered at `Guarded2Network/Lemmas.lean:38` but was reachable from nothing that calls
  `mvcgen` (no subfile under `Guarded2Network/Lemmas/` imported the aggregator back) and its target
  (`sem_side`) was itself deleted as unused; both removed rather than fixed.
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
- **A rewrite that fails only up to unfolding → `erw`, or `erwa` when the result is already a
  hypothesis.** Not `simp only [theOneUnfoldingLemma]`, and not adding a `@[simp]` tag to make a
  `simp` fire. `erwa` is `erw` followed by `assumption` (`CustomPrelude.lean:70`); plain `erw` is
  the same rewrite without that discharge, for when the goal is left open. Both are cheaper than a
  `simp` call and say which unfolding the step leans on.

  Same for a goal that is closed by definitional equality outright: `rfl`, or `show …` / `change …`
  to restate it in the form the next step wants. A `simp only` whose lemma list is one or two
  unfolding lemmas (`*_eq`, `*_apply`, a bare `def` name) is almost always one of these written the
  long way.

  Keep `simp` where it is doing real work — rewriting under binders, normalizing a union, closing a
  goal by a many-lemma chain. The rule is about `simp` used as a way to avoid naming a defeq step.

  Zero call sites in this project today; that measures a proof-writing habit, not the tactics. See
  `.claude/FINDINGS.md` §Tactic adoption, and `#defeq_abuse` in the table below for checking which
  steps actually lean on defeq.
- **An `induction` whose IH goes unused is a case split → `rintro (_|i)`.** Nothing mentions `ih`,
  so `induction … with | zero | succ i ih` costs the reader a hunt for the recursive appeal that is
  not there, and costs two lines of `| case =>` scaffolding to say what a pattern says. Fold the
  split into the `rintro`/`obtain` that was already there and bullet the branches.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:330`, `:344`
- **Introduce every binder before the split, not inside each branch.** `intro n hn` and *then*
  `induction n` — not `intro n`, then `intro hn` in one branch and `exact λ _ ↦ …` in the other.
  `induction` reverts the hypotheses that depend on the target and reintroduces them per branch, so
  the IH comes out already quantified over them and is applied to the reproved side condition:
  `ih (Nat.le_of_succ_le hn)`. Hand-threading `∀ n, n ≤ m → …` through the branches reaches the
  same IH with the binders written twice.
  `VerifiedCompiler/Denotational/StrongRefinement.lean:380`, `:384`

### Available, unused here, worth reaching for

Not yet used here, checked against the pinned toolchain's tactic set. Consider them before
hand-rolling the equivalent.

| Situation | Tactic |
|---|---|
| Find the lemma that closes goal | `exact?` / `apply?` / `rw?` — use while developing, paste the found term |
| Is this step leaning on defeq? | `#defeq_abuse in <tac>` — runs `tac` at both `backward.isDefEq.respectTransparency` settings, names the `isDefEq` checks that only pass at the loose one. Needs `import Mathlib.Tactic.DefEqAbuse`. Experimental; tactic still runs, so the proof stays valid while debugging. Use before deleting a `rw`/`change` that looks redundant — e.g. `rw [Set.mem_sUnion] at h` before an `obtain h` |
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
