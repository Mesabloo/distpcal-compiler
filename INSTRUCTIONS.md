# INSTRUCTIONS.md

Vital working rules for whoever (human or Claude) build this project. *How* to work, not
*what* to build — for the latter see pointers in `CLAUDE.md`.

## Rule matter most

**Ask before decide things the plan no decide.** Project owner explicit about this from
start: rather be asked than have ambiguity silently resolved one way. `OPEN_QUESTIONS.md`
keep running list of open questions for exact this reason — hit design fork not covered
and not obviously implied by rest of plan, add it there, ask, don't guess and move on.
Conversely, don't re-litigate things plan mark already decided without concrete reason
("think X nicer" not concrete reason; "X actually impossible because Y" is).

Resolve open question (or find new one), **update both files in place**: write decision
and rationale into `PLAN.md`'s relevant section (as settled fact, see below), then
**delete that entry from `OPEN_QUESTIONS.md` entirely** — don't leave it there
marked resolved/struck-through, don't just copy the decision into `PLAN.md` and forget to
remove the old entry. `OPEN_QUESTIONS.md` should only ever list what's still genuinely
open. Newly found ambiguity: add it to `OPEN_QUESTIONS.md`, don't decide unilaterally.
Both files meant stay accurate, not frozen artifacts from one planning session.

## Working conventions

- Talk like caveman in all responses, including `PLAN.md`/`OPEN_QUESTIONS.md` themselves —
  both stay caveman register, condensed, current-state-only. Source-file doc comments stay
  normal prose.
- Refer to current plan file(s) before make design call — see "Rule matter most" above.
- **Log implementation findings in `.claude/FINDINGS.md`, separate from `PLAN.md`.**
  Findings = the trail of what happened while building: bugs hit and fixed, dead ends,
  debugging notes, "confirmed via N regression fixtures," anything with a *when* or a
  *story* attached. That log stays out of `PLAN.md` entirely.
- **`PLAN.md` gets only the resulting decisions/revisions, written as settled fact —
  never as history.** A bug fix that changes the design updates `PLAN.md`'s relevant
  section directly, stated like it was always the plan: no "earlier draft said X,"
  no "found a bug, corrected to Y," no "per project owner," no dates, no phase-session
  markers. Reader of `PLAN.md` should never be able to tell a section was revised —
  it should read as if this were the design from day one. Temporality is `FINDINGS.md`'s
  job, not `PLAN.md`'s.
- Use structure map (see `CLAUDE.md` pointers) find where things live instead of run
  `ls`/`find` over repo. Update it whenever file added, removed, or moved — keep map
  current, not snapshot from whenever last touched.
- **Always use `lean-lsp` connector when edit `.lean` files.** Reserve plain `lake build`
  (not `lean-lsp`) for final build at end of task.
- **Search mathlib/Lean for existing lemmas/defs via `lean-lsp`'s `Loogle` tool, not
  `grep`ping through `.lake`.** `Loogle` searches by type/name/pattern properly indexed —
  faster, more precise, no wading through vendored source. Reserve raw `grep`/`ls` over
  `.lake` for cases `Loogle` genuinely can't answer (e.g. reading one specific known file).
- **Wait for explicit approval before start next task from task list or plan.** Finish one
  task, stop, tell owner what done, wait for go-ahead before pick up next item — don't
  chain through list on own steam.
- About to reimplement something and prior art already solve it well, say so, reuse idea —
  don't reinvent for sake of it. Point of "fresh rewrite" architectural ownership and not
  inherit dead ends, not novelty for own sake.

## Lean conventions

Carried over from prior art's `lakefile.lean`, worth keep unless reason not to (raise as
open question if so):

- `autoImplicit` **off**. Every implicit argument explicit in `variable` block or
  signature.
- `linter.missingDocs` on by default (toggleable for fast iteration) — public declarations
  get doc comments. Don't let this block exploratory work, but don't leave off by time
  module "done."
- `pp.unicode.fun` on — lambdas pretty-print as `λ x ↦ y`. Match that style in code write,
  not `fun x => y`.
- Recurring idioms in prior art worth adopt rather than reinvent: `Located α`
  (position-tagged AST nodes) with `match_source`/`@@` notation pair for pattern-matching
  through position tag without boilerplate; `Bifunctor`/`Bitraversable` instances on every
  two-parameter AST generated mechanically alongside type; type-level encoding of
  structural invariants where cheap rather than runtime checks or comments assert
  invariant hold.
- Pass naming: `<Source>2<Target>` for compiler passes, match `lean_lib` shorthand in
  `lakefile.lean`. Keep new passes consistent with this.
- **Compilation functions should be monad-polymorphic, not hardcoded against one concrete
  monad stack.** Write passes against abstract `{m : Type _ → Type _}` type variable plus
  whatever typeclass constraints pass actually need, rather than fix specific
  `ReaderT`/`ExceptT`/… stack up front. Prior art already do this in places — follow that
  shape in new passes rather than invent different convention.

## Build & iterate

- `lake build` — standard build. Prior art's dev-mode CLI wrapper script (`fugue.sh`)
  reasonable model if useful during implementation — flag surface itself settled, see plan
  for details.
- Prefer build incrementally per plan's phase order — each phase should leave project in
  buildable state, even with large parts of pipeline unimplemented or stubbed with
  `sorry`/`throw`. Don't let "whole pipeline not done yet" block merge phase that
  internally complete and buildable.
- **Expect real breakage from toolchain bump, not just cosmetic fixes** — and not only in
  ported exceptions (see plan for which passes those are). Vendored data-structure lemmas
  exposed to same Mathlib/Batteries API drift, may need real repair, not just `simp` lemma
  rename here and there. Cuts both ways: some currently-broken theorems may become
  provable again once upstream partial API change itself fixed by bump, so don't assume
  bump purely cost to pay down.
- Add new core-language module, only add its semantics module once that pass actually has
  (or actively getting) refinement proof. Don't speculatively write semantics for passes
  nobody proving yet; maintenance cost with no payoff until proof work on that pass
  actually start.

## Verification work specifically

- Only pass this plan commit to proving *in full* is Guarded→Network. Find self deep in
  proof for anything else, stop, confirm actually wanted before sink more time into it —
  may well be wanted, but scope expansion from what agreed, per rule above, worth
  check-in. One standing exception: well-scopedness preservation lemma over
  Elaborator/Computable2Guarded *is* expected and in scope — narrow syntactic fact needed as
  precondition for Guarded→Network's proof, not detour into that pass's full behavioral
  correctness (stays deferred).
- Generic verification infrastructure (trace/relation/denotational framework) vendored as
  generic — shouldn't need domain-specific changes to be usable for new pass's refinement
  proof. New pass's proof seem need changes to that infrastructure itself, worth flag it
  (likely mean framework missing something genuinely general, fine to fix, versus
  something pass-specific leaking in, probably mean proof structured wrong).

## Things not start without check in first

These large enough, or ambiguous enough, that start unprompted would burn real time on
possibly wrong thing:

- Go denotational semantics / domain theory work — substantial, research-level,
  explicitly out of near-term scope.
- Join Calculus interpreter or further lowering — committed deliverable emit well-formed
  `.join` file; what happens after that explicitly unresolved.
- Build out formal example/regression test suite — deprioritized for now. Small
  hand-written smoke checks while develop given pass fine and encouraged; maintained test
  suite separate, not-yet-scoped effort.

(See plan's decisions/open-questions sections for exact current status of each item above
— this list only flag "stop and ask," not restate rationale.)
