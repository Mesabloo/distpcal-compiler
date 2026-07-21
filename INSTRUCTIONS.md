# INSTRUCTIONS.md

*How* to work on this project. *What* to build: see `CLAUDE.md` pointers.

## Rule matter most

**Ask before decide things plan no decide.** Hit design fork not covered and not obviously
implied by rest of plan: add to `OPEN_QUESTIONS.md`, ask, don't guess. Don't re-litigate
things plan mark decided without concrete reason ("think X nicer" not concrete; "X
impossible because Y" is).

Resolve open question: write decision + rationale into `PLAN.md`'s relevant section as
settled fact, then **delete entry from `OPEN_QUESTIONS.md` entirely** — not struck-through,
not marked resolved. `OPEN_QUESTIONS.md` lists only what still genuinely open. New
ambiguity: add there, don't decide unilaterally.

## Working conventions

- Caveman register in all responses and in `PLAN.md`/`OPEN_QUESTIONS.md` themselves —
  condensed, current-state-only. Source-file doc comments stay normal prose.
- Refer to current plan file(s) before make design call.
- **Log implementation findings in `.claude/FINDINGS.md`, not `PLAN.md`.** Findings = bugs
  hit and fixed, dead ends, debugging notes, "confirmed via N fixtures" — anything with a
  *when* or *story*.
- **`PLAN.md` gets only resulting decisions, written as settled fact — never history.** No
  "earlier draft said X", no "found bug, corrected to Y", no "per project owner", no dates,
  no phase-session markers. Reader should not be able to tell a section was revised.
- Use `STRUCTURE.md` to find where things live instead of `ls`/`find`. Update it whenever
  file added, removed, moved.
- **Always use `lean-lsp` connector when edit `.lean` files.** Plain `lake build` only for
  final build at end of task.
- **Search mathlib/Lean via `lean-lsp`'s `Loogle`, not `grep` over `.lake`.** Raw `grep`/`ls`
  over `.lake` only when `Loogle` genuinely can't answer.
- **Wait for explicit approval before start next task** from task list or plan. Finish one,
  stop, report, wait.
- Prior art already solve something well: say so, reuse idea. "Fresh rewrite" is about
  architectural ownership, not novelty.

## Lean conventions

Carried from prior art's `lakefile.lean`; raise open question before dropping any:

- `autoImplicit` **off**. Every implicit argument explicit in `variable` block or signature.
- `linter.missingDocs` on by default (toggleable for fast iteration). Don't leave off by
  time module "done".
- `pp.unicode.fun` on — write `λ x ↦ y`, not `fun x => y`.
- Adopt prior art idioms: `Located α` (position-tagged AST nodes) with `match_source`/`@@`
  notation pair; `Bifunctor`/`Bitraversable` instances on every two-parameter AST; type-level
  encoding of structural invariants where cheap.
- Pass naming: `<Source>2<Target>`, matching `lean_lib` shorthand in `lakefile.lean`.
- **Compilation functions monad-polymorphic** — abstract `{m : Type _ → Type _}` plus the
  typeclass constraints the pass actually needs, not a fixed `ReaderT`/`ExceptT` stack.

## Build & iterate

- `lake build` standard. Prior art's dev-mode CLI wrapper (`fugue.sh`) reasonable model.
- Build incrementally per plan's phase order — each phase leaves project buildable, even
  with parts stubbed `sorry`/`throw`. "Whole pipeline not done" doesn't block a complete,
  buildable phase.
- **Expect real breakage from toolchain bump**, including in vendored `Extra/` lemmas under
  Mathlib/Batteries API drift. Cuts both ways: some broken theorems may become provable once
  upstream partial API change fixed.
- Add semantics module for a core-language module only once that pass has (or actively
  getting) a refinement proof.

## Verification work

- Only pass committed to proving *in full* is Guarded→Network. Deep in proof for anything
  else: stop, confirm wanted. One standing exception: well-scopedness preservation lemma over
  Elaborator/Computable2Guarded *is* in scope — precondition for Guarded→Network's proof, not
  full behavioral correctness of that pass (stays deferred).
- Verification infrastructure (trace/relation/denotational) vendored as generic. New pass's
  proof needing changes to it: flag it — likely framework missing something general (fine to
  fix), or something pass-specific leaking in (proof structured wrong).

## Things not start without check in first

- Go denotational semantics / domain theory work — research-level, out of near-term scope.
- Join Calculus interpreter or further lowering — deliverable is a well-formed `.join` file;
  what happens after is unresolved.
- Formal example/regression test suite — deprioritized. Small hand-written smoke checks while
  developing a pass fine and encouraged; maintained suite is separate, unscoped.
