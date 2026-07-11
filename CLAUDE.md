# CLAUDE.md

Work notes for whoever (human or Claude) build this project. Read `PLAN.md` first — got
architecture, pipeline stage-by-stage, decisions already made, open questions. This file
about *how* to work, not *what* to build. See `STRUCTURE.md` for directory-by-directory
map of repo.

## One rule matter most

**Ask before decide things `PLAN.md` no decide.** Project owner explicit about this from
start of planning: rather be asked than have ambiguity silently resolved one way. `PLAN.md`
§9 running list of open questions for exact this reason — hit design fork not in §9 and not
obviously implied by rest of plan, add it there, ask, don't guess and move on. Conversely,
don't re-litigate things `PLAN.md` §2 mark already decided without concrete reason
("think X nicer" not concrete reason; "X actually impossible because Y" is).

Resolve open question from §9 (or find new one), **update `PLAN.md` in place** — move out
of §9 into §2 with decision and rationale, or add to §9 if newly found. Plan meant stay
accurate, not frozen artifact from one planning session.

## Working conventions

- Talk like caveman in all responses, except inside source files and plan documents
  (doc comments, `PLAN.md`, other plan files, etc., stay normal prose — `CLAUDE.md` itself
  fine either way).
- Refer to `PLAN.md` and whichever other plan file current (e.g. anything under
  `.claude/plans/`) before make design call — see "One rule matter most" above.
- Use `STRUCTURE.md` find where things live instead of run `ls`/`find` over repo. Update it
  whenever file added, removed, or moved — keep map current, not snapshot from whenever
  last touched.
- **Always use `lean-lsp` connector when edit `.lean` files.** Reserve plain `lake build`
  (not `lean-lsp`) for final build at end of task.
- **Wait for explicit approval before start next task from task list or plan.** Finish one
  task, stop, tell owner what done, wait for go-ahead before pick up next item — don't
  chain through list on own steam.

## Reference material — where it live, how to use it

- `reference/thesis.pdf` — "Generating Distributed Programs from Formal Specifications."
  Primary spec for type checker (ch. 3.1), Distributed→Guarded PlusCal desugaring (ch. 3.2,
  now fully written including previously-stub §3.2.2.4 guard reordering), and Network
  PlusCal→Join Calculus backend (ch. 8). Chapters 4 and 5 still stubs — don't trust empty
  section mean "nothing to do here," it mean "go read code instead" (ch. 5) or "this
  genuinely undesigned, see PLAN.md" (ch. 4). Ch. 7 §7.1 (atomicity/lock inference) fully
  written; `PLAN.md` §5.7 follow its [HFP06]-derived algorithm instead of earlier
  connected-component scheme (§9.20). Second July 2026 revision also fill in §7.2.1.1 (Go
  representations of TLA+ types, now in `PLAN.md` §5.7 too) and open new numeric-dispatch
  question (`PLAN.md` §9.21). §7.2.1.2, §7.2.2, §7.3 remain stubs.
- `~/Documents/distpcal-compiler` (private repo, origin `github.com/mesabloo/distpcal-compiler`,
  several branches including uncommitted local `typechecker` branch) and
  `github.com/mesabloo/fugue` (public mirror, branches `main`/`develop`/`go-semantics`/
  `lock-inference`/`docs`) are two prior-art codebases. **Read them for design ideas; don't
  copy-paste wholesale.** Per `PLAN.md` §2, this fresh rewrite reuse only genuinely generic
  infrastructure (`Extra/`, `VerifiedCompiler/`, `ProgressBar/`, `Common/`) — most
  domain-specific code (every AST, every pass other than three exceptions below) written
  new against this project's own module layout, use prior art as reference for *what shape
  of solution looked like*, not source to port line-by-line. Three exceptions, meant
  actually ported and refactored rather than rewritten, are lexer/parser (`PLAN.md` §5.1 —
  **local** `~/Documents/distpcal-compiler` checkout's `Parser_/` implementation, not
  public `fugue` mirror's older parser), Guarded→Network (`PLAN.md` §5.5, proof included),
  and well-scopedness checking (`PLAN.md` §5.2a — `Core/GuardedPlusCal/Syntax/
  WellScopedness.lean` and `Core/TypedSetTheory/Syntax/WellScopedness.lean`; note no
  `Core/CoreTLAPlus/Syntax/WellScopedness.lean` in local checkout, despite earlier draft of
  `PLAN.md` claim otherwise — only these two files exist there).
- About to reimplement something and prior art already solve it well (e.g. `Bool`-indexed
  terminal-statement encoding in `CorePlusCal`, or general `StrongRefinement` framework),
  say so, reuse idea — don't reinvent for sake of it. Point of "fresh rewrite" architectural
  ownership and not inherit dead ends (like abandoned `GoCal` denotational semantics
  attempts), not novelty for own sake.

## Lean conventions

Carried over from `distpcal-compiler`'s `lakefile.lean`, worth keep unless reason not to
(raise as §9 item if so):

- `autoImplicit` **off**. Every implicit argument explicit in `variable` block or
  signature.
- `linter.missingDocs` on by default (toggleable via `-KNO_CHECK_DOC` for fast iteration)
  — public declarations get doc comments. Don't let this block exploratory work, but don't
  leave off by time module "done."
- `pp.unicode.fun` on — lambdas pretty-print as `λ x ↦ y`. Match that style in code write,
  not `fun x => y`.
- Recurring idioms in prior art worth adopt rather than reinvent: `Located α`
  (position-tagged AST nodes) with `match_source`/`@@` notation pair for pattern-matching
  through position tag without boilerplate; `Bifunctor`/`Bitraversable` instances on every
  two-parameter AST (usually `(annotation, expr)`) generated mechanically alongside type;
  type-level encoding of structural invariants where cheap (e.g. `CorePlusCal.Statement`'s
  `Bool`-indexed terminal/non-terminal split, `PLAN.md` §3.2) rather than runtime checks or
  comments assert invariant hold.
- Pass naming: `<Source>2<Target>` for compiler passes (`Guarded2Network`, `Network2Go`,
  `Typed2Guarded`, `Network2JoinCalculus`), match `lean_lib Fugue.G2N` / `Fugue.N2Go` /
  etc. shorthand in `lakefile.lean`. Keep new passes consistent with this.
- **Compilation functions should be monad-polymorphic, not hardcoded against one concrete
  monad stack.** Write passes against abstract `{m : Type _ → Type _}` type variable plus
  whatever typeclass constraints pass actually need (`[Monad m]`, plus effect classes for
  error-reporting/reader environment/etc.), rather than fix specific `ReaderT`/`ExceptT`/…
  stack up front. Prior art already do this in places — e.g. `Desugarer/TLAPlus.lean`'s
  `SurfaceTLAPlus.Expression.desugar`: `variable {α} {m : Type → Type}
  [MonadDesugarerExpr α m] [Monad m]` — follow that shape in new passes rather than invent
  different convention.

## Build & iterate

- `lake build` — standard build. Prior art's `fugue.sh` wrapper (`lake -R
  -KBUILD_TYPE=debug -KNO_CHECK_DOC exec fugue -D ... -- ...`) reasonable model for
  dev-mode CLI wrapper script if useful during implementation — flag surface itself
  settled, see `PLAN.md` §2 and §9.3 for few remaining details.
- Prefer build incrementally per `PLAN.md` §7's phase order — each phase should leave
  project in buildable state, even with large parts of pipeline unimplemented or stubbed
  with `sorry`/`throw`. Don't let "whole pipeline not done yet" block merge phase that
  internally complete and buildable.
- **Expect real breakage from toolchain bump (`PLAN.md` §2), not just cosmetic fixes** —
  and not only in three ported exceptions. `Extra/`'s vendored data-structure lemmas
  exposed to same Mathlib/Batteries API drift, may need real repair, not just `simp` lemma
  rename here and there. Cuts both ways: some currently-broken `Extra/` theorems may
  become provable again once upstream partial API change itself fixed by bump (e.g.
  string-related lemmas), so don't assume bump purely cost to pay down.
- Add new `Core/<Lang>` module, only add `Semantics/` once that pass actually has (or
  actively getting) refinement proof — see `PLAN.md` §6.2. Don't speculatively write
  semantics for passes nobody proving yet; maintenance cost with no payoff until proof
  work on that pass actually start.

## Verification work specifically

- Only pass this plan commit to proving *in full* Guarded→Network (`PLAN.md` §6.2). Find
  self deep in proof for anything else, stop, confirm actually wanted before sink more time
  into it — may well be wanted, but scope expansion from what agreed, per one rule above,
  worth check-in. One standing exception: well-scopedness preservation lemma over
  `Elaborator`/`Typed2Guarded` (`PLAN.md` §2, §5.2a, §6.3) *is* expected and in scope —
  narrow syntactic fact needed as precondition for Guarded→Network's proof, not detour into
  `Typed2Guarded`'s full behavioral correctness (stays deferred, §6.3).
- `VerifiedCompiler/{Trace,Relation}.lean` and `VerifiedCompiler/Denotational/*.lean`
  vendored as generic infrastructure — shouldn't need domain-specific changes to be usable
  for new pass's refinement proof. New pass's proof seem need changes to
  `VerifiedCompiler/` itself, worth flag it (likely mean framework missing something
  genuinely general, fine to fix, versus something pass-specific leaking in, probably mean
  proof structured wrong).

## Things not start without check in first

Per `PLAN.md`, these large enough, or ambiguous enough, that start unprompted would burn
real time on possibly wrong thing:

- Go denotational semantics / domain theory work (`PLAN.md` §6.4) — substantial,
  research-level, explicitly out of this plan's near-term scope.
- Join Calculus interpreter or further lowering (`PLAN.md` §9.1) — committed deliverable
  emit well-formed `.join` file; what happens after that explicitly unresolved.
- Build out formal example/regression test suite (`PLAN.md` §2) — deprioritized for now.
  Small hand-written smoke checks while develop given pass fine and encouraged; maintained
  `tests/` suite separate, not-yet-scoped effort.
