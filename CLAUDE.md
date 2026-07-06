# CLAUDE.md

Working notes for whoever (human or Claude) implements this project. Read `PLAN.md`
first — it has the architecture, the pipeline stage-by-stage, the decisions already made,
and the open questions. This file is about *how* to work, not *what* to build. See
`STRUCTURE.md` for a directory-by-directory map of the repo.

## The one rule that matters most

**Ask before deciding things `PLAN.md` didn't decide.** The project owner was explicit
about this from the start of planning: they'd rather be asked than have an ambiguity
silently resolved one way. `PLAN.md` §9 is a running list of open questions for exactly
this reason — if you hit a design fork that isn't in §9 and isn't obviously implied by
the rest of the plan, add it there and ask, don't guess and move on. Conversely, don't
re-litigate things `PLAN.md` §2 marks as already decided without a concrete reason
("I think X would be nicer" is not a concrete reason; "X is actually impossible because
Y" is).

When you resolve an open question from §9 (or discover a new one), **update `PLAN.md` in
place** — move it out of §9 into §2 with the decision and rationale, or add it to §9 if
newly discovered. The plan is meant to stay accurate, not to be a frozen artifact from
this one planning session.

## Working conventions

- Talk like caveman in all responses, except inside documentation and markdown files
  (`CLAUDE.md`, `STRUCTURE.md`, `PLAN.md`, doc comments, etc.), which stay normal prose.
- Update `STRUCTURE.md` whenever a file is added, removed, or moved — keep the map current,
  not a snapshot from whenever it was last touched.
- Use the `lean-lsp` connector for most tasks. Reserve the final `lake build` at the end of
  a task for plain `lake build` (not `lean-lsp`).

## Reference material — where it lives, how to use it

- `reference/thesis.pdf` — "Generating Distributed Programs from Formal Specifications."
  The primary spec for the type checker (ch. 3.1), the Distributed→Guarded PlusCal
  desugaring (ch. 3.2), and the Network PlusCal→Join Calculus backend (ch. 8). Chapters 4,
  5, and 7 are stubs in this document — don't trust an empty section to mean "nothing to
  do here," it means "go read the code instead" (ch. 5) or "this is genuinely undesigned,
  see PLAN.md" (ch. 4, 7).
- `~/Documents/distpcal-compiler` (private repo, origin `github.com/mesabloo/distpcal-compiler`,
  several branches including an uncommitted local `typechecker` branch) and
  `github.com/mesabloo/fugue` (public mirror, branches `main`/`develop`/`go-semantics`/
  `lock-inference`/`docs`) are the two prior-art codebases. **Read them for design ideas;
  don't copy-paste them wholesale.** Per `PLAN.md` §2, this is a fresh rewrite that reuses
  only the genuinely generic infrastructure (`Extra/`, `VerifiedCompiler/`, `ProgressBar/`,
  `Common/`) — most domain-specific code (every AST, and every pass other than the three
  exceptions below) is written new against this project's own module layout, using prior
  art as a reference for *what the shape of the solution looked like*, not as a source to
  port line-by-line. The three exceptions, meant to be actually ported and refactored
  rather than rewritten, are the lexer/parser (`PLAN.md` §5.1 — the **local**
  `~/Documents/distpcal-compiler` checkout's `Parser_/` implementation, not the public
  `fugue` mirror's older parser), Guarded→Network (`PLAN.md` §5.5, proof included), and
  well-scopedness checking (`PLAN.md` §5.2a — `Core/GuardedPlusCal/Syntax/
  WellScopedness.lean` and `Core/TypedSetTheory/Syntax/WellScopedness.lean`; note there is
  no `Core/CoreTLAPlus/Syntax/WellScopedness.lean` in the local checkout, despite an
  earlier draft of `PLAN.md` claiming otherwise — only these two files exist there).
- If you're about to reimplement something and prior art already solved it well (e.g. the
  `Bool`-indexed terminal-statement encoding in `CorePlusCal`, or the general
  `StrongRefinement` framework), say so and reuse the idea — don't reinvent for the sake
  of it. The point of "fresh rewrite" is architectural ownership and not inheriting dead
  ends (like the abandoned `GoCal` denotational semantics attempts), not novelty for its
  own sake.

## Lean conventions

These are carried over from `distpcal-compiler`'s `lakefile.lean` and are worth keeping
unless there's a reason not to (raise it as a §9 item if so):

- `autoImplicit` is **off**. Every implicit argument is explicit in a `variable` block or
  the signature.
- `linter.missingDocs` is on by default (toggleable via `-KNO_CHECK_DOC` for fast
  iteration) — public declarations get doc comments. Don't let this block exploratory
  work, but don't leave it off by the time a module is "done."
- `pp.unicode.fun` is on — lambdas pretty-print as `λ x ↦ y`. Match that style in code you
  write, not `fun x => y`.
- Recurring idioms in prior art worth adopting rather than reinventing: `Located α`
  (position-tagged AST nodes) with a `match_source`/`@@` notation pair for
  pattern-matching through the position tag without boilerplate; `Bifunctor`/
  `Bitraversable` instances on every two-parameter AST (usually `(annotation, expr)`)
  generated mechanically alongside the type; type-level encoding of structural invariants
  where cheap (e.g. `CorePlusCal.Statement`'s `Bool`-indexed terminal/non-terminal split,
  `PLAN.md` §3.2) rather than runtime checks or comments asserting an invariant holds.
- Pass naming: `<Source>2<Target>` for compiler passes (`Guarded2Network`,
  `Network2Go`, `Typed2Guarded`, `Network2JoinCalculus`), matching `lean_lib Fugue.G2N`
  / `Fugue.N2Go` / etc. shorthand in `lakefile.lean`. Keep new passes consistent with this.
- **Compilation functions should be monad-polymorphic, not hardcoded against one concrete
  monad stack.** Write passes against an abstract `{m : Type _ → Type _}` type variable
  plus whatever typeclass constraints the pass actually needs (`[Monad m]`, plus effect
  classes for error-reporting/reader environment/etc.), rather than fixing a specific
  `ReaderT`/`ExceptT`/… stack up front. Prior art already does this in places — e.g.
  `Desugarer/TLAPlus.lean`'s `SurfaceTLAPlus.Expression.desugar`:
  `variable {α} {m : Type → Type} [MonadDesugarerExpr α m] [Monad m]` — follow that shape
  in new passes rather than inventing a different convention.

## Build & iterate

- `lake build` — standard build. Prior art's `fugue.sh` wrapper
  (`lake -R -KBUILD_TYPE=debug -KNO_CHECK_DOC exec fugue -D ... -- ...`) is a reasonable
  model for a dev-mode CLI wrapper script if useful during implementation — the flag
  surface itself is settled, see `PLAN.md` §2 and §9.3 for the few remaining details.
- Prefer building incrementally per `PLAN.md` §7's phase order — each phase should leave
  the project in a buildable state, even with large parts of the pipeline unimplemented
  or stubbed with `sorry`/`throw`. Don't let "the whole pipeline isn't done yet" block
  merging a phase that's internally complete and buildable.
- **Expect real breakage from the toolchain bump (`PLAN.md` §2), not just cosmetic
  fixes** — and not only in the three ported exceptions. `Extra/`'s vendored
  data-structure lemmas are exposed to the same Mathlib/Batteries API drift and may need
  real repair, not just a `simp` lemma rename here and there. This cuts both ways: some
  currently-broken `Extra/` theorems may become provable again once an upstream partial
  API change is itself fixed by the bump (e.g. string-related lemmas), so don't assume
  the bump is purely a cost to pay down.
- When adding a new `Core/<Lang>` module, only add `Semantics/` once that pass actually
  has (or is actively getting) a refinement proof — see `PLAN.md` §6.2. Don't speculatively
  write semantics for passes nobody is proving yet; it's maintenance cost with no payoff
  until proof work on that pass actually starts.

## Verification work specifically

- The only pass this plan commits to proving *in full* is Guarded→Network (`PLAN.md`
  §6.2). If you find yourself deep in a proof for anything else, stop and confirm that's
  actually wanted before sinking more time into it — it may well be wanted, but it's a
  scope expansion from what was agreed, and per the one rule above, that's worth a
  check-in. The one standing exception: the well-scopedness preservation lemma over
  `Elaborator`/`Typed2Guarded` (`PLAN.md` §2, §5.2a, §6.3) *is* expected and in scope — it's
  a narrow syntactic fact needed as a precondition for Guarded→Network's proof, not a
  detour into `Typed2Guarded`'s full behavioral correctness (which stays deferred, §6.3).
- `VerifiedCompiler/{Trace,Relation}.lean` and `VerifiedCompiler/Denotational/*.lean` are
  vendored as generic infrastructure — they shouldn't need domain-specific changes to be
  usable for a new pass's refinement proof. If a new pass's proof seems to need changes to
  `VerifiedCompiler/` itself, that's worth flagging (it likely means the framework is
  missing something genuinely general, which is fine to fix, versus something
  pass-specific leaking in, which probably means the proof is structured wrong).

## Things not to start without checking in first

Per `PLAN.md`, these are large enough, or ambiguous enough, that starting them
unprompted would burn real time on possibly the wrong thing:

- The Go denotational semantics / domain theory work (`PLAN.md` §6.4) — substantial,
  research-level, and explicitly out of this plan's near-term scope.
- A Join Calculus interpreter or further lowering (`PLAN.md` §9.1) — the committed
  deliverable is emitting a well-formed `.join` file; what happens after that is
  explicitly unresolved.
- Building out a formal example/regression test suite (`PLAN.md` §2) — deprioritized for
  now. Small hand-written smoke checks while developing a given pass are fine and
  encouraged; a maintained `tests/` suite is a separate, not-yet-scoped effort.
