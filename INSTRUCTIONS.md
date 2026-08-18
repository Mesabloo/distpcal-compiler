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

## Comments

Docstring say **what declaration is and what it guarantee**. Nothing else.

- No how-it-proved. Tactic-debugging note go inline `--` at the tactic (one line) or
  `.claude/FINDINGS.md` (story).
- No plan/task reference: `PLAN.md`, `OPEN_QUESTIONS.md`, `.claude/`, `§N`, `item N`, `D5`, `T1`.
- No thesis/paper citation. Provenance live in `reference/SPEC_MAP.md`, one row per declaration.
  Citation carry content ("merge along strict domination") ⇒ keep content, drop number.
- No history, no prior-art comparison, no "still owed"/"not yet"/"now". Read as if current state
  always was state — same rule `PLAN.md` follow.
- No `file.lean:123` cross-reference. Name declaration.
- No commented-out code. Git have it.
- `TODO` need subject: `TODO(<subject>): <what owed>`.

`scripts/lean-style` enforce mechanical half, both direction (code rules and comment rules), on
`Stop`. Judgment half — proof narration, consumer note, weak doc — stay reader job.

`STRUCTURE.md` own rule: pure file map, one line per file, zero reference.
`scripts/structure-check` enforce it, own hook, own switch `FUGUE_STRUCTURE_HOOK=off`.

## Context discipline

Context re-billed every turn. Token read at turn 20 of 200 paid 180 more times. What *stays*
cost far more than what a call return once.

- **No whole-file read of big file.** `.lean` over 300 lines: `lean_file_outline` for
  skeleton, then `lean_declaration_file` for one declaration. Raw source needed: `Read` with
  `offset`/`limit`. `Driver/Modules.lean` alone burned 26k tokens over 6 whole-file reads.
  Enforced — `.claude/hooks/lean-reminder.sh` denies unbounded `.lean` reads past threshold.
  Sliced reads pass, and satisfy `Edit`'s read-first requirement (verified).
- **`STRUCTURE.md`, `PLAN.md`, `FINDINGS.md`: slice, never `cat`.** `STRUCTURE.md` carry index
  at top — 360 tokens vs 6.5k whole. Slice pattern live there.
- **`Edit` `old_string` = minimal unique anchor.** Not 40-line surrounding block. `Edit` inputs
  were 51k tokens over 15 sessions — biggest slice of own tool arguments.
- **Plan docs: append, no rewrite.** One plan file cost 9.7k tokens in `Write`+`Edit` churn.
  Same for `.claude/tasklist*.md`.
- **`.mcp.json` empty on purpose.** `gopls` removed — 11 calls in 91 sessions, instruction
  block cost ~450 tokens *every turn*. Re-add for real Go runtime work:
  `{"mcpServers":{"gopls":{"command":"gopls","args":["mcp"]}}}`.
- **Hooks echo own command text into context.** Hook command = file path, never inline shell
  one-liner. Emit `additionalContext` alone; adding `systemMessage` state same rule twice.
- **Deferred MCP tools lose to `Read`.** lean-lsp navigation got 94 calls vs 1389 `.lean`
  `Read`s + 1583 greps across 91 sessions — 3%. Cause: deferred schemas cost a `ToolSearch`
  turn, `Read` cost none. Reminders don't fix that; removing the substitute does.

## Lean conventions

**Moved. `LEAN_STYLE.md` is canonical** — language conventions, proof style, module-system rules,
and the tactic playbook (project's own 15, style calls already settled, Mathlib tactics worth
reaching for). Don't restate rules here; that duplication is what the move removed.

Rules carried from prior art's `lakefile.lean`; raise open question before dropping any.

Enforcement is `scripts/lean-style`, run on `Stop` over working-tree `.lean` files. Mechanical
rules only — the judgment ones stay a reader's job.

## Build & iterate

- `lake build` standard. Prior art's dev-mode CLI wrapper (`fugue.sh`) reasonable model.
- **Every semantics/proof module must be reachable from the executable's imports.** `lake build`
  with no target builds `lean_exe fugue` and nothing else, so a module outside `Fugue.lean`'s import
  closure is never elaborated — and its *stale olean is replayed silently*, meaning `lake build`
  reports success over source that no longer compiles. This bit twice before it was diagnosed. The
  fix is structural, not a longer build command: a pass's root module imports its own proof files
  (`Guarded2Network.lean` imports `Guarded2Network.Lemmas`, which imports `Lemmas/*` and
  `VerifiedCompiler`), so `lake build` checks everything. **A new proof file is only checked once
  something imports it** — wire it into the pass's `Lemmas.lean` as you create it.
- **Consumers import a pass's root module, not its submodules.** `Driver/Pipeline.lean` imports
  `Guarded2Network`, never `Guarded2Network.PlusCal`.
- Suspect a module was skipped? Compare timestamps — an olean older than its source means nothing
  built it, whatever the build said:

  ```bash
  ls -lT .lake/build/lib/lean/Core/GuardedPlusCal/Semantics/Lemmas.olean Core/GuardedPlusCal/Semantics/Lemmas.lean
  ```
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
