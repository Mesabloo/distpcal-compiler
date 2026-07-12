# CLAUDE.md

Pointer index only — no rules, no narrative here. Read `INSTRUCTIONS.md` for how to work
on this project.

## Files to check before work

- `INSTRUCTIONS.md` — working rules, conventions, check-in-first list. Read this before
  anything else.
- `PLAN.md` — architecture, pipeline stage-by-stage, decisions made, open questions. Check
  before any design call.
- `STRUCTURE.md` — directory-by-directory map of repo. Use instead of `ls`/`find`-ing
  around. Keep in sync when files move.
- `.claude/plans/` — holds current in-flight plan document(s) alongside `PLAN.md`, one or
  more per active effort. Names in there rotate per session, so ask owner which file (if
  any) currently active rather than assume a filename.
- `.claude/tasklist.md` — task list for current work, if present. May not exist, and even
  if present may be stale — confirm with owner before trusting it, especially if owner
  says to disregard it.
- `.claude/FINDINGS.md` — implementation findings log (bugs hit/fixed, debugging trails,
  dead ends), if present. Separate from `PLAN.md` on purpose — see `INSTRUCTIONS.md`.

## Reference material

- `reference/thesis.pdf` — "Generating Distributed Programs from Formal Specifications,"
  primary spec source. `PLAN.md` tracks which thesis chapters/sections are authoritative
  vs. stub vs. superseded — check there before treating any section as settled.
- `~/Documents/distpcal-compiler` (private, local checkout, several branches) and
  `github.com/mesabloo/fugue` (public mirror) — prior-art codebases. `PLAN.md` says what's
  safe to port wholesale vs. reference-only vs. rewrite-from-scratch.
