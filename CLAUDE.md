# CLAUDE.md

Pointer index only. Read `INSTRUCTIONS.md` for how to work on this project.

## Files to check before work

- `INSTRUCTIONS.md` — working rules, conventions, check-in-first list. Read first.
- `PLAN.md` — architecture, pipeline stage-by-stage, decisions. Check before any design call.
- `OPEN_QUESTIONS.md` — open questions/known issues, numbered `9.x` and cross-referenced from
  `PLAN.md` as `§9.x`. Check before treating an ambiguity as unlisted.
- `STRUCTURE.md` — directory map. Use instead of `ls`/`find`. Keep in sync when files move.
- `.claude/plans/` — in-flight plan documents, one or more per active effort. Names rotate per
  session — ask owner which is current rather than assume a filename.
- `.claude/tasklist*.md` — task lists for current work. May be stale; confirm with owner.
- `.claude/FINDINGS.md` — implementation findings log (bugs hit/fixed, debugging trails, dead
  ends). Separate from `PLAN.md` on purpose.

## Reference material

- `reference/thesis.pdf` — "Generating Distributed Programs from Formal Specifications", primary
  spec source. `PLAN.md` §3.3 tracks which chapters are authoritative vs. stub.
- `~/Documents/distpcal-compiler` (private, local checkout) and `github.com/mesabloo/fugue`
  (public mirror) — prior art. `PLAN.md` §2/§3 says what's safe to port vs. reference-only vs.
  rewrite.
