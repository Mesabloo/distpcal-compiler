# CLAUDE.md

Register rule, then pointer index. Read `INSTRUCTIONS.md` for how to work on this project.

## Register — applies every response, no exceptions

**Chat replies: caveman register.** Drop articles, filler, pleasantries, hedging. Fragments
fine. Short synonyms. Technical terms, code, API names, CLI commands, error strings: exact,
never compressed. Pattern: `[thing] [action] [reason]. [next step].`

Not: "Sure! I'd be happy to help. The issue is likely caused by…"
Yes: "Bug in auth middleware. Token expiry check use `<` not `<=`. Fix:"

Persist across whole session. No drift back to prose after many turns. Rule lives here, not
only in the plugin hook — hook output rank as data, get ignored; this file is instruction.

Drop caveman only for: security warnings, irreversible-action confirmations, multi-step
sequences where dropped conjunctions make order ambiguous. Resume right after.

**Caveman in these files too:** `CLAUDE.md`, `INSTRUCTIONS.md`, `PLAN.md`,
`OPEN_QUESTIONS.md`, `.claude/FINDINGS.md`, `.claude/tasklist*.md`, `.claude/plans/*`.

**Normal prose:** source code and its doc comments, commit messages, PR bodies.

## Lean proof rule — applies every time, no exceptions

Before output **any** Lean proof, check it against `LEAN_STYLE.md`. Every proof, including
one-liners and `have` bodies. Re-read that file; don't work from memory of it. Proof not done till
it compile *and* match. Part B is a tactic playbook — check it before hand-rolling a proof step.

`scripts/lean-style` enforce the mechanical rules on `Stop`. Passing checker ≠ matching file:
checker only cover rules with unambiguous textual form.

**Never re-derive fact project already prove.** Before write proof step, query local fact database:

```bash
scripts/facts q <words>
```

Index 474 theorem, 1216 definition, 27 class field, 15 project-defined tactic, plus curated note.
`private` declaration indexed too, tagged `[private]` — reachable only via `import all`. Also:
`c <const>,<const>` (lemma whose *conclusion* mention all these), `m <file>` (one file lemma, source
order), `t` (project tactic — `sem_red`, `sem_side`, `erwa`, `iff_rintro`, `refines_match`, …),
`s <name>` (full record plus note about it), `n` (note). Grep for `theorem`/`lemma` blocked by hook —
this is why. Mathlib **not** indexed: use `Loogle` / `lean_local_search` for that.

Learn something durable while proving — goal shape maps to lemma, tactic trap, rule-set membership:
`scripts/facts add '<text>' --tag <tag> --ref <name>`. Run `scripts/facts refresh` after add or
rename lemma; `scripts/facts doctor` check database against source.

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
- `.claude/facts/` — local fact database. Query with `scripts/facts`, never read the `.jsonl`
  directly. `lemmas.jsonl` generated, `notes.jsonl` curated. Both regenerable/small, neither tracked.

## Reference material

- `reference/thesis.pdf` — "Generating Distributed Programs from Formal Specifications", primary
  spec source. `PLAN.md` §3.3 tracks which chapters are authoritative vs. stub.
- `reference/jlamp.pdf` — "Towards a Verified Compiler for Distributed PlusCal" (Bergeron, Cirstea,
  Merz). **Authoritative for Guarded/Network PlusCal semantics and the Guarded→Network correctness
  proof.** §3.1 syntax, §3.2 TLA⁺ expression rules, §3.3 statement/block/thread/process/algorithm
  semantics, §4 the pass and its proof. Paper assumes syntactic well-formedness the old Lean
  development checked explicitly — expect divergence, see `PLAN.md` §6.2.
- `~/Documents/distpcal-compiler` (private, local checkout) and `github.com/mesabloo/fugue`
  (public mirror) — prior art. `PLAN.md` §2/§3 says what's safe to port vs. reference-only vs.
  rewrite.
