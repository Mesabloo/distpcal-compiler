# Diagnostic page style

Template every `docs/diagnostics/<CODE>.md` page follows. One page per registered diagnostic
code (`Common/Diagnostics/Registry.lean`). `fugue explain <CODE>` prints the registry line
(code, summary, stage, `-Wno-` name) and then this file verbatim.

Canonical: this file, not memory of it. Re-read before writing a page.

## Filename

`<CODE>.md`, code in canonical form: letter, four digits — `E0026.md`, `W0006.md`. No other
name is served. One file per code, including retired and placeholder codes.

## Register

Normal prose. This is user-facing output — the reader has a `.tla` file and an error, not the
compiler source.

**Describe the diagnostic, not the compiler.** The page answers two questions: what does this code
mean, and how do I fix my program. Nothing else belongs in it — not which pass raises it, not
whether some other check fires first, not how the passes are layered, not why the code is easy or
hard to reach, not what a future change would make possible. If a page cannot be written without
narrating implementation state, the page is being written wrong. This is `INSTRUCTIONS.md`
§Comments applied to user-facing text: read as if the current behaviour is the only behaviour
there ever was.

- No internal names: no Lean module, file, `def`, pass-internal type, or `linter.fugue.*`. Name
  the TLA+/PlusCal construct, the CLI flag, the operator. "the type checker", "resolution",
  "the Go backend" are fine; `Elaborator/Subtyping.lean` is not.
- No `PLAN.md` / `OPEN_QUESTIONS.md` / `§N` / `.claude/` references.
- No history, no roadmap: none of "was", "now", "still", "yet", "currently", "no longer", "does
  not yet", "will", "once X is added", "for now". Present tense, describing the rule as it stands.
- No thesis/paper citation. Keep the content, drop the number and the attribution.
- American spelling, Oxford comma, sentence case in headings.
- Wording tracks the *meaning*, not the exact message string. The message is free to change; the
  page must not need editing when it does.
- Must not contradict the registry `summary` for the code.

## Output constraints

`fugue explain` prints the raw markdown to a terminal — no renderer. Keep markup light:

- `#` title, `##` section headings.
- Fenced code blocks, language tag `tla`.
- `-` bullet lists, one level only.
- Inline `` `code` ``, `*emphasis*`, `**strong**` used sparingly.
- No tables, images, HTML, blockquotes, or nested lists.
- Wrap prose near 100 columns.

## Template

```
# <CODE>: <short noun phrase>

<Quick explanation.>

## Why it fires

```tla
<Quick example.>
```

<One or two sentences: what in the example trips the check.>

## How to fix it

- <Fix, most common cause first.>
- <...>

## See also

- `<CODE>` — <how it differs from this one.>
```

### Title

`# <CODE>: <name>` — a short lowercase noun phrase naming the diagnostic (`type mismatch`,
`unsafe cast`, `algorithm in an EXTENDS-ed module`). Not a sentence, not the fix. It repeats the
line `fugue explain` prints just above; that is fine — the page is also read on its own.

### Quick explanation

One to three short paragraphs, no heading. First sentence: what is wrong, in the reader's terms.
Then, if it helps: what the compiler was doing when it noticed, what rule this enforces, why the
rule exists. Stop there — the fix has its own section.

### Quick example

The smallest `tla` snippet that triggers the diagnostic. Either a **complete, compilable**
`---- MODULE … ----` / `====` (with `(*--algorithm … *)` when the code needs one), or a short
**fragment** the surrounding prose frames as illustrative. Do not elide with `{ ... }` inside a
snippet you present as complete — `(*--algorithm X { ... }*)` does not parse. Give the algorithm a
real one-statement body instead. Follow the block with one or two sentences pointing at the exact
token or shape at fault.

**Compile every complete example.** Run it through `fugue` and confirm it reports exactly this
code — not a parse error on the way there, not a different check firing first. Watch for:

- a process id must usually be a `CONSTANT` typed `Address` (`process (P = PID)`), not a literal —
  `process (P = 0)` fails with `E0026` before your check runs;
- arithmetic needs `EXTENDS Naturals`;
- a `fifos`/`channels` entry needs a `@type: Channel(…)`;
- PlusCal bodies are C-syntax (`{ }`).

The `tests/regression/` fixtures are the reference for shapes that compile; when a code has an
`Accept*`/`Reject*` fixture, base the example on it. When you cannot produce a compilable snippet
that lands on the code, drop the `tla` block — describe the meaning and the fix in prose and stop
there. Do not explain in the page why the code is hard to reach; that is implementation state, and
the reader is holding a program, not the compiler.

### How to fix it

Imperative bullets, ordered by how often each is the real cause. Cover:

- the ordinary fix (correct the program);
- when the diagnostic is advisory — for a warning, the `-Wno-<name>` that silences it, and when
  silencing is legitimate;
- any construct that does the same job without tripping the check.

### See also

Bullets linking *other diagnostic codes* only — nearby checks a reader might have meant, the
error/warning on the opposite side of the same rule, the next check in the same area. Each bullet:
`` `<CODE>` `` then an em dash then one clause on how it differs. Omit the section if there is
nothing genuine to point at; do not pad it.

## Special cases

- **Internal-invariant codes** (a compiler bug, not a program error — e.g. `E0056`, `E0057`,
  `E0058`, `E0060`): "Why it fires" describes the class of broken invariant, not a reproducer —
  there should be no way to trigger it from a well-formed program. "How to fix it" is a single
  bullet: report it, with the specification and the message text. No `tla` example. The pass name
  in the title (matching the registry summary) is the one place a pass may be named — it aids the
  bug report.
- **Catch-all codes** (`E0024`, `W0004`): one paragraph — the check that fired has no dedicated
  code of its own, the message text carries the detail, report the case if it warrants a narrower
  code. No example, no fix list.
- **Retired codes**: one paragraph — retired, what it used to mean, what replaced it (by code) if
  anything. Kept so old build logs stay meaningful.
- **Unallocated numbers** (e.g. `E0020`): no page. `fugue explain` reports it as unregistered.
