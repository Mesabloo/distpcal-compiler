# OPEN_QUESTIONS.md

Open questions and known issues, split out of `PLAN.md`. Same role as `PLAN.md`'s old §9:
ask before resolving any of these unilaterally if they turn out to matter more than
expected. Numbering (`9.x`) kept as-is — `PLAN.md` and other docs cross-reference these as
`§9.x`.

**Resolving one: delete it from this file.** Move the decision into `PLAN.md` as settled
fact (see `INSTRUCTIONS.md`'s "Rule matter most" — decisions land in `PLAN.md` written as
if always the plan, no history, no "earlier draft said"), then remove the corresponding
entry here entirely — don't leave a "resolved" marker or strike-through behind. This file
stays current-state-only, same as `PLAN.md`: it lists what's still open, nothing else.
Leftover subsection numbers (e.g. `9.9` missing) are fine — don't renumber remaining
entries to close the gap.

---

### 9.1 Join Calculus: what happens after emission?
§2/§5.6: committed scope is "emit a syntactically well-formed `.join` file implementing
the thesis's compilation scheme." Open: does this project eventually need (a) an
interpreter for the guarded dialect (closest to "formally verified compiler" in spirit —
much easier to relate an interpreter's semantics to a Lean model than real Go
concurrency), (b) a further lowering to something existing tooling runs (JoCaml-compatible
encoding, with the performance caveat the thesis flags), or (c) nothing at all, treating
the Join Calculus output purely as a verification artifact? Revisit once §5.6 exists.

### 9.2 Known parser gaps
Not blockers, none hit by §8's language subset, but real known gaps in `Parser_/`:
- Incomplete TLA⁺ reserved-word list (`TLAPlus.lean:62`); no binary/octal/hex number
  literals (`TLAPlus.lean:376`); no handling of junk before module start / after module
  end (`TLAPlus.lean:1135`).
- PlusCal `macro`/`procedure`/`define` sections unsupported (`PlusCal.lean:387`) —
  `Core/SurfacePlusCal/Syntax.lean` has no AST nodes for them. None appear in §8's
  subset.
- `parseChannels`/`parseFifos` (`PlusCal.lean`) only accept a single bracket-index group
  (`chan[S]`), unlike `Ref.args : List (String ⊕ List β)` which supports the multi-dimensional
  form (`x[i][j]`) used elsewhere (e.g. `parseRef`) — a narrow grammar gap for any future
  program wanting a multi-dimensional channel/fifo declaration.
- `Expression.choose` (`CHOOSE`) and `LET`/`IN` are lexed (`.choose`/`.let`/`.in` tokens
  exist) but have **no parser rule at all** — worth a real implementation pass before
  trusting any input using either.
- `@type` annotation dialect: only the current (Apalache-style, `Channel({type: Str,
  agent: Address})`) syntax is supported — a pre-Apalache-format dialect
  (`Channel[{type: string, agent: T}]`, square brackets, lowercase generic names) is not.

### 9.3 CLI / UX — two remaining details
Flag surface settled (§2). Two details still open:
- **Join Calculus "flavors"** (e.g. `-t join[jocaml]`, `-t join[jerlang]`) — possible way
  to select between different lowerings/encodings of the guarded-reaction dialect for
  different existing Join Calculus runtimes, ties into §9.1. Flagged as possibly not
  worth the complexity — don't build unless asked.
- **`-p` (Go package name)** — whether this stays its own flag or folds into something
  like `-t go[package=...]`, or is specified another way, still open.
- **`Int` machine-`int`-vs-`math/big` flag name** (mechanism resolved, §2) — likely fits
  the existing `-f<name>` category alongside `-fno-color`, but exact spelling (and
  whether boolean toggle or value-taking) not pinned down.

Also open: whether `-o`/`--output` names a file or a directory — matters more once two
backends have potentially different output shapes (Go may eventually emit more than one
file).

### 9.4 Join Calculus operational semantics — low priority
§5.6 points at where `Core/JoinCalculus/Semantics/` (RCHAM heating/cooling + reaction
rules, thesis Fig. 8.4.2–8.4.3, local and distributed solutions) would go, doesn't ask
for it now — getting `Network2JoinCalculus` to actually compile is the near-term goal.
Formalizing the target language's own operational semantics only starts to matter once
there's appetite to prove something about that pass (a prerequisite for §9.1) — revisit
then.

### 9.5 Multicast compilation is undescribed for both backends
`multicast(x, [y ∈ e1 ↦ e2])` is explicitly part of the v1 subset (§8), yet neither
backend's compilation scheme shows how it's compiled. §5.6's Join Calculus scheme (the
"Atomic blocks" bullet) only shows a single `send(c[α],e)` folded into a reaction body —
no bullet for emitting to a whole filtered set of recipients, unclear whether that means
one atom per recipient (needing some encoding of a bounded loop/comprehension inside a
reaction body, which the target calculus doesn't obviously support) or something else.
§5.7 says `Network2Go/PlusCal.lean` gets "essentially everything right" except lock
inference, doesn't say whether multicast codegen is included in that "everything" or
still needs new work — worth confirming by reading the actual pass.

### 9.6 Runtime value representation in Go: numeric representation is the real open piece
TLA+ `Int`/`Nat` are unbounded, FIFOs are (as far as §8's grammar says) uncapacitated;
Go's integer types and channels are inherently bounded (`int64` wraps on overflow; a Go
`chan` is either unbuffered/synchronous or has fixed capacity — never truly unbounded).
The dispatch mechanism between machine `int` and `math/big` is resolved (§2, §5.7): a
whole-program compiler flag. Exact flag name still open (§9.3).

The channel-capacity side is a real, unverified hypothesis, not a settled non-issue:
because lock-inference (§5.7) already serializes atomic blocks touching shared state, a
`send` blocking on a bounded Go channel shouldn't change *which* transitions are enabled
— at worst it should only slow execution down, not alter behavior or invalidate whatever
the source spec was checked/proved against. Worth confirming once a concrete backend
exists to test against.

Note this "bounded Go channel" reasoning is clearest for a same-process channel realized
as a literal Go `chan` (blocking-vs-capacity is exactly native Go semantics there). Per
§9.7, `send(c, e)` to a *different* process almost certainly isn't a literal shared Go
`chan` at all (can't span OS processes/machines) — it's a network send, whose
"capacity"/blocking is a property of a socket and whatever buffering the runtime library
puts around it. The reasoning above may still hold either way, but was worked out
assuming a literal Go `chan`, re-check once §9.7 pins down what a cross-process
`Channel(τ)` actually compiles to.

**Known, accepted risk:** a block that blocks on a channel op *while holding its
component's lock* freezes every other block sharing that lock — potentially including the
process's own `T_rx` thread — for as long as the send stays blocked. Stays **local to the
one process (agent)** that's stuck; not a cascading, system-wide deadlock, since what
unblocks it is the peer's own (user-written) code eventually processing/receiving the
corresponding message. Real-world failure mode is "one process goes locally unresponsive
until its peer drains the channel," not "the whole distributed system wedges" — a genuine,
accepted consequence of the locking design.

### 9.7 `send(c, e)`'s actual Go compilation scheme is unknown

The thesis resolves the adjacent question of whether `Channel(τ)` needs a general-purpose
Go value representation — it doesn't, since channels "are not first-class citizens in
Distributed PlusCal" (§5.7). That answers "what Go type does a channel value have" (none
— never stored, passed around, or put in a data structure the way an ordinary TLA+ value
is; only appears indexed, `c[α]`, at a `send`/`receive` site). It does **not** answer this
section's actual open question, about wire mechanics, not representation: connection
lifecycle, serialization format, how a channel's identity travels alongside its payload
once `send(c, e)` targets a different process.

§5.7 describes `Network2Go/PlusCal.lean` as "already gets essentially everything right"
except lock inference, separately lists the hand-written `tests/*/{lib,nameserver}`
scaffolding (TCP/UDP address resolution, a name-server process) as directly reusable —
but nowhere does this plan say how these two things connect: what `send(c, e)` concretely
compiles to once `c` is addressed to a *different* process, possibly on a different
machine.

Natural shape, sketched here but **not confirmed against the actual pass or committed
to**: look up the target address (the `α` in `c[α]`, per §5.3's `Channel(τ)` covariance)
via the nameserver client; obtain a network connection to that address (new per message,
or pooled/persistent — unspecified); serialize the channel's identity together with the
payload `e` (the receiver may have several distinct channels, so identity has to travel
with the message); transmit it; on the receiving end, some listener — the Go analogue of
§5.6's Join Calculus `T_rx` reaction — accepts the connection, deserializes, appends the
payload to the *local* `inbox` variable for that channel, which is what `receive` already
reduces to reading from (§5.5). None of connection lifecycle, wire format/serialization,
or how a channel's identity is encoded on the wire is decided.

This also means `Channel(τ)`'s Go runtime representation is genuinely two different
things depending on which side of a `send` you're standing on: for the *receiver*, a
channel is (or feeds) a real local `inbox` sequence — the kind of thing a literal Go
`chan`/queue can realize, matching §5.3's "channels are encoded as `Seq(τ)`" framing. For
the *sender*, addressing a remote process's channel can't be a shared Go `chan` value at
all (cannot cross OS processes, let alone machines) — has to go through the
nameserver-plus-network path above instead. §9.6's Go-channel-capacity discussion should
be re-read with this split in mind — its reasoning was worked out assuming a literal Go
`chan`, at best half the picture.

### 9.8 A "floating annotation" warning is blocked by the parser combinator library's backtracking

A warning for an annotation-shaped comment with *no* designated consuming site anywhere
nearby (as opposed to a real annotation attached to the *wrong specific role* at a real
site, which stays in scope, §5.1) is blocked by a genuine limitation in how
`Parser_/Common.lean`'s `first` — and the vendored `fgdorais/Parser` library's
`first`/`orElse` it's built on — actually backtrack.

**Mechanism:** `ParserT ε σ τ m α := σ → m (Parser.Result ε σ α)`. `orElse`/`first`'s
failure branch only ever resets `Stream.Position` (an explicit field of `ParserT`'s own
type) — never anything inside the base monad `m`. `first [parseAssume, parseConstants,
parseVariables, parseOperator, ...]` (`parseDeclaration`, `Parser_/TLAPlus.lean`) tries
`parseConstants`/`parseVariables` before reaching the correct `parseOperator`
alternative; both use `lexeme (pure ()) *> token .constants`/`(.variable <|>
.variables)` — generically skip past (`lexeme`/`ws`) whatever comment sits there *before*
checking their own keyword and failing. Any `m`-side-effect performed during that skip
(e.g. an accumulated warning) survives even though the *stream position* correctly rolls
back for the next alternative to retry — `first`'s reset only touches `σ`, not `m`. This
generic `lexeme (pure ())`-before-keyword skip is load-bearing, not an oversight — it's
what allows comments to legally appear between/before declarations at all without being
mistaken for consumed annotations; removing it isn't an option.

Fixing this properly means giving `first`/`orElse` real "commit" semantics (a failure
after any input has been consumed propagates immediately rather than retrying sibling
alternatives) — a change to the core parsing combinators, not a narrow fix, risks
breaking other grammar productions relying on retry-after-partial-consumption. Not
attempted now — the annotation-placement check proceeds with only the
structural-role-mismatch half (a real annotation captured at a real site but attached to
the wrong role there — e.g. `@parameter` on a quantifier binder — runs on the
already-successfully-parsed AST, has none of this problem, §5.1). The "nothing consumes
this at all" half stays out of scope until `first`/`orElse`'s backtracking semantics are
revisited.

### 9.10 `LAMBDA` — designed, not implemented

Thesis has typing rules for `LAMBDA` (Fig. 3.1.4), but neither `SurfaceTLAPlus.Expression`
nor `CoreTLAPlus.Expression` has a constructor for it, no `LAMBDA` lexer token. Stays out
of scope for now — `Elaborator/Expressions.lean` ships with no `LAMBDA` case (no AST node
to match on anyway); revisit as its own separately-scoped addition if a program needs it
— implementing means touching `Parser_/TLAPlus.lean`, `Core/SurfaceTLAPlus/Syntax.lean`,
`Core/CoreTLAPlus/Syntax.lean`, `Desugarer/TLAPlus.lean`, not just the checker.

Design, preserved for whenever picked up:
- **Checking-only without an annotation** (matches the thesis, Fig. 3.1.4) — `Γ, x1:τ1,
  ..., xn:τn ⊢ e ⇓ τ ⟹ Γ ⊢ LAMBDA x1,...,xn : e ⇓ (τ1,...,τn)⇒τ`, requiring the whole
  `LAMBDA`'s expected type already known.
- **Gains a synthesis form once every binder carries a `@type` annotation** — mirroring
  unbounded quantification's own trick: `(LAMBDA (* @type: Int; *) x : x + 2)(3)` should
  synthesize, even though the thesis's own unannotated example (p. 10) still can't
  (rewritable via `LET`-`IN` instead — except this project's AST has no `LET`-`IN` node
  either, so that specific workaround doesn't apply here regardless).
- **New AST work needed:** a `.lambda (binders : List (String × α)) (body : Expression α)`
  constructor on both `SurfaceTLAPlus.Expression`/`CoreTLAPlus.Expression`, a per-binder
  annotation slot so `tryParseAnnotations` can attach `@type` per binder (matching
  `parseQuantifierBound`'s existing pattern), a new lexer token, a new parser rule, a
  pass-through desugarer case, both the checking and (conditional) synthesis rules in
  `Elaborator/Expressions.lean`.

`Operator`-vs-`Operator` structural subtyping (`Elaborator/Subtyping.lean`, Fig. 3.1.8)
already only ever produces an identity coercion, precisely because there's no
`LAMBDA`-equivalent way to eta-expand into a new first-class operator value — a concrete
limitation already surfaced once, not just hypothetical.

### 9.11 Most temporal/action operators aren't parsed yet — `WF_`/`SF_` specifically need a lexer change

`UNCHANGED`/`ENABLED`/prime (`'`)/`~>`/`-+>`/`[]`/`<>` already have real surface syntax
(`Core/SurfaceTLAPlus/Syntax.lean`'s `Prefix`/`Infix`/`PostfixOperator` enums) and desugar
to plain `opCall`s onto builtin `var`s (`Desugarer/TLAPlus.lean`), so `Elaborator/
Expressions.lean`'s generic `OPERATOR CALL` rule already covers them with no dedicated
case. **But most temporal/action operators are not actually parsed yet.** Weak/strong
fairness (`WF_e(A)`/`SF_e(A)`, thesis Fig. 3.1.5) are the concrete example, a genuinely
non-trivial lexing problem, not just an unwritten parser rule: `WF_e` needs to lex as
**two** tokens (a fixed `WF_` keyword, then the identifier `e`), but ordinary
maximal-munch identifier lexing would otherwise swallow `WF_e` whole as one identifier
token.

Idea recorded, not implemented: modify the lexer's keyword checker so that, given an
identifier-shaped token starting with `WF_` or `SF_`, if leftover characters after that
prefix don't themselves start with `_` or a digit (still looks like a valid identifier
start), split into the `WF_`/`SF_` keyword token followed by a separate identifier token
for the remainder, rather than one combined identifier token.

`^+`/`^*`/`^#` (postfix action-closure operators, `Core/SurfaceTLAPlus/Syntax.lean`'s
`PostfixOperator`) additionally have **no documented typing rule anywhere** — not in the
thesis, not standard TLA⁺ as far as traced. Left unbound in `builtinContext` for now —
referencing one fails at `unboundVariable`, no regression. Their canonical names are
still included in `WellFormedness/Restrictions.lean`'s check-3 name list for
forward-compatibility, currently inert.

Future work, not started — revisit whenever a program actually needs `WF_`/`SF_`,
`^+`/`^*`/`^#`, or the other still-unparsed temporal/action operators checked.

### 9.12 Three regression fixtures parked as `skip_*`, pending parser/desugarer fixes
`tests/regression/run.sh`'s own `skip_*` convention (a file with that prefix is skipped
and reported yellow, never run, excluded from the pass/fail tally) has three fixtures
parked pending fixes unrelated to any currently-landed work:
- `skip_function_definition_multi_arg_tuple_domain.tla` — parser rejects
  `f[x \in S, y \in T] == ...`'s multi-arg function-literal domain syntax
  (`unexpected identifier f`).
- `skip_unbounded_choose_with_expected_type.tla` — parser rejects a bare
  `CHOOSE m : m = m` used as a `with`/variable initializer (`unexpected keyword
  'CHOOSE'`) — same root cause as §9.2's `CHOOSE`-parsing gap.
- `skip_function_literal_cartesian_product_binder.tla` — `\X` (Cartesian product) is
  either not desugared to its canonical operator name, or that name is missing from
  `builtinContext`/`Naturals`'s declarations (`Unbound variable` `\X`).

First two look like `Parser_/TLAPlus.lean` gaps, third looks like a
`Desugarer/TLAPlus.lean`/`Driver/Builtins.lean` gap — neither confirmed by tracing the
code. Fix each at the root (parser/desugarer/builtins), rename back to `accept_*`, re-run
the full suite once done — don't just patch the fixture unless it turns out to encode an
unsupported/wrong construct (check against §8's language subset first).

### 9.13 Three well-formedness checks (well, two and a half) are currently unreachable
The *rule* is right in each case, only the parser/type-checker can't produce the input
that would exercise it yet:
- **Check 2(b)'s `nonEmptyLocalChannels`** (a process's own `localState.channels`/
  `.fifos` must be empty): `Parser_/PlusCal.lean`'s `parseProcess` hardcodes
  `channels := []`/`fifos := []` when building a process's `localState` — never even
  attempts to parse `channels`/`fifos` syntax at process level, only `variables`. No
  fixture can exercise the reject side; stays defense-in-depth only.
- **Check 3's `unboundedQuantifier`**: an unbounded `\A x : P`/`\E x : P` is parseable
  but its bound variable's type can never reach an annotation under the current grammar
  (`parseQuantifier`'s unbounded branch is bare `parseIdentifier`, no
  `tryParseAnnotations` call) — always fails at `TCError.expectedTypeAnnotation` before
  well-formedness ever runs, *except* unbounded `CHOOSE x : P` in a checking position
  (`Elaborator/Expressions.lean:146`'s `[Unbounded choice]` rule does succeed there,
  ignoring any annotation and using the expected type instead) — but `CHOOSE` has no
  parser rule constructing it at all (only ever a lexer token, §9.2/§9.12's already-filed
  gap, same root cause). So `unboundedQuantifier` has no reachable trigger today, on
  either quantifier form.
- **Check 1's `channelInExpression`, specifically via `receive`'s destination `r`** (not
  the check as a whole — a direct `assert ch = ch;` still exercises it directly). The
  only way to get `r` itself typed as Channel-shaped past type-checking at all was a
  channel-of-channels source (`Channel(Channel(τ))`, needed for `Channel`'s
  reflexivity-only subtyping to accept the `receive`), which `sendable` (§5.3) now
  rejects outright, at declaration time, before a `receive` statement referencing it is
  ever reached.

Not a bug in any of these three checks' own logic — all exercised and confirmed correct
via direct calls, just not through a real `.tla` fixture end-to-end. Revisit once: (a) the
parser gains process-level `channels`/`fifos` parsing (probably never worth doing, given
check 2(b) is explicitly defense-in-depth and the restriction is already unconditional),
(b) §9.12's `CHOOSE`-parsing gap is fixed (would also make unbounded `CHOOSE` reachable)
or unbounded `\A`/`\E` gains annotation support (a bigger grammar change), or (c) some
other route to a channel-shaped `receive` destination `r` is found that doesn't require an
unsendable channel-of-channels declaration (none currently known — `Channel`'s
reflexivity-only subtyping and the lack of any other channel-shaped-type constructor make
this look structurally unlikely, not proven impossible).

### 9.14 Should intrinsic operators get dedicated AST constructors instead of `opCall`?
Every builtin operator, intrinsic or stdlib, is represented uniformly as `.opCall (.var
name _ origin) args` — no dedicated `Expression` constructor per operator. Keeps the type
checker's op-call rule uniform (one generic rule plus a `Γ`/`builtinContext` lookup, not
one typing rule per builtin), but pushes every downstream pass needing to special-case a
builtin into re-deriving its own string/`Origin` match against the same representation —
`WellFormedness/Restrictions.lean`'s `reservedTemporalActionNames` today,
`Typed2Computable`'s own computability classification, and (per `Driver/Builtins.lean`'s
own module doc) both backends unconditionally, since stdlib operators "get replaced by
backend-native implementations at code-generation time regardless of what their
'definition' says." The shared recognizer table (`Core/TypedTLAPlus/Builtins.lean`, §2)
is the near-term fix, decided and in place — open question is whether that's enough
long-term, or worth going further.

Scope of the question: intrinsics only — `builtinContext`'s own ~14 genuinely
`EXTENDS`-independent entries (`=`, `/=`, `/\`, `\/`, `=>`, `<=>`, `\neg`, `\in`,
`\notin`, `\subseteq`, `\cup`, `\cap`, `\`, `DOMAIN`, plus the temporal ones tracked
separately in §9.11) — **not** operators declared via vendored stdlib modules
(`Naturals`/`Sequences`/`Bags`/`FiniteSets`/etc., §5.3's `builtinModules` table). The two
groups differ in exactly the way that matters: intrinsics are a small, closed, permanent
set baked into every module regardless of `EXTENDS`, while stdlib operators are
open-ended declarations in an ordinary (if hardcoded) `Module` — giving *those* dedicated
constructors would mean a constructor per `Len`/`Head`/`+`/…, undermining the point of
representing them as ordinary declarations (§5.3) rather than special-cased primitives.

### 9.15 `Typed2Computable`'s finite-sets assumption doesn't cover an infinite set used as a quantifier/set-builder domain
`Nat`/`Int` (real, reachable builtin infinite sets — `STRING`, TLA+'s other classic
infinite base set, isn't parseable by this compiler at all yet, moot for now) can
currently be used as a bare `forall`/`exists`/`choose` domain, or a set-builder
(`collect`/`map'`) domain, with nothing rejecting it — confirmed empirically: `\A x \in
Nat : x >= 0` inside a PlusCal statement translates cleanly through `Typed2Computable`
today. Real gap given §5.7's own compilation scheme (§7.2.1.2): `\A x \in S : P`/`\E x
\in S : P` compile to "a search over `S`", `{x \in S : P}`/`{e : x \in S}` copy `S`'s
underlying slice, `CHOOSE x \in S : P` filters then takes a minimum over `S` — all three
genuinely enumerate `S` at runtime, so an infinite `S` there doesn't just look
inelegant, it doesn't terminate.

**Settled, not part of this gap:** a function literal's domain (`fn`, `[x \in S |-> e]`)
being infinite is not a problem and needs no restriction — per §5.7, functions compile to
lazy maps (avoiding eagerly computing the whole graph at declaration time), so `[x \in Nat
|-> x * x]` is fine and should stay unrestricted; disallowing it would be an unnecessary
regression relative to real TLA+ expressiveness. `Typed2Computable`'s current behavior (no
restriction on `fn`'s domain) is already correct here.

**Genuinely open:** whether/how to reject an infinite domain specifically at `forall`/
`exists`/`choose`/`collect`/`map'` (and PlusCal's own `with x \in dom`, same enumeration
concern), and where such a check should live (`Typed2Computable`, matching
`fnSet`/`recordSet`'s existing precedent, vs. deferred to `Network2Go`/§5.7 itself, where
the lazy-map/eager-slice distinction is actually implemented). Two options surfaced,
neither committed to:
- **Narrow, syntactic check**: reject a *direct* bare reference to a known-infinite
  builtin set (`Nat`/`Int`, recognized the same way `Typed2Computable`'s own
  builtin-drop logic already recognizes them) at exactly these positions — catches the
  obvious case, not a derived-but-still-infinite one (`Nat \ {0}`, `Nat \cup {1}`, an
  operator that returns `Nat` under another name, …).
- **Track possible-infiniteness with an invariant**: most infinite sets actually
  encountered (`Nat`, `STRING`, `[Nat -> Nat]`) denote "the universe of all values of some
  type" — a property that might be summarizable/tracked rather than requiring general
  finiteness inference. Explicitly floated as possibly not worth it, not designed further.

Revisit before `Network2Go`/§5.7 needs a real answer for how `forall`/`exists`/`choose`/
set-builder actually compile — that's the point this stops being deferrable. Revisit once
the shared recognizer table's shape (§9.14) is settled either way too, since that
determines how cheap a fix here becomes.

### 9.16 `EXTENDS` resolution reports a false "ambiguous module" when `-I` names the
importing module's own directory

`Driver/Modules.lean`'s `locate` (§5.3) builds its candidate list by walking
`containingDir.toList ++ (-I)'s searchPath`, appending a `(String × Candidate)` entry per
directory that has a matching `<name>.tla` — no dedup by resolved path. `-I dir` where
`dir` is (or resolves to) the same directory the importing module already lives in
produces two list entries pointing at the literal same file, and `locate` reports that as
`ambiguousModule`, listing the identical path twice. Confirmed by hand: `fugue -I foo
foo/Main.tla` (`Main.tla EXTENDS Dep`, `Dep.tla` also in `foo`) fails this way; dropping
`-I` or pointing it at a different directory than `foo` both work.

**Open:** how to dedup — compare `System.FilePath` values directly (fails if
`containingDir` and a `-I` entry spell the same directory differently, e.g. one relative
one absolute), or resolve each candidate to a canonical/real path first (needs an
`IO`-level realpath call, not yet used anywhere in this codebase) and dedup on that.
Whichever, `locate`'s final `match found with | [] | [_] | multiple` needs the dedup
applied before that match, not after — a false ambiguity is user-visible as a hard compile
error, not a warning.
