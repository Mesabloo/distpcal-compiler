# OPEN_QUESTIONS.md

Open questions and known issues. Ask before resolving any unilaterally. `PLAN.md` and other
docs cross-reference these as `§9.x`.

**Resolving one: delete it from this file** and write the decision into `PLAN.md` as settled
fact. No "resolved" markers, no strike-throughs. Gaps in the numbering are fine — don't
renumber.

---

### 9.1 Join Calculus: what happens after emission?
Committed scope (§2/§5.6) is "emit a syntactically well-formed `.join` file implementing the
thesis's compilation scheme." Open: (a) an interpreter for the guarded dialect (closest to
"formally verified compiler" in spirit — far easier to relate to a Lean model than real Go
concurrency), (b) a further lowering to something existing tooling runs (JoCaml-compatible
encoding, with the performance caveat the thesis flags), or (c) nothing, treating the output
purely as a verification artifact. Revisit once §5.6 exists.

### 9.2 Known parser gaps
Not blockers, none hit by §8's subset:
- Incomplete TLA⁺ reserved-word list (`TLAPlus.lean:62`); no binary/octal/hex number literals
  (`TLAPlus.lean:376`); no handling of junk before/after the module (`TLAPlus.lean:1135`).
- PlusCal `macro`/`procedure`/`define` unsupported (`PlusCal.lean:387`) —
  `Core/SurfacePlusCal/Syntax.lean` has no AST nodes for them.
- `parseChannels`/`parseFifos` accept only a single bracket-index group (`chan[S]`), unlike
  `Ref.args : List (String ⊕ List β)` which supports `x[i][j]` — blocks multi-dimensional
  channel/fifo declarations.
- `CHOOSE` and `LET`/`IN` are lexed (`.choose`/`.let`/`.in` tokens exist) but have **no parser
  rule at all**.
- `@type` supports only the Apalache-style syntax (`Channel({type: Str, agent: Address})`); the
  pre-Apalache dialect (`Channel[{type: string, agent: T}]`) is not.

### 9.3 CLI / UX — remaining details
Flag surface settled (§2), including `-X<name>`, which currently has **no members**. Open:
- **Join Calculus "flavors"** (`-t join[jocaml]`, `-t join[jerlang]`) — selecting between
  lowerings for different Join Calculus runtimes; ties into §9.1. Possibly not worth the
  complexity — don't build unless asked.
- **`-p` (Go package name)** — own flag, folded into `-t go[package=...]`, or something else.
- Whether `-o`/`--output` names a file or a directory — matters once Go may emit more than one
  file. Revisit once `Network2Go`'s output shape is concrete (phase 11 item 7).

### 9.4 Join Calculus operational semantics — low priority
`Core/JoinCalculus/Semantics/` (RCHAM heating/cooling + reaction rules, thesis Fig.
8.4.2–8.4.3, local and distributed) isn't wanted now — getting `Network2JoinCalculus` to
compile is the near-term goal. Only matters once there's appetite to prove something about
that pass (prerequisite for §9.1).

### 9.5 Multicast compilation is undescribed for both backends
`multicast(x, [y ∈ e1 ↦ e2])` is in the v1 subset (§8), yet neither backend's scheme shows how
it compiles. §5.6's Join Calculus scheme only shows a single `send(c[α],e)` folded into a
reaction body — unclear whether emitting to a filtered set means one atom per recipient (which
needs a bounded loop/comprehension inside a reaction body, not obviously supported by the
target calculus) or something else.

Thesis §7.2.3.1 omits multicast from the Go statement-compilation rules, saying only in prose
that it's "a simple 'iterated send'" — no loop construct, no compiled Go. Needs real design
(which set-comprehension form, sequential vs. concurrent sends) before `Network2Go` tasklist
item 3/6 can implement it.

### 9.6 Runtime value representation in Go: channel capacity
TLA+ `Int`/`Nat` are unbounded and FIFOs uncapacitated; Go's types and channels are bounded.
The numeric side is resolved (§2, §5.7): arbitrary precision by default, machine integers
behind the `fugue_machint` build tag, no Fugue-level flag.

The channel-capacity side is an unverified hypothesis: because lock inference (§5.7) already
serializes atomic blocks touching shared state, a `send` blocking on a bounded Go channel
shouldn't change *which* transitions are enabled — at worst it slows execution. Worth
confirming against a concrete backend. Caveat: this reasoning assumes a literal Go `chan`, so
it covers a same-process channel cleanly. Per §9.7 a cross-process `send` isn't a Go `chan` at
all — its blocking is a property of a socket plus runtime buffering. Re-check once §9.7 pins
down what a cross-process `Channel(τ)` compiles to.

**Known, accepted risk:** a block that blocks on a channel op *while holding its component's
lock* freezes every other block sharing that lock — potentially including the process's own
`T_rx` thread. Stays local to that one process; what unblocks it is the peer's own code
eventually receiving. Failure mode is "one process goes locally unresponsive," not a
system-wide deadlock.

### 9.7 `send(c, e)`'s actual Go compilation scheme is unknown
`Channel(τ)` needs no general-purpose Go value representation, since channels "are not
first-class citizens in Distributed PlusCal" (§5.7) — never stored, passed, or placed in a data
structure; only ever indexed (`c[α]`) at a `send`/`receive` site. That answers representation,
not wire mechanics: connection lifecycle, serialization format, how a channel's identity travels
with its payload once `send(c, e)` targets a different process.

§5.7 calls `Network2Go/PlusCal.lean` "already gets essentially everything right" except lock
inference, and separately lists the hand-written `tests/*/{lib,nameserver}` scaffolding (TCP/UDP
address resolution, name-server process) as reusable — nothing says how the two connect.

Natural shape, **not confirmed against the pass or committed to**: look up the target address
(the `α` in `c[α]`, per §5.3's `Channel(τ)` covariance) via the nameserver client; obtain a
connection (new per message, or pooled — unspecified); serialize the channel's identity together
with the payload (the receiver may have several channels, so identity must travel with the
message); transmit; on the receiving end a listener — the Go analogue of §5.6's `T_rx` reaction
— accepts, deserializes, appends the payload to the local `inbox` for that channel, which is
what `receive` reduces to reading (§5.5).

Consequence: `Channel(τ)`'s Go representation is two different things per side. Receiver: a
real local `inbox` sequence, realizable as a Go `chan`/queue, matching §5.3's "channels are
encoded as `Seq(τ)`". Sender: addressing a remote process can't be a shared Go `chan` at all,
so it goes through the nameserver-plus-network path.

Thesis pins the generated-code API surface on both sides, but not the internals:
- §7.2.3.1: `send(c[e1], e2)` compiles to `net.c[e1].Send(e2)`, `send(c, e2)` to
  `net.c.Send(e2)` — `Network`'s fields are per-channel, each with an indexable `.Send`. What
  `.Send` does internally is unspecified.
- §7.2.3.2: each compiled process is `func p(net Network, mailbox Receiver[τ], self Address)
  (chan struct{})` — `mailbox` (`Receiver[T]`, blocking `Recv() (T, bool)`) is
  **caller-supplied**, not constructed by generated code. So the generated code's obligation is
  just "accept something implementing `Receiver[τ]`"; how a real implementation accepts
  connections, deserializes, and demultiplexes by channel identity stays outside the compiler.

### 9.8 "Floating annotation" warning blocked by combinator backtracking
A warning for an annotation-shaped comment with *no* consuming site nearby (as opposed to a real
annotation attached to the wrong role at a real site, which stays in scope, §5.1) is blocked by
how `Parser_/Common.lean`'s `first` — and `fgdorais/Parser`'s `first`/`orElse` beneath it —
backtrack.

**Mechanism:** `ParserT ε σ τ m α := σ → m (Parser.Result ε σ α)`. The failure branch resets only
`Stream.Position`, never anything inside the base monad `m`. `first [parseAssume, parseConstants,
parseVariables, parseOperator, ...]` (`parseDeclaration`) tries `parseConstants`/`parseVariables`
before the correct `parseOperator`; both use `lexeme (pure ()) *> token .constants`/`(.variable
<|> .variables)` — they skip past whatever comment sits there *before* checking their keyword and
failing. Any `m`-side effect during that skip (an accumulated warning) survives the rollback. The
generic `lexeme (pure ())`-before-keyword skip is load-bearing: it's what lets comments legally
appear between declarations without being mistaken for consumed annotations.

Fixing properly means giving `first`/`orElse` real commit semantics (failure after consuming
input propagates instead of retrying siblings) — a core-combinator change risking other
productions that rely on retry-after-partial-consumption. Placement checking proceeds with only
the structural-role-mismatch half, which runs on the already-parsed AST and has none of this
problem.

**What's in the tree meanwhile:** `ParserWarning.unusedAnnotation` (`Parser_/Common.lean`) is
declared with a `msgOf`/`posOf`/`name` instance but never constructed — the emit site is exactly
what's blocked above. Its `-W` name is also absent from `Fugue.lean`'s `knownWarnings`, so
`-Wno-unused-annotation` is rejected as an unknown option today (§9.20). Open: keep the
constructor as the landing site for whenever the combinator question is settled, or delete it and
reintroduce it then. Keeping it costs the `knownWarnings` gap; deleting it loses nothing but the
signpost.

### 9.10 `LAMBDA` — designed, not implemented
Thesis has typing rules (Fig. 3.1.4), but neither `SurfaceTLAPlus.Expression` nor
`CoreTLAPlus.Expression` has a constructor, and there's no `LAMBDA` lexer token. Out of scope;
implementing touches `Parser_/TLAPlus.lean`, both `Syntax.lean`s, `Desugarer/TLAPlus.lean`, not
just the checker.

Design, preserved:
- **Checking-only without an annotation** (thesis Fig. 3.1.4) — `Γ, x1:τ1, ..., xn:τn ⊢ e ⇓ τ ⟹
  Γ ⊢ LAMBDA x1,...,xn : e ⇓ (τ1,...,τn)⇒τ`, requiring the expected type already known.
- **Synthesis form once every binder carries `@type`** — mirroring unbounded quantification:
  `(LAMBDA (* @type: Int; *) x : x + 2)(3)` should synthesize. (The thesis's `LET`-`IN` rewrite
  workaround doesn't apply here — this AST has no `LET`-`IN` node either.)
- **AST work needed:** a `.lambda (binders : List (String × α)) (body : Expression α)`
  constructor on both expression types, a per-binder annotation slot so `tryParseAnnotations` can
  attach `@type` per binder (matching `parseQuantifierBound`), a lexer token, a parser rule, a
  pass-through desugarer case, both checking and conditional synthesis rules.

`Operator`-vs-`Operator` structural subtyping (`Elaborator/Subtyping.lean`, Fig. 3.1.8) only ever
produces an identity coercion precisely because there's no `LAMBDA`-equivalent way to eta-expand
into a new first-class operator value.

### 9.11 Most temporal/action operators aren't parsed; `WF_`/`SF_` need a lexer change
`UNCHANGED`/`ENABLED`/prime/`~>`/`-+>`/`[]`/`<>` have real surface syntax and desugar to plain
`opCall`s onto builtin `var`s, so the generic `OPERATOR CALL` rule already covers them. **Most
other temporal/action operators are not parsed.** `WF_e(A)`/`SF_e(A)` (thesis Fig. 3.1.5) are a
genuine lexing problem, not just a missing parser rule: `WF_e` must lex as **two** tokens (fixed
`WF_` keyword, then identifier `e`), but maximal-munch identifier lexing swallows `WF_e` whole.

Idea, not implemented: in the keyword checker, given an identifier-shaped token starting with
`WF_`/`SF_`, if the remainder doesn't start with `_` or a digit, split into the keyword token plus
a separate identifier token.

`^+`/`^*`/`^#` (postfix action-closure) have **no documented typing rule anywhere** — not in the
thesis, not standard TLA⁺ as far as traced. Left unbound in `builtinContext`; referencing one
fails at `unboundVariable`. Their canonical names are in `WellFormedness/Restrictions.lean`'s
check-3 list for forward-compatibility, currently inert.

### 9.12 Three regression fixtures parked as `xfail`
All three run, all three still fail as described, and an unexpected pass is reported as XPASS.
They were `skip_*` files until phase 4; skipping meant they could quietly start working and nobody
would know.
- `AcceptFunctionDefinitionMultiArgTupleDomain.tla` — parser rejects `f[x \in S, y \in T] ==
  ...` (`unexpected identifier f`).
- `AcceptUnboundedChooseWithExpectedType.tla` — parser rejects bare `CHOOSE m : m = m` as a
  `with`/variable initializer (`unexpected keyword 'CHOOSE'`) — §9.2's `CHOOSE` gap.
- `AcceptFunctionLiteralCartesianProductBinder.tla` — `\X` either isn't desugared to its
  canonical operator name, or that name is missing from `builtinContext`/`Naturals` (`Unbound
  variable` `\X`).

First two look like `Parser_/TLAPlus.lean` gaps, third like `Desugarer/TLAPlus.lean`/
`Driver/Builtins.lean` — neither traced. Fix at the root, drop the `xfail` from the sidecar,
re-run the suite. Don't patch the fixture unless it encodes an unsupported construct (check §8 first).

### 9.13 Three well-formedness checks are currently unreachable
The rule is right in each case; the parser/type-checker just can't produce the triggering input:
- **Check 2(b)'s `nonEmptyLocalChannels`**: `Parser_/PlusCal.lean`'s `parseProcess` hardcodes
  `channels := []`/`fifos := []` — never parses process-level `channels`/`fifos` at all. No
  fixture can exercise the reject side; defense-in-depth only.
- **Check 3's `unboundedQuantifier`**: unbounded `\A x : P`/`\E x : P` parses, but its binder's
  type can never reach an annotation (`parseQuantifier`'s unbounded branch is bare
  `parseIdentifier`, no `tryParseAnnotations`) — always fails at
  `TCError.expectedTypeAnnotation` first. Exception: unbounded `CHOOSE x : P` in checking
  position does succeed (`Elaborator/Expressions.lean:146`'s `[Unbounded choice]` uses the
  expected type) — but `CHOOSE` has no parser rule (§9.2/§9.12). No reachable trigger on either
  form.
- **Check 1's `channelInExpression` via `receive`'s destination `r`** (not the check as a whole
  — `assert ch = ch;` exercises it directly). The only route to a Channel-shaped `r` past type
  checking was a channel-of-channels source (`Channel(Channel(τ))`, needed for `Channel`'s
  reflexivity-only subtyping to accept the `receive`), which `sendable` (§5.3) now rejects at
  declaration time.

All three confirmed correct via direct calls, just not end-to-end through a `.tla` fixture.
Revisit once: (a) the parser gains process-level `channels`/`fifos` (probably never worth it,
given 2(b) is explicitly defense-in-depth), (b) §9.12's `CHOOSE` gap is fixed, or unbounded
`\A`/`\E` gains annotation support, or (c) another route to a channel-shaped `receive`
destination appears (none known; `Channel`'s reflexivity-only subtyping and the lack of another
channel-shaped type constructor make it look structurally unlikely, not proven impossible).

### 9.14 Should intrinsic operators get dedicated AST constructors instead of `opCall`?
Every builtin, intrinsic or stdlib, is `.opCall (.var name _ origin) args`. Keeps the checker's
op-call rule uniform (one generic rule plus a `Γ`/`builtinContext` lookup), but pushes every
downstream pass needing to special-case a builtin into re-deriving its own string/`Origin` match
— `WellFormedness/Restrictions.lean`'s `reservedTemporalActionNames`, `Typed2Computable`'s
computability classification, and both backends unconditionally (stdlib operators "get replaced
by backend-native implementations at code-generation time regardless of what their 'definition'
says"). The shared recognizer table (`Core/TypedTLAPlus/Builtins.lean`, §2) is the near-term
fix, in place — open is whether that's enough long-term.

Scope: intrinsics only — `builtinContext`'s ~14 `EXTENDS`-independent entries (`=`, `/=`, `/\`,
`\/`, `=>`, `<=>`, `\neg`, `\in`, `\notin`, `\subseteq`, `\cup`, `\cap`, `\`, `DOMAIN`, plus the
temporal ones in §9.11) — **not** vendored stdlib operators (`Naturals`/`Sequences`/`Bags`/
`FiniteSets`, §5.3's `builtinModules`). Intrinsics are a small closed permanent set baked into
every module; stdlib operators are open-ended declarations in an ordinary (if hardcoded)
`Module`, and giving those constructors would mean one per `Len`/`Head`/`+`/…, undermining the
point of representing them as ordinary declarations.

### 9.15 Infinite set used as a quantifier/set-builder domain
`Nat`/`Int` (reachable builtin infinite sets; `STRING` isn't parseable yet, moot) can be used as
a bare `forall`/`exists`/`choose` or set-builder (`collect`/`map'`) domain with nothing rejecting
it — `\A x \in Nat : x >= 0` translates cleanly through `Typed2Computable` today. Real gap given
§5.7's scheme (§7.2.1.2): `\A x \in S : P`/`\E x \in S : P` compile to a search over `S`, `{x \in
S : P}`/`{e : x \in S}` copy `S`'s slice, `CHOOSE x \in S : P` filters then takes a minimum — all
three enumerate `S` at runtime, so an infinite `S` doesn't terminate.

**Settled, not part of this gap:** a function literal's domain (`[x \in S |-> e]`) may be
infinite. Functions compile to lazy maps (§5.7), so `[x \in Nat |-> x * x]` is fine and stays
unrestricted; `Typed2Computable`'s current no-restriction behavior is correct.

**Open:** whether/how to reject an infinite domain at `forall`/`exists`/`choose`/`collect`/`map'`
(and PlusCal's `with x \in dom`), and where the check lives (`Typed2Computable`, matching
`fnSet`/`recordSet`'s precedent, vs. deferred to `Network2Go`/§5.7 where the lazy-map/eager-slice
distinction is implemented). Two options, neither committed:
- **Narrow syntactic check**: reject a *direct* bare reference to a known-infinite builtin set
  (`Nat`/`Int`) at exactly these positions — misses derived cases (`Nat \ {0}`, `Nat \cup {1}`,
  an operator returning `Nat`).
- **Track possible-infiniteness with an invariant**: most infinite sets encountered (`Nat`,
  `STRING`, `[Nat -> Nat]`) denote "the universe of all values of some type", possibly
  summarizable rather than needing general finiteness inference. Possibly not worth it.

Revisit before §5.7 needs a real answer for how these compile, and once §9.14's recognizer-table
shape settles (it determines how cheap a fix is).

### 9.16 `EXTENDS` reports false "ambiguous module" when `-I` names the importing module's own directory
`Driver/Modules.lean`'s `locate` (§5.3) builds candidates by walking `containingDir.toList ++
(-I)'s searchPath`, appending one entry per directory with a matching `<name>.tla` — no dedup by
resolved path. `-I dir` where `dir` is the importing module's own directory produces two entries
for the literal same file, reported as `ambiguousModule` with the identical path listed twice.
Confirmed: `fugue -I foo foo/Main.tla` (`Main.tla EXTENDS Dep`, `Dep.tla` also in `foo`) fails;
dropping `-I` or pointing it elsewhere works.

**Open:** how to dedup — compare `System.FilePath` values directly (fails when `containingDir`
and a `-I` entry spell the same directory differently, relative vs. absolute), or canonicalize
each candidate first (needs an `IO`-level realpath, not used anywhere in this codebase yet).
Either way the dedup must land before `locate`'s final `match found with | [] | [_] | multiple`
— a false ambiguity is a hard compile error, not a warning.

### 9.17 No proof `subtype` and `Coercion.apply`/`.applyComputable` agree on type
`Coercion` is real closed data, not an opaque closure, which makes a real theorem statable; none
written. Checked only empirically — `tests/regression/` fixtures plus one hand-verified dump.

**Open:** what to prove, roughly `subtype τ τ' = .success c → ∀ e, Γ ⊢ e : τ → Γ ⊢ c.apply e :
τ'` — likely two statements, one per `apply`/`.applyComputable`, since they discharge against
different `Expression` types. Also open whether this falls under the well-scopedness-preservation
exception in `INSTRUCTIONS.md`'s verification-scope rule or is a separate ask;
`INSTRUCTIONS.md` names only well-scopedness preservation as in scope. Don't start without
check-in.

### 9.18 `lub` isn't a real join, so `IF`/`CASE`/set-literal *synthesis* over incomparable branches fails
`Elaborator/Subtyping.lean`'s `lub` returns the wider of its two arguments, or `none` when
neither is a subtype of the other — it can only ever return a type already handed to it, never
name a common upper bound that isn't one of the two inputs. `lubAll`
(`Elaborator/Expressions.lean`) folds it left across branches, so `IF`/`CASE`/`{e₁,…,eₙ}` in
*synthesis* position succeed only when the join happens to *be* one of the branch types;
otherwise `TCError.ambiguousType`.

Concretely: `IF c THEN "ab" ELSE <<1, 2>>` has branch types `Str` and `⟨Int,Int⟩`, whose common
upper bounds are `Seq(Int)` and `Int → Int` — neither producible by `lub`, so the fold fails on
the first pair. Order-sensitive for the same reason: the same branches with an `Int → Int` one
placed first succeed, since the join is then already in the accumulator. `lub` itself is
symmetric; the order-sensitivity is the fold's.

Distinct from `lub`'s *partiality*, which is correct and stays: `lub Int Str` is genuinely
`none` — `Int` has no axiom out of it, so no shared upper bound exists, and `ambiguousType` is
right. The gap is only pairs that do have a least upper bound and get rejected anyway.

**Not a blocker, by design.** §5.3 already commits to the matching trade on the metavariable side
("error and require an explicit annotation instead of implementing `lub`"), and thesis §3.1.3.6's
*checking* rules for `IF`/`CASE`, both implemented, make that escape hatch reachable: given an
expected type, each branch is checked against it directly and picks up its own coercion. The
example type-checks under an annotation
(`tests/regression/accept_if_checked_heterogeneous_branches.tla`,
`accept_case_checked_heterogeneous_branches.tla`). The limitation bites only in annotation-free
synthesis position.

**Open, quite possibly permanently:** whether to make `lub` a real join. Doing so means a
structural recursion mirroring `subtype`'s case split but producing a type rather than a
`Coercion` (`join (Set a) (Set b) = Set (join a b)`, records/tuples pointwise on matching shapes,
an axiom-widening fallback), plus a mutually-recursive `glb` for `function`'s contravariant
domain — roughly duplicating `subtype`'s ~90 lines for a case no fixture needs. Unchecked
prerequisite: folding a partial join pairwise is order-independent only if the subtype order is
**bounded-complete** (any two types with a common upper bound have a least one). Not verified;
`function`'s contravariant domain is where a counterexample would most likely hide. If it holds,
fixing `lub` suffices and `lubAll` stays a plain fold; if not, the join must become genuinely
n-ary and `lubAll` goes away. Don't start either without checking bounded-completeness first, and
don't start at all unless a real program hits this.

Cheap adjacent improvement, unclaimed: `TCError.ambiguousType`'s message
(`Elaborator/Errors.lean`) states the symptom without naming the fix. Pointing it at "annotate
the expected type" would make the workaround discoverable. Both throw sites are inside `lubAll`,
so no other caller's wording constrains it.

### 9.19 `GuardedPlusCal.Declarations` is a byte-identical copy of `ElaboratedPlusCal.Declarations`
`Core/GuardedPlusCal/Syntax.lean`'s `Declarations` has the same three fields at the same types as
`Core/TypedPlusCal/Syntax.lean`'s, plus a `Bifunctor`/`Bitraversable` pair whose bodies match
field for field. Its docstring says as much ("A fresh copy of `ElaboratedPlusCal.Declarations`'s
shape"). The cost lands in `Computable2Guarded.lean`'s `Declarations.toGuarded` — a
field-for-field repackaging its own docstring calls unnecessary — and `NetworkPlusCal` then reuses
the Guarded copy rather than adding a third.

The split isn't a blanket policy at this layer: the same file *reuses* `ElaboratedPlusCal.Ref` and
`.MulticastFilter` rather than copying them, precisely so `Computable2Guarded`'s `Ref`
field-access fix flows through. So `Declarations` is the odd one out, not the rule.

**Open:** collapse it (delete ~30 lines and the no-op conversion, pin `GuardedPlusCal.Declarations
:= ElaboratedPlusCal.Declarations` the way `Ref` already is), or keep the copy. Keeping it is
defensible under the standing preference for splitting an AST once a stage genuinely diverges —
the question is whether `Declarations` is *expected* to diverge at the Guarded stage. It hasn't
through Network, and no planned pass adds a field to it. If nothing is expected, the copy is
buying only the option to diverge cheaply later.

### 9.20 `knownDebugOptions`/`knownFeatures`/`knownWarnings` are hand-maintained arrays
`Fugue.lean` validates `-d`/`-f`/`-W` names against three literal `Array String`s. `knownWarnings`
has already drifted: it lists `fair` and `duplicate-parameter` but not `ParserWarning
.unusedAnnotation`'s name, so `-Wno-unused-annotation` is rejected as unknown (§9.8). Nothing
makes the arrays and the `CompilerDiagnostic.name` instances agree — the drift is silent, and the
same failure mode is available to every warning added later.

The warning half of this is now derivable and wasn't when it was written:
`Common/Diagnostics/Registry.lean` carries a `warningName` on every entry, so `knownWarnings` can
be `Diagnostics.entries.filterMap` over it — and since `CompilerDiagnostic.code` has no default,
a new warning cannot exist without an entry to derive from. That fixes §9.8's rejected
`-Wno-unused-annotation` as a side effect.

**Open:** the debug/feature arrays, which have no derivable source at all — no declaration site
anywhere names `dump-guarded` except the `getDebugFlag` call that reads it. Cheapest partial fix,
if a registry for them isn't wanted: move each array next to what it validates, so adding a dump
point and registering its name are the same edit.

### 9.21 `posOf` is called on values that were never registered, and answers with a dead one's span
`Common/Position.lean`'s `registerSource` (`@@`) and `posOf` attach spans to arbitrary values
through `Internal.sourceMap`, an `IO.Ref (Std.HashMap USize SourceSpan)` keyed on `ptrAddrUnsafe`.
The key fact is not that two live values can share an address — they cannot — but that **the map
outlives the values it describes**, while `posOf` has no way to tell a hit from a coincidence.

`Parser_/PlusCal.lean` and `Parser_/TLAPlus.lean` register the *Surface* AST. `Desugarer/
PlusCal.lean` contains **no `@@` at all**, so the `CorePlusCal` statements it builds are
unregistered — and `checkAssignConflicts` reads their positions anyway, via `match_source`. Those
statements are allocated as the Surface ones they replace are being freed, so they land on
addresses whose entries are still in the map, and `posOf` returns a neighbour's span.

Visible today, single file, plain CLI, nothing to do with the test runner:

```
$ fugue compile tests/regression/reject_repeated_indexed_assign.tla
error[E0018]: 'x' is written to more than once within the same atomic step.
 18 |         goto Done;
```

The second write is on line 17; line 18 is the statement after it. Had the map been empty, `posOf`
would have returned `default` — line `0`, which `SourceSpan.placeholder`'s doc comment already
warns renders wrong. There is no spelling of this that is right, because the position was never
recorded.

Across compiles in one process the stale entry comes from a *different file*, so the line need not
exist at all, and `CompilerDiagnostic.pretty`'s line lookup is a `get!`: `PANIC at
List.get!Internal`, on roughly one full-suite run in three. That is how `lake test` surfaced it;
one process per fixture never reuses another compile's addresses, which is why `run.sh` and the
CLI never crashed.

Mitigated, not fixed: `runPipelineIO` calls `forgetSourcePositions` before each compile. That
bounds staleness to one compile — restoring exactly the (already wrong) one-file CLI behaviour,
and with it a clean suite. It makes *concurrency* worse: one worker's clear lands mid-compile in
another and drops the spans it has registered, so `lake test` defaults to `-j 1`.

**Open:** two separable questions.
1. *Should the desugarer register what it builds?* Cheapest fix for the wrong spans — carry the
   Surface node's span onto the Core node with `@@` at each construction site. Restores correct
   positions without touching the mechanism.
2. *Should the mechanism survive?* An address key means a span is only as valid as the allocation
   it was recorded under, and `posOf` cannot distinguish "never registered" from "registered by
   something now dead". Per-compile state, or a real field on AST nodes, removes the class. The
   address key is what makes `@@` free to write at any node without changing its type, which is
   why it was chosen.

Blocks parallel fixtures either way, and blocks trusting a span assertion in a fixture sidecar
(planned check 4).

Worth noting: `CompilerDiagnostic.pretty` crashing on an out-of-range line is its own small
defect. A renderer should degrade, not `get!`.

### 9.23 Three fixtures assert something they do not exercise, and are parked as `Skip*`
Found by phase 4's sidecars: every rejection now records the stage and code it must produce, and
six fixtures produced something else. All six passed `run.sh`, which only ever asked for a nonzero
exit.

**Three are fixed.** `RejectGlobalTlaplusVariableCrossModule` and `RejectTransitiveTemporal` failed
at `resolve` (`E0021`) because their `EXTENDS` could not be found: `Driver/Modules.lean`'s `locate`
looks for `<ModuleName>.tla`, and the corpus named files in snake_case. Renaming every fixture to
its module name — which TLA⁺ requires anyway, and which nothing had been checking — makes both
resolve, and both now produce exactly what their headers always claimed: `E0052`
(`globalTLAPlusVariable`, check 2(c)) and `E0053` (`bareTemporalOrAction`, check 3 transitive).
`RejectAssignThenReceiveSameVariable`, which did not parse at all, was repaired by hand and now
produces `E0018` (`conflictingAssignment`) at `desugar`, as its header always said.

**Three are parked**, renamed from `Reject*` to `Skip*` with a sidecar `reason` the runner prints
on every run. `Skip` rather than `xfail` because the fault is in the fixture, not the compiler:
each claims to test a pass it never reaches, and fixing the compiler would not make it start
testing that pass. They need rewriting.

*Two die at parse (`E0002`) before reaching the pass they target.*
- `SkipFunctionDefinitionDomainNotTuple` — hits the multi-argument function-definition parser gap,
  duplicating `AcceptFunctionDefinitionMultiArgTupleDomain` (§9.2, `xfail`) while claiming to test
  `TCError.notATupleType`.
- `SkipUnboundedChooseSynthesisPosition` — hits the `CHOOSE` parser gap (§9.2), duplicating
  `AcceptUnboundedChooseWithExpectedType`, while claiming to test `TCError.cannotInferType`.

*One dies at annotation parsing (`E0005`).* `SkipOperatorParamArityMismatch`'s `@type` annotation
does not parse, so `TCError.paramArityMismatch` is never reached. Either the annotation is
malformed, or it uses the pre-Apalache dialect the parser rejects (§9.2).

**Open:** how each should be rewritten. The first two duplicate `xfail` fixtures that already track
their parser gaps, so they are only worth keeping if rewritten as genuine type-checker fixtures
once those gaps close. Note the cost of parking them: a skipped fixture does not run, so nothing
will announce it when the gap closes — the `xfail` pair is what to watch instead.
