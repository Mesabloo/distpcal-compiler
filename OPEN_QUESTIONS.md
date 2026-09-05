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
- `LET`/`IN` are lexed (`.let`/`.in` tokens exist) but have **no parser rule at all**. `CHOOSE`
  used to be in the same state; it now has one (`parseChoose`, bounded and unbounded both).
- `@type` supports only the Apalache-style syntax (`Channel({type: Str, agent: Address})`); the
  pre-Apalache dialect (`Channel[{type: string, agent: T}]`) is not.

### 9.3 CLI / UX — remaining details
Flag surface settled (§2), `-X<name>` included. One thing left open:
- **Join Calculus "flavors"** (`-t join[jocaml]`, `-t join[jerlang]`) — selecting between
  lowerings for different Join Calculus runtimes; ties into §9.1. Possibly not worth the
  complexity — don't build unless asked.

Resolved: the Go package name is `-Xgo-pkg:<name>`, defaulting to `main` — a property of the
output rather than of the compiler's behaviour, so `-X` rather than a `-p` of its own. `-o` names a
**file**: a compile emits one Go file, because everything lands in one package and Go compiles a
package as a unit, so splitting per process would buy nothing.

### 9.4 Join Calculus operational semantics — low priority
`Core/JoinCalculus/Semantics/` (RCHAM heating/cooling + reaction rules, thesis Fig.
8.4.2–8.4.3, local and distributed) isn't wanted now — getting `Network2JoinCalculus` to
compile is the near-term goal. Only matters once there's appetite to prove something about
that pass (prerequisite for §9.1).

### 9.5 Multicast compilation is undescribed for the Join Calculus backend
`multicast(x, [y ∈ e1 ↦ e2])` is in the v1 subset (§8). §5.6's Join Calculus scheme only shows a
single `send(c[α],e)` folded into a reaction body — unclear whether emitting to a filtered set
means one atom per recipient (which needs a bounded loop/comprehension inside a reaction body,
not obviously supported by the target calculus) or something else.

The Go side is settled and implemented (§5.2 for the filter collapse, §5.7 for the compiled
call), and does not constrain this: what it settles is that the *iteration* need not appear in
emitted code, which is an option the Go runtime library has and the target calculus may not.
What it does supply is the input shape — `CorePlusCal.Multicast` is a recipient set plus a
payload keyed by recipient, with no bind list left to destructure, so whatever this backend
emits starts from the same two pieces.

### 9.6 Runtime value representation in Go: channel capacity
TLA+ `Int`/`Nat` are unbounded and FIFOs uncapacitated; Go's types and channels are bounded.
The numeric side is resolved (§2, §5.7): arbitrary precision by default, machine integers
behind the `fugue_machint` build tag, no Fugue-level flag.

The channel-capacity side no longer belongs to the compiler at all (settled, §5.7): `send`
compiles to `Sender[τ]`'s `Send`, whose contract is "may block, no error result", so capacity
is a property of whichever endpoint implementation the person wiring the system supplies —
generated code neither picks it nor can observe it.

What remains is a hypothesis about *any* bounded implementation: because lock inference (§5.7)
already serializes atomic blocks touching shared state, a blocking `Send` shouldn't change
*which* transitions are enabled — at worst it slows execution. Holds for the Go-channel-backed
endpoints in the Ping-Pong end-to-end run (§5.7). Unconfirmed for a socket-backed endpoint,
where blocking comes out of the socket plus runtime buffering rather than a capacity anyone
chose; re-check whenever a reference transport gets written (§5.7's deferred-scope note).

**Known, accepted risk:** a block that blocks in `Send`/`Recv` *while holding its component's
lock* freezes every other block sharing that lock — potentially including the process's own
`T_rx` thread. Stays local to that one process; what unblocks it is the peer's own code
eventually receiving. Failure mode is "one process goes locally unresponsive," not a
system-wide deadlock.

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

### 9.11 Most temporal/action operators aren't parsed; `WF_e(A)`/`SF_e(A)` have no parser rule
`UNCHANGED`/`ENABLED`/prime/`~>`/`-+>`/`[]`/`<>` have real surface syntax and desugar to plain
`opCall`s onto builtin `var`s, so the generic `OPERATOR CALL` rule already covers them. **Most
other temporal/action operators are not parsed.** `WF_e(A)`/`SF_e(A)` (thesis Fig. 3.1.5) lex
correctly — `WF_`/`SF_` are their own tokens (`Parser_/TLAPlus.lean`'s `identifierOrKeyword`
matches them ahead of the maximal-munch identifier scan, so `WF_e` lexes as `WF_` then `e`,
`RejectWeakFairnessNotParsed` pins it) — but `parseAtom` has no production for either: `WF_`/`SF_`
reach the parser as unexpected tokens.

`^+`/`^*`/`^#` (postfix action-closure) have **no documented typing rule anywhere** — not in the
thesis, not standard TLA⁺ as far as traced. Left unbound in `builtinContext`; referencing one
fails at `unboundVariable`. Their canonical names are in `WellFormedness/Restrictions.lean`'s
check-3 list for forward-compatibility, currently inert.

### 9.12 Regression fixtures parked as `xfail`
All run, all still fail as described, and an unexpected pass is reported as XPASS. They were
`skip_*` files until phase 4; skipping meant they could quietly start working and nobody would
know.
- `AcceptFunctionDefinitionMultiArgTupleDomain.tla` — parser rejects `f[x \in S, y \in T] ==
  ...` (`unexpected identifier f`). Looks like a `Parser_/TLAPlus.lean` gap, not traced.
- `AcceptFunctionLiteralCartesianProductBinder.tla` — types now (`\X` is in `builtinContext` at
  `(Set(a), Set(b)) => Set(<<a,b>>)`), but has **no Go compilation**: a product's elements are
  pairs, and a tuple compiles to an *anonymous* struct that only the site building it can name,
  so a runtime `SetProduct` cannot construct its own elements the way `SetUnion` does. It would
  have to take the pair constructor as a callback, the way `SetMap` takes its function — not
  written, nothing needing it yet.
Fix at the root, drop the `xfail` from the sidecar, re-run the suite. Don't patch the fixture
unless it encodes an unsupported construct (check §8 first).

**Three left this list by that last rule**, all rewritten as `Reject*` fixtures asserting the
rejection they actually produce, since each encodes a construct outside §8:
- `RejectUnboundedChooseWithExpectedType` (was `Accept*`) — `CHOOSE` parses now (§9.2's gap is
  closed), and the fixture type-checks through `Elaborator/Expressions.lean`'s checking-mode
  `[Unbounded choice]` rule, so what it really exercises is check 3's `unboundedQuantifier`
  (`E0054`, `wellformedness`). §8 has no unbounded quantifier.
- `RejectMulticastMultiComponent`, `RejectMulticastPartialAnnotation` (both were `Accept*`) — a
  multi-component multicast filter (§5.2) makes the recipients a tuple, so the channel's domain is
  one, and the `Network` struct holds `map[comm.Address]`; the Go backend rejects it with `E0061`
  at `go`, the same limit `compileSend` has for a channel indexed by more than one bracket group.
  §8's multicast is single-binder (`multicast(x, [y ∈ e1 ↦ e2])`), so the multi-component form is
  outside the v1 subset and the rejection is the expectation. The second of the two remains the
  only route to W0005 (`partial-multicast-annotation`); the warning fires and is asserted there,
  now alongside the error.

**`\X` is binary here**, with a precedence and left associativity, though
`Core/SurfaceTLAPlus/Syntax.lean` notes it is not really binary in TLA⁺'s grammar. So `A \X B \X
C` is `(A \X B) \X C`, whose elements are pairs holding a pair rather than the flat triples TLA⁺
means. Nothing accepts the wrong shape — `collapseToSingleBinder` projects component `i` as
`z[i]`, and `z[3]` on a pair is caught by the tuple-index bound — but a genuinely n-ary `\X`
(needed before three-component products of any kind work, including multicast filters) is
unwritten.

### 9.13 Two well-formedness checks are currently unreachable
The rule is right in each case; the parser/type-checker just can't produce the triggering input:
- **Check 2(b)'s `nonEmptyLocalChannels`**: `Parser_/PlusCal.lean`'s `parseProcess` hardcodes
  `channels := []`/`fifos := []` — never parses process-level `channels`/`fifos` at all. No
  fixture can exercise the reject side; defense-in-depth only.
- **Check 1's `channelInExpression` via `receive`'s destination `r`** (not the check as a whole
  — `assert ch = ch;` exercises it directly). The only route to a Channel-shaped `r` past type
  checking was a channel-of-channels source (`Channel(Channel(τ))`, needed for `Channel`'s
  reflexivity-only subtyping to accept the `receive`), which `sendable` (§5.3) now rejects at
  declaration time.

Both confirmed correct via direct calls, just not end-to-end through a `.tla` fixture.
Revisit once: (a) the parser gains process-level `channels`/`fifos` (probably never worth it,
given 2(b) is explicitly defense-in-depth), or (b) another route to a channel-shaped `receive`
destination appears (none known; `Channel`'s reflexivity-only subtyping and the lack of another
channel-shaped type constructor make it look structurally unlikely, not proven impossible).

**Check 3's `unboundedQuantifier` is no longer on this list.** Unbounded `\A x : P`/`\E x : P`
still cannot trigger it — the binder's type can never reach an annotation (`parseQuantifier`'s
unbounded branch is bare `parseIdentifier`, no `tryParseAnnotations`), so it fails at
`TCError.expectedTypeAnnotation` first. Unbounded `CHOOSE x : P` in checking position does,
though: `Elaborator/Expressions.lean`'s `[Unbounded choice]` rule takes the type from the expected
type rather than an annotation, and `CHOOSE` now parses (§9.2). End-to-end fixture:
`RejectUnboundedChooseWithExpectedType`.

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

**Not affected by the denotational semantics.** `Core/ComputableTLAPlus/Semantics/Interface.lean`
keeps evaluation abstract (`class ExprSemantics`), so `Core/*/Semantics/Denotational.lean` says
nothing about quantifier or set-builder domains either way. This stays a `Network2Go`/§5.7
question, and whichever `ExprSemantics` instance eventually models TLA⁺ inherits it unchanged.

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

### 9.23 Six fixtures asserted something they did not exercise; one remains parked as `Skip*`
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

**Three were parked**, renamed from `Reject*` to `Skip*` with a sidecar `reason` the runner prints
on every run. `Skip` rather than `xfail` because the fault is in the fixture, not the compiler:
each claims to test a pass it never reaches, and fixing the compiler would not make it start
testing that pass. **One is still parked; two are back.**

*One dies at parse (`E0002`) before reaching the pass it targets.*
- `SkipFunctionDefinitionDomainNotTuple` — hits the multi-argument function-definition parser gap,
  duplicating `AcceptFunctionDefinitionMultiArgTupleDomain` (§9.2, `xfail`) while claiming to test
  `TCError.notATupleType`.

*Two are un-parked.* `SkipUnboundedChooseSynthesisPosition` was parked for the `CHOOSE` parser gap;
that gap is closed (§9.2), so `print CHOOSE x : x = x` now reaches the type checker and produces
the `E0028` (`cannotInferType`) its header always claimed. Back as
`RejectUnboundedChooseSynthesisPosition`, `status: ok`.
`SkipOperatorParamArityMismatch` was parked because its `@type` annotation died at annotation
parsing (`E0005`): `Parser_/Annotations.lean`'s `parseType'` could not nest an operator-shaped
(`=>`) type inside another operator type's argument list. That gap is closed too, so
`((Int) => Int, Int) => Int` now parses and `Op(F(_,_), x) == x` reaches `checkParamArity`, which
produces the `E0039` (`paramArityMismatch`) its header always claimed. Back as
`RejectOperatorParamArityMismatch`, `status: ok`, `failsAt: typecheck`.

**Open:** how the last one should be rewritten. It duplicates an `xfail` fixture that already
tracks its parser gap, so it is only worth keeping if rewritten as a genuine type-checker fixture
once that gap closes. Note the cost of parking it: a skipped fixture does not run, so nothing will
announce it when the gap closes — the `xfail` pair is what to watch instead. Both un-parkings above
were noticed by hand, not by the suite, which is the point.

### 9.24 The span map is still one global `IO.Ref`, so `lake test` stays `-j 1`
Every pass now registers every position-carrying node it builds (`PLAN.md` §2, "Source
positions"), so `posOf` no longer answers with a dead node's span for anything the pipeline
constructs. What that fixed is *correctness within one compile*. It did not change the storage:
`Common/Position.lean`'s map is a process-wide `IO.Ref (Std.HashMap USize SourceSpan)`, and
`runPipelineIO` still calls `forgetSourcePositions` before each compile to keep one compile's
entries from being live keys for the next one's freshly-allocated nodes.

That clear is destructive and takes no lock, so two concurrent compiles in one process still
break each other: one worker's clear drops spans the other has already registered. `Tests/Main
.lean` therefore defaults to `-j 1`.

**Open:** whether to make the map per-compile — an entry in `DriverState`, threaded like the
fresh-name counter — or leave it global and accept sequential fixtures. Per-compile is the
obvious answer for concurrency, but the map is reachable from `@@`/`posOf`, which are deliberately
*pure* and callable from anywhere without a monad; giving them a per-compile home means either
threading a reader through every construction site (losing exactly the property that makes `@@`
cheap to write) or keeping a global handle that a compile swaps in and out, which is the same
race in a different shape.

Also open, and separable: a small residue of `posOf` reads still land on values nothing ever
registered — statically allocated compiled-in constants, found by instrumenting `posOf` to report
map misses across the fixture corpus. These are a weaker failure than an unregistered *heap* node: a static object's
address is never recycled by the heap allocator, so the read returns `default` (line `0`, which
`SourceSpan.placeholder`'s doc comment explains renders wrong) rather than an unrelated node's
span. `Common/Errors.lean`'s renderer no longer panics on such a line — it degrades to a blank
quoted line — so the symptom is a bad-looking diagnostic, not a crash. Which constants these are
was not tracked down.

### 9.32 `@type` parser needs parens around a unary operator's own parameter
`\* @type: (Int) => Int;` parses; `\* @type: Int => Int;` fails at `E0005`. `Parser_/Annotations
.lean`'s `parseType'` only accepts an operator type's argument list when it is parenthesised, so a
one-argument operator type needs a paren pair a human would leave off. `((Int) => Int, Int) => Int`
already parses (§9.23), so nested operator types work — this is only the bare unary case. Make the
argument-list rule accept a single unparenthesised argument type, keeping the parenthesised form.

### 9.33 Reachability walk recurses into builtin-module definition bodies
`WellFormedness/Reachability.lean`'s `walkReachable`, on a `.var _ (.module m name)` that resolves
to an `operator`/`function`, recurses into its body — including when `m` is a builtin module
(`Naturals`, `Sequences`, `Fugue`, …). Every such body is now self-referential (`Op(x) == Op(x)`,
`Driver/Builtins.lean`), so the walk takes one wasted step per builtin reference and then stops on
its memo (or on `resolveInModule`'s `currentModule == targetModule` branch resolving `name` against
the *caller's* `ownDecls`, where it is absent). Backends replace every builtin call regardless of
its body (`PLAN.md` §5.3), so the recursion re-reaches nothing.

Fix: when the resolved declaration's module is in `builtinModules`, record the `(module, name)`
pair and stop — never walk the body. Both consumers already want exactly that: `Typed2Computable`
drops every closure entry whose origin hits `builtinOpOf?`, and `Restrictions.lean`'s transitive
temporal/action check keys on the builtin origin directly. Check the elaborator's own use of the
walk for the same recursion, and confirm against §9.13's two already-unreachable checks that
nothing reachable becomes unreachable.

### 9.34 No type synthesis for an unannotated operator/function definition
`Elaborator/Declarations.lean`'s `[Operator definition]`/`[Function definition]` cases open with
`requireAnnotation`, so `X == 0` (or `Y == 0 - 0`, `Op(x) == x + 1`) is rejected with `E0027`
without ever looking at the body — no attempt to synthesize `X : Int` from `0 ⇒ Int`. This matches
thesis Fig. 3.1.9, whose rule conclusions carry the type in the syntax (`f(x⃗) ⦂ (τ⃗)⇒τ ≜ e`) and
check the body against it; §3.1.4 explicitly notes the non-recursive case *could* be inferred and
requires the annotation anyway, for uniformity with the recursive case (where inferring `f`'s type
needs `f`'s type).

Open: whether to add a synthesis path for the unannotated, non-`RECURSIVE` case — `inferExpr body`
(already implemented, used everywhere else), bind `f` at the synthesized type, keep
`requireAnnotation` only when the body is in checking-only position or `f` is recursive. Cheap
given the bidirectional machinery; a deliberate step past the thesis. `CONSTANT`/`VARIABLE`
annotations stay mandatory regardless — they have no body to synthesize from.
Item 7 §9.5 (thesis phase 10, P3): `Core/{Guarded,Network}PlusCal/Semantics/Denotational.lean`'s
`Statement.reducing`/`.aborting` still have `multicast = ∅` (four sites, `TODO(item 7)`). Prior
art left the same case `sorry` in both — no existing shape to port.

`ComputableTLAPlus.ExprSemantics.mem : V → V → Prop` is a bare membership *relation*; there is no
`enumerate : V → List V` (or similar) to pull a concrete recipient list out of a set value. A
`multicast`'s `reducing` is meant to be "a set-indexed family of `send`s, folded over the evaluated
address set" (plan §1 P3), which needs such a list to fold over.

Proposed, not yet implemented: characterize the recipient list *relationally* instead of
computing it — `∃ recipients : List V, (∀ r, r ∈ recipients ↔ ExprSemantics.mem r S) ∧
recipients.Nodup ∧ …` — matching `Eval`'s own relational style ("no derivation tree" already
*is* "no value", `Semantics/Interface.lean`'s module doc). `Nodup` rules out the degenerate
reading where the same recipient is sent to twice. Fold sends over `recipients` via a new
inductive relation (`MulticastFold` for `reducing`, `MulticastAborts` for "the fold gets stuck
partway"), each recipient keyed as `(c, [.inr r])` — the recipient value as the channel's one
index segment, matching an ordinary `chan[addr]` reference's own indexing convention.

Open: whether this relational-enumeration approach is right, or whether `ExprSemantics` should
instead grow an actual enumeration field (bigger surface, but avoids `Nodup`-as-a-proxy-for-
"this is really a set" and the resulting order-nondeterminism in `reducing`'s outcome set).
Blocks P3, and P6/D4 (whose generic action-statement lemma quantifies over every action
constructor, `multicast` included) until resolved.

### 9.29 Nothing checks that block labels are unique within a process
Found during item 7, §D8, building `CodeLabelRefines` from `ProcessRefines`.

`WellFormedness/Labelling.lean` collect a process's labels (`Process.labels`) and check every `goto`
target resolve (`checkGotoTarget`), rejecting a redefined `"Done"`. It never check the collected list
is `Nodup`. Nothing else do either — `Nodup` appear only for *declaration* names
(`WellFormedness/WellScoped/CorePlusCal.lean:45`, `WellScoped/GuardedPlusCal.lean:149`).

**Why it matter.** A `goto l` name a label; two blocks carrying `l` make it ambiguous. The semantics
do not error — `Process.codeTable` (both languages) define a label to denote the *union* of every
block carrying it, so duplicates silently become non-deterministic choice between blocks. That is a
defensible reading of an ill-formed program, but it is not one the source language means, and no
diagnostic tell the user.

**What it cost the proof.** `CodeLabelRefines` want one branch list per label per side. With
duplicates possible, `srcBranchesAt`/`tgtBranchesAt` (`Guarded2Network/Lemmas/Process.lean`) are
*concatenations* over every block at that label, and the two side's lists cannot be paired
positionally. So `CodeLabelRefines.refines` is `BranchesRefine` (`∀ Br' ∈ brs', ∃ Br ∈ brs, …`) rather
than `List.Forall₂`. That weakening is free — `blockRefines_step` only ever spent the `Forall₂` via
`exists_left` — so the proof do not *need* uniqueness. Recorded because the checker gap is real, not
because item 7 is blocked on it.

**To resolve.** Add a `Nodup` check to `TypedPlusCal.Process.labels` (or beside it) with its own
`WellFormednessError`/`Diagnostics.Entry` — `duplicateLabel`, positioned at the second block carrying
the name, same way `redefinedDone` is positioned at `posOf blk.end`. Then decide whether the
Guarded/Network `WellScoped` structures should carry the fact as a field, so item 7 could strengthen
`BranchesRefine` back to `List.Forall₂` — cosmetic, and probably not worth it: the weaker form is
what every consumer wants anyway.

Cross-check when doing it: `§9.13` list two well-formedness checks already unreachable, so confirm a
new one is actually reachable from the driver before adding a fixture.

### 9.30 Parser fails before module header
In TLA+, any text that occurs before the module header, and after the module footer, is gibberish to be 
ignored. Currently, the parser may fail in unexpected ways (e.g. a comment before the header).

### 9.31 `CorrectInstance` private-import workaround
`Guarded2Network.lean` imports `Guarded2Network.CorrectInstance` privately (bare `import`) so plain
`lake build` builds and checks the concrete-`Value` refinement proof (`correct''`,
`assert_no_sorry`). Must be private: `zflean`'s `ZFLean/Basic.lean:172` `notation " ε "` is global,
and a `public import` re-exports it into `Driver/Pipeline.lean` (`runStage {ε}`) and later passes,
where `ε` is a type variable.

Cost: a private import is not re-exported, so downstream code doing `import Guarded2Network` cannot
reach `correct''` — using it needs a direct `import Guarded2Network.CorrectInstance`, which
re-triggers the clash. Blocks further development on top of the correctness theorem.

`zflean` makes the `ε` notation scoped in its `v4.33.0` release. The lockfile pins
`zflean @ v{Lean.versionString}`, so this arrives with the toolchain bump to Lean 4.33. Revisit
then: `public import Guarded2Network.CorrectInstance` and drop the workaround.
