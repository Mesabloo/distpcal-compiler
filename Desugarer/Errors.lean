import Common.Position
import Common.Errors

/-- Errors produced while desugaring `SurfaceTLAPlus`/`SurfacePlusCal` into `CoreTLAPlus`/`CorePlusCal`. -/
inductive DesugarError : Type
  /-- `@` used outside of an `EXCEPT` update (`Desugarer/TLAPlus.lean`). -/
  | misplacedAt (pos : SourceSpan)
  /-- A `goto` is immediately followed by more, unlabelled statements — unreachable dead code,
  not something to route around (`goto` immediately followed by a *label* is the ordinary
  "this block ends here" case and is not an error, `Desugarer/PlusCal.lean`'s module doc). -/
  | gotoNotInTailPosition (pos : SourceSpan)
  /-- A statement appears before the first label of its enclosing thread — there is no label to
  attach it (or the block it starts) to. Well-labelledness itself (every `goto` targets a real
  label) is checked later (§5.2a); this is a narrower, purely structural precondition for
  desugaring to even produce a `List (String × Block …)` at all. -/
  | unlabelledStatement (pos : SourceSpan)
  /-- A label appears inside a `with` body. Real PlusCal never allows this — `with` introduces a
  binding that only makes sense within one atomic step, so execution can never pause/reschedule
  in its middle (`Desugarer/PlusCal.lean`'s module doc; unlike `if`/`while`/`either`, which *do*
  allow nested labels, extracted into their own blocks). -/
  | nestedLabel (pos : SourceSpan)
  /-- A `while` statement appears inside a `with` body, at any nesting depth. The PlusCal manual
  (§3.2.6) lists this as its own, unconditional restriction, independent of `nestedLabel` above:
  a `while` is illegal inside `with` even with no label of its own anywhere near it — `with`'s
  one-atomic-step semantics never allows resuming mid-loop, and (per §3.2.4) a `while` always
  needs a label to loop back to, which `with` can never provide. -/
  | whileInWith (pos : SourceSpan)
  /-- A `while` statement is not immediately preceded by a real, user-written label. The PlusCal
  manual (§3.2.4/§3.7) states "a while statement must be labeled" unconditionally — this compiler
  does **not** auto-insert a label the way real PlusCal's opt-in `-label` translator flag would;
  matching real PlusCal's *default* (no-flag) behavior, an unlabelled `while` is rejected outright
  rather than silently fixed, confirmed with the project owner after an earlier draft of this
  desugarer auto-synthesized a fresh label here instead. -/
  | whileNotLabelled (pos : SourceSpan)
  /-- A statement following an `if`/`either` that contains a labelled statement or a `goto`
  anywhere within it is not itself labelled. The PlusCal manual (§3.2.2/§3.2.3) requires this
  unconditionally — real PlusCal's own default (no `-label`) behavior rejects a program that
  omits it rather than silently inserting one, and this compiler matches that rather than
  auto-synthesizing a continuation label (a correction from an earlier draft, alongside
  `whileNotLabelled` above — both found by the same deliberate cross-check against the manual). -/
  | notFollowedByLabel (pos : SourceSpan)
  /-- A statement writes into a variable that is currently bound by an enclosing `with` (at any
  nesting depth) — either an `assign` targeting it directly (`with x = e { x := 9 }`) or a
  `receive` whose target `Ref` is it (`with x = e { receive(c, x) }`, which writes the received
  value into `x` the same way `assign` writes into its target). A `with`-bound name is a local
  binding to a fixed value for the duration of its body, not a process variable — it was never
  declared in `variables` and has no state to update, so writing to it is meaningless the same
  way assigning to a TLA⁺ `LET`-bound name would be, regardless of whether the `with` used `=`
  or `∈`. -/
  | withBoundVarWritten (pos : SourceSpan) (name : String)
  /-- An annotation-carrying slot only accepts specific kinds of annotation (`@type` at
  `CONSTANTS`/`VARIABLES`/`channels`/`fifos` entries, operator/function signatures,
  quantifier/`CHOOSE` binders, and record-literal field values; `@mailbox` only immediately
  before a `process`; `@parameter` only on a `∈`-initialized process-local `variable`), but a
  different kind was found there — a real annotation, correctly captured at a real call site,
  just attached to the wrong specific role within it (§5.1's annotation-placement
  prerequisite; distinct from a merely-superfluous annotation with no consuming site nearby
  at all, which is out of scope, `PLAN.md` §9.13). -/
  | wrongAnnotationKindAtSite (pos : SourceSpan) (found : String) (expected : String)
  /-- Two or more annotations of the same kind found at one slot, for a kind whose *content*
  can actually differ between instances (`@type`: two different types would be genuinely
  ambiguous, which one applies?; `@mailbox`: two different channels on one process, same
  problem) — not merely redundant. Content-*free* markers (`@parameter`) get a warning
  instead (`DesugarWarning.duplicateParameterAnnotation`), not this error, since there's
  nothing to actually disagree about. -/
  | duplicateAnnotation (pos : SourceSpan) (kind : String)

instance : CompilerDiagnostic DesugarError String where
  isError := true
  posOf
    | .misplacedAt pos
    | .gotoNotInTailPosition pos
    | .unlabelledStatement pos
    | .nestedLabel pos
    | .whileInWith pos
    | .whileNotLabelled pos
    | .notFollowedByLabel pos
    | .withBoundVarWritten pos _
    | .wrongAnnotationKindAtSite pos _ _
    | .duplicateAnnotation pos _ => pos
  msgOf
    | .misplacedAt _ => "Unexpected '@' outside 'EXCEPT' construct."
    | .gotoNotInTailPosition _ => "'goto' may not be followed by further unlabelled statements."
    | .unlabelledStatement _ => "Statement is not preceded by a label."
    | .nestedLabel _ => "A label may not appear inside a 'with' block."
    | .whileInWith _ => "A 'while' statement may not appear inside a 'with' block."
    | .whileNotLabelled _ => "A 'while' statement must be immediately preceded by a label."
    | .notFollowedByLabel _ => "This statement must be labelled, since it follows an 'if'/'either' containing a label or 'goto'."
    | .withBoundVarWritten _ name => s!"'{name}' is bound by an enclosing 'with' and cannot be written to."
    | .wrongAnnotationKindAtSite _ found expected => s!"'{found}' is not valid here; only '{expected}' is expected at this position."
    | .duplicateAnnotation _ kind => s!"Only one '{kind}' annotation is allowed per binder."

/-- Non-fatal issues found while desugaring — collected out-of-band (mirroring
`Parser_/Common.lean`'s `ParserWarning`/`ParserWarningM`) rather than emitted immediately,
since `-W`/`-Wno-<name>` suppression is a CLI-driver concern. -/
inductive DesugarWarning : Type
  /-- A `@parameter` marker repeated on the same variable. Unlike `@type`/`@mailbox`,
  `@parameter` carries no content of its own to disagree about — a second one changes
  nothing, so it's a warning, not `DesugarError.duplicateAnnotation`. -/
  | duplicateParameterAnnotation (pos : SourceSpan)
  deriving Repr, Inhabited, BEq

/-- The `-W<name>`/`-Wno-<name>` name a given warning is filtered under. -/
def DesugarWarning.name : DesugarWarning → String
  | .duplicateParameterAnnotation _ => "duplicate-parameter"

instance : CompilerDiagnostic DesugarWarning String where
  isError := false
  posOf | .duplicateParameterAnnotation pos => pos
  msgOf | .duplicateParameterAnnotation _ => "Only one '@parameter' is needed per variable; the extra one(s) have no additional effect."
