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

instance : CompilerDiagnostic DesugarError String where
  isError := true
  posOf
    | .misplacedAt pos
    | .gotoNotInTailPosition pos
    | .unlabelledStatement pos
    | .nestedLabel pos
    | .whileInWith pos
    | .whileNotLabelled pos
    | .notFollowedByLabel pos => pos
  msgOf
    | .misplacedAt _ => "Unexpected '@' outside 'EXCEPT' construct."
    | .gotoNotInTailPosition _ => "'goto' may not be followed by further unlabelled statements."
    | .unlabelledStatement _ => "Statement is not preceded by a label."
    | .nestedLabel _ => "A label may not appear inside a 'with' block."
    | .whileInWith _ => "A 'while' statement may not appear inside a 'with' block."
    | .whileNotLabelled _ => "A 'while' statement must be immediately preceded by a label."
    | .notFollowedByLabel _ => "This statement must be labelled, since it follows an 'if'/'either' containing a label or 'goto'."
