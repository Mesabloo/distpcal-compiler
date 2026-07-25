module

public import Common.Errors
public import Core.TypedTLAPlus.Syntax

public section

/-! The well-formedness pass's diagnostics: one named error variant per violation. All checks
are hard errors — no `WellFormednessWarning` type is needed. -/

/-- The well-formedness pass's errors. -/
inductive WellFormednessError : Type
  /-- A `goto` targets a label that doesn't exist anywhere in its process (`"Done"` always
  counts as existing). -/
  | unknownLabel (pos : SourceSpan) (label : String)
  /-- `"Done"` used as a real, user-defined label. -/
  | redefinedDone (pos : SourceSpan)
  /-- A name is declared more than once in a scope where every name must be fresh. -/
  | duplicateName (pos : SourceSpan) (name : String)
  /-- A name shadows an already-in-scope name, in a scope where shadowing isn't allowed. -/
  | shadowedName (pos : SourceSpan) (name : String)
  /-- A channel-shaped value appears inside an ordinary expression — only `send`/`receive`'s
  channel argument and `multicast`'s target may reference one. No `name` field: the offending
  subexpression need not be a bare variable (e.g. `IF b THEN ch1 ELSE ch2`), so `τ` (the
  Channel-shaped type actually found) is the only thing always available, matching
  `TCError.notAChannelType`'s own shape. -/
  | channelInExpression (pos : SourceSpan) (τ : TypedTLAPlus.Typ)
  /-- A `variables`/`with`-declared name (algorithm-level, process-level, or `with`-bound) has
  a Channel-shaped type — the `channels`/`fifos` forms are the only legitimate way to declare
  one. -/
  | channelTypedVariable (pos : SourceSpan) (name : String)
  /-- A process's own `localState.channels`/`.fifos` isn't empty — defense-in-depth; the parser
  already guarantees this today. -/
  | nonEmptyLocalChannels (pos : SourceSpan) (process : String)
  /-- The PlusCal algorithm itself declares algorithm-level `variables` (shared mutable state
  across all processes) — only `fifos` is allowed at that level. -/
  | globalPlusCalVariable (pos : SourceSpan) (name : String)
  /-- A reference inside the algorithm resolves to a TLA⁺ module-level `VARIABLE` — `definedIn`
  names the module that actually declared it (own or, via `EXTENDS`, a dependency's). -/
  | globalTLAPlusVariable (pos : SourceSpan) (name : String) (definedIn : String)
  /-- A temporal formula or action operator (`[]`, `<>`, `ENABLED`, `UNCHANGED`, `'`, `^+`,
  `^*`, `^#`) appears somewhere the algorithm's expressions reach — directly in a statement
  (`path := []`) or transitively, through an operator/function call chain (`path` the sequence
  of operator names traversed to get there, innermost first). -/
  | bareTemporalOrAction (pos : SourceSpan) (op : String) (path : List String)
  /-- An unbounded quantifier (`\A x : P`/`\E x : P`/`CHOOSE x : P`, no domain) appears
  somewhere the algorithm's expressions reach — same direct-vs-transitive `path` shape as
  `bareTemporalOrAction`. -/
  | unboundedQuantifier (pos : SourceSpan) (path : List String)
  deriving Repr, Inhabited, BEq

/-- Renders a direct-vs-transitive `path` breadcrumb (innermost first) as "directly in a
statement" or "reachable via `f` → `g` → …", shared by `bareTemporalOrAction`/
`unboundedQuantifier`'s messages. -/
private def renderPath : List String → String
  | [] => "directly in a statement"
  | path@(_ :: _) => "reachable via " ++ String.intercalate " → " (path.map λ op ↦ s!"`{op}`")

@[no_expose]
instance : CompilerDiagnostic WellFormednessError String where
  isError := true
  code
    | .unknownLabel .. => Diagnostics.unknownLabel.code
    | .redefinedDone _ => Diagnostics.redefinedDone.code
    | .duplicateName .. => Diagnostics.duplicateName.code
    | .shadowedName .. => Diagnostics.shadowedName.code
    | .channelInExpression .. => Diagnostics.channelInExpression.code
    | .channelTypedVariable .. => Diagnostics.channelTypedVariable.code
    | .nonEmptyLocalChannels .. => Diagnostics.nonEmptyLocalChannels.code
    | .globalPlusCalVariable .. => Diagnostics.globalPlusCalVariable.code
    | .globalTLAPlusVariable .. => Diagnostics.globalTLAPlusVariable.code
    | .bareTemporalOrAction .. => Diagnostics.bareTemporalOrAction.code
    | .unboundedQuantifier .. => Diagnostics.unboundedQuantifier.code
  posOf
    | .unknownLabel pos _ => pos
    | .redefinedDone pos => pos
    | .duplicateName pos _ => pos
    | .shadowedName pos _ => pos
    | .channelInExpression pos _ => pos
    | .channelTypedVariable pos _ => pos
    | .nonEmptyLocalChannels pos _ => pos
    | .globalPlusCalVariable pos _ => pos
    | .globalTLAPlusVariable pos _ _ => pos
    | .bareTemporalOrAction pos _ _ => pos
    | .unboundedQuantifier pos _ => pos
  msgOf
    | .unknownLabel _ label => s!"`goto {label}` targets a label that doesn't exist in this process."
    | .redefinedDone _ => "`Done` is a reserved label and cannot be redefined."
    | .duplicateName _ name => s!"`{name}` is declared more than once in this scope."
    | .shadowedName _ name => s!"`{name}` shadows an already-in-scope name."
    | .channelInExpression _ τ => s!"`{τ}` is a channel-shaped type — a channel may only appear as `send`'s/`receive`'s channel argument or `multicast`'s target, never inside an ordinary expression."
    | .channelTypedVariable _ name => s!"`{name}` has a channel-shaped type — declare it with `channels`/`fifos` instead of `variables`/`with`."
    | .nonEmptyLocalChannels _ process => s!"Process `{process}` declares local `channels`/`fifos` — only the algorithm's own `fifos` may declare channels."
    | .globalPlusCalVariable _ name => s!"`{name}` is an algorithm-level `variables` entry — shared mutable state across processes isn't allowed; use `fifos` for shared channels, or a per-process `variables` entry for local state."
    | .globalTLAPlusVariable _ name definedIn => s!"`{name}` is a `VARIABLE` declared in module `{definedIn}` — a Distributed PlusCal algorithm may not reference module-level `VARIABLE`s."
    | .bareTemporalOrAction _ op path => s!"`{op}` is a temporal/action operator, {renderPath path} — not allowed anywhere in a Distributed PlusCal algorithm."
    | .unboundedQuantifier _ path => s!"Unbounded quantifier (no domain), {renderPath path} — not allowed anywhere in a Distributed PlusCal algorithm."

end
