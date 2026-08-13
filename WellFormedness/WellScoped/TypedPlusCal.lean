module

public import WellFormedness.Errors
public import Core.TypedPlusCal.Syntax

public section

/-!
  Well-scopedness, the **executable** check over `TypedPlusCal.Algorithm` (run by the driver):
  every name is fresh in the scope it's declared in — no duplicate names within one flat
  declaration list, and no name shadowing an already-in-scope one from an enclosing scope. Scope
  classes: global (`Algorithm.globalState`), process-local (`Process.localState`), and
  block-local (`with`'s own binder) — "channel" isn't a separate namespace from "global"/
  "process-local" here (`variables`/`channels`/`fifos` already coexist in one flat scope per
  `Declarations` value), so it's folded into whichever of those two applies.

  This is only the "no duplicate names / no shadowing" half — "every reference resolves to a
  declared name" is redundant with type checking's own success and isn't re-derived here.

  The `Prop`-side counterpart for each later `PlusCal` stage (`WellFormedness.WellScoped.
  CorePlusCal`, `.GuardedPlusCal`) lives in its own file, modeled on the same scope-class shape
  but not executed and not invoked by anything here.
-/

/-- Every name a `Declarations` value binds, paired with the best position available to report
against it — the entry's own initializer/index expression if one exists, `SourceSpan.placeholder`
otherwise (a bare `variables x;` with no initializer, or an unindexed channel, carries no
position of its own to point at; matches `requireAnnotation SourceSpan.placeholder`'s own
fallback elsewhere in this codebase). `variables` ++ `channels` ++ `fifos`, matching
`checkPlusCalDeclarations`'s own binding order (`Elaborator/PlusCal.lean`). -/
private def TypedPlusCal.Declarations.namesWithPos (d : TypedPlusCal.Declarations) : List (String × SourceSpan) :=
  d.variables.map (λ (x, _, _, init) ↦ (x, init.elim SourceSpan.placeholder (posOf ·.2)))
  ++ d.channels.map (λ (x, _, idxs) ↦ (x, idxs.head?.elim SourceSpan.placeholder posOf))
  ++ d.fifos.map (λ (x, _, idxs) ↦ (x, idxs.head?.elim SourceSpan.placeholder posOf))

variable {m : Type → Type} [Monad m] [MonadDiagnostic WellFormednessWarning WellFormednessError m]

/-- Rejects the first repeated name within one flat list — `duplicateName` at *that* repeat's
own position, not the first occurrence's. -/
private def checkNoDuplicates : List (String × SourceSpan) → m Unit
  | [] => pure ()
  | (n, _) :: rest =>
    match rest.find? (·.1 == n) with
    | some (_, pos) => throw (.duplicateName pos n)
    | none => checkNoDuplicates rest

/-- Rejects any of `names` already present in `inScope` — `shadowedName` at the shadowing
entry's own position. -/
private def checkNoShadow (inScope : List String) (names : List (String × SourceSpan)) : m Unit :=
  names.forM λ (n, pos) ↦ do
    if inScope.contains n then throw (.shadowedName pos n)

/-- Walks every `with` binder reachable from `s`, checking it against `inScope` and extending
it for the sub-block. No other statement introduces a PlusCal-visible name.

Keeps its own recursion rather than using `ElaboratedPlusCal.Statement.forEachNode` — `inScope`
grows at each `with` and only for that binder's own sub-block, so the check and the recursion
can't be separated the way `Labelling.lean`'s can. -/
partial def TypedPlusCal.Statement.checkWellScoped {b} (inScope : List String)
    (s : TypedPlusCal.Statement b) : m Unit :=
  match_source s with
  | .if _ B₁ B₂, _ => do
    ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) B₁
    ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) B₂
  | .either branches, _ =>
    ElaboratedPlusCal.Branches.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) branches
  | .while _ B, _ => ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) B
  | .with x _ _ _ B, pos => do
    if inScope.contains x then throw (.shadowedName pos x)
    ElaboratedPlusCal.Block.forStatements (TypedPlusCal.Statement.checkWellScoped (x :: inScope)) B
  | .goto _, _ | .skip, _ | .print _, _ | .assign _, _ | .await _, _ | .assert _, _
  | .receive _ _ _, _ | .send _ _, _ | .multicast _ _, _ => pure ()

/-- Well-scopedness over a whole algorithm: global declarations fresh among themselves; each
process's own local declarations fresh among themselves and not shadowing a global one; every
`with` binder inside a process's threads fresh against global ++ that process's own locals ++
whatever outer `with`s it's nested in. -/
def TypedPlusCal.Algorithm.checkWellScoped (algo : TypedPlusCal.Algorithm) : m Unit := do
  let globalNames := TypedPlusCal.Declarations.namesWithPos algo.globalState
  checkNoDuplicates globalNames
  for p in algo.processes do
    let localNames := TypedPlusCal.Declarations.namesWithPos p.localState
    checkNoDuplicates localNames
    checkNoShadow (globalNames.map Prod.fst) localNames
    let inScope := globalNames.map Prod.fst ++ localNames.map Prod.fst
    ElaboratedPlusCal.Process.forStatements (TypedPlusCal.Statement.checkWellScoped inScope) p

end
