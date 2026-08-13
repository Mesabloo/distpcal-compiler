module

public import WellFormedness.Errors
public import Core.TypedPlusCal.Syntax

public section

/-!
  Well-labelledness: every `goto` targets a label its process actually defines, or the reserved
  `"Done"`; `"Done"` itself is never a real, user-defined label.

  Assignment-conflict checking is **not** duplicated here — it already runs in
  `Desugarer/PlusCal.lean`'s `CorePlusCal.Algorithm.checkAssignConflicts`.
-/

variable {m : Type → Type} [Monad m] [MonadDiagnostic WellFormednessWarning WellFormednessError m]

/-- Collect every label a process defines across all its threads (`Process.threads`, the label
of every atomic block), rejecting a literal `"Done"` entry along the way — `"Done"` is a
reserved fallthrough target, never itself a real label. No better position exists for a
`redefinedDone` error than the labelled block's own terminal statement: labels are bare strings
paired with a block, not positioned nodes in their own right. -/
def TypedPlusCal.Process.labels (p : TypedPlusCal.Process) : m (List String) := do
  let perThread ← p.threads.mapM λ thread ↦
    thread.mapM λ (label, blk) ↦ do
      if label = "Done" then throw (.redefinedDone (posOf blk.end))
      else pure label
  return perThread.flatten

/-- Checks one `goto l` against `labels ∪ {"Done"}`. A per-node check with no context of its own
beyond `labels`, so it does no recursing — `ElaboratedPlusCal.Statement.forEachNode`
(`Core/TypedPlusCal/Syntax.lean`) supplies that. Every non-`goto` statement is vacuously fine. -/
def TypedPlusCal.Statement.checkGotoTarget {b} (labels : List String)
    (s : TypedPlusCal.Statement b) : m Unit :=
  match_source s with
  | .goto l, pos => unless labels.contains l ∨ l = "Done" do throw (.unknownLabel pos l)
  | _, _ => pure ()

/-- Well-labelledness over a whole algorithm: per process (labels are process-scoped, shared
across all of that process's threads, per `Process.labels` above), check every `goto` in every
thread of that same process. -/
def TypedPlusCal.Algorithm.checkLabelling (algo : TypedPlusCal.Algorithm) : m Unit :=
  algo.processes.forM λ p ↦ do
    let labels ← TypedPlusCal.Process.labels p
    ElaboratedPlusCal.Process.forStatements
      (ElaboratedPlusCal.Statement.forEachNode (TypedPlusCal.Statement.checkGotoTarget labels)) p

end
