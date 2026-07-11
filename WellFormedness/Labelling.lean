import WellFormedness.Errors
import Core.TypedPlusCal.Syntax

/-!
  Well-labelledness (`PLAN.md` §5.2a): every `goto` targets a label its process actually
  defines, or the reserved `"Done"`; `"Done"` itself is never a real, user-defined label.

  Assignment-conflict checking is **not** duplicated here — it already runs in
  `Desugarer/PlusCal.lean`'s `CorePlusCal.Algorithm.checkAssignConflicts`, ahead of its own
  phase slot. The mutual-recursion shape below mirrors that function's own style.
-/

/-- Collect every label a process defines across all its threads (`Process.threads`, the label
of every atomic block), rejecting a literal `"Done"` entry along the way — `"Done"` is a
reserved fallthrough target, never itself a real label. No better position exists for a
`redefinedDone` error than the labelled block's own terminal statement: labels are bare strings
paired with a block, not positioned nodes in their own right. -/
def TypedPlusCal.Process.labels {m : Type → Type} [Monad m] [MonadExceptOf WellFormednessError m]
    (p : TypedPlusCal.Process) : m (List String) := do
  let perThread ← p.threads.mapM λ thread ↦
    thread.mapM λ (label, blk) ↦ do
      if label = "Done" then throw (.redefinedDone (posOf blk.end))
      else pure label
  return perThread.flatten

mutual
  /-- Walks every `goto l` reachable from `s`, checking `l` against `labels ∪ {"Done"}`. -/
  partial def TypedPlusCal.Statement.checkGotoTargets {b} {m : Type → Type} [Monad m]
      [MonadExceptOf WellFormednessError m] (labels : List String) (s : TypedPlusCal.Statement b) : m Unit :=
    match_source s with
    | .goto l, pos => unless labels.contains l ∨ l = "Done" do throw (.unknownLabel pos l)
    | .if _ B₁ B₂, _ => do
      TypedPlusCal.Block.checkGotoTargets labels B₁
      TypedPlusCal.Block.checkGotoTargets labels B₂
    | .either branches, _ => TypedPlusCal.Branches.checkGotoTargets labels branches
    | .while _ B, _ => TypedPlusCal.Block.checkGotoTargets labels B
    | .with _ _ _ _ B, _ => TypedPlusCal.Block.checkGotoTargets labels B
    | .skip, _ | .print _, _ | .assign _, _ | .await _, _ | .assert _, _
    | .receive _ _ _, _ | .send _ _, _ | .multicast _ _, _ => pure ()

  partial def TypedPlusCal.Block.checkGotoTargets {b} {m : Type → Type} [Monad m]
      [MonadExceptOf WellFormednessError m] (labels : List String) (B : TypedPlusCal.Block b) : m Unit := do
    B.begin.forM (TypedPlusCal.Statement.checkGotoTargets labels)
    TypedPlusCal.Statement.checkGotoTargets labels B.end

  partial def TypedPlusCal.Branches.checkGotoTargets {b} {m : Type → Type} [Monad m]
      [MonadExceptOf WellFormednessError m] (labels : List String) : TypedPlusCal.Branches b → m Unit
    | .either B => TypedPlusCal.Block.checkGotoTargets labels B
    | .or B rest => do
      TypedPlusCal.Block.checkGotoTargets labels B
      TypedPlusCal.Branches.checkGotoTargets labels rest
end

/-- Well-labelledness over a whole algorithm: per process (labels are process-scoped, shared
across all of that process's threads, per `Process.labels` above), check every `goto` in every
thread of that same process. -/
def TypedPlusCal.Algorithm.checkLabelling {m : Type → Type} [Monad m]
    [MonadExceptOf WellFormednessError m] (algo : TypedPlusCal.Algorithm) : m Unit := do
  for p in algo.processes do
    let labels ← p.labels
    for thread in p.threads do
      for (_, blk) in thread do
        TypedPlusCal.Block.checkGotoTargets labels blk
