module

public import Core.CorePlusCal.Syntax

public section

/-!
  `CorePlusCal.WellScoped`, a **Prop**. Same scope-class shape as the executable check
  (`TypedPlusCal.Algorithm.checkWellScoped`), stated over the pre-`Elaborator`
  `CorePlusCal.Algorithm`: it is the form a preservation lemma is stated against, not something the
  executable check invokes.
-/

/-- Every name a `Declarations` value binds — the `Prop`-side counterpart of
`TypedPlusCal.Declarations.namesWithPos`, with no position (irrelevant to a `Prop`). -/
def CorePlusCal.Declarations.names {α β} (d : CorePlusCal.Declarations α β) : List String :=
  (d.variables.map (·.1)) ++ (d.channels.map (·.1)) ++ (d.fifos.map (·.1))

mutual
  /-- `s` introduces no shadowing/duplicate name, given `inScope` already holds — the `Prop`
  counterpart of `TypedPlusCal.Statement.checkWellScoped`. -/
  partial def CorePlusCal.Statement.WellScopedIn {α β b} (inScope : List String) :
      CorePlusCal.Statement α β b → Prop
    | .if _ B₁ B₂ => CorePlusCal.Block.WellScopedIn inScope B₁ ∧ CorePlusCal.Block.WellScopedIn inScope B₂
    | .either branches => CorePlusCal.Branches.WellScopedIn inScope branches
    | .while _ B => CorePlusCal.Block.WellScopedIn inScope B
    | .with x _ _ _ B => x ∉ inScope ∧ CorePlusCal.Block.WellScopedIn (x :: inScope) B
    | .goto _ | .skip | .print _ | .assign _ | .await _ | .assert _
    | .receive _ _ | .send _ _ | .multicast _ _ => True

  partial def CorePlusCal.Block.WellScopedIn {α β b} (inScope : List String) (B : CorePlusCal.Block α β b) : Prop :=
    (∀ s ∈ B.begin, CorePlusCal.Statement.WellScopedIn inScope s) ∧ CorePlusCal.Statement.WellScopedIn inScope B.end

  partial def CorePlusCal.Branches.WellScopedIn {α β b} (inScope : List String) :
      CorePlusCal.Branches α β b → Prop
    | .either B => CorePlusCal.Block.WellScopedIn inScope B
    | .or B rest => CorePlusCal.Block.WellScopedIn inScope B ∧ CorePlusCal.Branches.WellScopedIn inScope rest
end

/-- `p` has no duplicate name in any scope, and no name shadows an enclosing scope's — the
`Prop` counterpart of `TypedPlusCal.Algorithm.checkWellScoped`, over the pre-`Elaborator`
`CorePlusCal.Algorithm`. -/
def CorePlusCal.WellScoped {α β} (algo : CorePlusCal.Algorithm α β) : Prop :=
  algo.globalState.names.Nodup ∧
  ∀ p ∈ algo.processes,
    p.localState.names.Nodup ∧
    (∀ n ∈ p.localState.names, n ∉ algo.globalState.names) ∧
    ∀ thread ∈ p.threads, ∀ pair ∈ thread,
      CorePlusCal.Block.WellScopedIn (algo.globalState.names ++ p.localState.names) pair.2

end
