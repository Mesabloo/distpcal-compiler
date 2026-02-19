import PlusCalCompiler.GuardedPlusCal.Syntax
import PlusCalCompiler.NetworkPlusCal.Syntax
import PlusCalCompiler.CoreTLAPlus.Syntax
import CustomPrelude
import Mathlib.Data.List.Sigma
import Extra.List

namespace GuardedPlusCal
  def Ref.substOf.{u} (r : Ref.{u} (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (e : CoreTLAPlus.Expression.{u} CoreTLAPlus.Typ) : String × CoreTLAPlus.Expression.{u} CoreTLAPlus.Typ :=
    if r.args.isEmpty then
      ⟨r.name, e⟩
    else
      ⟨r.name, .except (.var r.name) [⟨.inl <$> r.args, e⟩]⟩

  def Thread.toNetwork (inbox procName : String) (chans : Std.HashMap.{_, 0} String (CoreTLAPlus.Typ × List (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (T : GuardedPlusCal.Thread.{0} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) :
      Id (List.{0} (String × CoreTLAPlus.Typ × Bool × (CoreTLAPlus.Expression CoreTLAPlus.Typ)) × List (NetworkPlusCal.Thread CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) × NetworkPlusCal.Thread.{0} SurfaceTLAPlus.Typ (CoreTLAPlus.Expression SurfaceTLAPlus.Typ)) := do
    let mut newLocals : List (String × CoreTLAPlus.Typ × Bool × (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []
    let mut rxs : List (NetworkPlusCal.Thread CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []
    let mut blocks : List (NetworkPlusCal.AtomicBlock CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []

    for ⟨label, branches⟩ in T do
      let mut branches' : List (NetworkPlusCal.AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []

      for branch in branches do
        let ⟨precond, newInstrs, rxs'⟩ ← processPrecondition branch.precondition
        let B := processBlock branch.action

        if let ⟨x, τ, c⟩ :: _ := rxs' then
          newLocals := newLocals.concat ⟨inbox ++ procName, .seq τ, true, .seq []⟩

          if let none := rxs.find? λ | .rx c' _ _ _ => c == c' | _ => false then
            rxs := rxs.concat <| .rx c x τ (inbox ++ procName)
        branches' := branches'.concat ⟨precond, newInstrs.foldr (init := B) NetworkPlusCal.Block.cons⟩

      blocks := blocks.concat ⟨label, branches'⟩

    return ⟨newLocals, rxs, .code blocks⟩
  where
    processPrecondition : Option (Block (Statement.{0} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true) false)
                        → Id (Option (NetworkPlusCal.Block (NetworkPlusCal.Statement.{0} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true) false) × List (NetworkPlusCal.Statement.{0} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) false false) × List.{0} (Σ (_ : String), CoreTLAPlus.Typ × NetworkPlusCal.ChanRef (CoreTLAPlus.Expression CoreTLAPlus.Typ)))
      | none => pure (none, [], [])
      | some B => do
        -- NOTE: when `i : Nat`, this provokes a universe unification error
        -- <https://github.com/leanprover/lean4/issues/8119#issue-3022011542>
        let mut i : Nat := 0
        let mut newInstrs : List (GuardedPlusCal.Ref.{0} (CoreTLAPlus.Expression CoreTLAPlus.Typ) × (CoreTLAPlus.Expression.{0} CoreTLAPlus.Typ)) := []
        let mut rxs : List ((_ : String) × CoreTLAPlus.Typ × GuardedPlusCal.ChanRef (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []
        let mut B' : Option (NetworkPlusCal.Block (NetworkPlusCal.Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true) false) := none

        /-
            A quick example:

            ```
            receive(c, x[0}]);
            await x[0] + y = 0;
            receive(c, y);
            await x[0] + y = 0;
            ```

            After the loop, We should obtain
            ```
            await Len(inbox) > 0;
            \* subst `x` with `[x EXCEPT ![0] = Head(inbox)]`
            await [x EXCEPT ![0] = Head(inbox)][0] + y = 0;
            await Len(inbox) > 1;
            \* subst `y` with `Head(Tail(inbox))`
            await [x EXCEPT ![0] = Head(inbox)][0] + Head(Tail(inbox)) = 0;

            x[0] := Head(inbox);
            inbox := Tail(inbox);
            y := Head(inbox);
            inbox := Tail(inbox);
            ```
        -/

        for S in B.begin.concat B.last do
          let pos := posOf S
          let S' ← match S with
            | .await e =>
              pure <| .await ((newInstrs.map λ ⟨r, e⟩ ↦ r.substOf e).foldr (init := e) λ ⟨k, e'⟩ e ↦ e.replace k e') @@ pos
            | .let x τ «=|∈» e =>
              pure <| .let x τ «=|∈» ((newInstrs.map λ ⟨r, e⟩ ↦ r.substOf e).foldr (init := e) λ ⟨k, e'⟩ e ↦ e.replace k e') @@ pos
            | .receive chan ref => match Prod.fst <$> chans.find? chan.name with
              | .some (.channel τ) | .some (.function _ (.channel τ)) =>
                newInstrs := newInstrs ++ [
                  ⟨ref, .opcall (.var "Head") [.var (inbox ++ procName)]⟩,
                  ⟨⟨inbox ++ procName, []⟩, .opcall (.var "Tail") [.var (inbox ++ procName)]⟩
                ]
                i := i + 1
                rxs := rxs.concat ⟨s!"rx_{i}", τ, chan⟩

                pure <| .await (.infix (.opcall (.var "Len") [.var (inbox ++ procName)]) .«>» (.nat s!"{i - 1}")) @@ pos
              | .some τ =>
                -- return `await FALSE` in case of wrong type, which actually should never happen
                let _ : Inhabited (NetworkPlusCal.Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true false) := ⟨.await (.bool false) @@ pos⟩
                pure <| panic! s!"Channel {chan.name} has wrong type {repr τ}"
              | .none =>
                -- return `await FALSE` in case of wrong type, which actually should never happen
                let _ : Inhabited (NetworkPlusCal.Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true false) := ⟨.await (.bool false) @@ pos⟩
                pure <| panic! s!"Channel {chan.name} not found in algorithm"

          B' := match B' with
            | none => some (NetworkPlusCal.Block.end S')
            | some B' => some (NetworkPlusCal.Block.concat B' S')

        return (B', (λ ⟨r, e⟩ ↦ .assign r e) <$> newInstrs, rxs)


    -- This one is basically the identity transformation between two types with the same shape.
    -- However, it may not be safe to just use `unsafeCast` in this case, I don't know.
    processBlock (B : Block (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) false) true) : NetworkPlusCal.Block (NetworkPlusCal.Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) false) true := {
      begin := B.begin.map λ S ↦ match_source S with
        | .skip, pos => .skip @@ pos
        | .print e, pos => .print e @@ pos
        | .assert e, pos => .assert e @@ pos
        | .send chan e, pos => .send chan e @@ pos
        | .multicast chan bs e, pos => .multicast chan bs e @@ pos
        | .assign ref e, pos => .assign ref e @@ pos

      last := match_source B.last with
        | .goto l, pos => .goto l @@ pos
    }

  def Process.toNetwork (inbox : String) (chans : Std.HashMap.{_, 0} String (CoreTLAPlus.Typ × List (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (P : Process.{0} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) : NetworkPlusCal.Process.{0} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) :=
    let threadss := P.threads.map <| Id.run <| Thread.toNetwork inbox P.name chans
    let (locals, threads, codes) := bimap List.flatten (bimap List.flatten id) threadss.unzip₃

    {
      name := P.name
      mailbox := P.mailbox
      locals := P.locals.mergeWith (λ _ v _ ↦ v) (Batteries.HashMap.ofList locals).inner
      threads := threads ++ codes
    }

  def Algorithm.toNetwork (inbox : String) (a : GuardedPlusCal.Algorithm.{0} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) : NetworkPlusCal.Algorithm CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) where
    name := a.name
    channels := a.channels
    fifos := a.fifos
    procs := a.procs.map <| Process.toNetwork inbox (a.channels.mergeWith (λ _ v _ ↦ v) a.fifos)
