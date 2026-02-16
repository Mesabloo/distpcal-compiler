import PlusCalCompiler.GuardedPlusCal.Syntax
import PlusCalCompiler.NetworkPlusCal.Syntax
import PlusCalCompiler.CoreTLAPlus.Syntax
import CustomPrelude
import Mathlib.Data.List.Sigma
import Extra.List

namespace GuardedPlusCal
  def Ref.substOf.{u} (pos : SourceSpan) (r : Ref.{u} (CoreTLAPlus.Expression CoreTLAPlus.Typ)) (e : CoreTLAPlus.Expression.{u} CoreTLAPlus.Typ) : String × CoreTLAPlus.Expression.{u} CoreTLAPlus.Typ :=
    if r.args.isEmpty then
      ⟨r.name, e⟩
    else
      ⟨r.name, .except pos (.var pos r.name) [⟨.inl <$> r.args, e⟩]⟩

  def Thread.toNetwork.{u} (inbox procName : String) (chans : Std.HashMap.{_, u} String (CoreTLAPlus.Typ.{u} × List.{u} (CoreTLAPlus.Expression CoreTLAPlus.Typ))) (T : GuardedPlusCal.Thread.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) :
        Id (List.{u} (String × CoreTLAPlus.Typ.{u} × Bool × (CoreTLAPlus.Expression.{u} CoreTLAPlus.Typ)) × List (NetworkPlusCal.Thread.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) × NetworkPlusCal.Thread.{u} SurfaceTLAPlus.Typ (CoreTLAPlus.Expression SurfaceTLAPlus.Typ)) := do
    let mut newLocals : List (String × CoreTLAPlus.Typ.{u} × Bool × (CoreTLAPlus.Expression.{u} CoreTLAPlus.Typ)) := []
    let mut rxs : List.{u} (NetworkPlusCal.Thread CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []
    let mut blocks : List.{u} (NetworkPlusCal.AtomicBlock CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []

    for ⟨label, branches⟩ in T do
      let mut branches' : List.{u} (NetworkPlusCal.AtomicBranch CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []

      for branch in branches do
        let ⟨precond, newInstrs, rxs'⟩ ← processPrecondition branch.precondition
        let B := processBlock branch.action

        if let ⟨x, τ, c⟩ :: _ := rxs' then
          newLocals := newLocals.concat ⟨inbox ++ procName, .seq τ, true, .seq default []⟩

          if let none := rxs.find? λ | .rx c' _ _ _ => c == c' | _ => false then
            rxs := rxs.concat <| .rx c x τ (inbox ++ procName)
        branches' := branches'.concat ⟨precond, newInstrs.foldr (init := B) NetworkPlusCal.Block.cons⟩

      blocks := blocks.concat ⟨label, branches'⟩

    return ⟨newLocals, rxs, .code blocks⟩
  where
    processPrecondition : Option (Block (Statement.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true) false)
                        → Id (Option (NetworkPlusCal.Block (NetworkPlusCal.Statement.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true) false) × List (NetworkPlusCal.Statement.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) false false) × List (Σ (_ : String), CoreTLAPlus.Typ.{u} × NetworkPlusCal.ChanRef.{u} (CoreTLAPlus.Expression CoreTLAPlus.Typ)))
      | none => pure (none, [], [])
      | some B => do
        -- NOTE: when `i : Nat`, this provokes a universe unification error
        -- <https://github.com/leanprover/lean4/issues/8119#issue-3022011542>
        let mut i : ULift.{u} Nat := ⟨0⟩
        let mut newInstrs : List (SourceSpan × GuardedPlusCal.Ref.{u} (CoreTLAPlus.Expression CoreTLAPlus.Typ) × (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []
        let mut rxs : List ((_ : String) × CoreTLAPlus.Typ.{u} × GuardedPlusCal.ChanRef.{u} (CoreTLAPlus.Expression CoreTLAPlus.Typ)) := []
        let mut B' : Option (NetworkPlusCal.Block (NetworkPlusCal.Statement.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true) false) := none

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
          let S' ← match S with
            | .await pos e =>
              pure <| .await pos <| (newInstrs.map λ ⟨p, r, e⟩ ↦ r.substOf p e).foldr (init := e) λ ⟨k, e'⟩ e ↦ e.replace k e'
            | .let pos x τ «=|∈» e =>
              pure <| .let pos x τ «=|∈» <| (newInstrs.map λ ⟨p, r, e⟩ ↦ r.substOf p e).foldr (init := e) λ ⟨k, e'⟩ e ↦ e.replace k e'
            | .receive pos chan ref => match Prod.fst <$> chans.find? chan.name with
              | .some (.channel τ) | .some (.function _ (.channel τ)) =>
                newInstrs := newInstrs ++ [
                  ⟨pos, ref, .opcall default (.var default "Head") [.var default (inbox ++ procName)]⟩,
                  ⟨pos, ⟨inbox ++ procName, []⟩, .opcall default (.var default "Tail") [.var default (inbox ++ procName)]⟩
                ]
                i := ⟨i.down + 1⟩
                rxs := rxs.concat ⟨s!"rx_{i.down}", τ, chan⟩

                pure <| .await pos (.infix pos (.opcall default (.var default "Len") [.var default (inbox ++ procName)]) .«>» (.nat pos s!"{i.down - 1}"))
              | .some τ =>
                -- return `await FALSE` in case of wrong type, which actually should never happen
                let _ : Inhabited (NetworkPlusCal.Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true false) := ⟨.await pos <| .bool pos false⟩
                pure <| panic! s!"Channel {chan.name} has wrong type {repr τ}"
              | .none =>
                -- return `await FALSE` in case of wrong type, which actually should never happen
                let _ : Inhabited (NetworkPlusCal.Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) true false) := ⟨.await pos <| .bool pos false⟩
                pure <| panic! s!"Channel {chan.name} not found in algorithm"

          B' := match B' with
            | none => some (NetworkPlusCal.Block.end S')
            | some B' => some (NetworkPlusCal.Block.concat B' S')

        return (B', (λ ⟨p, r, e⟩ ↦ .assign p r e) <$> newInstrs, rxs)


    -- This one is basically the identity transformation between two types with the same shape.
    -- However, it may not be safe to just use `unsafeCast` in this case, I don't know.
    processBlock (B : Block (Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) false) true) : NetworkPlusCal.Block (NetworkPlusCal.Statement CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) false) true := {
      begin := B.begin.map λ
        | .skip pos => .skip pos
        | .print pos e => .print pos e
        | .assert pos e => .assert pos e
        | .send pos chan e => .send pos chan e
        | .multicast pos chan bs e => .multicast pos chan bs e
        | .assign pos ref e => .assign pos ref e

      last := match B.last with
        | .goto pos l => .goto pos l
    }

  def Process.toNetwork.{u} (inbox : String) (chans : Std.HashMap String (CoreTLAPlus.Typ.{u} × List (CoreTLAPlus.Expression.{u} CoreTLAPlus.Typ))) (P : Process.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) : NetworkPlusCal.Process.{u} CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) :=
    let threadss := P.threads.map <| Id.run <| Thread.toNetwork.{u} inbox P.name chans
    let (locals, threads, codes) := bimap List.flatten (bimap List.flatten id) threadss.unzip₃

    {
      name := P.name
      mailbox := P.mailbox
      locals := P.locals.mergeWith (λ _ v _ ↦ v) (Batteries.HashMap.ofList locals).inner
      threads := threads ++ codes
    }

  def Algorithm.toNetwork (inbox : String) (a : GuardedPlusCal.Algorithm CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ)) : NetworkPlusCal.Algorithm CoreTLAPlus.Typ (CoreTLAPlus.Expression CoreTLAPlus.Typ) where
    name := a.name
    channels := a.channels
    fifos := a.fifos
    procs := a.procs.map <| Process.toNetwork inbox (a.channels.mergeWith (λ _ v _ ↦ v) a.fifos)
