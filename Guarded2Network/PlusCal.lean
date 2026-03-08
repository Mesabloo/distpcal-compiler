import Core.GuardedPlusCal.Syntax
import Core.NetworkPlusCal.Syntax
import Core.TypedSetTheory.Syntax
import CustomPrelude
import Mathlib.Data.List.Sigma
import Extra.List

namespace GuardedPlusCal
  open TypedSetTheory (Expression Typ)

  def Ref.substOf.{u} (r : Ref.{u} Typ (Expression Typ)) (e : Expression.{u} Typ) : String × Expression.{u} Typ :=
    if r.args.isEmpty then
      ⟨r.name, e⟩
    else
      ⟨r.name, .except (.var r.name r.τ) [⟨.inl <$> r.args, e⟩]⟩

  def Thread.toNetwork (inbox procName : String) (chans : Std.HashMap.{_, 0} String (Typ × List (Expression Typ))) (T : GuardedPlusCal.Thread.{0} Typ (Expression Typ)) :
      Id (List.{0} (String × Typ × Bool × (Expression Typ)) × List (NetworkPlusCal.Thread Typ (Expression Typ)) × NetworkPlusCal.Thread.{0} Typ (Expression Typ)) := do
    let mut newLocals : List (String × Typ × Bool × (Expression Typ)) := []
    let mut rxs : List (NetworkPlusCal.Thread Typ (Expression Typ)) := []
    let mut blocks : List (NetworkPlusCal.AtomicBlock Typ (Expression Typ)) := []

    for ⟨label, branches⟩ in T do
      let mut branches' : List (NetworkPlusCal.AtomicBranch Typ (Expression Typ)) := []

      for branch in branches do
        let ⟨precond, newInstrs, rxs'⟩ ← processPrecondition branch.precondition
        let B := processBlock branch.action

        if let ⟨x, τ, c⟩ :: _ := rxs' then
          newLocals := newLocals.concat ⟨inbox ++ procName, .seq τ, true, .seq [] τ⟩

          if let none := rxs.find? λ | .rx c' _ _ _ => c == c' | _ => false then
            rxs := rxs.concat <| .rx c x τ (inbox ++ procName)
        branches' := branches'.concat ⟨precond, newInstrs.foldr (init := B) NetworkPlusCal.Block.cons⟩

      blocks := blocks.concat ⟨label, branches'⟩

    return ⟨newLocals, rxs, .code blocks⟩
  where
    processPrecondition : Option (Block (Statement.{0} Typ (Expression Typ) true) false)
                        → Id (Option (NetworkPlusCal.Block (NetworkPlusCal.Statement.{0} Typ (Expression Typ) true) false) × List (NetworkPlusCal.Statement.{0} Typ (Expression Typ) false false) × List.{0} (Σ (_ : String), Typ × NetworkPlusCal.ChanRef Typ (Expression Typ)))
      | none => pure (none, [], [])
      | some B => do
        let mut i : Nat := 0
        let mut newInstrs : List (GuardedPlusCal.Ref.{0} Typ (Expression Typ) × (Expression.{0} Typ)) := []
        let mut rxs : List ((_ : String) × Typ × GuardedPlusCal.ChanRef Typ (Expression Typ)) := []
        let mut B' : Option (NetworkPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) true) false) := none

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
                  ⟨ref, .opcall (.var "Head" (.operator [.seq τ] τ)) [.var (inbox ++ procName) (.seq τ)]⟩,
                  ⟨⟨inbox ++ procName, .seq τ, []⟩, .opcall (.var "Tail" (.operator [.seq τ] (.seq τ))) [.var (inbox ++ procName) (.seq τ)]⟩
                ]
                i := i + 1
                rxs := rxs.concat ⟨s!"rx_{i}", τ, chan⟩

                pure <| .await (.infix (.opcall (.var "Len" (.operator [.seq τ] .int)) [.var (inbox ++ procName) (.seq τ)]) .«>» (.nat s!"{i - 1}")) @@ pos
              | .some τ =>
                -- return `await FALSE` in case of wrong type, which actually should never happen
                let _ : Inhabited (NetworkPlusCal.Statement Typ (Expression Typ) true false) := ⟨.await (.bool false) @@ pos⟩
                pure <| panic! s!"Channel {chan.name} has wrong type {repr τ}"
              | .none =>
                -- return `await FALSE` in case of wrong type, which actually should never happen
                let _ : Inhabited (NetworkPlusCal.Statement Typ (Expression Typ) true false) := ⟨.await (.bool false) @@ pos⟩
                pure <| panic! s!"Channel {chan.name} not found in algorithm"

          B' := match B' with
            | none => some (NetworkPlusCal.Block.end S')
            | some B' => some (NetworkPlusCal.Block.concat B' S')

        return (B', (λ ⟨r, e⟩ ↦ .assign r e) <$> newInstrs, rxs)


    -- This one is basically the identity transformation between two types with the same shape.
    -- However, it may not be safe to just use `unsafeCast` in this case, I don't know.
    processBlock (B : Block (Statement Typ (Expression Typ) false) true) : NetworkPlusCal.Block (NetworkPlusCal.Statement Typ (Expression Typ) false) true := {
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

  def Process.toNetwork (inbox : String) (chans : Std.HashMap.{_, 0} String (Typ × List (Expression Typ))) (P : Process.{0} Typ (Expression Typ)) : NetworkPlusCal.Process.{0} Typ (Expression Typ) :=
    let threadss := P.threads.map <| Id.run <| Thread.toNetwork inbox P.name chans
    let (locals, threads, codes) := bimap List.flatten (bimap List.flatten id) threadss.unzip₃

    {
      name := P.name
      mailbox := P.mailbox
      locals := P.locals.mergeWith (λ _ v _ ↦ v) (Batteries.HashMap.ofList locals).inner
      threads := threads ++ codes
    }

  def Algorithm.toNetwork (inbox : String) (a : GuardedPlusCal.Algorithm.{0} Typ (Expression Typ)) : NetworkPlusCal.Algorithm Typ (Expression Typ) where
    name := a.name
    channels := a.channels
    fifos := a.fifos
    procs := a.procs.map <| Process.toNetwork inbox (a.channels.mergeWith (λ _ v _ ↦ v) a.fifos)
