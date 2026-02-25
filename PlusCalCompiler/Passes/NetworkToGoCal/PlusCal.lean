import PlusCalCompiler.NetworkPlusCal.Syntax
import PlusCalCompiler.GoCal.Syntax
import Mathlib.Data.List.AList
import Extra.AList
import Extra.Prod
import Batteries.Data.HashMap

/-! # Compilation from Guarded PlusCal to a subset of Go


-/

namespace NetworkPlusCal
  open CoreTLAPlus

  macro "chan_from_name!" t:term : term => `(term| s!"{$t}_")
  macro "thread!" "(" t:term ", " t':term ")" : term => `(term| s!"thread_{$t}_{$t'}")
  macro "rx_thread!" "(" t:term ", " t':term ", " t'':term ")" : term => `(term| s!"thread_{$t}_{$t'}_{$t''}")
  macro "either_mutex!" : term => `(term| "either_mutex")
  macro "cancel!" : term => `(term| "cancel")
  macro "chan!" "(" t:term ")" : term => `(term| s!"chan_{$t}")

  def AtomicBranch.freeVars (B : AtomicBranch Typ (Expression Typ)) : List String :=
    let ⟨bound, free⟩ := B.precondition.elim ⟨[], []⟩ getFreeVars
    let ⟨_, free'⟩ := getFreeVars B.action -- NOTE: this block should not contain `bound` variables
    free' \ bound ∪ free
    where
      getFreeVars {b b' : Bool} (B : Block (Statement Typ (Expression Typ) b) b') : List String × List String := Id.run do
        let mut bound : List String := []
        let mut free : List String := []

        let f : {b : Bool} → Statement Typ (Expression Typ) b false → List String × List String
          | true, .await e => ⟨[], e.freeVars⟩
          | true, .let x _ _ e => ⟨[x], e.freeVars⟩
          | false, .assign ref e => ⟨[], ref.freeVars Expression.freeVars ∪ e.freeVars⟩
          | false, .multicast chan bs e => ⟨[], []⟩
          | false, .send chan e => ⟨[], chan.freeVars Expression.freeVars \ [chan.name] ∪ e.freeVars⟩
          | false, .assert e => ⟨[], e.freeVars⟩
          | false, .print e => ⟨[], e.freeVars⟩
          | false, .skip => ⟨[], []⟩

        for S in B.begin do
          let ⟨bound', free'⟩ := f S
          bound := bound ++ bound'
          free := free ++ free'

        match b', b, B.last with
        | false, _, S =>
          let ⟨bound', free'⟩ := f S
          bound := bound ++ bound'
          free := free ++ free'
        | true, false, .goto _ => pure ()

        return ⟨bound, free⟩

  /--
    Compiles a single branch of an atomic `either` into a block of GoCal statements with the same semantics.
  -/
  def AtomicBranch.toGoCal (label : String) (i : Nat) (B : AtomicBranch Typ (Expression Typ)) (vars : List (String × Typ × Expression Typ)) : GoCal.Function Typ (Expression Typ) GoCal.Typ.initArgs :=
    let (condsVars, conds) : List (String × Typ) × List _ := match B.precondition with
      | none => ([], [])
      | some B => B.toList.foldr (init := ([], [])) λ S (vars, B) ↦ match_source S with
        | NetworkPlusCal.Statement.await e, pos => (vars, (.assign ⟨"cont", []⟩ (.infix (.var "cont") .«∧» e) @@ pos) :: B)
        | NetworkPlusCal.Statement.let x τ «=|∈» e, pos =>
          /-
            FIXME: how do we solve the following problem?

            ```
            with x ∈ 1..10;
            await x = 3;
            print x;
            \* ...
            ```

            This block is always enabled, and `x` will always be `3` after the precondition (meaning `print` will always output `3`).
            How do we handle such case where the value chosen by `with` actually depends on the `await`s that are after?
            Randomly select a value until one satisfies the remainder of the precondition?
          -/
          (vars.concat (x, τ), if «=|∈» then sorry else (.assign ⟨x, []⟩ e @@ pos) :: B)

    let todo : List (GoCal.Statement Typ (Expression Typ) GoCal.Typ.initArgs) := compileBlock B.action.begin

    let next : GoCal.Statement Typ (Expression Typ) GoCal.Typ.initArgs := match_source B.action.last with
      | .goto "Done", pos => .send (.var "done") (.record []) @@ pos
      | .goto l, pos => .assign ⟨"_", []⟩ (.opcall (.var l) (.var "self" :: .var "done" :: vars.map λ ⟨v, _, _⟩ ↦ .var (chan_from_name! v))) @@ pos

    let toLock := B.freeVars ∩ vars.map Prod.fst |>.eraseDups
    let allVars : List (String × Typ) := toLock.filterMap λ v ↦ do
      let ⟨τ, _⟩ ← vars.lookup v
      match τ with
      | .int | .str | .bool | .record _ | .tuple _ | .seq _ | .set _ | .function _ _ => return (v, τ)
      | _ => failure

    let lockAll :=
      toLock.map λ v ↦ GoCal.Statement.receive (.var (chan_from_name! v)) ⟨v, []⟩
    let unlockAll :=
      toLock.map λ v ↦ GoCal.Statement.send (.var (chan_from_name! v)) (.var v)

    {
      name := s!"{label}_{i}"
      params :=
        ⟨"self", .address⟩ ::
        ⟨"done", .channel (.record [])⟩ ::
        vars.map λ ⟨v, τ, _⟩ ↦ ⟨chan_from_name! v, .channel τ⟩
      returnType := [.bool]
      body :=
        .make "cont" .bool (.some <| .bool true) ::
        -- Declare variables first
        ((allVars ++ condsVars).map λ ⟨v, τ⟩ ↦ match h : τ with
              | .int | .str | .bool => .make v τ (h ▸ .none)
              | .record _ | .tuple _ | .seq _ | .set _ => .make v τ (h ▸ [])
              | .function _ _ => .make v τ (h ▸ .inr [])
              | .var _ | .const _ | .operator _ _ | .channel _ | .address => panic! "Invalid variable type") ++
        lockAll ++ conds ++ [
          .if (.var "cont") (todo ++ [
            .go [next]
          ]) []
        ] ++ unlockAll ++ [
          .return [.var "cont"]
        ]
    }
  where
    compileBlock (B : List (Statement Typ (Expression Typ) false false)) : List (GoCal.Statement Typ (Expression Typ) GoCal.Typ.initArgs) := do
      match_source ← B with
      | .skip, _ => []
      | .print e, pos => [.print e @@ pos]
      | .assert e, pos => [.if (.prefix .«¬» e) [.panic (.str s!"Expression '{e}' evaluated to 'false'!") @@ pos] []]
      | .assign ref e, pos =>
        -- TODO: handle indices (transform into tuples)
        let ref' := { name := ref.name, args := [] : GoCal.LHS _ }
        [.assign ref' e @@ pos]
      | .send chan e, pos =>
        let _ : Inhabited (List (GoCal.Statement Typ (Expression Typ) GoCal.Typ.initArgs)) := ⟨[.panic (.str "send not implemented") @@ pos]⟩
        todo! "compile send to go"
          -- [.send pos _ e]
      | .multicast chan bs e, pos =>
        let _ : Inhabited (List (GoCal.Statement Typ (Expression Typ) GoCal.Typ.initArgs)) := ⟨[.panic (.str "multicast not implemented") @@ pos]⟩
        todo! "compile multicast to go"

  def AtomicBlock.toGoCal (B : NetworkPlusCal.AtomicBlock Typ (Expression Typ)) (vars : List (String × Typ × Expression Typ)) : List (GoCal.Function Typ (Expression Typ) GoCal.Typ.initArgs) :=
    let label := B.label
    let fn := B.branches.zipIdx.foldl (init := []) λ branches ⟨B, i⟩ ↦ branches.concat (B.toGoCal label i vars, i)

    -- let calls := fn.map λ ⟨name, _, _, _⟩ ↦
    --   GoCal.Statement.go [
    --     .assign ⟨"_", []⟩ <|
    --       .opcall (.var name) (.var "self" :: /-.var default cancel! ::-/ .var either_mutex! :: .var "done" :: vars.map λ ⟨v, _, _⟩ ↦ .var v)
    --   ]

    fn.map Prod.fst |>.concat {
      name := label
      params := ⟨"self", .address⟩ :: ⟨"done", .channel (.record [])⟩ :: vars.map λ ⟨v, τ, _⟩ ↦ ⟨v, .channel τ⟩
      returnType := [.record []]
      body := [
        .make "cont" .bool (.some <| .bool true),
        .while (.var "cont") [
          .switch (.opcall (.var "Rand") [.nat fn.length.repr]) (
            fn.map λ ⟨⟨name, _, _, _⟩, i⟩ ↦
              .case [.nat i.repr] [
                .assign ⟨"cont", []⟩ <| .opcall (.var name) (.var "self" :: .var "done" :: vars.map λ ⟨v, _, _⟩ ↦ .var v)
              ]
          )
        ],

        -- .make either_mutex! (.channel (.record [])) (.inl (.some ⟨1⟩)),
        -- .send (.var either_mutex!) (.record []),
        -- --.make default cancel! (.channel (.record [])) (.inl .none)
      ] ++ [
        .return [.record []]
      ]
    }

  def Thread.toGoCal (procName : String) (i : Nat) (vars : List (String × Typ × Expression Typ)) : Thread Typ (Expression Typ) → List (GoCal.Function Typ (Expression Typ) GoCal.Typ.initArgs)
    -- NOTE: in practice, this should never happen as all threads must contain at least one block (the parser should enforce it)
    | .code [] => [{
      name := thread!(procName, i)
      params := ⟨"self", .address⟩ :: vars.map λ ⟨v, τ, _⟩ ↦ ⟨s!"{v}_", .channel τ⟩
      returnType := [.channel (.record [])]
      body := [
        .make "done" (.channel (.record [])) (.inl (.some ⟨1⟩)),
        .go [.send (.var "done") (.record [])],
        .return [.var "done"]
      ]
    }]
    | .code blocks@h:(_ :: _) =>
      let blocks' := blocks >>= λ B ↦ B.toGoCal vars

      blocks'.concat {
        name := thread!(procName, i)
        params := ⟨"self", .address⟩ :: vars.map λ ⟨v, τ, _⟩ ↦ ⟨s!"{v}_", .channel τ⟩
        returnType := [.channel (.record [])]
        body := [
          .make "done" (.channel (.record [])) (.inl (.some ⟨1⟩)),
          .assign ⟨"_", []⟩ <|
            .opcall (.var <| blocks.head (List.ne_nil_iff_exists_cons.mpr ⟨_, _, h⟩) |>.label) (.var "self" :: .var "done" :: vars.map λ ⟨v, _, _⟩ ↦ .var (chan_from_name! v)),
          .return [.var "done"]
        ]
      }
    | .rx chan rx' τ inbox => match h : τ with
      | .var _ | .const _ | .operator _ _ | .channel _ | .address => panic! "Cannot receive some datatypes through channels"
      | .int | .str | .bool | .record _ | .tuple _ | .seq _ | .set _ | .function _ _ =>
        [{
          name := rx_thread!(procName, rx', inbox)
          params := ⟨"self", .address⟩ :: ⟨chan.name, .channel τ⟩ :: vars.map λ ⟨v, τ, _⟩ ↦ ⟨s!"{v}_", .channel τ⟩
          returnType := [.record []]
          body := [
            .make rx' τ (match h' : τ with
              | .int | .str | .bool => none
              | .record _ | .tuple _ | .seq _ | .set _ => []
              | .function _ _ => .inr []
              | .var _ | .const _ | .operator _ _ | .channel _ => nomatch h, h'),
            .make inbox (.seq τ) [],
            .make "ok" .bool (.some <| .bool true),
            .while (.var "ok") [
              .select [
                .receive [rx', "ok"] (by rfl) (.var chan.name) [
                  .if (.var "ok") [
                    .receive (.var s!"{inbox}_") ⟨inbox, []⟩,
                    .send (.var s!"{inbox}_") (.opcall (.var "Append") [.var inbox, .var rx'])
                  ] []
                ]
              ]
            ],
            .return [.record []]
          ]
        }]

  /--
    Generates a function named after the process `P` that:
    - takes all local variables which are declared `@parameter`, and put them inside cells (glorified channels);
    - asserts that all parameters have sensical values as indicated by the specification;
    - initializes all the other local variables to their given values inside cells;
    - initializes channels for receiving values from the outside world, if needed;
    - initializes a channel `Done` which marks whenever the process as a whole has finished executing;
    - calls all its threads one by one;
    - waits for all `done` channels of all individual threads to be sent a message, then sends a message to its `Done` channel;
    - returns `Done` and all the channels used to communicate with the outside world.
  -/
  def Process.toGoCal (P : Process Typ (Expression Typ)) : List (GoCal.Function Typ (Expression Typ) GoCal.Typ.initArgs) :=
    let ⟨vars, params⟩ := P.locals.toList.partitionMap λ
      | ⟨v, τ, true, e⟩ => .inl (v, τ, e)
      | ⟨v, τ, false, e⟩ => .inr (v, τ, e)

    let fns := P.threads.zipIdx >>= λ ⟨T, i⟩ ↦ T.toGoCal P.name i (vars ++ params)

    let ⟨threads, channels⟩ := P.threads.zipIdx.partitionMap
      λ | ⟨.code _, i⟩ => .inl (thread!(P.name, i))
        | ⟨.rx _ rx τ inbox, _⟩ => .inr (rx_thread!(P.name, rx, inbox), τ)

    let calls : List (GoCal.Statement Typ (Expression Typ) GoCal.Typ.initArgs) := threads.map λ v ↦ .make s!"done_{v}" (.channel (.record [])) <| .inr <|
      .opcall (.var v) (.var "self" :: (vars ++ params).map λ ⟨v, _, _⟩ ↦ .var v)
    let calls' : List (GoCal.Statement Typ (Expression Typ) GoCal.Typ.initArgs) := channels.map λ ⟨v, _⟩ ↦ .assign ⟨"_", []⟩ <|
      .opcall (.var v) <| .var "self" :: .var chan!(v) :: ((vars ++ params).map λ ⟨v, _, _⟩ ↦ .var v)

    fns.concat {
      name := P.name
      params := ⟨"self", .address⟩ :: params.map (λ ⟨v, τ, _⟩ ↦ ⟨chan_from_name! v, τ⟩)
      returnType := .channel (.record []) :: channels.map λ ⟨_, τ⟩ ↦ .channel τ
      body :=
        .make "done" (.channel (.record [])) (.inl (.some ⟨1⟩)) ::
        -- Initialize local variables
        (vars >>= λ ⟨v, τ, e⟩ ↦ [ .make v (.channel τ) (.inl (.some ⟨1⟩)), .send (.var v) e]) ++
        -- Box parameters
        (params >>= λ ⟨v, τ, e⟩ ↦ [
            .if (.prefix .«¬» <| .infix (.var <| chan_from_name! v) .«∈» e) [.panic (.str s!"Parameter '{v}' does not satisfy condition '{v} ∈ {e}'.")] [],
            .make v (.channel τ) (.inl (.some ⟨1⟩)),
            .send (.var v) (.var <| chan_from_name! v) ]) ++
        -- Initialize channels to receive message from the outside world
        (channels.map λ ⟨v, τ⟩ ↦ .make chan!(v) (.channel τ) (.inl (some ⟨10000⟩))) ++
        -- Call every thread in parallel
        calls ++
        -- Also call every receiving thread in parallel, if there are any
        calls' ++
        [
          -- Wait until all threads have finished, then signal the `done` channel
          .go <|
            threads.map (λ v ↦ .receive (.var s!"done_{v}") ⟨"_", []⟩) ++
            [
              .send (.var "done") (.record [])
            ],
          -- Return the `done` channel, as well as all channels that are used to communicate with the outside world
          .return <| .var "done" :: channels.map λ ⟨v, _⟩ ↦ .var chan!(v)
        ]
    }

  def Algorithm.toGoCal (a : Algorithm Typ (Expression Typ)) : List (GoCal.Function Typ (Expression Typ) GoCal.Typ.initArgs) :=
    a.procs.foldl (init := []) λ funcs proc ↦ funcs ++ proc.toGoCal
