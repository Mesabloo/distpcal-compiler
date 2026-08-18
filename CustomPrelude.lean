module

public meta import Batteries.CodeAction

public meta import Aesop

public meta import Mathlib.Tactic.ApplyAt
public meta import Mathlib.Tactic.Conv
public meta import Mathlib.Tactic.Clean
public meta import Mathlib.Tactic.SimpRw
public meta import Mathlib.Tactic.Monotonicity
-- NOTE: do not import `Mathlib.Tactic.DeriveTraversable`, as it creates instances whose name
-- are not scoped in the current namespace.
public meta import Extra.Mathlib.Tactic.DeriveTraversable
public meta import Mathlib.Tactic.FindSyntax
public meta import Batteries.Tactic.SeqFocus
public meta import Mathlib.Tactic.DefEqTransformations
public meta import Mathlib.Tactic.GuardGoalNums

public meta import Mathlib.Util.WhatsNew
public meta import Mathlib.Util.Delaborators
public meta import Mathlib.Util.Superscript
public meta import Mathlib.Util.AssertNoSorry

public meta import Mathlib.Tactic.Linter
public meta import Mathlib.Tactic.Linter.UnusedTacticExtension

public meta import LeanSearchClient



#allow_unused_tactic! guardGoalNums Lean.Parser.Tactic.change



-- `Functor.mapConst` ships without notation of its own.
infixl:100 " <$ " => Functor.mapConst

/-- `discard e` is a synonym for `let _ ← e` in a `do` block. -/
macro "discard " e:term : doElem => `(doElem| Functor.discard ($e))

open Lean Parser in
public meta def default := leading_parser
  atomic ("(" >> nonReservedSymbol "default" >> " := ") >> withoutPosition termParser >> ")" >> ppSpace

open Lean in
/--
  A shorthand to indicate at runtime that something has not been implemented yet.
  A `(default := e)` can be given as first argument to indicate the value to be returned, when
  either no `Inhabited` instance exists for the return type, or one exists but returns a
  nonsensical value for this purpose.
 -/
macro:lead withPosition("todo!") dflt:(default)? t:(term)? : term => do
  let f : TSyntax `term → MacroM (TSyntax `term) ← Option.elimM (pure dflt) (pure pure)
    -- Structural destructure instead of `` `(default| (default := $e)) `` quotation-matching,
    -- which needs an extra meta-eval capability on the matched value that direct indexing avoids.
    λ stx ↦
      let e : TSyntax `term := ⟨stx.raw[3]⟩
      pure λ x ↦ `(term| let _ : Inhabited (type_of% $e) := ⟨$e⟩; $x:term)
  let msg : TSyntax `term ← Option.elimM (pure t) `(term| "Something has not yet been done")
    λ msg ↦ `(term| "TODO: " ++ $msg)
  f =<< `(term| panic! $msg)

namespace Lean.Parser.Tactic
  /-- `erwa` is to `erw` what `rwa` is to `rw`. -/
  macro "erwa " c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
    `(tactic| (rw $[$(getConfigItems c)]* (transparency := .default) $s:rwRuleSeq $(loc)?; assumption))

  -- TODO(split-using): rename during elaboration, at `split`'s own `intron` site, instead of
  -- renaming per goal afterwards.
  /-- A version of `split` that also renames the hypotheses introduced. -/
  macro "split " loc:(location)? " using " names:sepBy1((ppSpace colGt binderIdent)+, "|") : tactic => do
    let renamings : Array (TSyntax `tactic) ← names.getElems.zipIdx.mapM λ ⟨xs, i⟩ ↦
      let ys : TSyntaxArray ``binderIdent := xs.raw.getArgs.map TSyntax.mk
      `(tactic| on_goal $(Lean.Syntax.mkNatLit i.succ) => rename_i $[$ys]*)
    `(tactic| (split $[$loc:location]?; $[$renamings];*))

  macro "injections " "with " names:(ppSpace colGt binderIdent)+ : tactic =>
    `(tactic| (injections; rename_i $names*))

  macro "iff_intro " x:ident ppSpace y:ident : tactic => `(tactic| refine Iff.intro (λ $x ↦ ?_) (λ $y ↦ ?_))

  macro "iff_rintro " x:rintroPat ppSpace y:rintroPat : tactic => `(tactic| (apply Iff.intro; (on_goal 2 => rintro $y); (on_goal 1 => rintro $x)))

  /-- Like `trans`, but generates the subgoal in the other order. -/
  macro "trans'" : tactic => `(tactic| (trans; swap))

  -- `seq_focus`'s own notation, respelled as `t <;> [t₁ | t₂]`.
  @[inherit_doc Batteries.Tactic.seq_focus]
  macro:1 t:tactic " <;> " "[" ts:sepBy(tactic, " | ") "]" : tactic => `(tactic| $t <;> [$[$ts];*])

  section
    open Lean Elab Term Meta Tactic

    declare_syntax_cat range_selector
    syntax num : range_selector
    syntax num "-" num : range_selector
    declare_syntax_cat tac_selector
    /-- Select multiple ranges of subgoals. -/
    syntax (range_selector),+ : tac_selector
    /-- Select all the subgoals. -/
    syntax "all" : tac_selector

    /-- Select the subgoals onto which to apply a given tactic sequence, Rocq style. -/
    syntax tac_selector ": " tacticSeq : tactic

    meta def selectGoals (stx : TSyntax `tac_selector) (mvarIds : List MVarId) : MetaM ((List MVarId) × (List MVarId)) :=
      match stx with
        | `(tac_selector|all) => return (mvarIds,[])
        | `(tac_selector| $[$r:range_selector],* ) => do
          let mut set := Std.HashSet.emptyWithCapacity
          for r in r do
            match r with
              | `(range_selector|$n:num) => set := set.insert n.getNat
              | `(range_selector|$n₁:num - $n₂:num) => for n in [n₁.getNat:n₂.getNat+1] do set := set.insert n
              | _ => throwUnsupportedSyntax
          return mvarIds.zipIdx 1 |>.partitionMap λ (mvar, i) ↦ if i ∈ set then .inl mvar else .inr mvar
        | _ => throwUnsupportedSyntax

    elab_rules : tactic
      | `(tactic| $select:tac_selector : $t:tacticSeq) => do
        let mvarIds ← getUnsolvedGoals
        let (mvarIds,unselectedMVarIds) ← selectGoals select mvarIds
        let mut mvarIdsNew := unselectedMVarIds
        let mut abort := false
        for mvarId in mvarIds.reverse do
          setGoals [mvarId]
          let saved ← saveState
          abort ← Tactic.tryCatch
            (do
              evalTactic t
              pure abort)
            (λ ex ↦ do
              if (← read).recover then
                logException ex
                let msgLog ← Core.getMessageLog
                saved.restore
                Core.setMessageLog msgLog
                admitGoal mvarId
                pure true
              else
                throw ex)
          mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
        if abort then
          throwAbortTactic
        setGoals mvarIdsNew

    open Conv in
    /-- Select the subgoals onto which to apply a given `conv` sequence, Rocq style. -/
    macro sel:tac_selector ": " s:convSeq : conv =>
      `(conv| tactic' => $sel:tac_selector : conv' => $s)
  end
end Lean.Parser.Tactic
