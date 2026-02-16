import Batteries.CodeAction

import Aesop

import Mathlib.Tactic.Conv
import Mathlib.Tactic.Clean
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Monotonicity
-- TODO: when upgrading lean
-- import Mathlib.Tactic.ByCases
-- NOTE: do not import `Mathlib.Tactic.DeriveTraversable`, as it creates instances whose name
-- are not scoped in the current namespace.
import Extra.Mathlib.Tactic.DeriveTraversable
import Mathlib.Tactic.FindSyntax
-- import Mathlib.Tactic.LiftLets
-- import Mathlib.Tactic.ExtractLets
import Batteries.Tactic.SeqFocus

import Mathlib.Util.WhatsNew
import Mathlib.Util.Delaborators
import Mathlib.Util.Superscript
import Mathlib.Util.AssertNoSorry

import Mathlib.Tactic.Linter

import LeanSearchClient

-- Somehow this is not in the notations for functors??
infixl:100 " <$ " => Functor.mapConst

/-- `discard e` is a synonym for `let _ ← e` in a `do` block. -/
macro "discard " e:term : doElem => `(doElem| Functor.discard ($e))

open Lean Parser in
private def default := leading_parser
  atomic ("(" >> nonReservedSymbol "default" >> " := ") >> withoutPosition termParser >> ")" >> ppSpace

open Lean in
/--
  A shorthand to indicate at runtime that something has not been implemented yet.
  A `(default := e)` can be given as first argument to indicate the value to be returned, in case either
  - no `Inhabited` instance exists for the return type and it would be boring to make one just for this; or
  - an `Inhabited` instance exists but returns a non-sensical value for the current purpose.
 -/
macro:lead withPosition("todo!") dflt:(default)? t:(term)? : term => do
  let f : TSyntax `term → MacroM (TSyntax `term) ← Option.elimM (pure dflt) (pure pure)
    λ | `(default| (default := $e)) => pure λ x ↦ `(term| let _ : Inhabited (type_of% $e) := ⟨$e⟩; $x:term)
      | _ => Macro.throwUnsupported
  let msg : TSyntax `term ← Option.elimM (pure t) `(term| "Something has not yet been done")
    λ msg ↦ `(term| "TODO: " ++ $msg)
  f =<< `(term| panic! $msg)

namespace Lean.Parser.Tactic
  /-- `erwa` is to `erw` what `rwa` is to `rw`. -/
  macro "erwa " c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
    `(tactic| (rw $[$(getConfigItems c)]* (transparency := .default) $s:rwRuleSeq $(loc)?; assumption))

  -- ideally, we would copy-paste the elab of `split` and plug our vars at the `intron` site
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

  -- The syntax proposed by `seq_focus` is horrendous!
  @[inherit_doc Batteries.Tactic.seq_focus]
  macro:1 t:tactic " <;> " "[" ts:sepBy(tactic, " | ") "]" : tactic => `(tactic| $t <;> [$[$ts];*])

  section
    -- Thanks for this, Arthur

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

    def selectGoals (stx : TSyntax `tac_selector) (mvarIds : List MVarId) : MetaM ((List MVarId) × (List MVarId)) :=
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
          --return mvarIds.zipIdx 1 |>.foldl (init := ([],[])) (fun (acc₁,acc₂) (mvar,i) => if i ∈ set then (mvar::acc₁,acc₂) else (acc₁,mvar::acc₂))
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
            (fun ex => do
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

/-
----------------------------------------
---- Tests
----------------------------------------

private example : Nat := todo!
private example : Nat := todo! "implement"
private example : Nat := todo! (default := 0) "implement but return 0 for now"

private example {a : Nat} : match a with | 0 => True | _ => True := by
  split using n | n _ <;> try trivial
private example {a : Nat} (h : match a with | 0 => False | _ => False) : False := by
  split at h using n | n _ <;> assumption

private inductive Foo where
  | a | b | c | d | e

private example (x : Foo) : Nat := by
  cases x
  1-3 : have n := 3
        induction n
        all: first | assumption | exact 0
  all : exact 2
-/
