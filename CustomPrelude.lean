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
public meta import Mathlib.Tactic.SimpIntro
public meta import Mathlib.Tactic.Set

public meta import Mathlib.Util.WhatsNew
public meta import Mathlib.Util.Delaborators
public meta import Mathlib.Util.Superscript
public meta import Mathlib.Util.AssertNoSorry

public meta import Mathlib.Tactic.Linter
public meta import Mathlib.Tactic.Linter.UnusedTacticExtension

public meta import LeanSearchClient

public meta import CustomPrelude.Linter

public meta import CustomPrelude.Tactic



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
    λ stx ↦ do
      let `(default| (default := $e)) := stx | unreachable!
      pure λ x ↦ `(term| let _ : Inhabited (type_of% $e) := ⟨$e⟩; $x:term)
  let msg : TSyntax `term ← Option.elimM (pure t) `(term| "Something has not yet been done")
    λ msg ↦ `(term| "TODO: " ++ $msg)
  f =<< `(term| panic! $msg)
