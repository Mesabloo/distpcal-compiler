module

public meta import Lean.Elab.Tactic
public meta import Batteries.Tactic.PermuteGoals

/-!
# `split … using`

`split`, followed by a per-goal `rename_i` so the hypotheses it introduces arrive named.
-/

open Lean Lean.Parser Lean.Parser.Tactic

namespace CustomPrelude.Tactic

-- TODO(split-using): rename during elaboration, at `split`'s own `intron` site, instead of
-- renaming per goal afterwards.
/-- A version of `split` that also renames the hypotheses introduced. -/
macro "split " loc:(location)? " using " names:sepBy1((ppSpace colGt binderIdent)+, "|") : tactic => do
  let renamings : Array (TSyntax `tactic) ← names.getElems.zipIdx.mapM λ ⟨xs, i⟩ ↦
    let ys : TSyntaxArray ``binderIdent := xs.raw.getArgs.map TSyntax.mk
    `(tactic| on_goal $(Lean.Syntax.mkNatLit i.succ) => rename_i $[$ys]*)
  `(tactic| (split $[$loc:location]?; $[$renamings];*))

end CustomPrelude.Tactic
