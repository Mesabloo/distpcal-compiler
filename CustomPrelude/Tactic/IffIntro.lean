module

public meta import Lean.Elab.Tactic
public meta import Batteries.Tactic.PermuteGoals

/-!
# `iff_intro` / `iff_rintro`

Build an `Iff` from its two directions, folding the introduction of each side's hypothesis into
the split — `constructor` followed by two `intro`s, in one tactic.
-/

open Lean Lean.Parser.Tactic

namespace CustomPrelude.Tactic

/-- Split an `Iff` goal and introduce one hypothesis on each side. -/
macro "iff_intro " x:ident ppSpace y:ident : tactic =>
  `(tactic| refine Iff.intro (λ $x ↦ ?_) (λ $y ↦ ?_))

/-- Split an `Iff` goal and `rintro` one pattern on each side. -/
macro "iff_rintro " x:rintroPat ppSpace y:rintroPat : tactic =>
  `(tactic| (apply Iff.intro; (on_goal 2 => rintro $y); (on_goal 1 => rintro $x)))

end CustomPrelude.Tactic
