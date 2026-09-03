module

public meta import Batteries.Tactic.Trans
public meta import Batteries.Tactic.PermuteGoals

/-!
# `trans'`

`trans`, with its two subgoals produced in the opposite order.
-/

open Lean

namespace CustomPrelude.Tactic

/-- Like `trans`, but generates the subgoal in the other order. -/
macro "trans'" : tactic => `(tactic| (trans; swap))

end CustomPrelude.Tactic
