module

import CustomPrelude

/-! Tests for `linter.fugue.packUnpack`. -/

/--
warning: `obtain ⟨…⟩ : T := ⟨…⟩` packs and unpacks in one line — write the `have`s

Note: This linter can be disabled with `set_option linter.fugue.packUnpack false`
-/
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : True := by
  obtain ⟨x, y⟩ : p ∧ q := ⟨hp, hq⟩
  trivial

-- `obtain … := by …` is fine — the ascription is the tactic block's goal.
#guard_msgs in
example (p q : Prop) (hp : p) (hq : q) : True := by
  obtain ⟨x, y⟩ : p ∧ q := by refine ⟨?_, ?_⟩ <;> assumption
  trivial
