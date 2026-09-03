module

import CustomPrelude

/-! Tests for `linter.fugue.firstParens`. -/

/--
warning: parentheses around `first` add nothing — `| pat => first` then the `|` branches under it

Note: This linter can be disabled with `set_option linter.fugue.firstParens false`
-/
#guard_msgs in
example (h : True ∨ True) : True := by
  rcases h with h | h
  · (first | rfl | exact h)
  · exact h

-- No parens is fine.
#guard_msgs in
example (h : True ∨ True) : True := by
  rcases h with h | h
  · first | rfl | exact h
  · exact h
