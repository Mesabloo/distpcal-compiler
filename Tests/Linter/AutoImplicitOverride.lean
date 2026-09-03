module

import CustomPrelude

/-! Tests for `linter.fugue.autoImplicitOverride`. -/

section
/--
warning: `autoImplicit` is off project-wide — write every implicit explicitly

Note: This linter can be disabled with `set_option linter.fugue.autoImplicitOverride false`
-/
#guard_msgs in
set_option autoImplicit true
end

-- Turning it off is fine.
#guard_msgs in
set_option autoImplicit false in
example : True := trivial
