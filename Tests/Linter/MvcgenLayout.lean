module

import CustomPrelude
import Std.Do.WP

/-! Tests for `linter.fugue.mvcgenLayout`.

Each case runs `mvcgen` on the same one-loop program — inlined, because routing it through a
`def`/`abbrev` changes how `mvcgen` labels its VCs. -/

open Std.Do

-- Correct layout: `invariants` / `with` on their own lines, alternatives at the keyword column.
#guard_msgs in
example : ⦃⌜True⌝⦄ (do
    let mut acc := 0
    for i in [1, 2, 3] do
      acc := acc + i
    pure acc : ExceptT String (StateM Nat) Nat) ⦃⇓r => ⌜r ≥ 0⌝⦄ := by
  mvcgen
  invariants
  | inv1 => ⇓ _ _ => ⌜True⌝
  with
  | vc3 => omega

/--
warning: `mvcgen` alternative is indented past `with` — align it to the keyword's column

Note: This linter can be disabled with `set_option linter.fugue.mvcgenLayout false`
-/
#guard_msgs in
example : ⦃⌜True⌝⦄ (do
    let mut acc := 0
    for i in [1, 2, 3] do
      acc := acc + i
    pure acc : ExceptT String (StateM Nat) Nat) ⦃⇓r => ⌜r ≥ 0⌝⦄ := by
  mvcgen
  invariants
  | inv1 => ⇓ _ _ => ⌜True⌝
  with | vc3 => omega

/--
warning: `invariants` starts mid-line — give it its own line, like a `match`

Note: This linter can be disabled with `set_option linter.fugue.mvcgenLayout false`
-/
#guard_msgs in
example : ⦃⌜True⌝⦄ (do
    let mut acc := 0
    for i in [1, 2, 3] do
      acc := acc + i
    pure acc : ExceptT String (StateM Nat) Nat) ⦃⇓r => ⌜r ≥ 0⌝⦄ := by
  mvcgen invariants
  | inv1 => ⇓ _ _ => ⌜True⌝
  with
  | vc3 => omega

/--
warning: `mvcgen` alternative is indented past `invariants` — align it to the keyword's column

Note: This linter can be disabled with `set_option linter.fugue.mvcgenLayout false`
-/
#guard_msgs in
example : ⦃⌜True⌝⦄ (do
    let mut acc := 0
    for i in [1, 2, 3] do
      acc := acc + i
    pure acc : ExceptT String (StateM Nat) Nat) ⦃⇓r => ⌜r ≥ 0⌝⦄ := by
  mvcgen
  invariants
    | inv1 => ⇓ _ _ => ⌜True⌝
  with
  | vc3 => omega
