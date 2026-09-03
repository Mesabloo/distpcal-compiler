module

public meta import CustomPrelude.Tactic.Erwa
public meta import CustomPrelude.Tactic.SplitUsing
public meta import CustomPrelude.Tactic.Injections
public meta import CustomPrelude.Tactic.IffIntro
public meta import CustomPrelude.Tactic.Trans
public meta import CustomPrelude.Tactic.SeqFocusBracket
public meta import CustomPrelude.Tactic.Selector

/-!
# Project tactics

The project's own tactics, one module per tactic. `CustomPrelude` pulls this in with
`public meta import`, so a `meta import CustomPrelude` reaches all of them.
-/
