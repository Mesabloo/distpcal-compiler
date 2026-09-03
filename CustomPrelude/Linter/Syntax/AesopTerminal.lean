module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.aesopTerminal`

`aesop` is terminal or not used at all — a non-terminal `aesop` leaves whatever the search
stopped at, and later steps get written against that fixed order. A plain non-terminal `aesop`
already self-warns (`warnOnNonterminal := true` by default); this linter flags the escape
hatches: an `aesop (config := …)` that sets `warnOnNonterminal`, and a bare
`set_option aesop.warn.nonterminal false` (the one-command `… in` form is peeled off first).
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `aesop` terminal, or not at all. -/
register_option linter.fugue.aesopTerminal : Bool := {
  defValue := true
  descr := "flag the escapes that silence aesop's own non-terminal warning"
}

/-- Every `set_option aesop.warn.nonterminal false`, and every `aesop` whose config mentions
`warnOnNonterminal`. -/
def aesopTerminalCore : Syntax → Array Finding :=
  scan λ s ↦
    if isSetOption "nonterminal" "false" s then
      hit s m!"`set_option aesop.warn.nonterminal false` — make the `aesop` terminal instead"
    else if s.getKind == `Aesop.Frontend.Parser.aesopTactic
        && (s.find? (λ i ↦ identLast? i == some "warnOnNonterminal")).isSome then
      hit s m!"`aesop` config silences the non-terminal warning — make the `aesop` terminal instead"
    else #[]

/-- The `linter.fugue.aesopTerminal` linter. -/
def aesopTerminal : Linter where run := mkFugueLinter linter.fugue.aesopTerminal aesopTerminalCore

initialize addLinter aesopTerminal

end CustomPrelude.Linter
