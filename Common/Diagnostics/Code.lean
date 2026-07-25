module

meta import CustomPrelude
import Mathlib.Data.String.Defs

public section

/-!
  Diagnostic codes: the stable identity of a diagnostic, independent of its wording.

  `rustc`-shaped — `E0042`, `W0003` — because that shape is already what a user expects to be
  able to look up (`fugue explain E0042`), grep a build log for, or write into a regression
  fixture's expectations. Wording changes freely; a code never does.
-/

/-- Whether a diagnostic stops the compile. The letter a code starts with. -/
inductive Severity : Type
  /-- Fatal: `E….` -/
  | error
  /-- Non-fatal: `W…`, and suppressible via `-Wno-<name>`. -/
  | warning
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable, Ord

/-- The letter this severity's codes start with. -/
def Severity.letter : Severity → Char
  | .error => 'E'
  | .warning => 'W'

/-- A diagnostic's code: a severity and a four-digit number, e.g. `E0042`.

A structure over `Fin 10000` rather than a `String`, so a malformed code cannot be constructed in
the first place — every code that exists renders in the one canonical form, and `explain`'s
argument either parses into this type or was never a code at all. -/
structure DiagnosticCode : Type where
  /-- Error or warning. -/
  severity : Severity
  /-- The number, unique within the whole compiler (not per severity, not per stage). -/
  number : Fin 10000
  -- `Ord` is lexicographic on `(severity, number)`, i.e. every `E…` before every `W…`. Nothing
  -- reads meaning into the order; it exists so that a list of codes has *one* spelling — a
  -- warning tally that printed in hash order would differ run to run for no reason.
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable, Ord

namespace DiagnosticCode

/-- `E0042`: the letter, then the number padded to four digits. -/
def toString (c : DiagnosticCode) : String :=
  let n := ToString.toString c.number.val
  s!"{c.severity.letter}{String.replicate (4 - n.length) '0'}{n}"

instance : ToString DiagnosticCode := ⟨DiagnosticCode.toString⟩

/-- Parse a code back from its printed form; `none` if `s` is not one. Strict: the letter must be
`E`/`W`, and exactly four digits must follow — `E42` and `banana` are both simply not codes. -/
def ofString? (s : String) : Option DiagnosticCode := do
  match s.toList with
  | letter :: digits =>
    let severity ← match letter with
      | 'E' => some Severity.error
      | 'W' => some Severity.warning
      | _ => none
    guard (digits.length == 4)
    guard (digits.all Char.isDigit)
    let n ← (String.ofList digits).toNat?
    if h : n < 10000 then some { severity, number := ⟨n, h⟩ } else none
  | [] => none

end DiagnosticCode

end
