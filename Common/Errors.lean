import Common.Position
import Mathlib.Data.String.Defs
import Colorized
import CustomPrelude

open Colorized (Colorized)

/-- Anything can be colorized if we ignore the annotations. -/
instance (priority := low) {α} : Colorized α where
  colorize _ _ := id
  style _ := id

class CompilerDiagnostic (ε : Type _) (α : outParam (Type _)) [Colorized α] where
  isError : Bool
  posOf : ε → SourceSpan
  msgOf : ε → α
  hintsOf : ε → List α := λ _ ↦ []

/-- `Colorized.color`, but a no-op when `enabled` is `false` (`-fno-color`, `PLAN.md` §2). Not
`private`: `Fugue.lean` reuses it for its `Built`/`Replayed` progress lines, not just here. -/
def colorizeIf {α} [Colorized α] (enabled : Bool) (c : Colorized.Color) (x : α) : α :=
  if enabled then Colorized.color c x else x

/-- `Colorized.style`, but a no-op when `enabled` is `false` (`-fno-color`, `PLAN.md` §2). Not
`private`: `Fugue.lean` reuses it too, for its `Built`/`Replayed`/`Failed` progress lines. -/
def styleIf {α} [Colorized α] (enabled : Bool) (s : Colorized.Style) (x : α) : α :=
  if enabled then Colorized.style s x else x

/-- Pretty basic error pretty printing. `colored := false` (driven by `-fno-color`) disables ANSI styling. -/
def CompilerDiagnostic.pretty {ε α : Type _} [Colorized α] [ToString α] [CompilerDiagnostic ε α] (err : ε) (source : List String.Slice) (colored : Bool := true) : String :=
  let header := if CompilerDiagnostic.isError ε then "error" else "warning"
  let color := if CompilerDiagnostic.isError ε then Colorized.Color.Red else .Yellow
  let headerPadding := String.replicate (header.length + 2) ' '
  let pos := CompilerDiagnostic.posOf err
  let n := pos.start.line
  let linePadding := String.replicate (n.repr.length + 2) ' '
  let line := source[n - 1]!
  let startCol := pos.start.col
  let endCol := if pos.end.line > n then line.length else pos.end.col
  let beginLine := line.take startCol
  let middleLine := line.drop startCol |>.take (endCol - startCol)
  let endLine := line.takeEnd (line.length - endCol)
  s!"{colorizeIf colored color <| styleIf colored .Bold s!"{header}:"} {toString (CompilerDiagnostic.msgOf err) |>.replace "\n" s!"\n{headerPadding}"}{String.join ((CompilerDiagnostic.hintsOf err).map λ s ↦ s!"\n{headerPadding}" ++ (toString s).replace "\n" s!"\n{headerPadding}")}
{linePadding}|
 {n} | {beginLine}{colorizeIf colored color middleLine}{endLine}
{linePadding}|{String.replicate (startCol + 1) ' '}{colorizeIf colored color <| String.replicate (endCol - startCol) '^'}"
