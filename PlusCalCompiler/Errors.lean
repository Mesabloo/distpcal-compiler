import PlusCalCompiler.Position
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

/-- Pretty basic error pretty printing. -/
def CompilerDiagnostic.pretty {ε α : Type _} [Colorized α] [ToString α] [CompilerDiagnostic ε α] (err : ε) (source : List String.Slice) : String :=
  let header := if CompilerDiagnostic.isError ε then "error" else "warning"
  let color := if CompilerDiagnostic.isError ε then Colorized.Color.Red else .Yellow
  let headerPadding := String.replicate (header.length + 2) ' '
  let pos := CompilerDiagnostic.posOf err
  let n := pos.start.line
  let linePadding := String.replicate (n.repr.length + 2) ' '
  let line := source[n - 1]!
  let startCol := pos.start.col
  let endCol := if pos.end.line > n then line.length - 1 else pos.end.col
  let beginLine := line.take (startCol - 1)
  let middleLine := line.drop (startCol - 1) |>.take (endCol - startCol + 1)
  let endLine := line.takeRight (line.length - endCol)
  s!"{Colorized.color color <| Colorized.style .Bold s!"{header}:"} {toString (CompilerDiagnostic.msgOf err) |>.replace "\n" s!"\n{headerPadding}"}{String.join ((CompilerDiagnostic.hintsOf err).map λ s ↦ s!"\n{headerPadding}" ++ (toString s).replace "\n" s!"\n{headerPadding}")}
{linePadding}|
 {n} | {beginLine}{Colorized.color color middleLine}{endLine}
{linePadding}|{String.replicate (startCol + 1) ' '}{Colorized.color color <| String.replicate (endCol - startCol) '^'}"
