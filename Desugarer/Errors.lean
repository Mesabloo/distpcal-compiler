import Common.Position
import Common.Errors

inductive DesugarError.{u} : Type u
  | misplacedAt (pos : SourceSpan)
  | seqExpectsATupleArgument (pos : SourceSpan)

instance : CompilerDiagnostic DesugarError String where
  isError := true

  posOf
    | .misplacedAt pos
    | .seqExpectsATupleArgument pos => pos
  msgOf
    | .misplacedAt _ => "Unexpected '@' outside 'EXCEPT' construct."
    | .seqExpectsATupleArgument _ => "Builtin operator 'Seq' expects a single syntactical tuple as its only argument."
