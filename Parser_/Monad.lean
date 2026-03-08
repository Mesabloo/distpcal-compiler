import Parser
import Parser_.Common
import Parser_.Tokens.PlusCal
import Parser_.Tokens.TLAPlus

/-! # TLA+ -/

/-- The type of lexers consuming characters of a string. -/
abbrev TLAPlusLexer := SimpleParser PositionedSlice Char

private local instance {α} : Inhabited (TLAPlusLexer α) where
  default := Parser.throwUnexpected none

/-- The type of parser consuming located tokens. -/
abbrev TLAPlusParser := SimpleParser (Parser.Stream.OfList (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token)))) (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token)))

private local instance {α} : Inhabited (TLAPlusParser α) where
  default := Parser.throwUnexpected none

/-! # PlusCal -/

abbrev PlusCalLexer := SimpleParser PositionedSlice Char

private local instance {α} : Inhabited (PlusCalLexer α) where
  default := Parser.throwUnexpected none

abbrev PlusCalParser := SimpleParser (Parser.Stream.OfList (Located' SurfacePlusCal.Token)) (Located' SurfacePlusCal.Token)

private local instance {α} : Inhabited (PlusCalParser α) where
  default := Parser.throwUnexpected none
