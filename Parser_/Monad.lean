module

public import Parser
public import Parser_.Common
public import Parser_.Tokens.PlusCal
public import Parser_.Tokens.TLAPlus

@[expose] public section


/-! # TLA+ -/

/-- The type of lexers consuming characters of a string. -/
abbrev TLAPlusLexer := SimpleParser PositionedSlice Char

private local instance {α} : Inhabited (TLAPlusLexer α) where
  default := Parser.throwUnexpected none

/-- The type of parser consuming located tokens. -/
abbrev TLAPlusParser := SimpleParserT (Parser.Stream.OfList (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token)))) (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token))) ParserWarningM

private local instance {α} : Inhabited (TLAPlusParser α) where
  default := Parser.throwUnexpected none

/-! # PlusCal -/

abbrev PlusCalLexer := SimpleParser PositionedSlice Char

private local instance {α} : Inhabited (PlusCalLexer α) where
  default := Parser.throwUnexpected none

abbrev PlusCalParser := SimpleParserT (Parser.Stream.OfList (Located' SurfacePlusCal.Token)) (Located' SurfacePlusCal.Token) ParserWarningM

private local instance {α} : Inhabited (PlusCalParser α) where
  default := Parser.throwUnexpected none

end
