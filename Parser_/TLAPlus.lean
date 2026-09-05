module

public import Parser_.Tokens.TLAPlus
public import Parser_.Tokens.PlusCal
public import Core.SurfaceTLAPlus.Syntax
public import Core.SurfacePlusCal.Syntax
public import Common.Position
import Parser
import Lean.Data.Trie
meta import CustomPrelude
import Parser_.PlusCal
import Mathlib.Data.List.Basic
public import Parser_.Common
public import Parser_.Monad
import Common.Errors
import Mathlib.Logic.Function.Basic

public section

/-! # A small lexer for TLA⁺ -/

namespace SurfaceTLAPlus.Lexer
  open Parser hiding eoption takeMany1 takeMany
  open Char

  section
    variable {σ τ α : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ]

    /-- Surrounds the result of a parser `p` with its starting and ending positions. -/
    private def located {ε} [Parser.Error ε PositionedSlice Char] (p : ParserT ε PositionedSlice Char m α) : ParserT ε PositionedSlice Char m (Located α) := do
      let startPos ← getPosition
      let res ← p
      let endPos ← getPosition
      return { segment := ⟨startPos, endPos⟩, data := res }

    /-- Skips whitespace: `p₁` consumes (at least 1) whitespace character, `p₂` line comments,
    `p₃` block comments. -/
    @[inline]
    private def space {ε} [Parser.Error ε σ τ] [lt : LT (Stream.Position σ)] [le : LE (Stream.Position σ)] [DecidableRel lt.lt] [DecidableRel le.le] (p₁ p₂ p₃ : ParserT ε σ τ m PUnit) : ParserT ε σ τ m PUnit
      := dropMany <| first [p₁, p₂, p₃]

    @[inline]
    private def empty {ε} [Parser.Error ε σ τ] : ParserT ε σ τ m PUnit :=
      throwUnexpected none

    /-- Parse "blank" tokens, i.e. tokens which convey no syntactical relevance. -/
    @[inline]
    private def ws {ε} [Parser.Stream σ Char] [Parser.Error ε σ Char] [lt : LT (Stream.Position σ)] [le : LE (Stream.Position σ)] [DecidableRel lt.lt] [DecidableRel le.le] : ParserT ε σ Char m PUnit
      := space (Unicode.whitespace >>= λ | '\t' => throwUnexpectedWithMessage (some '\t') "Horizontal tab characters (U+0009) are forbidden." | _ => pure ()) empty empty

    /-- Try to apply a parser, then consume some whitespace as defined by `SurfaceTLAPlus.Lexer.ws`. -/
    @[inline]
    private def lexeme {ε} [Parser.Stream σ Char] [Parser.Error ε σ Char] [lt : LT (Stream.Position σ)] [le : LE (Stream.Position σ)] [DecidableRel lt.lt] [DecidableRel le.le] (p : ParserT ε σ Char m α) : ParserT ε σ Char m α :=
      p <* ws
  end

  section Tokens
    /-- Lex either a keyword or an identifier. -/
    private def identifierOrKeyword {α} : TLAPlusLexer (Token α) := do
      -- `WF_`/`SF_` are the one keyword pair that ends in `_` and binds as a bare prefix: `WF_e`
      -- is the keyword `WF_` followed by the identifier `e`, so they are matched ahead of the
      -- maximal-munch scan that would otherwise swallow `WF_e` whole. `WFoo` (no `_`) stays an
      -- identifier.
      (Token.«WF_» <$ withBacktracking (chars "WF_"))
        <|> (Token.«SF_» <$ withBacktracking (chars "SF_"))
        <|> do
          let c ← Unicode.alpha <|> char '_'
          let cs ← takeMany (withBacktracking <| Unicode.alpha <|> char '_' <|> (String.front ∘ toString) <$> Unicode.digit)

          return mapKeywordToToken (String.ofList (cs.insertIdx 0 c).toList)
    where
      -- TODO(reserved): complete the TLA⁺ reserved-word list.
      mapKeywordToToken : String → Token α
        | "MODULE" => .module
        | "EXTENDS" => .extends
        | "CONSTANTS" => .constants
        | "CONSTANT" => .constant
        | "VARIABLES" => .variables
        | "VARIABLE" => .variable
        | "IF" => .if
        | "THEN" => .then
        | "ELSE" => .else
        | "ASSUME" => .assume
        | "EXCEPT" => .except
        | "UNCHANGED" => .prefix .«UNCHANGED»
        | "DOMAIN" => .prefix .«DOMAIN»
        | "SUBSET" => .prefix .«SUBSET»
        | "ENABLED" => .prefix .«ENABLED»
        | "UNION" => .prefix .«UNION»
        | "CHOOSE" => .choose
        | "CASE" => .case
        | "OTHER" => .other
        | "LET" => .let
        | "IN" => .in
        | "INSTANCE" => .instance
        | "WITH" => .with
        | "TRUE" => .true
        | "FALSE" => .false
        -- LAMBDA
        | "_" => .underscore
        | str => .identifier str

    /-- Every fixed operator and reserved-symbol spelling, mapped to its token. Order is
    irrelevant: `symbolTrie` resolves ambiguity by longest match. -/
    private def symbolTable : List (String × Token (Located SurfacePlusCal.Token)) :=
      [ ("\\intersect", .infix .«\intersect»), ("\\in", .infix .«\in»),
        ("\\notin", .infix .«\notin»), ("\\neg", .prefix .«\neg»), ("\\lnot", .prefix .«\lnot»),
        ("\\A", .«\A»), ("\\E", .«\E»),
        ("\\cup", .infix .«\cup»), ("\\cap", .infix .«\cap»), ("\\circ", .infix .«\circ»),
        ("\\cong", .infix .«\cong»), ("\\cdot", .infix .«\cdot»),
        ("\\oplus", .infix .«\oplus»), ("\\ominus", .infix .«\ominus»),
        ("\\odot", .infix .«\odot»), ("\\otimes", .infix .«\otimes»),
        ("\\oslash", .infix .«\oslash»), ("\\o", .infix .«\o»),
        ("\\land", .infix .«\land»), ("\\lor", .infix .«\lor»), ("\\leq", .infix .«\leq»),
        ("\\ll", .infix .«\ll»),
        ("\\preceq", .infix .«\preceq»), ("\\prec", .infix .«\prec»),
        ("\\propto", .infix .«\propto»),
        ("\\subseteq", .infix .«\subseteq»), ("\\subset", .infix .«\subset»),
        ("\\supseteq", .infix .«\supseteq»), ("\\supset", .infix .«\supset»),
        ("\\succeq", .infix .«\succeq»), ("\\succ", .infix .«\succ»),
        ("\\sqcap", .infix .«\sqcap»), ("\\sqcup", .infix .«\sqcup»),
        ("\\sqsubseteq", .infix .«\sqsubseteq»), ("\\sqsubset", .infix .«\sqsubset»),
        ("\\sqsupseteq", .infix .«\sqsupseteq»), ("\\sqsupset", .infix .«\sqsupset»),
        ("\\simeq", .infix .«\simeq»), ("\\sim", .infix .«\sim»), ("\\star", .infix .«\star»),
        ("\\geq", .infix .«\geq»), ("\\gg", .infix .«\gg»),
        ("\\union", .infix .«\union»), ("\\uplus", .infix .«\uplus»),
        ("\\times", .infix .«\times»), ("\\wr", .infix .«\wr»),
        ("\\div", .infix .«\div»), ("\\doteq", .infix .«\doteq»),
        ("\\bullet", .infix .«\bullet»), ("\\bigcirc", .infix .«\bigcirc»),
        ("\\asymp", .infix .«\asymp»), ("\\approx", .infix .«\approx»),
        ("\\equiv", .infix .«\equiv»),
        ("\\X", .infix .«\X»), ("\\/", .infix .«\/»), ("\\", .infix .«\»),
        ("...", .infix .«...»), ("..", .infix .«..»), (".", .infix .«.»),
        ("==", .eqeq false), ("=>", .infix .«=>»), ("=|", .infix .«=|»),
        ("=<", .infix .«=<»), ("=", .infix .«=»),
        (",", .comma),
        ("(+)", .infix .«(+)»), ("(-)", .infix .«(-)»), ("(.)", .infix .«(.)»),
        ("(/)", .infix .«(/)»), ("(\\X)", .infix .«(\X)»), ("(", .lparen), (")", .rparen),
        ("<=>", .infix .«<=>»), ("<=", .infix .«<=»), ("<<", .langle), ("<>", .prefix .«<>»),
        ("<:", .infix .«<:»), ("<", .infix .«<»),
        (">>_", .«>>_»), (">>", .rangle), (">=", .infix .«>=»), (">", .infix .«>»),
        ("->", .«->»), ("-+->", .infix .«-+->»), ("--", .infix .«--»), ("-", .infix .«-»),
        ("|->", .«|->»), ("|-", .infix .«|-»), ("||", .infix .«||»), ("|=", .infix .«|=»),
        ("|", .infix .«|»),
        ("{", .lbrace), ("}", .rbrace),
        ("/\\", .infix .«/\»), ("/=", .infix .«/=»), ("//", .infix .«//»), ("/", .infix .«/»),
        ("[]", .prefix .«[]»), ("[", .lbracket), ("]_", .«]_»), ("]", .rbracket),
        ("::=", .infix .«::=»), (":=", .infix .«:=»), (":>", .infix .«:>»), (":", .colon),
        ("~>", .infix .«~>»), ("~", .prefix .«~»),
        ("^^", .infix .«^^»), ("^+", .postfix .«^+»), ("^*", .postfix .«^*»),
        ("^#", .postfix .«^#»), ("^", .infix .«^»),
        ("++", .infix .«++»), ("+", .infix .«+»),
        ("'", .postfix .«'»),
        ("!!", .infix .«!!»), ("!", .bang),
        ("##", .infix .«##»), ("#", .infix .«#»),
        ("$$", .infix .«$$»), ("$", .infix .«$»),
        ("%%", .infix .«%%»), ("%", .infix .«%»),
        ("&&", .infix .«&&»), ("&", .infix .«&»),
        ("**", .infix .«**»), ("*", .infix .«*»),
        ("??", .infix .«??»), ("?", .infix .«?»),
        ("@@", .infix .«@@»), ("@", .at) ]

    /-- The operator and reserved-symbol trie, built once from `symbolTable`. Values pair each
    token with its spelling's length, so a match tells `lexSymbol` how much input it consumed.
    `noinline` pins that "built once": inlining would rebuild it on every `lexSymbol` call. -/
    @[noinline]
    private def symbolTrie : Lean.Data.Trie (Nat × Token (Located SurfacePlusCal.Token)) :=
      symbolTable.foldl (init := .empty) λ t (spelling, tk) ↦ t.insert spelling (spelling.length, tk)

    /-- Longest spelling in `symbolTable`, i.e. how far `lexSymbol` must look ahead to give
    `symbolTrie` a chance at every entry. -/
    private def maxSymbolLen : Nat := symbolTable.foldl (init := 0) (max · ·.1.length)

    /-- Longest-match one operator or reserved symbol against `symbolTrie`, failing without
    consuming when no spelling matches. -/
    private def lexSymbol : TLAPlusLexer (Token (Located SurfacePlusCal.Token)) := do
      let cs ← lookAhead (takeUpTo maxSymbolLen anyToken)
      match symbolTrie.matchPrefix (String.ofList cs.toList) {} with
      | none => throwUnexpected none
      | some (len, .prefix .«[]») =>
        -- `[]_` is `[` then `]_`, never `[]` then `_`.
        match cs[len]? with
        | some '_' => drop 1 anyToken *> pure .lbracket
        | _ => drop len anyToken *> pure (.prefix .«[]»)
      | some (len, tk) => drop len anyToken *> pure tk

    /-- Lex an operator or a reserved symbol: the `----`/`====` module delimiters, which are runs
    rather than fixed strings, then a longest-match walk over every other spelling. -/
    private def symbol : TLAPlusLexer (Token (Located SurfacePlusCal.Token)) := first [
      (.moduleStart ∘ Array.size) <$> takeManyN 4 (char '-'),
      (.moduleEnd ∘ Array.size) <$> takeManyN 4 (char '='),
      lexSymbol
    ]

    private def lineComment {α} : TLAPlusLexer (Token α) := do
      let _ ← chars r"\*"
      let ⟨content, _⟩ ← takeUntil (() <$ eol <|> endOfInput) anyToken
      -- TODO(perf): find a faster array-to-string conversion.
      return .inlineComment <| String.ofList <| Array.toList content

    private partial def blockComment (lexTLAToken : TLAPlusLexer (Located (Token (Located SurfacePlusCal.Token)))) (inner : Bool := false) : TLAPlusLexer (Token (Located SurfacePlusCal.Token)) := do
      let _ ← chars "(*"
      unless inner do
        let isAlg ← test <| lookAhead do
          -- Assumes the comment starts directly with the algorithm, not other content.
          let _ ← takeMany (withBacktracking <| lexeme <| char '*')
          let _ ← chars "--"
          let _ ← eoption (withBacktracking (chars "fair") <* takeMany1 (withBacktracking <| Unicode.whitespace))
          let _ ← chars "algorithm"
          pure ()
        if isAlg then
          let _ ← takeMany (lexeme <| withBacktracking <| char '*')
          let alg ← lexeme <| SurfacePlusCal.Lexer.lexAlgorithm λ () ↦ ((SurfacePlusCal.Token.tla ∘ (Located.data <$> ·)) <$> ·) <$> lexTLAToken
          let _ ← lexeme <| takeMany1 (withBacktracking <| char '*') <* char ')'
          return Token.pcal alg.toList
      let ⟨chars, _⟩ ← takeUntil (chars "*)") <| first [
        (λ | .blockComment cs => cs | _ => unreachable!) <$> blockComment lexTLAToken (inner := true),
        String.singleton <$> anyToken
      ]
      return .blockComment (chars.foldl (init := "") (· ++ ·))

    -- TODO(numerals): support binary, octal and hexadecimal literals.
    private def number {α} : TLAPlusLexer (Token α) :=
      (.number ∘ String.ofList ∘ Array.toList) <$> takeMany1 (withBacktracking ASCII.numeric)

    private def string {α} : TLAPlusLexer (Token α) := do
      let _ ← char '"'
      let raw ← takeMany stringChar
      let _ ← char '"'
      return .string (raw.foldl (init := "") (· ++ ·))
    where
      stringChar : TLAPlusLexer String := first [
        char '\\' *> first [
          r"\n" <$ char 'n', -- LF: Line Feed
          r"\t" <$ char 't', -- HT: Horizontal Tab
          r"\r" <$ char 'r', -- CR: Carriage Return
          r"\f" <$ char 'f', -- FF: Form Feed
          "\\\"" <$ char '"',
          "\\\\" <$ char '\\',
        ],
        String.singleton <$> tokenFilter (· != '"')
      ]
  end Tokens

  /-- Lex a full TLA⁺ token: operator, reserved word, identifier, or literal. -/
  private partial def lexToken : TLAPlusLexer (Located (Token (Located SurfacePlusCal.Token))) := located <| first [
    lineComment,
    blockComment lexToken,
    identifierOrKeyword,
    symbol,
    number,
    string,
  ]

  /-- Lex a full module. -/
  def lexModule' : TLAPlusLexer (Array (Located (Token (Located SurfacePlusCal.Token)))) := do
    -- remove any leading comments before actually trying to parse anything
    let _ ← lexeme (pure ())
    Prod.fst <$> Parser.takeUntil Parser.endOfInput (lexeme lexToken)

  def lexModule (s : String) : Unexpected Char ⊕ Array (Located' (Token (Located' SurfacePlusCal.Token))) :=
    match lexModule'.run ⟨s, ⟨1, 0⟩⟩ with
    | .error _ e => .inl <| errToUnexpected e
    | .ok str tokens =>
      assert! str.1.isEmpty
      -- TODO(positions): patch positions from byte indices to line/column in UTF-8 codepoints.
      -- The current conversion traverses the whole token list, and overlapping stream parts once
      -- per token.
      .inr <| tokens.map λ ⟨pos, tok⟩ ↦ ⟨mkPosition pos, (λ ⟨pos, tok⟩ ↦ ⟨mkPosition pos, tok⟩) <$> tok⟩
  where
    @[inline]
    posToLineCol (pos : Stream.Position PositionedSlice) : Cursor := pos.2

    mkPosition (seg : Stream.Segment PositionedSlice) : SourceSpan :=
      ⟨posToLineCol seg.start, posToLineCol seg.stop⟩

    errToUnexpected (e : ParseError PositionedSlice Char) : Unexpected Char :=
      { token := e.unexpected
        pos := e.posOverride.getD (mkPosition ⟨e.pos, e.pos⟩)
        hints := e.expectedHints }
end SurfaceTLAPlus.Lexer



/-! # Main parser for a single TLA⁺ module -/

namespace SurfaceTLAPlus.Parser
  open _root_.Parser hiding eoption takeMany1 takeMany first sepBy sepBy1 sepNoEndBy1 sepEndBy1 withBacktracking tokenMap tokenFilter token anyToken withErrorMessage
  open Parser_

  /--
    Attaches some location information to the result of a parser.
  -/
  private def located {α} (p : TLAPlusParser α) : TLAPlusParser α := do
    let toks := (← getStream).toks
    let ⟨res, start, «end»⟩ ← withCapture p
    let spanAt := λ (i : Nat) ↦ (toks[i]?).elim SourceSpan.placeholder (·.segment)
    -- The span runs from the first token `p` consumed to the last; `end` is one past it, and
    -- equals `start` when `p` consumed nothing.
    return res @@ (spanAt start ++ spanAt (if «end» > start then «end» - 1 else start))

  /-- Drops "blank" tokens. Use sparingly: comments must still be kept in some places, for type
  annotations. -/
  @[inline]
  private def ws : TLAPlusParser PUnit :=
    dropMany <| tokenFilter (λ | ⟨_, .inlineComment _⟩ | ⟨_, .blockComment _⟩ => true | _ => false)

  /-- `lexeme p` applies `p`, then tries to consume trailing "whitespace" as defined by `ws`. -/
  @[inline]
  private def lexeme {α} (p : TLAPlusParser α) : TLAPlusParser α := p <* ws

  private def getCol : TLAPlusParser Nat := do
    let ⟨pos, _⟩ ← peek
    return pos.start.col

  local instance : ToString Ordering where
    toString
      | .lt => "<"
      | .eq => "="
      | .gt => ">"

  private def indentGuard (ord : Ordering) (col : Nat) : TLAPlusParser PUnit := do
    let ord' := Ord.compare (← getCol) col
    if ord = ord' then
      return ()
    throwUnexpectedWithMessage (msg := s!"Expected indentation level to be {ord} {col}, but was {ord'} instead")

  private def aligned {α} (p : TLAPlusParser PUnit → TLAPlusParser α) : TLAPlusParser α := do
    let col ← getCol
    let ws : TLAPlusParser PUnit := lexeme (pure ()) *> indentGuard .eq col
    p ws

  section Tokens
    /-- Accepts `tk`, failing otherwise with `tk` itself named as what would have matched — every
    call site gets a real "expected" hint for free, no per-site message needed. -/
    @[inline]
    private def token (tk : Token (Located' SurfacePlusCal.Token)) : TLAPlusParser (Located' (Token (Located' SurfacePlusCal.Token))) :=
      withErrorMessage (toString tk) <| withBacktracking <| tokenFilter λ ⟨_, tk'⟩ => tk == tk'

    /-- Parse an identifier and return its raw name. -/
    private def parseIdentifier : TLAPlusParser String := withErrorMessage "identifier" do
      let ⟨pos, .identifier str⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .identifier _⟩ => true | _ => false
        | unreachable!
      return str @@ pos

    private def parseNumber : TLAPlusParser String := withErrorMessage "number" do
      let ⟨pos, .number raw⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .number _⟩ => true | _ => false
        | unreachable!
      return raw @@ pos

    private def parseString : TLAPlusParser String := withErrorMessage "string" do
      let ⟨pos, .string raw⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .string _⟩ => true | _ => false
        | unreachable!
      return raw @@ pos

    @[inline]
    private def comma : TLAPlusParser PUnit := () <$ token .comma

    @[inline]
    private def underscore : TLAPlusParser PUnit := () <$ token .underscore

    @[inline]
    private def parens {α} (p : TLAPlusParser α) : TLAPlusParser α :=
      token .lparen *> p <* token .rparen

    @[inline]
    private def brackets {α} (p : TLAPlusParser α) : TLAPlusParser α :=
      token .lbracket *> p <* token .rbracket

    @[inline]
    private def angles {α} (p : TLAPlusParser α) : TLAPlusParser α :=
      token .langle *> p <* token .rangle

    @[inline]
    private def braces {α} (p : TLAPlusParser α) : TLAPlusParser α :=
      token .lbrace *> p <* token .rbrace
  end Tokens

  namespace Annotations
    /--
      Parses annotations out of a run of adjacent comments by concatenating their raw content
      into one flat `String` and parsing over it with the ordinary `String.Slice` stream. Each
      match's flat position is mapped back to its original comment (via `commentIndexOf` below)
      to recover that comment's own `SourceSpan`.
    -/
    private abbrev TypeParser := SimpleParser String.Slice Char

    /-- Surrounds the result of a parser `p` with its starting and ending positions. -/
    private def located {σ τ m α} [st : Parser.Stream σ τ] [Monad m] (p : SimpleParserT σ τ m α) : SimpleParserT σ τ m (st.Position × st.Position × α) := do
      let startPos ← Parser.getPosition
      let res ← p
      let endPos ← Parser.getPosition
      return ⟨startPos, endPos, res⟩

    open Char

    private def parseAnnotation : TypeParser CommentAnnotation := do
      let _ ← _root_.Parser.token '@'
      let name ← identifier
      let _ ← ws
      let args : List _ ← first [
        do
          let _ ← withBacktracking <| _root_.Parser.token '(' <* ws
          let args ← sepBy1 (_root_.Parser.token ',' <* ws) arg
          let _ ← _root_.Parser.token ')'
          pure <| Array.toList args,
        do
          let _ ← withBacktracking <| _root_.Parser.token ':' <* ws
          let chars ← takeMany1 (withBacktracking <| tokenFilter λ | '@' | ';' => false | _ => true)
          let _ ← _root_.Parser.token ';'
          pure [Sum.inl <| String.ofList chars.toList],
        pure []
      ]
      return ⟨name, args⟩
    where
      ws := dropMany (withBacktracking Unicode.whitespace)
      identifier := do
        let char₁ ← ASCII.alpha
        let chars ← takeMany (withBacktracking <| ASCII.alphanum <|> char '_')
        return String.ofList <| char₁ :: chars.toList
      arg : TypeParser (String ⊕ Int ⊕ Bool ⊕ String) := first [
        (.inl ∘ String.ofList ∘ Array.toList) <$> (char '"' *> takeMany stringChar <* char '"'),
        (.inr ∘ .inr ∘ .inr) <$> identifier,
        (.inr ∘ .inl) <$> integer,
        .inr (.inr (.inl true)) <$ chars "true",
        .inr (.inr (.inl false)) <$ chars "false",
      ]
      stringChar : TypeParser Char := first [
        (char '\\' *> tokenFilter λ | 'n' | '\'' | '"' | 'f' | 'r' | 't' | '\\' => true | _ => false) <&>
          λ | 'n' => '\n'
            | 'r' => '\r'
            | 'f' => Char.ofNat 12
            | 't' => '\t'
            | '"' => '"'
            | '\'' => '\''
            | '\\' => '\\'
            | _ => unreachable!,
        tokenFilter λ | '"' | '\\' => false | _ => true,
      ]
      integer : TypeParser Int := do
        let sign ← eoption <| char '-'
        let digits ← takeMany1 <| tokenFilter λ | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => true | _ => false
        return (sign.elim' "" String.singleton ++ String.ofList digits.toList).toInt!

    /-- Try to parse annotations out of one flat string (the concatenation of every comment in
    a run), ignoring any raw text in between. `\@` is an escaped, literal `@` — it never starts
    an annotation, so prose that needs to mention e.g. `@type` without triggering the annotation
    grammar can write `\@type` instead. -/
    private def tryParseAnnotations' : TypeParser (List (String.Pos.Raw × String.Pos.Raw × CommentAnnotation)) := do
      let ⟨anns, _⟩ ← takeUntil endOfInput <| first [
        .inl "@" <$ withBacktracking (chars "\\@"),
        .inr <$> withBacktracking (located parseAnnotation),
        .inl <$> String.singleton <$> anyToken,
      ]
      return anns.toList.filterMap Sum.getRight?

    /-- Cumulative `[start, end)` byte-offset ranges, one per comment, within the flat string
    `String.join contents` (in the same order). -/
    private def commentBoundaries (contents : List String) : Array (String.Pos.Raw × String.Pos.Raw) :=
      (contents.foldl (init := (#[], 0)) λ (acc, off) c ↦
        let endOff := off + c.utf8ByteSize
        (acc.push (.mk off, .mk endOff), endOff)).fst

    /-- Which comment (by index into the original list) a flat position falls in — the first
    one whose own `[start, end)` range extends past `pos`, falling back to the last comment
    for a position sitting exactly at the very end of the concatenation. -/
    private def commentIndexOf (boundaries : Array (String.Pos.Raw × String.Pos.Raw)) (pos : String.Pos.Raw) : Nat :=
      (boundaries.findIdx? λ (_, endOff) ↦ pos.byteIdx < endOff.byteIdx).getD (boundaries.size - 1)

    /-- The position of a `TypeParser` failure's innermost `unexpected` — the flat-string offset
    a `.addMessage` chain always bottoms out at. -/
    private partial def annotationErrorPos : Parser.Error.Simple String.Slice Char → String.Pos.Raw
      | .unexpected pos _ => pos
      | .addMessage err _ _ => annotationErrorPos err

    private def tryParseAnnotations : TLAPlusParser (List CommentAnnotation) := do
      let comments ← takeMany <| withBacktracking <| tokenFilter λ | ⟨_, .inlineComment _⟩ | ⟨_, .blockComment _⟩ => true | _ => false
      let contents := comments.toList.map λ | ⟨_, .inlineComment c⟩ | ⟨_, .blockComment c⟩ => c | _ => unreachable!

      if contents.isEmpty then
        return []
      let boundaries := commentBoundaries contents
      match tryParseAnnotations'.run (String.join contents) with
        | .ok _ res =>
          return res.map λ ⟨start, «end», ann⟩ ↦
            let startPos := comments[commentIndexOf boundaries start]!.segment
            let endPos := comments[commentIndexOf boundaries «end»]!.segment
            ann @@ startPos ++ endPos
        | .error _ e =>
          -- The failure's real position lives in the flat comment string's own numbering, not
          -- this (outer, token-indexed) parser's — resolve it against `boundaries` now, while
          -- `comments` is in scope, and hand the already-resolved span over via `posOverride`.
          let span := comments[commentIndexOf boundaries (annotationErrorPos e)]!.segment
          throw { pos := ← getPosition, unexpected := none
                  expected := [s!"Malformed annotation: {toString e}"], posOverride := some span }
  end Annotations
  export Annotations (tryParseAnnotations)

  section Expressions
    private def parseInfixOperator (ws : TLAPlusParser PUnit) : TLAPlusParser InfixOperator := debug "infix op" <| lexeme do
      match ← withBacktracking <| ws *> tokenFilter λ | ⟨_, .infix _⟩ | ⟨_, .prefix .«-»⟩ => true | _ => false with
        | ⟨pos, .infix op⟩ => return op @@ pos
        | ⟨pos, .prefix .«-»⟩ => return .«-» @@ pos
        | ⟨_, _⟩ => unreachable!

    private def parsePrefixOperator : TLAPlusParser PrefixOperator := do
      match ← withBacktracking <| tokenFilter λ | ⟨_, .prefix _⟩ | ⟨_, .infix .«-»⟩ => true | _ => false with
        | ⟨pos, .prefix op⟩ => return op @@ pos
        | ⟨pos, .infix .«-»⟩ => return .«-» @@ pos
        | ⟨_, _⟩ => unreachable!

    private def parsePostfixOperator : TLAPlusParser PostfixOperator := do
      let ⟨pos, .postfix op⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .postfix _⟩ => true | _ => false
        | unreachable!
      return op @@ pos

    inductive OperatorOrExpression : Type _
      | «prefix» (_ : PrefixOperator)
      | «postfix» (_ : PostfixOperator)
      | «infix» (_ : InfixOperator)
      | atom (_ : Expression (List CommentAnnotation))
      | index (_ : Bool × List (Expression (List CommentAnnotation)))
      deriving Repr

    section ShuntingYardAlgorithm
      class HasPrecedence (α : Type) where
        range : α → Nat × Nat
        wf : ∀ x : α, (range x).fst ≤ (range x).snd

      instance {α} [HasPrecedence α] : HasPrecedence (Located α) where
        range := λ ⟨_, x⟩ ↦ HasPrecedence.range x
        wf := λ ⟨_, x⟩ ↦ HasPrecedence.wf x

      /-- Returns `true` if the precedence range of the two operators overlap, `false` otherwise. -/
      def HasPrecedence.conflicts {α β} [HasPrecedence α] [HasPrecedence β] (x : α) (y : β) : Bool :=
        let (xb, xe) := HasPrecedence.range x
        let (yb, ye) := HasPrecedence.range y
        (yb ≤ xb && xb ≤ ye) || (xb ≤ yb && yb ≤ xe)

      def HasPrecedence.blt {α β} [HasPrecedence α] [HasPrecedence β] (x : α) (y : β) : Bool :=
        (HasPrecedence.range x).snd < (HasPrecedence.range y).fst

      instance : HasPrecedence SurfaceTLAPlus.PrefixOperator where
        range
          | .«\neg » _ => (4, 4)
          | .«ENABLED» | .«UNCHANGED» | .«[]» | .«<>» => (4, 15)
          | .«SUBSET» | .«UNION» => (8, 8)
          | .«DOMAIN» => (9, 9)
          | .«-» => (12, 12)
        wf := by rintro (_|_) <;> simp

      instance : HasPrecedence SurfaceTLAPlus.PostfixOperator where
        range
          | .«^+» | .«^*» | .«^#» | .«'» => (15, 15)
        wf := by rintro (_|_) <;> simp

      instance : HasPrecedence SurfaceTLAPlus.InfixOperator where
        range
          | .«?» => (0, 20) -- Conflicts with every operator: this operator's semantics are unknown.
          | .«=>» => (1, 1)
          | .«-+->» | .«<=> » _ | .«~>» => (2, 2)
          | .«/\ » _ | .«\/ » _ => (3, 3)
          | .«/= » _ | .«-|» | .«::=» | .«:=» | .«<» | .«=» | .«=|» | .«>» | .«\approx» | .«\asymp» | .«\cong» | .«\doteq» | .«>= » _
            | .«\gg» | .«\in» | .«\notin» | .«=< » _ | .«\ll» | .«\prec» | .«\preceq» | .«\propto» | .«\sim» | .«\simeq» | .«\sqsubset»
            | .«\sqsubseteq» | .«\sqsupset» | .«\sqsupseteq» | .«\subset» | .«\subseteq» | .«\succ» | .«\succeq» | .«\supset» | .«\supseteq»
            | .«|-» | .«|=» => (5, 5)
          | .«\cdot» => (5, 14)
          | .«@@» => (6, 6)
          | .«:>» | .«<:» => (7, 7)
          | .«\» | .«\cap » _ | .«\cup » _ => (8, 8)
          | .«..» | .«...» => (9, 9)
          | .«!!» | .«##» | .«$» | .«$$» | .«??» | .«\sqcap» | .«\sqcup» | .«\uplus» => (9, 13)
          | .«\wr» => (9, 14)
          | .«(+) » _ | .«+» | .«++» => (10, 10)
          | .«%» | .«%%» | .«|» | .«||» => (10, 11)
          | .«\X » _ => (10, 13)
          | .«(-) » _ | .«-» | .«--» => (11, 11)
          | .«&» | .«&&» | .«(.) » _ | .«(/) » _ | .«(\X) » _ | .«*» | .«**» | .«/» | .«//» | .«\bigcirc» | .«\bullet» | .«\div» | .«\o » _
            | .«\star» => (13, 13)
          | .«^» | .«^^» => (14, 14)
          | .«.» => (17, 17)
        wf := by rintro (_|_) <;> simp

      /-- Associativity of an infix operator. -/
      inductive Associativity : Type
        /-- An operator `⊙` is left-associative if `x ⊙ y ⊙ z = (x ⊙ y) ⊙ z`. -/
        | left
        /-- An operator `⊙` is right-associative if `x ⊙ y ⊙ z = x ⊙ (y ⊙ z)`. -/
        | right
        /-- An operator `⊙` is non-associative if it does not make sense to write `x ⊙ y ⊙ z`. -/
        | none
        deriving DecidableEq

      /-- Maps a TLA+ infix operator to its associativity. -/
      def TLAPlus.InfixOperator.assoc : SurfaceTLAPlus.InfixOperator → Associativity
        -- No TLA+ operator is right-associative.
        | .«/\ » _ | .«\/ » _ | .«\cdot» | .«@@» | .«\cap » _ | .«\cup » _ | .«##» | .«$» | .«$$» | .«??» | .«\sqcap» | .«\sqcup» | .«\uplus»
          | .«(+) » _ | .«+» | .«++» | .«%%» | .«|» | .«||» | .«(-) » _ | .«-» | .«--» | .«&» | .«&&» | .«(.) » _ | .«(\X) » _ | .«*»
          | .«**» | .«\bigcirc» | .«\bullet» | .«\o » _ | .«\star» | .«\X » _ | .«.» => .left
        | _ => .none

      def checkConflicts {α β γ σ ε m} [Monad m] [HasPrecedence β] [HasPrecedence γ] [Parser.Stream σ α] [Parser.Error ε σ α] [ToString β] [ToString γ]
        (op₁ : β) (op₂ : γ) : ParserT ε σ α m PUnit := do
          if HasPrecedence.conflicts op₁ op₂ then
            throwUnexpectedWithMessage
              (msg := s!"Operator conflict detected between {op₁} (precedence {HasPrecedence.range op₁}) and {op₂} (precedence {HasPrecedence.range op₂})")
          return ()

      set_option linter.unusedVariables false in
      /-- A modified Shunting Yard algorithm: also handles prefix/postfix operators and conflicts
      between precedence ranges. -/
      def shuntingYard (input : List OperatorOrExpression) : TLAPlusParser (Expression (List CommentAnnotation))
        := do
          let mut output : List (Expression (List CommentAnnotation)) := []
          let mut opsStack : List OperatorOrExpression := []

          for tk in input do
            match tk with
              | .atom expr => do
                if let .postfix op :: _ := opsStack then
                  throwUnexpectedWithMessage (msg := s!"Unexpected postfix operator {op}")
                output := expr :: output
              | .index args => do
                if input.isEmpty then
                  throwUnexpectedWithMessage (msg := s!"Unexpected function/operator call")
                while h : !opsStack.isEmpty do
                  let o :: os := opsStack
                  match o with
                    | .postfix op => output := pushOperatorOntoOutput (.postfix op) output
                    | .infix op@.«.» => output := pushOperatorOntoOutput (.infix op) output
                    | .infix op | .prefix op => break
                    | .atom _ | .index _ => unreachable!
                  opsStack := os
                output := pushOperatorOntoOutput (.index args) output
              | .postfix opPost => do
                if input.isEmpty then
                  throwUnexpectedWithMessage (msg := s!"Unexpected postfix operator {opPost}")
                while h : !opsStack.isEmpty do
                  let o :: os := opsStack
                  match o with
                    | .postfix _ => break
                    | .infix opIn => do
                      let _ ← checkConflicts opIn opPost
                      if HasPrecedence.blt opIn opPost then
                        break
                      else if HasPrecedence.blt opPost opIn then
                        output := pushOperatorOntoOutput (.infix opIn) output
                    | .prefix opPre => do
                      let _ ← checkConflicts opPre opPost
                      if HasPrecedence.blt opPre opPost then
                        break
                      else if HasPrecedence.blt opPost opPre then
                        output := pushOperatorOntoOutput (.prefix opPre) output
                    | .atom _ | .index _ => unreachable!
                  opsStack := os
                opsStack := .postfix opPost :: opsStack
              | .infix opIn => do
                while h : !opsStack.isEmpty do
                  let o :: os := opsStack
                  match o with
                    | .prefix opPre => do
                      let _ ← checkConflicts opPre opIn
                      if HasPrecedence.blt opPre opIn then
                        break
                      else if HasPrecedence.blt opIn opPre then
                        output := pushOperatorOntoOutput (.prefix opPre) output
                    | .infix opIn' =>
                      if opIn = opIn' then
                        match TLAPlus.InfixOperator.assoc opIn with
                          | .left => output := pushOperatorOntoOutput (.infix opIn') output
                          | .right => break
                          | .none => checkConflicts opIn opIn' -- conflict is bound to happen here
                      else
                        let _ ← checkConflicts opIn opIn'
                        if HasPrecedence.blt opIn opIn' then
                          output := pushOperatorOntoOutput (.infix opIn') output
                        else if HasPrecedence.blt opIn' opIn then
                          break
                    | .postfix opPost =>
                      output := pushOperatorOntoOutput (.postfix opPost) output
                    | .atom _ | .index _ => unreachable!
                  opsStack := os
                opsStack := .infix opIn :: opsStack
              | .prefix opPre => do
                if let .postfix _ :: _ := opsStack then
                  throwUnexpectedWithMessage (msg := "Unexpected prefix operator {opPre}")
                opsStack := .prefix opPre :: opsStack

          while h : opsStack.length ≠ 0 do
            let o :: os := opsStack
            output := pushOperatorOntoOutput o output
            opsStack := os

          if h : output.length ≠ 1 then
            throwUnexpectedWithMessage (msg := "Failed to parse expression (missing operator)")
          else
            return output[0]'(by
              obtain ⟨x, h'⟩ := List.length_eq_one_iff.mp (Decidable.not_not.mp h)
              simp [h']
            )
        where
          pushOperatorOntoOutput
            | .infix opIn, e₂ :: e₁ :: es => (.infixCall e₁ opIn e₂ @@ posOf e₁ ++ posOf e₂) :: es
            | .prefix opPre, e :: es => (.prefixCall opPre e @@ posOf opPre ++ posOf e) :: es
            | .postfix opPost, e :: es => (.postfixCall e opPost @@ posOf e ++ posOf opPost) :: es
            | .index x@⟨funOrOp, args⟩, e :: es => ((if funOrOp then Expression.fnCall else .opCall) e args @@ posOf x ++ posOf e) :: es
            | _, _ => unreachable!
    end ShuntingYardAlgorithm

    section
      variable (ws : TLAPlusParser PUnit) (expr : TLAPlusParser PUnit → TLAPlusParser (Expression (List CommentAnnotation)))

      private def parseIdentifierOrTuple : TLAPlusParser (IdentifierOrTuple (List CommentAnnotation)) := do
        first [
          Function.uncurry .var <$> parseId,
          .tuple <$> do
            let _ ← ws *> token .langle
            let xs ← sepBy1 (ws *> comma) parseId
            let _ ← ws *> token .rangle
            pure xs.toList
        ]
      where
        parseId := do
          let anns ← tryParseAnnotations
          let x ← ws *> parseIdentifier
          pure ⟨anns, x⟩

      private def parseIfThenElse : TLAPlusParser (Expression (List CommentAnnotation)) := located do
        let _ ← ws *> token .if
        let cond ← expr ws
        let _ ← ws *> token .then
        let t ← expr ws
        let _ ← ws *> token .else
        let e ← expr ws
        return .if cond t e

      private def parseJList : TLAPlusParser (Expression (List CommentAnnotation)) := located <| aligned λ ws ↦ do
        let col ← getCol

        let ⟨_, op⟩ ← ws *> lexeme (first [token (.infix .«/\»), token (.infix .«\/»)])

        let es ← sepNoEndBy1 (ws *> lexeme (token op)) (expr <| indentGuard .gt col)
        return match op with
          | .infix .«/\» => .conj es.toList
          | .infix .«\/» => .disj es.toList
          | _ => unreachable!

      /-- Read an already-parsed `x ∈ A` (or `⟨x, …⟩ ∈ A`) expression back as a `QuantifierBound`,
      `anns` on its (first) binder. The load-bearing move of the `[`/`{` forms: the token *after*
      the shared `x ∈ A` prefix (`|->` vs `->` vs `,`) is what says whether it was a binder, and
      it can only be read once the prefix is parsed. -/
      private def Expression.asBound? (anns : List CommentAnnotation) :
          Expression (List CommentAnnotation) →
          Option (QuantifierBound (List CommentAnnotation) (Expression (List CommentAnnotation)))
        | .infixCall (.var x) .«\in» dom => some (.var anns x dom)
        | .infixCall (.tuple xs) .«\in» dom => do
          let names ← xs.mapM λ | .var x => some (([] : List CommentAnnotation), x) | _ => none
          some (.varTuple names dom)
        | _ => none

      /-- `x ∈ A` read back as the binder-and-domain of a set-collect, `anns` on the binder. -/
      private def Expression.asCollectBinder? (anns : List CommentAnnotation) :
          Expression (List CommentAnnotation) →
          Option (IdentifierOrTuple (List CommentAnnotation) × Expression (List CommentAnnotation))
        | .infixCall (.var x) .«\in» dom => some (.var anns x, dom)
        | .infixCall (.tuple xs) .«\in» dom => do
          let names ← xs.mapM λ | .var x => some (([] : List CommentAnnotation), x) | _ => none
          some (.tuple names, dom)
        | _ => none

      /-- The bare field/variable name an expression is, if it is one. -/
      private def Expression.asName? : Expression (List CommentAnnotation) → Option String
        | .var x => some x
        | _ => none

      private def parseQuantifierBound : TLAPlusParser (QuantifierBound (List CommentAnnotation) (Expression (List CommentAnnotation))) := first [
        .varTuple <$> angles (Array.toList <$> sepBy1 (ws *> comma) ((·, ·)
          <$> (ws *> tryParseAnnotations)
          <*> (ws *> parseIdentifier))),
        do
          let vs ← sepBy1 (ws *> comma) ((·, ·) <$> (ws *> tryParseAnnotations) <*> (ws *> parseIdentifier))
          return if h : vs.size = 1 then QuantifierBound.var vs[0].fst vs[0].snd else .vars (Array.toList vs)
      ] <*> do
        let _ ← ws *> token (.infix .«\in»)
        expr ws

      private def parseTupleLiteral : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> angles do
        let es ← sepBy (ws *> comma) (expr ws)
        return .tuple es.toList

      private def parseQuantifier : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> do
        let q ← token .«\A» <||> token .«\E»
        -- `x \in S` (bounded) and `x` (plain) share their leading identifier list; the token
        -- right after it — `\in` versus `:` — is what tells them apart, so parse the list once
        -- and read that token back. A leading `<<` is an unambiguous bounded tuple binder.
        let vars : Sum (Array (QuantifierBound (List CommentAnnotation) (Expression (List CommentAnnotation)))) (Array String) ← do
          match ← ws *> peek with
          | ⟨_, .angle true⟩ => Sum.inl <$> sepBy1 (lexeme comma) (parseQuantifierBound ws expr)
          | _ =>
            let ids ← sepBy1 (lexeme comma)
              ((·, ·) <$> (ws *> tryParseAnnotations) <*> (ws *> parseIdentifier))
            match ← ws *> peek with
            | ⟨_, .infix .«\in»⟩ =>
              let _ ← ws *> token (.infix .«\in»)
              let dom ← expr ws
              let hd : QuantifierBound (List CommentAnnotation) (Expression (List CommentAnnotation)) :=
                if h : ids.size = 1 then .var ids[0].fst ids[0].snd dom else .vars ids.toList dom
              let tl ← takeMany (withBacktracking (lexeme comma) *> parseQuantifierBound ws expr)
              pure (Sum.inl (#[hd] ++ tl))
            | _ => pure (Sum.inr (ids.map (·.snd)))
        let _ ← lexeme <| token .colon
        let e ← expr ws
        return match q, vars with
          | ⟨_, .«\A»⟩, .inl qs => .bforall qs.toList e
          | ⟨_, .«\E»⟩, .inl qs => .bexists qs.toList e
          | ⟨_, .«\A»⟩, .inr vs => .forall vs.toList e
          | ⟨_, .«\E»⟩, .inr vs => .exists vs.toList e
          | _, _ => unreachable!

      /-- The `!…` index chain of one `EXCEPT` update: `.a`/`.b` record steps and `[i, j]` function
      steps, in order. Shared by the update loop below. -/
      private def parseExceptIndex : TLAPlusParser (List (String ⊕ List (Expression (List CommentAnnotation)))) := do
        (·.toList) <$> takeMany1 do
          match ← peek with
          | ⟨_, .infix .«.»⟩ => Sum.inl <$> (token (.infix .«.») *> parseIdentifier)
          | ⟨_, .bracket true⟩ => .inr <$> brackets (Array.toList <$> sepBy1 (ws *> comma) (expr ws))
          | tk => throwExpected (some tk) ["'.'", "'['"]

      private def parseCase : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> do
        let _ ← token .case
        let mkBranch := do
          let cond ← expr ws
          let _ ← ws *> token .«->»
          let e ← expr ws
          pure (⟨cond, e⟩ : _ × _)
        -- A `[]` introduces another branch unless `OTHER` follows it — one token of lookahead
        -- separates the two, so the `[]` probe is atomic and the branch after it commits.
        let branch₁ ← mkBranch
        let branchₙ ← takeMany do
          let _ ← withBacktracking (ws *> token (.prefix .«[]») <* notFollowedBy (ws *> token .other))
          mkBranch
        let branches := #[branch₁] ++ branchₙ
        let other ← eoption do
          let _ ← ws *> token (.prefix .«[]»)
          let _ ← ws *> token .other
          let _ ← ws *> token .«->»
          expr ws
        return .case branches.toList other

      private def parseChoose : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> do
        let _ ← token .choose
        let xs ← parseIdentifierOrTuple ws <* ws
        let bound ← eoption do
          let _ ← token (.infix .«\in»)
          expr ws
        let _ ← ws *> token .colon <* ws
        let p ← expr ws
        return .choose xs bound p
    end

    mutual
      /-- A primary expression, chosen by its first token — no backtracking between forms. The
      `[` and `{` families, whose members share a leading expression, are each one production
      (`parseBracketForm`/`parseBraceForm`) that parses that expression once and then dispatches
      on the token after it. -/
      private partial def parseAtom (ws : TLAPlusParser PUnit) (inUpdate : Bool := false) : TLAPlusParser (Expression (List CommentAnnotation)) :=
        located <| ws *> do
          match ← peek with
          | ⟨_, .number _⟩ => (.nat ·) <$> parseNumber
          | ⟨_, .identifier _⟩ => (.var ·) <$> parseIdentifier
          | ⟨_, .string _⟩ => (.str ·) <$> parseString
          | ⟨_, .true⟩ => Expression.true <$ token .true
          | ⟨_, .false⟩ => Expression.false <$ token .false
          | tk@⟨_, .at⟩ =>
            if inUpdate then .at <$ token .at
            else throwUnexpectedWithMessage (some tk) "'@' is only valid inside an EXCEPT update value"
          | ⟨_, .if⟩ => parseIfThenElse ws (parseExpression · inUpdate)
          | ⟨_, .infix .«/\»⟩ | ⟨_, .infix .«\/»⟩ => parseJList (parseExpression · inUpdate)
          | ⟨_, .«\A»⟩ | ⟨_, .«\E»⟩ => parseQuantifier ws (parseExpression · inUpdate)
          | ⟨_, .case⟩ => parseCase ws (parseExpression · inUpdate)
          | ⟨_, .choose⟩ => parseChoose ws (parseExpression · inUpdate)
          | ⟨_, .angle true⟩ => parseTupleLiteral ws (parseExpression · inUpdate)
          | ⟨_, .paren true⟩ => located (.parens <$> parens (parseExpression ws inUpdate))
          | ⟨_, .bracket true⟩ => parseBracketForm ws inUpdate
          | ⟨_, .brace true⟩ => parseBraceForm ws inUpdate
          | tk => throwExpected (some tk) ["number", "identifier", "string", "keyword 'TRUE'", "keyword 'FALSE'", "keyword 'IF'", "'/\\'", "'\\/'", "'\\A'", "'\\E'", "keyword 'CASE'", "keyword 'CHOOSE'", "'<<'", "'('", "'['", "'{'"]

      /-- The `[`-led forms: `[a |-> e]` record, `[a : A]` record set, `[x \in S |-> e]` function
      literal, `[A -> B]` function set, `[f EXCEPT !… = …]`, `[A]_e` stutter. Parse `[`, then one
      expression, then let the next token — read against that expression's shape — decide. -/
      private partial def parseBracketForm (ws : TLAPlusParser PUnit) (inUpdate : Bool) : TLAPlusParser (Expression (List CommentAnnotation)) :=
        located <| ws *> do
          let _ ← token .lbracket
          let leadAnns ← tryParseAnnotations
          let e₁ ← parseExpression ws inUpdate
          let fieldsFrom (hd : List CommentAnnotation × String × Expression (List CommentAnnotation)) (sepTok : Token (Located' SurfacePlusCal.Token)) : TLAPlusParser (List (List CommentAnnotation × String × Expression (List CommentAnnotation))) := do
            let rest ← takeMany do
              let _ ← ws *> comma
              let anns ← tryParseAnnotations
              let f ← ws *> parseIdentifier
              let _ ← ws *> token sepTok
              let v ← parseExpression ws inUpdate
              pure (anns, f, v)
            pure (hd :: rest.toList)
          match ← ws *> peek with
          | ⟨_, .«|->»⟩ =>
            let _ ← ws *> token .«|->»
            match Expression.asName? e₁ with
            | some fld =>
              let v ← parseExpression ws inUpdate
              let fields ← fieldsFrom (leadAnns, fld, v) .«|->»
              let _ ← ws *> token .rbracket
              return .record fields
            | none =>
              let some qb := Expression.asBound? leadAnns e₁
                | throwUnexpectedWithMessage none "Expected a field name or a bound (`x \\in S`) before '|->'"
              let body ← parseExpression ws inUpdate
              let _ ← ws *> token .rbracket
              return .fn [qb] body
          | ⟨_, .comma⟩ =>
            match Expression.asBound? leadAnns e₁ with
            | some qb₀ =>
              let more ← takeMany (ws *> comma *> parseQuantifierBound ws (parseExpression · inUpdate))
              let _ ← ws *> token .«|->»
              let body ← parseExpression ws inUpdate
              let _ ← ws *> token .rbracket
              return .fn (qb₀ :: more.toList) body
            | none =>
              let some x := Expression.asName? e₁
                | throwUnexpectedWithMessage none "Expected an identifier or a bound (`x \\in S`) before ','"
              let more ← takeMany do
                let _ ← ws *> comma
                let anns ← tryParseAnnotations
                let n ← ws *> parseIdentifier
                pure (anns, n)
              let _ ← ws *> token (.infix .«\in»)
              let dom ← parseExpression ws inUpdate
              let _ ← ws *> token .«|->»
              let body ← parseExpression ws inUpdate
              let _ ← ws *> token .rbracket
              return .fn [.vars ((leadAnns, x) :: more.toList) dom] body
          | ⟨_, .colon⟩ =>
            let _ ← ws *> token .colon
            let some fld := Expression.asName? e₁
              | throwUnexpectedWithMessage none "Expected a field name (identifier) before ':'"
            let v ← parseExpression ws inUpdate
            let fields ← fieldsFrom (leadAnns, fld, v) .colon
            let _ ← ws *> token .rbracket
            return .recordSet fields
          | ⟨_, .«->»⟩ =>
            let _ ← ws *> token .«->»
            let e₂ ← parseExpression ws inUpdate
            let _ ← ws *> token .rbracket
            return .fnSet e₁ e₂
          | ⟨_, .except⟩ =>
            let _ ← ws *> token .except
            let upds ← sepBy1 (ws *> comma) do
              let _ ← ws *> token .bang
              let index ← ws *> parseExceptIndex ws (parseExpression · inUpdate)
              let _ ← ws *> token (.infix .«=»)
              let e ← parseExpression ws true
              pure (index, e)
            let _ ← ws *> token .rbracket
            return .except e₁ upds.toList
          | ⟨_, .«]_»⟩ =>
            let _ ← ws *> token .«]_»
            let a ← parseAtom ws inUpdate
            return .stutter e₁ a
          | tk => throwExpected (some tk) ["'|->'", "','", "':'", "'->'", "keyword 'EXCEPT'", "']_'"]

      /-- The `{`-led forms: `{}`/`{e, …}` set literal, `{x \in S : p}` set collect,
      `{e : x \in S, …}` set map. Parse `{`, then (unless it is `}`) one expression, then dispatch
      on the token after it. -/
      private partial def parseBraceForm (ws : TLAPlusParser PUnit) (inUpdate : Bool) : TLAPlusParser (Expression (List CommentAnnotation)) :=
        located <| ws *> do
          let _ ← token .lbrace
          let leadAnns ← tryParseAnnotations
          match ← ws *> peek with
          | ⟨_, .brace false⟩ =>
            let _ ← ws *> token .rbrace
            return .set []
          | _ =>
            let e₁ ← parseExpression ws inUpdate
            match ← ws *> peek with
            | ⟨_, .comma⟩ | ⟨_, .brace false⟩ =>
              let more ← takeMany (ws *> comma *> parseExpression ws inUpdate)
              let _ ← ws *> token .rbrace
              return .set (e₁ :: more.toList)
            | ⟨_, .colon⟩ =>
              let _ ← ws *> token .colon
              match Expression.asCollectBinder? leadAnns e₁ with
              | some (binder, dom) =>
                let pred ← parseExpression ws inUpdate
                let _ ← ws *> token .rbrace
                return .collect binder dom pred
              | none =>
                let qs ← sepBy1 (ws *> comma) (parseQuantifierBound ws (parseExpression · inUpdate))
                let _ ← ws *> token .rbrace
                return .map' e₁ qs.toList
            | tk => throwExpected (some tk) ["','", "'}'", "':'"]

      partial def parseExpression (ws : TLAPlusParser PUnit := pure ()) (inUpdate : Bool := false) : TLAPlusParser (Expression (List CommentAnnotation)) := debug "expression" <| withErrorMessage "expression" do
        let ⟨atoms, infixOps⟩ ← sepAccBy1 (parseInfixOperator ws) parseInfixAtom
        let expr := orderInput atoms (OperatorOrExpression.infix <$> infixOps)
        shuntingYard expr
      where
        /-- An infix atom is an atom, optionally prefixed by prefix operators and optionally
        followed by postfix operators. -/
        @[inline]
        parseInfixAtom : TLAPlusParser (List OperatorOrExpression) := do
          let prefixOps ← Array.map .prefix <$> takeMany parsePrefixOperator
          let atom ← .atom <$> parseAtom ws inUpdate
          let postfixOps ← Array.map .postfix <$> takeMany parsePostfixOperator
          let indices ← takeMany do
            match ← peek with
            | ⟨_, .bracket true⟩ =>
              .index <$> located ((Prod.mk true ∘ Array.toList) <$> brackets (sepBy1 comma <| parseExpression ws inUpdate))
            | ⟨_, .paren true⟩ =>
              .index <$> located ((Prod.mk false ∘ Array.toList) <$> parens (sepBy comma <| parseExpression ws inUpdate))
            | tk => throwExpected (some tk) ["'['", "'('"]
          return (prefixOps ++ #[atom] ++ postfixOps ++ indices).toList

        orderInput {α} : List (List α) → List α → List α
          | [x], [] => x
          | x :: xs, o :: os => x ++ (o :: orderInput xs os)
          | _, _ => unreachable!
    end
  end Expressions

  /-- Parse an `EXTENDS` clause. -/
  private def parseExtends : TLAPlusParser (List String) := do
    let _ ← withBacktracking <| lexeme (pure ()) *> token .extends
    let mods ← sepBy1 (lexeme comma) parseIdentifier
    return mods.toList

  -- `parseDeclaration` reaches these only after peeking their keyword, so they commit on it.
  private def parseAssume : TLAPlusParser (Expression (List CommentAnnotation)) := debug "assume" do
    let _ ← token .assume
    parseExpression

  private def parseConstants : TLAPlusParser (List (String × List CommentAnnotation)) := debug "constant" do
    let _ ← token .constant <||> token .constants

    let vars ← sepBy1 comma do
      let ann ← tryParseAnnotations
      let var ← parseIdentifier
      return ⟨var, ann⟩
    return vars.toList

  private def parseVariables : TLAPlusParser (List (String × List CommentAnnotation)) := debug "variables" do
    let _ ← token .variable <||> token .variables

    let vars ← sepBy1 comma do
      let ann ← tryParseAnnotations
      let var ← parseIdentifier
      return ⟨var, ann⟩
    return vars.toList

  private def parseOperator : TLAPlusParser (List CommentAnnotation × String × List (String × Nat) × Expression (List CommentAnnotation)) := debug "operator def" do
    -- `tryParseAnnotations` eats leading comments before it is known whether an operator
    -- definition even follows (a comment can equally precede the PlusCal block or the module
    -- footer), so the probe up to `==` is atomic; past `==` the rule commits.
    let ⟨ann, var, args⟩ ← withBacktracking do
      let ann ← tryParseAnnotations
      let var ← parseIdentifier
      let args ← eoption <| lexeme <| parens <| sepBy comma do
        let var ← parseIdentifier
        let argCount ← eoption <| parens <| Array.size <$> sepBy1 comma underscore
        return ⟨var, argCount.getD 0⟩
      let _ ← lexeme <| token (.eqeq false)
      pure (⟨ann, var, args⟩ : _ × _ × _)
    let expr ← parseExpression
    return ⟨ann, var, args.elim [] Array.toList, expr⟩

  /-- One module-body declaration, chosen by the keyword that follows any leading comment run.
    A comment or identifier (the default) is an operator definition — whose own probe up to `==`
    is atomic, since a comment run can equally precede the PlusCal block or the module footer, in
    which case it belongs to neither and must stay unconsumed. `----` ends the declaration run. -/
  private def parseDeclaration : TLAPlusParser (Option (Declaration (List CommentAnnotation))) := located do
    match ← lookAhead (lexeme (pure ()) *> peek) with
    | ⟨_, .assume⟩ => (.some ∘ .assume) <$> (lexeme (pure ()) *> parseAssume)
    | ⟨_, .constant⟩ | ⟨_, .constants⟩ => (.some ∘ .constants) <$> (lexeme (pure ()) *> parseConstants)
    | ⟨_, .variable⟩ | ⟨_, .variables⟩ => (.some ∘ .variables) <$> (lexeme (pure ()) *> parseVariables)
    | ⟨_, .moduleStart _⟩ =>
      .none <$ (lexeme (pure ()) *> tokenFilter λ | ⟨_, .moduleStart _⟩ => true | _ => false)
    | _ => (λ ⟨a, b, c, d⟩ ↦ .some <| .operator a b c d) <$> parseOperator

  private def parsePlusCalAlgorithm : TLAPlusParser (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
    let ⟨pos, .pcal tks⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .pcal _⟩ => true | _ => false
      | unreachable!
    let n := Stream.getPosition (← getStream)
    let res ← (SurfacePlusCal.Parser.parseAlgorithm tryParseAnnotations parseExpression).run (TokenStream.ofArray tks.toArray)
    match res with
    | .error _ err =>
      letI err := fromSurfacePlusCalError n pos tks err
      MonadExceptOf.throw err
    | .ok s alg => assert! s.atEnd; return alg
  where
    fromSurfacePlusCalError : _ → _ → _ →
        ParseError (TokenStream (Located' SurfacePlusCal.Token)) (Located' SurfacePlusCal.Token) →
        ParseError (TokenStream (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token))))
          (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token)))
      | n, blockPos, tks, err =>
        { pos := n
          expected := err.expected
          unexpected := match tks[err.pos - 1]? with
            | none => none
            | some ⟨pos, .tla tk⟩ => some ⟨pos, (⟨pos, ·⟩) <$> tk⟩
            | some tk => some ⟨blockPos, .pcal [tk]⟩ }

  /-- Parse a full module. -/
  def parseModule' : TLAPlusParser (Module (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) (List CommentAnnotation)) := located do
    -- TODO(module-junk): handle text before the module header and after the module footer.
    let _ ← lexeme <| tokenFilter λ | ⟨_, .moduleStart _⟩ => true | _ => false
    let _ ← lexeme <| token .module
    let name ← lexeme parseIdentifier
    let _ ← tokenFilter λ | ⟨_, .moduleStart _⟩ => true | _ => false
    let exts ← eoption <| parseExtends
    let decls₁ ← lexeme <| takeMany parseDeclaration
    let alg ← eoption parsePlusCalAlgorithm
    let decls₂ ← lexeme <| takeMany parseDeclaration

    let _ ← lexeme <| tokenFilter (λ | ⟨_, .moduleEnd _⟩ => true | _ => false)
    let _ ← endOfInput

    return {
      name
      «extends» := exts.getD []
      declarations₁ := decls₁.toList.filterMap λ x ↦ (λ y ↦ y @@ posOf x) <$> x
      pcalAlgorithm := alg
      declarations₂ := decls₂.toList.filterMap λ x ↦ (λ y ↦ y @@ posOf x) <$> x
    }

  /-- Parse a full module, always pairing any collected `ParserWarning`s with the result —
  whether or not parsing itself succeeded, so a warning emitted before a fatal parse error still
  reaches the caller. A `DiagT` in all but name (`Id` base), ascribed that way so
  `Driver/Modules.lean` can absorb it directly via `DiagT.lift`.

  `.reverse` because `ParserWarningM` accumulates by prepending (`Parser_/Common.lean`,
  `modify (w :: ·)` — O(1) per warning, unlike appending), so its list is newest-first. Every
  other pass reports through `DiagT`, whose `bind` *appends*, so warnings elsewhere come out in
  source order; reversing here is what puts the parser's on that same footing. -/
  def parseModule (tokens : Array (Located' (Token (Located' SurfacePlusCal.Token)))) :
    DiagT ParserWarning (Unexpected (Token (Located' SurfacePlusCal.Token))) Id
      (Module (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) (List CommentAnnotation)) :=
      let (res, warnings) := (parseModule'.run (TokenStream.ofArray tokens)).run []
      (warnings.reverse, match res with
      | .error _ e => .error <| errToUnexpected e
      | .ok _ mod => .ok mod)
  where
    errToUnexpected (e : ParseError (TokenStream _) (Located' (Token (Located' SurfacePlusCal.Token)))) :
        Unexpected _ :=
      match e.unexpected with
      -- `e.pos` points past the end of `tokens` when the error is genuinely "ran out of input"
      -- (e.g. an unterminated module) -- fall back to the last real token's position rather
      -- than panicking on an out-of-bounds index.
      | none =>
        { token := .none
          pos := e.posOverride.getD ((tokens[e.pos]? <|> tokens[tokens.size - 1]?).elim default (·.segment))
          hints := e.expectedHints }
      -- If an error occurs within a PlusCal algorithm, `.pcal [tk]` is returned as the offending token
      | some ⟨_, .pcal [tk]⟩ =>
        { token := .some (.pcal [tk]), pos := e.posOverride.getD tk.segment, hints := e.expectedHints }
      | some ⟨pos, tk⟩ =>
        { token := .some tk, pos := e.posOverride.getD pos, hints := e.expectedHints }
end SurfaceTLAPlus.Parser

end
