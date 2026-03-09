import Parser_.Tokens.TLAPlus
import Parser_.Tokens.PlusCal
import Core.SurfaceTLAPlus.Syntax
import Core.SurfacePlusCal.Syntax
import Common.Position
import Parser
import CustomPrelude
import Parser_.PlusCal
import Mathlib.Data.List.Basic
import Parser_.Common
import Common.Errors
import Mathlib.Logic.Function.Basic


/-! # A small lexer for TLA⁺ -/

namespace SurfaceTLAPlus.Lexer
  open Parser hiding eoption takeMany1 takeMany first
  open Char

  section
    variable {σ τ α : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ]

    /-- Surrounds the result of a parser `p` with its starting and ending positions. -/
    private def located (p : SimpleParserT PositionedSlice Char m α) : SimpleParserT PositionedSlice Char m (Located α) := do
      let startPos ← getPosition
      let res ← p
      let endPos ← getPosition
      return { segment := ⟨startPos, endPos⟩, data := res }

    /--
      A parser designed to ignore whitespaces, given `p₁` a parser which consumes (at least 1) whitespace,
      `p₂` a parser consuming line comments and `p₃` a parser consuming block comments.
    -/
    @[inline]
    private def space [lt : LT (Stream.Position σ)] [le : LE (Stream.Position σ)] [DecidableRel lt.lt] [DecidableRel le.le] (p₁ p₂ p₃ : SimpleParserT σ τ m PUnit) : SimpleParserT σ τ m PUnit
      := dropMany <| first [p₁, p₂, p₃]

    @[inline]
    private def empty : SimpleParserT σ τ m PUnit :=
      throwUnexpected none

    /-- Parse "blank" tokens, i.e. tokens which convey no syntactical relevance. -/
    @[inline]
    private def ws [Parser.Stream σ Char] [lt : LT (Stream.Position σ)] [le : LE (Stream.Position σ)] [DecidableRel lt.lt] [DecidableRel le.le] : SimpleParserT σ Char m PUnit
      := space (Unicode.whitespace >>= λ | '\t' => throwUnexpectedWithMessage (some '\t') "Horizontal tab characters (U+0009) are forbidden." | _ => pure ()) empty empty

    /-- Try to apply a parser, then consume some whitespace as defined by `SurfaceTLAPlus.Lexer.ws`. -/
    @[inline]
    private def lexeme [Parser.Stream σ Char] [lt : LT (Stream.Position σ)] [le : LE (Stream.Position σ)] [DecidableRel lt.lt] [DecidableRel le.le] (p : SimpleParserT σ Char m α) : SimpleParserT σ Char m α :=
      p <* ws
  end

  section Tokens
    /-- Lex either a keyword or an identifier. -/
    private def identifierOrKeyword {α} : TLAPlusLexer (Token α) := do
      let c ← Unicode.alpha <|> char '_'
      let cs ← takeMany (withBacktracking <| Unicode.alpha <|> char '_' <|> (String.front ∘ toString) <$> Unicode.digit)

      return mapKeywordToToken (String.ofList (cs.insertIdx 0 c).toList)
    where
      -- TODO: add all TLA⁺ reserved words
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

    /-- Lex an operator or a reserved symbol. -/
    private def symbol {α} : TLAPlusLexer (Token α) := first [
      (.moduleStart ∘ Array.size) <$> takeManyN 4 (char '-'),
      (.moduleEnd ∘ Array.size) <$> takeManyN 4 (char '='),
      -- LaTeX-like notations or set difference or disjunction
      char '\\' *> first [
        char 'i' *> first [
          char 'n' *> first [
            .infix .«\intersect» <$ chars "tersect",
            pure (.infix .«\in»)
          ]
        ],
        char 'n' *> first [
          .infix .«\notin» <$ chars "otin",
          .prefix .«\neg» <$ chars "eg"
        ],
        -- .«\AA» <$ chars "AA",
        .«\A» <$ char 'A',
        .«\E» <$ char 'E',
        char 'c' *> first [
          .infix .«\cup» <$ chars "up",
          .infix .«\cap» <$ chars "ap",
          .infix .«\circ» <$ chars "irc",
          .infix .«\cong» <$ chars "ong",
          .infix .«\cdot» <$ chars "dot"
        ],
        char 'o' *> first [
          .infix .«\oplus» <$ chars "plus",
          .infix .«\ominus» <$ chars "minus",
          .infix .«\odot» <$ chars "dot",
          .infix .«\otimes» <$ chars "times",
          .infix .«\oslash» <$ chars "slash",
          pure (.infix .«\o»)
        ],
        char 'l' *> first [
          .prefix .«\lnot» <$ chars "not",
          .infix .«\land» <$ chars "and",
          .infix .«\lor» <$ chars "or",
          .infix .«\leq» <$ chars "eq",
          .infix .«\ll» <$ chars "l"
        ],
        char 'p' *> first [
          char 'r' *> first [
            char 'e' *> first [
              char 'c' *> first [
                .infix .«\preceq» <$ chars "eq",
                pure (.infix .«\prec»)
              ]
            ],
            .infix .«\propto» <$ chars "opto"
          ]
        ],
        char 's' *> first [
          char 'u' *> first [
            char 'b' *> first [
              chars "set" *> first [
                .infix .«\subseteq» <$ chars "eq",
                pure (.infix .«\subset»)
              ]
            ],
            char 'p' *> first [
              chars "set" *> first [
                .infix .«\supseteq» <$ chars "eq",
                pure (.infix .«\supset»)
              ]
            ],
            chars "cc" *> first [
              .infix .«\succeq» <$ chars "eq",
              pure (.infix .«\succ»)
            ]
          ],
          char 'q' *> first [
            char 'c' *> first [
              .infix .«\sqcap» <$ chars "ap",
              .infix .«\sqcup» <$ chars "up"
            ],
            chars "su" *> first [
              char 'b' *> first [
                chars "set" *> first [
                  .infix .«\sqsubseteq» <$ chars "eq",
                  pure (.infix .«\sqsubset»)
                ]
              ],
              char 'p' *> first [
                chars "set" *> first [
                  .infix .«\sqsupseteq» <$ chars "eq",
                  pure (.infix .«\sqsupset»)
                ]
              ]
            ]
          ],
          chars "im" *> first [
            .infix .«\simeq» <$ chars "eq",
            pure (.infix .«\sim»)
          ],
          .infix .«\star» <$ chars "tar"
        ],
        char 'g' *> first [
          .infix .«\geq» <$ chars "eq",
          .infix .«\gg» <$ char 'g'
        ],
        char 'u' *> first [
          .infix .«\union» <$ chars "nion",
          .infix .«\uplus» <$ chars "plus"
        ],
        .infix .«\times» <$ chars "times",
        .infix .«\wr» <$ chars "wr",
        char 'd' *> first [
          .infix .«\div» <$ chars "iv",
          .infix .«\doteq» <$ chars "oteq"
        ],
        char 'b' *> first [
          .infix .«\bullet» <$ chars "ullet",
          .infix .«\bigcirc» <$ chars "igcirc"
        ],
        char 'a' *> first [
          .infix .«\asymp» <$ chars "symp",
          .infix .«\approx» <$ chars "pprox"
        ],
        .infix .«\equiv» <$ chars "equiv",
        .infix .«\X» <$ char 'X',
        .infix .«\/» <$ char '/',
        pure (.infix .«\»)
      ],
      -- Other operators
      char '.' *> first [
        char '.' *> first [
          .infix .«...» <$ char '.',
          pure (.infix .«..»)
        ],
        pure (.infix .«.»)
      ],
      char '=' *> first [
        .eqeq false <$ char '=',
        .infix .«=>» <$ char '>',
        .infix .«=|» <$ char '|',
        .infix .«=<» <$ char '<',
        pure (.infix .«=»)
      ],
      .comma <$ char ',',
      char '(' *> first [
        .infix .«(+)» <$ chars "+)",
        .infix .«(-)» <$ chars "-)",
        .infix .«(.)» <$ chars ".)",
        .infix .«(/)» <$ chars "/)",
        .infix .«(\X)» <$ chars "\\X)",
        .lparen <$ notFollowedBy (char '*')
      ],
      .rparen <$ char ')',
      char '<' *> first [
        char '=' *> first [
          .infix .«<=>» <$ char '>',
          pure (.infix .«<=»)
        ],
        .langle <$ char '<',
        .prefix .«<>» <$ char '>',
        .infix .«<:» <$ char ':',
        -- .«<-» <$ char '-',
        pure (.infix .«<»)
      ],
      char '>' *> first [
        char '>' *> first [
          .«>>_» <$ char '_',
          pure .rangle
        ],
        .infix .«>=» <$ char '=',
        pure (.infix .«>»)
      ],
      char '-' *> first [
        .«->» <$ char '>',
        .infix .«-+->» <$ chars "+->",
        .infix .«--» <$ char '-',
        pure (.infix .«-»)
      ],
      char '|' *> first [
        char '-' *> first [
          .«|->» <$ char '>',
          pure (.infix .«|-»)
        ],
        .infix .«||» <$ char '|',
        .infix .«|=» <$ char '=',
        pure (.infix .«|»)
      ],
      .lbrace <$ char '{',
      .rbrace <$ char '}',
      char '/' *> first [
        .infix .«/\» <$ char '\\',
        .infix .«/=» <$ char '=',
        .infix .«//» <$ char '/',
        pure (.infix .«/»)
      ],
      char '[' *> first [
        .prefix .«[]» <$ char ']' <* notFollowedBy (char '_'),
        pure .lbracket
      ],
      char ']' *> first [
        .«]_» <$ char '_',
        pure .rbracket
      ],
      char ':' *> first [
        .infix .«::=» <$ chars ":=",
        .infix .«:=» <$ char '=',
        .infix .«:>» <$ char '>',
        pure .colon
      ],
      char '~' *> first [
        .infix .«~>» <$ char '>',
        pure (.prefix .«~»)
      ],
      char '^' *> first [
        .infix .«^^» <$ char '^',
        .postfix .«^+» <$ char '+',
        .postfix .«^*» <$ char '*',
        .postfix .«^#» <$ char '#',
        pure (.infix .«^»)
      ],
      char '+' *> first [
        .infix .«++» <$ char '+',
        pure (.infix .«+»)
      ],
      .postfix .«'» <$ char '\'',
      char '!' *> first [
        .infix .«!!» <$ char '!',
        pure .bang
      ],
      char '#' *> first [
        .infix .«##» <$ char '#',
        pure (.infix .«#»)
      ],
      char '$' *> first [
        .infix .«$$» <$ char '$',
        pure (.infix .«$»)
      ],
      char '%' *> first [
        .infix .«%%» <$ char '%',
        pure (.infix .«%»)
      ],
      char '&' *> first [
        .infix .«&&» <$ char '&',
        pure (.infix .«&»)
      ],
      char '*' *> first [
        .infix .«**» <$ char '*',
        pure (.infix .«*»)
      ],
      char '?' *> first [
        .infix .«??» <$ char '?',
        pure (.infix .«?»)
      ],
      char '@' *> first [
        .infix .«@@» <$ char '@',
        pure .at
      ]
    ]

    private def lineComment {α} : TLAPlusLexer (Token α) := do
      let _ ← chars r"\*"
      let ⟨content, _⟩ ← takeUntil (() <$ eol <|> endOfInput) anyToken
      -- TODO: perhaps there is a faster way to convert an array into a string?
      return .inlineComment <| String.ofList <| Array.toList content

    private partial def blockComment (lexTLAToken : TLAPlusLexer (Located (Token (Located SurfacePlusCal.Token)))) (inner : Bool := false) : TLAPlusLexer (Token (Located SurfacePlusCal.Token)) := do
      let _ ← chars "(*"
      unless inner do
        let isAlg ← test <| lookAhead do
          -- NOTE: big assumption that the comment actually starts with the algorithm, not random junk.
          --       maybe one day we'll remove that?
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

    -- TODO: support binary, octal and hexadecimal formats
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

  /-- Lex a full TLA⁺ token, may it be an operator, a reserved word, an identifier, or anything else really. -/
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
      -- TODO: we need to patch positions: from byte indices to line/column in UTF-8 codepoints
      --       this is very inefficient, as we have to traverse the whole token list, and overlapping
      --       parts of the stream for each token
      --       maybe one day I'll fix that, if it ends up being too slow?
      .inr <| tokens.map λ ⟨pos, tok⟩ ↦ ⟨mkPosition pos, (λ ⟨pos, tok⟩ ↦ ⟨mkPosition pos, tok⟩) <$> tok⟩
  where
    @[inline]
    posToLineCol (pos : Stream.Position PositionedSlice) : Cursor := pos.2

    mkPosition (seg : Stream.Segment PositionedSlice) : SourceSpan :=
      ⟨posToLineCol seg.start, posToLineCol seg.stop⟩

    errToUnexpected : Parser.Error.Simple PositionedSlice Char → Unexpected Char
      | .unexpected pos token => { token, pos := mkPosition ⟨pos, pos⟩, hints := [] }
      | .addMessage err _ msg => let err := errToUnexpected err; {err with hints := err.hints.concat msg }

  -- #eval show IO _ from do
  --   return lexModule (← IO.FS.readFile "tests/LamportMutex/LamportMutex2.tla")
  -- #eval do return (← IO.FS.readFile "tests/LamportMutex/LamportMutex.tla").get {byteIdx := 6450}
end SurfaceTLAPlus.Lexer



/-! # Main parser for a single TLA⁺ module -/

namespace SurfaceTLAPlus.Parser
  open _root_.Parser hiding eoption takeMany1 takeMany first

  /--
    Attaches some location information to the result of a parser.
  -/
  private def located {α} (p : TLAPlusParser α) : TLAPlusParser α := do
    let s ← getStream
    let ⟨res, start, «end»⟩ ← withCapture p

    if s.next.isEmpty then
      -- EOF has been reached
      let ⟨pos₁, _⟩ := fetchTk start s
      let ⟨pos₂, _⟩ := fetchTk («end» - 1) s
      return res @@ pos₁ ++ pos₂
    else
      let ⟨pos₁, _⟩ := fetchTk start s
      let ⟨pos₂, _⟩ := fetchTk «end» s
      return res @@ pos₁ ++ pos₂
  where
    fetchTk (n : Nat) (s : Stream.OfList _) :=
      if n ≥ s.past.length then
        s.next[n - s.past.length - 1]!
      else
        s.past[n]!

  /--
    Removes "blank" tokens when parsing. Be careful so as to not call this too much, as we still
    want to keep comments for type annotations in some places.
  -/
  @[inline]
  private def ws : TLAPlusParser PUnit :=
    dropMany <| tokenFilter (λ | ⟨_, .inlineComment _⟩ | ⟨_, .blockComment _⟩ => true | _ => false)

  /--
    `lexeme p` applies the parser `p` then tries to consume some "whitespace" as defined by `ws`.
  -/
  @[inline]
  private def lexeme {α} (p : TLAPlusParser α) : TLAPlusParser α := p <* ws

  -- @[inline]
  -- private def optionD {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [DecidableEq (Stream.Position σ)] (default : α) (p : ParserT ε σ τ m α) : ParserT ε σ τ m α :=
  --   Option.getD (dflt := default) <$> p

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
    @[inline]
    private def token (tk : Token (Located' SurfacePlusCal.Token)) : TLAPlusParser (Located' (Token (Located' SurfacePlusCal.Token))) := do
      withBacktracking <| tokenFilter λ ⟨_, tk'⟩ => tk == tk'

    /-- Parse an identifier and return its raw name. -/
    private def parseIdentifier : TLAPlusParser String := do
      let ⟨pos, .identifier str⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .identifier _⟩ => true | _ => false
        | unreachable!
      return str @@ pos

    private def parseNumber : TLAPlusParser String := do
      let ⟨pos, .number raw⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .number _⟩ => true | _ => false
        | unreachable!
      return raw @@ pos

    private def parseString : TLAPlusParser String := do
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
    private def next? {σ τ} [inst : Parser.Stream σ τ] (s : Parser.Stream.OfList σ) [Repr τ] [Repr σ] : Option (τ × Parser.Stream.OfList σ) :=
      if h : s.next.isEmpty then
        .none
      else match inst.next? <| s.next[0]'(by simpa [List.isEmpty_eq_false_iff, List.length_pos_iff] using h) with
        | .none => next? {next := s.next.drop 1, past := (s.next[0]'(by simpa [List.isEmpty_eq_false_iff, List.length_pos_iff] using h)) :: s.past}
        | .some ⟨tk, s'⟩ =>
          -- dbg_trace "found token {repr tk} at beginning of stream {repr s'}"
          some ⟨tk, {s with next := s.next.modifyHead λ _ ↦ s'}⟩
    termination_by s.next
    decreasing_by
      all_goals simp_wf
      · apply eq_false_of_ne_true at h
        apply List.isEmpty_eq_false_iff.mp at h
        obtain ⟨_, _, s_next_eq⟩ := List.exists_cons_of_ne_nil h
        rw [s_next_eq, List.tail_cons]
        decreasing_trivial

    private def getPosition {σ τ} [inst : Parser.Stream σ τ] [Inhabited inst.Position] (s : Parser.Stream.OfList σ) : Nat × inst.Position :=
      if h : s.next.isEmpty then
        if h' : s.past.isEmpty then
          -- TODO: what to return?
          ⟨0, default⟩
        else
          ⟨s.past.length - 1, inst.getPosition <| s.past[s.past.length - 1]'(by apply Nat.sub_one_lt_of_lt; simpa [← List.length_pos_iff] using h')⟩
      else
        ⟨s.past.length, inst.getPosition <| s.next[0]'(by simpa [List.length_pos_iff] using h)⟩

    @[reducible]
    local instance {σ τ} [inst : Parser.Stream σ τ] [Inhabited inst.Position] [Repr τ] [Repr σ] : Parser.Stream (Parser.Stream.OfList σ) τ where
      Position := Nat × inst.Position
      next? s := Annotations.next? s
      getPosition s := Annotations.getPosition s
      setPosition s pos :=
        -- if pos.fst = (Annotations.getPosition s).fst then
        --   {s with next := s.next.modifyHead λ h ↦ inst.setPosition h pos.snd}
        -- else
          let s' := s.setPosition pos.fst
          {s' with next := s'.next.modifyHead λ h ↦ inst.setPosition h pos.snd}

    -- Somehow this does not exist already, as a low priority instance?
    local instance (priority := low) {α β} [LT α] [LT β] : LT (α × β) where
      lt := Prod.Lex LT.lt LT.lt

    local instance {α β} [instLTα : LT α] [instLTβ : LT β] [DecidableRel instLTα.lt] [DecidableRel instLTβ.lt] [DecidableEq α] : @DecidableRel (α × β) (α × β) LT.lt :=
      inferInstanceAs (DecidableRel (Prod.Lex _ _))

    private abbrev TypeParser := SimpleParser (Stream.OfList Substring) Char

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
      let args ← eoption <| first [
        Array.toList <$> (_root_.Parser.token '(' *> sepBy1 (_root_.Parser.token ',' <* ws) arg <* _root_.Parser.token ')'),
        do
          let _ ← ws *> _root_.Parser.token ':' <* ws
          let chars ← takeMany1 (withBacktracking <| tokenFilter λ | '@' | ';' => false | _ => true)
          let _ ← _root_.Parser.token ';'
          return [Sum.inl <| String.ofList chars.toList],
      ]
      return ⟨name, args.toList.flatten⟩
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
        return (sign.elim' "" String.singleton ++ String.mk digits.toList).toInt!

    /-- Try to parse annotations in a comment, ignoring any raw text. -/
    private def tryParseAnnotations' : TypeParser (List (Stream.Position (Stream.OfList Substring) × Stream.Position (Stream.OfList Substring) × CommentAnnotation)) := do
      let ⟨anns, _⟩ ← takeUntil endOfInput <| first [
        .inr <$> located parseAnnotation,
        .inl <$> first [
          withBacktracking (chars r"\@"),
          String.singleton <$> withBacktracking (tokenFilter λ | '@' => false | _ => true)
        ],
      ]
      return anns.toList.filterMap Sum.getRight?

    private def tryParseAnnotations : TLAPlusParser (List CommentAnnotation) := do
      let s ← getStream
      let comments ← takeMany <| withBacktracking <| tokenFilter λ | ⟨_, .inlineComment _⟩ | ⟨_, .blockComment _⟩ => true | _ => false
      let stream := comments.map λ | ⟨_, .inlineComment c⟩ | ⟨_, .blockComment c⟩ => c.toSubstring | _ => unreachable!

      if stream.size = 0 then
        return []
            -- Concatenate all comments into a single one, then try to parse this for annotations
      match tryParseAnnotations'.run (Parser.Stream.mkOfList stream.toList) with
        | .ok s' res =>
          assert! List.Forall (Substring.Raw.bsize · == 0) s'.next
          return res.map λ ⟨start, «end», ann⟩ ↦
            let startPos := comments[start.fst]!.segment
            let endPos := comments[«end».fst]!.segment
            ann @@ startPos ++ endPos
        | .error s' e =>
          dbg_trace e
          let m := Stream.getPosition s
          let ⟨n, _⟩ := Stream.getPosition s'
          throw (Error.unexpected (m + n) none) -- TODO: use `e` to report a better error
  end Annotations
  export Annotations (tryParseAnnotations)

  section Expressions
    private def parseInfixOperator (ws : TLAPlusParser PUnit) : TLAPlusParser InfixOperator := debug "infix op" <| lexeme do
      match ← withBacktracking <| ws *> tokenFilter λ | ⟨_, .infix _⟩ | ⟨_, .prefix .«-»⟩ => true | _ => false with
        | ⟨pos, .infix op⟩ => return op @@ pos
        | ⟨pos, .prefix .«-»⟩ => return .«-» @@ pos
        | ⟨_, _⟩ => unreachable!

    private def parsePrefixOperator : TLAPlusParser PrefixOperator := do
      let ⟨pos, .prefix op⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .prefix _⟩ => true | _ => false
        | unreachable!
      return op @@ pos

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
          | .«?» => (0, 20) -- NOTE: conflict with all operators, as I don't know what this operator is supposed to be
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
        -- Somehow there's no right associative operator in TLA+?
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
      /--
        A modified version of the Shunting Yard algorithm for parsing expressions with infix operators.
        In our case, we also need to handle prefix and postfix operators and conflicts between precedence ranges.
      -/
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
            | .index ⟨funOrOp, args⟩, e :: es => ((if funOrOp then Expression.fnCall else .opCall) e args @@ posOf funOrOp ++ posOf e) :: es
            | _, _ => unreachable!
    end ShuntingYardAlgorithm

    section
      variable (ws : TLAPlusParser PUnit) (expr : TLAPlusParser PUnit → TLAPlusParser (Expression (List CommentAnnotation)))

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

      private def parseRecordLiteral : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> do
        -- NOTE: do not use `brackets` here, as it may gobble type annotations
        let _ ← token .lbracket
        let fields ← sepBy1 comma do
          let anns ← tryParseAnnotations
          let var ← ws *> parseIdentifier
          let _ ← ws *> token .«|->»
          let expr ← expr ws
          return ⟨anns, var, expr⟩
        let _ ← token .rbracket
        return .record fields.toList

      private def parseQuantifierBound : TLAPlusParser (QuantifierBound (List CommentAnnotation) (Expression (List CommentAnnotation))) := first [
        -- TODO: parse annotations
        .varTuple <$> angles (Array.toList <$> sepBy1 (ws *> comma) ((·, ·)
          <$> (ws *> tryParseAnnotations)
          <*> (ws *> parseIdentifier))),
        do
          let vs ← sepBy1 (ws *> comma) ((·, ·) <$> (ws *> tryParseAnnotations) <*> (ws *> parseIdentifier))
          return if h : vs.size = 1 then QuantifierBound.var vs[0].fst vs[0].snd else .vars (Array.toList vs)
      ] <*> do
        let _ ← ws *> token (.infix .«\in»)
        expr ws

      private def parseFunctionLiteral : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> brackets do
        let qs ← Array.toList <$> sepBy1 (ws *> comma) (parseQuantifierBound ws expr)
        let _ ← ws *> token .«|->»
        let expr ← expr ws
        return .fn qs expr

      private def parseSetLiteral : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> braces do
        let es ← sepBy (ws *> comma) (expr ws)
        return .set es.toList

      private def parseTupleLiteral : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> angles do
        let es ← sepBy (ws *> comma) (expr ws)
        return .tuple es.toList

      private def parseQuantifier : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> do
        let q ← token .«\A» <|> token .«\E»
        let vars ← first [
          Sum.inl <$> sepBy1 (lexeme comma) (parseQuantifierBound ws expr),
          Sum.inr <$> sepBy1 (lexeme comma) parseIdentifier,
        ]
        let _ ← lexeme <| token .colon
        let e ← expr ws
        return match q, vars with
          | ⟨_, .«\A»⟩, .inl qs => .bforall qs.toList e
          | ⟨_, .«\E»⟩, .inl qs => .bexists qs.toList e
          | ⟨_, .«\A»⟩, .inr vs => .forall vs.toList e
          | ⟨_, .«\E»⟩, .inr vs => .exists vs.toList e
          | _, _ => unreachable!

      private def parseExcept (expr' : TLAPlusParser PUnit → Bool → TLAPlusParser (Expression (List CommentAnnotation))) : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> brackets do
        let e ← expr ws
        let _ ← ws *> token .except
        let upds ← sepBy1 (ws *> comma) do
          let _ ← ws *> token .bang
          let index ← ws *> takeMany1 (first [
            Sum.inl <$> (token (.infix .«.») *> parseIdentifier),
            .inr <$> brackets (Array.toList <$> sepBy1 (ws *> comma) (expr ws)),
          ])
          let _ ← ws *> token (.infix .«=»)
          let e ← expr' ws true
          return ⟨index.toList, e⟩
        return .except e upds.toList

      private def parseSetMap : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> braces do
        let e ← expr ws
        let _ ← ws *> token .colon
        let qs ← sepBy1 (ws *> comma) (parseQuantifierBound ws expr)
        return .map' e qs.toList

      private def parseFunctionSet : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> brackets do
        let e₁ ← expr ws
        let _ ← ws *> token .«->»
        let e₂ ← expr ws
        return .fnSet e₁ e₂

      private def parseCase : TLAPlusParser (Expression (List CommentAnnotation)) := located <| ws *> do
        let _ ← token .case
        let branches ← sepBy1 (ws *> token (.prefix .«[]»)) do
          let cond ← expr ws
          let _ ← ws *> token .«->»
          let e ← expr ws
          return ⟨cond, e⟩
        let other ← eoption do
          let _ ← ws *> token (.prefix .«[]»)
          expr ws
        return .case branches.toList other
    end

    mutual
      private partial def parseAtom (ws : TLAPlusParser PUnit) (inUpdate : Bool := false) : TLAPlusParser (Expression (List CommentAnnotation)) := first [
        (.nat ·) <$> parseNumber,
        (.var ·) <$> parseIdentifier,
        (.str ·) <$> parseString,
        if inUpdate then .at <$ token .at else throwUnexpected none,
        parseIfThenElse ws (parseExpression · inUpdate),
        parseJList (parseExpression · inUpdate),
        parseRecordLiteral ws (parseExpression · inUpdate),
        parseFunctionLiteral ws (parseExpression · inUpdate),
        parseTupleLiteral ws (parseExpression · inUpdate),
        parseSetLiteral ws (parseExpression · inUpdate),
        parseQuantifier ws (parseExpression · inUpdate),
        parseExcept ws (parseExpression · inUpdate) (parseExpression · ·),
        -- parse collect BEFORE map because, as stated in "Specifying Systems",
        -- `{x ∈ S : x ∈ T}` should be parsed as a collect, not a map
        parseSetMap ws (parseExpression · inUpdate),
        parseFunctionSet ws (parseExpression · inUpdate),
        parseCase ws (parseExpression · inUpdate),
        located (.parens <$> parens (parseExpression ws inUpdate)),
        located do
          let _ ← lexeme <| token .lbracket
          let e ← parseExpression ws inUpdate
          let _ ← lexeme <| token .«]_»
          let a ← parseAtom ws inUpdate
          return .stutter e a
      ]

      partial def parseExpression (ws : TLAPlusParser PUnit := pure ()) (inUpdate : Bool := false) : TLAPlusParser (Expression (List CommentAnnotation)) := debug "expression" <| withErrorMessage "expected expression" do
        let ⟨atoms, infixOps⟩ ← sepAccBy1 (parseInfixOperator ws) parseInfixAtom
        let expr := orderInput atoms (OperatorOrExpression.infix <$> infixOps)
        shuntingYard expr
      where
        /--
          An infix atom is an atom, optionally prefixed with some prefix operators,
          and optionally followed by some postfix operators.
        -/
        @[inline]
        parseInfixAtom : TLAPlusParser (List OperatorOrExpression) := do
          let prefixOps ← Array.map .prefix <$> takeMany parsePrefixOperator
          let atom ← .atom <$> parseAtom ws inUpdate
          let postfixOps ← Array.map .postfix <$> takeMany parsePostfixOperator
          let indices ← takeMany <| first [
            .index <$> located ((Prod.mk true ∘ Array.toList) <$> brackets (sepBy1 comma <| parseExpression ws inUpdate)),
            .index <$> located ((Prod.mk false ∘ Array.toList) <$> parens (sepBy comma <| parseExpression ws inUpdate)),
          ]
          return (prefixOps ++ #[atom] ++ postfixOps ++ indices).toList

        orderInput {α} : List (List α) → List α → List α
          | [x], [] => x
          | x :: xs, o :: os => x ++ (o :: orderInput xs os)
          | _, _ => unreachable!
    end
  end Expressions

  /-- Parse an `EXTENDS` clause. -/
  private def parseExtends : TLAPlusParser (List String) := do
    let _ ← lexeme <| token .extends
    let mods ← sepBy1 (lexeme comma) parseIdentifier
    return mods.toList

  private def parseAssume : TLAPlusParser (Expression (List CommentAnnotation)) := debug "assume" do
    let _ ← withBacktracking <| token .assume
    parseExpression

  private def parseConstants : TLAPlusParser (List (String × List CommentAnnotation)) := debug "constant" do
    let _ ← withBacktracking <| lexeme (pure ()) *> (token .constant <|> token .constants)

    let vars ← sepBy1 comma do
      let ann ← tryParseAnnotations
      let var ← parseIdentifier
      return ⟨var, ann⟩
    return vars.toList

  private def parseVariables : TLAPlusParser (List (String × List CommentAnnotation)) := debug "variables" do
    let _ ← withBacktracking <| lexeme (pure ()) *> (token .variable <|> token .variables)

    let vars ← sepBy1 comma do
      let ann ← tryParseAnnotations
      let var ← parseIdentifier
      return ⟨var, ann⟩
    return vars.toList

  private def parseOperator : TLAPlusParser (List CommentAnnotation × String × List (String × Nat) × Expression (List CommentAnnotation)) := debug "operator def" do
    let ann ← tryParseAnnotations
    let var ← parseIdentifier
    let args ← eoption <| lexeme <| parens <| sepBy comma do
      let var ← parseIdentifier
      let argCount ← eoption <| parens <| Array.size <$> sepBy1 comma underscore
      return ⟨var, argCount.getD 0⟩
    let _ ← lexeme <| token (.eqeq false)
    let expr ← parseExpression
    return ⟨ann, var, args.elim [] Array.toList, expr⟩

  private def parseDeclaration : TLAPlusParser (Option (Declaration (List CommentAnnotation))) := located <| first [
    (.some ∘ .assume) <$> parseAssume,
    (.some ∘ .constants) <$> parseConstants,
    (.some ∘ .variables) <$> parseVariables,
    (λ ⟨a, b, c, d⟩ ↦ .some <| .operator a b c d) <$> parseOperator,
    .none <$ tokenFilter λ | ⟨_, .moduleStart _⟩ => true | _ => false
  ]

  private def parsePlusCalAlgorithm : TLAPlusParser (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
    let ⟨pos, .pcal tks⟩ ← withBacktracking <| tokenFilter λ | ⟨_, .pcal _⟩ => true | _ => false
      | unreachable!
    let n := Stream.getPosition (← getStream)
    match (SurfacePlusCal.Parser.parseAlgorithm tryParseAnnotations parseExpression).run (Stream.mkOfList tks) with
    | .error _ err =>
      letI err := fromSurfacePlusCalError n pos tks err
      MonadExceptOf.throw err
    | .ok s alg => assert! s.next.isEmpty; return alg
  where
    fromSurfacePlusCalError : _ → _ → _ → Error.Simple _ _ → Error.Simple _ _
      | n, pos, tks, .unexpected m _ => match tks[m-1]? with
        | none => .unexpected n .none
        | .some ⟨pos, .tla tk⟩ => .unexpected n (some ⟨pos, (⟨pos, ·⟩) <$> tk⟩)
        | .some tk => .unexpected n (some ⟨pos, .pcal [tk]⟩)
      | n, pos, tks, .addMessage err _ msg => .addMessage (fromSurfacePlusCalError n pos tks err) n msg

  /-- Parse a full module. -/
  def parseModule' : TLAPlusParser (Module (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) (List CommentAnnotation)) := located do
    -- TODO: handle junk before module start and after module end
    let _ ← lexeme <| tokenFilter λ | ⟨_, .moduleStart _⟩ => true | _ => false
    let _ ← lexeme <| token .module
    let name ← lexeme parseIdentifier
    let _ ← lexeme <| tokenFilter λ | ⟨_, .moduleStart _⟩ => true | _ => false
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

  def parseModule (tokens : Array (Located' (Token (Located' SurfacePlusCal.Token)))) :
    Unexpected (Token (Located' SurfacePlusCal.Token)) ⊕ Module (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) (List CommentAnnotation) :=
      match parseModule'.run (Stream.mkOfList tokens.toList) with
      | .error _ e => .inl <| errToUnexpected e
      | .ok _ mod => .inr mod
  where
    errToUnexpected : Parser.Error.Simple (Stream.OfList _) (Located' (Token (Located' SurfacePlusCal.Token))) → Unexpected _
      | .unexpected n .none => { token := .none, pos := tokens[n]!.segment, hints := [] }
      -- If an error occurs within a PlusCal algorithm, `.pcal [tk]` is returned as the offending token
      | .unexpected _ (.some ⟨_, .pcal [tk]⟩) => { token := .some (.pcal [tk]), pos := tk.segment, hints := [] }
      | .unexpected _ (.some ⟨pos, tk⟩) => { token := .some tk, pos, hints := [] }
      | .addMessage err _ msg => let err := errToUnexpected err; { err with hints := err.hints.concat msg }

  -- for better errors (to avoid duplicated locations)
  -- local instance {α} [ToString α] : ToString (Located α) where
  --   toString loc := toString loc.data

  -- #eval do
  --   let source ← IO.FS.readFile "tests/TPC/TPC2.tla"
  --   let lines := source.split (· == '\n')

  --   match SurfaceTLAPlus.Lexer.lexModule source with
  --   | .inl e => println! e.pretty lines
  --   | .inr toks => do
  --     -- dbg_trace repr (toks[18]!)
  --     match parseModule toks with
  --     | .inl e => println! e.pretty lines
  --     | .inr mod => println! repr mod
end SurfaceTLAPlus.Parser
