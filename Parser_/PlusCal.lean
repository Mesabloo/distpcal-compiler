module

public import Parser_.Tokens.PlusCal
public import Core.SurfacePlusCal.Syntax
import Parser
meta import CustomPrelude
public import Common.Position
import Extra.List
import Parser_.Common
public import Parser_.Monad

public section

namespace SurfacePlusCal.Lexer
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
    private def space {ε} [Parser.Error ε σ τ] [LE (Stream.Position σ)] [LT (Stream.Position σ)] [DecidableLE (Stream.Position σ)] [DecidableLT (Stream.Position σ)] (p₁ p₂ p₃ : ParserT ε σ τ m PUnit) : ParserT ε σ τ m PUnit
      := dropMany <| first [p₁, p₂, p₃]

    @[inline]
    private def empty {ε} [Parser.Error ε σ τ] : ParserT ε σ τ m PUnit :=
      throwUnexpected none

    /-- Parses a whitespace token -/
    @[inline]
    private def ws {ε} [Parser.Stream σ Char] [Parser.Error ε σ Char] [LE (Stream.Position σ)] [LT (Stream.Position σ)] [DecidableLE (Stream.Position σ)] [DecidableLT (Stream.Position σ)] : ParserT ε σ Char m PUnit
      := space (Unicode.whitespace >>= λ | '\t' => throwUnexpectedWithMessage (some '\t') "Horizontal tab characters (U+0009) are forbidden." | _ => pure ()) empty empty

    /-- Tries to apply a parser, then consume some whitespace as defined by `SurfacePlusCal.Lexer.ws`. -/
    @[inline]
    private def lexeme {ε} [Parser.Stream σ Char] [Parser.Error ε σ Char] [LE (Stream.Position σ)] [LT (Stream.Position σ)] [DecidableLE (Stream.Position σ)] [DecidableLT (Stream.Position σ)] (p : ParserT ε σ Char m α) : ParserT ε σ Char m α :=
      p <* ws
  end

  section Tokens
    /-- `.barbar` (`||`, the multi-assignment separator in `x := e1 || y := e2`) must be tried
    before falling through to the TLA⁺ sub-lexer, otherwise the TLA⁺ lexer's generic `||`
    infix-operator token wins and multi-assignment never parses correctly. -/
    private def symbol : PlusCalLexer Token := first [
      .dashdash <$ chars "--",
      .semicolon <$ char ';',
      .barbar <$ chars "||",
    ]
  end Tokens

  @[inline]
  private def patchTLALexer (lexTLAToken : Unit → PlusCalLexer (Located Token)) : PlusCalLexer (Located Token) := do
    -- Patch the TLA⁺ lexer so it rejects identifiers that are actually PlusCal keywords.
    match ← lexTLAToken () with
    | tk@⟨_, .tla (.identifier x)⟩ => checkReserved x tk
    | tk => return tk
  where
    checkReserved : String → _ → PlusCalLexer _
      | "algorithm", tk => return .algorithm <$ tk
      | "fair", tk => return .fair <$ tk
      | "process", tk => return .process <$ tk
      | "variable", tk => return .variable <$ tk
      | "variables", tk => return .variables <$ tk
      | "fifo", tk => return .fifo <$ tk
      | "fifos", tk => return .fifos <$ tk
      | "channel", tk => return .channel <$ tk
      | "channels", tk => return .channels <$ tk
      | "define", tk => return .define <$ tk
      | "skip", tk => return .skip <$ tk
      | "if", tk => return .if <$ tk
      | "else", tk => return .else <$ tk
      | "while", tk => return .while <$ tk
      | "with", tk => return .with <$ tk
      | "either", tk => return .either <$ tk
      | "or", tk => return .or <$ tk
      | "goto", tk => return .goto <$ tk
      | "when", tk => return .when <$ tk
      | "await", tk => return .await <$ tk
      | "print", tk => return .print <$ tk
      | "assert", tk => return .assert <$ tk
      | "send", tk => return .send <$ tk
      | "receive", tk => return .receive <$ tk
      | "multicast", tk => return .multicast <$ tk
      | _, tk => return tk

  private def lexToken (lexTLAToken : Unit → PlusCalLexer (Located Token)) : PlusCalLexer (Located Token) := first [
    located symbol,
    patchTLALexer lexTLAToken,
  ]

  /-- Lex a full algorithm, until `*)` is reached (but not consumed). -/
  def lexAlgorithm (lexTLAToken : Unit → PlusCalLexer (Located Token)) : PlusCalLexer (Array (Located Token)) := do
    Prod.fst <$> takeUntil (lookAhead <| takeMany1 (withBacktracking <| char '*') <* char ')') (lexeme <| lexToken lexTLAToken)
end SurfacePlusCal.Lexer

namespace SurfacePlusCal.Parser
  open _root_.Parser hiding eoption takeMany1 takeMany first sepBy sepBy1 sepNoEndBy1 sepEndBy1 withBacktracking tokenMap tokenFilter token anyToken withErrorMessage
  open Parser_
  open SurfaceTLAPlus (Expression CommentAnnotation)

  /--
    Attaches some location information to the result of a parser.
  -/
  private def located {α} (p : PlusCalParser α) : PlusCalParser α := do
    let toks := (← getStream).toks
    let ⟨res, start, «end»⟩ ← withCapture p
    let spanAt := λ (i : Nat) ↦ (toks[i]?).elim SourceSpan.placeholder (·.segment)
    return res @@ (spanAt start ++ spanAt (if «end» > start then «end» - 1 else start))

  /-- Drops "blank" tokens. Use sparingly: comments must still be kept in some places, for type
  annotations. -/
  @[inline]
  private def ws : PlusCalParser PUnit :=
    dropMany <| tokenFilter (λ | ⟨_, .tla <| .inlineComment _⟩ | ⟨_, .tla <| .blockComment _⟩ => true | _ => false)

  @[inline]
  private def lexeme {α} (p : PlusCalParser α) : PlusCalParser α := p <* ws

  section Tokens
    /-- Accepts `tk`, failing otherwise with `tk` itself named as what would have matched — every
    call site gets a real "expected" hint for free, no per-site message needed. -/
    @[inline]
    private def token (tk : Token) : PlusCalParser (Located' Token) :=
      withErrorMessage (toString tk) <| withBacktracking <| tokenFilter λ | ⟨_, tk'⟩ => tk' == tk

    @[inline]
    private def comma : PlusCalParser (Located' Token) :=
      token (.tla .comma)

    @[inline]
    private def colon : PlusCalParser (Located' Token) :=
      token (.tla .colon)

    @[inline]
    private def semicolon : PlusCalParser (Located' Token) :=
      token .semicolon

    @[inline]
    private def equals : PlusCalParser (Located' Token) :=
      token (.tla <| .infix .«=»)

    private def parseIdentifier : PlusCalParser String := withErrorMessage "identifier" <| withBacktracking do
      match ← tokenFilter λ | ⟨_, .tla (.identifier _)⟩ => true | _ => false with
      | ⟨pos, .tla (.identifier raw)⟩ => return raw @@ pos
      | _ => unreachable!

    @[inline]
    private def brackets {α} (p : PlusCalParser α) : PlusCalParser α :=
      lexeme (token (.tla .lbracket)) *> p <* (token (.tla .rbracket))

    @[inline]
    private def parens {α} (p : PlusCalParser α) : PlusCalParser α :=
      lexeme (token (.tla .lparen)) *> p <* (token (.tla .rparen))

    @[inline]
    private def braces {α} (p : PlusCalParser α) : PlusCalParser α :=
      lexeme (token (.tla .lbrace)) *> p <* token (.tla .rbrace)
  end Tokens

  @[inline]
  private def patchTLAParser {α} (p : ParserT (ParseError (TokenStream (Located' (SurfaceTLAPlus.Token (Located' Token)))) (Located' (SurfaceTLAPlus.Token (Located' Token)))) (TokenStream (Located' (SurfaceTLAPlus.Token (Located' Token)))) (Located' (SurfaceTLAPlus.Token (Located' Token))) ParserWarningM α) : PlusCalParser α :=
    p.mapStream (λ | ⟨pos, .tla tk⟩ => some ⟨pos, Located'.mk pos <$> tk⟩ | _ => none) (λ ⟨pos, tk⟩ ↦ ⟨pos, .tla <| Located'.data <$> tk⟩)

  /-- `fair process`/`fair+` is parsed for round-tripping but never acted on downstream;
  records a `ParserWarning.fairIgnored` for the CLI driver to render once parsing completes. -/
  private def warnIfFair (isFair : Bool) : PlusCalParser Unit :=
    if isFair then
      (modify (ParserWarning.fairIgnored (posOf isFair) :: ·) : ParserWarningM Unit)
    else
      pure ()

  section
    variable (tryParseAnnotations : ParserT (ParseError (TokenStream (Located' (SurfaceTLAPlus.Token (Located' Token)))) (Located' (SurfaceTLAPlus.Token (Located' Token)))) (TokenStream (Located' (SurfaceTLAPlus.Token (Located' Token)))) (Located' (SurfaceTLAPlus.Token (Located' Token))) ParserWarningM (List CommentAnnotation))
             (parseExpression : ParserT (ParseError (TokenStream (Located' (SurfaceTLAPlus.Token (Located' Token)))) (Located' (SurfaceTLAPlus.Token (Located' Token)))) (TokenStream (Located' (SurfaceTLAPlus.Token (Located' Token)))) (Located' (SurfaceTLAPlus.Token (Located' Token))) ParserWarningM (Expression (List CommentAnnotation)))

    private def parseVariables : PlusCalParser (List (String × List CommentAnnotation × Option (Bool × Expression (List CommentAnnotation)))) := do
      let moreThanOne ← withBacktracking (lexeme (pure ()) *> (false <$ token .variable <|> true <$ token .variables))
      let vars ← (if moreThanOne then sepBy1 comma else Functor.map Array.singleton) do
        let annotations ← patchTLAParser tryParseAnnotations
        let var ← parseIdentifier
        let expr ← eoption do
          Prod.mk <$> (true <$ equals <|> false <$ token (.tla <| .infix .«\in»))
                  <*> patchTLAParser parseExpression
        return ⟨var, annotations, expr⟩
      let _ ← semicolon
      return vars.toList

    private def parseChannels : PlusCalParser (List (String × List CommentAnnotation × List (Expression (List CommentAnnotation)))) := do
      let moreThanOne ← withBacktracking (lexeme (pure ()) *> (false <$ token .channel <|> true <$ token .channels))
      let chans ← (if moreThanOne then sepNoEndBy1 comma else Functor.map Array.singleton) do
        let annotations ← patchTLAParser tryParseAnnotations
        let var ← parseIdentifier
        let exprs ← eoption <| brackets <| sepNoEndBy1 comma <| patchTLAParser parseExpression
        return ⟨var, annotations, exprs.elim [] Array.toList⟩
      let _ ← semicolon
      return chans.toList

    private def parseFifos : PlusCalParser (List (String × List CommentAnnotation × List (Expression (List CommentAnnotation)))) := do
      let moreThanOne ← withBacktracking (lexeme (pure ()) *> (false <$ token .fifo <|> true <$ token .fifos))
      let chans ← (if moreThanOne then sepNoEndBy1 comma else Functor.map Array.singleton) do
        let annotations ← patchTLAParser tryParseAnnotations
        let var ← parseIdentifier
        let exprs ← eoption <| brackets <| sepNoEndBy1 comma <| patchTLAParser parseExpression
        return ⟨var, annotations, exprs.elim [] Array.toList⟩
      let _ ← semicolon
      return chans.toList

    private def parseSkip : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .skip
      return .skip

    private def parseAwait : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .await <|> token .when
      let e ← patchTLAParser parseExpression
      return .await e

    private def parsePrint : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .print
      let e ← patchTLAParser parseExpression
      return .print e

    private def parseAssert : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .assert
      let e ← patchTLAParser parseExpression
      return .assert e

    private def parseGoto : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .goto
      let l ← parseIdentifier
      return .goto l

    private def parseWhile (block : PlusCalParser (List (String ⊕ Statement (List CommentAnnotation) (Expression (List CommentAnnotation))))) : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .while
      let cond ← parens <| patchTLAParser parseExpression
      let b ← block
      return .while cond b

    private def parseIf (block : PlusCalParser (List (String ⊕ Statement (List CommentAnnotation) (Expression (List CommentAnnotation))))) : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .if
      let cond ← parens <| patchTLAParser parseExpression
      let b₁ ← block
      let b₂ ← eoption <| token .else *> block
      return .if cond b₁ b₂

    private def parseRef : PlusCalParser (Ref (Expression (List CommentAnnotation))) := do
      let name ← parseIdentifier
      let segments ← takeMany <| first [
        Sum.inl <$> (token (.tla <| .infix .«.») *> parseIdentifier),
        Sum.inr <$> (Array.toList <$> brackets (sepBy1 (lexeme comma) (patchTLAParser parseExpression))),
      ]
      return { name, args := segments.toList }

    private def parseAssign : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let assigns ← sepNoEndBy1 (lexeme <| token .barbar) do
        let ref ← located (parseRef parseExpression)
        let _ ← token <| .tla <| .infix .«:=»
        let expr ← patchTLAParser parseExpression
        return ⟨ref, expr⟩
      return .assign assigns.toList

    private def parseReceive : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .receive
      let ⟨c, r⟩ ← parens do
        let c ← located <| parseRef parseExpression
        let _ ← comma
        let r ← located <| parseRef parseExpression
        return (⟨c, r⟩ : _ × _)
      return .receive c r

    private def parseSend : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .send
      let ⟨c, e⟩ ← parens do
        let c ← located <| parseRef parseExpression
        let _ ← comma
        let e ← patchTLAParser parseExpression
        return (⟨c, e⟩ : _ × _)
      return .send c e

    private def parseWith (block : PlusCalParser (List (String ⊕ Statement (List CommentAnnotation) (Expression (List CommentAnnotation))))) : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← lexeme <| token .with
      -- Not `parens`: `lexeme`'s trailing-whitespace skip treats comments as whitespace too, so
      -- it would consume any type annotation on the first binder (same reason `parseFilter`,
      -- multicast, avoids `brackets`).
      let _ ← token (.tla .lparen)
      let vars ← sepBy1 (semicolon <|> comma) do
        let annotations ← patchTLAParser tryParseAnnotations
        let var ← parseIdentifier
        let «=|∈» ← located <| true <$ equals <|> false <$ token (.tla (.infix .«\in»))
        let e ← patchTLAParser parseExpression
        return ⟨var, annotations, «=|∈», e⟩
      let _ ← token (.tla .rparen)
      let b ← block
      return .with vars.toList b

    private def parseEither (block : PlusCalParser (List (String ⊕ Statement (List CommentAnnotation) (Expression (List CommentAnnotation))))) : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .either
      let block₁ ← block
      let blocks ← takeMany1 (token .or *> block)
      return .either <| block₁ :: blocks.toList

    private def parseMulticast : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := do
      let _ ← token .multicast
      let ⟨var, filter⟩ ← parens do
        let var ← parseIdentifier
        let _ ← comma
        let filter ← parseFilter
        return (⟨var, filter⟩ : _ × _)
      return .multicast var filter
    where
      parseFilter : PlusCalParser (MulticastFilter (List CommentAnnotation) (Expression (List CommentAnnotation))) := located do
        -- Not `brackets`: it would consume any type annotation given for the bindings.
        let _ ← token (.tla .lbracket)
        let binds ← sepBy1 comma do
          let anns ← patchTLAParser tryParseAnnotations
          let var ← parseIdentifier
          let «=|∈» ← true <$ equals <|> false <$ token (.tla <| .infix .«\in»)
          let val ← patchTLAParser parseExpression
          return ⟨var, anns, «=|∈», val⟩
        let _ ← token (.tla .«|->»)
        let val ← patchTLAParser parseExpression
        let _ ← token (.tla .rbracket)
        return {binds := binds.toList, val}

    mutual
      /-- One statement without its label — chosen by its keyword, `parseAssign` (`x := …`) the
      default. No backtracking: a keyword commits, so an error inside its body reports where it
      happened, not at the keyword. -/
      private partial def parseUnlabeledStatement : PlusCalParser (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))) := lexeme <| located do
        match ← peek with
        | ⟨_, .skip⟩ => parseSkip
        | ⟨_, .goto⟩ => parseGoto
        | ⟨_, .await⟩ | ⟨_, .when⟩ => parseAwait parseExpression
        | ⟨_, .print⟩ => parsePrint parseExpression
        | ⟨_, .assert⟩ => parseAssert parseExpression
        | ⟨_, .while⟩ => parseWhile parseExpression parseStatement
        | ⟨_, .if⟩ => parseIf parseExpression parseStatement
        | ⟨_, .with⟩ => parseWith tryParseAnnotations parseExpression parseStatement
        | ⟨_, .receive⟩ => parseReceive parseExpression
        | ⟨_, .send⟩ => parseSend parseExpression
        | ⟨_, .either⟩ => parseEither parseStatement
        | ⟨_, .multicast⟩ => parseMulticast tryParseAnnotations parseExpression
        | _ => parseAssign parseExpression

      private partial def parseCompoundStatement : PlusCalParser (List (String ⊕ (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))))) := braces do
        let stmts ← sepEndBy1 (lexeme semicolon) parseStatement
        return stmts.toList.flatten

      private partial def parseStatement : PlusCalParser (List (String ⊕ (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))))) := do
        let label? ← eoption <| lexeme <| withBacktracking <| parseIdentifier <* colon
        let stmts ← match ← peek with
          | ⟨_, .tla (.brace true)⟩ => lexeme parseCompoundStatement
          | _ => ([Sum.inr ·]) <$> parseUnlabeledStatement
        return match label? with
          | .none => stmts
          | .some label => .inl label :: stmts
    end

    private def parseThread : PlusCalParser (List (String ⊕ (Statement (List CommentAnnotation) (Expression (List CommentAnnotation))))) := do
      -- A thread is a `{ … }` block. Comments before it are the *next* process's annotations, so
      -- probe for the brace atomically before committing (and before the comment skip sticks).
      let _ ← withBacktracking <| lexeme (pure ()) *> lookAhead (token (.tla .lbrace))
      parseCompoundStatement tryParseAnnotations parseExpression

    private def parseProcess : PlusCalParser (Process (List CommentAnnotation) (Expression (List CommentAnnotation))) := located do
      let annotations ← patchTLAParser tryParseAnnotations
      -- `test (token .fair)` consumes the `fair` and `warnIfFair` emits, both before `process` is
      -- checked — so a stray `fair` with no `process` after it must roll the warning back too.
      let isFair ← withBacktracking do
        let isFair ← located <| test <| token .fair
        let _ ← warnIfFair isFair
        let _ ← token .process
        pure isFair
      let ⟨name, «=|∈», pid⟩ ← parens do
        let var ← parseIdentifier
        let «=|∈» ← true <$ equals <|> false <$ token (.tla <| .infix .«\in»)
        let pid ← patchTLAParser parseExpression
        return (⟨var, «=|∈», pid⟩ : _ × _ × _)
      let «variables» ← Option.getD (dflt := []) <$> eoption (parseVariables tryParseAnnotations parseExpression)
      let threads ← takeMany1 (parseThread tryParseAnnotations parseExpression)
      return {
        ann := annotations
        isFair
        name
        «=|∈»
        id := pid
        localState := {
          «variables»
          channels := []
          fifos := []
        }
        threads := threads.toList
      }

    def parseAlgorithm : PlusCalParser (Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) := located do
      -- TODO(pluscal-decls): support macros, procedures and `define` blocks.
      let _ ← token .dashdash
      let isFair ← withBacktracking do
        let isFair ← located <| test <| token .fair
        let _ ← warnIfFair isFair
        let _ ← token .algorithm
        pure isFair
      let name ← parseIdentifier
      let _ ← lexeme <| token (.tla .lbrace)
      let «variables» ← Option.getD (dflt := []) <$> eoption (parseVariables tryParseAnnotations parseExpression)
      let channels ← Option.getD (dflt := []) <$> eoption (parseChannels tryParseAnnotations parseExpression)
      let fifos ← Option.getD (dflt := []) <$> eoption (parseFifos tryParseAnnotations parseExpression)
      let processes ← takeMany (parseProcess tryParseAnnotations parseExpression)
      let _ ← token (.tla .rbrace)
      let _ ← endOfInput
      return {
        isFair
        name
        globalState := {
          «variables»
          channels
          fifos
        }
        processes := processes.toList
      }
  end
end SurfacePlusCal.Parser

end
