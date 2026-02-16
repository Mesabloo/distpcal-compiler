import PlusCalCompiler.SurfacePlusCal.Tokens
import PlusCalCompiler.SurfacePlusCal.Syntax
import Parser
import CustomPrelude
import PlusCalCompiler.Position
import Extra.List
import PlusCalCompiler.Passes.SourceCodeToSurface.Common

namespace SurfacePlusCal.Lexer
  abbrev PlusCalLexer := SimpleParser Substring Char

  private local instance {α} : Inhabited (PlusCalLexer α) where
    default := Parser.throwUnexpected none

  structure Located' (α : Type _) where
    segment : Parser.Stream.Segment Substring
    data : α
    deriving Functor

  instance {σ τ : Type _} [Parser.Stream σ τ] [Repr (Parser.Stream.Position σ)] : Repr (Parser.Stream.Segment σ) :=
    inferInstanceAs (Repr (_ × _))

  instance {α : Type _} [Repr (Parser.Stream.Segment Substring)] [Repr α] : Repr (Located' α) where
    reprPrec l _ :=
      .bracket
        "{ "
          ("segment" ++ " := " ++ .group (.nest 11 <| repr l.segment) ++ .line ++
           "data" ++ " := " ++ .group (.nest 11 <| repr l.data) ++ .line)
        " }"

  open Parser hiding eoption takeMany1 takeMany
  open Char

  private nonrec def first {σ τ α : Type _} {m : Type _ → Type _}
                           [Monad m] [Parser.Stream σ τ] [LT (Stream.Position σ)] [(p₁ p₂ : Stream.Position σ) → Decidable (p₁ < p₂)]
                           (ps : List (SimpleParserT σ τ m α)) : SimpleParserT σ τ m α := do
    first ps λ | e₁@(.unexpected p₁ _), e₂@(.unexpected p₂ _)
               | e₁@(.unexpected p₁ _), e₂@(.addMessage _ p₂ _)
               | e₁@(.addMessage _ p₁ _), e₂@(.unexpected p₂ _)
               | e₁@(.addMessage _ p₁ _), e₂@(.addMessage _ p₂ _) =>
                 -- Report the error the furthest in the stream.
                 -- This is dumb, but I don't (yet) want to write a custom heuristic to know which error to report
                 -- (similarly to how [`megaparsec`](https://hackage.haskell.org/package/megaparsec) handles them.)
                 if p₁ < p₂ then e₂ else e₁

  section
    variable {σ τ α : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ]

    /-- Surrounds the result of a parser `p` with its starting and ending positions. -/
    private def located (p : SimpleParserT Substring Char m α) : SimpleParserT Substring Char m (Located' α) := do
      let startPos ← getPosition
      let res ← p
      let endPos ← getPosition
      return { segment := ⟨startPos, endPos⟩, data := res }

    /--
      A parser designed to ignore whitespaces, given `p₁` a parser which consumes (at least 1) whitespace,
      `p₂` a parser consuming line comments and `p₃` a parser consuming block comments.
    -/
    @[inline]
    private def space [LT (Stream.Position σ)] [(p₁ p₂ : Stream.Position σ) → Decidable (p₁ < p₂)] (p₁ p₂ p₃ : SimpleParserT σ τ m PUnit) : SimpleParserT σ τ m PUnit
      := dropMany <| first [p₁, p₂, p₃]

    @[inline]
    private def empty : SimpleParserT σ τ m PUnit :=
      throwUnexpected none

    /-- Parses a whitespace token -/
    @[inline]
    private def ws [Parser.Stream σ Char] [LT (Stream.Position σ)] [(p₁ p₂ : Stream.Position σ) → Decidable (p₁ < p₂)] : SimpleParserT σ Char m PUnit
      := space (Unicode.whitespace >>= λ | '\t' => throwUnexpectedWithMessage (some '\t') "Horizontal tab characters (U+0009) are forbidden." | _ => pure ()) empty empty

    /-- Tries to apply a parser, then consume some whitespace as defined by `SurfacePlusCal.Lexer.ws`. -/
    @[inline]
    private def lexeme [Parser.Stream σ Char] [LT (Stream.Position σ)] [(p₁ p₂ : Stream.Position σ) → Decidable (p₁ < p₂)] (p : SimpleParserT σ Char m α) : SimpleParserT σ Char m α :=
      p <* ws
  end

  section Tokens
    -- TODO: write the lexers for tokens (lmao?)

    private def symbol : PlusCalLexer Token := first [
      .dashdash <$ chars "--",
      .semicolon <$ char ';',
    ]
  end Tokens

  @[inline]
  private def patchTLALexer (lexTLAToken : Unit → PlusCalLexer (Located' Token)) : PlusCalLexer (Located' Token) := do
    -- NOTE: patch the TLA⁺ lexer so that it does NOT accept some of our PlusCal-exclusive keywords and stuff
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

  private def lexToken (lexTLAToken : Unit → PlusCalLexer (Located' Token)) : PlusCalLexer (Located' Token) := first [
    located symbol,
    patchTLALexer lexTLAToken,
  ]

  /-- Lex a full algorithm, until `*)` is reached (but not consumed). -/
  def lexAlgorithm (lexTLAToken : Unit → PlusCalLexer (Located' Token)) : PlusCalLexer (Array (Located' Token)) := do
    Prod.fst <$> takeUntil (lookAhead <| takeMany1 (withBacktracking <| char '*') <* char ')') (lexeme <| lexToken lexTLAToken)
end SurfacePlusCal.Lexer

namespace SurfacePlusCal.Parser
  abbrev PlusCalParser := SimpleParser (Parser.Stream.OfList (Located Token)) (Located Token)

  private local instance {α} : Inhabited (PlusCalParser α) where
    default := Parser.throwUnexpected none

  open _root_.Parser hiding eoption takeMany1 takeMany
  open SurfaceTLAPlus (Expression CommentAnnotation)

  private nonrec def first {σ τ α : Type _} {m : Type _ → Type _}
                           [Monad m] [Parser.Stream σ τ] [LT (Stream.Position σ)] [LE (Stream.Position σ)] [(p₁ p₂ : Stream.Position σ) → Decidable (p₁ < p₂)] [(p₁ p₂ : Stream.Position σ) → Decidable (p₁ ≤ p₂)]
                           (ps : List (SimpleParserT σ τ m α)) : SimpleParserT σ τ m α := do
    first ps
      λ | e₁@(.unexpected p₁ _), e₂@(.unexpected p₂ _)
        | e₁@(.addMessage _ p₁ _), e₂@(.addMessage _ p₂ _) =>
          -- Report the error the furthest in the stream.
          -- This is dumb, but I don't (yet) want to write a custom heuristic to know which error to report
          -- (similarly to how [`megaparsec`](https://hackage.haskell.org/package/megaparsec) handles them.)
          if p₁ < p₂ then e₂ else e₁
        | e₁@(.unexpected p₁ _), e₂@(.addMessage _ p₂ _) =>
          if p₁ ≤ p₂ then e₂ else e₁
        | e₁@(.addMessage _ p₁ _), e₂@(.unexpected p₂ _) =>
          if p₁ < p₂ then e₂ else e₁

  /--
    Attaches some location information to the result of a parser.
  -/
  private def located {α} (p : PlusCalParser α) : PlusCalParser (Located α) := do
    let s ← getStream
    let ⟨res, start, «end»⟩ ← withCapture p

    if s.next.isEmpty then
      -- EOF has been reached
      let ⟨⟨start, _⟩, _⟩ := fetchTk start s
      let ⟨⟨_, «end»⟩, _⟩ := fetchTk («end» - 1) s
      return ⟨⟨start, «end»⟩, res⟩
    else
      let ⟨⟨start, _⟩, _⟩ := fetchTk start s
      let ⟨⟨_, «end»⟩, _⟩ := fetchTk «end» s
      return ⟨⟨start, «end»⟩, res⟩
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
  private def ws : PlusCalParser PUnit :=
    dropMany <| tokenFilter (λ | ⟨_, .tla <| .inlineComment _⟩ | ⟨_, .tla <| .blockComment _⟩ => true | _ => false)

  @[inline]
  private def lexeme {α} (p : PlusCalParser α) : PlusCalParser α := p <* ws

  section Tokens
    @[inline]
    private def token (tk : Token) : PlusCalParser (Located Token) :=
      withBacktracking <| tokenFilter λ | ⟨_, tk'⟩ => tk' == tk

    @[inline]
    private def comma : PlusCalParser (Located Token) :=
      token (.tla .comma)

    @[inline]
    private def colon : PlusCalParser (Located Token) :=
      token (.tla .colon)

    @[inline]
    private def semicolon : PlusCalParser (Located Token) :=
      token .semicolon

    @[inline]
    private def equals : PlusCalParser (Located Token) :=
      token (.tla <| .infix .«=»)

    private def parseIdentifier : PlusCalParser (Located String) := withBacktracking do
      match ← tokenFilter λ | ⟨_, .tla (.identifier _)⟩ => true | _ => false with
      | ⟨pos, .tla (.identifier raw)⟩ => return ⟨pos, raw⟩
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
  private def patchTLAParser {α} (p : SimpleParser (Stream.OfList (Located (SurfaceTLAPlus.Token (Located Token)))) (Located (SurfaceTLAPlus.Token (Located Token))) α) : PlusCalParser α :=
    p.mapStream (λ | ⟨pos, .tla tk⟩ => some ⟨pos, Located.mk pos <$> tk⟩ | _ => none) (λ ⟨pos, tk⟩ ↦ ⟨pos, .tla <| Located.data <$> tk⟩)

  section
    variable (tryParseAnnotations : SimpleParser (Parser.Stream.OfList (Located (SurfaceTLAPlus.Token (Located Token)))) (Located (SurfaceTLAPlus.Token (Located Token))) (List (Located CommentAnnotation)))
             (parseExpression : SimpleParser (Parser.Stream.OfList (Located (SurfaceTLAPlus.Token (Located Token)))) (Located (SurfaceTLAPlus.Token (Located Token))) (Located (Expression (Located CommentAnnotation))))

    private def parseVariables : PlusCalParser (List (Located 𝒱 × List (Located CommentAnnotation) × Option (Bool × Located (Expression (Located CommentAnnotation))))) := do
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

    private def parseChannels : PlusCalParser (List (Located 𝒱 × List (Located CommentAnnotation) × List (Located (Expression (Located CommentAnnotation))))) := do
      let moreThanOne ← withBacktracking (lexeme (pure ()) *> (false <$ token .channel <|> true <$ token .channels))
      let chans ← (if moreThanOne then sepNoEndBy1 comma else Functor.map Array.singleton) do
        let annotations ← patchTLAParser tryParseAnnotations
        let var ← parseIdentifier
        let exprs ← eoption <| brackets <| sepNoEndBy1 comma <| patchTLAParser parseExpression
        return ⟨var, annotations, exprs.elim [] Array.toList⟩
      let _ ← semicolon
      return chans.toList

    private def parseFifos : PlusCalParser (List (Located 𝒱 × List (Located CommentAnnotation) × List (Located (Expression (Located CommentAnnotation))))) := do
      let moreThanOne ← withBacktracking (lexeme (pure ()) *> (false <$ token .fifo <|> true <$ token .fifos))
      let chans ← (if moreThanOne then sepNoEndBy1 comma else Functor.map Array.singleton) do
        let annotations ← patchTLAParser tryParseAnnotations
        let var ← parseIdentifier
        let exprs ← eoption <| brackets <| sepNoEndBy1 comma <| patchTLAParser parseExpression
        return ⟨var, annotations, exprs.elim [] Array.toList⟩
      let _ ← semicolon
      return chans.toList

    private def parseSkip : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .skip
      return .skip

    private def parseAwait : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .await <|> token .when
      let e ← patchTLAParser parseExpression
      return .await e

    private def parsePrint : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .print
      let e ← patchTLAParser parseExpression
      return .print e

    private def parseAssert : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .assert
      let e ← patchTLAParser parseExpression
      return .assert e

    private def parseGoto : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .goto
      let l ← parseIdentifier
      return .goto l

    private def parseWhile (block : PlusCalParser (List (Located ℒ ⊕ Located (Statement (Located CommentAnnotation))))) : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .while
      let cond ← parens <| patchTLAParser parseExpression
      let b ← block
      return .while cond b

    private def parseIf (block : PlusCalParser (List (Located ℒ ⊕ Located (Statement (Located CommentAnnotation))))) : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .if
      let cond ← parens <| patchTLAParser parseExpression
      let b₁ ← block
      let b₂ ← eoption <| token .else *> block
      return .if cond b₁ b₂

    private def parseRef : PlusCalParser (Ref (Located CommentAnnotation)) := do
      let ⟨_, name⟩ ← parseIdentifier
      let indices ← takeMany <| brackets <| sepBy1 (lexeme comma) (patchTLAParser parseExpression)
      return { name, args := indices.toList.map Array.toList }

    private def parseAssign : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let assigns ← sepNoEndBy1 (lexeme <| token .barbar) do
        let ref ← located (parseRef parseExpression)
        let _ ← token <| .tla <| .infix .«:=»
        let expr ← patchTLAParser parseExpression
        return ⟨ref, expr⟩
      return .assign assigns.toList

    private def parseReceive : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .receive
      let ⟨c, r⟩ ← parens do
        let c ← located <| parseRef parseExpression
        let _ ← comma
        let r ← located <| parseRef parseExpression
        return (⟨c, r⟩ : _ × _)
      return .receive c r

    private def parseSend : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .send
      let ⟨c, e⟩ ← parens do
        let c ← located <| parseRef parseExpression
        let _ ← comma
        let e ← patchTLAParser parseExpression
        return (⟨c, e⟩ : _ × _)
      return .send c e

    private def parseWith (block : PlusCalParser (List (Located ℒ ⊕ Located (Statement (Located CommentAnnotation))))) : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .with
      let vars ← parens <| sepBy1 (semicolon <|> comma) do
        let var ← parseIdentifier
        let «=|∈» ← located <| false <$ equals <|> true <$ token (.tla (.infix .«\in»))
        let e ← patchTLAParser parseExpression
        return ⟨var, «=|∈», e⟩
      let b ← block
      return .with vars.toList b

    private def parseEither (block : PlusCalParser (List (Located ℒ ⊕ Located (Statement (Located CommentAnnotation))))) : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .either
      let block₁ ← block
      let blocks ← takeMany1 (token .or *> block)
      return .either <| block₁ :: blocks.toList

    private def parseMulticast : PlusCalParser (Statement (Located CommentAnnotation)) := do
      let _ ← token .multicast
      let ⟨var, filter⟩ ← parens do
        let var ← parseIdentifier
        let _ ← comma
        let filter ← parseFilter
        return (⟨var, filter⟩ : _ × _)
      return .multicast var filter
    where
      parseFilter : PlusCalParser (Located (MulticastFilter (Located CommentAnnotation))) := located do
        -- NOTE: don't use `brackets` here, as it will potentially consume any type information given for the bindings
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
      private partial def parseUnlabeledStatement : PlusCalParser (Located (Statement (Located CommentAnnotation))) := lexeme <| located <| first [
        parseSkip,
        parseGoto,
        parseAwait parseExpression,
        parsePrint parseExpression,
        parseAssert parseExpression,
        parseWhile parseExpression parseStatement,
        parseIf parseExpression parseStatement,
        parseWith parseExpression parseStatement,
        parseReceive parseExpression,
        parseSend parseExpression,
        parseEither parseStatement,
        parseMulticast tryParseAnnotations parseExpression,
        parseAssign parseExpression,
      ]

      private partial def parseCompoundStatement : PlusCalParser (List (Located ℒ ⊕ Located (Statement (Located CommentAnnotation)))) := braces do
        let stmts ← sepEndBy1 (lexeme semicolon) parseStatement
        return stmts.toList.flatten

      private partial def parseStatement : PlusCalParser (List (Located 𝒱 ⊕ Located (Statement (Located CommentAnnotation)))) := do
        let label? ← eoption <| lexeme <| withBacktracking <| parseIdentifier <* colon
        let stmts ← first [
          ([Sum.inr ·]) <$> parseUnlabeledStatement,
          lexeme parseCompoundStatement,
        ]
        return match label? with
          | .none => stmts
          | .some label => .inl label :: stmts
    end

    private def parseThread : PlusCalParser (List (Located ℒ ⊕ Located (Statement (Located CommentAnnotation)))) := withBacktracking do
      let _ ← lexeme <| pure ()
      parseCompoundStatement tryParseAnnotations parseExpression

    private def parseProcess : PlusCalParser (Process (Located CommentAnnotation)) := do
      let annotations ← patchTLAParser tryParseAnnotations
      let isFair ← located <| test <| token .fair
      let _ ← token .process
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

    def parseAlgorithm : PlusCalParser (Located (Algorithm (Located CommentAnnotation))) := located do
      -- TODO: support macros, procedures, defines
      let _ ← token .dashdash
      let isFair ← located <| test <| token .fair
      let _ ← token .algorithm
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
