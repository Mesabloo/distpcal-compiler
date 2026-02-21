import PlusCalCompiler.Position
import PlusCalCompiler.SurfaceTLAPlus.Syntax
-- import PlusCalCompiler.SurfacePlusCal.Syntax
import PlusCalCompiler.Errors
import Parser
import PlusCalCompiler.Passes.SourceCodeToSurface.Common
import PlusCalCompiler.Passes.SourceCodeToSurface.TLAPlus

section
  inductive ResolverError
    | invalidArgsLen (pos : SourceSpan) (ann : String) (expected : Nat) (nbArgs : Nat)
    | invalidAnnotationType (pos : SourceSpan) (ann : String) (expected : String)
    | typeParseFailure (pos : SourceSpan)
    | expressionParseFailure (pos : SourceSpan)
    | invalidMailboxSpecification (pos : SourceSpan)

  instance : CompilerDiagnostic ResolverError String where
    isError := true
    msgOf
      | .invalidArgsLen _ ann expected nbArgs => s!"{ann} annotation expects {expected} arguments, but {nbArgs} were found."
      | .invalidAnnotationType _ ann expected => s!"{ann} annotation expects {expected}."
      | .typeParseFailure _ => "Failed to parse type annotation."
      | .expressionParseFailure _ => "Failed to parse expression."
      | .invalidMailboxSpecification _ => "@mailbox annotation expects an expression of the form 'var[e₁, …, eₙ]'."
    posOf
      | .invalidArgsLen pos _ _ _
      | .invalidAnnotationType pos _ _
      | .typeParseFailure pos
      | .expressionParseFailure pos
      | .invalidMailboxSpecification pos => pos

  variable {m : Type _ → Type _} [Monad m] [MonadExcept ResolverError m]

  open SurfaceTLAPlus (Typ Expression CommentAnnotation Module)

  /-- A subset of general annotations, as understood by our tool. -/
  inductive Annotation
    /-- Type information for variables. -/
    | «@type» (_ : Located Typ)
    /-- Mailbox information for PlusCal processes. -/
    | «@mailbox» (_ : SourceSpan) (_ : String) (_ : List (Expression Annotation))
    /-- Functional parameter of a PlusCal process. -/
    | «@parameter»
    deriving Repr, Inhabited, BEq

  def Annotation.name : Annotation → String
    | .«@type» _ => "@type"
    | .«@mailbox» _ _ _ => "@mailbox"
    | .«@parameter» => "@parameter"

  section Types
    open Parser hiding eoption takeMany takeMany1 first
    open Char
    open SurfacePlusCal.Lexer (Located')

    private abbrev TypeParser := SimpleParser String.Slice Char

    @[inline]
    private def ws : TypeParser Unit := dropMany Unicode.whitespace

    @[inline]
    private def between {α β} (p₁ p₂ : TypeParser β) (p : TypeParser α) : TypeParser α :=
      p₁ *> ws *> p <* ws <* p₂

    @[inline]
    private def parens {α} : TypeParser α → TypeParser α :=
      between (char '(') (char ')')

    private partial def chainr1 {α} (p : TypeParser α) (op : TypeParser (α → α → α)) : TypeParser α := scan
    where
      scan := do let x ← p; rest x
      rest x : TypeParser α := first [
        do let f ← op; let y ← p; rest (f x y),
        --             ^^^^^^^^^
        -- TODO: drop error of `op`, but keep error of `p`
        pure x
      ]

    private partial def parseType' : TypeParser Typ := expr
    where
      atom : TypeParser Typ := first [
        .bool <$ chars "Bool" <* ws,
        .int <$ chars "Int" <* ws,
        .address <$ chars "Address" <* ws,
        .str <$ (chars "Str" <* ws),
        .set <$> (chars "Set" *> ws *> parens expr),
        .seq <$> (chars "Seq" *> ws *> parens expr),
        .channel <$> (chars "Channel" *> ws *> parens expr),
        .tuple <$> between (chars "<<") (chars ">>") (Array.toList <$> sepBy1 (char ',' <* ws) expr),
        .record <$> between (char '{') (char '}') (Array.toList <$> sepBy1 (char ',' <* ws) do
          (·, ·)
            <$> (identifier true <* ws <* char ':' <* ws)
            <*> expr
        ),
        .const <$> allCapsIdentifier,
        .var <$> identifier,
        parens expr,
      ]

      /-- Parses a TLA+ identifier in all caps. -/
      allCapsIdentifier : TypeParser String := do
        let char₁ ← tokenFilter λ c => Unicode.isAlphabetic c && Unicode.isUppercase c
        let chars ← takeMany <| withBacktracking <| tokenFilter λ c => (Unicode.isAlphabetic c && Unicode.isUppercase c) || c = '_' || Unicode.isDigit c
        return String.mk <| char₁ :: chars.toList

      /-- Parses a TLA+ identifier starting with a lowercase alphabetic character. -/
      identifier (b := false) : TypeParser String := do
        let char₁ ← tokenFilter λ c => Unicode.isAlphabetic c && (b || Unicode.isLowercase c)
        let chars ← takeMany <| withBacktracking <| tokenFilter λ c => Unicode.isAlphabetic c || c = '_' || Unicode.isDigit c
        return String.mk <| char₁ :: chars.toList

      fn : TypeParser Typ := chainr1 atom (.function <$ (ws *> chars "->" <* ws))

      expr : TypeParser Typ := do
        let argss ← takeMany <| withBacktracking do
          let args ← parens <| sepBy (ws *> char ',' *> ws) fn
          let _ ← ws *> chars "=>" <* ws
          return args.toList
        let ret ← fn
        return argss.foldr (init := ret) .operator

    private def parseType (pos : SourceSpan) (input : String) : m (Located Typ) :=
      match parseType'.run input with
        | .error _ _ => throw <| .typeParseFailure pos
        | .ok s r => do
          unless s.isEmpty do throw <| .typeParseFailure pos
          return ⟨pos, r⟩
  end Types

  section Mailbox
    private def parseMailbox (pos : SourceSpan) (input : String) : m (Located (Expression (Located CommentAnnotation))) := do
      let tks ← match SurfaceTLAPlus.Lexer.lexModule input with
        | .inl _ => throw <| .expressionParseFailure pos
        | .inr x => pure x
      let expr ← match SurfaceTLAPlus.Parser.parseExpression.run (Parser.Stream.mkOfList tks.toList) with
        | .error _ _ => throw <| .expressionParseFailure pos
        | .ok s x =>
          assert! s.next.isEmpty
          pure x
  end Mailbox

  private partial def tryResolveAnnotations (ann : Located CommentAnnotation) : m Annotation :=
    match ann.data with
    | ⟨"type", [.inl arg]⟩ => .«@type» <$> parseType ann.segment arg
    | ⟨"type", [_]⟩ => throw <| .invalidAnnotationType ann.segment "@mailbox" "either a string literal or an inline argument"
    | ⟨"type", args⟩ => throw <| .invalidArgsLen ann.segment "@type" 1 args.length
    | ⟨"mailbox", [.inl expr]⟩ => Sigma.uncurry (Annotation.«@mailbox» ann.segment) <$> do
      match ← parseMailbox ann.segment expr >>= traverse (traverse tryResolveAnnotations) with
        | ⟨_, .var v⟩ => return ⟨v, []⟩
        | ⟨_, .fnCall ⟨_, .var v⟩ args⟩ => return ⟨v, args.map Located.data⟩
        | _ => throw <| .invalidMailboxSpecification ann.segment
    | ⟨"mailbox", [_]⟩ => throw <| .invalidAnnotationType ann.segment "@mailbox" "either a string literal or an inline argument"
    | ⟨"mailbox", args⟩ => throw <| .invalidArgsLen ann.segment "@mailbox" 1 args.length
    | ⟨"parameter", []⟩ => return .«@parameter»
    | ⟨"parameter", args⟩ => throw <| .invalidArgsLen ann.segment "@parameter" 0 args.length
    | _ => unreachable!

  private def resolveAnnotations' : Module (Located (SurfacePlusCal.Algorithm (Located CommentAnnotation))) (Located CommentAnnotation) → m (Module (Located (SurfacePlusCal.Algorithm Annotation)) Annotation) :=
    bitraverse (traverse (traverse tryResolveAnnotations)) tryResolveAnnotations

  def resolveAnnotations : Module (Located (SurfacePlusCal.Algorithm (Located CommentAnnotation))) (Located CommentAnnotation) → Except ResolverError (Module (Located (SurfacePlusCal.Algorithm Annotation)) Annotation) :=
    resolveAnnotations'
end
