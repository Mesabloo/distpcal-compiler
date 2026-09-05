module

import Common.Position
public import Core.SurfaceTLAPlus.Syntax
import Common.Errors
import Parser
public import Parser_.Common
public import Parser_.TLAPlus
meta import CustomPrelude

public section

section
  inductive ResolverError
    | invalidArgsLen (pos : SourceSpan) (ann : String) (expected : Nat) (nbArgs : Nat)
    | invalidAnnotationType (pos : SourceSpan) (ann : String) (expected : String)
    | typeParseFailure (pos : SourceSpan)
    | expressionParseFailure (pos : SourceSpan)
    | invalidMailboxSpecification (pos : SourceSpan)

  instance : CompilerDiagnostic ResolverError String where
    isError := true
    code
      | .invalidArgsLen .. => Diagnostics.annotationArity.code
      | .invalidAnnotationType .. => Diagnostics.annotationArgumentKind.code
      | .typeParseFailure _ => Diagnostics.annotationTypeParse.code
      | .expressionParseFailure _ => Diagnostics.annotationExpressionParse.code
      | .invalidMailboxSpecification _ => Diagnostics.annotationMailboxShape.code
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

  /--
    A subset of general annotations understood by this tool. Each constructor carries its own
    `pos : SourceSpan` explicitly rather than using `Common/Position.lean`'s `@@`/`posOf`
    mechanism, which is unsound for nullary constructors such as `«@parameter»`: they share a
    single tagged scalar representation, so pointer-identity-based position lookup can't
    distinguish separate occurrences.
  -/
  inductive Annotation
    /-- Type information for variables. -/
    | «@type» (pos : SourceSpan) (_ : Typ)
    /-- Mailbox information for PlusCal processes. -/
    | «@mailbox» (pos : SourceSpan) (_ : String) (_ : List (Expression (List Annotation)))
    /-- Functional parameter of a PlusCal process. -/
    | «@parameter» (pos : SourceSpan)
    deriving Repr, Inhabited, BEq

  def Annotation.name : Annotation → String
    | .«@type» _ _ => "@type"
    | .«@mailbox» _ _ _ => "@mailbox"
    | .«@parameter» _ => "@parameter"

  /-- The position of the comment (group) this annotation was parsed from. -/
  def Annotation.posOf : Annotation → SourceSpan
    | .«@type» pos _ => pos
    | .«@mailbox» pos _ _ => pos
    | .«@parameter» pos => pos

  section Types
    open Parser hiding eoption takeMany takeMany1
    open Char

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
        -- TODO(errors): drop `op`'s error but keep `p`'s.
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
        return String.ofList <| char₁ :: chars.toList

      /-- Parses a TLA+ identifier starting with a lowercase alphabetic character. -/
      identifier (b := false) : TypeParser String := do
        let char₁ ← tokenFilter λ c => Unicode.isAlphabetic c && (b || Unicode.isLowercase c)
        let chars ← takeMany <| withBacktracking <| tokenFilter λ c => Unicode.isAlphabetic c || c = '_' || Unicode.isDigit c
        return String.ofList <| char₁ :: chars.toList

      fn : TypeParser Typ := chainr1 atom (.function <$ (ws *> chars "->" <* ws))

      expr : TypeParser Typ := do
        let argss ← takeMany <| withBacktracking do
          let args ← first [
            Array.toList <$> (parens <| sepBy (ws *> char ',' *> ws) expr),
            List.singleton <$> atom,
          ]
          let _ ← ws *> chars "=>" <* ws
          return args
        let ret ← fn
        return argss.foldr (init := ret) .operator

    private def parseType (pos : SourceSpan) (input : String) : m Typ :=
      match parseType'.run input with
        | .error _ _ => throw <| .typeParseFailure pos
        | .ok s r => do
          unless s.isEmpty do throw <| .typeParseFailure pos
          return r
  end Types

  section Mailbox
    private def parseMailbox (pos : SourceSpan) (input : String) : m (Expression (List CommentAnnotation)) := do
      let tks ← match SurfaceTLAPlus.Lexer.lexModule input with
        | .inl _ => throw <| .expressionParseFailure pos
        | .inr x => pure x
      let expr ← match (SurfaceTLAPlus.Parser.parseExpression.run (TokenStream.ofArray tks)).run [] with
        | (.error _ _, _) => throw <| .expressionParseFailure pos
        | (.ok s x, _) =>
          assert! s.atEnd
          pure x
      return expr
  end Mailbox

  private partial def tryResolveAnnotations (ann : CommentAnnotation) : m Annotation :=
    match_source ann with
    | ⟨"type", [.inl arg]⟩, pos => (.«@type» pos <| · @@ pos) <$> parseType pos arg
    | ⟨"type", [_]⟩, pos => throw <| .invalidAnnotationType pos "@mailbox" "either a string literal or an inline argument"
    | ⟨"type", args⟩, pos => throw <| .invalidArgsLen pos "@type" 1 args.length
    | ⟨"mailbox", [.inl expr]⟩, pos => Sigma.uncurry (Annotation.«@mailbox» pos) <$> do
      match ← parseMailbox pos expr >>= traverse (traverse tryResolveAnnotations) with
        | .var v => return ⟨v, []⟩
        | .fnCall (.var v) args => return ⟨v, args⟩
        | _ => throw <| .invalidMailboxSpecification pos
    | ⟨"mailbox", [_]⟩, pos => throw <| .invalidAnnotationType pos "@mailbox" "either a string literal or an inline argument"
    | ⟨"mailbox", args⟩, pos => throw <| .invalidArgsLen pos "@mailbox" 1 args.length
    | ⟨"parameter", []⟩, pos => return .«@parameter» pos
    | ⟨"parameter", args⟩, pos => throw <| .invalidArgsLen pos "@parameter" 0 args.length
    | _, _ => unreachable!

  private def resolveAnnotations' :
      Module (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) (List CommentAnnotation) →
      m (Module (SurfacePlusCal.Algorithm (List Annotation) (Expression (List Annotation))) (List Annotation)) :=
    bitraverse (bitraverse (traverse tryResolveAnnotations) (traverse (traverse tryResolveAnnotations))) (traverse tryResolveAnnotations)

  def resolveAnnotations :
      Module (SurfacePlusCal.Algorithm (List CommentAnnotation) (Expression (List CommentAnnotation))) (List CommentAnnotation) →
      Except ResolverError (Module (SurfacePlusCal.Algorithm (List Annotation) (Expression (List Annotation))) (List Annotation)) :=
    resolveAnnotations'
end

end
