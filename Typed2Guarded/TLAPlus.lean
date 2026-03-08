import PlusCalCompiler.SurfaceTLAPlus.Syntax
import PlusCalCompiler.CoreTLAPlus.Syntax
import PlusCalCompiler.Passes.SourceCodeToSurface.Annotations
import PlusCalCompiler.Passes.SurfaceToGuarded.PlusCal

namespace SurfaceTLAPlus
  inductive CoreTranslationError
    | unsupportedExpressionKind (pos : SourceSpan) (e : Expression Annotation)
    | invalidDottedAccessor (pos : SourceSpan)
    | seqWrongArgument (pos : SourceSpan)
    | transError (e : SurfacePlusCal.TranslationError)

  inductive CoreTranslationWarning
    | transWarning (w : SurfacePlusCal.TranslationWarning)

  instance : CompilerDiagnostic SurfaceTLAPlus.CoreTranslationError String where
    isError := true
    msgOf
      | .unsupportedExpressionKind _ e => s!"Unsupported expression {repr e}"
      | .invalidDottedAccessor _ => s!"Expression after '.' must be an identifier."
      | .seqWrongArgument _ => "Builtin function `Seq` expects a single sequence literal as argument."
      | .transError err => CompilerDiagnostic.msgOf err
    posOf
      | .unsupportedExpressionKind pos _
      | .invalidDottedAccessor pos
      | .seqWrongArgument pos => pos
      | .transError err => CompilerDiagnostic.posOf err

  instance : CompilerDiagnostic SurfaceTLAPlus.CoreTranslationWarning String where
    isError := false
    msgOf
      | .transWarning err => CompilerDiagnostic.msgOf err
    posOf
      | .transWarning err => CompilerDiagnostic.posOf err

  variable {m : Type → Type} [Monad m] [MonadExcept CoreTranslationError m] [MonadWriter (List CoreTranslationWarning) m]

  open private variableHasTypeAndInit? from PlusCalCompiler.Passes.SurfaceToGuarded.PlusCal in
  private nonrec def variableHasTypeAndInit? (var : Located String) (anns : List Annotation) («=|∈» : Bool) (init : Located (Expression Annotation)) : m (Typ × Bool × Located (Expression Annotation)) :=
    -- Is there a better way to do this?
    letI tmp : Except SurfacePlusCal.TranslationError (_ × List SurfacePlusCal.TranslationWarning) :=
      WriterT.run <| variableHasTypeAndInit? var anns (some ⟨«=|∈», init⟩)
    match tmp with
    | .error err => throw (.transError err)
    | .ok ⟨res, warns⟩ => res <$ tell (.transWarning <$> warns)

  private partial def toCore' (pos : SourceSpan) : Expression Annotation → m (CoreTLAPlus.Expression Typ)
    | .var v => pure (.var v @@ pos)
    | .opCall ⟨pos', fn⟩ args => match fn, args with
      | .var "Seq", [⟨_, .tuple es⟩] => (.seq · @@ pos) <$> traverse ↿toCore' es
      | .var "Seq", _ => throw (.seqWrongArgument pos)
      | e, es => (.opcall · · @@ pos) <$> toCore' pos' e <*> traverse ↿toCore' es
    | e@(.prefixCall ⟨_, op⟩ e₁) => do
      let e₁ ← (↿toCore') e₁
      match op with
      | .«\neg » _ => return .prefix .«¬» e₁ @@ pos
      | _ => throw (.unsupportedExpressionKind pos e)
    | e@(.infixCall e₁ ⟨_, op⟩ e₂) => do
      let e₁ ← (↿toCore') e₁
      let e₂ ← (↿toCore') e₂
      match op with
      | .«\in» => return .infix e₁ .«∈» e₂ @@ pos
      | .«\notin» => return .prefix .«¬» (.infix e₁ .«∈» e₂ @@ pos) @@ pos
      | .«/= » _ => return .prefix .«¬» (.infix e₁ .«=» e₂ @@ pos) @@ pos
      | .«=» => return .infix e₁ .«=» e₂ @@ pos
      | .«.» => match e₂ with
        | .var v => return .access e₁ v @@ pos
        | _ => throw (.invalidDottedAccessor pos)
      | .«\cup » _ => return .infix e₁ .«∪» e₂ @@ pos
      | _ => throw (.unsupportedExpressionKind pos e)
    | e@(.postfixCall _ _) => throw (.unsupportedExpressionKind pos e)
    | .parens ⟨pos, e⟩ => toCore' pos e
    | e@(.bforall _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.bexists _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.forall _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.exists _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.fforall _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.eexists _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.choose _ _ _) => throw (.unsupportedExpressionKind pos e)
    | .set es => (.set · @@ pos) <$> traverse ↿toCore' es
    | e@(.collect _ _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.map' _ _) => throw (.unsupportedExpressionKind pos e)
    | .fnCall fn args => (.funcall · · @@ pos) <$> (↿toCore') fn <*> traverse ↿toCore' args
    | e@(.fn _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.fnSet _ _) => throw (.unsupportedExpressionKind pos e)
    | .record fs => (.record · @@ pos) <$> fs.mapM λ ⟨anns, v, e⟩ ↦ do
      let ⟨τ, _, e⟩ ← variableHasTypeAndInit? v anns true e
      pure ⟨v.data, τ, ← (↿toCore') e⟩
    | e@(.recordSet _) => throw (.unsupportedExpressionKind pos e)
    | e@(.except _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.recordAccess _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.tuple _) => throw (.unsupportedExpressionKind pos e)
    | e@(.if _ _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.case _ _) => throw (.unsupportedExpressionKind pos e)
    | e@(.conj _) => throw (.unsupportedExpressionKind pos e)
    | e@(.disj _) => throw (.unsupportedExpressionKind pos e)
    | .nat raw => pure (.nat raw @@ pos)
    | .str raw => pure (.str raw @@ pos)
    | e@.at => throw (.unsupportedExpressionKind pos e)
    | e@(.stutter _ _) => throw (.unsupportedExpressionKind pos e)

  def Expression.toCore : Located (Expression Annotation) → Except CoreTranslationError (CoreTLAPlus.Expression Typ × List CoreTranslationWarning) :=
    WriterT.run ∘ ↿toCore'
