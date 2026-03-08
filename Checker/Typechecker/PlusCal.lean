-- import PlusCalCompiler.Passes.AnnotationChecker.Typechecker.Expressions
import PlusCalCompiler.Passes.AnnotationChecker.Typechecker.Monad
import PlusCalCompiler.SurfacePlusCal.Syntax
import PlusCalCompiler.SurfaceTLAPlus.Syntax
import PlusCalCompiler.Passes.SourceCodeToSurface.Annotations

section
  open SurfaceTLAPlus SurfacePlusCal

  variable {m} [MonadTC m] [Monad m]

  def expectSingleTypeAnnotation (pos : SourceSpan) (anns : List Annotation) : m Typ := do
    let (types, otheranns) := anns.partition λ | .«@type» _ => true | _ => false

    unless otheranns.isEmpty do
      throw <| .unexpectedNonTypeAnnotations pos otheranns

    match types with
    | [] => throw <| .expectedTypeAnnotation pos
    | [.«@type» τ] => return τ
    | _ => throw <| .tooManyTypeAnnotations pos

  variable (checkExpr : Expression (List Annotation) → Typ → m (Expression InternalType))
           (inferExpr : Expression (List Annotation) → m (InternalType × Expression InternalType))

  def checkDeclarations (d : Declarations (List Annotation) (Expression (List Annotation))) : m (Declarations InternalType (Expression InternalType)) := do
    sorry

  @[macro_inline]
  def locallyAddDecls {γ} (decls : Declarations InternalType (Expression InternalType)) : m γ → m γ :=
    letI vars := List.toArray <|
        decls.variables.map (λ (v, τ, _) ↦ (v, τ))
        ++ decls.channels.map (λ (v, τ, _) ↦ (v, τ))
        ++ decls.fifos.map (λ (v, τ, _) ↦ (v, τ))
    withLocalDecls vars

  def checkStatement (S : ℒ ⊕ Statement (List Annotation) (Expression (List Annotation))) : m (ℒ ⊕ Statement InternalType (Expression InternalType)) := do
    sorry

  def checkProcess (p : Process (List Annotation) (Expression (List Annotation))) : m (Process InternalType (Expression InternalType)) := do
    let id ← checkExpr p.id (if p.«=|∈» then .address else .set .address)

    withLocalDecl "self" (InternalType.typ SurfaceTLAPlus.Typ.address) do
      let decls ← checkDeclarations p.localState
      let threads ← locallyAddDecls decls <| traverse (traverse checkStatement) p.threads

      return {
        ann := sorry
        isFair := p.isFair
        name := p.name
        «=|∈» := p.«=|∈»
        id
        localState := decls
        threads
      }

  def checkAlgorithm (a : Algorithm (List Annotation) (Expression (List Annotation))) : m (Algorithm InternalType (Expression InternalType)) := do
    let decls ← checkDeclarations a.globalState
    let ps ← locallyAddDecls decls <| traverse (checkProcess checkExpr) a.processes
    return {
      isFair := a.isFair
      name := a.name
      globalState := decls
      processes := ps
    }
end
