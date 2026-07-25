module

public import Desugarer.Monad
public import Core.SurfaceTLAPlus.Syntax
public import Core.CoreTLAPlus.Syntax
public import Core.SurfacePlusCal.Syntax
public import Parser_.Annotations

public section

namespace SurfaceTLAPlus
  /-- The canonical (single-spelling) name a builtin prefix operator becomes as a
  `CoreTLAPlus.Expression.var`, reachable via `opCall`. -/
  def PrefixOperator.canonicalName : PrefixOperator → String
    -- Unary minus gets its own canonical spelling, `"-."`, distinct from infix `-`'s
    -- `InfixOperator.canonicalName` below, so the two arities of `-` get non-colliding `Γ`
    -- entries — the surface syntax stays plain `-x`.
    | .«-» => "-."
    | .«\neg » _ => "\\neg"
    | .«[]» => "[]"
    | .«<>» => "<>"
    | .DOMAIN => "DOMAIN"
    | .ENABLED => "ENABLED"
    | .SUBSET => "SUBSET"
    | .UNCHANGED => "UNCHANGED"
    | .UNION => "UNION"

  /-- The canonical name a builtin postfix operator becomes. -/
  def PostfixOperator.canonicalName : PostfixOperator → String
    | .«^+» => "^+"
    | .«^*» => "^*"
    | .«^#» => "^#"
    | .«'» => "'"

  /-- The canonical name a builtin infix operator becomes (collapsing every alternative spelling
  — e.g. `<=`/`=<`/`\leq` — to one). -/
  def InfixOperator.canonicalName : InfixOperator → String
    | .«!!» => "!!" | .«##» => "##" | .«$$» => "$$" | .«$» => "$" | .«%%» => "%" | .«%» => "%"
    | .«&&» => "&&" | .«&» => "&"
    | .«(+) » _ => "(+)" | .«(-) » _ => "(-)" | .«(.) » _ => "(.)" | .«(/) » _ => "(/)"
    | .«(\X) » _ => "(\\X)" | .«\X » _ => "\\X"
    | .«**» => "**" | .«*» => "*" | .«++» => "++" | .«+» => "+"
    | .«-+->» => "-+->" | .«--» => "--" | .«-|» => "-|" | .«-» => "-"
    | .«...» => "..." | .«..» => ".." | .«.» => "." | .«//» => "//"
    | .«/= » _ => "/=" | .«/\ » _ => "/\\" | .«/» => "/"
    | .«::=» => "::=" | .«:=» => ":=" | .«:>» => ":>" | .«<:» => "<:"
    | .«<=> » _ => "<=>" | .«=< » _ => "=<" | .«=>» => "=>" | .«=|» => "=|" | .«<» => "<" | .«=» => "="
    | .«>= » _ => ">=" | .«>» => ">"
    | .«??» => "??" | .«?» => "?" | .«@@» => "@@"
    | .«\/ » _ => "\\/" | .«^^» => "^^" | .«^» => "^"
    | .«|-» => "|-" | .«|=» => "|=" | .«||» => "||" | .«|» => "|" | .«~>» => "~>"
    | .«\approx» => "\\approx" | .«\sqsupseteq» => "\\sqsupseteq" | .«\asymp» => "\\asymp"
    | .«\gg» => "\\gg" | .«\star» => "\\star" | .«\bigcirc» => "\\bigcirc" | .«\in» => "\\in"
    | .«\preceq» => "\\preceq" | .«\prec» => "\\prec" | .«\subseteq» => "\\subseteq"
    | .«\subset» => "\\subset" | .«\bullet» => "\\bullet"
    | .«\cap » _ => "\\cap" | .«\propto» => "\\propto"
    | .«\succeq» => "\\succeq" | .«\succ» => "\\succ" | .«\cdot» => "\\cdot"
    | .«\simeq» => "\\simeq" | .«\sim» => "\\sim" | .«\ll» => "\\ll"
    | .«\supseteq» => "\\supseteq" | .«\supset» => "\\supset" | .«\cong» => "\\cong"
    | .«\sqcap» => "\\sqcap" | .«\cup » _ => "\\cup"
    | .«\o » _ => "\\o" | .«\sqcup» => "\\sqcup" | .«\div» => "\\div"
    | .«\sqsubseteq» => "\\sqsubseteq" | .«\sqsubset» => "\\sqsubset" | .«\uplus» => "\\uplus"
    | .«\doteq» => "\\doteq" | .«\wr» => "\\wr" | .«\sqsupset» => "\\sqsupset"
    | .«\notin» => "\\notin" | .«\» => "\\"

  /-- Cartesian product, used to collapse a multi-binder function literal/set-map into a single
  fresh tuple binder (see `flattenBound`/`collapseToSingleBinder` below). -/
  private def cartesianProduct : InfixOperator := .«\X » 0

  -- `[Inhabited α]`: needed wherever a synthesized binder (fresh tuple/product variables, or an
  -- unbounded binder with no per-variable annotation) needs some annotation value to use.
  variable {α} [Inhabited α] {m : Type → Type} [MonadDesugarerExpr α m] [Monad m]

  /-- Substitute every free occurrence of `CoreTLAPlus.Expression.var x` with `e`, stopping at any
  binder that rebinds `x`. Used to reconstruct tuple-pattern/multi-binder variables as
  projections off a single fresh binder (`flattenBound`, `collapseToSingleBinder`).

  Substitution rebuilds every node on the path it walks, so each rebuilt node is re-registered
  (`match_source`/`@@`) at the span the original carried. Skipping that would leave a whole
  subtree of the desugared body positionless, and `posOf` answers for an unregistered node with
  an unrelated node's span rather than failing (`Common/Position.lean`). -/
  partial def CoreTLAPlus.Expression.subst {α} (x : String) (e : CoreTLAPlus.Expression α)
      (target : CoreTLAPlus.Expression α) : CoreTLAPlus.Expression α := match_source target with
    | .var y, pos => if y == x then e else .var y @@ pos
    | .opCall f es, pos => .opCall (subst x e f) (subst x e <$> es) @@ pos
    | .forall y ann dom body, pos => .forall y ann (subst x e <$> dom) (if y == x then body else subst x e body) @@ pos
    | .exists y ann dom body, pos => .exists y ann (subst x e <$> dom) (if y == x then body else subst x e body) @@ pos
    | .fforall y ann body, pos => .fforall y ann (if y == x then body else subst x e body) @@ pos
    | .eexists y ann body, pos => .eexists y ann (if y == x then body else subst x e body) @@ pos
    | .choose y ann dom body, pos => .choose y ann (subst x e <$> dom) (if y == x then body else subst x e body) @@ pos
    | .set es, pos => .set (subst x e <$> es) @@ pos
    | .collect y ann dom pred, pos => .collect y ann (subst x e dom) (if y == x then pred else subst x e pred) @@ pos
    | .map' body y ann dom, pos => .map' (if y == x then body else subst x e body) y ann (subst x e dom) @@ pos
    | .fnCall f e', pos => .fnCall (subst x e f) (subst x e e') @@ pos
    | .fn y ann dom body, pos => .fn y ann (subst x e dom) (if y == x then body else subst x e body) @@ pos
    | .fnSet e₁ e₂, pos => .fnSet (subst x e e₁) (subst x e e₂) @@ pos
    | .record fs, pos => .record (fs.map λ (ann, name, v) ↦ (ann, name, subst x e v)) @@ pos
    | .recordSet fs, pos => .recordSet (fs.map λ (ann, name, v) ↦ (ann, name, subst x e v)) @@ pos
    | .except f upds, pos =>
      .except (subst x e f) (upds.map λ (idx, v) ↦ (idx.map (Sum.map id (subst x e)), subst x e v)) @@ pos
    | .recordAccess f name, pos => .recordAccess (subst x e f) name @@ pos
    | .tuple es, pos => .tuple (subst x e <$> es) @@ pos
    | .if e₁ e₂ e₃, pos => .if (subst x e e₁) (subst x e e₂) (subst x e e₃) @@ pos
    | .case bs other, pos => .case (bs.map (Bifunctor.bimap (subst x e) (subst x e))) (subst x e <$> other) @@ pos
    | .nat n, pos => .nat n @@ pos
    | .str s, pos => .str s @@ pos
    | .true, pos => .true @@ pos
    | .false, pos => .false @@ pos
    | .stutter e₁ e₂, pos => .stutter (subst x e e₁) (subst x e e₂) @@ pos

  /-- The `z[i]` (1-based, TLA⁺-style) tuple projection — a single index, so no `<<…>>`
  wrapping (`wrapIndices` below) is needed. Registered at `pos`, the span of the tuple-pattern
  binder this projection was synthesized to replace. -/
  private def tupleProj {α} (pos : SourceSpan) (z : String) (i : Nat) : CoreTLAPlus.Expression α :=
    .fnCall (.var z @@ pos) (.nat (toString (i + 1)) @@ pos) @@ pos

  /-- `f[e₁, …, eₙ]`'s/`![e₁, …, eₙ]`'s indices, collapsed to the single `CoreTLAPlus.Expression`
  `fnCall`/`except` take: a lone index (`n = 1`) stays exactly that, `f[e]`; more than one becomes
  the tuple `f[<<e₁, …, eₙ>>]`. `es` is always non-empty by construction of the parser. Reused by
  `Desugarer/PlusCal.lean` for `SurfacePlusCal.Ref`'s own indices. -/
  def wrapIndices {α} (pos : SourceSpan) : List (CoreTLAPlus.Expression α) → CoreTLAPlus.Expression α
    | [e] => e
    | es => .tuple es @@ pos

  /-- Flatten one already-desugared `QuantifierBound` into a list of single-variable `(name,
  annotation, domain)` bindings, plus how `body` needs rewriting to still make sense in terms of
  those flattened names:
  - `.var ann x dom` is already single-variable: one binding, no rewriting.
  - `.vars [(ann₁,x),(ann₂,y),…] dom` (`\A x, y ∈ S : …`) shares one domain across several names:
    expands to one binding per name, no rewriting.
  - `.varTuple [(ann₁,x),(ann₂,y),…] dom` (`\A ⟨x,y⟩ ∈ S : …`) is a tuple pattern: collapses to
    one fresh binding over `dom`, rewriting `body` to substitute each `x`/`y` with the
    corresponding projection out of the fresh variable. -/
  def flattenBound (pos : SourceSpan) (qb : QuantifierBound α (CoreTLAPlus.Expression α))
      (body : CoreTLAPlus.Expression α) :
      m (List (String × α × CoreTLAPlus.Expression α) × CoreTLAPlus.Expression α) :=
    match qb with
    | .var ann x dom => pure ([(x, ann, dom)], body)
    | .vars xs dom => pure (xs.map λ (ann, x) ↦ (x, ann, dom), body)
    | .varTuple xs dom => do
      let z ← freshName "tuple"
      let body := xs.zipIdx.foldr (init := body) λ ((_, x), i) body ↦
        CoreTLAPlus.Expression.subst x (tupleProj pos z i) body
      let ann := xs.head?.map Prod.fst |>.getD default
      pure ([(z, ann, dom)], body)

  /-- Collapse a list of already-flattened single-variable bindings into exactly one, as required
  by `CoreTLAPlus`'s single-binder function literals/set-maps. A single binding needs no change;
  multiple bindings `x ∈ A, y ∈ B, …` collapse to one fresh variable over the Cartesian product
  `A × B × …`, rewriting `body` to project each original name back out. Not the same
  transformation as `\A x, y : P`'s sequential nesting (`nestQuantifier` below): `[x ∈ A, y ∈ B ↦
  e]` denotes one function over pairs, not a function of functions. -/
  def collapseToSingleBinder (pos : SourceSpan) (bindings : List (String × α × CoreTLAPlus.Expression α))
      (body : CoreTLAPlus.Expression α) :
      m (String × α × CoreTLAPlus.Expression α × CoreTLAPlus.Expression α) :=
    match bindings with
    | [(x, ann, dom)] => pure (x, ann, dom, body)
    | (_, ann, dom₀) :: rest@(_ :: _) => do
      let z ← freshName "tuple"
      let domain := rest.foldl (init := dom₀) λ acc (_, _, dom) ↦
        .opCall (.var cartesianProduct.canonicalName @@ pos) [acc, dom] @@ pos
      let body := bindings.zipIdx.foldr (init := body) λ ((x, _, _), i) body ↦
        CoreTLAPlus.Expression.subst x (tupleProj pos z i) body
      pure (z, ann, domain, body)
    | [] => unreachable!

  /-- Sequentially nest a list of `(name, annotation, domain)` bindings into repeated
  single-variable quantification: `x ∈ A, y ∈ B` becomes `∫ x ∈ A : ∫ y ∈ B : body` (a true
  nesting, unlike `collapseToSingleBinder`'s product collapse). -/
  def nestQuantifier (pos : SourceSpan)
      (mk : String → α → Option (CoreTLAPlus.Expression α) → CoreTLAPlus.Expression α → CoreTLAPlus.Expression α)
      (bindings : List (String × α × CoreTLAPlus.Expression α)) (body : CoreTLAPlus.Expression α) : CoreTLAPlus.Expression α :=
    bindings.foldr (init := body) λ (x, ann, dom) body ↦ mk x ann (some dom) body @@ pos

  partial def Expression.desugar (e : Expression α) : m (CoreTLAPlus.Expression α) := match_source e with
    | .var x, pos => return .var x @@ pos
    | .opCall e es, pos => (.opCall · · @@ pos) <$> e.desugar <*> traverse Expression.desugar es
    | .prefixCall op e, pos => (λ e ↦ .opCall (.var op.canonicalName @@ pos) [e] @@ pos) <$> e.desugar
    | .infixCall e₁ .«.» (.var x), pos =>
      (.recordAccess · x @@ pos) <$> e₁.desugar
    | .infixCall _ .«.» _, pos => throw (.invalidRecordFieldAccess pos)
    | .infixCall e₁ op e₂, pos =>
      (λ e₁ e₂ ↦ .opCall (.var op.canonicalName @@ pos) [e₁, e₂] @@ pos) <$> e₁.desugar <*> e₂.desugar
    | .postfixCall e op, pos => (λ e ↦ .opCall (.var op.canonicalName @@ pos) [e] @@ pos) <$> e.desugar
    | .parens e, _ => e.desugar
    | .bforall qs e, pos => do
      let e ← e.desugar
      let (bindings, e) ← qs.foldrM (init := ([], e)) λ qb (bindings, e) ↦ do
        let (bs, e) ← flattenBound pos (← bitraverse pure Expression.desugar qb) e
        return (bs ++ bindings, e)
      return nestQuantifier pos .forall bindings e @@ pos
    | .bexists qs e, pos => do
      let e ← e.desugar
      let (bindings, e) ← qs.foldrM (init := ([], e)) λ qb (bindings, e) ↦ do
        let (bs, e) ← flattenBound pos (← bitraverse pure Expression.desugar qb) e
        return (bs ++ bindings, e)
      return nestQuantifier pos .exists bindings e @@ pos
    | .forall vs e, pos =>
      (λ e ↦ vs.foldr (init := e) λ v e ↦ .forall v default none e @@ pos) <$> e.desugar
    | .exists vs e, pos =>
      (λ e ↦ vs.foldr (init := e) λ v e ↦ .exists v default none e @@ pos) <$> e.desugar
    | .fforall vs e, pos =>
      (λ e ↦ vs.foldr (init := e) λ v e ↦ .fforall v default e @@ pos) <$> e.desugar
    | .eexists vs e, pos =>
      (λ e ↦ vs.foldr (init := e) λ v e ↦ .eexists v default e @@ pos) <$> e.desugar
    | .choose vs A e, pos => do
      let A ← traverse Expression.desugar A
      let e ← e.desugar
      match vs with
      | .var ann x => return .choose x ann A e @@ pos
      | .tuple xs => do
        let z ← freshName "tuple"
        let e := xs.zipIdx.foldr (init := e) λ ((_, x), i) e ↦ CoreTLAPlus.Expression.subst x (tupleProj pos z i) e
        -- The fresh variable stands for the whole tuple, so it takes the first component's
        -- annotation — the same choice `flattenBound` makes for `QuantifierBound.varTuple`.
        let ann := xs.head?.map Prod.fst |>.getD default
        return .choose z ann A e @@ pos
    | .set es, pos => (.set · @@ pos) <$> traverse Expression.desugar es
    | .collect vs A e, pos => do
      let A ← A.desugar
      let e ← e.desugar
      match vs with
      | .var ann x => return .collect x ann A e @@ pos
      | .tuple xs => do
        let z ← freshName "tuple"
        let e := xs.zipIdx.foldr (init := e) λ ((_, x), i) e ↦ CoreTLAPlus.Expression.subst x (tupleProj pos z i) e
        let ann := xs.head?.map Prod.fst |>.getD default
        return .collect z ann A e @@ pos
    | .map' e qs, pos => do
      let e ← e.desugar
      let (bindings, e) ← qs.foldrM (init := ([], e)) λ qb (bindings, e) ↦ do
        let (bs, e) ← flattenBound pos (← bitraverse pure Expression.desugar qb) e
        return (bs ++ bindings, e)
      let (x, ann, dom, e) ← collapseToSingleBinder pos bindings e
      return .map' e x ann dom @@ pos
    | .fnCall e es, pos => (.fnCall · · @@ pos) <$> e.desugar <*> (wrapIndices pos <$> traverse Expression.desugar es)
    | .fn qs e, pos => do
      let e ← e.desugar
      let (bindings, e) ← qs.foldrM (init := ([], e)) λ qb (bindings, e) ↦ do
        let (bs, e) ← flattenBound pos (← bitraverse pure Expression.desugar qb) e
        return (bs ++ bindings, e)
      let (x, ann, dom, e) ← collapseToSingleBinder pos bindings e
      return .fn x ann dom e @@ pos
    | .fnSet e₁ e₂, pos => (.fnSet · · @@ pos) <$> e₁.desugar <*> e₂.desugar
    | .record fs, pos =>
      (.record · @@ pos) <$> traverse (bitraverse pure (bitraverse pure Expression.desugar)) fs
    | .recordSet fs, pos =>
      (.recordSet · @@ pos) <$> traverse (bitraverse pure (bitraverse pure Expression.desugar)) fs
    | .except e upds, pos => do
      let e ← e.desugar
      let upds ← upds.traverse λ ⟨idx, e'⟩ ↦ do
        let idx ← traverse (bitraverse pure (traverse Expression.desugar)) idx
        let e := idx.foldl (init := e) λ | e, .inl x => .recordAccess e x
                                         | e, .inr es => .fnCall e (wrapIndices pos es)
        let e' ← withReader (Function.const _ (.some e)) e'.desugar
        return ⟨idx.map (Sum.map id (wrapIndices pos)), e'⟩
      return .except e upds @@ pos
    | .recordAccess e x, pos => (.recordAccess · x @@ pos) <$> e.desugar
    | .tuple es, pos => (.tuple · @@ pos) <$> traverse Expression.desugar es
    | .if e₁ e₂ e₃, pos =>
      (.if · · · @@ pos) <$> e₁.desugar <*> e₂.desugar <*> e₃.desugar
    | .case bs other, pos =>
      (.case · · @@ pos)
        <$> traverse (bitraverse Expression.desugar Expression.desugar) bs
        <*> traverse Expression.desugar other
    | .conj es, pos => match es with
      | [] => return .true @@ pos
      | e :: es => do
        es.foldlM (init := ← e.desugar) λ e e' ↦ (λ e' ↦ .opCall (.var "/\\" @@ pos) [e, e'] @@ pos) <$> e'.desugar
    | .disj es, pos => match es with
      | [] => return .false @@ pos
      | e :: es => do
        es.foldlM (init := ← e.desugar) λ e e' ↦ (λ e' ↦ .opCall (.var "\\/" @@ pos) [e, e'] @@ pos) <$> e'.desugar
    | .nat n, pos => return .nat n @@ pos
    | .str s, pos => return .str s @@ pos
    | .at, pos => do match ← read with
      | .none => throw <| .misplacedAt pos
      | .some e => return e
    | .true, pos => return .true @@ pos
    | .false, pos => return .false @@ pos
    | .stutter e₁ e₂, pos => (.stutter · · @@ pos) <$> e₁.desugar <*> e₂.desugar

  def Declaration.desugar : Declaration α → m (CoreTLAPlus.Declaration α)
    | .constants vs => pure <| .constants vs
    | .variables vs => pure <| .variables vs
    | .assume e => .assume <$> e.desugar
    | .operator ann x ps e => .operator ann x ps <$> e.desugar
    | .function ann x ps e =>
      .function ann x <$> traverse (bitraverse pure Expression.desugar) ps <*> e.desugar

  def Module.desugar (mod : Module (SurfacePlusCal.Algorithm α (Expression α)) α) :
      m (CoreTLAPlus.Module (SurfacePlusCal.Algorithm α (CoreTLAPlus.Expression α)) α) :=
    (CoreTLAPlus.Module.mk mod.name mod.extends · · · @@ posOf mod)
      <$> traverse Declaration.desugar mod.declarations₁
      <*> traverse (bitraverse pure Expression.desugar) mod.pcalAlgorithm
      <*> traverse Declaration.desugar mod.declarations₂
end SurfaceTLAPlus

/-- Run expression desugaring against the concrete monad it needs: `@`'s Reader context,
fresh-name generation, and `MonadDiagnostic`'s error reporting/warning accumulation (instantiated
at `DiagT`, so a warning survives a later fatal error). No expression-level rule actually emits a
`DesugarWarning` yet, but the concrete stack stays uniform with `Desugarer/PlusCal.lean`'s
statement-level `runDesugarer`. The base monad `n` stays abstract, constrained only to supply the
fresh-name counter (`MonadStateOf Nat`, which `Common/Fresh.lean`'s `MonadFresh` instance reads):
the counter belongs to one compile, so the driver owns it (`Driver/Modules.lean`'s `DriverState`)
rather than this pass pinning a base monad that can reach a process-wide one. -/
def SurfaceTLAPlus.Module.runDesugarer {α} [Inhabited α] {n : Type → Type} [Monad n] [MonadFresh n]
    (mod : SurfaceTLAPlus.Module (SurfacePlusCal.Algorithm α (SurfaceTLAPlus.Expression α)) α) :
    DiagT DesugarWarning DesugarError n (CoreTLAPlus.Module (SurfacePlusCal.Algorithm α (CoreTLAPlus.Expression α)) α) :=
  let desugar : ReaderT (Option (CoreTLAPlus.Expression α)) (DiagT DesugarWarning DesugarError n) _ := mod.desugar
  desugar.run none

/-- Validate an annotation slot known to be `@type`-only: must contain only `@type`, and at most
one, then is replaced by the `Typ` it names. Shared between the TLA⁺ half below
(`stripTLAPlusAnnotations`) and `Desugarer/PlusCal.lean`'s equivalent check. -/
def extractType {m : Type → Type} [Monad m] [MonadDiagnostic DesugarWarning DesugarError m]
    (anns : List Annotation) : m (Option SurfaceTLAPlus.Typ) := do
  let mut seenType : Option SurfaceTLAPlus.Typ := none
  for ann in anns do
    match ann with
    | .«@type» pos τ =>
      match seenType with
      -- Two identical `@type`s genuinely disagree about nothing — accepted, not an error
      -- (only a real conflict, a *different* `τ'`, is ambiguous enough to reject).
      | some τ' => unless τ == τ' do throw (.duplicateAnnotation pos "@type")
      | none => seenType := some τ
    | _ => throw (.wrongAnnotationKindAtSite ann.posOf ann.name "@type")
  return seenType

/-- Validate every `List Annotation` slot reachable from a module's own declarations/expressions
— excluding the embedded PlusCal algorithm, which `Desugarer/PlusCal.lean`'s
`SurfacePlusCal.Algorithm.desugar` covers separately — must contain only `@type`, and at most
one (`extractType` above), and is replaced by the `Option Typ` it names. Runs after
`Module.desugar`/`runDesugarer`, since this check is only meaningful once `α` is concretely
`List Annotation`.

`DiagT … Id` rather than a bare `Except`, so every diagnostics-producing entry point in the
compiler reports through the same `MonadDiagnostic` shape — the caller absorbs it with
`DiagT.lift`, exactly as it already does for `parseModule` and `runDesugarer`. This check emits
no warnings today; the `List DesugarWarning` it pairs against its result is simply always `[]`. -/
def CoreTLAPlus.Module.stripTLAPlusAnnotations {γ} (mod : CoreTLAPlus.Module γ (List Annotation)) :
    DiagT DesugarWarning DesugarError Id (CoreTLAPlus.Module γ (Option SurfaceTLAPlus.Typ)) :=
  bitraverse pure extractType mod

end
