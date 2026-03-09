import Desugarer.Monad
import Core.SurfaceTLAPlus.Syntax
import Core.CoreTLAPlus.Syntax
import Core.SurfacePlusCal.Syntax

namespace SurfaceTLAPlus
  variable {α} {m : Type → Type} [MonadDesugarerExpr α m] [Monad m]

  def PrefixOperator.toCore (op : PrefixOperator) : CoreTLAPlus.PrefixOperator := match_source op with
    | .«-», pos => .«-» @@ pos
    | .«\neg » _, pos => .«\neg» @@ pos
    | .«[]», pos => .«[]» @@ pos
    | .«<>», pos => .«<>» @@ pos
    | .«DOMAIN», pos => .«DOMAIN» @@ pos
    | .«ENABLED», pos => .«ENABLED» @@ pos
    | .«SUBSET», pos => .«SUBSET» @@ pos
    | .«UNCHANGED», pos => .«UNCHANGED» @@ pos
    | .«UNION», pos => .«UNION» @@ pos

  def PostfixOperator.toCore (op : PostfixOperator) : CoreTLAPlus.PostfixOperator := match_source op with
    | .«^+», pos => .«^+» @@ pos
    | .«^*», pos => .«^*» @@ pos
    | .«^#», pos => .«^#» @@ pos
    | .«'», pos => .«'» @@ pos

  def InfixOperator.toCore (op : InfixOperator) : CoreTLAPlus.InfixOperator := match_source op with
    | .«!!», pos => .«!!» @@ pos
    | .«##», pos => .«##» @@ pos
    | .«$$», pos => .«$$» @@ pos
    | .«$», pos => .«$» @@ pos
    | .«%%», pos => .«%» @@ pos
    | .«%», pos => .«%» @@ pos
    | .«&&», pos => .«&&» @@ pos
    | .«&», pos => .«&» @@ pos
    | .«(+) » _, pos => .«(+)» @@ pos
    | .«(-) » _, pos => .«(-)» @@ pos
    | .«(.) » _, pos => .«(.)» @@ pos
    | .«(/) » _, pos => .«(/)» @@ pos
    | .«(\X) » _, pos => .«(\X)» @@ pos
    | .«\X » _, pos => .«\X» @@ pos
    | .«**», pos => .«**» @@ pos
    | .«*», pos => .«*» @@ pos
    | .«++», pos => .«++» @@ pos
    | .«+», pos => .«+» @@ pos
    | .«-+->», pos => .«-+->» @@ pos
    | .«--», pos => .«--» @@ pos
    | .«-|», pos => .«-|» @@ pos
    | .«-», pos => .«-» @@ pos
    | .«...», pos => .«...» @@ pos
    | .«..», pos => .«..» @@ pos
    | .«.», pos => .«.» @@ pos
    | .«//», pos => .«//» @@ pos
    | .«/= » _, pos => .«/=» @@ pos
    | .«/\ » _, pos => .«/\» @@ pos
    | .«/», pos => .«/» @@ pos
    | .«::=», pos => .«::=» @@ pos
    | .«:=», pos => .«:=» @@ pos
    | .«:>», pos => .«:>» @@ pos
    | .«<:», pos => .«<:» @@ pos
    | .«<=> » _, pos => .«<=>» @@ pos
    | .«=< » _, pos => .«=<» @@ pos
    | .«=>», pos => .«=>» @@ pos
    | .«=|», pos => .«=|» @@ pos
    | .«<», pos => .«<» @@ pos
    | .«=», pos => .«=» @@ pos
    | .«>= » _, pos => .«>=» @@ pos
    | .«>», pos => .«>» @@ pos
    | .«??», pos => .«??» @@ pos
    | .«?», pos => .«?» @@ pos
    | .«@@», pos => .«@@» @@ pos
    | .«\/ » _, pos => .«\/» @@ pos
    | .«^^», pos => .«^^» @@ pos
    | .«^», pos => .«^» @@ pos
    | .«|-», pos => .«|-» @@ pos
    | .«|=», pos => .«|=» @@ pos
    | .«||», pos => .«||» @@ pos
    | .«|», pos => .«|» @@ pos
    | .«~>», pos => .«~>» @@ pos
    | .«\approx», pos => .«\approx» @@ pos
    | .«\sqsupseteq», pos => .«\sqsupseteq» @@ pos
    | .«\asymp», pos => .«\asymp» @@ pos
    | .«\gg», pos => .«\gg» @@ pos
    | .«\star», pos => .«\star» @@ pos
    | .«\bigcirc», pos => .«\bigcirc» @@ pos
    | .«\in», pos => .«\in» @@ pos
    | .«\preceq», pos => .«\preceq» @@ pos
    | .«\prec», pos => .«\prec» @@ pos
    | .«\subseteq», pos => .«\subseteq» @@ pos
    | .«\subset», pos => .«\subset» @@ pos
    | .«\bullet», pos => .«\bullet» @@ pos
    | .«\cap » _, pos => .«\cap» @@ pos
    | .«\propto», pos => .«\propto» @@ pos
    | .«\succeq», pos => .«\succeq» @@ pos
    | .«\succ», pos => .«\succ» @@ pos
    | .«\cdot», pos => .«\cdot» @@ pos
    | .«\simeq», pos => .«\simeq» @@ pos
    | .«\sim», pos => .«\sim» @@ pos
    | .«\ll», pos => .«\ll» @@ pos
    | .«\supseteq», pos => .«\supseteq» @@ pos
    | .«\supset», pos => .«\supset» @@ pos
    | .«\cong», pos => .«\cong» @@ pos
    | .«\sqcap», pos => .«\sqcap» @@ pos
    | .«\cup » _, pos => .«\cup» @@ pos
    | .«\o » _, pos => .«\o» @@ pos
    | .«\sqcup», pos => .«\sqcup» @@ pos
    | .«\div», pos => .«\div» @@ pos
    | .«\sqsubseteq», pos => .«\sqsubseteq» @@ pos
    | .«\sqsubset», pos => .«\sqsubset» @@ pos
    | .«\uplus», pos => .«\uplus» @@ pos
    | .«\doteq», pos => .«\doteq» @@ pos
    | .«\wr», pos => .«\wr» @@ pos
    | .«\sqsupset», pos => .«\sqsupset» @@ pos
    | .«\notin», pos => .«\notin» @@ pos
    | .«\», pos => .«\» @@ pos

  partial def Expression.desugar (e : Expression α) : m (CoreTLAPlus.Expression α) := match_source e with
    | .var x, pos => return .var x @@ pos
    | .opCall e es, pos => do
      let e ← e.desugar
      let es ← traverse Expression.desugar es

      match e with
      | .var "Seq" => match es with
        | [.tuple es] => return .seq es @@ pos
        | _ => throw <| .seqExpectsATupleArgument pos
      | _ => return .opCall e es @@ pos
    | .prefixCall op e, pos => (.prefixCall op.toCore · @@ pos) <$> e.desugar
    | .infixCall e₁ op e₂, pos =>
      (.infixCall · op.toCore · @@ pos) <$> e₁.desugar <*> e₂.desugar
    | .postfixCall e op, pos => (.postfixCall · op.toCore @@ pos) <$> e.desugar
    | .parens e, _ => e.desugar
    | .bforall qs e, pos =>
      (.bforall · · @@ pos) <$> traverse (bitraverse pure Expression.desugar) qs <*> e.desugar
    | .bexists qs e, pos =>
      (.bexists · · @@ pos) <$> traverse (bitraverse pure Expression.desugar) qs <*> e.desugar
    | .forall vs e, pos => (.forall vs · @@ pos) <$> e.desugar
    | .exists vs e, pos => (.exists vs · @@ pos) <$> e.desugar
    | .fforall vs e, pos => (.fforall vs · @@ pos) <$> e.desugar
    | .eexists vs e, pos => (.eexists vs · @@ pos) <$> e.desugar
    | .choose vs A e, pos =>
      (.choose vs · · @@ pos) <$> traverse Expression.desugar A <*> e.desugar
    | .set es, pos => (.set · @@ pos) <$> traverse Expression.desugar es
    | .collect vs A e, pos => (.collect vs · · @@ pos) <$> A.desugar <*> e.desugar
    | .map' e qs, pos =>
      (.map' · · @@ pos) <$> e.desugar <*> traverse (bitraverse pure Expression.desugar) qs
    | .fnCall e es, pos => (.fnCall · · @@ pos) <$> e.desugar <*> traverse Expression.desugar es
    | .fn qs e, pos =>
      (.fn · · @@ pos) <$> traverse (bitraverse pure Expression.desugar) qs <*> e.desugar
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
                                         | e, .inr es => .fnCall e es
        let e' ← withReader (Function.const _ (.some e)) e'.desugar
        return ⟨idx, e'⟩
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
        es.foldlM (init := ← e.desugar) λ e e' ↦ .infixCall e .«/\» <$> e'.desugar
    | .disj es, pos => match es with
      | [] => return .false @@ pos
      | e :: es => do
        es.foldlM (init := ← e.desugar) λ e e' ↦ .infixCall e .«\/» <$> e'.desugar
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

abbrev SurfaceTLAPlus.Module.runDesugarer {α} (mod : Module (SurfacePlusCal.Algorithm α (Expression α)) α) :
    Except DesugarError (CoreTLAPlus.Module (SurfacePlusCal.Algorithm α (CoreTLAPlus.Expression α)) α) :=
  ReaderT.run mod.desugar (none : Option (CoreTLAPlus.Expression α))
