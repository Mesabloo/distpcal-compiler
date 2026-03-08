import Core.TypedSetTheory.Syntax
import CustomPrelude
import Common.Pretty
import Extra.String

namespace TypedSetTheory
  variable {Typ : Type} [Std.ToFormat Typ]

  partial def Expression.pretty (e : Expression Typ) (prec : Nat) : Std.Format := match_source e with
    | .var name τ, pos => formatPos pos ++ " " ++ name ++ " : " ++ Std.format τ
    | .str raw, pos => formatPos pos ++ " " ++ "\"" ++ raw.escape ++ "\""
    | .nat raw, pos => formatPos pos ++ " " ++ raw
    | .bool raw, pos => formatPos pos ++ " " ++ (toString raw).toUpper
    | .set elems τ, pos => formatPos pos ++ " " ++ .bracket (f!"[{τ}]".pretty ++ "{") (.joinSep (elems.map (pretty · 0)) ", ") "}"
    | .record fields, pos => formatPos pos ++ " " ++ .sbracket (.joinSep (fields.map λ ⟨name, τ, e⟩ ↦ name ++ " : " ++ Std.format τ ++ " ↦ " ++ e.pretty 0) ", ")
    | .prefix op e, pos => formatPos pos ++ " " ++ .«prefix» Expression.pretty op.prec (toString op) e prec
    | .infix e₁ op e₂, pos => formatPos pos ++ " " ++ .«infix» Expression.pretty op.prec (toString op) e₁ e₂ prec
    | .funcall fn args, pos => formatPos pos ++ " " ++ pretty fn 30 ++ .sbracket (.joinSep (args.map λ e ↦ pretty e 0) ", ")
    | .opcall fn args, pos => formatPos pos ++ " " ++ pretty fn 30 ++ .paren (.joinSep (args.map λ e ↦ pretty e 0) ", ")
    | .access e x, pos => formatPos pos ++ " " ++ pretty e 30 ++ "." ++ x
    | .seq es τ, pos => formatPos pos ++ " " ++ f!"Seq[{τ}](<<{Std.Format.joinSep (es.map (·.pretty 0)) ", "}>>)"
    | except fn upds, pos =>
      let prettyUpd (upds : List (List (Expression Typ) ⊕ String)) (e : Expression Typ) : Std.Format :=
        f!"!{Std.Format.joinSep (upds.map λ | .inr x => f!".{x}" | .inl es => .sbracket (.joinSep (es.map (pretty · 0)) ", ")) ", "} = {e.pretty 0}"
      formatPos pos ++ " " ++ f!"[{fn.pretty 0} EXCEPT {Std.Format.joinSep (upds.map ↿prettyUpd) ", "}]"
  where
    formatPos (pos : SourceSpan) : Std.Format := .bracket "(* " (Std.format pos) " *)"

  instance : Std.ToFormat (Expression Typ) := ⟨(Expression.pretty · 0)⟩
