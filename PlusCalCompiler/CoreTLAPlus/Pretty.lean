import PlusCalCompiler.CoreTLAPlus.Syntax
import CustomPrelude
import Extra.Format
import Extra.String

namespace CoreTLAPlus
  universe u
  variable {Typ : Type u} [Std.ToFormat Typ]

  partial def Expression.pretty : Expression Typ → Nat → Std.Format
    | .var pos name => λ _ ↦ formatPos pos ++ " " ++ name
    | .str pos raw => λ _ ↦ formatPos pos ++ " " ++ "\"" ++ raw.escape ++ "\""
    | .nat pos raw => λ _ ↦ formatPos pos ++ " " ++ raw
    | .bool pos raw => λ _ ↦ formatPos pos ++ " " ++ (toString raw).toUpper
    | .set pos elems => λ _ ↦ formatPos pos ++ " " ++ .bracket "{" (.joinSep (elems.map (pretty · 0)) ", ") "}"
    | .record pos fields => λ _ ↦ formatPos pos ++ " " ++ .sbracket (.joinSep (fields.map λ ⟨name, τ, e⟩ ↦ name ++ " : " ++ Std.format τ ++ " ↦ " ++ e.pretty 0) ", ")
    | .prefix pos op e => (formatPos pos ++ " " ++ ·) ∘ .«prefix» Expression.pretty op.prec (toString op) e
    | .infix pos e₁ op e₂ => (formatPos pos ++ " " ++ ·) ∘ .«infix» Expression.pretty op.prec (toString op) e₁ e₂
    | .funcall pos fn args => λ _ ↦ formatPos pos ++ " " ++ pretty fn 30 ++ .sbracket (.joinSep (args.map λ e ↦ pretty e 0) ", ")
    | .opcall pos fn args => λ _ ↦ formatPos pos ++ " " ++ pretty fn 30 ++ .paren (.joinSep (args.map λ e ↦ pretty e 0) ", ")
    | .access pos e x => λ _ ↦ formatPos pos ++ " " ++ pretty e 30 ++ "." ++ x
    | .seq pos es => λ _ ↦ formatPos pos ++ " " ++ f!"Seq(<<{Std.Format.joinSep (es.map (·.pretty 0)) ", "}>>)"
    | except pos fn upds =>
      let prettyUpd (upds : List (List (Expression Typ) ⊕ String)) (e : Expression Typ) : Std.Format :=
        f!"!{Std.Format.joinSep (upds.map λ | .inr x => f!".{x}" | .inl es => .sbracket (.joinSep (es.map (pretty · 0)) ", ")) ", "} = {e.pretty 0}"
      λ _ ↦ formatPos pos ++ " " ++ f!"[{fn.pretty 0} EXCEPT {Std.Format.joinSep (upds.map ↿prettyUpd) ", "}]"
  where
    formatPos (pos : SourceSpan) : Std.Format := .bracket "(* " (Std.format pos) " *)"
  instance : Std.ToFormat (Expression Typ) := ⟨(Expression.pretty · 0)⟩
