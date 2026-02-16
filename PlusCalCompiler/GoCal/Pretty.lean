import PlusCalCompiler.GoCal.Syntax
import PlusCalCompiler.CoreTLAPlus.Syntax
import Extra.Format
import Extra.List

namespace GoCal
  open CoreTLAPlus (Typ Expression)

  partial scoped instance instToFormatTyp : Std.ToFormat Typ where
    format :=
      let rec go : Typ → Std.Format
        | .bool => "bool"
        | .int => "int"
        | .str => "string"
        | .address => "Address"
        | .function τ₁ τ₂ => f!"map[{go τ₁}]{go τ₂}"
        | .set τ => f!"[]{go τ}"
        | .seq τ => f!"[]{go τ}"
        | .tuple _ => sorry
        | .operator τs τ => "func (" ++ .joinSuffix (τs.map λ τ ↦ f!"_ {go τ}") ", " ++ f!") {go τ}"
        | .var v => v
        | .const v => v
        | .record fs => "struct {" ++ .joinSuffix (fs.map λ ⟨v, τ⟩ ↦ v ++ " " ++ go τ) "; " ++ "}"
        | .channel τ => f!"chan {go τ}"
      go

  partial scoped instance instToFormatExpression : Std.ToFormat (Expression Typ) where
    format :=
      let formatPos (pos : SourceSpan) : Std.Format := if pos = default then .nil else f!"/* {pos} */ "
      let rec go : Expression Typ → Nat → Std.Format
        | .var pos name => λ _ ↦ formatPos pos ++ f!"{name}"
        | .str pos raw => λ _ ↦ formatPos pos ++ f!"`{raw}`"
        | .nat pos raw => λ _ ↦ formatPos pos ++ f!"{raw}"
        | .bool pos raw => λ _ ↦ formatPos pos ++ f!"{raw}"
        | .set pos elems => λ _ ↦ formatPos pos ++ "SetLiteral(" ++ Std.Format.joinSuffix (elems.map (go · 0)) ", " ++ ")"
        | .record pos fields => λ _ ↦
          let ⟨τs, es⟩ := fields.unzipWith (λ ⟨v, τ, _⟩ ↦ (v, τ)) (λ ⟨v, _, e⟩ ↦ (v, e))
          formatPos pos ++ "struct"
            ++ .bracket "{" (.joinSuffix (τs.map λ ⟨v, τ⟩ ↦ v ++ " " ++ Std.format τ) "; ") "}"
            ++ .bracket "{" (.joinSuffix (es.map λ ⟨v, e⟩ ↦ v ++ ": " ++ go e 0) ", ") "}"
        | .prefix pos op e => (formatPos pos ++ ·) ∘ match op with
          | .«¬» => .«prefix» go 6 "!" e
          | .«-» => .«prefix» go 6 "-" e
        | .infix pos e₁ op e₂ => (formatPos pos ++ ·) ∘ match op with
          | .«=» => .«infixl» go 3 "==" e₁ e₂
          | .«>» => .«infixl» go 3 ">" e₁ e₂
          | .«∪» => λ _ ↦ f!"SetUnion({go e₁ 0}, {go e₂ 0}, )"
          | .«∈» => λ _ ↦ f!"SetIn({go e₁ 0}, {go e₂ 0}, )"
          | .«-» => .«infixl» go 4 "-" e₁ e₂
          | .«+» => .«infixl» go 4 "+" e₁ e₂
        | .funcall pos fn args => λ _ ↦ formatPos pos ++ go fn 30 ++ .join (args.map λ e ↦ .sbracket (go e 0))
        | .opcall pos fn args => λ _ ↦ formatPos pos ++ go fn 30 ++ .paren (.joinSuffix (args.map (go · 0)) ", ")
        | .access pos e x => λ _ ↦ formatPos pos ++ go e 30 ++ "." ++ x
        | .seq pos es => λ _ ↦ formatPos pos ++ f!"Seq({Std.Format.joinSuffix (es.map (go · 0)) ", "})"
        | .except pos fn upds => λ _ ↦ formatPos pos ++ f!"TODO upd"
      (go · 0)

  universe u
  variable {Expr : Type u} [Std.ToFormat Expr]

  private instance : Std.ToFormat (LHS Expr) where
    format lhs := f!"{lhs.name}" ++ .join (lhs.args.map λ e ↦ .sbracket <| Std.format e)

  partial def Statement.pretty : Statement Typ Expr GoCal.Typ.initArgs → Std.Format
    | .panic pos msg => formatPos pos ++ f!" panic({msg})"
    -- depends on `args`, hence on `init`
    | .make pos name τ args => formatPos pos ++ match τ, args with
      | .int, .some e | .bool, .some e | .str, .some e => f!"var {name} {τ} = {e}"
      | .int, .none | .bool, .none | .str, .none => f!"var {name} {τ}"
      | .channel _, .inl .none => f!"{name} := make({τ})"
      | .channel _, .inl (.some n) => f!"{name} := make({τ}, {n})"
      | .channel _, .inr e => f!"{name} := {e}"
      | .seq _, es | .set _, es => f!"{name} := {τ}" ++ .bracket "{" (.joinSuffix es ", ") "}"
      | .record _, bs => f!"{name} := {τ}" ++ .bracket "{" (.joinSuffix (bs.map λ ⟨v, e⟩ ↦ f!"{v}: {e}") ", ") "}"
      | .var _, r | .const _, r | .operator _ _, r => nomatch r
      -- tuples and functions
      | τ, _ => todo! (default := Std.Format.text s!"{name} := make(...)") s!"formatter for `make` with {τ}"
    | .close pos chan => formatPos pos ++ f!"close({chan})"
    | .assign pos ref e => formatPos pos ++ f!"{ref} = {e}"
    | .return pos e => formatPos pos ++ "return " ++ .joinSep e ", "
    | .print pos e => formatPos pos ++ f!"println({e})"
    | .go pos B => formatPos pos ++ "go func()" ++ .bracket "{" (formatBlock B) "}()"
    | .while pos cond B => formatPos pos ++ f!"for {cond} " ++ .bracket "{" (formatBlock B) "}"
    | .if pos cond B₁ B₂ => formatPos pos ++ f!"if {cond} " ++ .bracket "{" (formatBlock B₁) "}" ++ " else " ++ .bracket "{" (formatBlock B₂) "}"
    | .receive pos «from» «to» => formatPos pos ++ f!"{«to»} = <-{«from»}"
    | .send pos «to» e => formatPos pos ++ f!"{«to»} <- {e}"
    | .select pos clauses =>
      let formatClause : SelectClause Expr (Statement Typ Expr GoCal.Typ.initArgs) → Std.Format
        | .receive «to» _ «from» B =>
          let tos := Std.Format.joinSep «to» ", " ++ if !«to».isEmpty then " = " else ""
          f!"case {tos}<-{«from»}: " ++ formatBlock B
        | .send «to» e B => f!"case {«to»} <- {e}: " ++ formatBlock B
        | .default B => f!"default: " ++ formatBlock B
      formatPos pos ++ "select " ++ .bracket "{" (.group <| .indent 0 <| .joinSep (clauses.map formatClause) .line) "}"
    where
      formatPos (pos : SourceSpan) : Std.Format := if pos = default then .nil else f!"/* {pos} */ "

      formatBlock (B : List (Statement Typ Expr GoCal.Typ.initArgs)) : Std.Format :=
        .group <| .indent 4 <| .joinSuffix (B.map Statement.pretty) (";" ++ .line)

  instance : Std.ToFormat (Statement Typ Expr GoCal.Typ.initArgs) := ⟨Statement.pretty⟩

  def Function.pretty (F : Function Typ Expr GoCal.Typ.initArgs) : Std.Format :=
    let params := .joinSep (F.params.map λ ⟨v, τ⟩ ↦ v ++ " " ++ Std.format τ) ", "
    let ret := .joinSep F.returnType ", "
    let body := .joinSuffix F.body (";" ++ .line)

    "func " ++ F.name ++ .paren params ++ " " ++ .paren ret ++ " " ++ .bracket "{" (.group <| .indent 4 body) "}"

  instance : Std.ToFormat (Function Typ Expr GoCal.Typ.initArgs) := ⟨Function.pretty⟩
