import PlusCalCompiler.GoCal.Syntax
import PlusCalCompiler.CoreTLAPlus.Syntax
import Extra.Format
import Extra.List

namespace GoCal
  open CoreTLAPlus (Typ Expression)

  private def keywords : Std.HashSet String := {
    -- keywords
    "break", "case", "chan", "const", "continue", "default",
    "defer", "else", "fallthrough", "for", "func", "go", "goto",
    "if", "import", "interface", "map", "package", "range", "return",
    "select", "struct", "switch", "type", "var",
    -- types
    "any", "bool", "byte", "comparable", "complex64", "complex128", "error",
    "float32", "float64", "int", "int8", "int16", "int32", "int64", "rune",
    "string", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr",
    -- constants
    "true", "false", "iota",
    -- zero value
    "nil",
    -- functions
    "append", "cap", "clear", "close", "complex", "copy", "delete", "imag",
    "len", "make", "max", "min", "new", "panic", "print", "println", "real",
    "recover"
  }

  @[inline]
  private def sanitize (name : String) :=
    if name ∈ keywords then f!"{name}__" else f!"{name}"

  partial scoped instance instToFormatTyp : Std.ToFormat Typ where
    format :=
      let rec go : Typ → Std.Format
        | .bool => "bool"
        | .int => "int"
        | .str => "string"
        | .address => "Address[interface {}]"
        | .function τ₁ τ₂ => f!"Func[{go τ₁}, {go τ₂}]"
        | .set τ => f!"Set[{go τ}]"
        | .seq τ => f!"Seq[{go τ}]"
        | .tuple _ => sorry
        | .operator τs τ => "func (" ++ .joinSuffix (τs.map λ τ ↦ f!"_ {go τ}") ", " ++ f!") {go τ}"
        | .var v => v
        | .const v => v
        | .record fs => "struct {" ++ .joinSuffix (fs.map λ ⟨v, τ⟩ ↦ sanitize v ++ " " ++ go τ) "; " ++ "}"
        | .channel τ => f!"chan {go τ}"
      go

  partial scoped instance instToFormatExpression : Std.ToFormat (Expression Typ) where
    format :=
      let formatPos (pos : SourceSpan) : Std.Format := if pos = default then .nil else f!"/* {pos} */ "
      let rec go (e : Expression Typ) (prec : Nat) : Std.Format := match_source e with
        | .var name, pos => formatPos pos ++ sanitize name
        | .str raw, pos => formatPos pos ++ f!"`{raw}`"
        | .nat raw, pos => formatPos pos ++ f!"{raw}"
        | .bool raw, pos => formatPos pos ++ f!"{raw}"
        | .set elems, pos => formatPos pos ++ "SetLiteral(" ++ Std.Format.joinSuffix (elems.map (go · 0)) ", " ++ ")"
        | .record fields, pos =>
          let ⟨τs, es⟩ := fields.unzipWith (λ ⟨v, τ, _⟩ ↦ (v, τ)) (λ ⟨v, _, e⟩ ↦ (v, e))
          formatPos pos ++ "struct"
            ++ .bracket "{" (.joinSuffix (τs.map λ ⟨v, τ⟩ ↦ sanitize v ++ " " ++ Std.format τ) "; ") "}"
            ++ .bracket "{" (.joinSuffix (es.map λ ⟨v, e⟩ ↦ sanitize v ++ ": " ++ go e 0) ", ") "}"
        | .prefix op e, pos => formatPos pos ++ match op with
          | .«¬» => .«prefix» go 6 "!" e prec
          | .«-» => .«prefix» go 6 "-" e prec
        | .infix e₁ op e₂, pos => formatPos pos ++ match op with
          | .«=» => .«infixl» go 3 "==" e₁ e₂ prec
          | .«>» => .«infixl» go 3 ">" e₁ e₂ prec
          | .«∪» => f!"SetUnion({go e₁ 0}, {go e₂ 0}, )"
          | .«∈» => f!"SetIn({go e₁ 0}, {go e₂ 0}, )"
          | .«-» => .«infixl» go 4 "-" e₁ e₂ prec
          | .«+» => .«infixl» go 4 "+" e₁ e₂ prec
        | .funcall fn args, pos => formatPos pos ++ go fn 30 ++ .join (args.map λ e ↦ .sbracket (go e 0))
        | .opcall fn args, pos => formatPos pos ++ go fn 30 ++ .paren (.joinSuffix (args.map (go · 0)) ", ")
        | .access e x, pos => formatPos pos ++ go e 30 ++ "." ++ sanitize x
        | .seq es, pos => formatPos pos ++ f!"SeqLiteral({Std.Format.joinSuffix (es.map (go · 0)) ", "})"
        | .except fn upds, pos => formatPos pos ++ f!"TODO upd"
      (go · 0)

  universe u
  variable {Expr : Type} [Std.ToFormat Expr]

  private instance : Std.ToFormat (LHS Expr) where
    format lhs := f!"{lhs.name}" ++ .join (lhs.args.map λ e ↦ .sbracket <| Std.format e)

  partial def Statement.pretty (S : Statement Typ Expr GoCal.Typ.initArgs) : Std.Format := match_source S with
    | .panic msg, pos => formatPos pos ++ f!" panic({msg})"
    -- depends on `args`, hence on `init`
    | .make name τ args, pos => formatPos pos ++ match τ, args with
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
    | .close chan, pos => formatPos pos ++ f!"close({chan})"
    | .assign ref e, pos => formatPos pos ++ f!"{ref} = {e}"
    | .return e, pos => formatPos pos ++ "return " ++ .joinSep e ", "
    | .print e, pos => formatPos pos ++ f!"println({e})"
    | .go B, pos => formatPos pos ++ "go func()" ++ .bracket "{" (formatBlock B) "}()"
    | .while cond B, pos => formatPos pos ++ f!"for {cond} " ++ .bracket "{" (formatBlock B) "}"
    | .if cond B₁ B₂, pos => formatPos pos ++ f!"if {cond} " ++ .bracket "{" (formatBlock B₁) "}" ++ " else " ++ .bracket "{" (formatBlock B₂) "}"
    | .receive «from» «to», pos => formatPos pos ++ f!"{«to»} = <-{«from»}"
    | .send «to» e, pos => formatPos pos ++ f!"{«to»} <- {e}"
    | .select clauses, pos =>
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
