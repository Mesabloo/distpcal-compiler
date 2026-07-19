module

public import Core.Go.Syntax
public import Common.Pretty

public section


/-!
  Pretty-printing for `Core/Go/Syntax.lean`. Unlike every other `Pretty.lean` in this repo, this
  one is **not** a debug dump — it *is* `Network2Go`'s code generator: the `.go` file the compiler
  ships is whatever this module prints. (`Guarded2Network` has no pretty-printer at all and dumps
  via `reprStr`; that path stays for `-d dump-network`, and `-d dump-go` will reuse this one.)

  - `keywords`/`sanitize` come from prior art
    (`~/Documents/distpcal-compiler/Core/Go/Pretty.lean`), **split in two**: that table mixed Go's
    reserved words with its predeclared identifiers, so it escaped the generated code's own
    references to `int`/`any`/`comparable`/`len` into `int__`/`comparable__`. Only `keywords` is
    escaped here; `predeclared` is exported for `Network2Go` to rename *user-chosen* names against,
    since only the pass knows which names came from the specification (`PLAN.md` §2's
    identifier-hygiene row: hygiene is checked at every pass, not just the printer). Extend
    `keywords` with `Network2Go`'s own synthesized names (lock variables) once those exist.
  - Precedence levels are Go's own: `||` 1, `&&` 2, comparisons 3, `+`/`-` 4, `*`/`/`/`%` 5, unary
    6, selector/index/call 7. `Common/Pretty.lean`'s `infixl`/`prefix` combinators parenthesize
    against them, so no expression is over-parenthesized.
  - Blocks always break (`Std.Format.indent` without a surrounding `group`): generated Go is read
    and `gofmt`-ed by whoever consumes it, so a stable one-statement-per-line layout is worth more
    than a compact one.
  - String literals print as Go raw strings (`` `…` ``), same as prior art — no escaping pass
    needed. A source string containing a backtick would break this; TLA⁺'s own string syntax has no
    way to write one.
  - `print` compiles to Go's builtin `println`, not `fmt.Println`, so that generated code needs no
    import beyond the runtime library.
-/

namespace Go

/-- Go's 25 reserved words. These can never be identifiers, in any position, so the printer escapes
them unconditionally. -/
private def keywords : Std.HashSet String := {
  "break", "case", "chan", "const", "continue", "default",
  "defer", "else", "fallthrough", "for", "func", "go", "goto",
  "if", "import", "interface", "map", "package", "range", "return",
  "select", "struct", "switch", "type", "var"
}

/-- Go's *predeclared* identifiers — types, constants and builtin functions living in the universe
block. Unlike `keywords` these are ordinary identifiers that a declaration may legally shadow, so
the printer must **not** escape them: the generated code refers to `int`, `any`, `comparable`,
`error` and `append`/`len`/`make` by name constantly, and prior art's single combined table turned
those into `int__`/`comparable__`.

A *user-chosen* name colliding with one of these still has to be renamed — shadowing `int` in a
file that also emits `int` for TLA⁺'s `Int` would silently change what the generated code means.
That rename belongs to `Network2Go`, which is the only place that knows whether a name came from
the specification or from the compiler; this set is exported for it to consult (`PLAN.md` §2's
"checked at every pass, not just the final pretty-printer"). -/
def predeclared : Std.HashSet String := {
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

/-- Escape an identifier that would otherwise be a Go reserved word. Applied at every
identifier-print site — a backstop, not the whole hygiene story: see `predeclared`. -/
@[inline]
def sanitize (name : String) : String :=
  if name ∈ keywords then name ++ "__" else name

/-- A `{ … }` block. Built by hand rather than with `Std.Format.bracket`, which `group`s its
contents (so short blocks would collapse onto one line) and `nest`s the closing brace by the
opening one's width (so it wouldn't line up with the statement that opened it). -/
private def cblock (body : Std.Format) : Std.Format :=
  "{" ++ .indent 4 body ++ .line ++ "}"

partial def Typ.pretty : Typ → Std.Format
  | .int => "int"
  | .str => "string"
  | .bool => "bool"
  | .chan τ => "chan " ++ Typ.pretty τ
  | .slice τ => "[]" ++ Typ.pretty τ
  | .array n τ => f!"[{n}]" ++ Typ.pretty τ
  | .map key value => "map" ++ .sbracket (Typ.pretty key) ++ Typ.pretty value
  | .struct fields =>
    "struct " ++ .cbracket (.joinSep (fields.map λ (x, τ) ↦ sanitize x ++ " " ++ Typ.pretty τ) "; ")
  | .func params returns =>
    -- Go's return-type syntax: nothing when there is none, bare when there is exactly one,
    -- parenthesized when there are several.
    "func" ++ .paren (.joinSep (params.map Typ.pretty) ", ")
      ++ match returns with
        | [] => .nil
        | [τ] => " " ++ Typ.pretty τ
        | τs => " " ++ .paren (.joinSep (τs.map Typ.pretty) ", ")
  | .named name args =>
    sanitize name ++ if args.isEmpty then .nil else .sbracket (.joinSep (args.map Typ.pretty) ", ")
  | .var name => sanitize name

instance : Std.ToFormat Typ := ⟨Typ.pretty⟩

def UnaryOperator.symbol : UnaryOperator → String
  | .not => "!"
  | .neg => "-"

def BinaryOperator.symbol : BinaryOperator → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"

/-- Go's binary-operator precedence: `*`/`/`/`%` bind tighter than `+`/`-`, which bind tighter than
the comparisons, then `&&`, then `||`. -/
def BinaryOperator.precedence : BinaryOperator → Nat
  | .mul | .div | .mod => 5
  | .add | .sub => 4
  | .eq | .ne | .lt | .le | .gt | .ge => 3
  | .and => 2
  | .or => 1

def Builtin.name : Builtin → String
  | .len => "len"
  | .cap => "cap"
  | .append => "append"

partial def Expression.pretty {α} [Std.ToFormat α] (e : Expression α) (prec : Nat) : Std.Format :=
  match e with
  | .nat n => f!"{n}"
  | .str s => f!"`{s}`"
  | .true => "true"
  | .false => "false"
  | .var name => sanitize name
  | .unary op e => .prefix Expression.pretty 6 op.symbol e prec
  | .binary op e₁ e₂ => .infixl Expression.pretty op.precedence op.symbol e₁ e₂ prec
  | .index e i => Expression.pretty e 7 ++ .sbracket (Expression.pretty i 0)
  | .field e name => Expression.pretty e 7 ++ "." ++ sanitize name
  | .call f args =>
    Expression.pretty f 7 ++ .paren (.joinSep (args.map (Expression.pretty · 0)) ", ")
  | .builtin b args =>
    b.name ++ .paren (.joinSep (args.map (Expression.pretty · 0)) ", ")
  | .structLit τ fields =>
    Std.format τ
      ++ .cbracket (.joinSep (fields.map λ (x, e) ↦
        sanitize x ++ ": " ++ Expression.pretty e 0) ", ")
  | .sliceLit τ elems =>
    Std.format τ ++ .cbracket (.joinSep (elems.map (Expression.pretty · 0)) ", ")
  | .mapLit τ entries =>
    Std.format τ
      ++ .cbracket (.joinSep (entries.map λ (k, v) ↦
        Expression.pretty k 0 ++ ": " ++ Expression.pretty v 0) ", ")
  | .make τ args =>
    "make" ++ .paren (.joinSep (Std.format τ :: args.map (Expression.pretty · 0)) ", ")

instance {α} [Std.ToFormat α] : Std.ToFormat (Expression α) := ⟨(Expression.pretty · 0)⟩

partial def Ref.pretty {Expr} [Std.ToFormat Expr] : Ref Expr → Std.Format
  | .wildcard => "_"
  | .var name => sanitize name
  | .index r e => Ref.pretty r ++ .sbracket (Std.format e)
  | .field r name => Ref.pretty r ++ "." ++ sanitize name

instance {Expr} [Std.ToFormat Expr] : Std.ToFormat (Ref Expr) := ⟨Ref.pretty⟩

/-- `skip` has no Go counterpart, so it prints as nothing and is dropped from every block rather
than left behind as a stray empty statement. -/
private def isSkip {Typ Expr} : Statement Typ Expr → Bool
  | .skip => true
  | _ => false

/-- Statements, one per line. Go terminates statements with the newline itself, so no `;`. -/
private def formatStatements {Typ Expr} (f : Statement Typ Expr → Std.Format)
    (B : List (Statement Typ Expr)) : Std.Format :=
  .joinSep (f <$> B.filter (!isSkip ·)) .line

private def formatBlock {Typ Expr} (f : Statement Typ Expr → Std.Format)
    (B : List (Statement Typ Expr)) : Std.Format :=
  if B.all isSkip then "{}" else cblock (formatStatements f B)

partial def Statement.pretty {Typ Expr} [Std.ToFormat Typ] [Std.ToFormat Expr] :
    Statement Typ Expr → Std.Format
  | .skip => .nil
  | .print e => f!"println({e})"
  | .panic e => f!"panic({e})"
  | .return es => "return " ++ .joinSep (Std.format <$> es) ", "
  | .var name τ => f!"var {sanitize name} {τ}"
  | .assign lhs rhs =>
    .joinSep (Std.format <$> lhs) ", " ++ " = " ++ .joinSep (Std.format <$> rhs) ", "
  | .make name τ capacity =>
    f!"{sanitize name} := make({τ}" ++ (capacity.elim .nil (f!", {·}")) ++ ")"
  | .close c => f!"close({c})"
  | .send c e => f!"{c} <- {e}"
  | .receive c x ok =>
    Std.format x ++ (ok.elim .nil (f!", {·}")) ++ f!" = <-{c}"
  | .go body => "go func() " ++ formatBlock Statement.pretty body ++ "()"
  | .if cond thenBranch elseBranch =>
    f!"if {cond} " ++ formatBlock Statement.pretty thenBranch
      ++ if elseBranch.isEmpty then .nil else " else " ++ formatBlock Statement.pretty elseBranch
  | .for cond body => f!"for {cond} " ++ formatBlock Statement.pretty body
  | .switch e cases «default» =>
    f!"switch {e} " ++ cblock (.joinSep
      ((cases.map λ c ↦ f!"case {c.head}:" ++ (formatCase c.body))
        ++ [f!"default:" ++ (formatCase «default»)]) .line)
  | .select cases «default» =>
    "select " ++ cblock (.joinSep
      ((cases.map λ c ↦
        f!"case " ++ Statement.pretty c.guard ++ f!":" ++ (formatCase c.body))
        ++ («default».elim [] (λ B ↦ [f!"default:" ++ (formatCase B)]))) .line)
where
  /-- A `case`/`default` arm's body: no braces of its own, since Go's `case` already delimits it,
  and nothing at all (not even an indented blank line) when the arm is empty. -/
  formatCase (B : List (Statement Typ Expr)) : Std.Format :=
    if B.all isSkip then .nil
    else Std.Format.indent 4 (formatStatements Statement.pretty B)

instance {Typ Expr} [Std.ToFormat Typ] [Std.ToFormat Expr] : Std.ToFormat (Statement Typ Expr) :=
  ⟨Statement.pretty⟩

def Function.pretty {Typ Expr} [Std.ToFormat Typ] [Std.ToFormat Expr]
    (F : Function Typ Expr) : Std.Format :=
  -- Each type parameter's constraint sits next to it: `[T comparable, U Ord[U]]`.
  let typeParams :=
    if F.typeParams.isEmpty then .nil
    else .sbracket (.joinSep (F.typeParams.map λ (T, c) ↦ f!"{sanitize T} {c}") ", ")
  let params := .joinSep (F.params.map λ (x, τ) ↦ f!"{sanitize x} {τ}") ", "
  let returns :=
    match F.returnType with
    | [] => Std.Format.nil
    | [τ] => " " ++ Std.format τ
    | τs => " " ++ .paren (.joinSep (Std.format <$> τs) ", ")
  f!"func {sanitize F.name}" ++ typeParams ++ .paren params ++ returns ++ " "
    ++ formatBlock Statement.pretty F.body

instance {Typ Expr} [Std.ToFormat Typ] [Std.ToFormat Expr] : Std.ToFormat (Function Typ Expr) :=
  ⟨Function.pretty⟩

end Go

end
