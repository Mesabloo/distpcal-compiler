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
  - Expressions and statements print from one `mutual` block, since `Expression.funcLit` carries a
    statement body. Statement cases therefore call `Expression.pretty · 0` directly rather than
    going through the `Std.ToFormat` instance, which is only available once the block closes.
  - String literals print as Go raw strings (`` `…` ``), same as prior art — no escaping pass
    needed. A source string containing a backtick would break this; TLA⁺'s own string syntax has no
    way to write one.
  - `print` compiles to Go's builtin `println`, not `fmt.Println`, so that generated code needs no
    import beyond the runtime library.
-/

namespace Go

/-- Go's 25 reserved words. These can never be identifiers, in any position, so the printer escapes
them unconditionally.

Exported alongside `predeclared` so that `Network2Go` can rename a user-chosen name *out* of this
set rather than leaving it to `sanitize` below — a rename that knows the name's provenance can pick
a spelling that stays distinct from every other name, which a blind suffix cannot. -/
def keywords : Std.HashSet String := {
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
identifier-print site — a backstop, not the whole hygiene story: see `predeclared`.

Unreachable for anything `Network2Go` emits, which renames user-chosen names out of `keywords`
itself; this catches only a name reaching the printer from somewhere that did not.

The suffix is a *single* `_`, not the doubled one prior art used, because `Network2Go` spends
underscore-run parity to separate user-written names from compiler-introduced ones (see its
`Naming.lean`): a doubled suffix lands in the user half, so `type` and a user's own `type_` would
both print `type__`. An odd-length suffix cannot collide with either. -/
@[inline]
def sanitize (name : String) : String :=
  if name ∈ keywords then name ++ "_" else name

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

/-- Go's return-type syntax, shared by `Typ.func`, `Expression.funcLit` and `Function`: nothing when
there is none, bare when there is exactly one, parenthesized when there are several. -/
private def formatReturns {α} [Std.ToFormat α] : List α → Std.Format
  | [] => .nil
  | [τ] => " " ++ Std.format τ
  | τs => " " ++ .paren (.joinSep (Std.format <$> τs) ", ")

/-- Takes the expression formatter as an argument rather than resolving it from `Std.ToFormat`:
`Ref` is printed from inside the `Expression`/`Statement` mutual block below, where the instance
for `Expression` does not exist yet. -/
partial def Ref.pretty {Expr} (f : Expr → Std.Format) : Ref Expr → Std.Format
  | .wildcard => "_"
  | .var name => sanitize name
  | .index r e => Ref.pretty f r ++ .sbracket (f e)
  | .field r name => Ref.pretty f r ++ "." ++ sanitize name

instance {Expr} [Std.ToFormat Expr] : Std.ToFormat (Ref Expr) := ⟨Ref.pretty Std.format⟩

/-- `skip` has no Go counterpart, so it prints as nothing and is dropped from every block rather
than left behind as a stray empty statement. -/
private def isSkip {α} : Statement α → Bool
  | .skip => true
  | _ => false

/-- Statements, one per line. Go terminates statements with the newline itself, so no `;`. -/
private def formatStatements {α} (f : Statement α → Std.Format) (B : List (Statement α)) :
    Std.Format :=
  .joinSep (f <$> B.filter (!isSkip ·)) .line

private def formatBlock {α} (f : Statement α → Std.Format) (B : List (Statement α)) : Std.Format :=
  if B.all isSkip then "{}" else cblock (formatStatements f B)

/-- A `case`/`default` arm's body: no braces of its own, since Go's `case` already delimits it, and
nothing at all (not even an indented blank line) when the arm is empty. -/
private def formatCase {α} (f : Statement α → Std.Format) (B : List (Statement α)) : Std.Format :=
  if B.all isSkip then .nil else Std.Format.indent 4 (formatStatements f B)

mutual

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
  -- No parentheses around the literal itself: Go accepts `func() T { … }()` in call position and
  -- in every argument position, and a bare literal never starts a statement in emitted code (the
  -- immediately-applied ones are always an operand of something).
  | .funcLit params returns body =>
    "func" ++ .paren (.joinSep (params.map λ (x, τ) ↦ f!"{sanitize x} {τ}") ", ")
      ++ formatReturns returns ++ " " ++ formatBlock Statement.pretty body

partial def Statement.pretty {α} [Std.ToFormat α] : Statement α → Std.Format
  | .skip => .nil
  | .print e => "println" ++ .paren (Expression.pretty e 0)
  | .panic e => "panic" ++ .paren (Expression.pretty e 0)
  | .return es => "return " ++ .joinSep (es.map (Expression.pretty · 0)) ", "
  | .var name τ => f!"var {sanitize name} {τ}"
  | .assign lhs rhs =>
    .joinSep (lhs.map (Ref.pretty (Expression.pretty · 0))) ", " ++ " = "
      ++ .joinSep (rhs.map (Expression.pretty · 0)) ", "
  | .make name τ capacity =>
    f!"{sanitize name} := make({τ}"
      ++ (capacity.elim .nil (λ e ↦ ", " ++ Expression.pretty e 0)) ++ ")"
  | .close c => "close" ++ .paren (Expression.pretty c 0)
  | .send c e => Expression.pretty c 0 ++ " <- " ++ Expression.pretty e 0
  | .receive c x ok =>
    Ref.pretty (Expression.pretty · 0) x
      ++ (ok.elim .nil (λ r ↦ ", " ++ Ref.pretty (Expression.pretty · 0) r))
      ++ " = <-" ++ Expression.pretty c 0
  | .go body => "go func() " ++ formatBlock Statement.pretty body ++ "()"
  | .if cond thenBranch elseBranch =>
    "if " ++ Expression.pretty cond 0 ++ " " ++ formatBlock Statement.pretty thenBranch
      ++ if elseBranch.isEmpty then .nil else " else " ++ formatBlock Statement.pretty elseBranch
  | .for cond body =>
    "for " ++ Expression.pretty cond 0 ++ " " ++ formatBlock Statement.pretty body
  | .switch e cases «default» =>
    "switch " ++ Expression.pretty e 0 ++ " " ++ cblock (.joinSep
      ((cases.map λ c ↦
        "case " ++ Expression.pretty c.head 0 ++ ":" ++ formatCase Statement.pretty c.body)
        ++ [f!"default:" ++ formatCase Statement.pretty «default»]) .line)
  | .select cases «default» =>
    "select " ++ cblock (.joinSep
      ((cases.map λ c ↦
        f!"case " ++ Statement.pretty c.guard ++ f!":" ++ formatCase Statement.pretty c.body)
        ++ («default».elim [] (λ B ↦ [f!"default:" ++ formatCase Statement.pretty B]))) .line)

end

instance {α} [Std.ToFormat α] : Std.ToFormat (Expression α) := ⟨(Expression.pretty · 0)⟩

instance {α} [Std.ToFormat α] : Std.ToFormat (Statement α) := ⟨Statement.pretty⟩

def Function.pretty {α} [Std.ToFormat α] (F : Function α) : Std.Format :=
  -- Each type parameter's constraint sits next to it: `[T comparable, U Ord[U]]`.
  let typeParams :=
    if F.typeParams.isEmpty then .nil
    else .sbracket (.joinSep (F.typeParams.map λ (T, c) ↦ f!"{sanitize T} {c}") ", ")
  let params := .joinSep (F.params.map λ (x, τ) ↦ f!"{sanitize x} {τ}") ", "
  f!"func {sanitize F.name}" ++ typeParams ++ .paren params ++ formatReturns F.returnType ++ " "
    ++ formatBlock Statement.pretty F.body

instance {α} [Std.ToFormat α] : Std.ToFormat (Function α) := ⟨Function.pretty⟩

/-- A top-level declaration. The `var` form spells its type even when there is an initializer, so
that a `nil`-valued or otherwise uninferable right-hand side still declares the right thing, and
because §7.2.2's own listings do. -/
def Declaration.pretty {α} [Std.ToFormat α] : Declaration α → Std.Format
  | .function F => Function.pretty F
  | .var name τ value =>
    f!"var {sanitize name} {τ}"
      ++ value.elim .nil (λ e ↦ " = " ++ Expression.pretty e 0)

instance {α} [Std.ToFormat α] : Std.ToFormat (Declaration α) := ⟨Declaration.pretty⟩

end Go

end
