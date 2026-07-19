module

public import Core.Go.Syntax

public section

/-!
  Naming policy for `Network2Go`: what the generated Go calls the things a specification named,
  and what it calls the runtime library it links against.

  Two separate concerns meet here.

  - **Runtime references.** Generated code names the runtime library constantly, so the package
    qualifiers live in one place rather than being spelled at every construction site. The
    packages are `runtime/tlaplus` (TLA⁺'s own value types), `runtime/comm` (message passing) and
    `runtime/locks` (mutual exclusion); none of them is called `runtime`, deliberately, since that
    is Go's own package name.
  - **Renaming what the user wrote.** Thesis §7.2.2 capitalizes every defined name in the
    generated code regardless of the original's case, except `LOCAL` definitions, so that
    definitions are exported from the package they land in; record fields get the same treatment
    (§7.3's worked example turns a record's `from`/`mes` into `From`/`Mes`), process variables do
    not.
-/

namespace Network2Go

/-- The `runtime/tlaplus` package's qualifier, as it appears in generated code. -/
def tlaplusPkg : String := "tlaplus"

/-- The `runtime/comm` package's qualifier. -/
def commPkg : String := "comm"

/-- The `runtime/locks` package's qualifier. -/
def locksPkg : String := "locks"

/-- A qualified reference to a name in one of the runtime packages, `pkg.name`. Go's package
qualifier is an ordinary part of the identifier as far as this AST is concerned — `Go.Typ.named`
and `Go.Expression.var` both carry it as one string. -/
def qualified (pkg name : String) : String := s!"{pkg}.{name}"

/-- A runtime type from `runtime/tlaplus`, applied to type arguments when generic:
`tlaplus.Set[τ]`, `tlaplus.Int`. -/
def tlaplusTyp (name : String) (args : List Go.Typ := []) : Go.Typ :=
  .named (qualified tlaplusPkg name) args

/-- A runtime type from `runtime/comm`: `comm.Address`, `comm.Sender[τ]`. -/
def commTyp (name : String) (args : List Go.Typ := []) : Go.Typ :=
  .named (qualified commPkg name) args

/-- A runtime type from `runtime/locks`: `locks.Lock[τ]`. -/
def locksTyp (name : String) (args : List Go.Typ := []) : Go.Typ :=
  .named (qualified locksPkg name) args

/-- The Go name of a top-level TLA⁺ definition (§7.2.2).

Capitalized so that the definition is exported, which is what lets generated code spread over
more than one file later without revisiting the naming scheme. `LOCAL` definitions keep their
case, since exporting them would contradict the `LOCAL` they were declared with.

Two caveats, neither of which bites while all generated code lands in one package.

`String.capitalize` uppercases via `Char.toUpper`, which is ASCII-only, while the lexer accepts
any Unicode letter to start an identifier (`Parser_/TLAPlus.lean`'s `identifierOrKeyword` uses
`Unicode.alpha`). A definition named `élan` therefore stays lowercase, and Go's export rule reads
the first character's Unicode class, so it would not be exported.

Capitalizing is also not injective: `from` and `From` are different TLA⁺ names and become the
same Go one. §2 makes renaming user-chosen names on collision this pass's job, and that renaming
is not written yet. -/
def definitionName (isLocal : Bool) (name : String) : String :=
  if isLocal then name else name.capitalize

/-- The Go name of a record field (§7.2.2 — "the same renaming is performed for fields of record
types"). -/
def fieldName (name : String) : String := name.capitalize

/-- The Go name of tuple component `i`, counting from 1.

A tuple is compiled as the record shape `[proj1 ↦ τ₁, …, projn ↦ τₙ]` (§5.7), so its components
are ordinary fields and get an ordinary field's capitalization. -/
def projName (i : Nat) : String := fieldName s!"proj{i}"

end Network2Go

end
