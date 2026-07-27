module

public import Core.Go.Syntax
public import Core.Go.Pretty
public import UnicodeBasic

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

/-- A reference to a `runtime/tlaplus` function or type-conversion, as an expression:
`tlaplus.MkSet`, `tlaplus.Bool`. Applying it is `Go.Expression.call`, which also covers Go's
conversion syntax — `tlaplus.Bool(true)` is a call as far as this AST is concerned. -/
def tlaplusVar {α} (name : String) : Go.Expression α := .var (qualified tlaplusPkg name)

/-- A reference to a `runtime/comm` function. -/
def commVar {α} (name : String) : Go.Expression α := .var (qualified commPkg name)

/-- A reference to a `runtime/locks` function: `locks.Acquire`, `locks.MkLock`. -/
def locksVar {α} (name : String) : Go.Expression α := .var (qualified locksPkg name)

/-- `tlaplus.f(e₁, …, eₙ)`. -/
def tlaplusCall {α} (name : String) (args : List (Go.Expression α)) : Go.Expression α :=
  .call (tlaplusVar name) args

/--
  Any name from the source — user-written or compiler-synthesized — respelled as a Go identifier.
  **Every** name crossing into generated code goes through this, which is what makes the two
  name-spaces disjoint.

  `Common/Fresh.lean` mints names as `<prefix>$<n>`, `$` being chosen because a TLA⁺ identifier
  cannot contain one, which is what makes the scheme collision-free across passes. A Go identifier
  cannot contain one either — and `Core/Go/Pretty.lean`'s `sanitize` will not respell it, escaping
  reserved words only — so the freshness argument has to be re-established in Go's alphabet rather
  than simply carried over.

  The encoding sends `_` to `__` and `$` to `_`:

  | source | Go |
  |---|---|
  | `x_1` (user) | `x__1` |
  | `set$1` (fresh) | `set_1` |
  | `set_1` (user) | `set__1` |

  **What carries it is parity, not the particular lengths.** Every maximal run of underscores in
  the output is a sum of contributions, two per source `_` and one per source `$`, so a run is
  odd exactly when it covers an odd number of `$`s. A user name contains no `$` and so has only
  even runs; a fresh name contains exactly one and so has exactly one odd run. An odd run
  therefore means "compiler-introduced", and no user name can reach a fresh name's spelling
  however it is written.

  Any pair of lengths with those parities would do — `$` odd, `_` even, or the two swapped. The
  one choice that cannot work is leaving `_` as itself, which would put user underscores and `$`s
  in the same parity class. Note the argument does not need fresh prefixes to be free of `_`:
  a prefix's underscores contribute evenly and leave the `$`'s parity intact.

  The encoding is **not injective in general** and must not be reused as though it were: `_$` and
  `$_` both encode to three underscores. That costs nothing here, since telling the two
  name-spaces apart is all that is asked of it — but a *second* `$` in one name would flip a run
  back to even and break the property silently. `freshName` interpolates exactly one.
-/
def goIdent (name : String) : String :=
  name.foldl (init := "") λ acc c ↦
    acc ++ (if c == '_' then "__" else if c == '$' then "_" else c.toString)

/-- The Go name of the dictionary parameter bound for a rigid type variable.

A polymorphic definition is called at many types, so its element ordering cannot be a closed
expression and has to be a value parameter — the one case where `ordDict` reads an environment
instead of building the dictionary outright. The parameter's name is derived from the type
variable's rather than looked up, so that `ordDict` needs no environment threaded through it: the
enclosing definition binds `ord_a` for exactly the type variables its own type mentions.

The single `_` in the prefix is itself compiler-introduced, and an odd-length run, so no user name
can reach it: `ord_x` here and a user's own `ord_x` (which escapes to `ord__x`) stay distinct.

It sits in the same shape as an escaped fresh name, though, so `ord` is **reserved as a
`freshName` prefix** — `freshName "ord"` would mint `ord$n`, spelled `ord_n`, which is exactly this
function's answer for a type variable named `n`. Nothing uses that prefix (the live ones are
`set`, `i`, `rec`, `inbox`, `fresh`); the reservation is what keeps it that way. -/
def ordParamName (a : String) : String := s!"ord_{goIdent a}"

/-!
  ## Renaming user-chosen names

  `goIdent` separates the compiler's names from the user's. What is left is the user's names
  against *each other* and against Go's own vocabulary, and the requirement (`PLAN.md` §2) is that
  generated code never introduces shadowing.

  **The renaming is a pure function of the name, not a collision map, and that is forced rather
  than preferred.** Record fields decide it: Go identifies struct types *structurally*, so a field
  name has to receive the same Go name at every occurrence or two identically-shaped records become
  two different Go types, and `compileTyp`'s field sorting stops making the shapes coincide. A map
  would therefore have to be built from every field name in the whole program before any of it is
  emitted — and fields appear in *inferred* types, not only in declared ones, so collecting them
  means a pass over everything the checker produced. A pure function gives the same guarantee for
  free, and the same mechanism then serves definitions, so there is only one story to keep straight.

  **The disambiguation mark is one appended `_`.** `goIdent` leaves a name's trailing underscore
  run even-length (or absent), so appending one makes it odd, which is the compiler's half of the
  parity split — a marked name is unreachable from an unmarked one however it is spelled, and from
  a fresh name too, those ending in a digit. The mark composes with the escaping instead of
  competing with it.

  **Which side gets marked differs by name class, and follows the conventions of the language being
  compiled.** A definition must start uppercase to be exported and TLA⁺ definitions are
  conventionally already capitalized, so `Init` passes through and `init` is marked. Record fields
  must also be capitalized (§7.2.2), but TLA⁺ fields are conventionally lowercase, so the marking
  is reversed: `from` becomes `From`, matching §7.3's worked example, and a source `From` is the
  one marked. Each class keeps its common case clean. The two do not share a namespace — Go's
  struct fields are per-type, package-level names are not — so the two schemes cannot interfere.
-/

/-- The compiler's disambiguation mark: one `_`, which makes the trailing underscore run odd and so
puts the result in the compiler's half of `goIdent`'s parity split. -/
private def marked (name : String) : String := name ++ "_"

/-- `f` applied to a name's first character. -/
private def mapFirst (f : Char → Char) (name : String) : String :=
  match name.toList with
  | [] => name
  | c :: cs => String.ofList (f c :: cs)

/-- Does `name` already start with an uppercase letter, i.e. is Go already willing to export it?

`Unicode.isUppercase` rather than an ASCII test: Go's export rule reads the first character's
Unicode class, and the lexer accepts any Unicode letter to start an identifier, so a definition
named `Élan` is exported and must not be marked as though it were lowercase. -/
private def startsUppercase (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: _ => Unicode.isUppercase c

/-- A name Go's own vocabulary would swallow: a reserved word, or a predeclared identifier the
generated code refers to by name. Marked rather than left alone — shadowing `len` in a scope where
the emitted code calls `len` silently changes what that call means, and `compileQuantifier` emits
one two lines from any binder it introduces. -/
private def avoidsReserved (name : String) : String :=
  if Go.keywords.contains name || Go.predeclared.contains name then marked name else name

/-- The Go name of a binder: a quantifier's variable, an operator's parameter, a rigid type
variable. §7.2.2 renames definitions and record fields but deliberately leaves variables alone, so
this only escapes the name and steps around Go's own vocabulary. -/
def binderName (name : String) : String := avoidsReserved (goIdent name)

/-- The Go name of a top-level TLA⁺ definition (§7.2.2).

Capitalized so that the definition is exported, which is what lets generated code spread over
more than one file later without revisiting the naming scheme. Uppercasing is `Unicode.getUpperChar`
rather than `String.capitalize`, whose `Char.toUpper` is ASCII-only while the lexer accepts any
Unicode letter to start an identifier (`Parser_/TLAPlus.lean`'s `identifierOrKeyword`): a definition
named `élan` becomes `Élan` and is exported, where an ASCII capitalize would have left it lowercase
and unexported for a reason having nothing to do with the specification.

A *caseless* first letter has no uppercase to map to, and so stays unexported: `getUpperChar` is
`Simple_Uppercase_Mapping` and leaves `ß` and `ﬁ` alone (their full mappings are two characters, and
`UnicodeBasic` ships no `SpecialCasing.txt`), while `א` and `日` have no uppercase in any mapping.
Knowingly unhandled — TLA⁺ proper admits only ASCII identifiers (*Specifying Systems* §16.1), so
these names are already outside the specified language and reach this function only through this
parser's more permissive lexer. Everything still compiles; the definitions are merely package-local,
which costs nothing while the generated code is one package.

Already-capitalized names pass through and lowercase ones are marked, so `Init` stays `Init` and
`init` becomes `Init_` — the conventional spelling of a TLA⁺ definition is the one kept clean.

`LOCAL` definitions must *not* export, so they are pushed the other way, into the lowercase-initial
half, with the marking reversed to match. The two halves are disjoint by first-character case,
which is what keeps a `LOCAL` name from colliding with an exported one. (`LOCAL` has no parser
production today, so this arm is unreachable.) -/
def definitionName (isLocal : Bool) (name : String) : String :=
  let name := goIdent name
  if isLocal then
    if startsUppercase name then marked (mapFirst Unicode.getLowerChar name) else name
  else
    if startsUppercase name then name else marked (mapFirst Unicode.getUpperChar name)

/-- The Go name of a record field (§7.2.2 — "the same renaming is performed for fields of record
types").

Marked on the opposite side from `definitionName`: TLA⁺ record fields are conventionally lowercase,
so `from` becomes `From` — §7.3's worked example — and a source `From` is the one that takes the
mark. Package-level names and struct field names do not share a namespace, so the two schemes are
free to differ. -/
def fieldName (name : String) : String :=
  let name := goIdent name
  if startsUppercase name then marked name else mapFirst Unicode.getUpperChar name

/-!
  ## Names this pass invents at package level

  §7.2.3 needs a Go function per atomic block, per branch, per thread and per process, plus the
  `Network` struct type — none of which the specification names. They land in the same package
  namespace as the compiled TLA⁺ definitions, so they need to be disjoint from those *and* from
  each other, and the thesis's own spellings are not: §7.3 calls `sndPi`'s scheduler `SndPi`,
  which `definitionName` would also produce for a definition named `sndPi`, and calls the process
  function `Pong` — while `PingPongs.tla` has both a process named `Ping` and a `CONSTANT` named
  `Ping`, whose compiled names would then be the same identifier. So the readable names cannot be
  used as-is.

  **The shape is `<Kind>_<parts…>`, and the single underscore is what makes it safe.** `goIdent`
  doubles every user underscore, so a single one can only come from a `$` — which no user name
  contains. A compiler name whose first underscore is followed by more characters is therefore
  unreachable from any `definitionName` output, whose only single underscore is the trailing mark.
  The parts are `goIdent`-escaped, so distinct sources give distinct names: `goIdent` is injective
  on `$`-free strings, which user labels and process names are.

  Every one of these is capitalized and so exported. That is deliberate for the process function —
  it is the entry point whoever wires the system together calls — and harmless for the rest.
-/

/-- The Go type name for the network shape (§7.3's `Network` struct). One per compiled algorithm,
not per process. -/
def networkTypName : String := "Net_Network"

/-- The scheduler function for an atomic block: the `Rand`-driven loop over its branches. -/
def blockName (proc label : String) : String := s!"Blk_{goIdent proc}_{goIdent label}"

/-- The function for one branch of an atomic block, `i` counting from 1 as in §7.3's `SndPi1`. -/
def branchName (proc label : String) (i : Nat) : String :=
  s!"Brn_{goIdent proc}_{goIdent label}_{i}"

/-- The function for a thread, `k` its index in the process. -/
def threadName (proc : String) (k : Nat) : String := s!"Thr_{goIdent proc}_{k}"

/-- The function for a receiving thread (§7.3's `Thread_rx`), `k` its index in the process. Kept
distinct from `threadName` rather than sharing its numbering: the two have different signatures,
and a reader should not have to count threads to tell which is which. -/
def rxThreadName (proc : String) (k : Nat) : String := s!"Rx_{goIdent proc}_{k}"

/-- The function for a whole process — the one the user calls to start it. -/
def processName (proc : String) : String := s!"Proc_{goIdent proc}"

/-- The Go name of tuple component `i`, counting from 1.

A tuple is compiled as the record shape `[proj1 ↦ τ₁, …, projn ↦ τₙ]` (§5.7), so its components
are ordinary fields and get an ordinary field's capitalization. Being lowercase in the source, they
land on `fieldName`'s clean side: `Proj1`, not `Proj1_`. -/
def projName (i : Nat) : String := fieldName s!"proj{i}"

end Network2Go

end
