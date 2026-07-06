import Elaborator.Elaborator

/-!
  Standard TLA⁺ modules (`Sequences`, `TLC`, `Naturals`, `FiniteSets`, …) — a hardcoded table of
  already-checked `Module`s, **not** bundled `.tla` stub files: the compiler would need to know
  their install location, and each one would still need processing like any other module, for no
  benefit — standard-library operators (`Len`, `Head`, `Append`, …) get replaced by backend-native
  implementations at code-generation time regardless of what their "definition" says. Populated
  incrementally as real test input needs specific operators.

  Kept as full `Module`s (not a bare declaration list) so the `Γ`-merge step in
  `Driver/Modules.lean`'s `compileModule` treats a builtin hit and a real resolved dependency
  identically: `mod.declarations₁ ++ mod.declarations₂`, no special case. Still subject to the
  same ambiguity rule as any other candidate source (`Driver/Modules.lean`'s `locate`) — a user's
  own module of the same name is not silently shadowed by a builtin, or vice versa. A builtin
  `EXTENDS`ing another builtin needs no separate mechanism — `resolveModule`'s existing recursion
  already generalizes to it.
-/

/-- Every declaration below only needs to carry a name and a type into `Γ` (module doc) —
`Decl.bindings` never looks at a body, and standard-library operators get replaced by
backend-native implementations at code-generation time regardless of what their "definition"
says. Still, each one below is a genuinely well-typed value *of that operator's own return
type*, except `Head`'s `a` below: a rigid, universally-quantified type variable has no witness
value at all, so it's the one placeholder that's still genuinely fake. -/
private def intZero : TypedTLAPlus.Expression TypedTLAPlus.Typ := .nat "0"
private def emptySetInt : TypedTLAPlus.Expression TypedTLAPlus.Typ := .set [] .int
private def emptySeqOfVarA : TypedTLAPlus.Expression TypedTLAPlus.Typ := .seq [] (.var "a")

/-- `Naturals`'s operators: arithmetic, comparisons, the `..` range constructor, and `Nat` itself
(a *value* — `Set(Int)` — not the grammar's own `Int` *type*; a 0-ary "operator" the same way
`Elaborator/Declarations.lean`'s `checkDeclaration` binds a 0-ary definition's name directly to
its plain result type, no `Typ.operator` wrapper). `-.` is unary minus, distinct from binary `-`.
Every body here is checked against the operator's own *return* type, so `Int`-returning operators
get `intZero`, `Bool`-returning comparisons get `.true`, and `..`/`Nat` (both `Set(Int)`-returning)
get `emptySetInt`. -/
private def naturalsDeclarations : List Decl :=
  [ .operator (.operator [.int, .int] .int) "+" [("x", 0), ("y", 0)] intZero,
    .operator (.operator [.int, .int] .int) "-" [("x", 0), ("y", 0)] intZero,
    .operator (.operator [.int] .int) "-." [("x", 0)] intZero,
    .operator (.operator [.int, .int] .int) "*" [("x", 0), ("y", 0)] intZero,
    .operator (.operator [.int, .int] .bool) "<" [("x", 0), ("y", 0)] .true,
    .operator (.operator [.int, .int] .bool) ">" [("x", 0), ("y", 0)] .true,
    .operator (.operator [.int, .int] .bool) "=<" [("x", 0), ("y", 0)] .true,
    .operator (.operator [.int, .int] .bool) ">=" [("x", 0), ("y", 0)] .true,
    .operator (.operator [.int, .int] (.set .int)) ".." [("x", 0), ("y", 0)] emptySetInt,
    .operator (.set .int) "Nat" [] emptySetInt ]

/-- `Sequences`'s operators. `Len` returns `Int` (`intZero`); `Tail`/`Append` return `Seq(a)`,
genuinely well-typed for *any* `a` via the empty sequence (`emptySeqOfVarA`) — no witness of `a`
itself is needed to build one. `Head` returns bare `a` — a rigid type variable with no witness
value at all, so `intZero` here is the one placeholder in this file that isn't actually
well-typed (harmless: never re-checked, module doc above). -/
private def sequencesDeclarations : List Decl :=
  [ .operator (.operator [.seq (.var "a")] .int) "Len" [("s", 0)] intZero,
    .operator (.operator [.seq (.var "a")] (.var "a")) "Head" [("s", 0)] intZero,
    .operator (.operator [.seq (.var "a")] (.seq (.var "a"))) "Tail" [("s", 0)] emptySeqOfVarA,
    .operator (.operator [.seq (.var "a"), .var "a"] (.seq (.var "a"))) "Append" [("s", 0), ("e", 0)] emptySeqOfVarA ]

/-- The table itself (doc above). `Sequences` genuinely `«extends» := ["Naturals"]`, matching
real TLA⁺ — `Driver/Modules.lean`'s `resolveModule` `.builtin` case resolves a builtin's own
`extends` list the same way it does an ordinary module's, so a module that only `EXTENDS
Sequences` (not separately `Naturals`) still transitively sees `Naturals`'s operators. -/
def builtinModules : Std.HashMap String TypedModule := Std.HashMap.ofList <|
  #[("Sequences", sequencesDeclarations, ["Naturals"]), ("Naturals", naturalsDeclarations, []),
      ("Bags", [], []), ("TLC", [], []), ("FiniteSets", [], [])].toList.map λ (name, decls, exts) ↦
    (name, ({
      name := name
      «extends» := exts
      declarations₁ := decls
      pcalAlgorithm := none
      declarations₂ := []
    } : TypedModule))
