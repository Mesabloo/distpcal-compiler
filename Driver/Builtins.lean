import Elaborator.Elaborator

/-!
  Standard TLA⁺ modules (`Sequences`, `TLC`, `Naturals`, `FiniteSets`, …) — a hardcoded table of
  already-checked `Module`s, not bundled `.tla` stub files: standard-library operators (`Len`,
  `Head`, `Append`, …) get replaced by backend-native implementations at code-generation time
  regardless of what their "definition" says.

  Kept as full `Module`s (not a bare declaration list) so the `Γ`-merge step in
  `Driver/Modules.lean`'s `compileModule` treats a builtin hit and a real resolved dependency
  identically. Still subject to the same ambiguity rule as any other candidate source: a user's
  own module of the same name is not silently shadowed by a builtin, or vice versa.
-/

/-- Placeholder bodies for the declarations below — only the name and type actually matter
(`Decl.bindings` never looks at a body). Each is a well-typed value of the operator's own return
type, except `Head`'s use of `intZero`: a rigid type variable has no witness value at all, so
that one is genuinely fake but harmless. -/
private def intZero : TypedTLAPlus.Expression TypedTLAPlus.Typ := .nat "0"
private def emptySetInt : TypedTLAPlus.Expression TypedTLAPlus.Typ := .set [] .int
private def emptySeqOfVarA : TypedTLAPlus.Expression TypedTLAPlus.Typ := .seq [] (.var "a")

/-- `Naturals`'s operators: arithmetic, comparisons, the `..` range constructor, and `Nat` itself
(a value — `Set(Int)` — bound as a 0-ary operator). `-.` is unary minus, distinct from binary
`-`. -/
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

/-- `Sequences`'s operators. `Len` returns `Int`; `Tail`/`Append` return `Seq(a)`, well-typed for
any `a` via the empty sequence; `Head` returns bare `a`, so its placeholder body isn't actually
well-typed (harmless, see module doc). -/
private def sequencesDeclarations : List Decl :=
  [ .operator (.operator [.seq (.var "a")] .int) "Len" [("s", 0)] intZero,
    .operator (.operator [.seq (.var "a")] (.var "a")) "Head" [("s", 0)] intZero,
    .operator (.operator [.seq (.var "a")] (.seq (.var "a"))) "Tail" [("s", 0)] emptySeqOfVarA,
    .operator (.operator [.seq (.var "a"), .var "a"] (.seq (.var "a"))) "Append" [("s", 0), ("e", 0)] emptySeqOfVarA ]

/-- The table itself (doc above). `Sequences` genuinely `«extends» := ["Naturals"]`, matching
real TLA⁺, so a module that only `EXTENDS Sequences` still transitively sees `Naturals`'s
operators. -/
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
