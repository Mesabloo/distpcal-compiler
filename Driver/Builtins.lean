module

public import Elaborator

public section

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
that one is genuinely fake but harmless.

Each is registered at `SourceSpan.placeholder`. A builtin operator has no source text anywhere,
so there is no real span to give it — but *not* registering it is not the same as having no
position: `posOf` cannot distinguish an unregistered value from one whose address a dead value
left an entry under, and answers with that entry (`Common/Position.lean`). These bodies are
compiled-in constants that live for the whole process, and `WellFormedness/Reachability.lean`'s
walk reads their positions whenever a module `EXTENDS` a standard module, so leaving them
unregistered means a real diagnostic can be reported against an unrelated span. -/
private def pos : SourceSpan := SourceSpan.placeholder

/-- `TRUE`, as the body of every predicate-valued builtin.

Named rather than written inline at each use because `Expression.true` is a *nullary*
constructor: Lean gives every occurrence of it one shared, statically allocated object, so it has
exactly one address and therefore exactly one entry in the span map, program-wide. Registering it
here is what keeps `posOf` from answering for it with an unrelated node's span; it cannot give
per-occurrence positions, and no amount of registration would — the same limitation
`Parser_/Annotations.lean` records for `Annotation`'s own nullary constructors. -/
private def trueBody : TypedTLAPlus.Expression TypedTLAPlus.Typ := .true @@ pos

private def intZero : TypedTLAPlus.Expression TypedTLAPlus.Typ := .nat "0" @@ pos
private def emptySetInt : TypedTLAPlus.Expression TypedTLAPlus.Typ := .set [] .int @@ pos
private def emptySeqOfVarA : TypedTLAPlus.Expression TypedTLAPlus.Typ := .seq [] (.var "a") @@ pos
private def emptySetOfVarA : TypedTLAPlus.Expression TypedTLAPlus.Typ := .set [] (.var "a") @@ pos
/-- A vacuous `[x \in {} |-> 0]` — well-typed at `Function(a, Int)` for any `a`, since an empty
domain witnesses any codomain. Used as the placeholder body for every `Bags` operator returning a
bag. -/
private def emptyFnOfVarAToInt : TypedTLAPlus.Expression TypedTLAPlus.Typ :=
  .fn "x" (.var "a") .int emptySetOfVarA intZero @@ pos
private def emptyFnOfVarBToInt : TypedTLAPlus.Expression TypedTLAPlus.Typ :=
  .fn "x" (.var "b") .int (.set [] (.var "b") @@ pos) intZero @@ pos
private def emptySetOfFnVarAToInt : TypedTLAPlus.Expression TypedTLAPlus.Typ :=
  .set [] (.function (.var "a") .int) @@ pos

/-- `Naturals`'s operators: arithmetic, comparisons, the `..` range constructor, and `Nat` itself
(a value — `Set(Int)` — bound as a 0-ary operator). `-.` is unary minus, distinct from binary
`-`. -/
private def naturalsDeclarations : List Decl :=
  [ .operator (.operator [.int, .int] .int) "+" [("x", 0), ("y", 0)] intZero,
    .operator (.operator [.int, .int] .int) "-" [("x", 0), ("y", 0)] intZero,
    .operator (.operator [.int] .int) "-." [("x", 0)] intZero,
    .operator (.operator [.int, .int] .int) "*" [("x", 0), ("y", 0)] intZero,
    .operator (.operator [.int, .int] .bool) "<" [("x", 0), ("y", 0)] trueBody,
    .operator (.operator [.int, .int] .bool) ">" [("x", 0), ("y", 0)] trueBody,
    .operator (.operator [.int, .int] .bool) "=<" [("x", 0), ("y", 0)] trueBody,
    .operator (.operator [.int, .int] .bool) ">=" [("x", 0), ("y", 0)] trueBody,
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

/-- `Integers`'s operators — just `Int` itself. Unary minus (`-.`) is already declared by
`naturalsDeclarations` above: unlike real TLA⁺ (where `-.` belongs to `Integers`), this project's
`Naturals` stub already carries it, and `Integers` genuinely `«extends» := ["Naturals"]`, so it
doesn't need to redeclare it. -/
private def integersDeclarations : List Decl :=
  [ .operator (.set .int) "Int" [] emptySetInt ]

/-- `FiniteSets`'s operators. `Naturals`/`Sequences` are `LOCAL INSTANCE`d in the real module —
`LOCAL` there only means "not re-exported to a module doing `EXTENDS FiniteSets`", but this
table's `«extends»` field is this project's own import-dependency edge, not a re-export flag
(`resolveModule`/`compileModule` treat every builtin the same regardless of `LOCAL`), so
`FiniteSets` still `«extends» := ["Naturals", "Sequences"]`. -/
private def finiteSetsDeclarations : List Decl :=
  [ .operator (.operator [.set (.var "a")] .bool) "IsFiniteSet" [("S", 0)] trueBody,
    .operator (.operator [.set (.var "a")] .int) "Cardinality" [("S", 0)] intZero ]

/-- `Bags`'s operators — a bag of `a`s represented the same way the real module does, as a
`Function(a, Int)` (`DOMAIN` gives the underlying set, application gives a copy count). `Sum` is
`LOCAL` in the real module (a helper for `BagUnion`/`BagCardinality`'s own definitions), so it's
not included here — matches `FiniteSets`/`Sequences` never exporting their own `LOCAL` helpers
either. `EXTENDS TLC` and `LOCAL INSTANCE Naturals` in the real module both become `«extends»`
edges here regardless of `LOCAL` (see `finiteSetsDeclarations`'s doc above), so `«extends» :=
["TLC", "Naturals"]` — `TLC` itself is currently an empty stub so this has no effect yet.

`EmptyBag : Function(a, Int)` is genuinely polymorphic, matching real TLA⁺ — every reference gets
its own fresh instantiation of `a`, since `Decl.bindings` (`Driver/Modules.lean`) marks every
0-ary `operator` declaration a scheme (`Elaborator/Monad.lean`'s `Binding.isScheme`), freshened at
each `Γ`-reference by `Elaborator/Expressions.lean`'s `inferExpr`. -/
private def bagsDeclarations : List Decl :=
  [ .operator (.operator [.function (.var "a") .int] .bool) "IsABag" [("B", 0)] trueBody,
    .operator (.operator [.function (.var "a") .int] (.set (.var "a"))) "BagToSet" [("B", 0)] emptySetOfVarA,
    .operator (.operator [.set (.var "a")] (.function (.var "a") .int)) "SetToBag" [("S", 0)] emptyFnOfVarAToInt,
    .operator (.operator [.var "a", .function (.var "a") .int] .bool) "BagIn" [("e", 0), ("B", 0)] trueBody,
    .operator (.function (.var "a") .int) "EmptyBag" [] emptyFnOfVarAToInt,
    .operator (.operator [.function (.var "a") .int, .function (.var "a") .int] (.function (.var "a") .int))
      "(+)" [("B1", 0), ("B2", 0)] emptyFnOfVarAToInt,
    .operator (.operator [.function (.var "a") .int, .function (.var "a") .int] (.function (.var "a") .int))
      "(-)" [("B1", 0), ("B2", 0)] emptyFnOfVarAToInt,
    .operator (.operator [.set (.function (.var "a") .int)] (.function (.var "a") .int)) "BagUnion" [("S", 0)] emptyFnOfVarAToInt,
    .operator (.operator [.function (.var "a") .int, .function (.var "a") .int] .bool)
      "\\sqsubseteq" [("B1", 0), ("B2", 0)] trueBody,
    .operator (.operator [.function (.var "a") .int] (.set (.function (.var "a") .int))) "SubBag" [("B", 0)] emptySetOfFnVarAToInt,
    .operator (.operator [.operator [.var "a"] (.var "b"), .function (.var "a") .int] (.function (.var "b") .int))
      "BagOfAll" [("F", 1), ("B", 0)] emptyFnOfVarBToInt,
    .operator (.operator [.function (.var "a") .int] .int) "BagCardinality" [("B", 0)] intZero,
    .operator (.operator [.var "a", .function (.var "a") .int] .int) "CopiesIn" [("e", 0), ("B", 0)] intZero ]

/-- The table itself (doc above). `«extends»` mirrors each real module's own top-of-file
dependency list (`EXTENDS`/`LOCAL INSTANCE` alike — `LOCAL` only means "not re-exported" in real
TLA⁺, not "not a dependency", and `resolveModule`/`compileModule` don't distinguish the two
anyway), so a module that only `EXTENDS Sequences`/`Integers`/`FiniteSets`/`Bags` still
transitively sees everything that real module itself imports. `RealTime`/`Reals` are out of
scope entirely (never ported). -/
def builtinModules : Std.HashMap String TypedModule := Std.HashMap.ofList <|
  #[("Sequences", sequencesDeclarations, ["Naturals"]), ("Naturals", naturalsDeclarations, []),
      ("Integers", integersDeclarations, ["Naturals"]), ("FiniteSets", finiteSetsDeclarations, ["Naturals", "Sequences"]),
      ("Bags", bagsDeclarations, ["TLC", "Naturals"]), ("TLC", [], [])].toList.map λ (name, decls, exts) ↦
    (name, ({
      name := name
      «extends» := exts
      declarations₁ := decls
      pcalAlgorithm := none
      declarations₂ := []
    } : TypedModule))

end
