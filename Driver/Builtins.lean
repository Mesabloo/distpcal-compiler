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

/-- The span every synthesized builtin body node is registered at. A builtin operator has no
source text anywhere, so there is no real span to give it — but *not* registering it is not the
same as having no position: `posOf` cannot distinguish an unregistered value from one whose
address a dead value left an entry under, and answers with that entry (`Common/Position.lean`).
These bodies are compiled-in constants that live for the whole process, and
`WellFormedness/Reachability.lean`'s walk reads their positions whenever a module `EXTENDS` a
standard module, so leaving them unregistered means a real diagnostic can be reported against an
unrelated span. -/
private def pos : SourceSpan := SourceSpan.placeholder

/-- `Op(x₁, …, xₙ) == Op(x₁, …, xₙ)` (`Op == Op` at arity 0): a self-referential body for a builtin
whose meaning is a backend-native implementation with no TLA⁺ expression behind it — which is every
builtin here. The parameter types come from `τ`'s own operator argument list, so each `xᵢ` is a de
Bruijn `.bound (n-1-i)` (declaration order, last innermost, matching `Elaborator/Context.lean`).
Only the name and type of a builtin declaration are ever read (`Decl.bindings`); the body exists so
the reachability walk has a registered span, and the self-reference resolves against the walk's own
memo the second time it is reached, so the walk terminates. -/
private def selfRef (mod : String) (τ : TypedTLAPlus.Typ) (name : String) :
    TypedTLAPlus.Expression TypedTLAPlus.Typ :=
  match τ with
  | .operator args _ =>
    let n := args.length
    .opCall (.var τ (.module mod name) @@ pos)
      ((List.range n).zip args |>.map λ (i, ρ) ↦ .var ρ (.bound (n - 1 - i)) @@ pos) @@ pos
  | _ => .var τ (.module mod name) @@ pos

/-- A builtin operator declaration with a self-referential body (`selfRef`). -/
private def builtinOp (mod : String) (τ : TypedTLAPlus.Typ) (name : String)
    (params : List (String × Nat)) : Decl :=
  .operator τ name params (selfRef mod τ name)

/-- `Naturals`'s operators: arithmetic, comparisons, the `..` range constructor, and `Nat` itself
(a value — `Set(Int)` — bound as a 0-ary operator). Unary minus is **not** here — real TLA⁺ puts
it in `Integers`, `Naturals` having no negatives. `\div`/`%` are integer division and its
remainder, `\div` spelled with the backslash it is written with (the parser's
`InfixOperator.canonicalName`, `Desugarer/TLAPlus.lean`) — there is no bare `/` on `Int`, real
TLA⁺'s `/` belonging to `Reals`, which is out of scope. `^` is exponentiation, typed
`Int × Int → Int` and so only total for a non-negative exponent: `2^-1` is a `Reals` value, and the
runtime rejects it rather than the type system. -/
private def naturalsDeclarations : List Decl :=
  let binInt : TypedTLAPlus.Typ := .operator [.int, .int] .int
  let binCmp : TypedTLAPlus.Typ := .operator [.int, .int] .bool
  [ builtinOp "Naturals" binInt "+" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binInt "-" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binInt "*" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binInt "\\div" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binInt "%" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binInt "^" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binCmp "<" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binCmp ">" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binCmp "=<" [("x", 0), ("y", 0)],
    builtinOp "Naturals" binCmp ">=" [("x", 0), ("y", 0)],
    builtinOp "Naturals" (.operator [.int, .int] (.set .int)) ".." [("x", 0), ("y", 0)],
    builtinOp "Naturals" (.set .int) "Nat" [] ]

/-- `Sequences`'s operators. `Len` returns `Int`; `Head` returns bare `a`; `Tail`/`Append` return
`Seq(a)`. -/
private def sequencesDeclarations : List Decl :=
  [ builtinOp "Sequences" (.operator [.seq (.var "a")] .int) "Len" [("s", 0)],
    builtinOp "Sequences" (.operator [.seq (.var "a")] (.var "a")) "Head" [("s", 0)],
    builtinOp "Sequences" (.operator [.seq (.var "a")] (.seq (.var "a"))) "Tail" [("s", 0)],
    builtinOp "Sequences" (.operator [.seq (.var "a"), .var "a"] (.seq (.var "a"))) "Append"
      [("s", 0), ("e", 0)] ]

/-- `Integers`'s operators: `Int` itself and unary minus (`-.`, distinct from binary `-` by the
parser's `InfixOperator.canonicalName`). `Integers` `«extends» := ["Naturals"]`, so a module doing
`EXTENDS Integers` gets the arithmetic too — matching real TLA⁺, where unary minus is an `Integers`
operator, not a `Naturals` one. -/
private def integersDeclarations : List Decl :=
  [ builtinOp "Integers" (.set .int) "Int" [],
    builtinOp "Integers" (.operator [.int] .int) "-." [("x", 0)] ]

/-- `FiniteSets`'s operators. `Naturals`/`Sequences` are `LOCAL INSTANCE`d in the real module —
`LOCAL` there only means "not re-exported to a module doing `EXTENDS FiniteSets`", but this
table's `«extends»` field is this project's own import-dependency edge, not a re-export flag
(`resolveModule`/`compileModule` treat every builtin the same regardless of `LOCAL`), so
`FiniteSets` still `«extends» := ["Naturals", "Sequences"]`. `Network2Go` compiles `IsFiniteSet` to
constant `true` (every `Set` this compiler represents is finite by construction), independent of
this self-referential body. -/
private def finiteSetsDeclarations : List Decl :=
  [ builtinOp "FiniteSets" (.operator [.set (.var "a")] .bool) "IsFiniteSet" [("S", 0)],
    builtinOp "FiniteSets" (.operator [.set (.var "a")] .int) "Cardinality" [("S", 0)] ]

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
  let bag : TypedTLAPlus.Typ := .function (.var "a") .int
  let binBag : TypedTLAPlus.Typ := .operator [bag, bag] bag
  [ builtinOp "Bags" (.operator [bag] .bool) "IsABag" [("B", 0)],
    builtinOp "Bags" (.operator [bag] (.set (.var "a"))) "BagToSet" [("B", 0)],
    builtinOp "Bags" (.operator [.set (.var "a")] bag) "SetToBag" [("S", 0)],
    builtinOp "Bags" (.operator [.var "a", bag] .bool) "BagIn" [("e", 0), ("B", 0)],
    builtinOp "Bags" bag "EmptyBag" [],
    builtinOp "Bags" binBag "(+)" [("B1", 0), ("B2", 0)],
    builtinOp "Bags" binBag "(-)" [("B1", 0), ("B2", 0)],
    builtinOp "Bags" (.operator [.set bag] bag) "BagUnion" [("S", 0)],
    builtinOp "Bags" (.operator [bag, bag] .bool) "\\sqsubseteq" [("B1", 0), ("B2", 0)],
    builtinOp "Bags" (.operator [bag] (.set bag)) "SubBag" [("B", 0)],
    builtinOp "Bags" (.operator [.operator [.var "a"] (.var "b"), bag] (.function (.var "b") .int))
      "BagOfAll" [("F", 1), ("B", 0)],
    builtinOp "Bags" (.operator [bag] .int) "BagCardinality" [("B", 0)],
    builtinOp "Bags" (.operator [.var "a", bag] .int) "CopiesIn" [("e", 0), ("B", 0)] ]

private def funAsSeqType : TypedTLAPlus.Typ :=
  .operator [.function .int (.var "a")] (.seq (.var "a"))
private def mkSeqType : TypedTLAPlus.Typ :=
  .operator [.int, .operator [.int] (.var "a")] (.seq (.var "a"))
private def setAsFunType : TypedTLAPlus.Typ :=
  .operator [.set (.tuple [.var "a", .var "b"])] (.function (.var "a") (.var "b"))

/-- `Fugue`'s operators — this compiler's own module, not a real TLA⁺ standard one, so there is no
upstream source to mirror.

`\prec`/`\preceq`/`\succ`/`\succeq` are the order on `Address`. The generated Go requires one
(`runtime/comm/address.go`'s `Address` interface carries `Lt`, and every set of addresses,
address-keyed function, and `CHOOSE` over addresses depends on it), while the type checker treats
`Address` as an opaque atomic type with equality only. These four are the seam: a specification
that wants to talk about that order `EXTENDS Fugue` and writes `a \prec b`, and code generation
compiles it to `comm.AddressOrd`'s `Lt`/`Le`/`Gt`/`Ge`. They have no TLA⁺-side definition — the
order is deliberately unspecified (`runtime/comm/address.go`), so no TLA⁺ definition would be sound
for every implementation, and a specification may assume nothing about them beyond their type.

`FunAsSeq : (Int -> a) => Seq(a)` reads a function back as the sequence it encodes — the direction
subtyping's `Seq(τ) <: Int → τ` axiom cannot give. Partial: defined only when `DOMAIN f = 1 .. n`
for some `n`, and the generated program aborts otherwise. `SetAsFun : Set(<<a,b>>) => (a -> b)`
reads a set of pairs as a function, aborting when two pairs share a first component. Both are
Apalache operators; a call to either raises `-Wunsafe`. `MkSeq : (Int, (Int -> a)) => Seq(a)` is
the total sequence constructor `[i ∈ 1 .. N ↦ F(i)]` — safe, no warning. -/
private def addressOrderOp (name : String) : Decl :=
  builtinOp "Fugue" (.operator [.address, .address] .bool) name [("x", 0), ("y", 0)]

private def fugueDeclarations : List Decl :=
  [ addressOrderOp "\\prec", addressOrderOp "\\preceq",
    addressOrderOp "\\succ", addressOrderOp "\\succeq",
    builtinOp "Fugue" funAsSeqType "FunAsSeq" [("f", 0)],
    builtinOp "Fugue" mkSeqType "MkSeq" [("N", 0), ("F", 1)],
    builtinOp "Fugue" setAsFunType "SetAsFun" [("S", 0)] ]

/-- The table itself (doc above). `«extends»` mirrors each real module's own top-of-file
dependency list (`EXTENDS`/`LOCAL INSTANCE` alike — `LOCAL` only means "not re-exported" in real
TLA⁺, not "not a dependency", and `resolveModule`/`compileModule` don't distinguish the two
anyway), so a module that only `EXTENDS Sequences`/`Integers`/`FiniteSets`/`Bags` still
transitively sees everything that real module itself imports. `RealTime`/`Reals` are out of
scope entirely (never ported). `Fugue` is the one entry with no real counterpart — this compiler's
own module; it `EXTENDS Naturals`, since a downcast's `1 .. n` domain is unwritable without it, so
`EXTENDS Fugue` alone is enough to use one. -/
def builtinModules : Std.HashMap String TypedModule := Std.HashMap.ofList <|
  #[("Sequences", sequencesDeclarations, ["Naturals"]), ("Naturals", naturalsDeclarations, []),
      ("Integers", integersDeclarations, ["Naturals"]), ("FiniteSets", finiteSetsDeclarations, ["Naturals", "Sequences"]),
      ("Bags", bagsDeclarations, ["TLC", "Naturals"]), ("TLC", [], []),
      ("Fugue", fugueDeclarations, ["Naturals"])].toList.map λ (name, decls, exts) ↦
    (name, ({
      name := name
      «extends» := exts
      declarations₁ := decls
      pcalAlgorithm := none
      declarations₂ := []
    } : TypedModule))

end
