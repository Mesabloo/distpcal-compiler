module

public import Core.TypedTLAPlus.Syntax

@[expose] public section


/-!
  The single shared table of builtin operators — every name `builtinContext`
  (`Elaborator/Declarations.lean`) and `builtinModules` (`Driver/Builtins.lean`) bind, keyed by
  `(Origin, name)`. Pure data with no `Driver`/`Elaborator` dependency, so any pass downstream of
  type checking can recognize a builtin call without re-deriving its own string list.

  `WellFormedness/Restrictions.lean`'s reserved-temporal-action check and `Typed2Computable`'s
  "is this builtin computable?" question used to keep independent copies of this list — this file
  is now the one place that name↔operator wiring is written down.

  One constructor per literal builtin rather than a lighter category-tagged table: gives
  exhaustiveness-checked `match`es to every downstream consumer, at the cost of hand-duplicating
  each name a third time here.
-/

namespace TypedTLAPlus

/-- One constructor per name `builtinContext`/`builtinModules` bind. Naming mirrors each
operator's own TLA⁺ role, not its surface spelling (`eq` for `=`, `cup` for `\cup`, …) — see
`builtinOpOf?` for the spelling↔constructor table itself. -/
inductive BuiltinOp : Type
  -- `builtinContext` (`Elaborator/Declarations.lean`) — `Origin.intrinsic`.
  | eq | neq
  | and | or | implies | iff | neg
  | inSet | notInSet | subseteq | cup | cap | setMinus
  | domain
  | enabled | unchanged | always | eventually | prime
  -- `Naturals` (`Driver/Builtins.lean`).
  | plus | minus | unaryMinus | times | lt | gt | leq | geq | range | natSet
  -- `Sequences`.
  | len | head | tail | append
  -- `Integers`.
  | intSet
  -- `FiniteSets`.
  | isFiniteSet | cardinality
  -- `Bags`.
  | isABag | bagToSet | setToBag | bagIn | emptyBag | bagAdd | bagSub | bagUnion | bagLeq
  | subBag | bagOfAll | bagCardinality | copiesIn
  deriving Repr, Inhabited, BEq, DecidableEq

/-- The name↔operator table itself, one arm per `BuiltinOp` constructor (exhaustiveness-checked
by the compiler — a new `BuiltinOp` constructor with no arm here is a build error, not a silent
gap). `none` for any `(origin, name)` pair not bound by `builtinContext`/`builtinModules`. -/
def builtinOpOf? : Origin → String → Option BuiltinOp
  | .intrinsic, name => match name with
    | "=" => some .eq | "/=" => some .neq
    | "/\\" => some .and | "\\/" => some .or | "=>" => some .implies | "<=>" => some .iff
    | "\\neg" => some .neg
    | "\\in" => some .inSet | "\\notin" => some .notInSet | "\\subseteq" => some .subseteq
    | "\\cup" => some .cup | "\\cap" => some .cap | "\\" => some .setMinus
    | "DOMAIN" => some .domain
    | "ENABLED" => some .enabled | "UNCHANGED" => some .unchanged
    | "[]" => some .always | "<>" => some .eventually | "'" => some .prime
    | _ => none
  | .module "Naturals", name => match name with
    | "+" => some .plus | "-" => some .minus | "-." => some .unaryMinus | "*" => some .times
    | "<" => some .lt | ">" => some .gt | "=<" => some .leq | ">=" => some .geq
    | ".." => some .range | "Nat" => some .natSet
    | _ => none
  | .module "Sequences", name => match name with
    | "Len" => some .len | "Head" => some .head | "Tail" => some .tail | "Append" => some .append
    | _ => none
  | .module "Integers", name => match name with
    | "Int" => some .intSet
    | _ => none
  | .module "FiniteSets", name => match name with
    | "IsFiniteSet" => some .isFiniteSet | "Cardinality" => some .cardinality
    | _ => none
  | .module "Bags", name => match name with
    | "IsABag" => some .isABag | "BagToSet" => some .bagToSet | "SetToBag" => some .setToBag
    | "BagIn" => some .bagIn | "EmptyBag" => some .emptyBag
    | "(+)" => some .bagAdd | "(-)" => some .bagSub | "BagUnion" => some .bagUnion
    | "\\sqsubseteq" => some .bagLeq | "SubBag" => some .subBag | "BagOfAll" => some .bagOfAll
    | "BagCardinality" => some .bagCardinality | "CopiesIn" => some .copiesIn
    | _ => none
  | .binder, _ | .module _, _ => none

/-- Recognizes `e` as a builtin call — `.opCall (.var name _ origin) args` where
`(origin, name)` hits `builtinOpOf?` — returning the operator and its argument list. `none` for
anything else, including a call to a resolved-but-non-builtin operator/function. -/
def Expression.recognizeBuiltin? {α : Type} : Expression α → Option (BuiltinOp × List (Expression α))
  | .opCall (.var name _ origin) args => (builtinOpOf? origin name).map (·, args)
  | _ => none

/-- The eight reserved temporal/action operator spellings real TLA⁺ core syntax carries, banned
outright by bare name in `WellFormedness/Restrictions.lean`'s check 3 regardless of whether the
name resolves to anything (a reserved name can never be shadowed by a user declaration, so an
origin-agnostic check is exact). `^+`/`^*`/`^#` have no typing rule and so no `BuiltinOp`
constructor above — genuinely unbound, unlike the other five, which double as real `builtinOpOf?`
entries (`.enabled`, `.unchanged`, `.always`, `.eventually`, `.prime`). Kept as a separate list
rather than derived from `builtinOpOf?`, since the two overlap but aren't the same. -/
def reservedTemporalActionNames : List String :=
  ["[]", "<>", "ENABLED", "UNCHANGED", "'", "^+", "^*", "^#"]

end TypedTLAPlus

end
