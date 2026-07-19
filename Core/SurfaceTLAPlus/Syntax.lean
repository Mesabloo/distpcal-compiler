module

public import Common.Position
public import Core.Declaration
public import Mathlib.Control.Bifunctor
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Control.Traversable.Instances
public import Mathlib.Control.Bitraversable.Basic
public import Mathlib.Control.Bitraversable.Instances
public import Extra.Prod

@[expose] public section


/-!
  The surface syntax of TLA⁺ modules, as accepted by the parser — a CST close to the concrete
  grammar (<https://lamport.azurewebsites.net/tla/TLAPlus2Grammar.tla>), not yet desugared.

  Positions are not stored structurally in these types: every constructor produced by the parser
  is tagged out-of-band via the `@@`/`posOf`/`match_source` mechanism in `Common/Position.lean`.
-/

namespace SurfaceTLAPlus

/--
  The entire set of prefix operators reserved in TLA⁺. `Fin _` parameters distinguish
  alternative spellings of the same operator (given in doc-comment order).
-/
inductive PrefixOperator : Type
  /-- `-` -/
  | «-»
  /-- `¬`: `\neg`, `\lnot`, or `~` -/
  | «\neg » (_ : Fin 3)
  /-- `□`: `[]` -/
  | «[]»
  /-- `◇`: `<>` -/
  | «<>»
  /-- `DOMAIN` -/
  | DOMAIN
  /-- `ENABLED` -/
  | ENABLED
  /-- `SUBSET` -/
  | SUBSET
  /-- `UNCHANGED` -/
  | UNCHANGED
  /-- `UNION` -/
  | UNION
  deriving BEq, Repr, DecidableEq, Inhabited

abbrev PrefixOperator.«\neg» : PrefixOperator := .«\neg » 0
abbrev PrefixOperator.«\lnot» : PrefixOperator := .«\neg » 1
abbrev PrefixOperator.«~» : PrefixOperator := .«\neg » 2

instance : ToString PrefixOperator where
  toString
    | .«-» => "-"
    | .«\neg» => r"\neg"
    | .«\lnot» => r"\lnot"
    | .«~» => r"~"
    | .«[]» => "[]"
    | .«<>» => "<>"
    | .DOMAIN => "DOMAIN"
    | .ENABLED => "ENABLED"
    | .SUBSET => "SUBSET"
    | .UNCHANGED => "UNCHANGED"
    | .UNION => "UNION"

/-- The entire set of postfix operators reserved in TLA⁺. -/
inductive PostfixOperator : Type
  /-- `^+` -/
  | «^+»
  /-- `^*` -/
  | «^*»
  /-- `^#` -/
  | «^#»
  /-- `'` -/
  | «'»
  deriving BEq, Repr, DecidableEq, Inhabited

instance : ToString PostfixOperator where
  toString
    | .«^+» => "^+"
    | .«^*» => "^*"
    | .«^#» => "^#"
    | .«'» => "'"

/-- The entire set of infix operators reserved in TLA⁺. -/
inductive InfixOperator : Type
  | «!!» | «##» | «$$» | «$» | «%%» | «%» | «&&» | «&»
  /-- `⊕`: `(+)` or `\oplus` -/
  | «(+) » (_ : Fin 2)
  /-- `⊝`: `(-)` or `\ominus` -/
  | «(-) » (_ : Fin 2)
  /-- `⊙`: `(.)` or `\odot` -/
  | «(.) » (_ : Fin 2)
  /-- `⊘`: `(/)` or `\oslash` -/
  | «(/) » (_ : Fin 2)
  /-- `⊗`: `(\X)` or `\otimes` -/
  | «(\X) » (_ : Fin 2)
  /--
    `×`: `\X` or `\times`. Not actually a binary operator in the grammar, but treated as such
    for simplicity.
  -/
  | «\X » (_ : Fin 2)
  | «**» | «*» | «++» | «+» | «-+->» | «--»
  /-- `⊣`: `-|` -/
  | «-|»
  | «-» | «...» | «..» | «.» | «//»
  /-- `≠`: `/=` or `#` -/
  | «/= » (_ : Fin 2)
  /-- `∧`: `/\` or `\land` -/
  | «/\ » (_ : Fin 2)
  | «/»
  /-- `⩴`: `::=` -/
  | «::=»
  /-- `≔`: `:=` -/
  | «:=»
  | «:>» | «<:»
  /-- `≡`: `<=>` or `\equiv` -/
  | «<=> » (_ : Fin 2)
  /-- `≤`: `=<`, `<=`, or `\leq` -/
  | «=< » (_ : Fin 3)
  /-- `⇒`: `=>` -/
  | «=>»
  /-- `⫤`: `=|` -/
  | «=|»
  | «<» | «=»
  /-- `≥`: `>=` or `\geq` -/
  | «>= » (_ : Fin 2)
  | «>» | «??» | «?» | «@@»
  /-- `∨`: `\/` or `\lor` -/
  | «\/ » (_ : Fin 2)
  | «^^» | «^»
  /-- `⊢`: `|-` -/
  | «|-»
  /-- `⊨`: `|=` -/
  | «|=»
  /-- `‖`: `||` -/
  | «||»
  | «|»
  /-- `⤳`: `~>` -/
  | «~>»
  -- LaTeX-only spellings, no ASCII alternative.
  | «\approx» | «\sqsupseteq» | «\asymp» | «\gg» | «\star» | «\bigcirc»
  /-- `∈`: `\in` -/
  | «\in»
  | «\preceq» | «\prec» | «\subseteq» | «\subset» | «\bullet»
  /-- `∩`: `\cap` or `\intersect` -/
  | «\cap » (_ : Fin 2)
  | «\propto» | «\succeq» | «\succ» | «\cdot» | «\simeq» | «\sim» | «\ll» | «\supseteq» | «\supset» | «\cong» | «\sqcap»
  /-- `∪`: `\cup` or `\union` -/
  | «\cup » (_ : Fin 2)
  /-- `∘`: `\o` or `\circ` -/
  | «\o » (_ : Fin 2)
  | «\sqcup» | «\div» | «\sqsubseteq» | «\sqsubset» | «\uplus» | «\doteq» | «\wr» | «\sqsupset»
  /-- `∉`: `\notin` -/
  | «\notin»
  /-- backslash, `\` -/
  | «\»
  deriving BEq, Repr, Inhabited

set_option maxHeartbeats 400000 in
deriving instance DecidableEq for InfixOperator

abbrev InfixOperator.«(+)» : InfixOperator := .«(+) » 0
abbrev InfixOperator.«\oplus» : InfixOperator := .«(+) » 1
abbrev InfixOperator.«(-)» : InfixOperator := .«(-) » 0
abbrev InfixOperator.«\ominus» : InfixOperator := .«(-) » 1
abbrev InfixOperator.«(.)» : InfixOperator := .«(.) » 0
abbrev InfixOperator.«\odot» : InfixOperator := .«(.) » 1
abbrev InfixOperator.«(/)» : InfixOperator := .«(/) » 0
abbrev InfixOperator.«\oslash» : InfixOperator := .«(/) » 1
abbrev InfixOperator.«(\X)» : InfixOperator := .«(\X) » 0
abbrev InfixOperator.«\otimes» : InfixOperator := .«(\X) » 1
abbrev InfixOperator.«\X» : InfixOperator := .«\X » 0
abbrev InfixOperator.«\times» : InfixOperator := .«\X » 1
abbrev InfixOperator.«/=» : InfixOperator := .«/= » 0
abbrev InfixOperator.«#» : InfixOperator := .«/= » 1
abbrev InfixOperator.«/\» : InfixOperator := .«/\ » 0
abbrev InfixOperator.«\land» : InfixOperator := .«/\ » 1
abbrev InfixOperator.«<=>» : InfixOperator := .«<=> » 0
abbrev InfixOperator.«\equiv» : InfixOperator := .«<=> » 1
abbrev InfixOperator.«=<» : InfixOperator := .«=< » 0
abbrev InfixOperator.«<=» : InfixOperator := .«=< » 1
abbrev InfixOperator.«\leq» : InfixOperator := .«=< » 2
abbrev InfixOperator.«>=» : InfixOperator := .«>= » 0
abbrev InfixOperator.«\geq» : InfixOperator := .«>= » 1
abbrev InfixOperator.«\/» : InfixOperator := .«\/ » 0
abbrev InfixOperator.«\lor» : InfixOperator := .«\/ » 1
abbrev InfixOperator.«\cap» : InfixOperator := .«\cap » 0
abbrev InfixOperator.«\intersect» : InfixOperator := .«\cap » 1
abbrev InfixOperator.«\cup» : InfixOperator := .«\cup » 0
abbrev InfixOperator.«\union» : InfixOperator := .«\cup » 1
abbrev InfixOperator.«\o» : InfixOperator := .«\o » 0
abbrev InfixOperator.«\circ» : InfixOperator := .«\o » 1

instance : ToString InfixOperator where
  toString
    | .«!!» => "!!" | .«##» => "##" | .«$$» => "$$" | .«$» => "$" | .«%%» => "%%" | .«%» => "%"
    | .«&&» => "&&" | .«&» => "&"
    | .«(+)» => "(+)" | .«\oplus» => r"\oplus"
    | .«(-)» => "(-)" | .«\ominus» => r"\ominus"
    | .«(.)» => "(.)" | .«\odot» => r"\odot"
    | .«(/)» => "(/)" | .«\oslash» => r"\oslash"
    | .«(\X)» => r"(\X)" | .«\otimes» => r"\otimes"
    | .«\X» => r"\X" | .«\times» => r"\times"
    | .«**» => "**" | .«*» => "*" | .«++» => "++" | .«+» => "+"
    | .«-+->» => "-+->" | .«--» => "--" | .«-|» => "-|" | .«-» => "-"
    | .«...» => "..." | .«..» => ".." | .«.» => "." | .«//» => "//"
    | .«/=» => "/=" | .«#» => "#"
    | .«/\» => r"/\" | .«\land» => r"\land" | .«/» => "/" -- "
    | .«::=» => "::=" | .«:=» => ":=" | .«:>» => ":>" | .«<:» => "<:"
    | .«<=>» => "<=>" | .«\equiv» => r"\equiv"
    | .«=<» => "=<" | .«<=» => "<=" | .«\leq» => r"\leq"
    | .«=>» => "=>" | .«=|» => "=|" | .«<» => "<" | .«=» => "="
    | .«>=» => ">=" | .«\geq» => r"\geq" | .«>» => ">"
    | .«?» => "?" | .«??» => "??" | .«@@» => "@@"
    | .«\/» => r"\/" | .«\lor» => r"\lor" | .«^^» => "^^" | .«^» => "^"
    | .«|-» => "|-" | .«|=» => "|=" | .«||» => "||" | .«|» => "|" | .«~>» => "~>"
    | .«\approx» => r"\approx" | .«\sqsupseteq» => r"\sqsupseteq" | .«\asymp» => r"\asymp"
    | .«\gg» => r"\gg" | .«\star» => r"\star" | .«\bigcirc» => r"\bigcirc" | .«\in» => r"\in"
    | .«\preceq» => r"\preceq" | .«\prec» => r"\prec" | .«\subseteq» => r"\subseteq"
    | .«\subset» => r"\subset" | .«\bullet» => r"\bullet"
    | .«\cap» => r"\cap" | .«\intersect» => r"\intersect" | .«\propto» => r"\propto"
    | .«\succeq» => r"\succeq" | .«\succ» => r"\succ" | .«\cdot» => r"\cdot"
    | .«\simeq» => r"\simeq" | .«\sim» => r"\sim" | .«\ll» => r"\ll"
    | .«\supseteq» => r"\supseteq" | .«\supset» => r"\supset" | .«\cong» => r"\cong"
    | .«\sqcap» => r"\sqcap" | .«\cup» => r"\cup" | .«\union» => r"\union"
    | .«\o» => r"\o" | .«\circ» => r"\circ" | .«\sqcup» => r"\sqcup" | .«\div» => r"\div"
    | .«\sqsubseteq» => r"\sqsubseteq" | .«\sqsubset» => r"\sqsubset" | .«\uplus» => r"\uplus"
    | .«\doteq» => r"\doteq" | .«\wr» => r"\wr" | .«\sqsupset» => r"\sqsupset"
    | .«\notin» => r"\notin" | .«\» => r"\" -- "

/-- TLA⁺ types, in the [same format as Apalache](https://apalache-mc.org/docs/adr/002adr-types.html). -/
inductive Typ : Type
  | bool
  | int
  | str
  /-- `τ -> τ` -/
  | function (_ _ : Typ)
  /-- `Set(τ)` -/
  | set (_ : Typ)
  /-- `Seq(τ)` -/
  | seq (_ : Typ)
  /-- `<<τ₁, …, τₙ>>` -/
  | tuple (_ : List Typ)
  /-- `(τ₁, …, τₙ) => τₙ₊₁` -/
  | operator (_ : List Typ) (_ : Typ)
  /-- A rigid, universally-quantified type variable `a`. -/
  | var (_ : String)
  /-- `CONSTANT` -- an abstract type. -/
  | const (_ : String)
  | record (_ : List (String × Typ))
  /-- `Channel(τ)`. Covariant: `τ <: τ' → Channel(τ) <: Channel(τ')`. -/
  | channel (_ : Typ)
  /-- `Address`. -/
  | address
  /-- A metavariable `?n`, resolved during type checking; never appears in a fully-elaborated
  `TypedTLAPlus` term. -/
  | mvar (_ : Nat)
  deriving Repr, Inhabited, BEq

/-- Whether `τ` is Channel-shaped: a bare `Channel(τ')`, or an indexed channel family `dom ->
Channel(τ')` (as `Elaborator/PlusCal.lean`'s `checkChannelDecl` encodes it). Shared by
`WellFormedness/Declarations.lean` (checks 2(a)/(d)) and `WellFormedness/Restrictions.lean` (check
1) as one source of truth for "legal channel type." -/
def Typ.isChannelLike : Typ → Bool
  | .channel _ => true
  | .function _ (.channel _) => true
  | _ => false

-- `deriving DecidableEq` doesn't apply here -- proved by hand instead.
partial instance : DecidableEq Typ :=
  let rec go (τ τ' : Typ) : Decidable (τ = τ') := match τ, τ' with
    | .bool, .bool | .int, .int | .str, .str | .address, .address => isTrue rfl
    | .function dom rng, .function dom' rng' =>
      match go dom dom', go rng rng' with
      | .isTrue h₁, .isTrue h₂ => isTrue (by rw [h₁, h₂])
      | .isFalse h, _ | _, .isFalse h => isFalse λ h' ↦ by injections; contradiction
    | .set τ, .set τ' | .seq τ, .seq τ' | .channel τ, .channel τ' =>
      match go τ τ' with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse λ h' ↦ by injections; contradiction
    | .tuple τs, .tuple τs' =>
      match @List.hasDecEq _ go τs τs' with
      | .isTrue h => isTrue (by rw [h])
      | .isFalse h => isFalse λ h' ↦ by injections; contradiction
    | .operator τs τ, .operator τs' τ' =>
      match @List.hasDecEq _ go τs τs', go τ τ' with
      | .isTrue h₁, .isTrue h₂ => isTrue (by rw [h₁, h₂])
      | .isFalse h, _ | _, .isFalse h => isFalse λ h' ↦ by injections; contradiction
    | .var v, .var v' | .const v, .const v' =>
      if h : v = v' then isTrue (by rw [h]) else isFalse λ h' ↦ by injections; contradiction
    | .record fs, .record fs' =>
      match @List.hasDecEq _ (@Prod.hasDecEq _ _ inferInstance go) fs fs' with
      | .isTrue h => isTrue (by rw [h])
      | .isFalse h => isFalse λ h' ↦ by injections; contradiction
    | .mvar n, .mvar n' =>
      if h : n = n' then isTrue (by rw [h]) else isFalse λ h' ↦ by injections; contradiction
    | .bool, .int | .bool, .str | .bool, .function .. | .bool, .set .. | .bool, .seq .. | .bool, .channel ..
    | .bool, .tuple .. | .bool, .operator .. | .bool, .var .. | .bool, .const .. | .bool, .record .. | .bool, .address | .bool, .mvar ..
    | .int, .bool | .int, .str | .int, .function .. | .int, .set .. | .int, .seq .. | .int, .channel ..
    | .int, .tuple .. | .int, .operator .. | .int, .var .. | .int, .const .. | .int, .record .. | .int, .address | .int, .mvar ..
    | .str, .bool | .str, .int | .str, .function .. | .str, .set .. | .str, .seq .. | .str, .channel ..
    | .str, .tuple .. | .str, .operator .. | .str, .var .. | .str, .const .. | .str, .record .. | .str, .address | .str, .mvar ..
    | .function .., .bool | .function .., .int | .function .., .str | .function .., .set .. | .function .., .seq ..
    | .function .., .channel .. | .function .., .tuple .. | .function .., .operator .. | .function .., .var ..
    | .function .., .const .. | .function .., .record .. | .function .., .address | .function .., .mvar ..
    | .set .., .bool | .set .., .int | .set .., .str | .set .., .function .. | .set .., .seq ..
    | .set .., .channel .. | .set .., .tuple .. | .set .., .operator .. | .set .., .var ..
    | .set .., .const .. | .set .., .record .. | .set .., .address | .set .., .mvar ..
    | .seq .., .bool | .seq .., .int | .seq .., .str | .seq .., .function .. | .seq .., .set ..
    | .seq .., .channel .. | .seq .., .tuple .. | .seq .., .operator .. | .seq .., .var ..
    | .seq .., .const .. | .seq .., .record .. | .seq .., .address | .seq .., .mvar ..
    | .channel .., .bool | .channel .., .int | .channel .., .str | .channel .., .function .. | .channel .., .set ..
    | .channel .., .seq .. | .channel .., .tuple .. | .channel .., .operator .. | .channel .., .var ..
    | .channel .., .const .. | .channel .., .record .. | .channel .., .address | .channel .., .mvar ..
    | .tuple .., .bool | .tuple .., .int | .tuple .., .str | .tuple .., .function .. | .tuple .., .set ..
    | .tuple .., .seq .. | .tuple .., .channel .. | .tuple .., .operator .. | .tuple .., .var ..
    | .tuple .., .const .. | .tuple .., .record .. | .tuple .., .address | .tuple .., .mvar ..
    | .operator .., .bool | .operator .., .int | .operator .., .str | .operator .., .function .. | .operator .., .set ..
    | .operator .., .seq .. | .operator .., .channel .. | .operator .., .tuple .. | .operator .., .var ..
    | .operator .., .const .. | .operator .., .record .. | .operator .., .address | .operator .., .mvar ..
    | .var .., .bool | .var .., .int | .var .., .str | .var .., .function .. | .var .., .set ..
    | .var .., .seq .. | .var .., .channel .. | .var .., .tuple .. | .var .., .operator ..
    | .var .., .const .. | .var .., .record .. | .var .., .address | .var .., .mvar ..
    | .const .., .bool | .const .., .int | .const .., .str | .const .., .function .. | .const .., .set ..
    | .const .., .seq .. | .const .., .channel .. | .const .., .tuple .. | .const .., .operator ..
    | .const .., .var .. | .const .., .record .. | .const .., .address | .const .., .mvar ..
    | .record .., .bool | .record .., .int | .record .., .str | .record .., .function .. | .record .., .set ..
    | .record .., .seq .. | .record .., .channel .. | .record .., .tuple .. | .record .., .operator ..
    | .record .., .var .. | .record .., .const .. | .record .., .address | .record .., .mvar ..
    | .address, .bool | .address, .int | .address, .str | .address, .function .. | .address, .set ..
    | .address, .seq .. | .address, .channel .. | .address, .tuple .. | .address, .operator ..
    | .address, .var .. | .address, .const .. | .address, .record .. | .address, .mvar ..
    | .mvar .., .bool | .mvar .., .int | .mvar .., .str | .mvar .., .function .. | .mvar .., .set ..
    | .mvar .., .seq .. | .mvar .., .channel .. | .mvar .., .tuple .. | .mvar .., .operator ..
    | .mvar .., .var .. | .mvar .., .const .. | .mvar .., .record .. | .mvar .., .address => isFalse nofun
  go

partial instance : ToString Typ where
  toString :=
    let rec go : Typ → String
      | .bool => "Bool"
      | .int => "Int"
      | .str => "Str"
      | .address => "Address"
      | .function τ₁@(.function ..) τ₂
      | .function τ₁@(.operator ..) τ₂ => s!"({go τ₁}) -> {go τ₂}"
      | .function τ₁ τ₂ => s!"{go τ₁} -> {go τ₂}"
      | .set τ => s!"Set({go τ})"
      | .seq τ => s!"Seq({go τ})"
      | .tuple τs => s!"<<{String.intercalate ", " (τs.map go)}>>"
      | .operator τs τ => s!"({String.intercalate ", " (τs.map go)}) => {go τ}"
      | .var v => v
      | .const v => v
      | .record fs => "[" ++ String.intercalate ", " (fs.map λ (v, τ) ↦ v ++ " : " ++ go τ) ++ "]"
      | .channel τ => s!"Channel({go τ})"
      | .mvar n => s!"?{n}"
    go

/-- Groups of variables bound in quantifiers (`\A`/`\E`/…). -/
inductive QuantifierBound (α β : Type) : Type
  /-- `x ∈ A` -/
  | var : α → String → β → QuantifierBound α β
  /-- `⟨x, y, …, z⟩ ∈ A` -/
  | varTuple : List (α × String) → β → QuantifierBound α β
  /-- `x, y, …, z ∈ A` -/
  | vars : List (α × String) → β → QuantifierBound α β
  deriving Repr, DecidableEq, BEq

protected def QuantifierBound.bimap {α β γ δ : Type} (f : α → γ) (g : β → δ) : QuantifierBound α β → QuantifierBound γ δ
  | .var ann v x => .var (f ann) v (g x)
  | .vars vs x => .vars (Bifunctor.fst f <$> vs) (g x)
  | .varTuple vs x => .varTuple (Bifunctor.fst f <$> vs) (g x)

instance : Bifunctor QuantifierBound where
  bimap := QuantifierBound.bimap

protected def QuantifierBound.bitraverse {G : Type → Type} [Applicative G] {α β γ δ} (f : α → G γ) (g : β → G δ) : QuantifierBound α β → G (QuantifierBound γ δ)
  | .var ann v x => (.var · v ·) <$> f ann <*> g x
  | .vars vs x => .vars <$> traverse (bitraverse f pure) vs <*> g x
  | .varTuple vs x => .varTuple <$> traverse (bitraverse f pure) vs <*> g x

instance : Bitraversable QuantifierBound where
  bitraverse := QuantifierBound.bitraverse

/-- Either a single bound variable `x`, or a tuple of them `⟨x, y, …, z⟩`.

An inductive rather than an alias for `𝒱 ⊕ List 𝒱`, for the same reason `QuantifierBound` is one.
`Expression.choose`/`.collect` instantiate this at `α × String`, and `α` is itself a datatype being
declared wherever `Expression` is nested inside one — `Parser_/Annotations.lean`'s `Annotation`
holds `Expression (List Annotation)`. Lean's nested-inductive compiler inspects constructor
argument types syntactically, and a recursive occurrence may sit under `List`/`Prod`/`Sum` or
another *inductive*, but not under a definition, whose head stays opaque; reducibility does not
help, an `abbrev` fails exactly as a `def` does ("contains a non valid occurrence of the datatypes
being declared"). This was invisible while the element type was plain `String`: no `α`, hence no
occurrence to check. -/
inductive IdentifierOrTuple (α : Type) : Type
  | var (ann : α) (x : String)
  | tuple (xs : List (α × String))
  deriving Repr, BEq, DecidableEq

/-- Independent of `α` — the empty tuple needs no annotation. -/
instance {α} : Inhabited (IdentifierOrTuple α) := ⟨.tuple []⟩

instance : Functor IdentifierOrTuple where
  map f
    | .var ann x => .var (f ann) x
    | .tuple xs => .tuple (Prod.map f id <$> xs)

instance : Traversable IdentifierOrTuple where
  traverse f
    | .var ann x => (.var · x) <$> f ann
    | .tuple xs => .tuple <$> traverse (bitraverse f pure) xs


/-- General annotations, as [supported in Apalache](https://apalache-mc.org/docs/adr/004adr-annotations.html). -/
abbrev CommentAnnotation := String × List (String ⊕ Int ⊕ Bool ⊕ String)

/--
  TLA⁺ expressions as accepted syntactically, before desugaring. The `α` parameter carries
  whatever comment-annotation payload the caller wants attached at binder sites (e.g. `@type`
  annotations).
-/
inductive Expression (α : Type) : Type
  /-- An unqualified identifier. -/
  | var : String → Expression α
  /-- An operator call `f(e₁, …, eₙ)`. -/
  | opCall : Expression α → List (Expression α) → Expression α
  | prefixCall : PrefixOperator → Expression α → Expression α
  | infixCall : Expression α → InfixOperator → Expression α → Expression α
  | postfixCall : Expression α → PostfixOperator → Expression α
  | parens : Expression α → Expression α
  /-- Bounded universal quantification `\A q \in A : e`. -/
  | bforall : List (QuantifierBound α (Expression α)) → Expression α → Expression α
  /-- Bounded existential quantification `\E q \in A : p`. -/
  | bexists : List (QuantifierBound α (Expression α)) → Expression α → Expression α
  /-- Unbounded universal quantification `\A x, y, …, z : p`. -/
  | «forall» : List String → Expression α → Expression α
  /-- Unbounded existential quantification `\E x, y, …, z : p`. -/
  | «exists» : List String → Expression α → Expression α
  /-- Temporal universal quantification `\AA x, y, …, z : p`. -/
  | fforall : List String → Expression α → Expression α
  /-- Temporal existential quantification `\EE x, y, …, z : p`. -/
  | eexists : List String → Expression α → Expression α
  /-- Hilbert's epsilon operator `CHOOSE x \in A : p`. Each bound name carries its own annotation,
  the same way `QuantifierBound` does — a binder here is as annotatable as one in `\A`/`\E`. -/
  | choose : IdentifierOrTuple α → Option (Expression α) → Expression α → Expression α
  /-- A literal set `{e₁, …, eₙ}`. -/
  | set : List (Expression α) → Expression α
  /-- Set collection/filtering `{x \in A : p}`. Bound names carry annotations, as in `choose`. -/
  | collect : IdentifierOrTuple α → Expression α → Expression α → Expression α
  /-- The image of a function by a set `{e : x \in A}`. -/
  | map' : Expression α → List (QuantifierBound α (Expression α)) → Expression α
  /-- A function call `f[e₁, …, eₙ]`. -/
  | fnCall : Expression α → List (Expression α) → Expression α
  /-- A function literal `[x \in A, …, z \in B ↦ e]`. -/
  | fn : List (QuantifierBound α (Expression α)) → Expression α → Expression α
  /-- The set of all functions from a domain to a codomain, `[A -> B]`. -/
  | fnSet : Expression α → Expression α → Expression α
  /-- A literal record `[a |-> e₁, …, z |-> eₙ]`. -/
  | record : List (α × String × Expression α) → Expression α
  /-- The set of all records whose fields are in the given sets, `[a : A, …, z : Z]`. -/
  | recordSet : List (α × String × Expression α) → Expression α
  /-- Function update `[f EXCEPT ![e₁] = e₂]`. -/
  | except : Expression α → List (List (String ⊕ List (Expression α)) × Expression α) → Expression α
  /-- Record access `r.x`. -/
  | recordAccess : Expression α → String → Expression α
  /-- A literal tuple `<<e₁, …, eₙ>>`. -/
  | tuple : List (Expression α) → Expression α
  /-- Conditional `IF e₁ THEN e₂ ELSE e₃`. -/
  | «if» : Expression α → Expression α → Expression α → Expression α
  /-- Case distinction `CASE p₁ -> e₁ [] … [] OTHER -> eₙ₊₁`. -/
  | case : List (Expression α × Expression α) → Option (Expression α) → Expression α
  /-- Conjunction list `/\ P /\ … /\ R`. -/
  | conj : List (Expression α) → Expression α
  /-- Disjunction list `\/ P \/ … \/ R`. -/
  | disj : List (Expression α) → Expression α
  | nat : String → Expression α
  | str : String → Expression α
  /-- `@`, TLA⁺'s self-reference inside `EXCEPT`. -/
  | at : Expression α
  | «true» : Expression α
  | «false» : Expression α
  /-- The stuttering-allowed action `[A]_e`. -/
  | stutter : Expression α → Expression α → Expression α
  deriving Repr, Inhabited, BEq

-- Structural recursion isn't visibly decreasing to Lean here (nested `List`/`QuantifierBound`
-- occurrences of `Expression`) — `partial` until that's revisited.
protected partial def Expression.map {α β} (f : α → β) (e : Expression α) : Expression β := match_source e with
  | .var v, pos => .var v @@ pos
  | .nat n, pos => .nat n @@ pos
  | .str s, pos => .str s @@ pos
  | .true, pos => .true @@ pos
  | .false, pos => .false @@ pos
  | .at, pos => .at @@ pos
  | .opCall v es, pos => .opCall (Expression.map f v) (Expression.map f <$> es) @@ pos
  | .prefixCall op e, pos => .prefixCall op (Expression.map f e) @@ pos
  | .infixCall e₁ op e₂, pos => .infixCall (Expression.map f e₁) op (Expression.map f e₂) @@ pos
  | .postfixCall e op, pos => .postfixCall (Expression.map f e) op @@ pos
  | .parens e, pos => .parens (Expression.map f e) @@ pos
  | .bforall qs e, pos => .bforall (bimap f (Expression.map f) <$> qs) (Expression.map f e) @@ pos
  | .bexists qs e, pos => .bexists (bimap f (Expression.map f) <$> qs) (Expression.map f e) @@ pos
  | .forall vs e, pos => .forall vs (Expression.map f e) @@ pos
  | .exists vs e, pos => .exists vs (Expression.map f e) @@ pos
  | .fforall vs e, pos => .fforall vs (Expression.map f e) @@ pos
  | .eexists vs e, pos => .eexists vs (Expression.map f e) @@ pos
  | .choose vs e₁ e₂, pos =>
    .choose (f <$> vs) (Expression.map f <$> e₁) (Expression.map f e₂) @@ pos
  | .set es, pos => .set (Expression.map f <$> es) @@ pos
  | .collect vs e₁ e₂, pos =>
    .collect (f <$> vs) (Expression.map f e₁) (Expression.map f e₂) @@ pos
  | .map' e qs, pos => .map' (Expression.map f e) (bimap f (Expression.map f) <$> qs) @@ pos
  | .fnCall e es, pos => .fnCall (Expression.map f e) (Expression.map f <$> es) @@ pos
  | .fn qs e, pos => .fn (bimap f (Expression.map f) <$> qs) (Expression.map f e) @@ pos
  | .fnSet e₁ e₂, pos => .fnSet (Expression.map f e₁) (Expression.map f e₂) @@ pos
  | .record fs, pos => .record (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
  | .recordSet fs, pos => .recordSet (Prod.map₃ f id (Expression.map f) <$> fs) @@ pos
  | .except e upds, pos => .except (Expression.map f e) (bimap (Bifunctor.snd (Expression.map f <$> ·) <$> ·) (Expression.map f) <$> upds) @@ pos
  | .recordAccess e v, pos => .recordAccess (Expression.map f e) v @@ pos
  | .tuple es, pos => .tuple (Expression.map f <$> es) @@ pos
  | .if e₁ e₂ e₃, pos => .if (Expression.map f e₁) (Expression.map f e₂) (Expression.map f e₃) @@ pos
  | .case es e, pos => .case (bimap (Expression.map f) (Expression.map f) <$> es) (Expression.map f <$> e) @@ pos
  | .conj es, pos => .conj (Expression.map f <$> es) @@ pos
  | .disj es, pos => .disj (Expression.map f <$> es) @@ pos
  | .stutter e₁ e₂, pos => .stutter (Expression.map f e₁) (Expression.map f e₂) @@ pos

instance : Functor Expression where
  map := Expression.map

local instance {F : Type → Type} [Applicative F] {α} : Inhabited (F (Expression α)) := ⟨pure .at⟩ in
protected partial def Expression.traverse {F : Type → Type} [Applicative F] {α β} (f : α → F β) (e : Expression α) : F (Expression β) := match_source e with
  | .var v, pos => pure <| .var v @@ pos
  | .nat n, pos => pure <| .nat n @@ pos
  | .str s, pos => pure <| .str s @@ pos
  | .true, pos => pure <| .true @@ pos
  | .false, pos => pure <| .false @@ pos
  | .at, pos => pure <| .at @@ pos
  | .opCall e es, pos => (.opCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
  | .prefixCall op e, pos => (.prefixCall op · @@ pos) <$> Expression.traverse f e
  | .infixCall e₁ op e₂, pos => (.infixCall · op · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .postfixCall e op, pos => (.postfixCall · op @@ pos) <$> Expression.traverse f e
  | .parens e, pos => (.parens · @@ pos) <$> Expression.traverse f e
  | .bforall qs e, pos => (.bforall · · @@ pos) <$> traverse (bitraverse f (Expression.traverse f)) qs <*> Expression.traverse f e
  | .bexists qs e, pos => (.bexists · · @@ pos) <$> traverse (bitraverse f (Expression.traverse f)) qs <*> Expression.traverse f e
  | .forall vs e, pos => (.forall vs · @@ pos) <$> Expression.traverse f e
  | .exists vs e, pos => (.exists vs · @@ pos) <$> Expression.traverse f e
  | .fforall vs e, pos => (.fforall vs · @@ pos) <$> Expression.traverse f e
  | .eexists vs e, pos => (.eexists vs · @@ pos) <$> Expression.traverse f e
  | .choose vs e₁ e₂, pos =>
    (.choose · · · @@ pos) <$> traverse f vs
      <*> traverse (Expression.traverse f) e₁ <*> Expression.traverse f e₂
  | .set es, pos => (.set · @@ pos) <$> traverse (Expression.traverse f) es
  | .collect vs e₁ e₂, pos =>
    (.collect · · · @@ pos) <$> traverse f vs
      <*> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .map' e qs, pos => (.map' · · @@ pos) <$> Expression.traverse f e <*> traverse (bitraverse f (Expression.traverse f)) qs
  | .fnCall e es, pos => (.fnCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
  | .fn qs e, pos => (.fn · · @@ pos) <$> traverse (bitraverse f (Expression.traverse f)) qs <*> Expression.traverse f e
  | .fnSet e₁ e₂, pos => (.fnSet · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
  | .record fs, pos => (.record · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
  | .recordSet fs, pos => (.recordSet · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
  | .except e upds, pos =>
    (.except · · @@ pos) <$> Expression.traverse f e
      <*> traverse (bitraverse (traverse (bitraverse pure (traverse (Expression.traverse f)))) (Expression.traverse f)) upds
  | .recordAccess e v, pos => (.recordAccess · v @@ pos) <$> Expression.traverse f e
  | .tuple es, pos => (.tuple · @@ pos) <$> traverse (Expression.traverse f) es
  | .if e₁ e₂ e₃, pos => (.if · · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂ <*> Expression.traverse f e₃
  | .case es e, pos => (.case · · @@ pos) <$> traverse (bitraverse (Expression.traverse f) (Expression.traverse f)) es <*> traverse (Expression.traverse f) e
  | .conj es, pos => (.conj · @@ pos) <$> traverse (Expression.traverse f) es
  | .disj es, pos => (.disj · @@ pos) <$> traverse (Expression.traverse f) es
  | .stutter e₁ e₂, pos => (.stutter · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂

instance : Traversable Expression where
  traverse := Expression.traverse

instance instTraversableProd {α : Type} : Traversable (Prod α) where
  traverse f x := ({x with snd := ·}) <$> f x.snd

/-- A top-level TLA⁺ declaration. `RECURSIVE` and module `INSTANCE` are not represented. -/
abbrev Declaration := _root_.Declaration Expression

/--
  A parsed TLA⁺ module, `EXTENDS`-list and all, wrapping the embedded (Distributed) PlusCal
  algorithm at whatever `α` the caller instantiates it at — kept abstract to avoid a cyclic
  import between the two Core ASTs.
-/
abbrev Module := _root_.Module Expression

namespace Module
export _root_.Module (mk)
end Module

end SurfaceTLAPlus

end
