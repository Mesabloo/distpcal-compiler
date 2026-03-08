import Common.Position
-- import PlusCalCompiler.SurfaceTLAPlus.Tokens
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Functor
import Mathlib.Logic.Function.Defs
import Extra.Prod

namespace SurfaceTLAPlus
  /-!
    `Fin _` parameters in operators are used to describe alternative syntaxes, given in order in the documentation
    for each operator.
  -/

  /--
    The entire set of prefix operators reserved in TLA⁺.
  -/
  inductive PrefixOperator : Type
    /-- `-` -/
    | «-»
    /-- `¬`: `\neg` or `\lnot` or `~` -/
    | «\neg » (_ : Fin 3)
    /-- `□`: `[]` -/
    | «[]»
    /-- `◇`: `<>` -/
    | «<>»
    /-- `DOMAIN` -/
    | «DOMAIN»
    /-- `ENABLED` -/
    | «ENABLED»
    /-- `SUBSET` -/
    | «SUBSET»
    /-- `UNCHANGED` -/
    | «UNCHANGED»
    /-- `UNION` -/
    | «UNION»
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

  /--
    The entire set of postfix operators reserved in TLA⁺.
  -/
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

  /--
    The entire set of infix operators reserved in TLA⁺.
  -/
  inductive InfixOperator : Type
    /-- `!!` -/
    | «!!»
    /-- `##` -/
    | «##»
    /-- `$$` -/
    | «$$»
    /-- `$` -/
    | «$»
    /-- `%%` -/
    | «%%»
    /-- `%` -/
    | «%»
    /-- `&&` -/
    | «&&»
    /-- `&` -/
    | «&»
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
      `×`: `\X` or `\times`

      ⚠ Not actually a binary operator in the grammar, but treated as such for simplicity.
    -/
    | «\X » (_ : Fin 2)
    /-- `**` -/
    | «**»
    /-- `*` -/
    | «*»
    /-- `++` -/
    | «++»
    /-- `+` -/
    | «+»
    /-- `-+->` -/
    | «-+->»
    /-- `--` -/
    | «--»
    /-- `⊣`: `-|` -/
    | «-|»
    /-- `-` -/
    | «-»
    /-- `...` -/
    | «...»
    /-- `..` -/
    | «..»
    /-- `.` -/
    | «.»
    /-- `//` -/
    | «//»
    /-- `≠`: `/=` or `#` -/
    | «/= » (_ : Fin 2)
    /-- `∧`: `/\` or `\land` -/
    | «/\ » (_ : Fin 2)
    /-- `/` -/
    | «/»
    /-- `⩴`: `::=` -/
    | «::=»
    /-- `≔`: `:=` -/
    | «:=»
    /-- `:>` -/
    | «:>»
    /-- `<:` -/
    | «<:»
    /-- `≡`: `<=>` or `\equiv` -/
    | «<=> » (_ : Fin 2)
    /-- `≤`: `=<` or `<=` or `\leq` -/
    | «=< » (_ : Fin 3)
    /-- `⇒`: `=>` -/
    | «=>»
    /-- `⫤`: `=|` -/
    | «=|»
    /-- `<` -/
    | «<»
    /-- `=` -/
    | «=»
    /-- `≥`: `>=` or `\geq` -/
    | «>= » (_ : Fin 2)
    /-- `>` -/
    | «>»
    /-- `??` -/
    | «??»
    /-- `?` -/
    | «?»
    /-- `@@` -/
    | «@@»
    /-- `∨`: `\/` or `\lor` -/
    | «\/ » (_ : Fin 2)
    /-- `^^` -/
    | «^^»
    /-- `^` -/
    | «^»
    /-- `⊢`: `|-` -/
    | «|-»
    /-- `⊨`: `|=` -/
    | «|=»
    /-- `‖`: `||` -/
    | «||»
    /-- `|` -/
    | «|»
    /-- `⤳`: `~>` -/
    | «~>»
    -- LaTeX notations
    /-- `≈`: `\approx` -/
    | «\approx»
    /-- `⊒`: `\sqsupseteq` -/
    | «\sqsupseteq»
    /-- `≍`: `\asymp` -/
    | «\asymp»
    /-- `≫`: `\gg` -/
    | «\gg»
    /-- `⋆`: `\star` -/
    | «\star»
    /-- `◯` : `\bigcirc` -/
    | «\bigcirc»
    /-- `∈`: `\in` -/
    | «\in»
    /-- `≼`: `\preceq` -/
    | «\preceq»
    /-- `≺`: `\prec` -/
    | «\prec»
    /-- `⊆`: `\subseteq` -/
    | «\subseteq»
    /-- `⊂`: `\subset` -/
    | «\subset»
    /-- `•`: `\bullet` -/
    | «\bullet»
    /-- `∩`: `\cap` or `\intersect` -/
    | «\cap » (_ : Fin 2)
    /-- `∝`: `\propto` -/
    | «\propto»
    /-- `≽`: `\succeq` -/
    | «\succeq»
    /-- `≻`: `\succ` -/
    | «\succ»
    /-- `⬝`: `\cdot` -/
    | «\cdot»
    /-- `≃`: `\simeq` -/
    | «\simeq»
    /-- `∼`: `\sim` -/
    | «\sim»
    /-- `≪`: `\ll` -/
    | «\ll»
    /-- `⊇`: `\supseteq` -/
    | «\supseteq»
    /-- `⊃`: `\supset` -/
    | «\supset»
    /-- `≅`: `\cong` -/
    | «\cong»
    /-- `⊓`: `\sqcap` -/
    | «\sqcap»
    /-- `∪`: `\cup` or `\union` -/
    | «\cup » (_ : Fin 2)
    /-- `∘`: `\o` or `\circ` -/
    | «\o » (_ : Fin 2)
    /-- `⊔`: `\sqcup` -/
    | «\sqcup»
    /-- `÷`: `\div` -/
    | «\div»
    /-- `⊑`: `\sqsubseteq` -/
    | «\sqsubseteq»
    /-- `⊏`: `\sqsubset` -/
    | «\sqsubset»
    /-- `⊎`: `\uplus` -/
    | «\uplus»
    /-- `≐`: `\doteq` -/
    | «\doteq»
    /-- `≀`: `\wr` -/
    | «\wr»
    /-- `⊐`: `\sqsupset` -/
    | «\sqsupset»
    /-- `∉`: `\notin` -/
    | «\notin»
    /-- `\`: `\` -/
    | «\»
    deriving BEq, Repr, Inhabited

  set_option maxHeartbeats 400000 in
  instance : DecidableEq InfixOperator := λ o₁ o₂ ↦ by
    cases o₁ <;> cases o₂ <;> solve
      | exact isTrue rfl
      | exact isFalse λ _ ↦ by contradiction
      | rename_i x y
        by_cases h : x = y
        · subst x; exact isTrue rfl
        · exact isFalse λ _ ↦ by injections; contradiction
  -- deriving instance DecidableEq for InfixOperator

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
      | .«!!» => "!!"
      | .«##» => "##"
      | .«$$» => "$$"
      | .«$» => "$"
      | .«%%» => "%%"
      | .«%» => "%"
      | .«&&» => "&&"
      | .«&» => "&"
      | .«(+)» => "(+)"
      | .«\oplus» => r"\oplus"
      | .«(-)» => "(-)"
      | .«\ominus» => r"\ominus"
      | .«(.)» => "(.)"
      | .«\odot» => r"\odot"
      | .«(/)» => "(/)"
      | .«\oslash» => r"\oslash"
      | .«(\X)» => r"(\X)"
      | .«\otimes» => r"\otimes"
      | .«\X» => r"\X"
      | .«\times» => r"\times"
      | .«**» => "**"
      | .«*» => "*"
      | .«++» => "++"
      | .«+» => "+"
      | .«-+->» => "-+->"
      | .«--» => "--"
      | .«-|» => "-|"
      | .«-» => "-"
      | .«...» => "..."
      | .«..» => ".."
      | .«.» => "."
      | .«//» => "//"
      | .«/=» => "/="
      | .«#» => "#"
      | .«/\» => r"/\" -- "
      | .«\land» => r"\land"
      | .«/» => "/"
      | .«::=» => "::="
      | .«:=» => ":="
      | .«:>» => ":>"
      | .«<:» => "<:"
      | .«<=>» => "<=>"
      | .«\equiv» => r"\equiv"
      | .«=<» => "=<"
      | .«<=» => "<="
      | .«\leq» => r"\leq"
      | .«=>» => "=>"
      | .«=|» => "=|"
      | .«<» => "<"
      | .«=» => "="
      | .«>=» => ">="
      | .«\geq» => r"\geq"
      | .«>» => ">"
      | .«?» => "?"
      | .«??» => "??"
      | .«@@» => "@@"
      | .«\/» => r"\/"
      | .«\lor» => r"\lor"
      | .«^^» => "^^"
      | .«^» => "^"
      | .«|-» => "|-"
      | .«|=» => "|="
      | .«||» => "||"
      | .«|» => "|"
      | .«~>» => "~>"
      | .«\approx» => r"\approx"
      | .«\sqsupseteq» => r"\sqsupseteq"
      | .«\asymp» => r"\asymp"
      | .«\gg» => r"\gg"
      | .«\star» => r"\star"
      | .«\bigcirc» => r"\bigcirc"
      | .«\in» => r"\in"
      | .«\preceq» => r"\preceq"
      | .«\prec» => r"\prec"
      | .«\subseteq» => r"\subseteq"
      | .«\subset» => r"\subset"
      | .«\bullet» => r"\bullet"
      | .«\cap» => r"\cap"
      | .«\intersect» => r"\intersect"
      | .«\propto» => r"\propto"
      | .«\succeq» => r"\succeq"
      | .«\succ» => r"\succ"
      | .«\cdot» => r"\cdot"
      | .«\simeq» => r"\simeq"
      | .«\sim» => r"\sim"
      | .«\ll» => r"\ll"
      | .«\supseteq» => r"\supseteq"
      | .«\supset» => r"\supset"
      | .«\cong» => r"\cong"
      | .«\sqcap» => r"\sqcap"
      | .«\cup» => r"\cup"
      | .«\union» => r"\union"
      | .«\o» => r"\o"
      | .«\circ» => r"\circ"
      | .«\sqcup» => r"\sqcup"
      | .«\div» => r"\div"
      | .«\sqsubseteq» => r"\sqsubseteq"
      | .«\sqsubset» => r"\sqsubset"
      | .«\uplus» => r"\uplus"
      | .«\doteq» => r"\doteq"
      | .«\wr» => r"\wr"
      | .«\sqsupset» => r"\sqsupset"
      | .«\notin» => r"\notin"
      | .«\» => r"\" -- "

  /-- TLA⁺ types, in the [same format as Apalache](https://apalache-mc.org/docs/adr/002adr-types.html). -/
  inductive Typ.{u} : Type u
    /-- `Bool` -/
    | bool
    /-- `Int` -/
    | int
    /-- `Str` -/
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
    /-- `a` -/
    | var (_ : String)
    /-- `CONST` -/
    | const (_ : String)
    -- polyrecord/polyvariants? https://apalache-mc.org/docs/adr/002adr-types.html#ts12
    | record (_ : List (String × Typ))
    --------------------
    -- Distributed PlusCal specific types
    /-- `Channel(τ)` -/
    | channel (_ : Typ)
    /-- `Address` -/
    | address
    deriving Repr, Inhabited, BEq

  partial instance : DecidableEq Typ :=
    let rec go (τ τ' : Typ) : Decidable (τ = τ') := match τ, τ' with
      -- Decide equality there
      | .bool, .bool | .int, .int | .str, .str => isTrue rfl
      | .function dom rng, .function dom' rng' =>
        match go dom dom', go rng rng' with
        | .isTrue h₁, .isTrue h₂ => isTrue (by rw [h₁, h₂])
        | .isTrue h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
        | .isFalse h₁, .isTrue h₂ => isFalse λ h' ↦ by injections; contradiction
        | .isFalse h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
      | .set τ, .set τ' | .seq τ, .seq τ' | .channel τ, .channel τ' =>
        match go τ τ' with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      | .tuple τs, .tuple τs' =>
        match @List.hasDecEq _ go τs τs' with
        | .isTrue h => isTrue (by rw [h])
        | .isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      | .operator τs τ, .operator τs' τ' =>
        match @List.hasDecEq _ go τs τs', go τ τ' with
        | .isTrue h₁, .isTrue h₂ => isTrue (by rw [h₁, h₂])
        | .isTrue h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; absurd h₁; trivial
        | .isFalse h₁, .isTrue h₂ => isFalse λ h' ↦ by injections; absurd h₁; trivial
        | .isFalse h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; absurd h₁; trivial
      | .var v, .var v' | .const v, .const v' =>
        if h : v = v' then
          isTrue (by rw [h])
        else
          isFalse λ h' ↦ by injections; absurd h; trivial
      | .record fs, .record fs' =>
        let Prod.hasDecEq {α β : Type _} [DecidableEq α] [DecidableEq β] : DecidableEq (α × β) := inferInstance

        match @List.hasDecEq _ (@Prod.hasDecEq _ _ inferInstance go) fs fs' with
        | .isTrue h => isTrue (by rw [h])
        | .isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      | .address, .address => isTrue rfl
      -- Other shit cases that need to be explicitly defined, unfortunately
      | .bool, .int | .bool, .str | .bool, .function .. | .bool, .set .. | .bool, .seq .. | .bool, .channel ..
      | .bool, .tuple .. | .bool, .operator .. | .bool, .var .. | .bool, .const .. | .bool, .record .. | .bool, .address => isFalse nofun
      | .int, .bool | .int, .str | .int, .function .. | .int, .set .. | .int, .seq .. | .int, .channel ..
      | .int, .tuple .. | .int, .operator .. | .int, .var .. | .int, .const .. | .int, .record .. | .int, .address => isFalse nofun
      | .str, .bool | .str, .int | .str, .function .. | .str, .set .. | .str, .seq .. | .str, .channel ..
      | .str, .tuple .. | .str, .operator .. | .str, .var .. | .str, .const .. | .str, .record .. | .str, .address => isFalse nofun
      | .function .., .bool | .function .., .int | .function .., .str | .function .., .set .. | .function .., .seq ..
      | .function .., .channel .. | .function .., .tuple .. | .function .., .operator .. | .function .., .var ..
      | .function .., .const .. | .function .., .record .. | .function .., .address => isFalse nofun
      | .set .., .bool | .set .., .int | .set .., .str | .set .., .function .. | .set .., .seq ..
      | .set .., .channel .. | .set .., .tuple .. | .set .., .operator .. | .set .., .var ..
      | .set .., .const .. | .set .., .record .. | .set .., .address => isFalse nofun
      | .seq .., .bool | .seq .., .int | .seq .., .str | .seq .., .function .. | .seq .., .set ..
      | .seq .., .channel .. | .seq .., .tuple .. | .seq .., .operator .. | .seq .., .var ..
      | .seq .., .const .. | .seq .., .record .. | .seq .., .address => isFalse nofun
      | .channel .., .bool | .channel .., .int | .channel .., .str | .channel .., .function .. | .channel .., .set ..
      | .channel .., .seq .. | .channel .., .tuple .. | .channel .., .operator .. | .channel .., .var ..
      | .channel .., .const .. | .channel .., .record .. | .channel .., .address => isFalse nofun
      | .tuple .., .bool | .tuple .., .int | .tuple .., .str | .tuple .., .function .. | .tuple .., .set ..
      | .tuple .., .seq .. | .tuple .., .channel .. | .tuple .., .operator .. | .tuple .., .var ..
      | .tuple .., .const .. | .tuple .., .record .. | .tuple .., .address => isFalse nofun
      | .operator .., .bool | .operator .., .int | .operator .., .str | .operator .., .function .. | .operator .., .set ..
      | .operator .., .seq .. | .operator .., .channel .. | .operator .., .tuple .. | .operator .., .var ..
      | .operator .., .const .. | .operator .., .record .. | .operator .., .address => isFalse nofun
      | .var .., .bool | .var .., .int | .var .., .str | .var .., .function .. | .var .., .set ..
      | .var .., .seq .. | .var .., .channel .. | .var .., .tuple .. | .var .., .operator ..
      | .var .., .const .. | .var .., .record .. | .var .., .address => isFalse nofun
      | .const .., .bool | .const .., .int | .const .., .str | .const .., .function .. | .const .., .set ..
      | .const .., .seq .. | .const .., .channel .. | .const .., .tuple .. | .const .., .operator ..
      | .const .., .var .. | .const .., .record .. | .const .., .address => isFalse nofun
      | .record .., .bool | .record .., .int | .record .., .str | .record .., .function .. | .record .., .set ..
      | .record .., .seq .. | .record .., .channel .. | .record .., .tuple .. | .record .., .operator ..
      | .record .., .var .. | .record .., .const .. | .record .., .address => isFalse nofun
      | .address, .bool | .address, .int | .address, .str | .address, .function .. | .address, .set ..
      | .address, .seq .. | .address, .channel .. | .address, .tuple .. | .address, .operator ..
      | .address, .var .. | .address, .const .. | .address, .record .. => isFalse nofun
    go

  partial instance : ToString Typ where
    toString :=
      let rec go : Typ → String
        | .bool => "Bool"
        | .int => "Int"
        | .str => "Str"
        | .address => "Address"
        | .function τ₁ τ₂ => s!"({go τ₁}) -> {go τ₂}"
        | .set τ => s!"Set({go τ})"
        | .seq τ => s!"Seq({go τ})"
        | .tuple τs => s!"<<{String.intercalate ", " (τs.map go)}>>"
        | .operator τs τ => s!"({String.intercalate ", " (τs.map go)}) => {go τ}"
        | .var v => v
        | .const v => v
        | .record fs => "{" ++ String.intercalate ", " (fs.map λ ⟨v, τ⟩ ↦ v ++ " : " ++ go τ) ++ "}"
        | .channel τ => s!"Channel({go τ})"
      go

  /- TLA+: https://lamport.azurewebsites.net/tla/TLAPlus2Grammar.tla -/
  /- See also page 268 of the book "Specifying Systems". -/

  /--
    Represents groups of variables bound in quantifiers (e.g. `\A`).
  -/
  inductive QuantifierBound (α β : Type) : Type
    /-- `x ∈ A` -/
    | var : α → String → β → QuantifierBound α β
    /-- `⟨x, y, ⋯, z⟩ ∈ A` -/
    | varTuple : List (α × String) → β → QuantifierBound α β
    /-- `x, y, ⋯, z ∈ A` -/
    | vars : List (α × String) → β → QuantifierBound α β
    deriving Repr, DecidableEq, BEq

  protected def QuantifierBound.bimap {α β γ δ : Type _} (f : α → γ) (g : β → δ) : QuantifierBound α β → QuantifierBound γ δ
    | .var anns v x => .var (f anns) v (g x)
    | .vars vs x => .vars (Bifunctor.fst f <$> vs) (g x)
    | .varTuple vs x => .varTuple (Bifunctor.fst f <$> vs) (g x)

  instance : Bifunctor QuantifierBound where
    bimap := QuantifierBound.bimap

  protected def QuantifierBound.bitraverse {G : Type _ → Type _} [Applicative G] {α β γ δ} (f : α → G γ) (g : β → G δ) : QuantifierBound α β → G (QuantifierBound γ δ)
    | .var anns v x => (.var · v ·) <$> f anns <*> g x
    | .vars vs x => .vars <$> traverse (bitraverse f pure) vs <*> g x
    | .varTuple vs x => .varTuple <$> traverse (bitraverse f pure) vs <*> g x

  instance : Bitraversable QuantifierBound where
    bitraverse := QuantifierBound.bitraverse

  /--
    This type represents either a single variable `x` or a tuple of variables `⟨x, y, …, z⟩`.
  -/
  def IdentifierOrTuple (𝒱 : Type _) := 𝒱 ⊕ List 𝒱

  instance {𝒱} [Repr 𝒱] : Repr (IdentifierOrTuple 𝒱) := inferInstanceAs (Repr (_ ⊕ _))

  instance {𝒱} [DecidableEq 𝒱] : DecidableEq (IdentifierOrTuple 𝒱) := inferInstanceAs (DecidableEq (_ ⊕ _))

  instance : Functor IdentifierOrTuple where
    map f
      | .inl x => .inl (f x)
      | .inr xs => .inr (f <$> xs)

  instance : Traversable IdentifierOrTuple where
    traverse f
      | .inl x => .inl <$> f x
      | .inr xs => .inr <$> traverse f xs

  /--
    General annotations, as [supported in Apalache](https://apalache-mc.org/docs/adr/004adr-annotations.html).
  -/
  abbrev CommentAnnotation := String × List (String ⊕ Int ⊕ Bool ⊕ String)

  -- TODO: support qualified identifiers and operators

  /--
    The inductive type describing TLA⁺ expressions as accepted syntactically.

    The `α` parameter is used to make the type of comment annotations generic.
  -/
  inductive Expression (α : Type) : Type
    /-- A TLA+ (unqualified) identifier. -/
    | var : String → Expression α
    /-- An operator call `f(e₁, …, eₙ)`. -/
    | opCall : Expression α → List (Expression α) → Expression α
    /-- A prefix operator call. -/
    | prefixCall : PrefixOperator → Expression α → Expression α
    /-- An infix operator call. -/
    | infixCall : Expression α → InfixOperator → Expression α → Expression α
    /-- A postfix operator call. -/
    | postfixCall : Expression α → PostfixOperator → Expression α
    /-- A simple parenthesized expression. -/
    | parens : Expression α → Expression α
    /-- Bounded universal quantification `\A q \in A : e`. -/
    | bforall : List (QuantifierBound α (Expression α)) → Expression α → Expression α
    /-- Bounded existential quantification `\E q \in A : p`. -/
    | bexists : List (QuantifierBound α (Expression α)) → Expression α → Expression α
    /-- Unbounded universal quantification `\A x, y, …, z : p`. -/
    | forall : List String → Expression α → Expression α
    /-- Unbounded existential quantification `\E x, y, …, z : p`. -/
    | exists : List String → Expression α → Expression α
    /-- Temporal universal quantification `\AA x, y, …, z : p`. -/
    | fforall : List String → Expression α → Expression α
    /-- Temporal existential quantification `\EE x, y, …, z : p`. -/
    | eexists : List String → Expression α → Expression α
    /-- Hilbert's epsilon operator `CHOOSE x \in A : p`. -/
    | choose : IdentifierOrTuple String → Option (Expression α) → Expression α → Expression α
    /-- A literal set `{e₁, …, eₙ}`. -/
    | set : List (Expression α) → Expression α
    /-- Set collection/filtering `{x \in A : p}`. -/
    | collect : IdentifierOrTuple String → Expression α → Expression α → Expression α
    /-- The image of a function by a set `{e : x \in A}`. -/
    | map' : Expression α → List (QuantifierBound α (Expression α)) → Expression α
    /-- A function call `f[e₁, …, eₙ]`. -/
    | fnCall : Expression α → List (Expression α) → Expression α
    /-- A function literal `[x \in A, …, z \in B ↦ e]`. -/
    | fn : List (QuantifierBound α (Expression α)) → Expression α → Expression α
    /-- The set of all functions from a given domain to a given codomain `[A -> B]`. -/
    | fnSet : Expression α → Expression α → Expression α
    /-- The literal record `[a |-> e₁, …, z |-> eₙ]`. -/
    | record : List (α × String × Expression α) → Expression α
    /-- The set of all records whose fields are in the given sets `[a : A, …, z : Z]`. -/
    | recordSet : List (α × String × Expression α) → Expression α
    /-- Function update `[f EXCEPT ![e₁] = e₂]`. -/
    | except : Expression α → List (List (String ⊕ List (Expression α)) × Expression α) → Expression α
    /-- Record access `r.x`. -/
    | recordAccess : Expression α → String → Expression α
    /-- A literal tuple `<<e₁, …, eₙ>>`. -/
    | tuple : List (Expression α) → Expression α
    /-- Conditional expression `IF e₁ THEN e₂ ELSE e₃`. -/
    | if : Expression α → Expression α → Expression α → Expression α
    /-- Case distinction `CASE p₁ -> e₁ [] … [] OTHER -> eₙ₊₁`. -/
    | case : List (Expression α × Expression α) → Option (Expression α) → Expression α
    -- TODO: to be able to define `LET`, we need to make `Expression` mutual with `Declaration`…
    /-- Conjunction `P /\ … /\ R`. -/
    | conj : List (Expression α) → Expression α
    /-- Disjunction `P \/ … \/ R`. -/
    | disj : List (Expression α) → Expression α
    /-- A natural number. -/
    | nat : String → Expression α
    /-- A literal string. -/
    | str : String → Expression α
    /-- `@` -/
    | at : Expression α
    /-- `[A]_e` -/
    | stutter : Expression α → Expression α → Expression α
    -- WF_ / SF_
    -- TODO: other temporal and action operators
    -- TODO: module instances
    deriving Repr, Inhabited, BEq

  -- TODO: prove termination, at some point
  protected partial def Expression.map {α β} (f : α → β) (e : Expression α) : Expression β := match_source e with
    | .var v, pos => .var v @@ pos
    | .nat n, pos => .nat n @@ pos
    | .str s, pos => .str s @@ pos
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
    | .choose vs e₁ e₂, pos => .choose vs (Expression.map f <$> e₁) (Expression.map f e₂) @@ pos
    | .set es, pos => .set (Expression.map f <$> es) @@ pos
    | .collect vs e₁ e₂, pos => .collect vs (Expression.map f e₁) (Expression.map f e₂) @@ pos
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

  local instance {F : Type _ → Type _} [Applicative F] {α} : Inhabited (F (Expression α)) := ⟨pure .at⟩ in
  -- TODO: prove termination at some point
  protected partial def Expression.traverse {F : Type _ → Type _} [Applicative F] {α β} (f : α → F β) (e : Expression α) : F (Expression β) := match_source e with
    | .var v, pos => pure <| .var v @@ pos
    | .nat n, pos => pure <| .nat n @@ pos
    | .str s, pos => pure <| .str s @@ pos
    | .at, pos => pure <| .at @@ pos
    | .opCall e es, pos =>
      (.opCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
    | .prefixCall op e, pos => (.prefixCall op · @@ pos) <$> Expression.traverse f e
    | .infixCall e₁ op e₂, pos =>
      (.infixCall · op · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
    | .postfixCall e op, pos => (.postfixCall · op @@ pos) <$> Expression.traverse f e
    | .parens e, pos => (.parens · @@ pos) <$> Expression.traverse f e
    | .bforall qs e, pos =>
      (.bforall · · @@ pos)
        <$> traverse (bitraverse f (Expression.traverse f)) qs
        <*> Expression.traverse f e
    | .bexists qs e, pos =>
      (.bexists · · @@ pos)
        <$> traverse (bitraverse f (Expression.traverse f)) qs
        <*> Expression.traverse f e
    | .forall vs e, pos => (.forall vs · @@ pos) <$> Expression.traverse f e
    | .exists vs e, pos => (.exists vs · @@ pos) <$> Expression.traverse f e
    | .fforall vs e, pos => (.fforall vs · @@ pos) <$> Expression.traverse f e
    | .eexists vs e, pos => (.eexists vs · @@ pos) <$> Expression.traverse f e
    | .choose vs e₁ e₂, pos =>
      (.choose vs · · @@ pos) <$> traverse (Expression.traverse f) e₁ <*> Expression.traverse f e₂
    | .set es, pos => (.set · @@ pos) <$> traverse (Expression.traverse f) es
    | .collect vs e₁ e₂, pos =>
      (.collect vs · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
    | .map' e qs, pos =>
      (.map' · · @@ pos) <$> Expression.traverse f e <*> traverse (bitraverse f (Expression.traverse f)) qs
    | .fnCall e es, pos =>
      (.fnCall · · @@ pos) <$> Expression.traverse f e <*> traverse (Expression.traverse f) es
    | .fn qs e, pos =>
      (.fn · · @@ pos)
        <$> traverse (bitraverse f (Expression.traverse f)) qs
        <*> Expression.traverse f e
    | .fnSet e₁ e₂, pos =>
      (.fnSet · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂
    | .record fs, pos =>
      (.record · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
    | .recordSet fs, pos =>
      (.recordSet · @@ pos) <$> traverse (Prod.traverse₃ f pure (Expression.traverse f)) fs
    | .except e upds, pos =>
      (.except · · @@ pos)
        <$> Expression.traverse f e
        <*> traverse (bitraverse (traverse (bitraverse pure (traverse (Expression.traverse f)))) (Expression.traverse f)) upds
    | .recordAccess e v, pos => (.recordAccess · v @@ pos) <$> Expression.traverse f e
    | .tuple es, pos => (.tuple · @@ pos) <$> traverse (Expression.traverse f) es
    | .if e₁ e₂ e₃, pos =>
      (.if · · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂ <*> Expression.traverse f e₃
    | .case es e, pos =>
      (.case · · @@ pos)
        <$> traverse (bitraverse (Expression.traverse f) (Expression.traverse f)) es
        <*> traverse (Expression.traverse f) e
    | .conj es, pos => (.conj · @@ pos) <$> traverse (Expression.traverse f) es
    | .disj es, pos => (.disj · @@ pos) <$> traverse (Expression.traverse f) es
    | .stutter e₁ e₂, pos =>
      (.stutter · · @@ pos) <$> Expression.traverse f e₁ <*> Expression.traverse f e₂

  instance : Traversable Expression where
    traverse := Expression.traverse

  instance instTraversableProd.{u} {α : Type u} : Traversable (Prod.{u, u} α) where
    traverse f x := ({x with snd := ·}) <$> f x.snd

  -- TODO: support distfix heads for operator definitions
  -- (keep in mind that to define the prefix `-`, one has to write `-. _ == _`, not `- _ == _`, somehow)

  inductive Declaration (α : Type) : Type
    | constants : List (String × α) → Declaration α
    | «variables» : List (String × α) → Declaration α
    | assume : Expression α → Declaration α
    /--
      An operator definition with optionally higher-order arguments.
      The `Nat` value associated to each parameter denotes its number of parameters (e.g. 0 for `x`, 3 for `F(_, _, _)`, …).
    -/
    | operator : α → String → List (String × Nat) → Expression α → Declaration α
    /-- A function definition given a domain for all its arguments. -/
    | function : α → String → List (String × Expression α) → Expression α → Declaration α
    deriving Repr

  instance : Functor Declaration where
    map f
      | .constants xs => .constants (Bifunctor.snd f <$> xs)
      | .variables xs => .variables (Bifunctor.snd f <$> xs)
      | .assume e => .assume (f <$> e)
      | .operator a x args e => .operator (f a) x args (f <$> e)
      | .function a x args e => .function (f a) x (Bifunctor.snd (f <$> ·) <$> args) (f <$> e)

  instance : Traversable Declaration where
    traverse f
      | .constants xs => .constants <$> traverse (bitraverse pure f) xs
      | .variables xs => .variables <$> traverse (bitraverse pure f) xs
      | .assume e => .assume <$> traverse f e
      | .operator a x args e => (.operator · x args ·) <$> f a <*> traverse f e
      | .function a x args e => (.function · x · ·) <$> f a <*> traverse (bitraverse pure (traverse f)) args <*> traverse f e

  structure Module (α β : Type _) : Type _ where
    name : String
    «extends» : List String
    declarations₁ : List (Declaration β)
    pcalAlgorithm : Option α -- (SurfacePlusCal.Algorithm Expr)
    declarations₂ : List (Declaration β)
    deriving Repr

  instance : Bifunctor Module where
    bimap f g m := {m with
      declarations₁ := (g <$> ·) <$> m.declarations₁
      pcalAlgorithm := f <$> m.pcalAlgorithm
      declarations₂ := (g <$> ·) <$> m.declarations₂
    }

  instance : Bitraversable Module where
    bitraverse f g m :=
      ({m with declarations₁ := ·, pcalAlgorithm := ·, declarations₂ := ·})
        <$> traverse (traverse g) m.declarations₁
        <*> traverse f m.pcalAlgorithm
        <*> traverse (traverse g) m.declarations₂
end SurfaceTLAPlus
