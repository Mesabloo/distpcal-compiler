import CustomPrelude
import Mathlib.Data.String.Defs

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
    deriving BEq, Repr, DecidableEq

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
    deriving BEq, Repr, DecidableEq

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
    deriving BEq, Repr

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

  /--
    The type of all syntactical tokens of the TLA⁺ language.
    This contains all unicode variations as well as LaTeX-like codes.

    `α` abstracts away the type of PlusCal tokens.
  -/
  inductive Token (α : Type _) : Type _
    | module
    | «extends»
    | «constant»
    | «constants»
    | «variable»
    | «variables»
    | «if»
    | «then»
    | «else»
    | assume
    | except
    | «let»
    | «in»
    | case
    | choose
    | «instance»
    | other
    | «with»
    /-- Left and right parenthesis `(` `)`. -/
    | paren (isLeft : Bool)
    /-- Left and right curly braces `{` `}`. -/
    | brace (isLeft : Bool)
    /-- Left and right square brackets `[` `]`. -/
    | bracket (isLeft : Bool)
    | «]_»
    | «>>_»
    /-- Operator definition operator `==` `≜`. -/
    | eqeq (isUnicode : Bool)
    | comma
    | underscore
    | colon
    | «prefix» (_ : PrefixOperator)
    | «infix» (_ : InfixOperator)
    | «postfix» (_ : PostfixOperator)
    | «\A»
    | «\E»
    | «|->»
    | «->»
    | bang
    | at
    /-- `<<` `>>`. -/
    | angle (isLeft : Bool)
    /-- The delimiter `----` with at least 4 dashes. -/
    | moduleStart (len : Nat)
    /-- The delimiter `====` with at least 4 equal signs. -/
    | moduleEnd (len : Nat)
    /-- A basic TLA⁺ identifier which is not a reserved word. -/
    | identifier (name : String)
    /-- An inline comment starting with `\*`. -/
    | inlineComment (content : String)
    /-- A multiline comment starting with `(*` and ending with `*)`. -/
    | blockComment (content : String)
    | number (repr : String)
    | string (repr : String)
    /-- The tokens of a PlusCal algorithm. -/
    | pcal (_ : List α)
    deriving Repr, Inhabited, BEq

  abbrev Token.lparen {α} : Token α := .paren true
  abbrev Token.rparen {α} : Token α := .paren false
  abbrev Token.lbrace {α} : Token α := .brace true
  abbrev Token.rbrace {α} : Token α := .brace false
  abbrev Token.lbracket {α} : Token α := .bracket true
  abbrev Token.rbracket {α} : Token α := .bracket false
  abbrev Token.langle {α} : Token α := .angle true
  abbrev Token.rangle {α} : Token α := .angle false

  instance {α} [ToString α] : ToString (Token α) where
    toString
      | .module => "keyword 'MODULE'"
      | .extends => "keyword 'EXTENDS'"
      | .constant => "keyword 'CONSTANT'"
      | .constants => "keyword 'CONSTANTS'"
      | .variable => "keyword 'VARIABLE'"
      | .variables => "keyword 'VARIABLES'"
      | .if => "keyword 'IF'"
      | .then => "keyword 'THEN'"
      | .else => "keyword 'ELSE'"
      | .assume => "keyword 'ASSUME'"
      | .except => "keyword 'EXCEPT'"
      | .with => "keyword 'WITH'"
      | .other => "keyword 'OTHER'"
      | .instance => "keyword 'INSTANCE'"
      | .case => "keyword 'CASE'"
      | .choose => "keyword 'CHOOSE'"
      | .in => "keyword 'IN'"
      | .let => "keyword 'LET'"
      | .lparen => "symbol '('"
      | .rparen => "symbol ')'"
      | .lbrace => "symbol '{'"
      | .rbrace => "symbol '}'"
      | .lbracket => "symbol '['"
      | .rbracket => "symbol ']'"
      | .«]_» => "symbol ']_'"
      | .«>>_» => "symbol '>>_'"
      | .eqeq _ => "symbol '=='"
      | .comma => "symbol ','"
      | .underscore => "symbol '_'"
      | .colon => "symbol ':'"
      | .prefix op => s!"prefix operator '{op}'"
      | .infix op => s!"infix operator '{op}'"
      | .postfix op => s!"postfix operator '{op}'"
      | .«\A» => r"symbol '\A'"
      | .«\E» => r"symbol '\E'"
      | .«|->» => r"symbol '|->'"
      | .«->» => r"symbol '->'"
      | .bang => "symbol '!'"
      | .at => "symbol '@'"
      | .langle => "symbol '<<'"
      | .rangle => "symbol '>>'"
      | .moduleStart len => s!"symbol '{String.replicate (len + 4) '-'}'"
      | .moduleEnd len => s!"symbol '{String.replicate (len + 4) '='}'"
      | .identifier name => s!"identifier {name}"
      | .inlineComment _ => "inline comment"
      | .blockComment _ => "multiline comment"
      | .number repr => s!"number {repr}"
      | .string repr => s!"string \"{repr}\""
      | .pcal [tk] => toString tk
      | .pcal _ => "PlusCal algorithm"

  -- Why does this fail when put in the `deriving` clause?
  deriving instance Functor for Token
end SurfaceTLAPlus
