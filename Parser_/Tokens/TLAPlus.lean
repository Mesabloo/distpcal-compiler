import CustomPrelude
import Mathlib.Data.String.Defs
import Core.SurfaceTLAPlus.Syntax

namespace SurfaceTLAPlus
  /--
    The type of all syntactical tokens of the TLA⁺ language.
    This contains all unicode variations as well as LaTeX-like codes.

    `α` abstracts away the type of PlusCal tokens.
  -/
  inductive Token.{u} (α : Type u) : Type u
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
