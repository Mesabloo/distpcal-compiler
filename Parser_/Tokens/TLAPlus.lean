module

meta import CustomPrelude
public import Mathlib.Data.String.Defs
public import Core.SurfaceTLAPlus.Syntax

public section

namespace SurfaceTLAPlus
  /--
    Syntactic tokens of the TLA⁺ language, including unicode and LaTeX-like variants.

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
    | «true»
    | «false»
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
    /-- The weak-fairness prefix `WF_`. Lexed as its own token: `WF_e` is `WF_` then identifier `e`. -/
    | «WF_»
    /-- The strong-fairness prefix `SF_`. Lexed as its own token: `SF_e` is `SF_` then identifier `e`. -/
    | «SF_»
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

  abbrev Token.lparen {α} : Token α := .paren .true
  abbrev Token.rparen {α} : Token α := .paren .false
  abbrev Token.lbrace {α} : Token α := .brace .true
  abbrev Token.rbrace {α} : Token α := .brace .false
  abbrev Token.lbracket {α} : Token α := .bracket .true
  abbrev Token.rbracket {α} : Token α := .bracket .false
  abbrev Token.langle {α} : Token α := .angle .true
  abbrev Token.rangle {α} : Token α := .angle .false

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
      | .true => "keyword 'TRUE'"
      | .false => "keyword 'FALSE'"
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
      | .«WF_» => "keyword 'WF_'"
      | .«SF_» => "keyword 'SF_'"
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

  -- TODO(deriving): find out why `Functor` fails inside `Token`'s own `deriving` clause and fold
  -- this back in.
  deriving instance Functor for Token
end SurfaceTLAPlus

end
