module

public import Parser_.Tokens.TLAPlus

public section

namespace SurfacePlusCal
  inductive Token : Type
    | fair
    | algorithm
    | «variable»
    | «variables»
    | define
    | process
    | «if»
    | «else»
    | «while»
    | «with»
    | skip
    | either
    | await
    | when
    | assert
    | print
    | goto
    | or
    | semicolon
    | barbar
    | dashdash
    -- Distributed PlusCal
    | fifo
    | fifos
    | channel
    | channels
    | receive
    | multicast
    | send
    /-- Embeds a TLA⁺ token, for parsing TLA⁺ expressions inside PlusCal. -/
    | tla (tk : SurfaceTLAPlus.Token SurfacePlusCal.Token)
    deriving Repr, Inhabited, BEq

  protected partial def Token.toString : Token → String := λ
    | .fair => "keyword 'fair'"
    | .algorithm => "keyword 'algorithm'"
    | .variable => "keyword 'variable'"
    | .variables => "keyword 'variables'"
    | .define => "keyword 'define'"
    | .process => "keyword 'process'"
    | .if => "keyword 'if'"
    | .else => "keyword 'else'"
    | .while => "keyword 'while'"
    | .with => "keyword 'with'"
    | .skip => "keyword 'skip'"
    | .either => "keyword 'either'"
    | .await => "keyword 'await'"
    | .when => "keyword 'when'"
    | .assert => "keyword 'assert'"
    | .print => "keyword 'print'"
    | .goto => "keyword 'goto'"
    | .or => "keyword 'or'"
    | .semicolon => "symbol ';'"
    | .barbar => "symbol '||'"
    | .dashdash => "symbol '--'"
    | .fifo => "keyword 'fifo'"
    | .fifos => "keyword 'fifos'"
    | .channel => "keyword 'channel'"
    | .channels => "keyword 'channels'"
    | .receive => "keyword 'receive'"
    | .multicast => "keyword 'multicast'"
    | .send => "keyword 'send'"
    | .tla tk => letI _ : ToString Token := ⟨Token.toString⟩; toString tk

  instance : ToString Token := ⟨Token.toString⟩
end SurfacePlusCal

end
