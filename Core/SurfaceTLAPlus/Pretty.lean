import CustomPrelude
import Common.Pretty
import Core.SurfaceTLAPlus.Syntax

namespace SurfaceTLAPlus
  partial def Typ.pretty : Typ → Std.Format
    | .bool => "Bool"
    | .int => "Int"
    | .str => "Str"
    | .address => "Address"
    | .function dom@(.function _ _) rng
    | .function dom@(.operator _ _) rng => .paren (pretty dom) ++ " → " ++ pretty rng
    | .function dom rng => pretty dom ++ " → " ++ pretty rng
    | .set τ => "Set" ++ .paren (pretty τ)
    | .seq τ => "Seq" ++ .paren (pretty τ)
    | .tuple τs => .bracket "<<" (.joinSep (τs.map pretty) ", ") ">>"
    | .operator dom rng => .paren (.joinSep (dom.map pretty) ", ") ++ " ⇒ " ++ pretty rng
    | .var v => v
    | .const v => v
    | .record fs => .bracket "{" (.joinSep (fs.map λ ⟨name, τ⟩ ↦ name ++ " : " ++ pretty τ) ", ") "}"
    | .channel τ => "Channel" ++ .paren (pretty τ)
  instance : Std.ToFormat Typ := ⟨Typ.pretty⟩
