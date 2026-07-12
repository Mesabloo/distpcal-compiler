module

public import Core.SurfacePlusCal.Syntax
public import Common.Pretty

@[expose] public section


/-! Pretty-printing for `SurfacePlusCal`, used by `-d`-style AST dumps. -/

namespace SurfacePlusCal

private abbrev formatFairness (b : Bool) : Std.Format :=
  if b then "fair " else .nil

private def formatBlock {α} (f : α → Std.Format) (t : List (String ⊕ α)) : Std.Format :=
  let fmt : String ⊕ α → Std.Format
    | .inl l => f!"{l}: "
    | .inr S => f!"    {f S}"
  Std.Format.sbracket <| .indent 2 <| .joinSep (fmt <$> t) .line

instance {β} [Std.ToFormat β] : Std.ToFormat (Ref β) where
  format r := f!"{r.name}" ++ .join (r.args.map λ
    | .inl field => f!".{field}"
    | .inr idx => .sbracket (.joinSep (Std.format <$> idx) ","))

instance {α β} [Std.ToFormat α] [Std.ToFormat β] : Std.ToFormat (MulticastFilter α β) where
  format f := .sbracket (.joinSep (f.binds.map λ (x, ann, eq, e) ↦
    f!"{ann} {x} {if eq then "=" else "\\in"} {e}") ", ") ++ f!" |-> {f.val}"

partial def Statement.pretty {α β} [Std.ToFormat α] [Std.ToFormat β] (S : Statement α β) : Std.Format :=
  formatPos (posOf S) ++ match S with
    | .skip => "skip;"
    | .goto label => f!"goto {label};"
    | .print e => f!"print {e};"
    | .assign asss => .joinSep (asss.map λ (r, e) ↦ f!"{r} := {e}") " || " ++ ";"
    | .if cond B₁ B₂ =>
      f!"if ({cond})" ++ formatBlock Statement.pretty B₁ ++
      B₂.elim .nil (λ B₂ ↦ .line ++ " else " ++ formatBlock Statement.pretty B₂) ++ ";"
    | .await e => f!"await {e};"
    | .with vars B =>
      "with " ++ .joinSep (vars.map λ (x, ann, eq, e) ↦ f!"{ann}{x} {if eq then "=" else "\\in"} {e}") ", " ++
      formatBlock Statement.pretty B ++ ";"
    | .assert e => f!"assert {e};"
    | .either branches => .align true ++ "either " ++ .joinSep (formatBlock Statement.pretty <$> branches) (.line ++ "or ") ++ ";"
    | .while cond B => f!"while ({cond})" ++ formatBlock Statement.pretty B ++ ";"
    | .receive c r => f!"receive({c}, {r});"
    | .send c e => f!"send({c}, {e});"
    | .multicast c filter => f!"multicast({c}, {filter});"
where
  formatPos (pos : SourceSpan) : Std.Format := .bracket "(* " (Std.format pos) " *)"

instance {α β} [Std.ToFormat α] [Std.ToFormat β] : Std.ToFormat (Statement α β) := ⟨Statement.pretty⟩

instance {α β} [Std.ToFormat α] [Std.ToFormat β] : Std.ToFormat (Declarations α β) where
  format d := .align true ++
    (if d.variables.isEmpty then Std.Format.nil else
      "variables " ++ .joinSep (d.variables.map λ (x, ann, e) ↦
        f!"{ann} {x}" ++ match e with
          | .none => Std.Format.nil
          | .some (eq, e) => f!"{if eq then " =" else " \\in"} {e}") ", " ++ ";") ++
    .line ++
    (if d.channels.isEmpty then Std.Format.nil else
      "channels " ++ .joinSep (d.channels.map λ (x, ann, es) ↦
        f!"{x} {ann}" ++ if es.isEmpty then Std.Format.nil else .join (es.map λ e ↦ .sbracket f!"{e}")) ", ") ++
    .line ++
    (if d.fifos.isEmpty then Std.Format.nil else
      "fifos " ++ .joinSep (d.fifos.map λ (x, ann, es) ↦
        f!"{x} {ann}" ++ if es.isEmpty then Std.Format.nil else .join (es.map λ e ↦ .sbracket f!"{e}")) ", ")

instance {α β} [Std.ToFormat α] [Std.ToFormat β] : Std.ToFormat (Process α β) where
  format p := Std.format p.ann ++ f!" {formatFairness p.isFair}process ({p.name} {if p.«=|∈» then " = " else " ∈ "} {p.id})" ++ .indent 2 (
    .nest 2 (Std.format p.localState) ++ .line ++
    .joinSep (formatBlock Std.format <$> p.threads) .line
  )

instance {α β} [Std.ToFormat α] [Std.ToFormat β] : Std.ToFormat (Algorithm α β) where
  format alg :=
    f!"(*--{formatFairness alg.isFair}algorithm {alg.name}" ++ .cbracket (.indent 2 <|
      .nest 2 (Std.format alg.globalState) ++ .line ++
      .joinSep (Std.format <$> alg.processes) .line)

end SurfacePlusCal

end
