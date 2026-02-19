import CustomPrelude
import PlusCalCompiler.GuardedPlusCal.Syntax
import Extra.Format

namespace GuardedPlusCal
  def Ref.pretty.{u} {Expr : Type u} [Std.ToFormat Expr] (r : Ref Expr) : Std.Format :=
    let args := r.args.map λ es ↦ .sbracket <| .joinSep es ", "
    r.name ++ .join args
  instance {Expr : Type _} [Std.ToFormat Expr] : Std.ToFormat (Ref Expr) := ⟨Ref.pretty⟩

  def ChanRef.pretty.{u} {Expr : Type u} [Std.ToFormat Expr] (c : ChanRef Expr) : Std.Format :=
    let args := if c.args.isEmpty then .nil else .sbracket <| .joinSep c.args ", "
    c.name ++ args
  instance {Expr : Type _} [Std.ToFormat Expr] : Std.ToFormat (ChanRef Expr) := ⟨ChanRef.pretty⟩

  variable {Typ Expr : Type} [Std.ToFormat Typ] [Std.ToFormat Expr]

  def Statement.pretty {b b' : Bool} (S : Statement Typ Expr b b') : Std.Format := match_source (indices := [3]) b, b', S with
    | true, false, .let name τ «=|∈» e, pos => formatPos pos ++ " let " ++ name ++ " : " ++ Std.format τ ++ (if «=|∈» then " = " else " ∈ ") ++ Std.format e
    | true, false, .await e, pos => formatPos pos ++ " await " ++ Std.format e
    | true, false, .receive chan ref, pos => formatPos pos ++ " receive" ++ .paren (Std.format chan ++ ", " ++ Std.format ref)
    | false, false, .skip, pos => formatPos pos ++ " skip"
    | false, true, .goto label, pos => formatPos pos ++ " goto " ++ label
    | false, false, .print e, pos => formatPos pos ++ " print " ++ Std.format e
    | false, false, .assert e, pos => formatPos pos ++ " assert " ++ Std.format e
    | false, false, .send chan e, pos => formatPos pos ++ " send" ++ .paren (Std.format chan ++ ", " ++ Std.format e)
    | false, false, .multicast chan filter e, pos =>
      let bs := filter.map λ ⟨name, τ, «=|∈», e⟩ ↦ name ++ " : " ++ Std.format τ ++ (if «=|∈» then " = " else " ∈ ") ++ Std.format e
      formatPos pos ++  " multicast" ++ .paren (chan ++ ", " ++ .sbracket (.joinSep bs ", " ++ " |-> " ++ Std.format e))
    | false, false, .assign ref e, pos => formatPos pos ++ " " ++ Std.format ref ++ " := " ++ Std.format e
    where
      formatPos (pos : SourceSpan) : Std.Format := .bracket "(* " (Std.format pos) " *)"
  instance {b b' : Bool} : Std.ToFormat (Statement Typ Expr b b') := ⟨Statement.pretty⟩

  def Block.pretty.{u} {α : Bool → Type u} {b : Bool} (pretty : ⦃b : Bool⦄ → α b → Std.Format) (B : Block α b) : Std.Format :=
    let _ : Std.ToFormat (α false) := ⟨pretty (b := _)⟩
    .joinSuffix B.begin ("; " ++ .line) ++ pretty B.last ++ "; "

  def AtomicBranch.pretty (B : AtomicBranch Typ Expr) : Std.Format :=
    B.precondition.elim .nil (Block.pretty (λ ⦃_⦄ ↦ Statement.pretty)) ++ .line
      ++ B.action.pretty (λ ⦃_⦄ ↦ Statement.pretty)
  instance : Std.ToFormat (AtomicBranch Typ Expr) := ⟨AtomicBranch.pretty⟩

  def AtomicBlock.pretty (B : AtomicBlock Typ Expr) : Std.Format :=
    let branches : List Std.Format := B.branches.map λ B ↦ .bracket "{" (.group (.nest 4 <| .line ++ B.pretty) ++ .line) "}"
    B.label ++ ": " ++ .line
      ++ .group (.nest 4 <| "either " ++ .joinSep branches " or ")
  instance : Std.ToFormat (AtomicBlock Typ Expr) := ⟨AtomicBlock.pretty⟩

  def Thread.pretty (T : Thread Typ Expr) : Std.Format :=
    .bracket "{" (.line ++ .joinSep T .line ++ .line) "}"
  instance : Std.ToFormat (Thread Typ Expr) := ⟨Thread.pretty⟩

  def Process.pretty (P : Process Typ Expr) : Std.Format :=
    let mailbox : Std.Format := P.mailbox.elim .nil λ e ↦ " " ++ .paren ("mailbox := " ++ Std.format e)
    let vars := if P.locals.isEmpty then .nil else .group (.indent 4 <|
      "variables " ++ .joinSep (P.locals.toList.map λ ⟨name, τ, «=|∈», e⟩ ↦ Std.Format.line ++ name ++ " : " ++ Std.format τ ++ (if «=|∈» then " = " else " ∈ ") ++ Std.format e) ", "
        ++ ";") ++ .line
    "process " ++ P.name ++ mailbox ++ " {" ++ .line ++ vars ++ .joinSep P.threads .line ++ .line ++ "}"
  instance : Std.ToFormat (Process Typ Expr) := ⟨Process.pretty⟩

  def Algorithm.pretty (A : Algorithm Typ Expr) : Std.Format :=
    let channels := if A.channels.isEmpty then .nil else .group (.nest 4 <|
      "channels " ++ .joinSep (A.channels.toList.map λ ⟨name, τ, dims⟩ ↦ name ++ (if dims.isEmpty then Std.Format.nil else .sbracket (.joinSep dims ", ")) ++ " : " ++ Std.format τ) ", " ++ ";") ++ .line
    let fifos := if A.fifos.isEmpty then .nil else .group (.nest 4 <|
      "fifos " ++ .joinSep (A.channels.toList.map λ ⟨name, τ, dims⟩ ↦ name ++ (if dims.isEmpty then Std.Format.nil else .sbracket (.joinSep dims ", ")) ++ " : " ++ Std.format τ) ", " ++ ";") ++ .line
    "algorithm " ++ A.name ++ .bracket " {" (.group (.indent 4 <| channels ++ fifos ++ .joinSep A.procs .line) ++ .line) "}"
  instance : Std.ToFormat (Algorithm Typ Expr) := ⟨Algorithm.pretty⟩
