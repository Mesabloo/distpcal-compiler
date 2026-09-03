module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.byCasesBang`

`by_cases h : p` then `push_neg at h` is `by_cases! h : p` — the `!` runs the `push_neg` itself.
Same for `by_contra` / `by_contra!`.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `by_cases! h`, not `by_cases h` + `push_neg`. -/
register_option linter.fugue.byCasesBang : Bool := {
  defValue := true
  descr := "flag `by_cases`/`by_contra` whose bound name a later `push_neg` clears — use the `!` form"
}

/-- The keyword of a plain (non-`!`) `by_cases` / `by_contra`, by its leading atom. -/
private def plainKw? (stx : Syntax) : Option String :=
  match stx[0] with
  | .atom _ "by_cases" => some "by_cases"
  | .atom _ "by_contra" => some "by_contra"
  | _ => none

/-- The name a `by_cases`/`by_contra` binds: its first nested identifier. -/
private def bindsHyp? (stx : Syntax) : Option String :=
  stx.find? (·.isIdent) |>.bind identLast?

/-- Names cleared by a `push_neg` anywhere under `root`. -/
private def pushNegNames (root : Syntax) : Array String :=
  (collect (·[0] matches .atom _ "push_neg") root).flatMap λ pn ↦
    (collect (·.isIdent) pn).filterMap identLast?

/-- Every plain `by_cases`/`by_contra` whose bound name some `push_neg` in the command clears. -/
def byCasesBangCore : Syntax → Array Finding := fun root ↦
  let cleared := pushNegNames root
  scan (fun s ↦
    match plainKw? s, bindsHyp? s with
    | some kw, some name =>
      if cleared.contains name then
        hit s m!"`{kw} {name}` then `push_neg at {name}` — use `{kw}! {name}`"
      else #[]
    | _, _ => #[]) root

/-- The `linter.fugue.byCasesBang` linter. -/
def byCasesBang : Linter where run := mkFugueLinter linter.fugue.byCasesBang byCasesBangCore

initialize addLinter byCasesBang

end CustomPrelude.Linter
