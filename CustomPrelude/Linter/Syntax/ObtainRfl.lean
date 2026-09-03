module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.obtainRfl`

`have h : a = b := proof` then `rw [h]` (with `h` unused afterwards) is `obtain rfl : a = b :=
proof` — substitution collapses the two names and takes the equation out of context, where `rw`
leaves `h` behind and only fires where it was aimed.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `obtain rfl : a = b := p`, not `have h` + `rw [h]`. -/
register_option linter.fugue.obtainRfl : Bool := {
  defValue := true
  descr := "flag `have h : a = b := p` + `rw [h]` with `h` then unused — use `obtain rfl`"
}

/-- A lone single-component identifier — a candidate for `subst`. `h.choose` (dotted) is not. -/
private def loneVar : Syntax → Bool
  | .ident _ _ n _ => match n.eraseMacroScopes with
    | .str .anonymous _ => true
    | _ => false
  | _ => false

/-- Every `have h : _ = _ := p` followed by a `rw`/`rewrite` whose only rule is `h`, with `h`
unused after. -/
def obtainRflCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      tacs.zipIdx.foldl (init := #[]) λ out (t, i) ↦
        if t.getKind != ``Lean.Parser.Tactic.tacticHave__ then out
        else match t.find? (·.isOfKind ``Lean.Parser.Term.letIdDecl) with
        | none => out
        | some d =>
          let hName := identLast? d[0][0]
          -- the type must be `X = Y` with at least one side a lone *single-component* identifier
          -- — the only shape `subst` / `obtain rfl` can act on (a dotted `h.choose` is not a var)
          let eqNode := (d.find? (·.isOfKind ``Lean.Parser.Term.typeSpec)).bind
            (·.find? (·.isOfKind `«term_=_»))
          let substable := eqNode.any λ eq ↦ loneVar eq[0] || loneVar eq[2]
          match hName with
          | none => out
          | some h =>
            -- next `rw`/`rewrite` rewriting the *goal* (no `at`) with only `h`
            let j := (tacs.extract (i + 1) tacs.size).findIdx? λ n ↦
              (n.getKind == ``Lean.Parser.Tactic.rwSeq || n.getKind == ``Lean.Parser.Tactic.rewriteSeq)
                && (n.find? (·.isOfKind ``Lean.Parser.Tactic.location)).isNone
                && (n.find? (·.isOfKind ``Lean.Parser.Tactic.rwRuleSeq)).any λ rs ↦
                  let rules := (collect (·.isOfKind ``Lean.Parser.Tactic.rwRule) rs)
                  rules.size == 1 && identsUnder rules[0]! == #[h]
            match j with
            | none => out
            | some jrel =>
              let jabs := i + 1 + jrel
              -- the `rw` must not be terminal (a terminal `rw` is closing the goal by `rfl`,
              -- which `obtain rfl` does not do), and `h` must be unused after it
              let notTerminal := jabs + 1 < tacs.size
              let usedLater := (tacs.extract (jabs + 1) tacs.size).any λ u ↦ (identsUnder u).contains h
              if substable && notTerminal && !usedLater then
                out.push ⟨t, m!"`have {h} : a = b := p` + `rw [{h}]` → `obtain rfl : a = b := p`"⟩
              else out
    else #[]

/-- The `linter.fugue.obtainRfl` linter. -/
def obtainRfl : Linter where run := mkFugueLinter linter.fugue.obtainRfl obtainRflCore

initialize addLinter obtainRfl

end CustomPrelude.Linter
