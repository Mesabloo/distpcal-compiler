module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.unfoldForeign`

A definition's body belongs to the file that defines it. A downstream proof that `unfold`s (or
`simp [f]`s) past the API into the body breaks together with every other such site the day the
body changes — invisibly, because no two of them share a name. Characterize the definition once,
beside it, and `rw` / `obtain` against that name downstream.

The linter flags an `unfold f` / `delta f`, or a `simp` argument naming a `def`, when `f` comes
from a module other than the one being elaborated. An `abbrev` (a reducible tag like
`registerSource`) is exempt — it has no body to protect.

`default := false`: a file-per-module check reads "another module" too literally for a
development that spreads one language's definitions and the lemmas about them across a directory
of sibling files (`Core/ComputableTLAPlus/{Subst,FreeVars,Coercion}.lean` all reason about
`ComputableTLAPlus.Expression.*`). Deciding whether a file "is about" the constant it unfolds
needs judgement; opt in per file (`set_option linter.fugue.unfoldForeign true`) where the API
boundary is real.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- `unfold f` / `simp [f]` only inside a proof about `f`. -/
register_option linter.fugue.unfoldForeign : Bool := {
  defValue := false
  descr := "flag `unfold` / `simp [f]` of a definition that another module owns"
}

/-- Candidate identifiers to resolve: `(idStx, fromSimp)`. `unfold` / `delta` arguments count
whatever they name; a `simp` argument only when it resolves to a `def`. -/
private def candidates (stx : Syntax) : Array (Syntax × Bool) := Id.run do
  let mut out : Array (Syntax × Bool) := #[]
  for u in collect (λ s ↦ s.getKind == ``Lean.Parser.Tactic.unfold
                        || s.getKind == ``Lean.Parser.Tactic.delta) stx do
    for i in u[1].getArgs do
      if i.isIdent then out := out.push (i, false)
  for sl in collect (·.getKind == `Lean.Parser.Tactic.simpLemma) stx do
    if sl[2].isIdent then out := out.push (sl[2], true)
  return out

/-- Every `unfold` / `simp [def]` whose target another module owns. -/
def unfoldForeignCore : Syntax → CommandElabM (Array Finding) := λ stx ↦ do
  let cands := candidates stx
  if cands.isEmpty then return #[]
  let env ← getEnv
  let curIdx := env.getModuleIdx? (← getMainModule)
  let mut out : Array Finding := #[]
  let mut seen : Std.HashSet Nat := {}
  for (idStx, fromSimp) in cands do
    let some declName ← liftTermElabM (observing? (realizeGlobalConstNoOverload idStx)) | continue
    -- `none` ⇒ the current module; equal to `curIdx` ⇒ also current (async elaboration registers
    -- a module's own constants under its index).
    let some declIdx := env.getModuleIdxFor? declName | continue
    if curIdx == some declIdx then continue
    match env.find? declName with
    | some (.defnInfo di) => if di.hints matches .abbrev then continue
    | some _ => if fromSimp then continue  -- a `simp` arg that is not a `def` is a lemma: fine
    | none => continue
    let some p := idStx.getRange?.map (·.start.byteIdx) | continue
    unless seen.contains p do
      seen := seen.insert p
      out := out.push ⟨idStx,
        m!"`{declName}` is imported — characterize it in the module that defines it, not by unfolding past its API here"⟩
  return out

/-- The `linter.fugue.unfoldForeign` linter. -/
def unfoldForeign : Linter where run := mkFugueLinterM linter.fugue.unfoldForeign unfoldForeignCore

initialize addLinter unfoldForeign

end CustomPrelude.Linter
