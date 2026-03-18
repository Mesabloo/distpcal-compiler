import CustomPrelude
import Mathlib.Topology.Maps.Basic

-- register_label_attr is_closed_embedding

-- set_option hygiene false in
/--
  Tries to automatically discharge goals of the shape `⊢ Topology.IsClosedEmbedding ?f`.
  This is an extendible tactic, new entries can be added via `macro_rules`.
-/
syntax "is_closed_embedding" : tactic

syntax "is_closed_embedding_step" : tactic

macro_rules
| `(tactic| is_closed_embedding_step) =>
  `(tactic| guard_target =ₛ Topology.IsClosedEmbedding (_ ∘ _); apply Topology.IsClosedEmbedding.comp)

elab_rules : tactic
| `(tactic| is_closed_embedding) => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| repeat1' is_closed_embedding_step))


  -- `(tactic| apply_rules (config := {symm := false, exfalso := false}) using is_closed_embedding)
