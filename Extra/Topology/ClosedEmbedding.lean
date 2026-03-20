import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Extra.Topology.ClosedEmbedding.Tactic

structure ClosedEmbedding (α β) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  isClosedEmbedding : Topology.IsClosedEmbedding toFun := by first | sorry_if_sorry | is_closed_embedding; done
infixr:25 " ↪c " => ClosedEmbedding

macro_rules | `(tactic| is_closed_embedding_step) => `(tactic| exact ClosedEmbedding.isClosedEmbedding _)

instance {α β} [TopologicalSpace α] [TopologicalSpace β] : FunLike (α ↪c β) α β where
  coe := ClosedEmbedding.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ ⟨⟩; rfl

theorem ClosedEmbedding.injective_toFun {α β} [TopologicalSpace α] [TopologicalSpace β] :
    Function.Injective (ClosedEmbedding.toFun (α := α) (β := β)) := by
  rintro ⟨⟩ ⟨⟩ rfl
  rfl

@[ext]
def ClosedEmbedding.ext {α β} [TopologicalSpace α] [TopologicalSpace β] {f g : α ↪c β}
  (h : f.toFun = g.toFun) :
    f = g := by
  let ⟨_, _⟩ := f
  let ⟨_, _⟩ := g
  grind only

def ClosedEmbedding.comp {α β γ} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  (g : ClosedEmbedding β γ) (f : ClosedEmbedding α β) :
    ClosedEmbedding α γ where
  toFun := g.toFun ∘ f.toFun
  isClosedEmbedding := g.isClosedEmbedding.comp f.isClosedEmbedding
