import Extra.Topology.IMetricSpace
import Extra.Topology.ClosedEmbedding

structure IsometricEmbedding (α β : Type _) [IMetricSpace α] [IMetricSpace β] extends ClosedEmbedding α β where
  isIso : Isometry toFun

infixr:25 " ↪c₁ " => IsometricEmbedding

instance {α β : Type _} [IMetricSpace α] [IMetricSpace β] : FunLike (α ↪c₁ β) α β where
  coe := (IsometricEmbedding.toClosedEmbedding · |>.toFun)
  coe_injective' := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩; rfl

@[ext]
theorem IsometricEmbedding.ext {α β} [IMetricSpace α] [IMetricSpace β] {f g : α ↪c₁ β}
  (h : f.toFun = g.toFun) :
    f = g := by
  let ⟨⟨_, _⟩, _⟩ := f
  let ⟨⟨_, _⟩, _⟩ := g
  simpa using h
