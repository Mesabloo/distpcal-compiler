import Extra.Topology.IMetricSpace
import Extra.Topology.ClosedEmbedding

structure IsometricEmbedding (α β : Type _) [IMetricSpace α] [IMetricSpace β] extends ClosedEmbedding α β where
  isIso : Isometry toFun

infixr:25 " ↪c₁ " => IsometricEmbedding

instance {α β : Type _} [IMetricSpace α] [IMetricSpace β] : Coe (IsometricEmbedding α β) (α → β) where
  coe := (IsometricEmbedding.toClosedEmbedding · |>.toFun)

@[ext]
theorem IsometricEmbedding.ext {α β} [IMetricSpace α] [IMetricSpace β] {f g : α ↪c₁ β}
  (h : f.toFun = g.toFun) :
    f = g := by
  let ⟨⟨_, _⟩, _⟩ := f
  let ⟨⟨_, _⟩, _⟩ := g
  simpa using h
