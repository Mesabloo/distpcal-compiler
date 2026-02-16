namespace Sum
  def hasDecEq {α β} [DecidableEq α] [DecidableEq β] : DecidableEq (α ⊕ β)
    | .inl x, .inl y | .inr x, .inr y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (λ _ ↦ by injections; contradiction)
    | .inl x, .inr y | .inr x, .inl y =>
      isFalse (λ _ ↦ by injections)

  def mapM.{u, v, w} {m : Type v → Type w} [Monad m] {α β : Type u} {α' β' : Type v}
    (f : α → m α') (g : β → m β') : α ⊕ β → m (α' ⊕ β')
      | .inl x => Sum.inl <$> f x
      | .inr x => Sum.inr <$> g x
