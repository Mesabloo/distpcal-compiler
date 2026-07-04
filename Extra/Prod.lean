namespace Prod
  def mapM {m : Type → Type} {α β δ γ : Type} [Monad m] (f : α → m β) (g : δ → m γ) (x : α × δ) : m (β × γ)
    := .mk <$> f x.fst <*> g x.snd

  abbrev thd {α β γ : Type} (x : α × β × γ) : γ := x.snd.snd

  def map₃ {α β γ δ ε ζ : Type _} (f : α → δ) (g : β → ε) (h : γ → ζ) : α × β × γ → δ × ε × ζ
    | ⟨x, y, z⟩ => ⟨f x, g y, h z⟩

  def traverse₃ {α β γ δ ε ζ : Type} {F : Type → Type} [Applicative F] (f : α → F δ) (g : β → F ε) (h : γ → F ζ) : α × β × γ → F (δ × ε × ζ)
    | ⟨x, y, z⟩ => (·, ·, ·) <$> f x <*> g y <*> h z

  def dup.{u} {α : Type u} (x : α) : α × α := (x, x)

  abbrev hasDecEq {α β : Type _} [DecidableEq α] [DecidableEq β] : DecidableEq (α × β) := inferInstance
end Prod

namespace MProd
  @[ext]
  theorem MProd.ext {α β} {x y : MProd α β} : x.fst = y.fst → x.snd = y.snd → x = y := by
    intros fst_eq snd_eq
    obtain ⟨⟩ := x
    obtain ⟨⟩ := y
    simp_all only
end MProd
