namespace Fin
  def downCast {m n} (x : Fin n) (h : ↑x < m) : Fin m := ⟨↑x, h⟩
