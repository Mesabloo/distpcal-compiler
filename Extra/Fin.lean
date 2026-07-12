module

public section

namespace Fin
  @[expose]
  def downCast {m n} (x : Fin n) (h : ↑x < m) : Fin m := ⟨↑x, h⟩
end Fin

end
