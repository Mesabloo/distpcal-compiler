module

public import Mathlib.Data.Finmap

public section

namespace Finmap
  @[expose]
  def get {α} {β : α → _} [DecidableEq α] (f : Finmap β) (x : α) (h : x ∈ f) : β x :=
    f.lookup x |>.get (Finmap.lookup_isSome.mpr h)
end Finmap

end
