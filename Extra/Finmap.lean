import Mathlib.Data.Finmap

namespace Finmap
  def get {α} {β : α → _} [DecidableEq α] (f : Finmap β) (x : α) (h : x ∈ f) : β x :=
    f.lookup x |>.get (Finmap.lookup_isSome.mpr h)
end Finmap
