module

-- public import Mathlib.Control.Traversable.Basic
meta import CustomPrelude

public section

namespace Array
  instance : Functor Array where
    map := Array.map
end Array

end
