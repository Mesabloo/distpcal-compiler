import Mathlib.Control.Traversable.Basic
import CustomPrelude

namespace Array
  instance : Functor Array where
    map := Array.map
end Array
