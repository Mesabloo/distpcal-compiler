module

public import Batteries.Data.AssocList

public section

namespace Batteries.AssocList
  instance {α β} [BEq α] : Membership α (Batteries.AssocList α β) where
    mem as k := as.find? k |>.isSome
end Batteries.AssocList

end
