module

public import Batteries.Data.AssocList

@[expose] public section


namespace Batteries.AssocList
  instance {α β} [BEq α] : Membership α (Batteries.AssocList α β) where
    mem as k := as.find? k |>.isSome

end
