module

public import Aesop

public section

-- Leaf discharge for `sem_side` (`Core/GuardedPlusCal/Semantics/Lemmas.lean`'s `T1`): evaluation
-- transfers, memberships, freshness — the side conditions `sem_red` leaves behind. Its own file:
-- an Aesop rule set is only visible to files that *import* the one that declared it, not to the
-- file that declares it itself.
declare_aesop_rule_sets [sem]

end
