class Reduce.{u, v} (α : Type u) (β : outParam (Type v)) where
  reducing : α → β
class Abort.{u, v} (α : Type u) (β : outParam (Type v)) where
  abort : α → β
class Diverge.{u, v} (α : Type u) (β : outParam (Type v)) where
  div : α → β
notation "⟦" e:0 "⟧*" => Reduce.reducing e
notation "⟦" e:0 "⟧⊥" => Abort.abort e
notation "⟦" e:0 "⟧∞" => Diverge.div e
