import PlusCalCompiler.CoreTLAPlus.Syntax

open CoreTLAPlus

def Conv : Typ → Typ → Prop := (· = ·)

-- inductive Conv : Typ → Typ → Prop
--   | int : Conv .int .int
--   | bool : Conv .bool .bool
--   | str : Conv .str .str

--   | set {τ τ'} : Conv τ τ' → Conv (.set τ) (.set τ')
--   | seq {τ τ'} : Conv τ τ' → Conv (.seq τ) (.seq τ')

--   | address : Conv .address .address
infix:60 " ≅ " => Conv

instance {τ τ'} : Decidable (Conv τ τ') :=
  inferInstanceAs (Decidable (τ = τ'))
