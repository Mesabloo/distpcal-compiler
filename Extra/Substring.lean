def Substring.count (s : Substring) (c : Char) : Nat :=
  s.foldl (init := 0) λ acc c' ↦ if c == c' then acc + 1 else acc
