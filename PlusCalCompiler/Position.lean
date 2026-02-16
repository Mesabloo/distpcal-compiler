import Mathlib.Control.Traversable.Basic
import Mathlib.Logic.Function.Basic

/--
  A position, expressed as a pair of numbers of UTF-8 codepoints (rather than byte indices).
-/
@[unbox]
structure Cursor where
  line : Nat
  col : Nat
  deriving Repr, Inhabited, DecidableEq, BEq, Hashable

instance : OfNat Cursor 0 where
  ofNat := { line := 0, col := 0 }

instance : ToString Cursor where
  toString cursor := s!"{cursor.line}:{cursor.col + 1}"

def Cursor.lt (c₁ c₂ : Cursor) : Prop :=
  c₁.line < c₂.line ∨ (c₁.line = c₂.line ∧ c₁.col < c₂.col)

def Cursor.le (c₁ c₂ : Cursor) : Prop := c₁.lt c₂ ∨ c₁ = c₂

instance : LT Cursor where
  lt := Cursor.lt

instance : LE Cursor where
  le := Cursor.le

instance (c₁ c₂ : Cursor) : Decidable (c₁ < c₂) := by
  if h : c₁.line < c₂.line ∨ (c₁.line = c₂.line ∧ c₁.col < c₂.col)
  then apply Decidable.isTrue
       assumption
  else apply Decidable.isFalse
       assumption

-- instance (c₁ c₂ : Cursor) : Decidable (c₁ = c₂) := by
--   if h : c₁.line = c₂.line ∧ c₁.col = c₂.col
--   then apply Decidable.isTrue
--        obtain ⟨_, _⟩ := c₁
--        obtain ⟨_, _⟩ := c₂
--        congr <;> {
--          obtain ⟨_, _⟩ := h
--          trivial
--        }
--   else apply Decidable.isFalse
--        intro _
--        obtain ⟨_, _⟩ := c₁
--        obtain ⟨_, _⟩ := c₂
--        injections
--        subst_vars
--        apply h
--        trivial

instance (c₁ c₂ : Cursor) : Decidable (c₁ > c₂) := inferInstanceAs (Decidable (_ ∨ _))

instance : Min Cursor where
  min c₁ c₂ := if c₁ < c₂ then c₁ else c₂

instance : Max Cursor where
  max c₁ c₂ := if c₁ < c₂ then c₂ else c₁

structure SourceSpan : Type where
  start : Cursor
  «end» : Cursor
  deriving Repr, Inhabited, DecidableEq, BEq, Hashable

instance : OfNat SourceSpan 0 where
  ofNat := { start := 0, «end» := 0 }

instance : ToString SourceSpan where
  toString span := s!"{span.start}-{span.end}"

instance : Std.ToFormat SourceSpan := inferInstance

def SourceSpan.merge (p₁ p₂ : SourceSpan) : SourceSpan where
  start := min p₁.start p₂.start
  «end» := max p₁.end p₂.end

instance : Append SourceSpan where
  append := SourceSpan.merge

/-- A piece of data is located if its span in the stream is fully known. -/
@[unbox]
structure Located (α : Type _) : Type _ where
  segment : SourceSpan
  data : α
  deriving Repr, Inhabited, DecidableEq, BEq --, Hashable

instance {α : Type _} : Coe (SourceSpan × α) (Located α) where
  coe := λ ⟨pos, x⟩ ↦ ⟨pos, x⟩

instance : Functor Located where
  map f l := {l with data := f l.data}

instance instTraversableLocated : Traversable Located where
  traverse f l := ({l with data := ·}) <$> f l.data

instance (priority := high) {α β} : Function.HasUncurry (SourceSpan → α → β) (Located α) β where
  uncurry f x := f x.segment x.data
