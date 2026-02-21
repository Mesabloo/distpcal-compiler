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

instance (c₁ c₂ : Cursor) : Decidable (c₁ = c₂) := by
  if h : c₁.line = c₂.line ∧ c₁.col = c₂.col
  then apply Decidable.isTrue
       obtain ⟨_, _⟩ := c₁
       obtain ⟨_, _⟩ := c₂
       congr <;> {
         obtain ⟨_, _⟩ := h
         trivial
       }
  else apply Decidable.isFalse
       intro _
       obtain ⟨_, _⟩ := c₁
       obtain ⟨_, _⟩ := c₂
       injections
       subst_vars
       apply h
       trivial

instance (c₁ c₂ : Cursor) : Decidable (c₁ ≤ c₂) := inferInstanceAs (Decidable (c₁ < c₂ ∨ c₁ = c₂))

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

---------------

private def Internal.initSourceMap : IO (IO.Ref (Std.HashMap USize SourceSpan)) :=
  IO.mkRef (Std.HashMap.emptyWithCapacity 60)

/--
  A hashmap associating arbitrary data to source positions.
-/
@[never_extract, noinline, init Internal.initSourceMap]
private unsafe opaque Internal.sourceMap : IO.Ref (Std.HashMap USize SourceSpan)

@[never_extract, noinline]
private unsafe def Internal.registerSourceImpl {α : Type} (x : α) (pos : SourceSpan) : α :=
  unsafeBaseIO do
    Internal.sourceMap.modifyGet (x, Std.HashMap.insert · (ptrAddrUnsafe x) pos)

@[never_extract, noinline]
private unsafe def Internal.posOfImpl {α : Type} (x : α) : SourceSpan :=
  (unsafeBaseIO Internal.sourceMap.get)[ptrAddrUnsafe x]?.getD default_or_ofNonempty%

@[implemented_by Internal.registerSourceImpl, never_extract]
abbrev registerSource {α : Type} (x : α) (_ : SourceSpan) : α := x
infix:60 " @@ " => registerSource

@[implemented_by Internal.posOfImpl, never_extract]
abbrev posOf {α : Type} (x : α) : SourceSpan := default_or_ofNonempty%

open Lean Parser Term in section
  def posIndices : Parser := leading_parser
    atomic ("(" >> nonReservedSymbol "indices") >> " := " >> "[" >> many numLit >> "]" >> ")" >> ppSpace

  /--
    Match arbitrary expressions, together with the positions attached to them.
    If some expressions may not be attached positions (e.g. proofs), one can specify `(indices := [n₁ ... nₙ])` to
    only match on the positions of the `nᵢ`-th discriminant (`1`-based indexing).
  -/
  @[term_parser]
  def matchSource : Parser := leading_parser:leadPrec
    "match_source " >> optional generalizingParam >> optional motive >> optional posIndices >> sepBy1 matchDiscr "," >>
    " with " >> ppDedent matchAlts

  macro_rules
  | `(term| match_source $[(generalizing := $generalize)]? $[(motive := $motive)]? $[(indices := [$idx*])]? $discr,* with $alts:matchAlts) => withFreshMacroScope do
    let discr := discr.getElems
    let idx : Array Nat := match idx with
      | .none => Array.range' 1 discr.size
      | .some idx => idx.map λ n ↦ n.getNat

    let (lets, discr) ← idx.foldlM (init := (#[], discr)) λ ⟨lets, discr'⟩ num ↦ withFreshMacroScope do
      if let .some d := discr[num - 1]? then
        let `(matchDiscr| $[$h:ident :]? $e:term) := d | Macro.throwUnsupported
        let x := mkCIdent (`pos |>.num num)
        return (lets.push (x, ← `(term| $(mkIdent ``posOf):ident $e)), discr'.push <| ← `(matchDiscr| $[$h:ident :]? $x:term))
      else
        Macro.throwError s!"Not enough discriminants: must have at least {num} discriminants"

    -- Since `idx` can contain multiple copies of the same index, there may be several `let` introduced for the same expression.
    -- Let's hope that Lean optimises them out.

    let «match» : Term ← `(term| match $[(generalizing := $generalize)]? $[(motive := $motive)]? $discr,* with $alts)
    let e : Term ← lets.foldlM (init := «match») λ «match» (x, e) ↦ `(term| let $x:ident := $e; $«match»)
    return e
end

-- section
--   private inductive X
--     | x (n : ℕ)
--     deriving BEq, Inhabited

--   set_option linter.style.nameCheck false in
--   set_option linter.constructorNameAsVariable false in
--   private unsafe def __ : Bool :=
--     let x : X := .x 0 @@ ⟨⟨1, 1⟩, ⟨1, 2⟩⟩
--     let y : X := .x 1 @@ ⟨⟨1, 3⟩, ⟨1, 4⟩⟩

--     -- dbg_trace "Address of x: {ptrAddrUnsafe x}; Address of y: {ptrAddrUnsafe y}"

--     assert! x != y
--     match_source x, y with
--     | .x _, .x _, posx, posy =>
--       assert! posx == ⟨⟨1, 1⟩, ⟨1, 2⟩⟩
--       assert! posy == ⟨⟨1, 3⟩, ⟨1, 4⟩⟩
--       true

--   #guard unsafe __
-- end
