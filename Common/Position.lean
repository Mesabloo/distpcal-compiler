module

public import Mathlib.Control.Traversable.Basic
public import Mathlib.Logic.Function.Basic

@[expose] public section


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

/-- A placeholder position for diagnostics with no real one to report against. **Not**
`default`/`(0 : SourceSpan)` — both are `⟨⟨0,0⟩,⟨0,0⟩⟩`, but every real position in this codebase
has 1-indexed lines (lexing starts at `⟨1,0⟩`), so line `0` would render a wrong, off-by-one line
number. Line `1` points at a real line even though the span itself stays meaningless. -/
def SourceSpan.placeholder : SourceSpan := ⟨⟨1, 0⟩, ⟨1, 0⟩⟩

instance : Append SourceSpan where
  append := SourceSpan.merge

private def Internal.initSourceMap : IO (IO.Ref (Std.TreeMap USize SourceSpan)) :=
  IO.mkRef ∅

/--
  A map associating arbitrary data to source positions.

  Deliberately a `Std.TreeMap`, not a `Std.HashMap`. The map lives in a module-initializer
  `IO.Ref`, whose contents the runtime marks multi-threaded; every `IO.Ref.modifyGet` re-marks
  the value it stores. A hash map's bucket `Array` then fails `Array.uset`'s exclusivity check
  on every insert and is deep-copied whole — O(size) per `registerSource`, O(size²) per compile.
  A red-black tree's `insert` path-copies O(log size) nodes regardless of mark state, so the
  marking costs nothing extra.
-/
@[never_extract, noinline, init Internal.initSourceMap]
private unsafe opaque Internal.sourceMap : IO.Ref (Std.TreeMap USize SourceSpan)

@[never_extract, noinline]
private unsafe def Internal.registerSourceImpl {α : Type} (x : α) (pos : SourceSpan) : α :=
  unsafeBaseIO do
    Internal.sourceMap.modifyGet (x, Std.TreeMap.insert · (ptrAddrUnsafe x) pos)

@[never_extract, noinline]
private unsafe def Internal.posOfImpl {α : Type} (x : α) : SourceSpan :=
  ((unsafeBaseIO Internal.sourceMap.get).get? (ptrAddrUnsafe x)).getD default_or_ofNonempty%

@[implemented_by Internal.registerSourceImpl, never_extract]
abbrev registerSource {α : Type} (x : α) (_ : SourceSpan) : α := x
infix:60 " @@ " => registerSource

@[implemented_by Internal.posOfImpl, never_extract]
abbrev posOf {α : Type} (x : α) : SourceSpan := default_or_ofNonempty%

@[never_extract, noinline]
private unsafe def Internal.forgetSourcePositionsImpl : BaseIO Unit :=
  Internal.sourceMap.set ∅

/--
  Drop every registered position. Call this at the start of a compile, never during one.

  `registerSource`/`posOf` key on `ptrAddrUnsafe`, and the map outlives the values it describes.
  That is harmless for a value that *was* registered — no two live values share an address, so its
  own entry is the only one its address can hold. It is not harmless for a value that was never
  registered and has its position read anyway: `posOf` cannot distinguish "no entry" from "an entry
  left by something now dead", and it answers with the corpse's span.

  **Registering is therefore an obligation on every pass, not a nicety.** This clear is the second
  half of the same contract: it bounds an address's reuse to one compile, so a
  node registered by a *previous* compile can never answer for a node in this one. Across compiles
  the stale span would come from another file, where the line need not exist at all.

  What this is **not** is a substitute for registering. A position that was never recorded has no
  right answer, and clearing only changes which wrong answer is given. Nor does it make concurrent
  compiles safe: the map is one global `IO.Ref` and clearing is itself destructive, so a clear on
  one thread drops the spans another thread has registered so far. That is why `lake test` defaults
  to `-j 1`.
-/
@[implemented_by Internal.forgetSourcePositionsImpl, never_extract]
def forgetSourcePositions : BaseIO Unit := pure ()

open Lean Parser Term in section
  meta def posIndices : Parser := leading_parser
    atomic ("(" >> nonReservedSymbol "indices") >> " := " >> "[" >> many numLit >> "]" >> ")" >> ppSpace

  /--
    Match arbitrary expressions, together with the positions attached to them.
    If some expressions may not be attached positions (e.g. proofs), one can specify `(indices := [n₁ ... nₙ])` to
    only match on the positions of the `nᵢ`-th discriminant (`1`-based indexing).
  -/
  @[term_parser]
  public meta def matchSource : Parser := leading_parser:leadPrec
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

    -- `idx` may repeat an index, so the same expression can get more than one `let`. They bind
    -- distinct names and are all pure, so the duplicates are harmless.

    let «match» : Term ← `(term| match $[(generalizing := $generalize)]? $[(motive := $motive)]? $discr,* with $alts)
    let e : Term ← lets.foldlM (init := «match») λ «match» (x, e) ↦ `(term| let $x:ident := $e; $«match»)
    return e
end

end
