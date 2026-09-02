module

meta import CustomPrelude
public import ZFLean

@[expose] public section

/-!
  The value domain for the concrete TLA⁺ expression evaluator: `Value := ZFSet`, one uniform
  representation for every kind of TLA⁺ value.

  TLA⁺ is untyped set theory, so a value — a number, a string, a set, a function, a tuple, a
  record — is always a set. This development represents that directly: `Value` is mathlib's
  `ZFSet`, set membership is `ZFSet`'s own `∈`, and the encodings below place each syntactic kind
  of literal into that one universe. Integers use `vtrelat/zflean`'s sign-tagged-pair encoding
  (`ZFSet.ofInt`), the booleans use its `zftrue`/`zffalse`, and functions, tuples, records and
  sequences are ordinary sets of ordered pairs.

  Distinct kinds of value are not kept provably disjoint: `FALSE` and the empty set share an
  encoding, a string and the tuple of its code points share an encoding, and so on. TLA⁺ leaves
  such cross-kind comparisons unspecified, and this compiler's type checker keeps them from ever
  being asked — an expression of set type only evaluates against the set encodings, one of string
  type only against the string encoding. Only within a kind are the encodings injective.

  Equality of values is not decidable — `ZFSet` extensionality is a `∀` — so `DecidableEq`/`BEq`
  are classical and noncomputable, which costs nothing here: evaluation is a `Prop` relation.
-/

namespace ComputableTLAPlus

/-- A TLA⁺ value: an element of the cumulative set hierarchy. Every kind of TLA⁺ value — scalar,
set, function, tuple, record — is one of these. `ZFSet` is `Type 1` (its underlying `PSet` is
`Type`), so `Value` is `Type 1`. -/
abbrev Value : Type 1 := ZFSet

namespace Value

/-- The integer `z`, as the corresponding element of `zflean`'s `ZFSet.Int` encoding. Routed
through `ZFInt.into` (rather than `ZFSet.ofInt`) because that map's injectivity is a public lemma,
whereas `ZFSet.ofInt`'s body is not exposed. -/
noncomputable def ofInt (z : ℤ) : Value := (ZFSet.ZFInt.into (z : ZFSet.ZFInt)).val

/-- The natural number `n`, as the integer `n`. TLA⁺ has one numeric type; `Nat` is a subset of
`Int`, not a separate encoding. -/
noncomputable def ofNat (n : ℕ) : Value := ofInt n

/-- `TRUE`. -/
def tru : Value := ZFSet.zftrue

/-- `FALSE`. -/
def fls : Value := ZFSet.zffalse

/-- The boolean `b`. -/
def ofBool (b : Bool) : Value := bif b then tru else fls

/-- The graph `{(start, v₁), (start + 1, v₂), …}` of a list of values indexed by consecutive
integers from `start`. The shape every TLA⁺ sequence and tuple value takes. -/
noncomputable def seqGraphFrom (start : ℕ) : List Value → Value
  | [] => ∅
  | v :: vs => insert (ZFSet.pair (ofNat start) v) (seqGraphFrom (start + 1) vs)

/-- A TLA⁺ sequence or tuple `⟨v₁, …, vₙ⟩`: the function `{1 ↦ v₁, …, n ↦ vₙ}`. Sequences and
tuples are the same kind of value; their two syntactic forms differ only in how they are checked. -/
noncomputable def ofSeq (vs : List Value) : Value := seqGraphFrom 1 vs

/-- A TLA⁺ tuple `⟨v₁, …, vₙ⟩`. Identical to `ofSeq`. -/
noncomputable def ofTuple : List Value → Value := ofSeq

/-- A TLA⁺ string: the sequence of its Unicode code points. `"abc"` is the tuple `⟨97, 98, 99⟩`,
matching TLA⁺'s treatment of a string as a tuple of characters. -/
noncomputable def ofString (s : String) : Value := ofSeq (s.toList.map λ c ↦ ofNat c.toNat)

/-- The graph `{(k₁, v₁), …}` of a record's fields, keyed by the string encodings of the field
names. -/
noncomputable def recordGraph : List (String × Value) → Value
  | [] => ∅
  | f :: fs => insert (ZFSet.pair (ofString f.1) f.2) (recordGraph fs)

/-- A TLA⁺ record `[a₁ ↦ v₁, …]`: the function from field-name strings to values. -/
noncomputable def ofRecord (fs : List (String × Value)) : Value := recordGraph fs

/-- A finite set literal `{v₁, …, vₙ}`. -/
def ofFinSet (vs : List Value) : Value := vs.foldr insert ∅

instance : Inhabited Value := ⟨(∅ : ZFSet)⟩

/-- `TRUE` and `FALSE` are distinct values. -/
@[simp] theorem tru_ne_fls : tru ≠ fls := by
  unfold tru fls; exact ZFSet.zftrue_ne_zffalse

/-- `FALSE` and `TRUE` are distinct values — the flipped orientation, for rewriting. -/
@[simp] theorem fls_ne_tru : fls ≠ tru := tru_ne_fls.symm

/-- The boolean encoding is injective. -/
@[simp] theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := by
  cases a <;> cases b <;>
    simp [ofBool, tru_ne_fls, tru_ne_fls.symm]

/-- The integer encoding is injective. -/
@[simp] theorem ofInt_inj {a b : ℤ} : ofInt a = ofInt b ↔ a = b := by
  refine ⟨λ h ↦ ?_, λ h ↦ h ▸ rfl⟩
  have hcast : ((a : ZFSet.ZFInt)) = ((b : ZFSet.ZFInt)) :=
    ZFSet.ZFInt.into.injective (Subtype.ext h)
  have := congrArg ZFSet.ZFInt.equivInt hcast
  rwa [ZFSet.ZFInt.equivInt_intCast, ZFSet.ZFInt.equivInt_intCast] at this

/-- The natural-number encoding is injective. -/
@[simp] theorem ofNat_inj {m n : ℕ} : ofNat m = ofNat n ↔ m = n := by
  rw [ofNat, ofNat, ofInt_inj, Int.natCast_inj]

/-- Membership in a finite set literal is list membership of the elements. -/
@[simp] theorem mem_ofFinSet {z : Value} {vs : List Value} : z ∈ ofFinSet vs ↔ z ∈ vs := by
  unfold ofFinSet
  induction vs with
  | nil => simp [ZFSet.notMem_empty]
  | cons v vs ih => simp [List.foldr, ZFSet.mem_insert_iff, ih, List.mem_cons]

/-- The pairs of a `seqGraphFrom`: one per list position, keyed by its index. -/
theorem mem_seqGraphFrom {z : Value} {start : ℕ} {vs : List Value} :
    z ∈ seqGraphFrom start vs ↔
      ∃ i, ∃ h : i < vs.length, z = ZFSet.pair (ofNat (start + i)) vs[i] := by
  induction vs generalizing start with
  | nil => simp [seqGraphFrom, ZFSet.notMem_empty]
  | cons v vs ih =>
    rw [seqGraphFrom, ZFSet.mem_insert_iff, ih]
    iff_rintro (rfl | ⟨i, hi, rfl⟩) ⟨i, hi, rfl⟩
    · exact ⟨0, by simp, by simp⟩
    · refine ⟨i + 1, by simpa using hi, ?_⟩
      have h : start + 1 + i = start + (i + 1) := by omega
      rw [h, List.getElem_cons_succ]
    · cases i with
      | zero => exact Or.inl (by simp)
      | succ k =>
        refine Or.inr ⟨k, by simpa using hi, ?_⟩
        have h : start + (k + 1) = start + 1 + k := by omega
        rw [h, List.getElem_cons_succ]

/-- The pairs of a `seqGraphFrom` starting at `1`, the sequence/tuple encoding. -/
theorem mem_ofSeq {z : Value} {vs : List Value} :
    z ∈ ofSeq vs ↔ ∃ i, ∃ h : i < vs.length, z = ZFSet.pair (ofNat (i + 1)) vs[i] := by
  rewrite [ofSeq, mem_seqGraphFrom]
  simp only [Nat.add_comm]

/-- The sequence/tuple encoding is injective. -/
theorem ofSeq_inj {vs ws : List Value} : ofSeq vs = ofSeq ws ↔ vs = ws := by
  refine ⟨λ h ↦ ?_, λ h ↦ h ▸ rfl⟩
  have key : ∀ (as bs : List Value), ofSeq as = ofSeq bs →
      ∀ i, ∀ hi : i < as.length, ∃ _ : i < bs.length, as[i] = bs[i] := by
    intro as bs hab i hi
    have hmem : ZFSet.pair (ofNat (i + 1)) as[i] ∈ ofSeq bs := by
      rw [← hab]; exact mem_ofSeq.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, he⟩ := mem_ofSeq.mp hmem
    rw [ZFSet.pair_inj, ofNat_inj] at he
    obtain ⟨hij, hv⟩ := he
    obtain rfl : i = j := by omega
    exact ⟨hj, hv⟩
  have hle : ∀ (as bs : List Value), ofSeq as = ofSeq bs → as.length ≤ bs.length := by
    intro as bs hab
    by_contra! hc
    obtain ⟨hj, _⟩ := key as bs hab bs.length (by omega)
    omega
  exact List.ext_getElem (Nat.le_antisymm (hle vs ws h) (hle ws vs h.symm))
    (λ i h1 _ ↦ (key vs ws h i h1).2)

/-- The pairs of a `recordGraph`: one per field, keyed by the string encoding of its name. -/
theorem mem_recordGraph {z : Value} {fs : List (String × Value)} :
    z ∈ recordGraph fs ↔ ∃ (k : String) (v : Value), (k, v) ∈ fs ∧ z = ZFSet.pair (ofString k) v := by
  induction fs with
  | nil => simp [recordGraph]
  | cons f fs ih =>
    obtain ⟨k, v⟩ := f
    rw [recordGraph, ZFSet.mem_insert_iff, ih]
    iff_rintro (rfl | ⟨k', v', hmem, rfl⟩) ⟨k', v', hmem, rfl⟩
    · exact ⟨k, v, by simp, rfl⟩
    · exact ⟨k', v', by simp [hmem], rfl⟩
    · rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
        exact Or.inl rfl
      · exact Or.inr ⟨k', v', hmem, rfl⟩

/-- `ZFSet` carries no canonical structural pretty-printer; a value prints as an opaque
placeholder. Present only so that a structure carrying a `Value` can still derive `Repr`. -/
instance : Repr Value := ⟨λ _ _ ↦ "(value : ZFSet)"⟩

/-- Value equality, classically. `ZFSet` equality is a universally quantified statement, so this
is noncomputable — harmless, since evaluation is a `Prop` relation. -/
noncomputable instance : DecidableEq Value := λ a b ↦ Classical.propDecidable (a = b)

noncomputable instance : BEq Value := ⟨λ a b ↦ decide (a = b)⟩

end Value

end ComputableTLAPlus

end
