module

public import Std.Do

@[expose] public section

/-!
  `Std.Do` spec lemmas the toolchain does not ship.

  `Std.Do.Triple.SpecLemmas` covers `forIn`/`forIn'`/`foldlM` over lists, arrays, ranges and
  iterators — every shape a `for` loop elaborates to. It does not cover `List.mapM`, which is what a
  pass written with `mapM` rather than with `for` actually calls, and which `mvcgen` therefore walks
  straight past.
-/

namespace Std.Do

universe u v

variable {m : Type u → Type v} {ps : PostShape.{u}}

/-- `List.mapM`'s loop-invariant spec, in the same shape `Spec.foldlM_list` has: an `Invariant`
indexed by how much of the list has been consumed, plus one obligation per element.

The invariant's second component is the list of results collected *so far, in order* — the natural
thing to state an invariant about. `List.mapM` itself accumulates them reversed
(`List.mapM_eq_reverse_foldlM_cons`), and undoing that here is the whole content of the proof.

Registered `@[spec]`, so `mvcgen invariants ⟨…⟩` picks it up on a `mapM` exactly as it does on a
`for` loop. -/
@[spec]
theorem Spec.mapM_list [Monad m] [LawfulMonad m] [WPMonad m ps] {α β : Type u}
    {xs : List α} {f : α → m β} (inv : Invariant xs (List β) ps)
    (step : ∀ pref cur suff (h : xs = pref ++ cur :: suff) bs,
      ⦃inv.1 (⟨pref, cur :: suff, h.symm⟩, bs)⦄
        f cur
      ⦃(λ b ↦ inv.1 (⟨pref ++ [cur], suff, by simp [h]⟩, bs ++ [b]), inv.2)⦄) :
    ⦃inv.1 (⟨[], xs, rfl⟩, [])⦄
      xs.mapM f
    ⦃(λ bs ↦ inv.1 (⟨xs, [], by simp⟩, bs), inv.2)⦄ := by
  rw [List.mapM_eq_reverse_foldlM_cons]
  apply Spec.map'
  apply Spec.foldlM_list
    (inv := (λ p : List.Cursor xs × List β ↦ inv.1 (p.1, p.2.reverse), inv.2))
  intro pref cur suff h bs
  apply Spec.map'
  have hstep := step pref cur suff h bs.reverse
  simpa only [List.reverse_cons] using hstep

end Std.Do

end
