module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Statement

@[expose] public section

/-!
  What a step leaves alone.

  The refinement invariant pins *one* resolved channel key, `⟨c.name, cpath⟩`, and `cpath` is read
  out of the **source's** memory. So a source step that moved that key would move the key the
  invariant names — and at the algorithm level, where each instance's key is what its inbox is
  accounted against, a moved key leaves the old key's drained prefix belonging to nobody. The
  algorithm-level invariant would then be false, not merely unprovable.

  It cannot happen, and `Fresh` is why: a statement writes at most one name, and `Fresh` says that
  name is not one the mailbox channel is indexed by. This file is that argument, one level at a time
  — statement, block, branch — ending at `AtomicBranch.reducing'_evalArgs`, which is the form the
  process layer needs.

  Stated over `Statement.writtenName?` rather than over `Fresh` directly: locality is a fact about
  the *language*, freshness a condition this pass arranges, and keeping them apart means the
  induction is done once against the smaller statement.
-/

namespace Guarded2Network

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep)
open GuardedPlusCal (Block ChanKey EvalStep LocalState' Trace)

variable {V : Type} [ExprSemantics V]

/-- **One statement writes one name.** Every other binding is exactly where it was.

`Statement.writtenName?` is the whole content: the three constructors that answer `.some` are the
three that touch memory (`assign` and `receive` through `Memory.update`, `with` through an insert),
and the rest are `.none` and leave the memory alone outright. -/
theorem Statement.reducing'_locality {g b : Bool}
    {S : ComputableGuardedPlusCal.Statement g b} {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      GuardedPlusCal.Statement.reducing' S)
    {y : String} (hy : ∀ x, Statement.writtenName? S = .some x → y ≠ x) :
    σ'.mem.lookup y = σ.mem.lookup y := by
  obtain ⟨M₁, F₁, l₁⟩ := σ
  obtain ⟨M₂, F₂, l₂⟩ := σ'
  cases S with
  | skip =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM; subst hσ'
    injection hpost with hM' _
    subst hM'
    rfl
  | goto label =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _⟩, _, hpost, _⟩ := step
    injection hM with hM _
    subst hM
    rw [hσ'] at hpost
    injection hpost with hM' _
    subst hM'
    rfl
  | print e =>
    obtain ⟨_, _, ⟨M, F, _, _, hM, hσ', _, _, _⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM; subst hσ'
    injection hpost with hM' _
    subst hM'
    rfl
  | assert e =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _, _⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM; subst hσ'
    injection hpost with hM' _
    subst hM'
    rfl
  | multicast c filter =>
    obtain ⟨_, -, hmem, -⟩ := step
    exact hmem.elim
  | await e =>
    obtain ⟨_, _, ⟨M, F, hM, hσ', _, _⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM; subst hσ'
    injection hpost with hM' _
    subst hM'
    rfl
  | send c e =>
    obtain ⟨_, _, ⟨M, F, _, _, _, _, _, _, _, _, hM, hσ', _⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM; subst hσ'
    injection hpost with hM' _
    subst hM'
    rfl
  | assign r e =>
    obtain ⟨_, _, ⟨M, F, M', _, _, _, _, hupd, hM, hσ', _⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM; subst hσ'
    injection hpost with hM' _
    subst hM'
    exact Memory.lookup_update_ne hupd (hy r.name rfl)
  | receive c r coe =>
    obtain ⟨_, _, ⟨M, F, M', _, _, _, _, _, _, _, _, _, hupd, hM, hσ', _⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM; subst hσ'
    injection hpost with hM' _
    subst hM'
    exact Memory.lookup_update_ne hupd (hy r.name rfl)
  | «with» x ann bound e =>
    obtain ⟨_, _, ⟨M, F, v, _, _, hM, _, hb⟩, hpost, _⟩ := step
    injection hM with hM _
    subst hM
    cases bound with
    | true =>
      subst hb
      injection hpost with hM' _
      subst hM'
      exact Finmap.lookup_insert_of_ne _ (hy x rfl)
    | false =>
      obtain ⟨u, _, rfl⟩ := hb
      injection hpost with hM' _
      subst hM'
      exact Finmap.lookup_insert_of_ne _ (hy x rfl)

/-- **A block writes only what its statements write.** The same left-to-right induction
`actionBlock_refines` runs, with one `Statement.reducing'_locality` per step and the intermediate
lookups chained. -/
theorem Block.reducing'_locality {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      Block.reducing (β := λ _ ↦ LocalState' V) (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing') B)
    {y : String}
    (hbegin : ∀ S ∈ B.begin, ∀ x, Statement.writtenName? S = .some x → y ≠ x)
    (hlast : ∀ x, Statement.writtenName? B.last = .some x → y ≠ x) :
    σ'.mem.lookup y = σ.mem.lookup y := by
  induction B using Block.cons_end_induct generalizing σ σ' ε with
  | «end» S =>
    rw [Block.reducing_end] at step
    exact Statement.reducing'_locality step hlast
  | cons S B IH =>
    rw [Block.reducing_cons] at step
    obtain ⟨σ'', ε₁, ε₂, hhead, htail, rfl⟩ := step
    rw [IH htail (λ S' hS' ↦ hbegin S' (List.mem_cons_of_mem _ hS')) hlast]
    exact Statement.reducing'_locality hhead (hbegin S List.mem_cons_self)

/-- **And a branch writes only what its two blocks write.** A branch is its precondition composed
with its action; a missing precondition is `Relation.Idle`, which writes nothing at all. -/
theorem AtomicBranch.reducing'_locality {Br : ComputableGuardedPlusCal.AtomicBranch}
    {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      GuardedPlusCal.AtomicBranch.reducing' Br)
    {y : String}
    (hpre : ∀ B', Br.precondition = .some B' →
      ∀ S ∈ Block.toList B', ∀ x, Statement.writtenName? S = .some x → y ≠ x)
    (hbegin : ∀ S ∈ Br.action.begin, ∀ x, Statement.writtenName? S = .some x → y ≠ x)
    (hlast : ∀ x, Statement.writtenName? Br.action.last = .some x → y ≠ x) :
    σ'.mem.lookup y = σ.mem.lookup y := by
  obtain ⟨σ'', ε₁, ε₂, hpres, hact, rfl⟩ := step
  rw [Block.reducing'_locality hact hbegin hlast]
  match hp : Br.precondition with
  | .none =>
    rw [hp] at hpres
    obtain ⟨rfl, -⟩ := hpres
    rfl
  | .some B' =>
    rw [hp] at hpres
    refine Block.reducing'_locality hpres (λ S hS ↦ hpre B' hp S ?_) (hpre B' hp _ ?_) <;>
      simp only [Block.toList, List.concat_eq_append]
    · exact List.mem_append_left _ hS
    · exact List.mem_append_right _ List.mem_cons_self

/-- **The key the invariant pins cannot move.** A branch whose every statement is `Fresh` for the
mailbox leaves the mailbox channel's resolved path exactly where it was: a statement writes one
name, and `Fresh`'s third clause says that name is not one the channel is indexed by.

This is what the algorithm level needs and has no other source for. Each instance's inbox is
accounted against *its* key, so a step that moved the key would leave the old key's drained prefix
belonging to no instance at all — `algRelatesTo` would be false after the step, not merely
unprovable. Every other hypothesis this pass carries is about keeping a proof going; this one is
about the statement being true. -/
theorem AtomicBranch.reducing'_evalArgs {mbox : Mailbox} {c : ComputableGuardedPlusCal.Ref}
    {inbox : String} (hmb : mbox = .some (c, inbox))
    {Br : ComputableGuardedPlusCal.AtomicBranch}
    (hpre : ∀ B', Br.precondition = .some B' → ∀ S ∈ Block.toList B', Fresh mbox S)
    (hbegin : ∀ S ∈ Br.action.begin, Fresh mbox S) (hlast : Fresh mbox Br.action.last)
    {σ σ' : LocalState' V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState' V × Trace V × LocalState' V) ∈
      GuardedPlusCal.AtomicBranch.reducing' Br)
    {path : List (PathStep V)} :
    Ref.EvalArgs σ.mem c path ↔ Ref.EvalArgs σ'.mem c path := by
  refine Ref.EvalArgs.congr_of_agree (λ y hy ↦ (AtomicBranch.reducing'_locality step ?_ ?_ ?_).symm)
  · intro B' hB' S hS _ hx
    rintro rfl
    exact (hpre B' hB' S hS c inbox hmb).2.2.1 _ hx hy
  · intro S hS _ hx
    rintro rfl
    exact (hbegin S hS c inbox hmb).2.2.1 _ hx hy
  · intro _ hx
    rintro rfl
    exact (hlast c inbox hmb).2.2.1 _ hx hy

end Guarded2Network

end
