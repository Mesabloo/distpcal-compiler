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
  — statement, block, branch — ending at `AtomicBranch.reducing_evalArgs`, which is the form the
  process layer needs.

  Stated over `Statement.writtenName?` rather than over `Fresh` directly: locality is a fact about
  the *language*, freshness a condition this pass arranges, and keeping them apart means the
  induction is done once against the smaller statement.
-/

namespace Guarded2Network

universe u

open ComputableTLAPlus (ExprSemantics Expression Memory PathStep OperatorEnv Model)
open GuardedPlusCal (Block ChanKey EvalStep LocalState Trace)

variable {V : Type u} [ExprSemantics V] {Ξ : OperatorEnv} {Ω : Model V}

/-- **One statement writes one name.** Every other binding is exactly where it was.

`Statement.writtenName?` is the whole content: the three constructors that answer `.some` are the
three that touch memory (`assign` and `receive` through `Memory.update`, `with` through an insert),
and the rest are `.none` and leave the memory alone outright. -/
theorem Statement.reducing_locality {g b : Bool}
    {S : ComputableGuardedPlusCal.Statement g b} {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      GuardedPlusCal.Statement.reducing Ξ Ω S)
    {y : String} (hy : ∀ x, Statement.writtenName? S = .some x → y ≠ x) :
    σ'.mem.lookup y = σ.mem.lookup y := by
  cases S with
  | skip => obtain ⟨M, F, rfl, rfl, -⟩ := step; rfl
  | goto label => obtain ⟨M, F, rfl, rfl, -⟩ := step; rfl
  | print e => obtain ⟨M, F, v, p, rfl, rfl, -, -, -⟩ := step; rfl
  | assert e => obtain ⟨M, F, rfl, rfl, -, -⟩ := step; rfl
  | multicast c filter => exact step.elim
  | await e => obtain ⟨M, F, rfl, rfl, -, -⟩ := step; rfl
  | send c e => obtain ⟨M, F, v, cpath, vs, p, -, -, -, -, rfl, rfl, -⟩ := step; rfl
  | assign r e =>
    obtain ⟨M, F, M', v, rpath, -, -, hupd, rfl, rfl, -⟩ := step
    exact Memory.lookup_update_ne hupd (hy r.name rfl)
  | receive c r coe =>
    obtain ⟨M, F, M', cpath, rpath, v, v', vs, -, -, -, -, hupd, rfl, rfl, -⟩ := step
    exact Memory.lookup_update_ne hupd (hy r.name rfl)
  | «with» x ann bound e =>
    obtain ⟨M, F, v, -, -, rfl, -, hb⟩ := step
    cases bound with
    | true => obtain rfl := hb; exact Finmap.lookup_insert_of_ne _ (hy x rfl)
    | false =>
      obtain ⟨u, -, rfl⟩ := hb
      exact Finmap.lookup_insert_of_ne _ (hy x rfl)

/-- **A statement *list* writes only what its statements write** — `Block.reducing_locality` on the
list form the precondition walk is stated against. -/
theorem Statement.listReducing_locality {g : Bool}
    {A : List (ComputableGuardedPlusCal.Statement g false)} {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      GuardedPlusCal.Statement.listReducing Ξ Ω A)
    {y : String}
    (h : ∀ S ∈ A, ∀ x, Statement.writtenName? S = .some x → y ≠ x) :
    σ'.mem.lookup y = σ.mem.lookup y := by
  induction A generalizing σ σ' ε with
  | nil =>
    rw [GuardedPlusCal.Statement.listReducing_nil] at step
    obtain ⟨rfl, rfl⟩ := step
    rfl
  | cons S A IH =>
    rw [GuardedPlusCal.Statement.listReducing_cons] at step
    obtain ⟨σ'', ε₁, ε₂, hhead, htail, rfl⟩ := step
    rw [IH htail (λ S' hS' ↦ h S' (List.mem_cons_of_mem _ hS'))]
    exact Statement.reducing_locality hhead (h S List.mem_cons_self)

/-- **A block writes only what its statements write.** The same left-to-right induction
`actionBlock_refines` runs, with one `Statement.reducing_locality` per step and the intermediate
lookups chained. -/
theorem Block.reducing_locality {g b : Bool}
    {B : Block (ComputableGuardedPlusCal.Statement g) b} {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      Block.reducing (λ ⦃_⦄ ↦ GuardedPlusCal.Statement.reducing Ξ Ω) B)
    {y : String}
    (hbegin : ∀ S ∈ B.begin, ∀ x, Statement.writtenName? S = .some x → y ≠ x)
    (hlast : ∀ x, Statement.writtenName? B.last = .some x → y ≠ x) :
    σ'.mem.lookup y = σ.mem.lookup y := by
  induction B using Block.cons_end_induct generalizing σ σ' ε with
  | «end» S =>
    rw [Block.reducing_end] at step
    exact Statement.reducing_locality step hlast
  | cons S B IH =>
    rw [Block.reducing_cons] at step
    obtain ⟨σ'', ε₁, ε₂, hhead, htail, rfl⟩ := step
    rw [IH htail (λ S' hS' ↦ hbegin S' (List.mem_cons_of_mem _ hS')) hlast]
    exact Statement.reducing_locality hhead (hbegin S List.mem_cons_self)

/-- **And a branch writes only what its two blocks write.** A branch is its precondition composed
with its action; a missing precondition is `Relation.Idle`, which writes nothing at all. -/
theorem AtomicBranch.reducing_locality {Br : ComputableGuardedPlusCal.AtomicBranch}
    {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      GuardedPlusCal.AtomicBranch.reducing Ξ Ω Br)
    {y : String}
    (hpre : ∀ B', Br.precondition = .some B' →
      ∀ S ∈ Block.toList B', ∀ x, Statement.writtenName? S = .some x → y ≠ x)
    (hbegin : ∀ S ∈ Br.action.begin, ∀ x, Statement.writtenName? S = .some x → y ≠ x)
    (hlast : ∀ x, Statement.writtenName? Br.action.last = .some x → y ≠ x) :
    σ'.mem.lookup y = σ.mem.lookup y := by
  obtain ⟨σ'', ε₁, ε₂, hpres, hact, rfl⟩ := step
  rw [Block.reducing_locality hact hbegin hlast]
  match hp : Br.precondition with
  | .none =>
    rw [hp] at hpres
    obtain ⟨rfl, -⟩ := hpres
    rfl
  | .some B' =>
    rw [hp] at hpres
    refine Block.reducing_locality hpres (λ S hS ↦ hpre B' hp S ?_) (hpre B' hp _ ?_) <;>
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
theorem AtomicBranch.reducing_evalArgs (hΞ : Ξ.WellScoped) {mbox : Mailbox}
    {c : ComputableGuardedPlusCal.Ref}
    {inbox : String} (hmb : mbox = .some (c, inbox))
    {Br : ComputableGuardedPlusCal.AtomicBranch}
    (hpre : ∀ B', Br.precondition = .some B' → ∀ S ∈ Block.toList B', Fresh mbox S)
    (hbegin : ∀ S ∈ Br.action.begin, Fresh mbox S) (hlast : Fresh mbox Br.action.last)
    {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      GuardedPlusCal.AtomicBranch.reducing Ξ Ω Br)
    {path : List (PathStep V)} :
    Ref.EvalArgs Ξ Ω σ.mem c path ↔ Ref.EvalArgs Ξ Ω σ'.mem c path := by
  refine Ref.EvalArgs.congr_of_agree hΞ (λ y hy ↦ (AtomicBranch.reducing_locality step ?_ ?_ ?_).symm)
  · intro B' hB' S hS _ hx
    rintro rfl
    exact (hpre B' hB' S hS c inbox hmb).2.2.1 _ hx hy
  · intro S hS _ hx
    rintro rfl
    exact (hbegin S hS c inbox hmb).2.2.1 _ hx hy
  · intro _ hx
    rintro rfl
    exact (hlast c inbox hmb).2.2.1 _ hx hy

/-- **A guard or a plain assignment leaves the channels untouched** — the only Network statements
that reach a fifo are `send` and `multicast`, and the compiled precondition together with its
consumption assignments is neither. -/
theorem NetworkPlusCal.Statement.reducing_fifos_of_guardOrAssign
    {S : ComputableNetworkPlusCal.Statement true false} {σ σ' : LocalState V} {ε : Trace V}
    (hS : (∃ e, S = .await e) ∨ ∃ x ann bound e, S = .with x ann bound e)
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      NetworkPlusCal.Statement.reducing Ξ Ω S) :
    σ'.fifos = σ.fifos := by
  rcases hS with ⟨e, rfl⟩ | ⟨x, ann, bound, e, rfl⟩
  · obtain ⟨M, F, rfl, rfl, -, -⟩ := NetworkPlusCal.Statement.reducing.await.elim step; rfl
  · obtain ⟨M, F, v, u, -, -, -, rfl, rfl, -⟩ := NetworkPlusCal.Statement.reducing.with.iff.mp step
    rfl

@[inherit_doc NetworkPlusCal.Statement.reducing_fifos_of_guardOrAssign]
theorem NetworkPlusCal.Statement.reducing_fifos_assign
    {r : ComputableGuardedPlusCal.Ref} {e : ComputablePlusCal.Expression}
    {σ σ' : LocalState V} {ε : Trace V}
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      NetworkPlusCal.Statement.reducing Ξ Ω (.assign r e)) :
    σ'.fifos = σ.fifos := by
  obtain ⟨M, F, M', v, rpath, -, -, -, rfl, rfl, -⟩ := NetworkPlusCal.Statement.reducing.assign.elim step
  rfl

/-- The list form for the compiled guards. -/
theorem NetworkPlusCal.Statement.listReducing_fifos_of_guards
    {A : List (ComputableNetworkPlusCal.Statement true false)} {σ σ' : LocalState V} {ε : Trace V}
    (hA : ∀ S ∈ A, (∃ e, S = .await e) ∨ ∃ x ann bound e, S = .with x ann bound e)
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      NetworkPlusCal.Statement.listReducing Ξ Ω A) :
    σ'.fifos = σ.fifos := by
  induction A generalizing σ σ' ε with
  | nil => rw [NetworkPlusCal.Statement.listReducing_nil] at step; obtain ⟨rfl, rfl⟩ := step; rfl
  | cons S A IH =>
    rw [NetworkPlusCal.Statement.listReducing_cons] at step
    obtain ⟨σ'', ε₁, ε₂, hhead, htail, rfl⟩ := step
    rw [IH (λ S' hS' ↦ hA S' (List.mem_cons_of_mem _ hS')) htail,
      NetworkPlusCal.Statement.reducing_fifos_of_guardOrAssign (hA S List.mem_cons_self) hhead]

/-- And for the consumption assignments. -/
theorem NetworkPlusCal.Statement.listReducing_fifos_of_assigns
    {A : List (ComputableNetworkPlusCal.Statement false false)} {σ σ' : LocalState V} {ε : Trace V}
    (hA : ∀ S ∈ A, ∃ r e, S = .assign r e)
    (step : (⟨σ, ε, σ'⟩ : LocalState V × Trace V × LocalState V) ∈
      NetworkPlusCal.Statement.listReducing Ξ Ω A) :
    σ'.fifos = σ.fifos := by
  induction A generalizing σ σ' ε with
  | nil => rw [NetworkPlusCal.Statement.listReducing_nil] at step; obtain ⟨rfl, rfl⟩ := step; rfl
  | cons S A IH =>
    rw [NetworkPlusCal.Statement.listReducing_cons] at step
    obtain ⟨σ'', ε₁, ε₂, hhead, htail, rfl⟩ := step
    obtain ⟨r, e, rfl⟩ := hA S List.mem_cons_self
    rw [IH (λ S' hS' ↦ hA S' (List.mem_cons_of_mem _ hS')) htail,
      NetworkPlusCal.Statement.reducing_fifos_assign hhead]

end Guarded2Network

end
