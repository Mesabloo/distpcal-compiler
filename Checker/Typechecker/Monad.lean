import PlusCalCompiler.SurfaceTLAPlus.Syntax
import PlusCalCompiler.Passes.AnnotationChecker.Typechecker.Errors
import Mathlib.Control.Monad.Writer
import Extra.List

instance (priority := low) {σ σ'} {m} [MonadState σ m] [Monad m] : MonadState σ (StateT σ' m) where
  get := λ s ↦ (·, s) <$> get
  set x := λ s ↦ (·, s) <$> MonadState.set x
  modifyGet f := λ s ↦ modifyGet λ x ↦ Prod.map (·, s) id (f x)

def ExceptT.mapT.{u, v} {m n : Type u → Type v} {α β ε ε' : Type u}
  (f : m (Except ε α) → n (Except ε' β)) (x : ExceptT ε m α) :
    ExceptT ε' n β := f x

universe u v in
instance {ε ω : Type u} {M : Type u → Type v} [MonadWriter ω M] [Monad M] :
    MonadWriter ω (ExceptT ε M) where
  tell w := liftM (tell w : M PUnit.{u + 1})
  listen x := x.mapT λ m ↦ do
    let (a, w) ← listen m
    return (λ r ↦ (r, w)) <$> a
  pass x := x.mapT λ m ↦ pass.{u, v} do
    return match ← m with
    | .error e => (.error e, id)
    | .ok x => (.ok x.1, x.2)

@[simp]
theorem WriterT.run_pure.{u, v} {m : Type u → Type v} {α ω : Type u} [Monoid ω] [Monad m] (x : α) :
    WriterT.run (M := m) (pure x) = pure (x, (1 : ω)) := by
  rfl

@[simp]
theorem WriterT.run_bind.{u, v} {m : Type u → Type v} {α β ω : Type u} [Monoid ω] [Monad m] {x : WriterT ω m α} {f : α → WriterT ω m β} :
    WriterT.run (M := m) (x >>= f) = x.run >>= λ p ↦ Prod.map id (p.2 * ·) <$> (f p.1).run := by
  rfl

section
  open Std.Do

  universe u v

  instance {ω : Type u} {m : Type u → Type v} {ps} [Monoid ω] [WP m ps] : WP (WriterT ω m) (.arg ω ps) where
    wp x := PredTrans.pushArg λ w ↦ Prod.map id (w * ·) <$> WP.wp x.run

  instance WriterT.instWP {ω} [Monoid ω] : WP (Writer ω) (.arg ω .pure) :=
    inferInstanceAs (WP (WriterT ω Id) _)

  instance {ω : Type u} {m : Type u → Type v} {ps} [Monad m] [WPMonad m ps] [Monoid ω] : WPMonad (WriterT ω m) (.arg ω ps) where
    wp_pure x := by ext; simp [wp]
    wp_bind x f := by ext; simp [wp, WPMonad.wp_bind, mul_assoc]
end

-------------------

inductive InternalType.{u} : Type u
  | typ (_ : SurfaceTLAPlus.Typ)
  | mvar (_ : ULift Nat)

instance : CoeTail SurfaceTLAPlus.Typ InternalType where
  coe := .typ




/--
  The class of monads `m` with simple context lookup capabilities.
-/
class MonadContext.{u, v} (α β : Type _) (m : Type u → Type v) where
  /-- Lookup a variable in the local context, and return its entry if found. -/
  lookupDecl : α → m (Option β)
export MonadContext (lookupDecl)

instance {α β m} [BEq α] [Hashable α] [Monad m] [MonadReader (Std.HashMap α β) m] :
    MonadContext α β m where
  lookupDecl x := (Std.HashMap.get? · x) <$> read

instance {α β m} [BEq α] [Hashable α] [Monad m] [MonadState (Std.HashMap α β) m] :
    MonadContext α β m where
  lookupDecl x := (Std.HashMap.get? · x) <$> get

/--
  The class of monads `m` with local context capabilites.
  `α` is the type of variable identifiers, and `β` the type of data to be registered
  for variables.
-/
class MonadLocalContext.{u, v} (α β : Type _) (m : Type u → Type v) extends MonadContext α β m where
  /-- Execute an action in a local context augmented with a variable entry. -/
  withLocalDecl {γ} : α → β → m γ → m γ
export MonadLocalContext (withLocalDecl)

def withLocalDecls {α β γ} {m} [MonadLocalContext α β m] (decls : Array (α × β)) (act : m γ) : m γ :=
  let rec go (i : ℕ) (h : i ≤ decls.size) : m γ :=
      if _h : i = decls.size then
        act
      else
        let (k, v) := decls[i]
        withLocalDecl k v (go (i + 1) (by grind only))
  go 0 (by grind only)

instance {α β m} [BEq α] [Hashable α] [Monad m] [MonadReader (Std.HashMap α β) m] [MonadWithReader (Std.HashMap α β) m] :
    MonadLocalContext α β m where
  withLocalDecl x y := withReader (Std.HashMap.insert · x y)

instance {α β m} [BEq α] [Hashable α] [Monad m] [MonadState (Std.HashMap α β) m] :
    MonadLocalContext α β m where
  withLocalDecl x y act := do
    let σ ← modifyGet λ σ ↦ (σ, σ.insert x y)
    act <* MonadState.set σ

class MonadGlobalContext.{u, v} (α β : Type _) (m : Type u → Type v) extends MonadLocalContext α β m where
  /-- Insert a new declaration into the global context. -/
  addDecl : α → β → m PUnit
export MonadGlobalContext (addDecl)

instance {α β m} [BEq α] [Hashable α] [Monad m] [MonadState (Std.HashMap α β) m] :
    MonadGlobalContext α β m where
  addDecl x y := modify (Std.HashMap.insert · x y)



class MonadMetavarContext.{u} (α : outParam (Type u)) (m : Type u → Type u) where
  /-- The type used to identify metavariables. -/
  MVarId : Type u

  /-- Creates a new fresh metavariable in the context. -/
  mkFreshMVar : m MVarId
  /--
    Solve a metavariable, by assigning it a value.
    This function is expected to do nothing if the metavariable is already assigned.
  -/
  assignMVar : MVarId → α → m PUnit
  /-- Is a metavariable already assigned? -/
  assigned? : MVarId → m (Option α)
export MonadMetavarContext (MVarId mkFreshMVar assignMVar assigned?)


structure MetavarContext α where
  private mvars : Array (Option α)
  deriving BEq, Hashable

instance {α} : EmptyCollection (MetavarContext α) where
  emptyCollection := ⟨∅⟩

instance {β m} [Monad m] [MonadState (MetavarContext β) m] : MonadMetavarContext β m where
  MVarId := ULift Nat

  mkFreshMVar := modifyGet λ ⟨vars⟩ ↦ ⟨⟨vars.size⟩, ⟨vars.push .none⟩⟩
  assignMVar v x :=
    modify λ ⟨vars⟩ ↦
      match h : vars[v.down]? with
      | none | some (some _) => ⟨vars⟩
      | some none => ⟨vars.set v.down x (of_getElem?_eq_some (c := vars) h)⟩
  assigned? v := do
    return (← get).mvars[v.down]?.join
attribute [reducible] MVarId

-------------

class abbrev MonadTCExpr.{u} (m : Type u → Type u) :=
  MonadLocalContext String InternalType m,
  MonadMetavarContext InternalType m,
  MonadExcept TCError m,
  MonadWriter (List TCWarning) m

class abbrev MonadTC.{u} (m : Type u → Type u) :=
  MonadGlobalContext String InternalType m,
  MonadMetavarContext InternalType m,
  MonadExcept TCError m,
  MonadWriter (List TCWarning) m

instance (priority := low) {m} [MonadTC m] : MonadTCExpr m where

-------------

/-- The typechecker monad, for expressions. -/
abbrev TCExpr.{u} (α : Type u) : Type u :=
  ReaderT
    (Std.HashMap String SurfaceTLAPlus.Typ)
    (ExceptT
      TCError
      (WriterT
        (List TCWarning)
        Id))
    α

nonrec abbrev TCExpr.run {α} (Γ : Std.HashMap String SurfaceTLAPlus.Typ) (x : TCExpr α) :
    Except TCError α × List TCWarning :=
  x.run Γ |>.run |>.run |>.run

instance (priority := high) : Monad TCExpr := inferInstance

instance (priority := high) : MonadLocalContext String SurfaceTLAPlus.Typ TCExpr := inferInstance

instance (priority := high) : MonadExcept TCError TCExpr := inferInstance

instance (priority := high) : MonadWriter (List TCWarning) TCExpr := inferInstance

instance (priority := high) : Std.Do.WP TCExpr (.arg (Std.HashMap String SurfaceTLAPlus.Typ) <| .except TCError <| .arg (List TCWarning) .pure) :=
  inferInstance

instance (priority := high) : Std.Do.WPMonad TCExpr (.arg (Std.HashMap String SurfaceTLAPlus.Typ) <| .except TCError <| .arg (List TCWarning) .pure) :=
  inferInstance

----------------

/-- The typechecker monad. -/
abbrev TC.{u} (α : Type u) : Type u :=
  StateT
    (Std.HashMap String InternalType)
    (StateT
      (MetavarContext InternalType)
      (ExceptT
        TCError
        (WriterT
          (List TCWarning)
          Id)))
    α

nonrec abbrev TC.run {α} (Γ : Std.HashMap String InternalType) (x : TC α) :
    Except TCError ((α × Std.HashMap String InternalType) × MetavarContext InternalType) × List TCWarning :=
  x.run Γ |>.run ∅ |>.run |>.run |>.run

-- def TC.ofTCExpr {α} (act : )

instance (priority := high) : Monad TC := inferInstance

instance (priority := high) : MonadLocalContext String InternalType TC := inferInstance

instance (priority := high) : MonadGlobalContext String InternalType TC := inferInstance

instance (priority := high) : MonadMetavarContext InternalType TC := inferInstance

instance : BEq (MVarId TC) := inferInstanceAs (BEq (ULift Nat))

deriving instance Hashable for ULift

instance : Hashable (MVarId TC) := inferInstanceAs (Hashable (ULift Nat))

instance (priority := high) : MonadExcept TCError TC := inferInstance

instance (priority := high) : MonadWriter (List TCWarning) TC := inferInstance

instance (priority := high) : Std.Do.WP TC (.arg (Std.HashMap String InternalType) <| .arg (MetavarContext InternalType) <| .except TCError <| .arg (List TCWarning) .pure) :=
  inferInstance

instance (priority := high) : Std.Do.WPMonad TC (.arg (Std.HashMap String InternalType) <| .arg (MetavarContext InternalType) <| .except TCError <| .arg (List TCWarning) .pure) :=
  inferInstance

partial def TC.mvarSolved? (m : MVarId TC) : TC (Option InternalType) := do
  go [m] (List.cons_ne_nil _ _) (← getThe (MetavarContext InternalType)).mvars
where
  go (stack : List (MVarId TC)) (_ : stack ≠ []) (vars : Array (Option InternalType)) : TC (Option InternalType) :=
    let m :: stack' := stack
    if stack'.contains m then
      throw <| .metavarCycle m.down
    else
      match vars[m.down]? with
      | .none | .some .none => return .none
      | .some (.some (.mvar n)) => go (n :: stack) (List.cons_ne_nil _ _) vars
      | .some (.some (.typ τ)) => return .some τ
