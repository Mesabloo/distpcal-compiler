module

public section

/--
  Execute a guard `p` in the monad `m`.
  If its result is `false`, fail with `Alternative.failure`, otherwise return `Unit.unit`.
-/
def guardM.{v} {m : Type → Type v} [Monad m] [Alternative m] (p : m Bool) : m Unit :=
  p >>= (guard ·)

/-- Lift an `IO.Ref α` into a `MonadStateOf α IO` instance, forwarding `get`/`set`/`modifyGet`
directly to the ref. -/
@[implicit_reducible]
def IO.Ref.toMonadStateOf {α} (ref : IO.Ref α) : MonadStateOf α IO where
  get := ref.get
  set := ref.set
  modifyGet := ref.modifyGet

end
