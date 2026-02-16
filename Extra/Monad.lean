/--
  Execute a guard `p` in the monad `m`.
  If its result is `false`, fail with `Alternative.failure`, otherwise return `Unit.unit`.
-/
def guardM.{v} {m : Type → Type v} [Monad m] [Alternative m] (p : m Bool) : m Unit :=
  p >>= (guard ·)
