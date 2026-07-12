module

meta import CustomPrelude
public import Std.Data.HashMap.Basic

public section

/-- Which backend the compiler is asked to target, per the `-t`/`--target` flag (§2). -/
inductive Target
  | go
  | join
  deriving Repr, DecidableEq, Inhabited

/--
  The fully-parsed CLI flag surface (`PLAN.md` §2), computed once by the driver from
  `Cli.Parsed` and threaded to every pass via `MonadReaderOf FlagsEnv m`, rather than an
  opaque `getFlag` action: flags aren't uniformly `Option String` (boolean `-f`/`-W` flags
  vs. valued `-d<name>=<value>` options vs. `-o`/`-t`/`-I`'s own typed values), and an
  opaque, unconstrained action would give the project's `Std.Do.WP`-based proofs nothing
  to reason about, unlike this transparent Reader effect.
-/
structure FlagsEnv where
  /-- `-d<name>[=<value>]` debugging options. -/
  debug : Std.HashMap String (Option String) := {}
  /-- `-f<name>[=<value>]` feature/config toggles. -/
  features : Std.HashMap String (Option String) := {}
  /-- `-W<name>` / `-Wno-<name>` per-warning enable/disable. -/
  warnings : Std.HashMap String Bool := {}
  /-- `-o`/`--output`. -/
  output : Option System.FilePath := none
  /-- `-t`/`--target go|join`. -/
  target : Target := .go
  /-- `-I <path>`, module search path (may be repeated). -/
  searchPath : List System.FilePath := []
  deriving Inhabited

namespace FlagsEnv

variable {m : Type → Type} [Monad m] [MonadReaderOf FlagsEnv m]

/-- Is `-d<name>` (with or without a value) present? -/
def getDebugFlag (name : String) : m Bool := do
  return (← readThe FlagsEnv).debug.contains name

/-- The value attached to `-d<name>=<value>`, if any (also `none` if `-d<name>` was given without a value). -/
def getDebugOption (name : String) : m (Option String) := do
  return (← readThe FlagsEnv).debug.get? name |>.join

/-- Is `-f<name>` (with or without a value) present? -/
def getFeatureFlag (name : String) : m Bool := do
  return (← readThe FlagsEnv).features.contains name

/-- The value attached to `-f<name>=<value>`, if any. -/
def getFeatureOption (name : String) : m (Option String) := do
  return (← readThe FlagsEnv).features.get? name |>.join

/-- Is warning `name` enabled? Defaults to `true` (warnings are on unless `-Wno-<name>` was given). -/
def isWarningEnabled (name : String) : m Bool := do
  return (← readThe FlagsEnv).warnings.getD name true

end FlagsEnv

/--
  Backing store for `MonadReaderOf FlagsEnv IO`, populated once at CLI startup (Phase 2)
  from `Cli.Parsed` — every pass, and the driver itself, reads flags through this same
  instance rather than a value threaded by hand.
-/
initialize flagsRef : IO.Ref FlagsEnv ← IO.mkRef {}

instance : MonadReaderOf FlagsEnv IO where
  read := flagsRef.get

end
