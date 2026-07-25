module

meta import CustomPrelude
public import Std.Data.HashMap.Basic

public section

/-- Which backend the compiler is asked to target, per the `-t`/`--target` flag. -/
inductive Target
  | go
  | join
  deriving Repr, DecidableEq, Inhabited

/--
  The fully-parsed CLI flag surface, computed once by the driver from `Cli.Parsed` and
  threaded to every pass via `MonadReaderOf FlagsEnv m`, rather than an opaque `getFlag`
  action: flags aren't uniformly `Option String` (boolean `-f`/`-W` flags vs. valued
  `-d<name>=<value>` options vs. `-o`/`-t`/`-I`'s own typed values), and the project's
  `Std.Do.WP`-based proofs need a transparent Reader effect to reason about, not an opaque one.
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

/-!
  There is deliberately no `MonadReaderOf FlagsEnv IO` instance backed by a global `IO.Ref`: a
  `FlagsEnv` belongs to *one* compile, not to the process. `Driver/Pipeline.lean`'s `runPipeline`
  takes one and supplies it as a real `ReaderT` layer, so two compiles running concurrently in the
  same process (the regression runner does exactly this) cannot see each other's flags. The CLI
  builds its `FlagsEnv` once from `Cli.Parsed` and hands it over the same way.
-/

end
