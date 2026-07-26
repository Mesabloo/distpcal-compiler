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
  /-- `-d<name>[:<value>]` debugging options. -/
  debug : Std.HashMap String (Option String) := {}
  /-- `-f<name>[:<value>]` feature/config toggles. -/
  features : Std.HashMap String (Option String) := {}
  /-- `-W<name>` / `-Wno-<name>` per-warning enable/disable. -/
  warnings : Std.HashMap String Bool := {}
  /-- `-X<name>[:<value>]` backend options. Named for the target rather than the compiler: what
  is valid depends on which backend `-t` selects. -/
  targetOptions : Std.HashMap String (Option String) := {}
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

/-- The value attached to `-X<name>=<value>`, if any (also `none` for a valueless `-X<name>`). -/
def getTargetOption (name : String) : m (Option String) := do
  return (← readThe FlagsEnv).targetOptions.get? name |>.join

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

/-! Where `-d dump-*` debugging artifacts go, and how they get written. Shared because both the
driver (`Driver/Modules.lean`, which dumps the per-module stages it runs — tokens, CST,
desugared, typed) and the CLI (`Fugue.lean`, which dumps the pipeline stages that run past the
driver — computable, guarded, network) write them, and the two must agree on the directory. -/

/-- Default value of `-ddump-dir:<path>`. -/
def defaultDumpDir : System.FilePath := ".fugue/debug"

/-- The directory `-d dump-*` artifacts are written to: `-ddump-dir:<path>` if given,
`defaultDumpDir` otherwise. Named like the `getDebugOption`/`getFeatureFlag` accessors above,
which it is one of. -/
def getDumpDir {m : Type → Type} [Monad m] [MonadReaderOf FlagsEnv m] : m System.FilePath := do
  return (← FlagsEnv.getDebugOption "dump-dir").elim defaultDumpDir (↑·)

/-- Write a `-d dump-*` debugging artifact to `dir/name`, creating `dir` if needed. -/
def dumpToFile {m : Type → Type} [Monad m] [MonadLiftT IO m] (content : String)
    (dir : System.FilePath) (name : String) : m Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / name) content

end
