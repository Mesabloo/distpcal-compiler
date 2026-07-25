module

public import Common.Flags

public section

/-! Where `-d dump-*` debugging artifacts go, and how they get written. Shared because both the
driver (`Driver/Modules.lean`, which dumps the per-module stages it runs — tokens, CST,
desugared, typed) and the CLI (`Fugue.lean`, which dumps the pipeline stages that run past the
driver — computable, guarded, network) write them, and the two must agree on the directory. -/

/-- Default value of `-d dump-dir=<path>`. -/
def defaultDumpDir : System.FilePath := ".fugue/debug"

/-- The directory `-d dump-*` artifacts are written to: `-d dump-dir=<path>` if given,
`defaultDumpDir` otherwise. Named like `Common/Flags.lean`'s own `getDebugOption`/`getFeatureFlag`
accessors, which it is one of. -/
def getDumpDir {m : Type → Type} [Monad m] [MonadReaderOf FlagsEnv m] : m System.FilePath := do
  return (← FlagsEnv.getDebugOption "dump-dir").elim defaultDumpDir (↑·)

/-- Write a `-d dump-*` debugging artifact to `dir/name`, creating `dir` if needed. -/
def dumpToFile {m : Type → Type} [Monad m] [MonadLiftT IO m] (content : String)
    (dir : System.FilePath) (name : String) : m Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / name) content

end
