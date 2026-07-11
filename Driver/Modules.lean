import Driver.Errors
import Driver.Builtins
import Common.Flags
import Extra.Monad
import WellFormedness.Monad

open Colorized (Colorized)

/-!
  Recursive `EXTENDS` module resolution — the driver-level orchestration that locates, lexes,
  parses, desugars, and checks a module, recursing on its own `EXTENDS` list for each dependency.

  `compileModule` below is the one function that runs a module's source all the way through to a
  checked module; `Fugue.lean`'s CLI entry point calls it directly for the main module, and
  `resolveModule` calls it again, recursively, for every `EXTENDS`-ed dependency.
-/

/-- Raw module source text by `moduleId`, so `DriverError` can carry just the lightweight key
rather than duplicating a (possibly large) source string into every thrown error — looked up
again only once, at the point an error is finally rendered. -/
class MonadSourceRegistry (m : Type → Type) where
  registerSource : String → String → m Unit
  lookupSource : String → m (Option String)
export MonadSourceRegistry (registerSource lookupSource)

instance {m} [Monad m] [MonadStateOf (Std.HashMap String String) m] : MonadSourceRegistry m where
  registerSource key source := modify (·.insert key source)
  lookupSource key := (·.get? key) <$> get

/-- Backing store for the source registry. -/
initialize sourceRegistryRef : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

instance : MonadStateOf (Std.HashMap String String) IO := sourceRegistryRef.toMonadStateOf

/-- The source lines to render `err`'s snippet against — the offending module's own, looked up
from the registry above by `moduleId`, not whichever module the caller started compiling from.
`none` for the position-free structural errors (`moduleNotFound`/`ambiguousModule`/
`cyclicExtends`, which carry no `moduleId` at all); the caller should fall back to rendering
against the main module's own lines. -/
def DriverError.sourceLines (err : DriverError) : IO (Option (List String.Slice)) := do
  let moduleId? := match err with
    | .lex moduleId _ | .parse moduleId _ | .annotation moduleId _ | .desugar moduleId _
    | .typeCheck moduleId _ | .wellFormedness moduleId _ | .computability moduleId _ =>
      some moduleId
    | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => none
  match moduleId? with
  | none => return none
  | some moduleId => return (·.split (· == '\n') |>.toList) <$> (← lookupSource moduleId)

/-- Names of modules currently being resolved, outermost first — pushed via `withReader (name ::
·)` before recursing into a dependency. A module about to be resolved that's already in this
list is a cyclic `EXTENDS`. -/
abbrev ResolutionStack := List String

/-- What happened when `compileModule`/`resolveModule` finished with a given module name — the
payload `onModuleEvent` reports (`Fugue.lean` turns this into `Built`/`Replayed`/`Failed <name>`).
`.failed` is reported once a module's own name is known but something past that point failed;
lex/parse failures, which happen before a name is known, just surface as the overall compile
failure. -/
inductive ModuleOutcome : Type
  | built
  | replayed
  | failed

/--
  The module cache `Ξ`. Keyed by module name alone, not by name-plus-hash: the hash of a
  candidate file isn't known until after it has already been located and read, so
  `resolveModule` looks up by name first, then compares the returned `CacheEntry.sourceHash`
  against the freshly-read file's own hash.
-/
structure CacheEntry (β : Type) : Type where
  /-- The hash of the source text that produced `value`. -/
  sourceHash : UInt64
  /-- The `EXTENDS` list recorded when this entry was written — trustworthy without re-parsing
  since a matching `sourceHash` means the file is byte-identical to what produced this entry.
  Lets `resolveModule` check whether any dependency changed without re-lexing/parsing an
  unchanged module. -/
  «extends» : List String
  /-- The checked module itself. -/
  value : β

/-- The module cache `Ξ`'s effect interface — `lookupModule`/`storeModule`. -/
class MonadModuleCache (β : outParam Type) (m : Type → Type) where
  /-- The cache entry recorded under this name, if any — not yet validated against any
  particular file; the caller compares `sourceHash` itself. -/
  lookupModule : String → m (Option (CacheEntry β))
  /-- Cache a checked module under its name. -/
  storeModule : String → CacheEntry β → m Unit
export MonadModuleCache (lookupModule storeModule)

instance {β m} [Monad m] [MonadStateOf (Std.HashMap String (CacheEntry β)) m] : MonadModuleCache β m where
  lookupModule n := (·.get? n) <$> get
  storeModule n entry := modify (·.insert n entry)

-- The effects `compileModule`/`resolveModule` need beyond ordinary IO: `Γ`'s enclosing `FlagsEnv`
-- (for `-I`'s search path), the resolution stack (cycle detection), the module cache, and error
-- reporting. Not a `class abbrev` bundle: two different `MonadReaderOf`/`MonadWithReaderOf`
-- instantiations as parents of the same abbrev collide, so every constraint is listed explicitly
-- on each function instead.

/-- The concrete monad `compileModule`/`resolveModule` run at when actually invoked.
`FlagsEnv`/`Ξ` are both backed by a global `IO.Ref` and reachable directly at `IO`;
`ResolutionStack` is the one genuinely scoped Reader (push-on-recurse, pop-on-return), so it's
the one transformer layer needed on top of `IO`. -/
abbrev M := ReaderT ResolutionStack (ExceptT DriverError IO)

/-- Run an `M` action from the top, with an empty resolution stack. -/
def runM {α} (act : M α) : IO (Except DriverError α) :=
  (ReaderT.run act []).run

/-- Backing store for `Ξ`, mirroring `Common/Flags.lean`'s `flagsRef` pattern. -/
initialize moduleCacheRef : IO.Ref (Std.HashMap String (CacheEntry TypedModule)) ← IO.mkRef {}

instance : MonadStateOf (Std.HashMap String (CacheEntry TypedModule)) IO :=
  moduleCacheRef.toMonadStateOf

/-- Where a candidate module named `name` was found — a real file, or the builtin table. -/
private inductive Candidate : Type
  | file (path : System.FilePath)
  | builtin (mod : TypedModule)

variable {m : Type → Type} [Monad m] [MonadReaderOf FlagsEnv m] [MonadReaderOf ResolutionStack m]
  [MonadWithReaderOf ResolutionStack m] [MonadModuleCache TypedModule m] [MonadSourceRegistry m]
  [MonadExceptOf DriverError m] [MonadLiftT IO m]

/-- Every directory searched for `EXTENDS name`, in order: the directory containing the
extending module (if any — absent when read from stdin), then `-I`'s search path. The builtin
table is checked as one more candidate source, so a name present in both a searched directory
and `builtinModules` is ambiguous, not silently resolved one way. -/
private def locate (name : String) (containingDir : Option System.FilePath) : m Candidate := do
  let mut found : List (String × Candidate) := []
  if let some mod := builtinModules[name]? then
    found := found ++ [("<builtin>", .builtin mod)]
  for dir in containingDir.toList ++ (← readThe FlagsEnv).searchPath do
    let path := dir / s!"{name}.tla"
    if ← liftM path.pathExists.toIO then
      found := found ++ [(toString path, .file path)]
  match found with
  | [] => throw (.moduleNotFound name)
  | [(_, candidate)] => return candidate
  | multiple => throw (.ambiguousModule name (multiple.map Prod.fst))

/-- `MonadForeignLookup`'s concrete instance (`WellFormedness/Monad.lean`) — a module's checked
declarations by name: a `.file` hit via the cache `Ξ` (reachable this way only once a dependency
has actually been resolved and cached), falling back to `builtinModules[name]?` for a builtin.
Mirrors `locate`'s own candidate search, minus the not-found/ambiguous error cases — a name
reachable via a checked `Origin.module name` tag has, by construction, already type-checked. -/
instance : MonadForeignLookup m where
  lookupForeign name := do
    match ← lookupModule name with
    | some entry => return some entry.value
    | none => return builtinModules[name]?

/-- Print every warning in `warnings` not suppressed by `-Wno-<name>`, in one batch, only once
this module's outcome (`Built`/`Replayed`/`Failed`) is known — never interleaved before it. Each
call site passes only warnings collected for that module's own `compileModule` call; a
dependency's warnings are flushed separately by its own recursive call. `logLine` is pluggable
(defaults to `eprintln`) so `Fugue.lean` can route it through its spinner instead. -/
private def flushWarnings {m} [Monad m] [MonadReaderOf FlagsEnv m] [MonadLiftT IO m]
    (lines : List String.Slice) (colored : Bool)
    (logLine : String → m Unit) (warnings : List DriverWarning) : m Unit :=
  warnings.forM λ warning ↦ do
    if ← FlagsEnv.isWarningEnabled warning.name then
      logLine <| CompilerDiagnostic.pretty warning lines colored

/-- Run `act`; if it throws, flush `warnings` (collected so far for this module), report `name` as
`.failed` via `onModuleEvent`, and re-throw the same error unchanged. Factored out since
`compileModule` needs this exact flush/report/re-throw shape at three separate points. -/
private def reportFailureOnThrow {m} [Monad m] [MonadReaderOf FlagsEnv m] [MonadLiftT IO m] [MonadExceptOf DriverError m] {α}
    (lines : List String.Slice) (colored : Bool) (logLine : String → m Unit)
    (onModuleEvent : String → ModuleOutcome → m Unit) (name : String) (warnings : List DriverWarning) (act : m α) : m α := do
  try
    act
  catch e =>
    flushWarnings lines colored logLine warnings
    onModuleEvent name .failed
    throw e

/-- Write a `-d dump-*` debugging artifact to `dir/name`, creating `dir` if needed. -/
private def dumpToFile {m} [Monad m] [MonadLiftT IO m] (content : String) (dir : System.FilePath) (name : String) : m Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / name) content

/-- Default value of `-d dump-dir=<path>`. -/
private def defaultDumpDir : System.FilePath := ".fugue/debug"

/-- Every name/type binding a checked declaration introduces, computed from an already-checked
`Decl` rather than by re-checking one. Used to expose an `EXTENDS`-ed dependency's own
declarations into a fresh `Γ₀` — all of a dependency's own `params`/`defs` come into scope, not
just its exported operators. PlusCal-internal declarations are never included, since they never
leak into a module's `Γ` in the first place. `moduleName` (`depMod.name` at the one call site) is
what declared this `Decl` — tags every returned binding's `Origin` accordingly (PLAN.md §9.22).

A `constants`/`variables` binding is never a scheme (`Binding.isScheme := false`); an
`operator`/`function` binding always is, any arity — matches `Elaborator/Declarations.lean`'s
`checkDeclaration`, whose own returned bindings follow the identical rule. This is what lets a
0-ary builtin like `Bags`'s `EmptyBag` (`Driver/Builtins.lean`) get freshened on every reference
without `Driver/Builtins.lean` itself needing any change — arity alone (already present on every
`Decl.operator`) decides `isScheme`. -/
private def Decl.bindings (moduleName : String) : Decl → List (String × Binding)
  | .constants xs => xs.map λ (x, τ) ↦ (x, { type := τ, origin := .module moduleName })
  | .variables xs => xs.map λ (x, τ) ↦ (x, { type := τ, origin := .module moduleName })
  | .assume _ => []
  | .operator τ f _ _ => [(f, { type := τ, isScheme := true, origin := .module moduleName })]
  | .function τ f _ _ => [(f, { type := τ, isScheme := true, origin := .module moduleName })]

-- `compileModule`/`resolveModule` call each other recursively (a module's own `EXTENDS` list is
-- resolved by calling `resolveModule`, which falls back to `compileModule` on a cache
-- miss/mismatch) — `mutual`, and `partial` since termination here depends on cyclic-`EXTENDS`
-- detection (`ResolutionStack`) at runtime, not on any argument that's structurally decreasing.
private instance {m} [Applicative m] {α} [Inhabited α] : Inhabited (m α) := ⟨pure default⟩

mutual
/--
  Run a module's source all the way through to a checked module: lex, parse, resolve
  annotations, desugar TLA⁺ expressions and the embedded PlusCal algorithm, resolve every
  `EXTENDS`-ed dependency (`resolveModule`, recursing into `compileModule` for anything not
  already satisfied by the cache or a builtin), merge their exported declarations into an
  initial `Γ`, and check.

  `onModuleProgress name` fires twice for this module: once as soon as `name` is known (right
  after parsing), and again right after its own `EXTENDS` dependencies finish resolving, to
  refocus display back onto this module once its dependencies are no longer "current".

  `onModuleEvent name .built` fires once this module is fully checked, and `.failed` if this
  module's own processing throws — the one place `.built`/`.failed` are reported for this
  module (a dependency's own outcome is reported inside its own recursive `compileModule` call,
  never duplicated here).

  `moduleId` is the registry key `DriverError`'s variants tag themselves with, registered
  against `source` before lexing runs. For a dependency this is the `EXTENDS`-requested name;
  for the main module it's whatever caller-chosen identifier `Fugue.lean` passes.
-/
partial def compileModule (source : String) (containingDir : Option System.FilePath) (moduleId : String)
    -- (onTokens : Array (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token))) → m Unit := fun _ ↦ pure ())
    -- (onParsed : SurfaceTLAPlus.Module
    --     (SurfacePlusCal.Algorithm (List SurfaceTLAPlus.CommentAnnotation) (SurfaceTLAPlus.Expression (List SurfaceTLAPlus.CommentAnnotation)))
    --     (List SurfaceTLAPlus.CommentAnnotation) → m Unit := fun _ ↦ pure ())
    -- (onDesugared : CoreTLAPlus.Module
    --     (CorePlusCal.Algorithm (Option SurfaceTLAPlus.Typ) (CoreTLAPlus.Expression (Option SurfaceTLAPlus.Typ)))
    --     (Option SurfaceTLAPlus.Typ) → m Unit := fun _ ↦ pure ())
    -- (onTyped : TypedModule → m Unit := fun _ ↦ pure ())
    (onModuleEvent : String → ModuleOutcome → m Unit := fun _ _ ↦ pure ())
    (onModuleProgress : String → m Unit := fun _ ↦ pure ())
    (logLine : String → m Unit := fun s ↦ liftM (IO.eprintln s : IO Unit)) : m TypedModule := do
  let dumpDir : System.FilePath := (← FlagsEnv.getDebugOption "dump-dir").elim defaultDumpDir (↑·)

  registerSource moduleId source
  let lines := source.split (· == '\n') |>.toList
  let colored ← not <$> FlagsEnv.getFeatureFlag "no-color"
  let tokens ← match SurfaceTLAPlus.Lexer.lexModule source with
    | .inl e => throw (.lex moduleId e)
    | .inr tokens => pure tokens

/-
      (onTokens := λ tokens ↦ do

      (onParsed := λ mod ↦ do

      (onDesugared := λ mod ↦ do
        )
      (onTyped := λ typed ↦ do
        )
-/

  if ← FlagsEnv.getDebugFlag "dump-tokens" then
    dumpToFile (reprStr tokens) dumpDir s!"{moduleId}-tokens"

  let (mod, parserWarnings) ← match SurfaceTLAPlus.Parser.parseModule tokens with
    | .inl e => throw (.parse moduleId e)
    | .inr r => pure r
  let warnings : List DriverWarning := parserWarnings.map (.parser moduleId)

  if ← FlagsEnv.getDebugFlag "dump-cst" then
    dumpToFile (reprStr mod) dumpDir s!"{moduleId}-cst"

  onModuleProgress mod.name
  let (mod, warnings) ← reportFailureOnThrow lines colored logLine onModuleEvent mod.name warnings do
    let mod ← match resolveAnnotations mod with
      | .error e => throw (.annotation moduleId e)
      | .ok mod => pure mod
    let mod ← match mod.runDesugarer with
      | .error e => throw (.desugar moduleId e)
      | .ok mod => pure mod
    let mod ← match mod.stripTLAPlusAnnotations with
      | .error e => throw (.desugar moduleId e)
      | .ok mod => pure mod
    let (algo, warnings) ← match mod.pcalAlgorithm with
      | none => pure (none, warnings)
      | some algo =>
        match algo.runDesugarer with
        | .error e => throw (.desugar moduleId e)
        | .ok (algo, desugarWarnings) =>
          pure (some algo, warnings ++ desugarWarnings.map (.desugar moduleId))
    let mod := { mod with pcalAlgorithm := algo }

    if ← FlagsEnv.getDebugFlag "dump-desugared" then
      dumpToFile (reprStr mod) dumpDir s!"{moduleId}-desugared"

    pure (mod, warnings)
  let deps ← reportFailureOnThrow lines colored logLine onModuleEvent mod.name warnings <|
    mod.extends.mapM λ dep ↦
      withReader (mod.name :: ·) (resolveModule containingDir dep onModuleEvent onModuleProgress logLine)
  onModuleProgress mod.name

  let typed ← reportFailureOnThrow lines colored logLine onModuleEvent mod.name warnings do
    let importedBindings := deps.flatMap λ (_, depMod) ↦
      (depMod.declarations₁ ++ depMod.declarations₂).flatMap (Decl.bindings depMod.name)
    let Γ₀ : Context := importedBindings.foldl (init := builtinContext) λ ctx (x, b) ↦ ctx.insert x b
    let typed ← match CoreTLAPlus.Module.runChecker Γ₀ mod with
      | .error e => throw (.typeCheck moduleId e)
      | .ok typed => pure typed

    match ← (TypedTLAPlus.Module.checkWellFormed typed : ExceptT WellFormednessError m Unit).run with
    | .error e => throw (.wellFormedness moduleId e)
    | .ok () => pure ()

    match ← (TypedTLAPlus.Module.toComputable typed : ExceptT ComputableError m _).run with
    | .error e => throw (.computability moduleId e)
    | .ok computable =>
      if ← FlagsEnv.getDebugFlag "dump-computable" then
        dumpToFile (reprStr computable) dumpDir s!"{moduleId}-computable"

    if ← FlagsEnv.getDebugFlag "dump-typed" then
      dumpToFile (reprStr typed) dumpDir s!"{moduleId}-typed"

    return typed

  flushWarnings lines colored logLine warnings
  onModuleEvent mod.name .built
  return typed

/--
  The `EXTENDS`-specific wrapper around `compileModule`: locate `name` (`locate` above, error on
  not-found/ambiguous), check `Ξ`, and recompute if `name`'s source changed or if anything it
  transitively depends on changed. The returned `Bool` is "was this module actually recomputed
  just now," threaded up so its dependents can tell whether they need to recompute in turn.

  Fires `onModuleEvent name .replayed` on the one path that never touches `compileModule` (a
  cache hit with nothing changed); every other outcome is reported by whichever `compileModule`
  call this makes. Not for `.builtin`, which is static. `onModuleProgress name` fires once, at
  the top of the `.file` case.
-/
partial def resolveModule (containingDir : Option System.FilePath) (name : String)
    (onModuleEvent : String → ModuleOutcome → m Unit := fun _ _ ↦ pure ())
    (onModuleProgress : String → m Unit := fun _ ↦ pure ())
    (logLine : String → m Unit := fun s ↦ liftM (IO.eprintln s : IO Unit)) : m (Bool × TypedModule) := do
  if name ∈ (← readThe ResolutionStack) then
    throw (.cyclicExtends ((← readThe ResolutionStack).reverse ++ [name]))
  match ← locate name containingDir with
  | .builtin mod => do
    let deps ← mod.extends.mapM λ dep ↦
      withReader (mod.name :: ·) (resolveModule containingDir dep onModuleEvent onModuleProgress logLine)
    let importedDecls := deps.flatMap λ (_, depMod) ↦ depMod.declarations₁ ++ depMod.declarations₂
    return (false, { mod with declarations₁ := importedDecls ++ mod.declarations₁ })
  | .file path => do
    onModuleProgress name
    let src ← IO.FS.readFile path
    let h := hash src
    match ← lookupModule name with
    | some entry =>
      if entry.sourceHash == h then
        let depResults ← entry.extends.mapM λ dep ↦
          withReader (name :: ·) (resolveModule containingDir dep onModuleEvent onModuleProgress logLine)
        if depResults.all (¬ ·.1) then
          onModuleEvent name .replayed
          return (false, entry.value)
        else
          let recomputed ← compileModule src path.parent name
            (onModuleEvent := onModuleEvent) (onModuleProgress := onModuleProgress) (logLine := logLine)
          storeModule name { sourceHash := h, «extends» := entry.extends, value := recomputed }
          return (true, recomputed)
      else
        let recomputed ← compileModule src path.parent name
          (onModuleEvent := onModuleEvent) (onModuleProgress := onModuleProgress) (logLine := logLine)
        storeModule name { sourceHash := h, «extends» := recomputed.extends, value := recomputed }
        return (true, recomputed)
    | none =>
      let recomputed ← compileModule src path.parent name
        (onModuleEvent := onModuleEvent) (onModuleProgress := onModuleProgress) (logLine := logLine)
      storeModule name { sourceHash := h, «extends» := recomputed.extends, value := recomputed }
      return (true, recomputed)
end
