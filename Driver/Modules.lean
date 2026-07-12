module

public import Driver.Errors
public import Driver.Builtins
public import Common.Flags
public import Extra.Monad
public import WellFormedness.Monad

public section

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
    | .typeCheck moduleId _ =>
      some moduleId
    | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => none
  match moduleId? with
  | none => return none
  | some moduleId => return (·.split (· == '\n') |>.toList) <$> (← lookupSource moduleId)

def DriverWarning.sourceLines (err : DriverWarning) : IO (Option (List String.Slice)) := do
  let moduleId? := match err with
    | .parser moduleId _ | .desugar moduleId _ | .typeCheck moduleId _ =>
      some moduleId
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
  | built (hadWarnings : Bool)
  | replayed
  | failed

/-- The module cache `Ξ`. Keyed by module name alone, not name-plus-hash: a candidate file's hash
isn't known until after it's been located and read, so `resolveModule` looks up by name first,
then compares the returned `CacheEntry.sourceHash` against the freshly-read file's hash. -/
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
the one transformer layer needed on top of `DiagT`'s own `DriverWarning`/`DriverError` reporting
over `IO` — `compileModule`/`resolveModule` are concrete against this one stack, not polymorphic
like everything else here: the per-module warning scoping below (`runScoped`) needs to actually
run `DiagT`'s layer down to a plain value, which is only possible against a fixed concrete stack,
not an abstract `m`. -/
abbrev M := ReaderT ResolutionStack (DiagT DriverWarning DriverError IO)

/-- Run an `M` action from the top, with an empty resolution stack. -/
def runM {α} (act : M α) : IO (List DriverWarning × Except DriverError α) :=
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

/-- Run `act`'s `M`-action down through the current `ResolutionStack` and `DiagT`'s `IO` base,
producing the exact `List DriverWarning` it `tell`'d and its `Except`-wrapped result as plain
data. This is the only way to observe either once a `throw` is in play: `MonadWriter.listen` has
nowhere to put warnings once the value they'd pair with disappears on a throw (same wall a
generic `ExceptT ε N` composition would hit), so this sidesteps `listen` entirely and goes
straight to `DiagT.run`. -/
private def runScoped {α} (act : M α) : M (List DriverWarning × Except DriverError α) := do
  let resStack ← readThe ResolutionStack
  liftM (DiagT.run (ReaderT.run act resStack) : IO (List DriverWarning × Except DriverError α))

/-- Run `act`; if it throws, flush the warnings `act` produced (up to the throw), report `name`
as `.failed` via `onModuleEvent`, and re-throw the error unchanged. If it succeeds, `tell` its
warnings back into the ambient accumulator — so they keep flowing toward whichever later stage,
or the final per-module flush, is next — and return its value. `compileModule` needs this exact
flush/report/re-throw-or-forward shape at three separate points. -/
private def reportFailureOnThrow {α} --(lines : List String.Slice) (colored : Bool) (logLine : String → M Unit)
    (onModuleEvent : String → ModuleOutcome → M Unit) (name : String) (act : M α) : M α := do
  let (warnings, result) ← runScoped act
  match result with
  | .error e =>
    -- flushWarnings lines colored logLine warnings
    tell warnings
    onModuleEvent name .failed
    throw e
  | .ok a =>
    tell warnings
    pure a

/-- Write a `-d dump-*` debugging artifact to `dir/name`, creating `dir` if needed. -/
private def dumpToFile {m} [Monad m] [MonadLiftT IO m] (content : String) (dir : System.FilePath) (name : String) : m Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / name) content

/-- Default value of `-d dump-dir=<path>`. -/
private def defaultDumpDir : System.FilePath := ".fugue/debug"

/-- Every name/type binding a checked declaration introduces, computed from an already-checked
`Decl` rather than by re-checking one. Used to expose an `EXTENDS`-ed dependency's own
declarations into a fresh `Γ₀` — all of a dependency's `params`/`defs` come into scope, not just
its exported operators. PlusCal-internal declarations are never included, since they never leak
into a module's `Γ` in the first place. `moduleName` (`depMod.name` at the one call site) is what
declared this `Decl` — tags every returned binding's `Origin` accordingly.

A `constants`/`variables` binding is never a scheme (`Binding.isScheme := false`); an
`operator`/`function` binding always is, any arity — matches `Elaborator/Declarations.lean`'s
`checkDeclaration`, whose returned bindings follow the identical rule. This is what lets a 0-ary
builtin like `Bags`'s `EmptyBag` (`Driver/Builtins.lean`) get freshened on every reference without
`Driver/Builtins.lean` needing any change — arity alone (already present on every `Decl.operator`)
decides `isScheme`. -/
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
/-- Run a module's source all the way through to a checked module: lex, parse, resolve
annotations, desugar TLA⁺ expressions and the embedded PlusCal algorithm, resolve every
`EXTENDS`-ed dependency (`resolveModule`, recursing into `compileModule` for anything not already
satisfied by the cache or a builtin), merge their exported declarations into an initial `Γ`, and
check.

`onModuleProgress name` fires twice: once as soon as `name` is known (right after parsing), and
again once its `EXTENDS` dependencies finish resolving, to refocus display back onto this module
once its dependencies are no longer "current".

`onModuleEvent name .built` fires once this module is fully checked, `.failed` if its own
processing throws — the one place either is reported for this module (a dependency's own outcome
is reported inside its own recursive `compileModule` call, never duplicated here).

`moduleId` is the registry key `DriverError`'s variants tag themselves with, registered against
`source` before lexing runs. For a dependency this is the `EXTENDS`-requested name; for the main
module it's whatever identifier `Fugue.lean` passes. -/
partial def compileModule (source : String) (containingDir : Option System.FilePath) (moduleId : String)
    (onModuleEvent : String → ModuleOutcome → M Unit := fun _ _ ↦ pure ())
    (onModuleProgress : String → M Unit := fun _ ↦ pure ())
    (logLine : String → M Unit := fun s ↦ liftM (IO.eprintln s : IO Unit)) : M TypedModule := do
  let dumpDir : System.FilePath := (← FlagsEnv.getDebugOption "dump-dir").elim defaultDumpDir (↑·)

  registerSource moduleId source

  let tokens ← match SurfaceTLAPlus.Lexer.lexModule source with
    | .inl e => throw (.lex moduleId e)
    | .inr tokens => pure tokens

  if ← FlagsEnv.getDebugFlag "dump-tokens" then
    dumpToFile (reprStr tokens) dumpDir s!"{moduleId}-tokens"

  let mod ← DiagT.lift (.parser moduleId) (.parse moduleId) (SurfaceTLAPlus.Parser.parseModule tokens)

  if ← FlagsEnv.getDebugFlag "dump-cst" then
    dumpToFile (reprStr mod) dumpDir s!"{moduleId}-cst"

  onModuleProgress mod.name
  let (warnings, result) ← runScoped do
    let mod ← reportFailureOnThrow /- lines colored logLine -/ onModuleEvent mod.name do
      let mod ← match resolveAnnotations mod with
        | .error e => throw (.annotation moduleId e)
        | .ok mod => pure mod
      let mod ← DiagT.lift (.desugar moduleId) (.desugar moduleId) mod.runDesugarer
      let mod ← match mod.stripTLAPlusAnnotations with
        | .error e => throw (.desugar moduleId e)
        | .ok mod => pure mod
      let algo ← match mod.pcalAlgorithm with
        | none => pure none
        | some algo => some <$> DiagT.lift (.desugar moduleId) (.desugar moduleId) algo.runDesugarer
      let mod := { mod with pcalAlgorithm := algo }

      if ← FlagsEnv.getDebugFlag "dump-desugared" then
        dumpToFile (reprStr mod) dumpDir s!"{moduleId}-desugared"

      pure mod
    let deps ← reportFailureOnThrow /- lines colored logLine -/ onModuleEvent mod.name <|
      mod.extends.mapM λ dep ↦
        withReader (mod.name :: ·) (resolveModule containingDir dep onModuleEvent onModuleProgress logLine)
    onModuleProgress mod.name

    reportFailureOnThrow /- lines colored logLine -/ onModuleEvent mod.name do
      let importedBindings := deps.flatMap λ (_, depMod) ↦
        (depMod.declarations₁ ++ depMod.declarations₂).flatMap (Decl.bindings depMod.name)
      let Γ₀ : Context := importedBindings.foldl (init := builtinContext) λ ctx (x, b) ↦ ctx.insert x b
      let typed ← DiagT.lift (.typeCheck moduleId) (.typeCheck moduleId) (CoreTLAPlus.Module.runChecker Γ₀ mod)

      if ← FlagsEnv.getDebugFlag "dump-typed" then
        dumpToFile (reprStr typed) dumpDir s!"{moduleId}-typed"

      return typed

  tell warnings
  match result with
  | .error e => throw e
  | .ok typed =>
    onModuleEvent mod.name (.built (!warnings.isEmpty))
    -- flushWarnings lines colored logLine warnings
    return typed

/-- The `EXTENDS`-specific wrapper around `compileModule`: locate `name` (`locate` above, error on
not-found/ambiguous), check `Ξ`, and recompute if `name`'s source changed or anything it
transitively depends on changed. The returned `Bool` is whether this module was actually
recomputed just now, threaded up so its dependents can tell whether they need to recompute in
turn.

Fires `onModuleEvent name .replayed` on the one path that never touches `compileModule` (a cache
hit with nothing changed); every other outcome is reported by whichever `compileModule` call this
makes. Not for `.builtin`, which is static. `onModuleProgress name` fires once, at the top of the
`.file` case. -/
partial def resolveModule (containingDir : Option System.FilePath) (name : String)
    (onModuleEvent : String → ModuleOutcome → M Unit := fun _ _ ↦ pure ())
    (onModuleProgress : String → M Unit := fun _ ↦ pure ())
    (logLine : String → M Unit := fun s ↦ liftM (IO.eprintln s : IO Unit)) : M (Bool × TypedModule) := do
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

end
