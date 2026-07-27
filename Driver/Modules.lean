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

/-- The registry itself, as plain data: `moduleId ↦ that module's source text`. -/
abbrev SourceRegistry := Std.HashMap String String

/-- The `moduleId` a `DriverError` is tagged with, if any — `none` for the position-free
structural errors (`moduleNotFound`/`ambiguousModule`/`cyclicExtends`), which carry none. -/
def DriverError.moduleId? : DriverError → Option String
  | .lex moduleId _ | .parse moduleId _ | .annotation moduleId _ | .desugar moduleId _
  | .typeCheck moduleId _ | .moduleNameMismatch moduleId _ _ => some moduleId
  | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => none

/-- The source lines to render `err`'s snippet against — the offending module's own, looked up in
`registry` by `moduleId`, not whichever module the caller started compiling from. `none` when
`err` carries no `moduleId`, or the registry has no entry for it; the caller should fall back to
rendering against the main module's own lines.

A pure function of the registry rather than an `IO` action reading a global ref, so rendering a
diagnostic needs no `IO` at all — which is what lets `Driver/Pipeline.lean` hand a caller finished
diagnostic text and lets the regression runner assert on it directly. -/
def DriverError.sourceLines (registry : SourceRegistry) (err : DriverError) :
    Option (List String.Slice) := do
  let moduleId ← err.moduleId?
  return (← registry.get? moduleId).split (· == '\n') |>.toList

/-- `DriverError.sourceLines`'s counterpart for warnings, which always carry a `moduleId`
(`DriverWarning.moduleId`, `Driver/Errors.lean`). -/
def DriverWarning.sourceLines (registry : SourceRegistry) (warning : DriverWarning) :
    Option (List String.Slice) := do
  return (← registry.get? warning.moduleId).split (· == '\n') |>.toList

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

-- The effects `compileModule`/`resolveModule` need beyond ordinary IO: `Γ`'s enclosing `FlagsEnv`
-- (for `-I`'s search path), the resolution stack (cycle detection), the module cache, the source
-- registry, the fresh-name counter, and error reporting. Not a `class abbrev` bundle: two
-- different `MonadReaderOf`/`MonadWithReaderOf` instantiations as parents of the same abbrev
-- collide, so every constraint is listed explicitly on each function instead.

/-- Everything one compile mutates as it runs: the fresh-name counter (`Common/Fresh.lean`), the
source registry (for rendering a diagnostic against its own module's lines), and the module cache
`Ξ`. One value per compile, threaded as a real `StateT` layer rather than a set of global
`IO.Ref`s, so concurrent compiles in one process — which is what the regression runner does — are
independent, and a compile's fresh names don't depend on what ran before it. -/
structure DriverState : Type where
  /-- `MonadFresh`'s counter. -/
  fresh : Nat := 0
  /-- Module sources by `moduleId`. -/
  sources : SourceRegistry := {}
  /-- The module cache `Ξ`. -/
  cache : Std.HashMap String (CacheEntry TypedModule) := {}
  deriving Inhabited

-- The three effects `DriverState` backs, each written against `MonadStateOf DriverState` directly.
-- A pass never sees `DriverState` itself: it asks for `MonadFresh`/`MonadSourceRegistry`/
-- `MonadModuleCache`, and `Common/Fresh.lean`'s lifts carry those down to here through whatever
-- layers the pass stacked on top.

/-- The compile's fresh-name counter (`Common/Fresh.lean`). -/
instance {m} [Monad m] [MonadStateOf DriverState m] : MonadFresh m where
  fresh := modifyGet λ s ↦ (s.fresh, { s with fresh := s.fresh + 1 })

instance {m} [Monad m] [MonadStateOf DriverState m] : MonadSourceRegistry m where
  registerSource key source := modify λ s ↦ { s with sources := s.sources.insert key source }
  lookupSource key := (·.sources.get? key) <$> get

instance {m} [Monad m] [MonadStateOf DriverState m] : MonadModuleCache TypedModule m where
  lookupModule n := (·.cache.get? n) <$> get
  storeModule n entry := modify λ s ↦ { s with cache := s.cache.insert n entry }

/-- What `M` sits on: the compile's flags and its mutable state, under plain `IO`. The state layer
is *below* `DiagT` on purpose — `StateT` above it would discard everything written before a
`throw`, and the source registry has to survive the throw that consults it. -/
abbrev Base := ReaderT FlagsEnv (StateT DriverState IO)

/-- The concrete monad `compileModule`/`resolveModule` run at when actually invoked.
`ResolutionStack` is the one genuinely scoped Reader (push-on-recurse, pop-on-return), which is
why it sits above `DiagT`'s own `DriverWarning`/`DriverError` reporting rather than in `Base`.
`compileModule`/`resolveModule` are concrete against this stack, not polymorphic like everything
else here: the per-module warning scoping below (`runScoped`) needs to actually run `DiagT`'s
layer down to a plain value, which is only possible against a fixed concrete stack, not an
abstract `m`. -/
abbrev M := ReaderT ResolutionStack (DiagT DriverWarning DriverError Base)

/-- Run an `M` action from the top, with an empty resolution stack — down to `Base`, not to `IO`:
whoever runs `Base` owns the compile's flags and state, and everything past this call (the passes
after type checking, and rendering the diagnostics against the sources this action registered)
still needs both. `Driver/Pipeline.lean` is that owner. -/
def runM {α} (act : M α) : Base (List DriverWarning × Except DriverError α) :=
  DiagT.run (ReaderT.run act [])

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
and `builtinModules` is ambiguous, not silently resolved one way.

Two searched directories naming the *same* file contribute one candidate, not two — `-I foo` on
`foo/Main.tla`, where `foo` is already the containing directory, is a duplicate rather than an
ambiguity. Sameness is decided by `IO.FS.realPath`, so a relative and an absolute spelling of one
directory, a `.`/`..` detour, and a symlink all collapse; what a genuine ambiguity then reports is
still each candidate as it was *spelled*, since that is what the user wrote and what they would
have to change. -/
private def locate (name : String) (containingDir : Option System.FilePath) : m Candidate := do
  let mut found : List (String × Candidate) := []
  let mut seen : List String := []
  if let some mod := builtinModules[name]? then
    found := found ++ [("<builtin>", .builtin mod)]
  for dir in containingDir.toList ++ (← readThe FlagsEnv).searchPath do
    let path := dir / s!"{name}.tla"
    if ← liftM path.pathExists.toIO then
      -- `realPath` throws only if the file went away between `pathExists` and here; the spelling
      -- itself is a fine key in that case, since nothing else will canonicalize onto it either.
      let canonical : IO String := do
        try return toString (← IO.FS.realPath path) catch _ => return toString path
      let key ← liftM canonical
      unless seen.contains key do
        seen := seen ++ [key]
        found := found ++ [(toString path, .file path)]
  match found with
  | [] => throw (.moduleNotFound name)
  | [(_, candidate)] => return candidate
  | multiple => throw (.ambiguousModule name (multiple.map Prod.fst))

/-- `MonadForeignLookup`'s concrete instance (`WellFormedness/Monad.lean`) — a module's checked
declarations by name: a `.file` hit via the cache `Ξ` (reachable this way only once a dependency
has actually been resolved and cached), falling back to `builtinModules[name]?` for a builtin.
Mirrors `locate`'s own candidate search, minus the not-found/ambiguous error cases — a name
reachable via a checked `Origin.module name` tag has, by construction, already type-checked.

Constrained to `MonadModuleCache` alone rather than taking the surrounding `variable` block's
whole bundle, so it applies at plain `IO` too — `Ξ` is a global `IO.Ref`, so the lookup needs
nothing the driver's own `M` uniquely has. That is what lets the passes running *past* the driver
(`Fugue.lean`'s `checkWellFormed`/`toComputable` calls, against `IO`) use this instance instead of
declaring a second copy of it. -/
instance {m : Type → Type} [Monad m] [MonadModuleCache TypedModule m] : MonadForeignLookup m where
  lookupForeign name := do
    match ← lookupModule name with
    | some entry => return some entry.value
    | none => return builtinModules[name]?

/-- Run `act`'s `M`-action down through the current `ResolutionStack` and `DiagT`'s `Base`,
producing the exact `List DriverWarning` it `tell`'d and its `Except`-wrapped result as plain
data. This is the only way to observe either once a `throw` is in play: `MonadWriter.listen` has
nowhere to put warnings once the value they'd pair with disappears on a throw (same wall a
generic `ExceptT ε N` composition would hit), so this sidesteps `listen` entirely and goes
straight to `DiagT.run`. Running down to `Base` rather than all the way to `IO` is what keeps
`act`'s state writes — the source registry entries it made, the cache entries it stored, the
fresh names it consumed — even when `act` threw. -/
private def runScoped {α} (act : M α) : M (List DriverWarning × Except DriverError α) := do
  let resStack ← readThe ResolutionStack
  liftM (DiagT.run (ReaderT.run act resStack) : Base (List DriverWarning × Except DriverError α))

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

-- `M` is five transformer layers deep now that flags and the compile's state are threaded rather
-- than read out of global `IO.Ref`s, and these two mutually recursive definitions are the largest
-- terms in the codebase at that stack: code generation (`LCNF check`) runs past the default
-- budget. Same accommodation `Core/SurfaceTLAPlus/Syntax.lean` already makes for its own big
-- derived instances.
set_option maxHeartbeats 1000000 in
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
    (expectedName : Option String := none)
    (onModuleEvent : String → ModuleOutcome → M Unit := fun _ _ ↦ pure ())
    (onModuleProgress : String → M Unit := fun _ ↦ pure ())
    (logLine : String → M Unit := fun s ↦ liftM (IO.eprintln s : IO Unit)) : M TypedModule := do
  registerSource moduleId source

  let tokens ← match SurfaceTLAPlus.Lexer.lexModule source with
    | .inl e => throw (.lex moduleId e)
    | .inr tokens => pure tokens

  dumpStage .lex moduleId tokens

  let mod ← DiagT.lift (.parser moduleId) (.parse moduleId) (SurfaceTLAPlus.Parser.parseModule tokens)

  dumpStage .parse moduleId mod

  -- TLA⁺ requires a module to live in a file named after it: `locate` builds its candidate path as
  -- `<dir>/<name>.tla` and looks nowhere else, so a module whose declared name differs from its
  -- file's is unreachable by any `EXTENDS`, however well it compiles on its own. Checked as soon
  -- as the name is known — right after parsing — and only when the caller knows what the name
  -- ought to be: stdin has no filename to compare against, so it passes `none` and is exempt.
  if let some expected := expectedName then
    if mod.name != expected then
      throw (.moduleNameMismatch moduleId mod.name expected)

  onModuleProgress mod.name
  let (warnings, result) ← runScoped do
    let mod ← reportFailureOnThrow /- lines colored logLine -/ onModuleEvent mod.name do
      let mod ← match resolveAnnotations mod with
        | .error e => throw (.annotation moduleId e)
        | .ok mod => pure mod
      -- Each `runDesugarer`/`runChecker` is polymorphic in its base monad (it needs only the
      -- fresh-name counter from it), so the base has to be pinned here: `Base`, this compile's
      -- own flags-and-state layer, is the whole point of their being polymorphic.
      let mod ← DiagT.lift (.desugar moduleId) (.desugar moduleId)
        (mod.runDesugarer : DiagT DesugarWarning DesugarError Base _)
      let mod ← DiagT.lift (.desugar moduleId) (.desugar moduleId) mod.stripTLAPlusAnnotations
      let algo ← match mod.pcalAlgorithm with
        | none => pure none
        | some algo =>
          let desugared : DiagT DesugarWarning DesugarError Base _ := algo.runDesugarer
          some <$> DiagT.lift (.desugar moduleId) (.desugar moduleId) desugared
      let mod := { mod with pcalAlgorithm := algo }

      dumpStage .desugar moduleId mod

      pure mod
    let deps ← reportFailureOnThrow /- lines colored logLine -/ onModuleEvent mod.name <|
      mod.extends.mapM λ dep ↦
        withReader (mod.name :: ·) (resolveModule containingDir dep onModuleEvent onModuleProgress logLine)
    onModuleProgress mod.name

    reportFailureOnThrow /- lines colored logLine -/ onModuleEvent mod.name do
      let importedBindings := deps.flatMap λ (_, depMod) ↦
        (depMod.declarations₁ ++ depMod.declarations₂).flatMap (Decl.bindings depMod.name)
      let Γ₀ : Context := importedBindings.foldl (init := builtinContext) λ ctx (x, b) ↦ ctx.insert x b
      let typed ← DiagT.lift (.typeCheck moduleId) (.typeCheck moduleId)
        (CoreTLAPlus.Module.runChecker Γ₀ mod : DiagT TCWarning TCError Base _)

      dumpStage .typeCheck moduleId typed

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
          let recomputed ← compileModule src path.parent name (expectedName := some name)
            (onModuleEvent := onModuleEvent) (onModuleProgress := onModuleProgress) (logLine := logLine)
          storeModule name { sourceHash := h, «extends» := entry.extends, value := recomputed }
          return (true, recomputed)
      else
        let recomputed ← compileModule src path.parent name (expectedName := some name)
          (onModuleEvent := onModuleEvent) (onModuleProgress := onModuleProgress) (logLine := logLine)
        storeModule name { sourceHash := h, «extends» := recomputed.extends, value := recomputed }
        return (true, recomputed)
    | none =>
      let recomputed ← compileModule src path.parent name (expectedName := some name)
        (onModuleEvent := onModuleEvent) (onModuleProgress := onModuleProgress) (logLine := logLine)
      storeModule name { sourceHash := h, «extends» := recomputed.extends, value := recomputed }
      return (true, recomputed)
end

end
