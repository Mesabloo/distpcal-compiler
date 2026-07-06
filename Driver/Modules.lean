import Driver.Errors
import Driver.Builtins
import Common.Flags

open Colorized (Colorized)

/-!
  Recursive `EXTENDS` module resolution (`PLAN.md` §2/§5.3) — **not** type-checking rules, the
  driver-level orchestration around invoking them. Lives outside `Elaborator/` on purpose: this
  file locates, lexes, parses, desugars, and (eventually) checks a module, recursing on its own
  `EXTENDS` list the same way for each dependency — it calls into the checker as one step, but
  isn't itself part of the checker.

  **Module resolution *is* recursive driver invocation, not a second copy of the driver.**
  `compileModule` below is the one function that runs a module's source all the way through to a
  checked module; `Fugue.lean`'s CLI entry point calls it directly for the main module, and
  `resolveModule` calls it again, recursively, for every `EXTENDS`-ed dependency — there is
  exactly one implementation of "lex → parse → desugar → resolve deps → check", not two.
-/

/--
  Raw module source text by `moduleId`, so `DriverError` can carry just the lightweight key
  (above) rather than duplicating a (possibly large) source string into every thrown error —
  looked up again only once, at the point an error is finally rendered. Mirrors `Ξ`
  (`MonadModuleCache`)'s own class-plus-generic-instance-plus-concrete-backing-ref shape.
-/
class MonadSourceRegistry (m : Type → Type) where
  registerSource : String → String → m Unit
  lookupSource : String → m (Option String)
export MonadSourceRegistry (registerSource lookupSource)

instance {m} [Monad m] [MonadStateOf (Std.HashMap String String) m] : MonadSourceRegistry m where
  registerSource key source := modify (·.insert key source)
  lookupSource key := (·.get? key) <$> get

/-- Backing store for the source registry, mirroring `Common/Flags.lean`'s `flagsRef`/`Ξ`'s own
`moduleCacheRef`. -/
initialize sourceRegistryRef : IO.Ref (Std.HashMap String String) ← IO.mkRef {}

instance : MonadStateOf (Std.HashMap String String) IO where
  get := sourceRegistryRef.get
  set := sourceRegistryRef.set
  modifyGet := sourceRegistryRef.modifyGet

/-- The source lines to render `err`'s snippet against — the offending module's own, looked up
from the registry above by `moduleId`, not whichever module the caller started compiling from.
`none` for the position-free structural errors (`moduleNotFound`/`ambiguousModule`/
`cyclicExtends`, which carry no `moduleId` at all) — the caller should fall back to rendering
against the main module's own lines (harmless: `posOf` for those is always `SourceSpan.placeholder`, so the exact
lines passed barely matter). Hardcoded to `IO` rather than generic over `m`: this is only
ever called once, in `Fugue.lean`, *after* `runM` has already unwrapped back down to plain `IO` —
same registry either way, since its backing ref is process-global. -/
def DriverError.sourceLines (err : DriverError) : IO (Option (List String.Slice)) := do
  let moduleId? := match err with
    | .lex moduleId _ | .parse moduleId _ | .annotation moduleId _ | .desugar moduleId _ | .typeCheck moduleId _ =>
      some moduleId
    | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => none
  match moduleId? with
  | none => return none
  | some moduleId => return (·.split (· == '\n') |>.toList) <$> (← lookupSource moduleId)

/-- Names of modules currently being resolved, outermost first — pushed via `withReader (name ::
·)` before recursing into a dependency; Lean's Reader scoping unwinds this automatically on
return, so no manual stack bookkeeping is needed. A module about to be resolved that's already in
this list is a cyclic `EXTENDS`. -/
abbrev ResolutionStack := List String

/-- What happened when `compileModule`/`resolveModule` finished with a given module name — the
payload `onModuleEvent` reports, Lean-`lake build`-style (`Fugue.lean` turns this into
`Built`/`Replayed`/`Failed <name>`). `.failed` is reported (then the underlying `DriverError` is
re-thrown unchanged) as soon as a module's own name is known but something past that point failed
— lex/parse failures, which happen *before* a name is known, aren't attributed to any module this
way and just surface as the overall compile failure. -/
inductive ModuleOutcome : Type
  | built
  | replayed
  | failed

/--
  The module cache `Ξ`. Lives here, not in `Elaborator/Monad.lean`: it isn't a type-*checking*
  effect (expression/declaration-level checking rules never touch `Ξ`), it's this file's own
  module-*resolution* effect — `Γ` is always fully assembled from already-resolved dependencies
  before a module's own checking rules ever run.

  Keyed by module name alone, **not** by name-plus-hash: the hash of a candidate file isn't known
  until *after* it has already been located and read, so it can't be part of a lookup key —
  `resolveModule` looks up by name first, then compares the returned `CacheEntry.sourceHash`
  against the freshly-read file's own hash itself.
-/
structure CacheEntry (β : Type) : Type where
  /-- The hash of the source text that produced `value`. -/
  sourceHash : UInt64
  /-- The `EXTENDS` list recorded when this entry was written — trustworthy without re-parsing
  exactly because a matching `sourceHash` means the file (and therefore its `EXTENDS` clause) is
  byte-identical to what produced this entry. Lets `resolveModule` check whether any dependency
  changed without re-lexing/parsing a module whose own text is unchanged. -/
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

/-
  The effects `compileModule`/`resolveModule` need beyond ordinary IO: `Γ`'s enclosing `FlagsEnv`
  (for `-I`'s search path), the resolution stack (cycle detection), the module cache, and error
  reporting. **Not** a `class abbrev` bundle like `MonadElaborator`/`MonadDesugarerExpr` — two
  different `MonadReaderOf`/`MonadWithReaderOf` instantiations (`FlagsEnv` and
  `ResolutionStack`) as parents of the same abbrev collide (`class abbrev`'s `extends` treats
  them as the same parent and silently drops one), so every constraint is listed explicitly on
  each function instead.
-/

/-- The concrete monad `compileModule`/`resolveModule` run at when actually invoked (by
`Fugue.lean`, or recursively by `resolveModule` itself). `FlagsEnv`/`Ξ` are both backed by a
global `IO.Ref` (`flagsRef`/`moduleCacheRef` below) and reachable directly at `IO` via their own
instances — `ResolutionStack` is the one piece here that's a genuinely *scoped* Reader
(push-on-recurse, pop-on-return), which a global ref can't express, so it's the one transformer
layer actually needed on top of `IO`. -/
abbrev M := ReaderT ResolutionStack (ExceptT DriverError IO)

/-- Run an `M` action from the top, with an empty resolution stack. -/
def runM {α} (act : M α) : IO (Except DriverError α) :=
  (ReaderT.run act []).run

/-- Backing store for `Ξ`, mirroring `Common/Flags.lean`'s `flagsRef` pattern. -/
initialize moduleCacheRef : IO.Ref (Std.HashMap String (CacheEntry TypedModule)) ← IO.mkRef {}

instance : MonadStateOf (Std.HashMap String (CacheEntry TypedModule)) IO where
  get := moduleCacheRef.get
  set := moduleCacheRef.set
  modifyGet := moduleCacheRef.modifyGet

/-- Where a candidate module named `name` was found — a real file, or the builtin table. -/
private inductive Candidate : Type
  | file (path : System.FilePath)
  | builtin (mod : TypedModule)

variable {m : Type → Type} [Monad m] [MonadReaderOf FlagsEnv m] [MonadReaderOf ResolutionStack m]
  [MonadWithReaderOf ResolutionStack m] [MonadModuleCache TypedModule m] [MonadSourceRegistry m]
  [MonadExceptOf DriverError m] [MonadLiftT IO m]

/-- Every directory searched for `EXTENDS name`, in order: the directory containing the
extending module (if any — absent when read from stdin), then `-I`'s search path, per the
project owner's review. The builtin table is checked as one more candidate *source*, not a
filesystem-bypassing priority lookup — so a name present in both a searched directory and
`builtinModules` is ambiguous, not silently resolved one way. -/
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

/-- Print every warning in `warnings` not suppressed by `-Wno-<name>`, in one batch — never as
they're produced. Matches `lake build`'s own behaviour: a module's warnings only ever appear once
its outcome (`Built`/`Replayed`/`Failed`, `onModuleEvent`) is known, not interleaved before it.
Every call site passes only warnings collected for *this* module's own `compileModule` call — a
dependency's warnings are flushed by its own recursive call, under its own name, never merged into
a dependent's batch (see `compileModule`'s own doc). `-W` filtering only needs `FlagsEnv`, which
this file already depends on (for `-I`'s search path).

Where the rendered line actually *goes* (`logLine`) is pluggable, defaulting to plain `eprintln` —
`Fugue.lean` overrides it to go through its spinner instead (`Spinner.log`), so a warning printed
while the spinner is animating doesn't corrupt the display. -/
private def flushWarnings {m} [Monad m] [MonadReaderOf FlagsEnv m] [MonadLiftT IO m]
    (lines : List String.Slice) (colored : Bool)
    (logLine : String → m Unit) (warnings : List DriverWarning) : m Unit :=
  warnings.forM λ warning ↦ do
    if ← FlagsEnv.isWarningEnabled warning.name then
      logLine <| CompilerDiagnostic.pretty warning lines colored

/-- Run `act`; if it throws, flush `warnings` (collected so far for this module), report `name` as
`.failed` via `onModuleEvent`, and re-throw the *same* error unchanged (this never swallows or
replaces it — it's purely an extra report alongside the ordinary propagation). Factored out since
`compileModule` needs this exact flush/report/re-throw shape three times, at points that must
*not* share one `try` (see `compileModule`'s own doc for why). -/
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

/-- Every name/type binding a checked declaration introduces, mirroring `Elaborator/
Declarations.lean`'s own `checkDeclaration`'s second return component — but computed from an
already-checked `Decl`, not by re-checking one. Used to expose an `EXTENDS`-ed dependency's own
declarations into a fresh `Γ₀` (thesis Fig. 3.1.12's `Extend` rule: all of a dependency's own
`params`/`defs` come into scope, not just its exported operators — PlusCal-internal declarations
are *not* included, `Elaborator/Elaborator.lean`'s own note: they never leak into a module's `Γ`
in the first place, so a dependency's checked `pcalAlgorithm` is never consulted here at all). -/
private def Decl.bindings : Decl → List (String × TypedTLAPlus.Typ)
  | .constants xs => xs
  | .variables xs => xs
  | .assume _ => []
  | .operator τ f _ _ => [(f, τ)]
  | .function τ f _ _ => [(f, τ)]

-- `compileModule`/`resolveModule` call each other recursively (a module's own `EXTENDS` list is
-- resolved by calling `resolveModule`, which falls back to `compileModule` on a cache
-- miss/mismatch) — `mutual`, and `partial` since termination here depends on cyclic-`EXTENDS`
-- detection (`ResolutionStack`) at runtime, not on any argument that's structurally decreasing.
private instance {m} [Applicative m] {α} [Inhabited α] : Inhabited (m α) := ⟨pure default⟩

mutual
/--
  Run a module's source all the way through to a checked module: lex, parse, resolve
  annotations, desugar TLA⁺ expressions and the embedded PlusCal algorithm (reconciling
  `mod.pcalAlgorithm` with the separately-desugared algorithm — the standing Phase-4 loose end),
  resolve every `EXTENDS`-ed dependency (`resolveModule`, recursing into `compileModule` again for
  anything not already satisfied by the cache or a builtin), merge their exported declarations
  into an initial `Γ`, and check. The one shared pipeline — see the module doc for why there
  isn't a second copy of it for `EXTENDS`-triggered resolution.

  `onTokens`/`onParsed`/`onDesugared`/`onTyped` are optional hooks (default: no-op) fired after
  each stage, purely so `Fugue.lean` can hang its `-d dump-*` artifact dumps off of them without
  any of that CLI/UX plumbing living in this file — `resolveModule` recursing into a dependency
  passes none of these four, so a dependency's own dump artifacts stay silent by default (unlike
  `onModuleEvent`/`onModuleProgress`/`logLine` below, which *do* get threaded down to every
  recursively-resolved dependency, since "some module is/was being worked on" and "a warning
  happened" are relevant no matter how deep the `EXTENDS` chain).

  `onModuleProgress name` fires twice for this exact module: once as soon as `name` is known
  (right after parsing), and again right after its own `EXTENDS` dependencies are done resolving
  — refocusing display back onto this module once its dependencies (which fire their own
  `onModuleProgress` while *they* run) are no longer the "current" one. Firing it twice with the
  same name is intentional, not a bug: `Fugue.lean` tracks a set of every name it's seen, so a
  repeat is a no-op there, it just moves the displayed "current module" back to this one.

  `onModuleEvent name .built` fires once this module is fully checked, and `.failed` if this
  module's *own* processing throws — this is the *one* place `.built`/`.failed` get reported (not
  `resolveModule`, which only ever reports `.replayed` itself and otherwise defers to whichever
  `compileModule` call it made), so a module compiled directly as the main module and one reached
  via `EXTENDS` are reported identically, without duplicating the event. **Deliberately does not
  wrap the `_deps.mapM` step below in the same failure-reporting `try`**: a dependency that fails
  already reports `.failed` for *itself*, inside its own recursive `compileModule` call — if this
  module's own `try` also caught that (propagated) exception and reported `.failed` again under
  *this* module's name, a single real failure deep in an `EXTENDS` chain would misleadingly show
  every module on the path back to the main one as "failed" too, when only the one at the bottom
  actually is.

  `moduleId` is the registry key `DriverError`'s variants tag themselves with (see
  `MonadSourceRegistry`) — registered against `source` right at the start, before lexing even
  runs, so a lex/parse failure (before any real module name is known) still has something to key
  its error against. For a dependency this is the `EXTENDS`-requested name (`resolveModule`
  already has it before reading the file at all); for the main module it's whatever caller-chosen
  identifier `Fugue.lean` passes (e.g. the input file's display name).
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
      (depMod.declarations₁ ++ depMod.declarations₂).flatMap Decl.bindings
    let Γ₀ : Context := importedBindings.foldl (init := builtinContext) λ ctx (x, τ) ↦ ctx.insert x τ
    let typed ← match mod.runChecker Γ₀ with
      | .error e => throw (.typeCheck moduleId e)
      | .ok typed => pure typed

    if ← FlagsEnv.getDebugFlag "dump-typed" then
      dumpToFile (reprStr typed) dumpDir s!"{moduleId}-typed"

    return typed

  flushWarnings lines colored logLine warnings
  onModuleEvent mod.name .built
  return typed

/--
  The `EXTENDS`-specific wrapper around `compileModule`: locate `name` (`locate` above, error on
  not-found/ambiguous), check `Ξ`, and — the review point this design started from — a cache hit
  on `name`'s own unchanged source still isn't enough: if anything `name` (transitively) depends
  on changed, `name` has to be rechecked too, even though its own text didn't. The returned `Bool`
  is exactly this: "was this module actually recomputed just now," threaded up so *its* dependents
  can tell whether they need to recompute in turn. It's `resolveModule`'s own bookkeeping, not
  part of the public `MonadModuleCache` interface.

  Fires `onModuleEvent name .replayed` itself on the one path that never touches `compileModule`
  at all (a cache hit with nothing changed) — every other outcome (`.built`/`.failed`) is reported
  by whichever `compileModule` call `resolveModule` makes, not duplicated here. Not for `.builtin`
  either — a builtin is static, never meaningfully built/replayed/failed. `onModuleProgress name`
  fires once, right at the top of the `.file` case (before even checking `Ξ`) — "we're now working
  on `name`", whether that turns out to be a cache hit or a fresh recompute. `logLine` is just
  forwarded to whatever `compileModule` call this makes.
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
