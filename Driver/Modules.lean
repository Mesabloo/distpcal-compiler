import Elaborator.Monad
import Core.TypedPlusCal.Syntax
import Parser_.TLAPlus
import Parser_.Annotations
import Desugarer.TLAPlus
import Desugarer.PlusCal
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

/-- The checker's own cached-module representation — kept as an abbrev rather than repeating the
full applied type everywhere. -/
abbrev TypedModule := TypedTLAPlus.Module TypedPlusCal.Algorithm TypedTLAPlus.Typ

/--
  This file's own errors — **not** `TCError`: nothing here is a type-checking-rule violation
  (`TCError`'s actual job), it's every way *driving* the pipeline up to and around the checker can
  fail. Wraps each lower-level pass's own error type directly (`lex`/`parse`/`annotation`/
  `desugar`) rather than collapsing them all into one generic placeholder, plus the three new
  resolution-specific conditions this session's design added (`moduleNotFound`/`ambiguousModule`/
  `cyclicExtends`), plus `typeCheck`, wrapping whatever `TCError` the (still-stubbed) checker
  itself raises — so `Fugue.lean` only ever has to handle one error type across the whole
  pipeline, without that type being a misnomer for everything that isn't actually type checking.
-/
inductive DriverError : Type
  /-- A lexing failure. `moduleId` is the *offending module's own* key into the source registry
  below — not necessarily the main module's: an error inside an `EXTENDS`-ed dependency must
  render against that dependency's own lines, not whichever module `Fugue.lean` originally
  started with. Every variant below carrying a real position carries its own `moduleId` for the
  same reason — a key, not the source text itself, so `DriverError` values stay lightweight
  rather than each one duplicating a (possibly large) source string. -/
  | lex (moduleId : String) (e : Unexpected Char)
  /-- A parsing failure. -/
  | parse (moduleId : String) (e : Unexpected (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token)))
  /-- A `@type`/`@mailbox`/`@parameter` annotation-resolution failure. -/
  | annotation (moduleId : String) (e : ResolverError)
  /-- A Surface→Core desugaring failure (TLA⁺ expressions or the embedded PlusCal algorithm). -/
  | desugar (moduleId : String) (e : DesugarError)
  /-- `EXTENDS name` didn't resolve to any file (searched: the extending module's own directory,
  `-I`'s search path, and the builtin table). -/
  | moduleNotFound (name : String)
  /-- `EXTENDS name` resolved to more than one candidate — no silent shadowing, per review. -/
  | ambiguousModule (name : String) (foundAt : List String)
  /-- `EXTENDS` forms a cycle; `chain` is the resolution stack at the point the cycle was found,
  outermost first, with the repeated name appended at the end for a readable `A -> B -> A`. -/
  | cyclicExtends (chain : List String)
  /-- A real type-checking failure, once `Elaborator/Declarations.lean` exists to produce one. -/
  | typeCheck (moduleId : String) (e : TCError)

-- Needed for `DriverError.lex`'s wrapped `Unexpected Char` — no global `ToString Char` exists on
-- purpose (`Fugue.lean` needs the identical local instance for the same reason).
private instance : ToString Char := ⟨λ c ↦ s!"'{c}'"⟩

-- Needed for `DriverError.parse`'s wrapped `Unexpected (Token (Located' SurfacePlusCal.Token))`.
private instance {α} [ToString α] : ToString (Located' α) := ⟨λ x ↦ toString x.data⟩

/-- A placeholder position for diagnostics with no real one to report (`moduleNotFound`/
`ambiguousModule`/`cyclicExtends`, and `TCError.todo`'s own stub). **Not** `default`/`(0 :
SourceSpan)` — both are `⟨⟨0,0⟩,⟨0,0⟩⟩`, but every *real* position in this codebase has 1-indexed
lines (`Parser_/TLAPlus.lean`'s `lexModule` starts lexing at `⟨1,0⟩`, not `⟨0,0⟩`) — using line
`0` here renders as an actual (wrong, off-by-one) line number, `"0 | <source line 1's text>"`
(`CompilerDiagnostic.pretty`'s `source[n - 1]!` still happens to land on line 1's text either way,
since `Nat` subtraction saturates at `0`, but the printed line *number* itself was still wrong).
Line `1` here at least points at a real line, even though the span itself is still meaningless. -/
private def noPos : SourceSpan := ⟨⟨1, 0⟩, ⟨1, 0⟩⟩

instance : CompilerDiagnostic DriverError String where
  isError := true
  posOf
    | .lex _ e => CompilerDiagnostic.posOf e
    | .parse _ e => CompilerDiagnostic.posOf e
    | .annotation _ e => CompilerDiagnostic.posOf e
    | .desugar _ e => CompilerDiagnostic.posOf e
    | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => noPos
    | .typeCheck _ e => CompilerDiagnostic.posOf e
  msgOf
    | .lex _ e => CompilerDiagnostic.msgOf e
    | .parse _ e => CompilerDiagnostic.msgOf e
    | .annotation _ e => CompilerDiagnostic.msgOf e
    | .desugar _ e => CompilerDiagnostic.msgOf e
    | .moduleNotFound name => s!"Could not find module '{name}'."
    | .ambiguousModule name foundAt =>
      s!"Module '{name}' is ambiguous: found at {String.intercalate ", " foundAt}."
    | .cyclicExtends chain => s!"Cyclic EXTENDS: {String.intercalate " -> " chain}."
    | .typeCheck _ e => CompilerDiagnostic.msgOf e

/--
  This file's own warnings — `DriverError`'s non-fatal counterpart, for the identical reason:
  a parser/desugarer/type-checker warning isn't itself a driver-level condition, but something
  has to carry it (plus its owning `moduleId`, same convention as `DriverError`) through this
  file's accumulate-then-flush machinery below (`MonadWarningAccumulator`), uniformly regardless
  of which pass produced it.
-/
inductive DriverWarning : Type
  | parser (moduleId : String) (w : ParserWarning)
  | desugar (moduleId : String) (w : DesugarWarning)
  | typeCheck (moduleId : String) (w : TCWarning)

/-- The `-W<name>`/`-Wno-<name>` name a given warning is filtered under — forwards to whichever
wrapped warning's own `.name`. -/
def DriverWarning.name : DriverWarning → String
  | .parser _ w => ParserWarning.name w
  | .desugar _ w => DesugarWarning.name w
  | .typeCheck _ w => TCWarning.name w

/-- The `moduleId` a given warning is tagged with — every variant carries one, unlike
`DriverError` (whose `moduleNotFound`/`ambiguousModule`/`cyclicExtends` carry none). -/
def DriverWarning.moduleId : DriverWarning → String
  | .parser moduleId _ | .desugar moduleId _ | .typeCheck moduleId _ => moduleId

instance : CompilerDiagnostic DriverWarning String where
  isError := false
  posOf
    | .parser _ w => CompilerDiagnostic.posOf w
    | .desugar _ w => CompilerDiagnostic.posOf w
    | .typeCheck _ w => CompilerDiagnostic.posOf w
  msgOf
    | .parser _ w => CompilerDiagnostic.msgOf w
    | .desugar _ w => CompilerDiagnostic.msgOf w
    | .typeCheck _ w => CompilerDiagnostic.msgOf w

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
against the main module's own lines (harmless: `posOf` for those is always `noPos`, so the exact
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

/--
  Standard TLA⁺ modules (`Sequences`, `TLC`, `Naturals`, `FiniteSets`, …) — a hardcoded table of
  already-checked `Module`s, **not** bundled `.tla` stub files: the compiler would need to know
  their install location, and each one would still need processing like any other module, for no
  benefit — standard-library operators (`Len`, `Head`, `Append`, …) get replaced by backend-native
  implementations at code-generation time regardless of what their "definition" says, so there's
  no reason for them to have a real body or a real file. Populated incrementally as real test
  input needs specific operators, same spirit as `TCError.todo`'s vocabulary.

  Kept as full `Module`s (not a bare declaration list) so the `Γ`-merge step in `compileModule`
  treats a builtin hit and a real resolved dependency identically:
  `mod.declarations₁ ++ mod.declarations₂`, no special case. Still subject to the same ambiguity
  rule as any other candidate source (`locate` below) — a user's own module of the same name is
  not silently shadowed by a builtin, or vice versa. A builtin `EXTENDS`ing another builtin (e.g.
  `Sequences` should itself `EXTENDS Naturals`, matching real TLA⁺) needs no separate mechanism —
  `resolveModule`'s existing recursion already generalizes to it (`PLAN.md` §9.19).

  **Not yet where `Elaborator/Declarations.lean`'s `builtinContext` operators
  (`+`/`-`/`Len`/`Head`/… ) actually live** — that prelude is a deliberate, flat, always-on
  approximation of what *should* eventually be real per-module entries here (`Naturals`'s
  arithmetic, `Sequences`'s sequence operators, …), tracked as future work rather than started now
  (`PLAN.md` §9.19).
-/
def builtinModules : Std.HashMap String TypedModule := {}

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
  let _deps ← reportFailureOnThrow lines colored logLine onModuleEvent mod.name warnings <|
    mod.extends.mapM λ dep ↦
      withReader (mod.name :: ·) (resolveModule containingDir dep onModuleEvent onModuleProgress logLine)
  onModuleProgress mod.name

  let typed ← reportFailureOnThrow lines colored logLine onModuleEvent mod.name warnings do
    let _Γ₀ : Context := {} -- TODO(Elaborator/Declarations.lean): merge `_deps`' declarations in
    let typed ← (throw (.typeCheck moduleId (.todo noPos "Type checking is not yet implemented.")) : m TypedModule)

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
  | .builtin mod => return (false, mod)
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
