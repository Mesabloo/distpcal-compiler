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
  /-- A lexing failure. -/
  | lex (e : Unexpected Char)
  /-- A parsing failure. -/
  | parse (e : Unexpected (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token)))
  /-- A `@type`/`@mailbox`/`@parameter` annotation-resolution failure. -/
  | annotation (e : ResolverError)
  /-- A Surface→Core desugaring failure (TLA⁺ expressions or the embedded PlusCal algorithm). -/
  | desugar (e : DesugarError)
  /-- `EXTENDS name` didn't resolve to any file (searched: the extending module's own directory,
  `-I`'s search path, and the builtin table). -/
  | moduleNotFound (name : String)
  /-- `EXTENDS name` resolved to more than one candidate — no silent shadowing, per review. -/
  | ambiguousModule (name : String) (foundAt : List String)
  /-- `EXTENDS` forms a cycle; `chain` is the resolution stack at the point the cycle was found,
  outermost first, with the repeated name appended at the end for a readable `A -> B -> A`. -/
  | cyclicExtends (chain : List String)
  /-- A real type-checking failure, once `Elaborator/Declarations.lean` exists to produce one. -/
  | typeCheck (e : TCError)

-- Needed for `DriverError.lex`'s wrapped `Unexpected Char` — no global `ToString Char` exists on
-- purpose (`Fugue.lean` needs the identical local instance for the same reason).
private instance : ToString Char := ⟨λ c ↦ s!"'{c}'"⟩

-- Needed for `DriverError.parse`'s wrapped `Unexpected (Token (Located' SurfacePlusCal.Token))`.
private instance {α} [ToString α] : ToString (Located' α) := ⟨λ x ↦ toString x.data⟩

instance : CompilerDiagnostic DriverError String where
  isError := true
  posOf
    | .lex e => CompilerDiagnostic.posOf e
    | .parse e => CompilerDiagnostic.posOf e
    | .annotation e => CompilerDiagnostic.posOf e
    | .desugar e => CompilerDiagnostic.posOf e
    | .moduleNotFound .. | .ambiguousModule .. | .cyclicExtends .. => default
    | .typeCheck e => CompilerDiagnostic.posOf e
  msgOf
    | .lex e => CompilerDiagnostic.msgOf e
    | .parse e => CompilerDiagnostic.msgOf e
    | .annotation e => CompilerDiagnostic.msgOf e
    | .desugar e => CompilerDiagnostic.msgOf e
    | .moduleNotFound name => s!"Could not find module '{name}'."
    | .ambiguousModule name foundAt =>
      s!"Module '{name}' is ambiguous: found at {String.intercalate ", " foundAt}."
    | .cyclicExtends chain => s!"Cyclic EXTENDS: {String.intercalate " -> " chain}."
    | .typeCheck e => CompilerDiagnostic.msgOf e

/-- Names of modules currently being resolved, outermost first — pushed via `withReader (name ::
·)` before recursing into a dependency; Lean's Reader scoping unwinds this automatically on
return, so no manual stack bookkeeping is needed. A module about to be resolved that's already in
this list is a cyclic `EXTENDS`. -/
abbrev ResolutionStack := List String

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
  not silently shadowed by a builtin, or vice versa.
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
  [MonadWithReaderOf ResolutionStack m] [MonadModuleCache TypedModule m] [MonadExceptOf DriverError m]
  [MonadLiftT IO m] [MonadLiftT BaseIO m]

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
    if ← liftM path.pathExists then
      found := found ++ [(toString path, .file path)]
  match found with
  | [] => throw (.moduleNotFound name)
  | [(_, candidate)] => return candidate
  | multiple => throw (.ambiguousModule name (multiple.map Prod.fst))

/-- Print every warning in `warnings` not suppressed by `-Wno-<name>`, `Parser_/Common.lean`'s
`ParserWarning`/`Desugarer/Errors.lean`'s `DesugarWarning` convention. `-W` filtering only needs
`FlagsEnv`, which this file already depends on (for `-I`'s search path) — no reason to bounce this
back out to `Fugue.lean` via a hook the way `-d dump-*`/spinners still are (those are genuinely
CLI presentation, this isn't). Applies uniformly to every `compileModule` call, main module and
`EXTENDS`-ed dependency alike — a dependency's own parser/desugar warnings are just as real as the
main module's, no reason to suppress them by default. -/
private def reportWarnings {m} [Monad m] [MonadReaderOf FlagsEnv m] [MonadLiftT IO m]
    {ε} [CompilerDiagnostic ε String]
    (lines : List String.Slice) (colored : Bool) (name : ε → String) (warnings : List ε) : m Unit :=
  warnings.forM λ warning ↦ do
    if ← FlagsEnv.isWarningEnabled (name warning) then
      liftM (IO.eprintln <| CompilerDiagnostic.pretty warning lines colored : IO Unit)

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
  each stage, purely so `Fugue.lean` can hang its `-d dump-*` artifact dumps and spinners off of
  them without any of that CLI/UX plumbing living in this file — `resolveModule` recursing into a
  dependency passes none, so nested resolution runs quietly on that front. Warning printing
  (`reportWarnings` above) isn't a hook, unlike an earlier draft — it doesn't need anything
  `Fugue.lean`-specific, so it just happens here directly, uniformly for every module compiled.
-/
partial def compileModule (source : String) (containingDir : Option System.FilePath)
    (onTokens : Array (Located' (SurfaceTLAPlus.Token (Located' SurfacePlusCal.Token))) → m Unit := fun _ ↦ pure ())
    (onParsed : SurfaceTLAPlus.Module
        (SurfacePlusCal.Algorithm (List SurfaceTLAPlus.CommentAnnotation) (SurfaceTLAPlus.Expression (List SurfaceTLAPlus.CommentAnnotation)))
        (List SurfaceTLAPlus.CommentAnnotation) → m Unit := fun _ ↦ pure ())
    (onDesugared : CoreTLAPlus.Module
        (CorePlusCal.Algorithm (Option SurfaceTLAPlus.Typ) (CoreTLAPlus.Expression (Option SurfaceTLAPlus.Typ)))
        (Option SurfaceTLAPlus.Typ) → m Unit := fun _ ↦ pure ())
    (onTyped : TypedModule → m Unit := fun _ ↦ pure ()) : m TypedModule := do
  let lines := source.split (· == '\n') |>.toList
  let colored ← not <$> FlagsEnv.getFeatureFlag "no-color"
  let tokens ← match SurfaceTLAPlus.Lexer.lexModule source with
    | .inl e => throw (.lex e)
    | .inr tokens => pure tokens
  onTokens tokens
  let (mod, parserWarnings) ← match SurfaceTLAPlus.Parser.parseModule tokens with
    | .inl e => throw (.parse e)
    | .inr r => pure r
  reportWarnings lines colored ParserWarning.name parserWarnings
  onParsed mod
  let mod ← match resolveAnnotations mod with
    | .error e => throw (.annotation e)
    | .ok mod => pure mod
  let mod ← match mod.runDesugarer with
    | .error e => throw (.desugar e)
    | .ok mod => pure mod
  let mod ← match mod.stripTLAPlusAnnotations with
    | .error e => throw (.desugar e)
    | .ok mod => pure mod
  let algo ← match mod.pcalAlgorithm with
    | none => pure none
    | some algo =>
      match algo.runDesugarer with
      | .error e => throw (.desugar e)
      | .ok (algo, desugarWarnings) => do
        reportWarnings lines colored DesugarWarning.name desugarWarnings
        pure (some algo)
  let mod := { mod with pcalAlgorithm := algo }
  onDesugared mod
  let _deps ← mod.extends.mapM λ dep ↦ withReader (mod.name :: ·) (resolveModule containingDir dep)
  let _Γ₀ : Context := {} -- TODO(Elaborator/Declarations.lean): merge `_deps`' declarations in
  let typed ← (throw (.typeCheck (.todo default "Type checking is not yet implemented.")) : m TypedModule)
  onTyped typed
  return typed

/--
  The `EXTENDS`-specific wrapper around `compileModule`: locate `name` (`locate` above, error on
  not-found/ambiguous), check `Ξ`, and — the review point this design started from — a cache hit
  on `name`'s own unchanged source still isn't enough: if anything `name` (transitively) depends
  on changed, `name` has to be rechecked too, even though its own text didn't. The returned `Bool`
  is exactly this: "was this module actually recomputed just now," threaded up so *its* dependents
  can tell whether they need to recompute in turn. It's `resolveModule`'s own bookkeeping, not
  part of the public `MonadModuleCache` interface.
-/
partial def resolveModule (containingDir : Option System.FilePath) (name : String) : m (Bool × TypedModule) := do
  if name ∈ (← readThe ResolutionStack) then
    throw (.cyclicExtends ((← readThe ResolutionStack).reverse ++ [name]))
  match ← locate name containingDir with
  | .builtin mod => return (false, mod)
  | .file path => do
    let src ← IO.FS.readFile path
    let h := hash src
    match ← lookupModule name with
    | some entry =>
      if entry.sourceHash == h then
        let depResults ← entry.extends.mapM λ dep ↦ withReader (name :: ·) (resolveModule containingDir dep)
        if depResults.all (¬ ·.1) then
          return (false, entry.value)
        else
          let recomputed ← compileModule src path.parent
          storeModule name { sourceHash := h, «extends» := entry.extends, value := recomputed }
          return (true, recomputed)
      else
        let recomputed ← compileModule src path.parent
        storeModule name { sourceHash := h, «extends» := recomputed.extends, value := recomputed }
        return (true, recomputed)
    | none =>
      let recomputed ← compileModule src path.parent
      storeModule name { sourceHash := h, «extends» := recomputed.extends, value := recomputed }
      return (true, recomputed)
end
