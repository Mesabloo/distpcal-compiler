import Lake
open Lake DSL

------ Dependencies
require "leanprover-community" / "mathlib" @ git s!"v{Lean.versionString}"
require "leanprover-community" / "batteries" @ git s!"v{Lean.versionString}"
require "fgdorais" / "UnicodeBasic" @ git "v2.0.1"
require "fgdorais" / "Parser" @ git "4a9f45abc119e9a03e9ae41ee80b1cd15ed66467"
require "leanprover" / "Cli" @ git s!"v{Lean.versionString}"
require "leanprover-community" / "LeanSearchClient" @ git "c5d5b8fe6e5158def25cd28eb94e4141ad97c843"
require Colorized
  from git "https://github.com/anzenlang/Colorized" @ "b59df24859e41dc1aecb46c004d8295e0bb3e2c1"
-- "anzenlang" / "Colorized" @ git "b59df24859e41dc1aecb46c004d8295e0bb3e2c1"
require "vtrelat" / "zflean" @ git s!"v{Lean.versionString}"

------ Options

/--
  Whether to emit warnings for definitions lacking documentation.
-/
def warnOnMissingDocs : Bool := (get_config? NO_CHECK_DOC).isNone

/--
  The current build type, determined from the CLI `-K` option `BUILD_TYPE`.

  See `Lake.BuildType.ofString?` for accepted formats. Parsing errors yield a debug build.
-/
def buildType : BuildType := (get_config? BUILD_TYPE >>= BuildType.ofString?).getD .debug

@[inherit_doc Package.moreLeanArgs]
abbrev moreLeanArgs : Array LeanOption := #[
  ⟨`linter.missingDocs, warnOnMissingDocs⟩ -- Warning on non-documented object
]
@[inherit_doc Package.leanOptions]
abbrev leanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩, -- Fully disable auto implicits
  ⟨`pp.unicode.fun, true⟩, -- Pretty-print lambdas as `λ x ↦ y`
  ⟨`weak.linter.docPrime, false⟩, -- No warning when no doc on symbol ending with `'`
  ⟨`pp.showLetValues.tactic.threshold, .ofNat 0⟩,
  ⟨`pp.showLetValues.threshold, .ofNat 0⟩,
  ⟨`mvcgen.warning, false⟩, -- `mvcgen` used deliberately project-wide; skip experimental-tactic notice
]
@[inherit_doc Package.moreServerOptions]
abbrev moreServerOptions : Array LeanOption := #[]

------ Version

/--
  The compiler's version, and the one place it is written: the `version` field below takes it,
  `lake` reports it, and the generated `Version.lean` — see `versionModule` — is what the CLI
  prints.
-/
def fugueVersion : LeanVer := v!"0.1.0"

/-- Where the generated `Version.lean` is written, relative to the package root. Under `.lake/`
but *outside* `.lake/build/`, which is what `lake clean` deletes: the generated source and the
compiled configuration that writes it must disappear together (`rm -rf .lake`) or survive
together, never one without the other. -/
def versionSrcDir : System.FilePath := ".lake" / "version"

/--
  The contents of `Version.lean`, the generated module that carries `fugueVersion` into compiled
  code.

  A generated *source file* rather than a Lean option, which is the obvious channel and the wrong
  one: the compiler elaborates with `leanOptions`/`moreLeanArgs` and the language server with
  `moreServerOptions`, so the two disagree about the elaboration environment and overwrite each
  other's `.olean`s. A source file is read identically by both.

  It is also the only channel Lake traces. A module's build depends on its own source, its
  options, its imports and the toolchain, and on nothing else — so an `input_file` named in
  `extraDepTargets` would not rebuild anything either (that trace reaches the module's *setup*,
  not the build of its artifacts).
-/
def versionModule : String := String.intercalate "\n" [
  "module",
  "",
  "/-!",
  "  GENERATED FILE — do not edit, and do not commit.",
  "",
  "  Written by `lakefile.lean` from the `Fugue` package's `version` field, which is the one place",
  "  the compiler's version is set. Rewritten whenever `lakefile.lean` is elaborated, which is",
  "  whenever it changes.",
  "-/",
  "",
  "public section",
  "",
  "/-- The compiler's version, as `fugue --version` reports it. -/",
  s!"abbrev fugueVersion : String := \"{fugueVersion}\"",
  "",
  "end",
  ""
]

run_cmd do
  println! "Building package in {buildType} mode (with missing docs := {warnOnMissingDocs})"
  -- Runs when this file is elaborated, which is when it changes and no oftener — exactly when the
  -- version can have changed. Rewritten only when the contents would differ, so an unchanged
  -- version does not touch the file and Lake does not rebuild anything.
  let path := __dir__ / versionSrcDir / "Version.lean"
  let current ← if ← path.pathExists then IO.FS.readFile path else pure ""
  unless current == versionModule do
    IO.FS.createDirAll (__dir__ / versionSrcDir)
    IO.FS.writeFile path versionModule

------- Config
package Fugue where
  version := fugueVersion
  leanOptions := leanOptions
  moreLeanArgs := moreLeanArgs.map λ o ↦ o.asCliArg
  moreServerOptions := moreServerOptions
  buildType := buildType

/-- The generated `Version.lean`. A `lean_lib` of its own for two reasons: `Fugue.lean` can only
import a module some library claims (see `Fugue.Tests` below), and scoping it here means a version
bump rebuilds this module and the CLI rather than everything sharing a library with it. -/
@[default_target]
lean_lib Fugue.Version where
  srcDir := versionSrcDir
  roots := #[`Version]

/-- A custom prelude with various tactics and additional imports. -/
@[default_target]
lean_lib CustomPrelude
/-- Extra definitions and theorems on common data structures. -/
lean_lib Extra
/-- Terminal progress bars. -/
@[default_target]
lean_lib ProgressBar
/-- A library for compiler verification through denotational semantics. -/
@[default_target]
lean_lib VerifiedCompiler

/-- Simple theories for various stuff (positions, diagnostics, etc.). -/
@[default_target]
lean_lib Fugue.Common where
  roots := #[`Common]
/-- Definitions of ASTs and semantics for our intermediate languages, along with useful lemmas. -/
@[default_target]
lean_lib Fugue.Core where
  roots := #[`Core]
/-- The parser for TLA+ modules and Distributed PlusCal algorithms. -/
@[default_target]
lean_lib Fugue.Parser where
  roots := #[`Parser_]
/-- Surface-to-Core desugaring (TLA+ expressions and PlusCal statements). -/
@[default_target]
lean_lib Fugue.Desugarer where
  roots := #[`Desugarer]
/-- Well-labelledness, variable well-scopedness, and no-bare-temporal-op checks over Core ASTs. -/
@[default_target]
lean_lib Fugue.WF where
  roots := #[`WellFormedness]
/-- The bidirectional type checker, Core to Typed. -/
@[default_target]
lean_lib Fugue.Elaborator where
  roots := #[`Elaborator]
/-- Recursive `EXTENDS` module resolution — not type-checking rules, but the driver-level
orchestration around invoking them. -/
@[default_target]
lean_lib Fugue.Driver where
  roots := #[`Driver]
/-- Translate the checked module into its computable (`ComputableTLAPlus`/`ComputablePlusCal`)
fragment. -/
@[default_target]
lean_lib Fugue.T2C where
  roots := #[`Typed2Computable]
/-- Transform typed PlusCal algorithms into Guarded PlusCal (the cflow/par/flat/reord pipeline). -/
@[default_target]
lean_lib Fugue.T2G where
  roots := #[`Computable2Guarded]
/-- Compiler from Guarded PlusCal to Network PlusCal, including its refinement proof.

`Guarded2Network` privately imports `Guarded2Network.CorrectInstance` (the refinement proof pinned
to the concrete `Value` semantics, `ZFSet` via `zflean`), so every consumer of this pass builds and
checks that proof. The import is private because `zflean` reserves `ε` as term notation, which would
otherwise shadow the `ε` type variables in `Driver` and the later passes. -/
@[default_target]
lean_lib Fugue.G2N where
  roots := #[`Guarded2Network]
/-- Compiler from Network PlusCal to the Join Calculus. -/
lean_lib Fugue.N2JC where
  roots := #[`Network2JoinCalculus]
/-- Compiler from Network PlusCal to Go, including lock inference. -/
@[default_target]
lean_lib Fugue.N2Go where
  roots := #[`Network2Go]

/-- Linker flags for a `release` build of `fugue`: strip local symbols and dead code, spelled for
the host platform's linker (`ld64` on macOS, GNU `ld` elsewhere). Empty on Windows. -/
def releaseLinkArgs : Array String :=
  if System.Platform.isOSX then #["-Wl,-x,-dead_strip"]
  else if System.Platform.isWindows then #[]
  else #["-Wl,--strip-all"]

lean_exe fugue where
  root := `Fugue
  moreLinkArgs := match buildType with
    | .release => releaseLinkArgs
    | _ => #[]

/-- The regression suite's modules. A `lean_lib` and not just the `lean_exe` root below because
Lake only discovers a package's modules through a library's globs: an executable's root is built
by recursively building its *local imports*, and an import only counts as local if some library
already claims it. Without this, `lake build test` fails with "object file … of module
Tests.Report does not exist". -/
lean_lib Fugue.Tests where
  roots := #[`Tests]

/-- The regression suite (`lake test -- [FILTER…]`). Runs every `tests/regression/*.tla` fixture
through the compiler, in-process. -/
@[test_driver]
lean_exe test where
  root := `Tests.Main

/-- Print `fugueVersion` to stdout and nothing else. Consumed by CI release tagging. -/
script «get-version» do
  IO.println s!"{fugueVersion}"
  return 0
