import Lake
open Lake DSL

------ Dependencies
require "leanprover-community" / "mathlib" @ git s!"v{Lean.versionString}"
require "leanprover-community" / "batteries" @ git s!"v{Lean.versionString}"
require "fgdorais" / "UnicodeBasic" @ git "v2.0.1"
require "fgdorais" / "Parser" @ git "4a9f45abc119e9a03e9ae41ee80b1cd15ed66467"
require "leanprover" / "Cli" @ git s!"v{Lean.versionString}"
require "leanprover-community" / "LeanSearchClient" @ git "c5d5b8fe6e5158def25cd28eb94e4141ad97c843"
require "algebraic-dev" / "Colorized" @ git "e631ffd114535e1ace876e1b7062d672f718454f"

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
]
@[inherit_doc Package.moreServerOptions]
abbrev moreServerOptions : Array LeanOption := #[]

run_cmd do
  println! "Building package in {buildType} mode (with missing docs := {warnOnMissingDocs})"

------- Config
package Fugue where
  leanOptions := leanOptions
  moreLeanArgs := moreLeanArgs.map λ o ↦ o.asCliArg
  moreServerOptions := moreServerOptions
  buildType := buildType

/-- A custom prelude with various tactics and additional imports. -/
lean_lib CustomPrelude
/-- Extra definitions and theorems on common data structures. -/
lean_lib Extra
/-- Terminal progress bars. -/
lean_lib ProgressBar
/-- A library for compiler verification through denotational semantics. -/
lean_lib VerifiedCompiler

/-- Simple theories for various stuff (positions, diagnostics, etc.). -/
lean_lib Fugue.Common where
  roots := #[`Common]
/-- Definitions of ASTs and semantics for our intermediate languages, along with useful lemmas. -/
lean_lib Fugue.Core where
  roots := #[`Core]
/-- The parser for TLA+ modules and Distributed PlusCal algorithms. -/
lean_lib Fugue.Parser where
  roots := #[`Parser_]
/-- Surface-to-Core desugaring (TLA+ expressions and PlusCal statements). -/
lean_lib Fugue.Desugarer where
  roots := #[`Desugarer]
/-- Well-labelledness, variable well-scopedness, and no-bare-temporal-op checks over Core ASTs. -/
lean_lib Fugue.WF where
  roots := #[`WellFormedness]
/-- The bidirectional type checker, Core to Typed. -/
lean_lib Fugue.Elaborator where
  roots := #[`Elaborator]
/-- Transform typed PlusCal algorithms into Guarded PlusCal (the cflow/par/flat/reord pipeline). -/
lean_lib Fugue.T2G where
  roots := #[`Typed2Guarded]
/-- Compiler from Guarded PlusCal to Network PlusCal, including its refinement proof. -/
lean_lib Fugue.G2N where
  roots := #[`Guarded2Network]
/-- Compiler from Network PlusCal to the Join Calculus. -/
lean_lib Fugue.N2JC where
  roots := #[`Network2JoinCalculus]
/-- Compiler from Network PlusCal to Go, including lock inference. -/
lean_lib Fugue.N2Go where
  roots := #[`Network2Go]

@[default_target]
lean_exe fugue where
  root := `Fugue
