import Lake
open Lake DSL

------ Dependencies
require "leanprover-community" / "mathlib" @ git s!"v{Lean.versionString}"
require "leanprover-community" / "batteries" @ git s!"v{Lean.versionString}"
require "fgdorais" / "UnicodeBasic" @ git "ff04f5c424e50e23476d3539c7c0cc4956e971ad"
require "fgdorais" / "Parser" @ git "d8428e25efb794c9147bb9beac1dfe2e51447c3e"
require "leanprover" / "Cli" @ git s!"v{Lean.versionString}"
require "leanprover-community" / "LeanSearchClient" @ git "c5d5b8fe6e5158def25cd28eb94e4141ad97c843"
require "algebraic-dev" / "Colorized" @ git "e631ffd114535e1ace876e1b7062d672f718454f"
-- require mpl from git "https://github.com/sgraf812/mpl" @ "252f4d18ad8cf53aec243eba0e5989698c3ca509"

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
  -- ⟨`pp.showLetValues, false⟩ -- Do not show the values of `let`s in goals
  ⟨`pp.showLetValues.tactic.threshold, .ofNat 0⟩,
  ⟨`pp.showLetValues.threshold, .ofNat 0⟩,
]
@[inherit_doc Package.moreServerOptions]
abbrev moreServerOptions : Array LeanOption := #[
  --⟨`termColors, false⟩
]

run_cmd do
  println! "Building package in {buildType} mode (with missing docs := {warnOnMissingDocs})"

------- Config
package «PlusCalCompiler» where
  leanOptions := leanOptions
  moreLeanArgs := moreLeanArgs.map λ o ↦ o.asCliArg
  moreServerOptions := moreServerOptions
  buildType := buildType

  testDriver := "tests"

@[default_target]
lean_lib «CustomPrelude»

lean_lib «Extra»

@[default_target]
lean_lib «ProgressBar»

@[default_target]
lean_lib «VerifiedCompiler»

@[default_target]
lean_lib «PlusCalCompiler»

lean_exe «pcvc» where
  root := `Main

lean_lib tests where
  globs := #[.submodules `tests]
