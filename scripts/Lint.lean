/-
Run Batteries' environment linters — dead `simp` lemmas, unused arguments, missing docstrings —
over the project. These inspect *elaborated declarations*, which no `@[linter]` (`linter.fugue.*`
or external) can do.

    lake build && lake lint [-- --all]

`@[lint_driver]` in `lakefile.lean` wires this executable into `lake lint`; `lake exe lint [--all]`
works the same. Ad-hoc: not on the `Stop` hook, not in CI. Run it before a release, or after a
`simp`-set or an API change. Building the `lint` executable does not build the project — run
`lake build` first. `simpNF` needs the whole project elaborated; expect a minute or two.

Default: `simpNF` (dead / malformed `simp` lemmas — the check that matters and cannot be a
tactic-syntax linter). `--all` adds `unusedArguments` (noisy here — every derived `Repr` ignores
its `prec`, `registerSource` ignores its tag by design) and `docBlame` (overlaps
`linter.missingDocs`, off by default here; ~400 hits — a docstring-coverage audit).

Restricting the set is `getChecks (runOnly := …)` — Batteries' `runLinter` executable runs every
registered `@[env_linter]` and has no per-linter flag, and `#lint only … in <pkg>` keys on a
shared name prefix the project's modules do not have.
-/
import Batteries.Tactic.Lint

open Lean Core Batteries.Tactic.Lint System

/-- Every default-target library root plus the CLI, i.e. every module tree the project
elaborates. Kept in step with `lakefile.lean`'s `@[default_target] lean_lib`s. -/
def projectRoots : Array Name :=
  #[`CustomPrelude, `ProgressBar, `VerifiedCompiler, `Common, `Core, `Parser_, `Desugarer,
    `WellFormedness, `Elaborator, `Driver, `Typed2Computable, `Computable2Guarded,
    `Guarded2Network, `Network2Go, `Fugue]

/-- The `@[env_linter]`s to run — those with no `@[linter]` form, so unreachable from a build. -/
def wantedLinters (all : Bool) : List Name :=
  `simpNF :: (if all then [`unusedArguments, `docBlame] else [])

unsafe def main (args : List String) : IO Unit := do
  let wanted := wantedLinters (args.contains "--all")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := (projectRoots.push `Batteries.Tactic.Lint).map ({ module := · })
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<Lint>", fileMap := default }
  discard <| (CoreM.toIO · ctx { env }) do
    let linters ← getChecks (slow := true) (runOnly := some wanted) none
    let mut seen : Std.HashSet Name := {}
    let mut decls : Array Name := #[]
    for root in projectRoots do
      for d in ← getDeclsInPackage root do
        unless seen.contains d do
          seen := seen.insert d
          decls := decls.push d
    let results ← lintCore decls linters (inIO := true)
    if results.any (!·.2.isEmpty) then
      let fmt ← formatLinterResults results decls (groupByFilename := true)
        "in the project" (runSlowLinters := true) .medium linters.size (useErrorFormat := true)
      IO.print (← fmt.toString)
      IO.Process.exit 1
    IO.println s!"-- {wanted.length} env-linter(s) over {decls.size} declarations: all clean."
