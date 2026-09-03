/-
List project `.lean` files that no library or executable root transitively imports.

Run from the project root, no build required:

    lake env lean --run scripts/OrphanCheck.lean

An orphan module is never a build target and never a local import, so `lake build` / `lake test`
never elaborate it — and no `@[linter]`, `linter.fugue.*` or external, ever runs on it
(`LEAN_STYLE.md` module-system rule, `INSTRUCTIONS.md` §Build). This is an ad-hoc check: run it
before a release or after moving files, not on every `Stop`. Exit code 1 when orphans are found.

Roots are every top-level `*.lean` (each is a `lean_lib` root or an executable root) plus
`Tests/Main.lean` (the `test` executable). `Extra/Mathlib/` is vendored and excluded from the
report. Imports are read with `Lean.parseImports'` — no elaboration, so this runs in a second.
-/
import Lean

open Lean System

/-- Directories with no project source, or source produced/managed by other means. -/
def skipDirs : List String :=
  [".lake", ".claude", ".git", ".fugue", "reference", "runtime", "persistent", "docs", "scripts"]

/-- Top-level files that are not project modules. -/
def skipFiles : List String := ["lakefile.lean"]

/-- Modules excluded from the orphan report even when unreached: vendored upstream code. -/
def exemptPrefixes : List Name := [`Extra.Mathlib]

/-- Every `.lean` file under `dir`, recursively, skipping `skipDirs`. -/
partial def leanFilesIn (dir : FilePath) : IO (Array FilePath) := do
  let mut out : Array FilePath := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      unless skipDirs.contains e.fileName do
        out := out ++ (← leanFilesIn e.path)
    else if e.fileName.endsWith ".lean" && !skipFiles.contains e.fileName then
      out := out.push e.path
  return out

/-- `./Core/Foo.lean` → `` `Core.Foo ``. -/
def pathToModule (p : FilePath) : Name :=
  let dirs := (p.parent.getD (FilePath.mk ".")).components.filter (· != ".")
  (dirs ++ [p.fileStem.getD p.toString]).foldl (·.mkStr ·) Name.anonymous

/-- `` `Core.Foo `` → `Core/Foo.lean`. -/
def moduleToPath (m : Name) : FilePath :=
  (mkFilePath (m.components.map (·.toString))).addExtension "lean"

/-- The module names `import`ed by the file at `p` (`Init` filtered out); `#[]` on a parse error,
which a real build would report anyway. -/
def directImports (p : FilePath) : IO (Array Name) := do
  try
    let h ← Lean.parseImports' (← IO.FS.readFile p) p.toString
    return h.imports.map (·.module) |>.filter (· != `Init)
  catch e =>
    IO.eprintln s!"warning: could not parse imports of {p}: {e.toString}"
    return #[]

def main (_ : List String) : IO Unit := do
  let onDisk := (← leanFilesIn ".").map pathToModule
  let known : Std.HashSet Name := onDisk.foldl (·.insert ·) {}

  let mut roots : Array Name := #[`Tests.Main]
  for e in ← (FilePath.mk ".").readDir do
    if e.fileName.endsWith ".lean" && !skipFiles.contains e.fileName then
      roots := roots.push (pathToModule e.path)

  -- transitive closure of imports from the roots, restricted to project modules
  let mut reached : Std.HashSet Name := {}
  let mut queue := roots
  while h : queue.size > 0 do
    let m := queue[queue.size - 1]
    queue := queue.pop
    if reached.contains m then continue
    reached := reached.insert m
    if known.contains m then
      for imp in ← directImports (moduleToPath m) do
        unless reached.contains imp do queue := queue.push imp

  let orphans := onDisk.filter λ m ↦
    !reached.contains m && !exemptPrefixes.any (·.isPrefixOf m)
  let orphans := orphans.qsort (·.toString < ·.toString)

  if orphans.isEmpty then
    IO.println s!"no orphan modules ({known.size} project modules, {reached.size} reached)"
  else
    IO.println s!"{orphans.size} orphan module(s) — never elaborated, no linter runs on them:"
    for m in orphans do
      IO.println s!"  {moduleToPath m}"
    IO.Process.exit 1
