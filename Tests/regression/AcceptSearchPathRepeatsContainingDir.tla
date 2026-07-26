---- MODULE AcceptSearchPathRepeatsContainingDir ----
\* Expect: accepted. The sidecar's `searchPath: ["."]` points `-I` at this fixture's own
\* directory, so `EXTENDS AcceptDepModuleVariable` finds the identical file twice over --- once
\* via the containing directory, once via `-I` --- spelled two different ways. `Driver/Modules.lean`'s
\* `locate` canonicalizes each candidate through `IO.FS.realPath` and keeps one entry per real
\* file, so this resolves instead of reporting a false `ambiguousModule` listing the same path
\* twice. The only fixture that uses the sidecar's `searchPath`, and the only regression cover
\* for `-I` at all.

EXTENDS AcceptDepModuleVariable

\* @type: Int;
x == 1

====
