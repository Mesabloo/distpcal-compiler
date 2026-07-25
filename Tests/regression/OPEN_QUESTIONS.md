
### 9.22 The module progress line ignores `-W`
`Driver/Modules.lean` reports `ModuleOutcome.built (hadWarnings : Bool)`, and `Fugue.lean` renders
it as a yellow `⚠ [1/1] Built <Module>` when the flag is set. `hadWarnings` counts warnings as
*reported by the pass*, before `-Wno-<name>` filtering, which happens later in
`PipelineResult.renderWarnings`. So `fugue compile -Wno-duplicate-parameter` on
`accept_duplicate_parameter_warns.tla` correctly prints no warning, and still marks the module
yellow with a warning dingbat for a warning the user asked not to hear about.

Pre-existing; unrelated to the pipeline extraction that surfaced it.

**Open:** which of the two is wrong. Either the outcome should be computed after filtering (`-W`
then genuinely silences the diagnostic everywhere, and `hadWarnings` needs the `FlagsEnv` at the
point it is built), or the dingbat is deliberately reporting "this module produced warnings"
independently of whether they were displayed, and only the colour is misleading. Matters for the
regression runner once it asserts on progress lines rather than only on diagnostics.
