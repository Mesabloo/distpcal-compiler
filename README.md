# Fugue

> In classical music, a **fugue** (/fjuːɡ/, from Latin *fuga*, meaning 'flight' or
> 'escape') is a contrapuntal, polyphonic compositional technique in two or more
> voices, built on a subject (a musical theme) that is introduced at the beginning in
> imitation (repetition at different pitches), which recurs frequently throughout the
> course of the composition.
>
> [Wikipedia, *Fugue*](https://en.wikipedia.org/wiki/Fugue)

Several voices state the same subject in turn, each entering a little behind the last,
and gradually settle into one line. A distributed algorithm does much the same:
independent processes, each running its own copy of the logic, drifting in and out of
step and converging on a shared outcome, though never quite together: PlusCal's atomic
blocks are what impose the delay. And *fuga*, a flight from something, fits in its own
way.

Fugue is a compiler for Distributed PlusCal algorithms (PlusCal extended with FIFO
channels and `send`, `receive` and `multicast`) into real Go: ordinary, readable code
using goroutines and channels, linked against a small runtime library kept in this
repository.

It is written in the Lean 4 proof assistant, and is built to be *verified*: the
compiler is structured so that each stage can carry a machine-checked proof that its
output preserves the behaviour of its input.

## Install

### Pre-built binaries

Every push to `master` publishes a release with binaries for Linux, macOS and Windows.
Download the archive for your platform from the
[Releases page](https://github.com/mesabloo/fugue/releases), unpack it, and put `fugue`
on your `PATH`.

```bash
fugue --version
```

### From source

You need [`elan`](https://github.com/leanprover/elan), which picks up the pinned Lean
toolchain automatically, plus Go 1.25 for the runtime library and the test suite.

```bash
git clone https://github.com/mesabloo/fugue
cd fugue
lake exe cache get                        # prebuilt Mathlib
lake build fugue -KBUILD_TYPE=release
```

The binary lands at `.lake/build/bin/fugue`.

## Usage

```bash
fugue compile path/to/Module.tla           # compile to Go, on stdout
fugue compile -o out.go Module.tla          # ... to a file
fugue compile -I ./lib Module.tla           # add a search path for EXTENDS
```

`fugue compile -` reads the module from standard input. A compile produces exactly one
Go file, because everything it generates lands in a single package.

Two other subcommands:

- `fugue explain E0021` says what a diagnostic code means; `fugue explain --list`
  prints all of them.
- `fugue help -d` (also `-f`, `-W`, `-X`) lists the names the matching `compile` flag
  accepts.

Worked example inputs live under `Tests/examples/`: `LamportMutex.tla`,
`TwoPhaseCommit.tla`, `Paxos.tla`, and more.

### The generated code

The emitted file is a normal Go package that depends on Fugue's runtime library
(`github.com/mesabloo/fugue/runtime/...`); `go mod tidy` fetches it like any other
module. Fugue does not emit a `main`: `CONSTANT` values, each process's identity, and
how many processes to run are yours to supply when you build the executable.

## The input language

Fugue reads a TLA⁺ module with an embedded Distributed PlusCal algorithm. The types of constants
and variables, and each process's mailbox, are given through annotations in TLA⁺
comments:

```tla
CONSTANTS
    (* @type: Address; *)      Ping,
    (* @type: Set(Address); *) Pongs

(*--algorithm PingPong {
    fifos (* @type: Channel({from: Address, mes: Str}); *) ping,
          (* @type: Address -> Channel(Str); *)            pong[Pongs];
    ...
*)
```

## License

Not yet licensed. Until a license file is added, treat this as "all rights reserved".
