module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic

/-!
# Fugue style linters — shared infrastructure

`linter.fugue.*` is the project's family of style linters: one per mechanically-checkable rule in
`LEAN_STYLE.md` and `INSTRUCTIONS.md`. Each is a `Lean.Linter` that runs at command elaboration
and reports through `Linter.logLint`, so every diagnostic is a warning and style never fails a
build.

This module carries what the linters share:

* `Finding` — a syntax node to underline and the message to show;
* `mkFugueLinter` / `mkFugueLinterM` — the wrapper turning a finding-producer into a `Linter.run`
  body, gated on the master toggle, the per-linter option, and the vendored-code skiplist;
* `linter.fugue` — the master toggle every wrapper checks;
* `skiplist` — module-path prefixes exempt from every `linter.fugue.*` linter;
* `scan` — a pre-order syntax walk that does not descend into syntax quotations.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/--
The master switch for the project's style linters. While this is off every `linter.fugue.*`
linter stays silent regardless of its own option, so `set_option linter.fugue false in …` turns
the whole family off for one command.
-/
public register_option linter.fugue : Bool := {
  defValue := true
  descr := "enable the project's `linter.fugue.*` style linters (master switch)"
}

/-- One linter finding: the syntax node to underline and the message to show. -/
public structure Finding where
  /-- The syntax node the warning is anchored at. -/
  ref : Syntax
  /-- The warning text. -/
  msg : MessageData

/--
Module-path prefixes exempt from every `linter.fugue.*` linter: vendored upstream code (keeps
upstream style) and the linter sources themselves (which necessarily name the constructs they
detect — `linter.fugue.comments` would flag its own rule list). `Tests.Linter.*` is *not* here —
those fixtures must be linted for `#guard_msgs` to capture the warning.
-/
public def skiplist : Array Name := #[`Extra.Mathlib, `CustomPrelude.Linter]

/-- Whether `mod` sits under a `skiplist` prefix. -/
public def isSkipped (mod : Name) : Bool := skiplist.any (·.isPrefixOf mod)

/--
Syntax-node kinds whose interior is a *pattern being constructed*, not proof text: a syntax
quotation. A syntax linter stops descending here — the rule it enforces holds in metaprogramming
code, not inside the quotations that code writes.
-/
public def isQuotationKind (k : SyntaxNodeKind) : Bool :=
  k matches .str _ "quot"
    || k == ``Lean.Parser.Term.dynamicQuot
    || k == ``Lean.Parser.Tactic.quotSeq

/--
Pre-order walk of `stx`, collecting `f`'s findings at every node, without descending into syntax
quotations (`isQuotationKind`) or any node whose kind `skip` accepts.
-/
public partial def scanExcept (skip : SyntaxNodeKind → Bool) (f : Syntax → Array Finding)
    (stx : Syntax) : Array Finding :=
  let here := f stx
  match stx with
  | .node _ k args =>
    if isQuotationKind k || skip k then here
    else args.foldl (init := here) λ acc a ↦ acc ++ scanExcept skip f a
  | _ => here

/-- `scanExcept` with no extra skip: the plain quotation-aware pre-order walk. -/
public def scan (f : Syntax → Array Finding) (stx : Syntax) : Array Finding :=
  scanExcept (λ _ ↦ false) f stx

/-- A one-node finding helper: `#[⟨ref, msg⟩]`. -/
public def hit (ref : Syntax) (msg : MessageData) : Array Finding := #[⟨ref, msg⟩]

/-- Every node under `stx` (pre-order) satisfying `p`, without descending into syntax
quotations (`isQuotationKind`). -/
public partial def collect (p : Syntax → Bool) (stx : Syntax) : Array Syntax :=
  let rest := match stx with
    | .node _ k args =>
      if isQuotationKind k then #[]
      else args.foldl (init := #[]) λ acc a ↦ acc ++ collect p a
    | _ => #[]
  if p stx then #[stx] ++ rest else rest

/-- The last component of an identifier's name, macro scopes erased; `none` for a non-identifier. -/
public def identLast? : Syntax → Option String
  | .ident _ _ n _ => match n.eraseMacroScopes with
    | .str _ s => some s
    | _ => none
  | _ => none

/-- Whether some component of `n` (macro scopes erased) equals `s`. -/
public def nameHasComponent (n : Name) (s : String) : Bool :=
  n.eraseMacroScopes.components.any λ c ↦ match c with
    | .str _ x => x == s
    | _ => false

/-- Whether the whitespace *after* `stx` (its trailing trivia, else the head token's) spans a line
break — i.e. whatever follows `stx` in the source starts on a later line. -/
public def crossesLine (stx : Syntax) : Bool :=
  match stx.getTrailing? with
  | some ss => ss.toString.any (· == '\n')
  | none => false

/-- Every identifier last-component appearing anywhere under `stx` (quotations excepted). -/
public def identsUnder (stx : Syntax) : Array String :=
  (collect (·.isIdent) stx).filterMap identLast?

/-- The `at <hyp>` names a tactic with a trailing `Tactic.location` carries; `#[]` for none. -/
public def locationHyps (stx : Syntax) : Array String :=
  match stx.find? (·.isOfKind ``Lean.Parser.Tactic.location) with
  | some loc => (collect (·.isIdent) loc).filterMap identLast?
  | none => #[]

/-- The direct arguments of an application `s` (`Term.app`), each unwrapped through one layer of
`(…)`. `#[]` when `s` is not an application. -/
public def appArgs (s : Syntax) : Array Syntax :=
  if s.isOfKind ``Lean.Parser.Term.app then
    s[1].getArgs.map λ a ↦ if a.isOfKind ``Lean.Parser.Term.paren then a[1] else a
  else #[]

/-- Whether `s` is a `set_option <opt> <val>` — command form or tactic form — for the given
option-name last component and value atom. -/
public def isSetOption (opt val : String) (s : Syntax) : Bool :=
  (s.isOfKind ``Lean.Parser.Command.set_option || s.isOfKind ``Lean.Parser.Tactic.set_option)
    && identLast? s[1] == some opt
    && s[3].getAtomVal == val

/-- The tactics of a `tacticSeq` / `tacticSeq1Indented` / bracketed sequence, in source order.
`#[]` for any other node. -/
public partial def seqTactics (stx : Syntax) : Array Syntax :=
  match stx.getKind with
  | ``Lean.Parser.Tactic.tacticSeq => seqTactics stx[0]
  | ``Lean.Parser.Tactic.tacticSeq1Indented => stx[0].getArgs.getSepElems
  | ``Lean.Parser.Tactic.tacticSeqBracketed => seqTactics stx[1]
  | _ => #[]

/-- The tactic body a goal selector applies, if `s` is one: the project's `tac_selector`
(`all:` / `n,m:` / `n-m:`), `all_goals`, or `any_goals`. `none` for anything else. -/
public def selectorBody? (s : Syntax) : Option Syntax :=
  if s.isOfKind ``Lean.Parser.Tactic.allGoals || s.isOfKind ``Lean.Parser.Tactic.anyGoals then
    some s[1]
  else if s.getKind == `CustomPrelude.Tactic.«tactic_:_» then some s[2]
  else none

/-- `first` / `solve` alternative-count, `none` if `s` is neither. -/
public def firstOrSolveAlts? (s : Syntax) : Option Nat :=
  if s.isOfKind ``Lean.Parser.Tactic.first then some s[1].getNumArgs
  else if s.getKind == `Lean.solveTactic then some s[1].getNumArgs
  else none

/-- Strip one layer of `( … )` / `{ … }` tactic grouping, and a single-tactic sequence, from `s`. -/
public partial def unwrapTac (s : Syntax) : Syntax :=
  match s.getKind with
  | ``Lean.Parser.Tactic.tacticSeq | ``Lean.Parser.Tactic.tacticSeq1Indented =>
    match seqTactics s with
    | #[t] => unwrapTac t
    | _ => s
  | ``Lean.Parser.Tactic.paren | ``Lean.Parser.Tactic.tacticSeqBracketed => unwrapTac s[1]
  | _ => s

/-- Structural equality ignoring source positions (compares the reprinted text). -/
public def sameShape (a b : Syntax) : Bool :=
  match a.reprint, b.reprint with
  | some x, some y => x.trimAscii == y.trimAscii
  | _, _ => false

/-- Whether every pair in `xs` is `sameShape`-distinct. -/
public def allDistinctShape (xs : Array Syntax) : Bool := Id.run do
  for h : i in [0:xs.size] do
    for h : j in [i+1:xs.size] do
      if sameShape xs[i] xs[j] then return false
  return true

/--
Turn a monadic finding-producer into a `Linter.run` body.

The wrapper:

* honours `set_option … in` at command scope, through `withSetOptionIn`;
* stays silent unless both the master `linter.fugue` and `opt` are enabled;
* stays silent on modules under `skiplist`;
* stays silent while the command still has elaboration errors — style stays out of the way of a
  proof the compiler is still rejecting;
* emits one `Linter.logLint opt` per finding, anchored at `Finding.ref`.
-/
public def mkFugueLinterM (opt : Lean.Option Bool)
    (core : Syntax → CommandElabM (Array Finding)) : Syntax → CommandElabM Unit :=
  withSetOptionIn λ stx ↦ do
    let opts ← getLinterOptions
    unless getLinterValue linter.fugue opts && getLinterValue opt opts do return
    if (← MonadState.get).messages.hasErrors then return
    if isSkipped (← getMainModule) then return
    for fnd in (← core stx) do
      Linter.logLint opt fnd.ref fnd.msg

/-- `mkFugueLinterM` for a pure `Syntax`-only core — the syntax-linter kind. -/
public def mkFugueLinter (opt : Lean.Option Bool) (core : Syntax → Array Finding) :
    Syntax → CommandElabM Unit :=
  mkFugueLinterM opt λ stx ↦ pure (core stx)

end CustomPrelude.Linter
