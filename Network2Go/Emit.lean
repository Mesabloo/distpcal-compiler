module

public import Network2Go.PlusCal

public section

/-!
  Assembling compiled declarations into a Go *source file*: the `package` clause, the `import`
  block, and the declarations themselves.

  Kept out of `Core/Go/Pretty.lean`, which prints the AST and nothing else. A file's framing is
  not part of the Go fragment §6.6 gives a semantics to, and the import paths are `Network2Go`'s
  knowledge — `Naming.lean` is where the runtime's package qualifiers are decided, so this is
  where the paths they resolve to belong.

  **Imports are computed, never assumed.** Go rejects an unused import, so emitting all three
  runtime packages unconditionally would break every program that happens not to need one — a
  specification whose processes never exchange a message uses no `comm`, one with no
  process-local variables uses no `locks`. `usedPackages` walks the declarations for qualified
  names instead.
-/

namespace Network2Go

open ComputableGo (Declaration)

/-- Where each runtime package qualifier resolves to. Keyed by the qualifier `Naming.lean` emits,
since that is what appears in the compiled AST. -/
def runtimeImports : List (String × String) :=
  [ (tlaplusPkg, "github.com/mesabloo/fugue/runtime/tlaplus"),
    (commPkg, "github.com/mesabloo/fugue/runtime/comm"),
    (locksPkg, "github.com/mesabloo/fugue/runtime/locks") ]

/-- The package qualifier of `pkg.Name`, if the name has one. Qualified names are single strings
in this AST (`Naming.lean`'s `qualified`), so the split is textual — but only names *this pass*
built ever contain a dot, since `goIdent` cannot produce one from a source identifier. -/
private def qualifierOf (name : String) : Option String :=
  match name.splitOn "." with
  | [pkg, _] => some pkg
  | _ => none

private def addQual (acc : List String) (name : String) : List String :=
  match qualifierOf name with
  | some pkg => if acc.contains pkg then acc else acc ++ [pkg]
  | none => acc

mutual

/-- Qualifiers named by a type, including inside its type arguments and struct fields. -/
private partial def typQuals (acc : List String) : Go.Typ → List String
  | .int | .str | .bool | .var _ => acc
  | .chan τ | .slice τ | .array _ τ => typQuals acc τ
  | .map κ τ => typQuals (typQuals acc κ) τ
  | .struct fields => fields.foldl (λ acc (_, τ) ↦ typQuals acc τ) acc
  | .func ps rs => rs.foldl typQuals (ps.foldl typQuals acc)
  | .named name args => args.foldl typQuals (addQual acc name)

/-- Qualifiers named by an expression: its `var` heads, and every type annotation it carries. -/
private partial def exprQuals (acc : List String) : ComputableGo.Expression → List String
  | .nat _ | .str _ | .true | .false => acc
  | .var name => addQual acc name
  | .unary _ e | .field e _ => exprQuals acc e
  | .binary _ e₁ e₂ | .index e₁ e₂ => exprQuals (exprQuals acc e₁) e₂
  | .call f args => args.foldl exprQuals (exprQuals acc f)
  | .builtin _ args => args.foldl exprQuals acc
  | .structLit τ fields => fields.foldl (λ acc (_, e) ↦ exprQuals acc e) (typQuals acc τ)
  | .sliceLit τ elems | .make τ elems => elems.foldl exprQuals (typQuals acc τ)
  | .mapLit τ entries =>
    entries.foldl (λ acc (k, v) ↦ exprQuals (exprQuals acc k) v) (typQuals acc τ)
  | .funcLit params returns body =>
    body.foldl stmtQuals (returns.foldl typQuals (params.foldl (λ acc (_, τ) ↦ typQuals acc τ) acc))

/-- Qualifiers named by a reference — only its index expressions can name one. -/
private partial def refQuals (acc : List String) : ComputableGo.Ref → List String
  | .wildcard | .var _ => acc
  | .index r e => exprQuals (refQuals acc r) e
  | .field r _ => refQuals acc r

private partial def stmtQuals (acc : List String) : ComputableGo.Statement → List String
  | .skip => acc
  | .expr e | .print e | .panic e | .close e => exprQuals acc e
  | .return es => es.foldl exprQuals acc
  | .var _ τ => typQuals acc τ
  | .assign lhs rhs => rhs.foldl exprQuals (lhs.foldl refQuals acc)
  | .make _ τ cap => cap.elim (typQuals acc τ) (exprQuals (typQuals acc τ))
  | .send c e => exprQuals (exprQuals acc c) e
  | .receive c x ok => ok.elim (refQuals (exprQuals acc c) x) (refQuals (refQuals (exprQuals acc c) x))
  | .go body => body.foldl stmtQuals acc
  | .if cond t f => f.foldl stmtQuals (t.foldl stmtQuals (exprQuals acc cond))
  | .for cond body => body.foldl stmtQuals (exprQuals acc cond)
  | .switch e cases dflt =>
    dflt.foldl stmtQuals
      (cases.foldl (λ acc c ↦ c.body.foldl stmtQuals (exprQuals acc c.head)) (exprQuals acc e))
  | .select cases dflt =>
    (dflt.getD []).foldl stmtQuals
      (cases.foldl (λ acc c ↦ c.body.foldl stmtQuals (stmtQuals acc c.guard)) acc)

end

/-- Every runtime package a declaration list actually names, in `runtimeImports` order. -/
def usedPackages (decls : List Declaration) : List String :=
  let quals := decls.foldl (init := []) λ acc d ↦
    match d with
    | .typ _ τ => typQuals acc τ
    | .var _ τ value => value.elim (typQuals acc τ) (exprQuals (typQuals acc τ))
    | .function F =>
      F.body.foldl stmtQuals
        (F.returnType.foldl typQuals
          ((F.typeParams ++ F.params).foldl (λ acc (_, τ) ↦ typQuals acc τ) acc))
  runtimeImports.filterMap λ (pkg, _) ↦ if quals.contains pkg then some pkg else none

/-- A complete `.go` file: package clause, the imports the declarations need, then the
declarations.

`package` defaults to `main` — the shape a user most often wants to drop a `func main` beside —
and `-Xgo-pkg:<name>` overrides it. The compiler emits no `main` of its own: which processes
run, where, and how they find each other is not something a specification says (§7.3), so the
generated file is a library its caller drives. -/
def emitFile (packageName : String) (decls : List Declaration) : String :=
  let imports := (usedPackages decls).filterMap λ pkg ↦
    (runtimeImports.lookup pkg).map λ path ↦ s!"\t{pkg} \"{path}\""
  let header :=
    if imports.isEmpty then "" else
      "import (\n" ++ String.intercalate "\n" imports ++ "\n)\n\n"
  s!"package {packageName}\n\n" ++ header
    ++ String.intercalate "\n\n" (decls.map λ d ↦ (Go.Declaration.pretty d).pretty 100)
    ++ "\n"

end Network2Go

end
