module

public import Lean

/-! # The blueprint's declaration checker

`lake exe checkdecls blueprint/lean_decls` checks that every name a `\lean{}` tag of the
blueprint cites is a declaration of the library. `leanblueprint web` writes the list, one
name per line, and the documentation deploy on `main` (`.github/workflows/blueprint.yml`,
through `leanprover-community/docgen-action`) runs the check between building the blueprint
and building the API documentation; the required `Build project` check runs it on every pull
request, on the same list.

This is the project's own executable, not the `PatrickMassot/checkdecls` dependency, for
two reasons recorded in `lakefile.toml`: that program imports every library root of the
package into one environment, and the Palomar `Challenge` and `Solution` roots declare the
same names, so the import fails; and the `MIPStarRE` dependency ships a `checkdecls`
executable of its own, which `lake exe` otherwise finds first and which checks the names
against that project's library. The root package's executable is the one `lake exe`
resolves. It imports `MIPRE` alone: the blueprint cites no Palomar declaration, and
`scripts/lean-coverage.py` resolves the tags against `MIPRE/` for the same reason.
-/

@[expose] public section

open Lean

/-- The non-blank lines of a `lean_decls` file, numbered from one. -/
def declLines (contents : String) : Array (Nat × String) := Id.run do
  let mut out := #[]
  let mut lineNo := 1
  for line in contents.splitOn "\n" do
    let name := line.trimAscii.toString
    if !name.isEmpty then
      out := out.push (lineNo, name)
    lineNo := lineNo + 1
  return out

/-- The cited names that `env` does not contain, with their line numbers. -/
def missingDecls (env : Environment) (decls : Array (Nat × String)) : Array (Nat × String) :=
  decls.filter fun (_, decl) => !env.contains decl.toName

unsafe def main (args : List String) : IO UInt32 := do
  let [pathStr] := args
    | IO.eprintln "usage: lake exe checkdecls blueprint/lean_decls"
      return 1
  let path : System.FilePath := pathStr
  unless ← path.pathExists do
    IO.eprintln s!"checkdecls: {path} does not exist; `leanblueprint web` writes it"
    return 1
  let decls := declLines (← IO.FS.readFile path)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `MIPRE }] {} (trustLevel := 1024)
  let missing := missingDecls env decls
  if missing.isEmpty then
    IO.println s!"checkdecls: all {decls.size} declarations cited in {path} exist in MIPRE"
    return 0
  IO.eprintln
    s!"checkdecls: {missing.size} of the {decls.size} declarations cited in {path} are not in MIPRE:"
  for (lineNo, decl) in missing do
    IO.eprintln s!"  line {lineNo}: {decl}"
  return 1

end
