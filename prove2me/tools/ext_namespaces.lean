import Lean
/-! Print every namespace of the environment the given modules make, one per line.  gen.py drops an
`open` of a namespace the generated file's environment lacks; for a namespace the project shares
with Mathlib (`Matrix`, whose scoped notation `ᴴ` a statement stub needs at parse time) it must know
that Mathlib has it, so it reads this list, made from the external modules the generated files import:
  lake env lean --run prove2me/tools/ext_namespaces.lean <file listing the modules> > ext_namespaces.txt -/
open Lean

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods := (← IO.FS.lines (args.headD "modules.txt")).filter (· ≠ "")
  let imports := mods.map fun a => ({ module := a.toName } : Import)
  let env ← importModules imports {} 0 (loadExts := true)
  let mut n := 0
  for ns in env.getNamespaces do
    IO.println ns
    n := n + 1
  IO.eprintln s!"{n} namespaces from {mods.size} modules"
