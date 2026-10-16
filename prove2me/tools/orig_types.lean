import Lean
/-! Print the elaborated type of every theorem declared in the given modules' closure, in the form
validate.py's original-tree phase reads (`<name> :: <type>`, one per line, continuation lines
indented), with the same pretty-printer (`ppExpr` at the root namespace, no `open`, width 100000).
Run in the workspace with the modules imported:
  lake env lean --run prove2me/tools/orig_types.lean <root module> ... > orig_types.txt
Only constants of modules whose name starts with `MIPRE` are printed, so the output covers the
source closure without Mathlib.  validate.py --orig-from <file> then needs no source olean. -/
open Lean Meta

def ppType (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let f ← ppExpr ci.type
  return f.pretty 100000

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := args.toArray.map fun a => ({ module := a.toName } : Import)
  let env ← importModules imports {} 0 (loadExts := true)
  let mods := env.header.moduleNames
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if n.isInternal then continue
      match env.getModuleIdxFor? n with
      | some idx =>
        if (`MIPRE).isPrefixOf (mods[idx.toNat]!) then names := names.push n
      | none => pure ()
  IO.eprintln s!"{names.size} theorems"
  let ctx : Core.Context := { fileName := "<orig_types>", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env }
  for n in names do
    let r ← ((ppType n).run' {} {}).toIO ctx st |>.toBaseIO
    match r with
    | .ok (s, _) => IO.println s!"{n} :: {s}"
    | .error e => IO.eprintln s!"FAILED {n}: {e}"
