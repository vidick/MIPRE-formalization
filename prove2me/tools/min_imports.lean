import Lean
/-! For each module named on the command line, print the Mathlib modules declaring the constants its
own declarations use (types AND proof/definition bodies), one `MODULE <m> <mathlib module>` line each.
The bodies are read from the module's `.olean.private` part (the exported part turns theorems into
axioms) with `value? (allowOpaque := true)` -- without it a theorem's value reads as `none`, which is
why the earlier P2MMinImports.lean saw only statement-level dependencies.  Run in the main repository, whose oleans are the module-system build of the current branch (the vendored
sources differ from `70cbf1c` only in their headers):
  lake env lean --run prove2me/tools/min_imports.lean <module> ... > min_imports.out
and turn the `MODULE` lines into `<P2M_DIR>/minimports.json` with tools/ws_rewrite_imports.py --from-lean.
Module names are the repository Mathlib's; ws_rewrite_imports.py maps the ones the platform pin renamed. -/
open Lean

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let imports := args.toArray.map fun a => ({ module := a.toName } : Import)
  let env ← importModules imports {} 0 (level := .private)
  for a in args do
    let mod := a.toName
    let olean ← findOLean mod
    let parts := #[olean, ⟨olean.toString ++ ".server"⟩, ⟨olean.toString ++ ".private"⟩]
    let avail ← parts.filterM fun p => p.pathExists
    let datas ← readModuleDataParts avail
    let some (data, _) := datas.back? | IO.println s!"NOMODULE {a}"
    IO.println s!"PARTS {a} {avail.size} consts {data.constants.size}"
    let mut used : NameSet := {}
    let mut withValue := 0
    for ci in data.constants do
      for n in ci.type.getUsedConstants do used := used.insert n
      match ci.value? (allowOpaque := true) with   -- theorem proofs are `none` without allowOpaque
      | some v => withValue := withValue + 1; for n in v.getUsedConstants do used := used.insert n
      | none => pure ()
    IO.println s!"VALUES {a} {withValue}"
    let mut mods : NameSet := {}
    let mut unknown := 0
    for n in used do
      match env.getModuleIdxFor? n with
      | some i =>
        let m := (env.header.modules[i.toNat]!).module
        if (`Mathlib).isPrefixOf m then
          mods := mods.insert m
          IO.println s!"CONST {a} {n} {m}"
      | none => unknown := unknown + 1
    for m in mods.toList.mergeSort (fun x y => x.toString < y.toString) do
      IO.println s!"MODULE {a} {m}"
    IO.println s!"DONE {a} {mods.size} unknown {unknown}"
