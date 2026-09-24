/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Lean

/-!
# The dependency graph of this repository's declarations, for `scripts/blueprint-edges.py`

    lake env lean --run scripts/blueprint-deps.lean OUT.jsonl KEEP.txt

reads the compiled `.olean` of every `MIPRE` module directly — no environment is built, so it
needs the modules to be compiled but costs seconds — and writes one JSON line per constant:

* `{"n": name, "k": kind, "m": module, "t": [...], "v": [...]}`, where `t` lists the constants
  its type uses (for an inductive type, also its constructors' types) and `v` those its value
  uses (a definition's body, a theorem's proof);
* `{"n": name, "a": target}` for a constructor or recursor, pointing at its inductive type.

A used constant is kept if it is itself a `MIPRE` constant, or if it is listed in `KEEP.txt`
(one name per line: the blueprint's `\lean{}` names, some of which are Mathlib's).
-/

open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm"
  | .defnInfo _ => "def"
  | .inductInfo _ => "ind"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def main (args : List String) : IO Unit := do
  let [out, keepFile] := args
    | throw <| IO.userError "usage: lake env lean --run scripts/blueprint-deps.lean OUT KEEP"
  initSearchPath (← findSysroot)
  let keep : NameSet := (← IO.FS.lines keepFile).foldl
    (fun s l => if l.trimAscii.isEmpty then s else s.insert l.trimAscii.toString.toName) {}
  -- every `MIPRE` module, through the imports of `MIPRE.lean`
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[`MIPRE]
  let mut consts : Array (Name × ConstantInfo) := #[]
  while !stack.isEmpty do
    let m := stack.back!
    stack := stack.pop
    if seen.contains m then continue
    seen := seen.insert m
    let (data, _) ← readModuleData (← findOLean m)
    for c in data.constants do
      consts := consts.push (m, c)
    for i in data.imports do
      if i.module.getRoot == `MIPRE then stack := stack.push i.module
  let mut ours : Std.HashMap Name ConstantInfo := {}
  for (_, c) in consts do
    ours := ours.insert c.name c
  let kept (e : Expr) : Array Name :=
    e.getUsedConstants.filter fun n => ours.contains n || keep.contains n
  let h ← IO.FS.Handle.mk out .write
  for (m, c) in consts do
    match c with
    | .ctorInfo v =>
      h.putStrLn (Json.compress (Json.mkObj [("n", toJson c.name), ("a", toJson v.induct)]))
    | .recInfo v =>
      h.putStrLn (Json.compress (Json.mkObj [("n", toJson c.name), ("a", toJson v.getMajorInduct)]))
    | _ =>
      let mut ty := kept c.type
      if let .inductInfo v := c then
        for ctor in v.ctors do
          if let some ci := ours[ctor]? then ty := ty ++ kept ci.type
      let val := match c.value? (allowOpaque := true) with
        | some v => kept v
        | none => #[]
      h.putStrLn (Json.compress (Json.mkObj [("n", toJson c.name), ("k", kindOf c),
        ("m", toJson m), ("t", toJson ty), ("v", toJson val)]))
  IO.eprintln s!"blueprint-deps: {seen.size} modules, {consts.size} constants"
