/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineData.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_MachineData does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

/-!
# The evaluation machine on data

Configurations of the evaluation machine (`Cost/Machine.lean`) encoded as `Data`
(`Machine.Cfg.toData`), and the step function transported to `Data` (`Machine.stepData`),
defined by the first-order operations `left`, `right`, `cons`, `unaryToNat`, `getList`
only — so that it is primitive recursive (`Cost/Partrec.lean`) and implementable by a
program of the ambient model (the self-interpreter). The correspondence is
`stepData_toData : stepData c.toData = (step c).toData`.

Encoding: a control is `cons nil (toData p)` ("evaluate `p`") or `cons (cons nil nil) v`
("return `v`"); a configuration is `cons ctrl (cons env kont)` with the environment and the
stack as `cons`-chains; a frame is `cons (ofNat tag) payload` with tags `0`–`3` for
`cons1 t env` (payload `cons t env`), `cons2 a` (payload `a`), `let1 b env`, `loop1 b env`.
-/

namespace MIPRE.Cost

namespace Machine

/-! ## Encoding -/

theorem initData_eq (p : Prog) (x : Data) : initData p.toData x = Cfg.toData ⟨.ev p, [x], []⟩ :=
  rfl

theorem isFinalD_toData (c : Cfg) : IsFinalD c.toData ↔ ∃ r e, c = ⟨.ret r, e, []⟩ := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    simp [IsFinalD, Cfg.toData, Ctrl.toData, evD]
  | ret v =>
    cases kont with
    | nil => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]
    | cons f k => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]

theorem resultD_toData (r : Data) (e : Env) : resultD (Cfg.toData ⟨.ret r, e, []⟩) = r := rfl

/-! ## The step function on data -/

end Machine

end MIPRE.Cost
