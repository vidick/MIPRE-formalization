/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/MapLoop.lean (statement stub of MIPRE.Cost.Prog.mapLoop_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.mapLoop_runs {univ : Prog} (hU : univ.WellScoped 1) {s : ℕ} (hs : 0 < s)
    (sD nD kD wD jD : Data) (f : List Data → List Data → Data) (Tu Z : ℕ) :
    ∀ (remU remY acc : List Data) (env : Env),
      (∀ p ∈ chunkPairs s hs remU remY,
        ∃ t ≤ Tu, Eval [mapQuery sD nD kD wD jD (list p.1) (list p.2)] univ (f p.1 p.2) t) →
      s + (list remU).size + (list remY).size + (mapCtx sD nD kD wD jD).size + (list acc).size +
        remU.length * (Tu + 1) + Tu ≤ Z →
      ∃ t ≤ (remU.length + 1) * mapIter Z,
        Eval (mapState s remU remY (mapCtx sD nD kD wD jD) acc :: env) (.loop (mapBody univ))
          (list (mapAcc f (chunkPairs s hs remU remY) acc)) t := by sorry
