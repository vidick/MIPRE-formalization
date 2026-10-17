/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SyncMergeByQuestion.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion
import Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero

/-! # Perfect PCC strategies under question-dependent answer encoding

Answers can be encoded separately at each question. The encoding need only
preserve acceptance for nonzero effects on question pairs of positive weight.
This allows format and range facts supplied by an honest strategy's support.
-/

noncomputable section
namespace MIPRE.SyncStrategy
open Matrix Finset Classical
variable {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {G : SynchronousGame X A}

/-- Group outcomes using the encoder appropriate to each question. -/
def mergeAnswersByQuestion (S : SyncStrategy G) (H : SynchronousGame X B)
    (f : X → A → B) : SyncStrategy H :=
  ⟨S.d,S.d_pos,S.P.mergeByQuestion f⟩

end MIPRE.SyncStrategy
