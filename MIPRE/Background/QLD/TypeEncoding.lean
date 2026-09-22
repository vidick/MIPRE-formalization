/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliStagePrograms
import MIPRE.Foundations.CL.DetypingProgParse

/-! # Faithful type labels and the finite Pauli branch decoder

Only the fixed set of twenty-six question types is tabulated. Field elements,
dimensions, seeds and answers are handled by uniform programs.
-/

noncomputable section
namespace MIPRE.QLD
open Cost Cost.PolyTimeFun CL.Detyping.Program

instance : SizedEncoding Ty where
  encode t := encode (Fintype.equivFin Ty t).val
  decode d := (decode d : Option ℕ).bind fun i =>
    if h : i < Fintype.card Ty then some ((Fintype.equivFin Ty).symm ⟨i, h⟩) else none
  decode_encode t := by simp [SizedEncoding.decode_encode]

namespace PauliCL

private def typeTable : PolyTimeFun Data Data :=
  finiteTable (fun d => ((decode d : Option Ty).map
    (fun t => encode (programTag t))).getD .nil)
    ((Finset.univ.image (encode : Ty → Data)).toList)

private theorem typeTable_encode (t : Ty) : typeTable (encode t) = encode (programTag t) := by
  rw [typeTable, finiteTable_apply_of_mem _ _ _ (by simp)]
  simp [SizedEncoding.decode_encode]

def typeTag : PolyTimeFun Data Introspection.PauliStageProgram.Tag :=
  ((readNat.comp treeHead).pair (rawTruthProg.comp treeTail)).comp typeTable

theorem typeTag_encode (t : Ty) : typeTag (encode t) = programTag t := by
  simp only [typeTag, comp_apply, pair_apply, typeTable_encode]
  rcases programTag t with ⟨a, b⟩
  simp only [encode_prod, treeHead_cons, treeTail_cons, readNat_encode,
    rawTruthProg_encode_bool]

end PauliCL
end MIPRE.QLD
end
