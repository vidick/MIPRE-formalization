/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FiniteEncoding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B

/-! # Encodings for bounded and optional control labels -/

namespace MIPRE.Cost

/-- Finite numeric labels retain the ambient binary natural encoding. -/
instance {n : ℕ} : SizedEncoding (Fin n) where
  encode i := encode i.val
  decode d := (decode d : Option ℕ).bind fun i => if h : i < n then some ⟨i,h⟩ else none
  decode_encode i := by simp [SizedEncoding.decode_encode, i.isLt]

/-- An empty tree represents absence; a tagged pair represents presence. -/
instance {α : Type*} [SizedEncoding α] : SizedEncoding (Option α) where
  encode
    | none => .nil
    | some a => .cons .nil (encode a)
  decode
    | .nil => some none
    | .cons .nil d => (decode d : Option α).map some
    | _ => none
  decode_encode a := by cases a <;> simp [SizedEncoding.decode_encode]

end MIPRE.Cost
