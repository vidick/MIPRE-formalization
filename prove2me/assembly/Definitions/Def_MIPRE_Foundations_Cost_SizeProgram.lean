/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/SizeProgram.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader

/-! # Encoded size as an ambient polynomial-time program -/

namespace MIPRE.Cost.PolyTimeFun

open Polynomial

/-- Count the actual encoded tree size in unary. The output size is linear in
the supplied encoding, including for arbitrary malformed object-level programs. -/
noncomputable def encodedSizeU (α : Type*) [SizedEncoding α] : PolyTimeFun α Unary where
  toFun a := unary (esize a)
  code := Prog.sizeProg
  closed := Prog.sizeProg_wellScoped
  timeBound := (X + 1) * (5 * X + 20) + X + 6
  computes a := by
    obtain ⟨t, ht, hr⟩ := Prog.sizeProg_runs (encode a)
    refine ⟨t, ?_, ?_⟩
    · simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_ofNat, esize] using ht
    · simpa only [encode_unary, esize] using hr

@[simp] theorem encodedSizeU_apply {α : Type*} [SizedEncoding α] (a : α) :
    encodedSizeU α a = unary (esize a) := rfl

end MIPRE.Cost.PolyTimeFun
