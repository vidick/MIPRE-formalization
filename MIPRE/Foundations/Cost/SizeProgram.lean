/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Cost.Reader
import MIPRE.Foundations.Cost.Unary

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
