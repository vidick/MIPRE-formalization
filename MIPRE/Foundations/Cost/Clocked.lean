/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Toolkit
import MIPRE.Foundations.Cost.Numeric

/-!
# Clocked simulation as a polynomial-time predicate

Given a clocked universal machine `UT`, `PolyTimeFun.haltsWithin UT : PolyTimeFun (Prog × ℕ)
Bool` decides whether `e` halts on the empty input within `Nat.size n` steps: it computes
the budget in unary from the binary `n` (`lenProg`), assembles the machine's input
`(ofNat k, (encode e, nil))`, runs `UT.univT`, and reads the halting flag of
`clockedResult`. This is the "run `e` for `log n` steps" of [MNY, Lemma 5.1].
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- The program of `PolyTimeFun.haltsWithin`. Input: `cons (encode e) (encode n)`. -/
def haltsWithinProg (univT : Prog) : Prog :=
  .let_ (.elim 0 .nil (.var 1))
    (.let_ (callVar 0 lenProg)
      (.let_ (.elim 2 .nil (.var 0))
        (.let_ (.cons (.var 1) (.cons (.var 0) .nil))
          (.let_ (callVar 0 univT)
            (.elim 0 .nil (.const (.cons .nil .nil)))))))

theorem haltsWithinProg_wellScoped {univT : Prog} (hU : univT.WellScoped 1) :
    (haltsWithinProg univT).WellScoped 1 :=
  ⟨⟨by decide, trivial, by simp [WellScoped]⟩,
    ⟨callVar_wellScoped (by decide) lenProg_wellScoped,
      ⟨⟨by decide, trivial, by simp [WellScoped]⟩,
        ⟨⟨by simp [WellScoped], by simp [WellScoped], trivial⟩,
          ⟨callVar_wellScoped (by decide) hU, ⟨by decide, trivial, trivial⟩⟩⟩⟩⟩⟩

/-- The run of `haltsWithinProg`, in terms of the clocked machine's result. -/
theorem haltsWithinProg_runs (UT : ClockedUniversalMachine) (e : Prog) (n : ℕ) :
    ∃ t ≤ UT.bound.eval (Nat.size n + esize e + 1) +
        (Nat.size n + 1 + 1) * (esize n + 1 + 2 * Nat.size n + 13) +
        3 * esize e + 4 * Nat.size n + 2 * esize n + 40,
      (haltsWithinProg UT.univT).Runs (.cons (encode e) (encode n))
        (encode (evalWithin e .nil (Nat.size n)).isSome) t := by
  have hLen : (n.bits.map Data.ofBool).length = Nat.size n := by
    rw [List.length_map, Nat.size_eq_bits_len]
  have hne : encode n = Data.list (n.bits.map Data.ofBool) := encode_bitStr_eq_list n.bits
  have hnesz : (encode n).size = esize n := rfl
  have heesz : (encode e).size = esize e := rfl
  -- step 1: the second component
  have s1 : Eval [Data.cons (encode e) (encode n)] (.elim 0 .nil (.var 1)) (encode n)
      ((encode n).size + 1 + 1) :=
    Eval.elim_cons (i := 0) (a := encode e) (b := encode n) (by simp)
      (Eval.var_of_get (i := 1) (v := encode n) (by simp))
  -- step 2: the budget in unary
  obtain ⟨t₂, ht₂, h₂⟩ := lenProg_runs (n.bits.map Data.ofBool)
  rw [hLen] at ht₂ h₂
  rw [← hne] at ht₂ h₂
  rw [hnesz] at ht₂
  have s2 := callVar_eval (env := [encode n, Data.cons (encode e) (encode n)]) (i := 0)
    lenProg_wellScoped (v := encode n) (by simp) h₂
  -- step 3: the first component
  have s3 : Eval [Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)]
      (.elim 2 .nil (.var 0)) (encode e) ((encode e).size + 1 + 1) :=
    Eval.elim_cons (i := 2) (a := encode e) (b := encode n) (by simp)
      (Eval.var_of_get (i := 0) (v := encode e) (by simp))
  -- step 4: the machine's input
  have s4 : Eval [encode e, Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)]
      (.cons (.var 1) (.cons (.var 0) .nil))
      (.cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil)) _ :=
    Eval.cons (Eval.var_of_get (i := 1) (v := Data.ofNat (Nat.size n)) (by simp))
      (Eval.cons (Eval.var_of_get (i := 0) (v := encode e) (by simp)) (Eval.nil _))
  -- step 5: the simulation
  obtain ⟨t₅, ht₅, h₅⟩ := UT.run e .nil (Nat.size n)
  rw [Data.size_nil] at ht₅
  have s5 := callVar_eval
    (env := [Data.cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil), encode e,
      Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)])
    (i := 0) UT.closed (v := .cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil))
    (by simp) h₅
  -- step 6: the flag
  have s6 : ∃ t₆ ≤ 4, Eval (clockedResult e .nil (Nat.size n) ::
      [Data.cons (Data.ofNat (Nat.size n)) (.cons (encode e) .nil), encode e,
        Data.ofNat (Nat.size n), encode n, Data.cons (encode e) (encode n)])
      (.elim 0 .nil (.const (.cons .nil .nil)))
      (encode (evalWithin e .nil (Nat.size n)).isSome) t₆ := by
    unfold clockedResult
    rcases hres : evalWithin e .nil (Nat.size n) with _ | r
    · exact ⟨2, by omega, Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
    · exact ⟨4, le_rfl, Eval.elim_cons (i := 0) (a := .cons .nil .nil) (b := r) (by simp)
        (Eval.const _ (.cons .nil .nil))⟩
  obtain ⟨t₆, ht₆, h₆⟩ := s6
  refine ⟨_, ?_, Eval.let_ s1 (Eval.let_ s2 (Eval.let_ s3 (Eval.let_ s4 (Eval.let_ s5 h₆))))⟩
  simp only [Data.size_cons, Data.size_nil, Data.size_ofNat]
  omega

end Prog

/-- Decides "`e` halts on the empty input within `Nat.size n` steps", in polynomial time,
given a clocked universal machine. -/
noncomputable def PolyTimeFun.haltsWithin (UT : ClockedUniversalMachine) :
    PolyTimeFun (Prog × ℕ) Bool where
  toFun p := (evalWithin p.1 .nil (Nat.size p.2)).isSome
  code := Prog.haltsWithinProg UT.univT
  closed := Prog.haltsWithinProg_wellScoped UT.closed
  timeBound := UT.bound + (X + C 2) * (C 4 * X + C 14) + C 9 * X + C 40
  computes p := by
    obtain ⟨e, n⟩ := p
    obtain ⟨t, ht, h⟩ := Prog.haltsWithinProg_runs UT e n
    refine ⟨t, ?_, h⟩
    have h1 : Nat.size n ≤ esize n := size_le_esize_nat n
    have h2 : Nat.size n + esize e + 1 ≤ esize e + esize n + 1 := by omega
    have hmono := polynomial_eval_mono UT.bound h2
    have hp : (Nat.size n + 1 + 1) * (esize n + 1 + 2 * Nat.size n + 13) ≤
        (esize e + esize n + 1 + 2) * (4 * (esize e + esize n + 1) + 14) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      esize_prod]
    omega

@[simp] theorem PolyTimeFun.haltsWithin_apply (UT : ClockedUniversalMachine) (e : Prog) (n : ℕ) :
    PolyTimeFun.haltsWithin UT (e, n) = (evalWithin e .nil (Nat.size n)).isSome := rfl

end MIPRE.Cost
