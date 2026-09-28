/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Paper.Decider

/-!
# The halting verifier along the paper's route: sizes

The sizes of the descriptions the accounting of `Paper/Cost.lean` runs on, each an exact
affine function of `|M| + |λ|` — the binary encodings' sizes `esize M + esize lam` — with a
constant depending on `G`, `U`, `UT` and `S'` alone:

* the code of the map `F` (`esize_F_code`), which carries `body`, `M` and `λ` as constants;
* the two-argument program `kleeneProg` of the fixed point (`esize_kleeneProg_F`);
* the decider `dec M λ` itself, a hardcoding of `kleeneProg` to its own description
  (`esize_dec`), so **twice** the previous plus a constant — this is the `2|c|` of the
  criterion route and the reason the parameter `λ(M)` of `lem:lambda` is `Λ₀ + 4|M|`;
* `F` applied to the decider (`esize_F_dec`), the program the fixed point actually runs;
* the time bound of `F` (`F_timeBound_eval`) and the overhead of the fixed point's
  transfer (`kleeneOverhead_eq`).

The constants are what Lean computes from the constructors; they are named rather than
tracked, since only their existence matters downstream.
-/

namespace MIPRE.Halting

open Cost Cost.Prog Polynomial

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-- `esize n ≤ 4n + 1`: the binary numeral of `n` has at most `size n ≤ n` digits. -/
theorem esize_nat_le_self (n : ℕ) : esize n ≤ 4 * n + 1 :=
  (esize_nat_le n).trans (by have := Nat.size_le.2 (Nat.lt_two_pow_self (n := n)); omega)

/-- The size of the code of `F` beyond `|M| + |λ|`. -/
noncomputable def cF (S' : Prog) : ℕ := esize (body G U UT S') + esize smnProg + 77

theorem esize_F_code (S' M : Prog) (lam : ℕ) :
    esize (F G U UT S' M lam).code = esize M + esize lam + cF G U UT S' := by
  simp only [F, PolyTimeFun.comp, PolyTimeFun.pair, PolyTimeFun.const, PolyTimeFun.id,
    PolyTimeFun.smn, esize_eq_size_toData, toData, Data.size_cons, Data.size_ofNat]
  have h1 : M.toData.size = esize M := rfl
  have h1' : (encode M : Data).size = esize M := rfl
  have h2 : (encode lam : Data).size = esize lam := rfl
  have h3 : (body G U UT S').toData.size = esize (body G U UT S') := rfl
  have h3' : (encode (body G U UT S') : Data).size = esize (body G U UT S') := rfl
  have h4 : smnProg.toData.size = esize smnProg := rfl
  unfold cF
  omega

/-- The size of `kleeneProg U.univ F` beyond `|M| + |λ|`. -/
noncomputable def cK (S' : Prog) : ℕ := cF G U UT S' + esize U.univ + esize smnProg + 136

theorem esize_kleeneProg_F (S' M : Prog) (lam : ℕ) :
    esize (kleeneProg U.univ (F G U UT S' M lam)) = esize M + esize lam + cK G U UT S' := by
  have h0 := esize_F_code G U UT S' M lam
  simp only [kleeneProg, callVar, esize_eq_size_toData, toData, Data.size_cons,
    Data.size_ofNat, Data.size_nil] at h0 ⊢
  have h1 : U.univ.toData.size = esize U.univ := rfl
  have h2 : smnProg.toData.size = esize smnProg := rfl
  have h3 : M.toData.size = esize M := rfl
  unfold cK
  omega

/-- The size of the decider `dec M λ` beyond `2 (|M| + |λ|)`. -/
noncomputable def cD (S' : Prog) : ℕ := 2 * cK G U UT S' + 35

theorem esize_dec (S' M : Prog) (lam : ℕ) :
    esize (dec G U UT S' M lam) = 2 * (esize M + esize lam) + cD G U UT S' := by
  rw [dec, kleeneFix, hardcode_size]
  have h1 : (encode (kleeneProg U.univ (F G U UT S' M lam)) : Data).size =
    esize (kleeneProg U.univ (F G U UT S' M lam)) := rfl
  rw [h1, esize_kleeneProg_F, cD]
  omega

/-- The description `(M, (λ, e))` has size `|M| + |λ| + |e| + 2`. -/
theorem size_descData (M : Prog) (lam : ℕ) (e : Prog) :
    (encode (M, (lam, e)) : Data).size = esize M + esize lam + esize e + 2 := by
  show esize M + (esize lam + esize e + 1) + 1 = _
  omega

/-- `F e = hardcode body (M, (λ, e))` has size `|body| + |M| + |λ| + |e| + 37`. -/
theorem esize_F_apply (S' M : Prog) (lam : ℕ) (e : Prog) :
    esize (F G U UT S' M lam e) = esize (body G U UT S') + esize M + esize lam + esize e + 37 := by
  rw [F_apply, hardcode_size, size_descData]
  omega

/-- The time bound of `F`: affine in the argument and in `|body| + |M| + |λ|`. -/
theorem F_timeBound_eval (S' M : Prog) (lam x : ℕ) :
    (F G U UT S' M lam).timeBound.eval x =
      2 * (esize (body G U UT S') + esize M + esize lam + x) + 47 := by
  simp only [F, PolyTimeFun.comp, PolyTimeFun.pair, PolyTimeFun.const, PolyTimeFun.id,
    PolyTimeFun.smn, eval_add, eval_comp, eval_X, eval_C, eval_one]
  omega

/-- The overhead of the fixed point's time transfer beyond `21 (|M| + |λ|)`. -/
noncomputable def cO (S' : Prog) : ℕ :=
  7 * cK G U UT S' + 5 * cD G U UT S' + 4 * esize (body G U UT S') + 181

theorem kleeneOverhead_eq (S' M : Prog) (lam : ℕ) :
    kleeneOverhead U (F G U UT S' M lam) = 21 * (esize M + esize lam) + cO G U UT S' := by
  have h1 := esize_kleeneProg_F G U UT S' M lam
  have h2 := esize_dec G U UT S' M lam
  have h3 := esize_F_apply G U UT S' M lam (dec G U UT S' M lam)
  have h4 := F_timeBound_eval G U UT S' M lam (esize (dec G U UT S' M lam))
  rw [kleeneOverhead]
  change 7 * esize (kleeneProg U.univ (F G U UT S' M lam)) + esize (dec G U UT S' M lam) +
    (F G U UT S' M lam).timeBound.eval (esize (dec G U UT S' M lam)) +
    2 * esize (F G U UT S' M lam (dec G U UT S' M lam)) + 60 = _
  rw [h1, h4, h3, h2, cO]
  omega

end MIPRE.Halting
