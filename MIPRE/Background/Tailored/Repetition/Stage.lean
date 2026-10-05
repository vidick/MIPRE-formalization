/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Repetition.Soundness
public import MIPRE.Background.Repetition.Verifier
public import MIPRE.Tailored.Repeat.LpCost
public import MIPRE.Tailored.Stages

@[expose] public section

/-!
# Parallel repetition of tailored verifiers, inhabited

`TailoredRepetition` (blueprint `thm:tailored-rep`, issue #280) with the repeated sampler
`Repeat.repSampler`, the repeated answer-length calculator `RepProg.repLen` and the repeated
linear-constraints processor `RepProg.repLp`:

* the programs are polynomial-time functions of the inputs through the s-m-n map;
* the complexity clause from the three time bounds (`repSampler_timeBound`,
  `RepProg.repLen_timeBound`, `RepProg.repLp_timeBound`) and the length bound
  `RepProg.repLen_lenBound`;
* completeness and soundness from `RepSpec` (`RepProg.repSpec`) through
  `RepSpec.hasPerfectZPC` and `RepSpec.valStar_le`.
-/

namespace MIPRE.Tailored

open Cost Cost.Prog Cost.PolyTimeFun CL Repeat RepProg

/-! ## The constants of the running-time bounds -/

noncomputable def lenTC : ℕ := repLen_timeBound.choose
noncomputable def lenTM : ℕ := repLen_timeBound.choose_spec.choose
noncomputable def lenTE : ℕ := repLen_timeBound.choose_spec.choose_spec.choose

theorem lenTC_spec {ℓ : ℕ} (S : CL.Sampler ℓ) (L : Decider) (lam tau n : ℕ) (R : Budget) (W : ℕ)
    (hW : LenDom S L lam tau n R W) (hS : S.TimeBoundAt n R.S R.k) (hL : L.TimeBoundAt n R.D R.k) :
    (repLen S L lam tau).TimeBoundAt n (lenTC * (W + 1) ^ lenTM) (lenTE * (R.k + 1)) :=
  repLen_timeBound.choose_spec.choose_spec.choose_spec S L lam tau n R W hW hS hL

noncomputable def lpTC : ℕ := repLp_timeBound.choose
noncomputable def lpTM : ℕ := repLp_timeBound.choose_spec.choose
noncomputable def lpTE : ℕ := repLp_timeBound.choose_spec.choose_spec.choose

theorem lpTC_spec {ℓ : ℕ} (S : CL.Sampler ℓ) (L P : Decider) (lam tau n : ℕ) (R : Budget) (W : ℕ)
    (hW : LpDom S L P lam tau n R W) (hS : S.TimeBoundAt n R.S R.k) (hL : L.TimeBoundAt n R.D R.k)
    (hP : P.TimeBoundAt n R.D R.k) :
    (repLp S L P lam tau).TimeBoundAt n (lpTC * (W + 1) ^ lpTM) (lpTE * (R.k + 1)) :=
  repLp_timeBound.choose_spec.choose_spec.choose_spec S L P lam tau n R W hW hS hL hP

/-- The polynomial bounding the running times and the dimension of the output. -/
noncomputable def tailoredRepBound : Polynomial ℕ :=
  Polynomial.C (sampC + lenTC + lpTC + 1) * (Polynomial.X + 1) ^ (max (max sampM lenTM) lpTM + 2)

theorem tailoredRepBound_eval (W : ℕ) :
    tailoredRepBound.eval W =
      (sampC + lenTC + lpTC + 1) * (W + 1) ^ (max (max sampM lenTM) lpTM + 2) := by
  simp [tailoredRepBound]

/-- The degree multiplier of the output's running times. -/
noncomputable def tailoredRepDeg : ℕ := max (max sampE lenTE) lpTE

/-! ## The procedure -/

variable {ℓ : ℕ}

/-- **The repeated tailored verifier.** -/
noncomputable def tailoredRepOutput (V : TailoredVerifier ℓ) (lam tau : ℕ) : TailoredVerifier ℓ :=
  TailoredVerifier.repTV V lam tau (repLen V.sampler V.len lam tau)
    (repLp V.sampler V.len V.lp lam tau)

theorem le_bound_of_le {a b W : ℕ} (ha : a ≤ sampC + lenTC + lpTC + 1)
    (hb : b ≤ max (max sampM lenTM) lpTM + 2) : a * (W + 1) ^ b ≤ tailoredRepBound.eval W := by
  rw [tailoredRepBound_eval]
  exact Nat.mul_le_mul ha (Nat.pow_le_pow_right (by omega) hb)

theorem arg_bounds (lam tau n : ℕ) (R : Budget) (s : ℕ) :
    Repetition.reps lam tau n ≤ TailoredRepetition.arg lam tau n R s ∧
      R.S ≤ TailoredRepetition.arg lam tau n R s ∧ R.d ≤ TailoredRepetition.arg lam tau n R s ∧
      R.D ≤ TailoredRepetition.arg lam tau n R s ∧ R.B ≤ TailoredRepetition.arg lam tau n R s ∧
      s ≤ TailoredRepetition.arg lam tau n R s ∧ lam ≤ TailoredRepetition.arg lam tau n R s ∧
      tau ≤ TailoredRepetition.arg lam tau n R s ∧ n ≤ TailoredRepetition.arg lam tau n R s ∧
      10 ^ R.k ≤ TailoredRepetition.arg lam tau n R s := by
  unfold TailoredRepetition.arg
  generalize 10 ^ R.k = P
  omega

/-- **The complexity clause.** -/
theorem within_tailoredRep (V : TailoredVerifier ℓ) (lam tau n : ℕ) (R : Budget)
    (hV : V.Within n R) :
    (tailoredRepOutput V lam tau).Within n
      ⟨tailoredRepBound.eval (TailoredRepetition.arg lam tau n R V.size),
        tailoredRepBound.eval (TailoredRepetition.arg lam tau n R V.size),
        tailoredRepBound.eval (TailoredRepetition.arg lam tau n R V.size), tailoredRepDeg * (R.k + 1),
        Repetition.reps lam tau n * R.B⟩ := by
  obtain ⟨hS, hdim, hL, hP, hB⟩ := hV
  set W := TailoredRepetition.arg lam tau n R V.size with hWdef
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := arg_bounds lam tau n R V.size
  have hsS : esize V.sampler.prog ≤ V.size := le_max_left _ _
  have hsL : esize V.len.prog ≤ V.size := (le_max_left _ _).trans (le_max_right _ _)
  have hsP : esize V.lp.prog ≤ V.size := (le_max_right _ _).trans (le_max_right _ _)
  have hLD : LenDom V.sampler V.len lam tau n R W :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hSD : SampDom V.sampler lam tau n R W :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact (sampC_spec V.sampler lam tau n R W hSD hS).mono (le_bound_of_le (by omega) (by omega))
      (Nat.mul_le_mul_right _ ((le_max_left _ _).trans (le_max_left _ _)))
  · show Repetition.reps lam tau n * V.sampler.dim n ≤ _
    calc Repetition.reps lam tau n * V.sampler.dim n ≤ W * W := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (W + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 1 * (W + 1) ^ (max (max sampM lenTM) lpTM + 2) := by
          rw [one_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := le_bound_of_le (by omega) le_rfl
  · exact (lenTC_spec V.sampler V.len lam tau n R W hLD hS hL).mono
      (le_bound_of_le (by omega) (by omega))
      (Nat.mul_le_mul_right _ ((le_max_right _ _).trans (le_max_left _ _)))
  · exact (lpTC_spec V.sampler V.len V.lp lam tau n R W ⟨hLD, by omega⟩ hS hL hP).mono
      (le_bound_of_le (by omega) (by omega)) (Nat.mul_le_mul_right _ (le_max_right _ _))
  · exact repLen_lenBound V.sampler V.len lam tau n R.B hB

/-- **The repeated calculator halts where the input's does.** -/
theorem lenTotal_tailoredRep (V : TailoredVerifier ℓ) (lam tau n : ℕ)
    (h : LenTotal V.len n (V.sampler.dim n)) :
    LenTotal (tailoredRepOutput V lam tau).len n ((tailoredRepOutput V lam tau).sampler.dim n) := by
  intro x hx κ
  have hx' : x.length = TailoredVerifier.K lam tau n * V.sampler.dim n := hx
  have hgood : ∀ i, V.LenDefined n (toBits (TailoredVerifier.qc V lam tau n
      (ofBits (TailoredVerifier.K lam tau n * V.sampler.dim n) x) i)) :=
    fun i => h _ (length_toBits _)
  have := repLen_lenIs V lam tau n _ hgood κ
  rw [toBits_ofBits hx'] at this
  exact ⟨_, this⟩

/-- **Parallel repetition of tailored verifiers** (blueprint `thm:tailored-rep`), inhabited. -/
noncomputable def tailoredRepetition (ℓ : ℕ) : TailoredRepetition ℓ where
  c := Repetition.repConst / 2
  c_pos := by have := Repetition.repConst_pos; positivity
  bound := tailoredRepBound
  deg := tailoredRepDeg
  sampler S lam tau := repSampler S lam tau
  samplerProg := (PolyTimeFun.smn (Prog × ℕ × ℕ)).comp
    ((PolyTimeFun.const (repSampCore selfUniversal.univ)).pair (PolyTimeFun.id _))
  samplerProg_eq _ _ _ := rfl
  len S L lam tau := repLen S L lam tau
  lenProg := (PolyTimeFun.smn LenPar).comp
    ((PolyTimeFun.const (lenCore selfUniversal.univ)).pair (PolyTimeFun.id _))
  lenProg_eq _ _ _ _ := rfl
  compute := (PolyTimeFun.smn LpPar).comp
    ((PolyTimeFun.const (lpCore selfUniversal.univ)).pair
      ((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair ((snd.comp (snd.comp fst)).pair snd))))
  output V lam tau := tailoredRepOutput V lam tau
  output_sampler _ _ _ := rfl
  output_len _ _ _ := rfl
  output_lp _ _ _ := rfl
  within V lam tau n R hV := within_tailoredRep V lam tau n R hV
  len_total V lam tau n h := lenTotal_tailoredRep V lam tau n h
  completeness V lam tau n h := (repSpec V lam tau n).hasPerfectZPC h
  soundness V lam tau n B ε hε _ hB hV := (repSpec V lam tau n).valStar_le hε hB hV

end MIPRE.Tailored

end
