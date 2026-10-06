/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Scale
public import MIPRE.Background.Tailored.Intro.CompleteContract
public import MIPRE.Background.Tailored.Intro.LpIntroCost
public import MIPRE.Tailored.Stages
public import MIPRE.Foundations.Halting.Bounded
public import MIPRE.Foundations.Introspection.VerifierSourceGame

@[expose] public section

/-!
# Question reduction for tailored verifiers

`TailoredIntrospection 7` inhabited (blueprint `thm:tailored-qr`, paper II's
`thm:h_level_question_reduciton`, II:5712, in value form), on Route A of
`planning/aldous-lyons-track.md`: the tailored presentation of `Introspection.seven`.

The input's normal form verifier is `C₀ λ`-bounded for a `λ`-bounded input
(`TailoredVerifier.ofTNFVT_isBounded`), so the output at `λ` is the output tailored verifier
`Output.outTV` at `M λ`, with `M = 2^{C₀+1} ≥ max(C₀, 2)` a power of two so that `λ ↦ M λ` is a
polynomial-time function (`Scale.mulPow2F`): `seven`'s sampler, the answer-length calculator
`LenIntro.lenIntro` and the linear-constraints processor `LpIntro.lpIntro`, both at `M λ`. The
two programs meet the specification `Output.IntroSpec` (`LpIntro.introSpec_lenIntro_lpIntro`),
so soundness is `Output.soundness_contract` and completeness at `n ≥ 1` is
`Output.completeness_contract`; at `n = 0` both programs output nothing and the trivial strategy
is perfect (`Scale.hasPerfectZPC_of_zero`). The budgets at `M λ` are budgets at `λ` with the
exponent multiplied by `M` (`Budget.sampler_within`, `Scale.ansBound_scale`).
-/

namespace MIPRE.Tailored.TailoredVerifier

/-- `λ`-boundedness of a tailored verifier is monotone in `λ`. -/
theorem IsBounded.mono {ℓ : ℕ} {T : TailoredVerifier ℓ}
    {lam lam' : ℕ} (h : T.IsBounded lam) (hle : lam ≤ lam') : T.IsBounded lam' := by
  obtain ⟨hmain, hsize⟩ := h
  refine ⟨fun n hn => ?_, hsize.trans hle⟩
  obtain ⟨hdim, hS, hL, hP, hB⟩ := hmain n hn
  have hpow : n ^ lam ≤ n ^ lam' := Nat.pow_le_pow_right (by omega) hle
  exact ⟨hdim.trans hpow, hS.mono hpow hle, hL.mono hpow hle, hP.mono hpow hle,
    Intro.Scale.LenBound.mono hB hpow⟩

end MIPRE.Tailored.TailoredVerifier

namespace MIPRE.Tailored.Intro.Inhabit

open Cost MIPRE.Introspection

/-! ## The constants -/

/-- The constant of `ofTNFVT_isBounded` for `selfUniversal`. -/
noncomputable def C₀ : ℕ := (TailoredVerifier.ofTNFVT_isBounded selfUniversal).choose

theorem C₀_spec {ℓ : ℕ} (V : TailoredVerifier ℓ) (lam : ℕ) (h : V.IsBounded lam) :
    (V.ofTNFVT selfUniversal).IsBounded (C₀ * lam) :=
  (TailoredVerifier.ofTNFVT_isBounded selfUniversal).choose_spec V lam h

/-- The exponent of the scale. -/
noncomputable def kM : ℕ := C₀ + 1

/-- The scale `M = 2^{C₀+1}`. -/
noncomputable def M : ℕ := 2 ^ kM

theorem C₀_le_M : C₀ ≤ M := (Nat.lt_two_pow_self).le.trans' (by simp [kM])

theorem two_le_M : 2 ≤ M := by
  unfold M kM
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (C₀ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem one_le_M : 1 ≤ M := by have := two_le_M; omega

/-- The calculator's constant. -/
noncomputable def C₁ : ℕ := Scale.lenIntro_within.choose

/-- The processor's time constant. -/
noncomputable def C₂ : ℕ := LpIntro.lpIntro_budget.choose

/-- The processor's size constant. -/
noncomputable def C₃ : ℕ := LpIntro.lpIntro_size_le.choose

/-- The complexity constant of the stage. -/
noncomputable def Cf : ℕ := M * sevenC + M * C₁ + M * C₂ + C₃ * M ^ C₃ + 1

/-! ## The stage -/

/-- The output at `λ`: the output tailored verifier at `M λ`. -/
noncomputable def output (V : Prog × Prog × Prog) (lam : ℕ) : TailoredVerifier 5 :=
  Output.outTV sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 (M * lam)
    (LenIntro.lenIntro (M * lam)) (LpIntro.lpIntro V (M * lam))

theorem pow_le_pow_Cf (u k : ℕ) (hk : k ≤ Cf) : (u + 1) ^ k ≤ (u + 1) ^ Cf :=
  Nat.pow_le_pow_right (by omega) hk

theorem within (V : Prog × Prog × Prog) (lam n : ℕ) :
    (output V lam).Within n (Introspection.budget Cf lam n) := by
  have hM := one_le_M
  obtain ⟨hS, hd⟩ := Budget.sampler_within (Prog.nil, Prog.nil) hM lam n
  obtain ⟨hL, hLB⟩ := Scale.lenIntro_within.choose_spec M hM lam n
  have hP := LpIntro.lpIntro_budget.choose_spec V (M * lam) n
  have h1 : M * sevenC ≤ Cf := by unfold Cf; omega
  have h2 : M * C₁ ≤ Cf := by unfold Cf; omega
  have h3 : M * C₂ ≤ Cf := by unfold Cf; omega
  have h3' : C₂ ≤ Cf := (Nat.le_mul_of_pos_left _ hM).trans h3
  have hB1 : ansBound (M * C₁) lam n ≤ ansBound Cf lam n := InputRuns.ansBound_mono n h2 le_rfl
  have hB2 : ansBound C₂ (M * lam) n ≤ ansBound Cf lam n :=
    (Scale.ansBound_scale M C₂ lam n).trans (InputRuns.ansBound_mono n h3 le_rfl)
  refine ⟨hS.mono (pow_le_pow_Cf _ _ h1) h1, hd.trans (pow_le_pow_Cf _ _ h1),
    hL.mono hB1 h2, hP.mono hB2 h3', Scale.LenBound.mono hLB hB1⟩

theorem lp_size (V : Prog × Prog × Prog) (lam : ℕ) :
    (output V lam).lp.size ≤ Cf * (lam + 1) ^ Cf := by
  have h := LpIntro.lpIntro_size_le.choose_spec V (M * lam)
  change (LpIntro.lpIntro V (M * lam)).size ≤ _
  have hM := one_le_M
  have hC3 : C₃ ≤ Cf := by
    have : C₃ ≤ C₃ * M ^ C₃ := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    unfold Cf; omega
  calc (LpIntro.lpIntro V (M * lam)).size ≤ C₃ * (M * lam + 1) ^ C₃ := h
    _ ≤ C₃ * (M ^ C₃ * (lam + 1) ^ C₃) := by
        apply Nat.mul_le_mul_left
        rw [← Nat.mul_pow]
        exact Nat.pow_le_pow_left (by nlinarith) _
    _ = (C₃ * M ^ C₃) * (lam + 1) ^ C₃ := by ring
    _ ≤ Cf * (lam + 1) ^ Cf :=
        Nat.mul_le_mul (by unfold Cf; omega) (pow_le_pow_Cf _ _ hC3)

theorem completeness (T : TailoredVerifier 7) (lam n : ℕ) (hT : T.IsBounded lam)
    (hZ : T.HasPerfectZPC (2 ^ n)) : (output T.progs lam).HasPerfectZPC n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Scale.hasPerfectZPC_of_zero _ 0
      (fun x κ => LenIntro.lenIntro_lenIs_zero (Or.inr rfl) x κ)
      (fun x y aR bR => LpIntro.lpIntro_lpIs_zero (Or.inr rfl) x y aR bR)
  have hl : 1 ≤ lam := by have := hT.two_le; omega
  have hM := two_le_M
  have hl' : 1 ≤ M * lam := Nat.mul_pos (by omega) hl
  have hV : (T.ofTNFVT selfUniversal).IsBounded (M * lam) :=
    (C₀_spec T lam hT).mono (Nat.mul_le_mul_right _ C₀_le_M)
  have hT' : T.IsBounded (M * lam) := hT.mono (Nat.le_mul_of_pos_left _ (by omega))
  have hs := VerifierSource.dimension_le_registerBits sevenConstant_spec.1 _ hV hn
  exact Output.completeness_contract T selfUniversal hM hl hn hT hV
    (kerGens_regKerGens _) (LpIntro.introSpec_lenIntro_lpIntro T selfUniversal hT' hV hl' hn hs) hZ

theorem soundness (T : TailoredVerifier 7) (lam n : ℕ) (ε : ℝ) (hT : T.IsBounded lam)
    (hn : 1 ≤ n) (hε : 0 < ε) (hv : 1 - ε < (output T.progs lam).valStar n) :
    1 - Introspection.delta (CompiledSoundness.coefficient sevenConstant *
        (M : ℝ) ^ CompiledSoundness.coefficient sevenConstant) CompiledSoundness.exponent lam n ε ≤
      T.valStar (2 ^ n) := by
  have hl : 1 ≤ lam := by have := hT.two_le; omega
  have hM := two_le_M
  have hl' : 1 ≤ M * lam := Nat.mul_pos (by omega) hl
  have hV : (T.ofTNFVT selfUniversal).IsBounded (M * lam) :=
    (C₀_spec T lam hT).mono (Nat.mul_le_mul_right _ C₀_le_M)
  have hT' : T.IsBounded (M * lam) := hT.mono (Nat.le_mul_of_pos_left _ (by omega))
  have hs := VerifierSource.dimension_le_registerBits sevenConstant_spec.1 _ hV hn
  exact Output.soundness_contract T selfUniversal hM hl hn hT hV (kerGens_regKerGens _)
    (LpIntro.introSpec_lenIntro_lpIntro T selfUniversal hT' hV hl' hn hs) hε hv

/-- **Question reduction for tailored verifiers** (blueprint `thm:tailored-qr`, II:5712), at
input level `7`: the tailored presentation of `Introspection.seven` at `M λ`. -/
noncomputable def tailoredIntrospection : TailoredIntrospection 7 where
  a := CompiledSoundness.coefficient sevenConstant *
    (M : ℝ) ^ CompiledSoundness.coefficient sevenConstant
  b := CompiledSoundness.exponent
  one_le_a := by
    have h1 := CompiledSoundness.coefficient_one_le sevenConstant
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast one_le_M
    have h2 : (1 : ℝ) ≤ (M : ℝ) ^ CompiledSoundness.coefficient sevenConstant :=
      Real.one_le_rpow hM (by linarith)
    nlinarith
  b_pos := CompiledSoundness.exponent_pos
  b_le_one := CompiledSoundness.exponent_le_one
  C := Cf
  sampler lam := PauliSampler.finalSampler sevenConstant one_le_sevenConstant
    sevenConstant_spec.2.1 7 (M * lam)
  samplerProg := (PauliSampler.finalCompiler sevenConstant 7).comp (Scale.mulPow2F kM)
  samplerProg_eq lam := by
    rw [PolyTimeFun.comp_apply, Scale.mulPow2F_apply]
    exact PauliSampler.finalCompiler_apply sevenConstant one_le_sevenConstant
      sevenConstant_spec.2.1 7 _
  len lam := LenIntro.lenIntro (M * lam)
  lenProg := LenIntro.lenIntroProg.comp (Scale.mulPow2F kM)
  lenProg_eq lam := by
    rw [PolyTimeFun.comp_apply, Scale.mulPow2F_apply]
    exact LenIntro.lenIntroProg_eq _
  compute := LpIntro.lpIntroProg.comp
    (PolyTimeFun.fst.pair ((Scale.mulPow2F kM).comp PolyTimeFun.snd))
  output := output
  output_sampler _ _ := rfl
  output_len _ _ := rfl
  output_lp V lam := by
    simp only [PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.fst_apply,
      PolyTimeFun.snd_apply, Scale.mulPow2F_apply]
    exact (LpIntro.lpIntroProg_eq V _).symm
  within V lam n := within V lam n
  lp_size := lp_size
  len_total lam n := LenIntro.lenIntro_lenTotal _ n _
  completeness V lam n hV hZ := completeness V lam n hV hZ
  soundness V lam n ε hV hn hε hv := soundness V lam n ε hV hn hε hv

/-- **`TailoredIntrospection 7` is inhabited.** -/
theorem exists_tailoredIntrospection : Nonempty (TailoredIntrospection 7) :=
  ⟨tailoredIntrospection⟩

end MIPRE.Tailored.Intro.Inhabit

end
