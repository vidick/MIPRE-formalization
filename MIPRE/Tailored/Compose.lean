/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Stages
public import MIPRE.Foundations.Pipeline.Compress

@[expose] public section

/-!
# Tailored compression from its three stages

Phase 5 of `planning/aldous-lyons-track.md`; paper II, `thm:h_level_compression` (II:5643), in
value form. `TailoredGapCompression.ofTailoredPipeline` composes question reduction
(`TailoredIntrospection 7`), answer reduction (`TailoredAnswerReduction 5`) and parallel
repetition (`TailoredRepetition 7`) into a `TailoredGapCompression 7`, along the route of the
existing pipeline's `GapCompression.ofPipeline` (`MIPRE/Foundations/Pipeline/Compress.lean`),
whose margins (`MIPRE/Foundations/Pipeline/Margin.lean`) it reuses.

What differs from the existing composition:

* every verifier has three programs, so the size parameter `σ(λ)` dominates the sizes of the
  introspective sampler, answer-length calculator and linear-constraints processor, and the
  accounting carries a third program in every line;
* the compressed answer-length calculator depends on `λ` only: it is repetition's calculator on
  the answer-reduced sampler and calculator at `λ`, which depend on `λ` only;
* completeness is read in perfect ZPC strategies, and the chain has no answer bounds to adjust;
* repetition reads its input's lengths from the calculator, so the parse exponent `β` becomes an
  exponent bounding the answer-reduced lengths, `B(λ, n) ≤ (λn + 1)^β`, which `τ` is chosen
  against.
-/

namespace MIPRE.Tailored

open Cost

namespace TailoredVerifier

variable {ℓ : ℕ} {V : TailoredVerifier ℓ}

theorem Within.mono {n : ℕ} {R R' : Budget} (h : V.Within n R) (hle : R.Le R') :
    V.Within n R' :=
  ⟨h.1.mono hle.1 hle.2.2.2.1, h.2.1.trans hle.2.1, h.2.2.1.mono hle.2.2.1 hle.2.2.2.1,
    h.2.2.2.1.mono hle.2.2.1 hle.2.2.2.1,
    fun x κ k hk => (h.2.2.2.2 x κ k hk).trans hle.2.2.2.2⟩

end TailoredVerifier

namespace Compose

open Polynomial

/-! ## The size of a program computed from `λ` -/

/-- The coefficient of the monomial bound on the size of `f λ`. -/
noncomputable def coefOf (f : PolyTimeFun ℕ Prog) : ℕ :=
  (∑ i ∈ Finset.range (f.timeBound.natDegree + 1), f.timeBound.coeff i) *
    4 ^ f.timeBound.natDegree

/-- `|f λ| ≤ c (λ + 1)^d` for a polynomial-time `f`. -/
theorem esize_le_coefOf (f : PolyTimeFun ℕ Prog) (lam : ℕ) :
    esize (f lam) ≤ coefOf f * (lam + 1) ^ f.timeBound.natDegree := by
  have hs : 4 * Nat.size lam + 1 ≤ 4 * (lam + 1) := by
    have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := lam)); omega
  refine (f.esize_apply_le lam).trans ((polynomial_eval_mono _ (esize_nat_le lam)).trans
    ((polynomial_eval_mono _ hs).trans ((polynomial_eval_le_sum_coeff_mul_pow _
      (by omega)).trans (le_of_eq ?_))))
  rw [coefOf, mul_pow, Nat.mul_assoc]

/-- `|f λ| ≤ poly(|λ|)`, the bound monotone in `λ`. -/
noncomputable def sizeOf (f : PolyTimeFun ℕ Prog) (lam : ℕ) : ℕ :=
  f.timeBound.eval (4 * Nat.size lam + 1)

theorem esize_le_sizeOf (f : PolyTimeFun ℕ Prog) (lam : ℕ) : esize (f lam) ≤ sizeOf f lam :=
  (f.esize_apply_le lam).trans (polynomial_eval_mono _ (esize_nat_le lam))

theorem polyBounded_sizeOf (f : PolyTimeFun ℕ Prog) : PolyBounded (sizeOf f) :=
  PolyBounded.eval _ ((PolyBounded.size.const_mul 4).add_const 1)

/-! ## The parameters -/

variable (I : TailoredIntrospection 7) (A : TailoredAnswerReduction 5) (R : TailoredRepetition 7)

/-- The exponent of `σ`: `C_σ (λ + 1)^{C_σ}` dominates the sizes of the three introspective
programs. -/
noncomputable def Csig : ℕ :=
  I.C + coefOf I.samplerProg + I.samplerProg.timeBound.natDegree + coefOf I.lenProg +
    I.lenProg.timeBound.natDegree

theorem mul_pow_le_Csig {c d : ℕ} (hc : c ≤ Csig I) (hd : d ≤ Csig I) (lam : ℕ) :
    c * (lam + 1) ^ d ≤ Csig I * (lam + 1) ^ Csig I :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)

/-- `σ(λ)`. -/
noncomputable def sigma (lam : ℕ) : ℕ := MIPRE.Pipeline.sigmaFun (Csig I) lam

theorem le_sigma {c d : ℕ} (hc : c ≤ Csig I) (hd : d ≤ Csig I) (lam : ℕ) :
    c * (lam + 1) ^ d ≤ sigma I lam :=
  (mul_pow_le_Csig I hc hd lam).trans (MIPRE.Pipeline.le_sigmaFun _ _)

/-- **The introspective verifier is within `σ(λ)`**: all three of its programs. -/
theorem size_le_sigma (V : Prog × Prog × Prog) (lam : ℕ) :
    (I.output V lam).size ≤ sigma I lam := by
  refine max_le ?_ (max_le ?_ ?_)
  · show esize (I.output V lam).sampler.prog ≤ _
    rw [I.output_sampler, ← I.samplerProg_eq]
    exact (esize_le_coefOf _ lam).trans (le_sigma I (by unfold Csig; omega)
      (by unfold Csig; omega) lam)
  · show esize (I.output V lam).len.prog ≤ _
    rw [I.output_len, ← I.lenProg_eq]
    exact (esize_le_coefOf _ lam).trans (le_sigma I (by unfold Csig; omega)
      (by unfold Csig; omega) lam)
  · exact (I.lp_size V lam).trans (le_sigma I (by unfold Csig; omega) (by unfold Csig; omega) lam)

theorem one_le_sigma (lam : ℕ) : 1 ≤ sigma I lam := MIPRE.Pipeline.one_le_sigmaFun _ _

theorem sigma_mono {m n : ℕ} (h : m ≤ n) : sigma I m ≤ sigma I n :=
  MIPRE.Pipeline.sigmaFun_mono _ h

/-- The exponent `K` with `σ(z) ≤ z^K` for `z ≥ 2`. -/
noncomputable def K : ℕ := (MIPRE.Pipeline.polyBounded_sigmaFun (Csig I)).exists_le_pow.choose

theorem sigma_le_pow : ∀ z, 2 ≤ z → sigma I z ≤ z ^ K I :=
  (MIPRE.Pipeline.polyBounded_sigmaFun (Csig I)).exists_le_pow.choose_spec

/-- `μ`, from the margin claim, at least `C + 1`. -/
noncomputable def mu : ℕ :=
  (MIPRE.Pipeline.exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I) (I.C + 1)).choose

theorem C_succ_le_mu : I.C + 1 ≤ mu I A :=
  (MIPRE.Pipeline.exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I)
    (I.C + 1)).choose_spec.1

theorem C_le_mu : I.C ≤ mu I A := (Nat.le_succ _).trans (C_succ_le_mu I A)

theorem one_le_mu : 1 ≤ mu I A := (Nat.le_add_left 1 _).trans (C_succ_le_mu I A)

/-- The threshold of the margin claim. -/
noncomputable def N₁ : ℕ :=
  (MIPRE.Pipeline.exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I)
    (I.C + 1)).choose_spec.2.choose

theorem margin_spec : ∀ x : ℝ, (N₁ I A : ℝ) ≤ x → ∀ s : ℝ, 1 ≤ s → s ≤ x ^ (K I : ℝ) →
    s ^ A.a * x ^ (-((mu I A : ℝ) * A.b)) < MIPRE.Pipeline.eps1 I.a I.b x / 2 :=
  (MIPRE.Pipeline.exists_mu (b₁ := I.b) I.one_le_a A.one_le_a A.b_pos (K I)
    (I.C + 1)).choose_spec.2.choose_spec

theorem polyBounded_arBound :
    PolyBounded fun z => (A.bound.eval (z ^ mu I A + sigma I z + z + z)) ^ (mu I A + 1) :=
  (PolyBounded.eval A.bound ((((PolyBounded.id.pow _).add
    (MIPRE.Pipeline.polyBounded_sigmaFun (Csig I))).add PolyBounded.id).add PolyBounded.id)).pow _

/-- `β`, an exponent bounding the answer-reduced lengths: `B(λ, n) ≤ (λn + 1)^β`. -/
noncomputable def beta : ℕ := (polyBounded_arBound I A).exists_le_pow.choose

theorem arBound_le_pow :
    ∀ z, 2 ≤ z → (A.bound.eval (z ^ mu I A + sigma I z + z + z)) ^ (mu I A + 1) ≤ z ^ beta I A :=
  (polyBounded_arBound I A).exists_le_pow.choose_spec

/-- `P`, with `ε₂ ≥ x^{-P}`. -/
noncomputable def P : ℕ :=
  (MIPRE.Pipeline.exists_eps2_lower I.one_le_a I.b_pos A.one_le_a A.b_pos (mu I A)
    (K I)).choose

/-- The threshold of the lower bound on `ε₂`. -/
noncomputable def N₂ : ℕ :=
  (MIPRE.Pipeline.exists_eps2_lower I.one_le_a I.b_pos A.one_le_a A.b_pos (mu I A)
    (K I)).choose_spec.choose

theorem eps2_lower_spec : ∀ x : ℝ, (N₂ I A : ℝ) ≤ x → ∀ s : ℝ, 1 ≤ s → s ≤ x ^ (K I : ℝ) →
    x ^ (-(P I A : ℝ)) ≤ MIPRE.Pipeline.eps2 I.a I.b A.a A.b (mu I A) s x :=
  (MIPRE.Pipeline.exists_eps2_lower I.one_le_a I.b_pos A.one_le_a A.b_pos (mu I A)
    (K I)).choose_spec.choose_spec

/-- `τ`, the repetition exponent, against the lengths `B(λ, n) ≤ (λn + 1)^β`. -/
noncomputable def tau : ℕ := (MIPRE.Pipeline.exists_tau R.c_pos (P I A) (beta I A)).choose

theorem tau_spec : ∀ z : ℝ, (tau I A R : ℝ) ≤ z → ∀ k : ℝ, z ^ tau I A R ≤ k →
    ∀ B : ℝ, 0 ≤ B → B ≤ z ^ beta I A → ∀ ε : ℝ, 0 < ε → z ^ (-(P I A : ℝ)) ≤ ε →
    Real.exp (-(R.c * ε ^ 13 * k / (B + 1))) ≤ 1 / 2 :=
  (MIPRE.Pipeline.exists_tau R.c_pos (P I A) (beta I A)).choose_spec

/-- The threshold of the introspection margin, `⌈(4a)^{1/b}⌉`. -/
noncomputable def C₁ : ℕ := ⌈(4 * I.a) ^ (1 / I.b)⌉₊

/-- `C₀`, the threshold of the compression theorem. -/
noncomputable def C₀ : ℕ :=
  max (max (max 2 (C₁ I)) (max (N₁ I A) (N₂ I A))) (max A.C (tau I A R))

theorem C₀_spec {n : ℕ} (hn : C₀ I A R ≤ n) :
    2 ≤ n ∧ C₁ I ≤ n ∧ N₁ I A ≤ n ∧ N₂ I A ≤ n ∧ A.C ≤ n ∧ tau I A R ≤ n := by
  unfold C₀ at hn
  omega

/-! ## The data -/

/-- The answer-reduced verifier at `λ`, at level `7 = max (5 + 2) 5`. -/
noncomputable def arOutput (V : Prog × Prog × Prog) (lam : ℕ) : TailoredVerifier 7 :=
  A.output (I.output V lam) lam (mu I A) (sigma I lam)

/-- The answer-reduced sampler at `λ`, which depends on `λ` only. -/
noncomputable def arSampler (lam : ℕ) : CL.Sampler 7 :=
  A.sampler (I.sampler lam) lam (mu I A) (sigma I lam)

/-- The answer-reduced calculator at `λ`. -/
noncomputable def arLen (lam : ℕ) : Decider := A.len lam (mu I A) (sigma I lam)

theorem arOutput_sampler (V : Prog × Prog × Prog) (lam : ℕ) :
    (arOutput I A V lam).sampler = arSampler I A lam := by
  rw [arOutput, A.output_sampler, I.output_sampler, arSampler]

theorem arOutput_len (V : Prog × Prog × Prog) (lam : ℕ) :
    (arOutput I A V lam).len = arLen I A lam := A.output_len _ _ _ _

/-- The parameters `(λ, μ, σ(λ))`, as a polynomial-time function of `λ`. -/
noncomputable def paramsF : PolyTimeFun ℕ (ℕ × ℕ × ℕ) :=
  (PolyTimeFun.id ℕ).pair ((PolyTimeFun.const (mu I A)).pair
    (MIPRE.Pipeline.sigmaFun (Csig I)))

theorem paramsF_apply (lam : ℕ) : paramsF I A lam = (lam, mu I A, sigma I lam) := rfl

/-- The answer-reduced sampler's program, from `λ`. -/
noncomputable def arSamplerProg : PolyTimeFun ℕ Prog :=
  A.samplerProg.comp (I.samplerProg.pair (paramsF I A))

theorem arSamplerProg_eq (lam : ℕ) : arSamplerProg I A lam = (arSampler I A lam).prog := by
  simp only [arSamplerProg, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, paramsF_apply]
  rw [I.samplerProg_eq, A.samplerProg_eq]
  rfl

/-- The answer-reduced calculator's program, from `λ`. -/
noncomputable def arLenProg : PolyTimeFun ℕ Prog := A.lenProg.comp (paramsF I A)

theorem arLenProg_eq (lam : ℕ) : arLenProg I A lam = (arLen I A lam).prog := by
  simp only [arLenProg, PolyTimeFun.comp_apply, paramsF_apply]
  exact A.lenProg_eq _ _ _

/-- The compressed sampler `S^λ`. -/
noncomputable def sampler (lam : ℕ) : CL.Sampler 7 :=
  R.sampler (arSampler I A lam) lam (tau I A R)

/-- Its program, as a polynomial-time function of `λ`. -/
noncomputable def samplerProg : PolyTimeFun ℕ Prog :=
  R.samplerProg.comp ((arSamplerProg I A).pair
    ((PolyTimeFun.id ℕ).pair (PolyTimeFun.const (tau I A R))))

theorem samplerProg_eq (lam : ℕ) : samplerProg I A R lam = (sampler I A R lam).prog := by
  simp only [samplerProg, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.id_apply,
    PolyTimeFun.const_apply]
  rw [arSamplerProg_eq, R.samplerProg_eq]
  rfl

/-- The compressed answer-length calculator `L^λ`. -/
noncomputable def len (lam : ℕ) : Decider :=
  R.len (arSampler I A lam) (arLen I A lam) lam (tau I A R)

/-- Its program, as a polynomial-time function of `λ`. -/
noncomputable def lenProg : PolyTimeFun ℕ Prog :=
  R.lenProg.comp ((arSamplerProg I A).pair ((arLenProg I A).pair
    ((PolyTimeFun.id ℕ).pair (PolyTimeFun.const (tau I A R)))))

theorem lenProg_eq (lam : ℕ) : lenProg I A R lam = (len I A R lam).prog := by
  simp only [lenProg, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.id_apply,
    PolyTimeFun.const_apply]
  rw [arSamplerProg_eq, arLenProg_eq, R.lenProg_eq]
  rfl

/-- `Compress`: the program of the compressed linear-constraints processor, from the input's
three programs and `λ`. -/
noncomputable def compress : PolyTimeFun ((Prog × Prog × Prog) × ℕ) Prog :=
  let lamF : PolyTimeFun ((Prog × Prog × Prog) × ℕ) ℕ := PolyTimeFun.snd
  let params := (paramsF I A).comp lamF
  let P₂ := A.compute.comp
    (((I.samplerProg.comp lamF).pair ((I.lenProg.comp lamF).pair I.compute)).pair params)
  R.compute.comp ((((arSamplerProg I A).comp lamF).pair (((arLenProg I A).comp lamF).pair P₂)).pair
    (lamF.pair (PolyTimeFun.const (tau I A R))))

/-- The output of `Compress`. -/
noncomputable def output (V : Prog × Prog × Prog) (lam : ℕ) : TailoredVerifier 7 :=
  R.output (arOutput I A V lam) lam (tau I A R)

theorem output_sampler (V : Prog × Prog × Prog) (lam : ℕ) :
    (output I A R V lam).sampler = sampler I A R lam := by
  rw [output, R.output_sampler, arOutput_sampler, sampler]

theorem output_len (V : Prog × Prog × Prog) (lam : ℕ) :
    (output I A R V lam).len = len I A R lam := by
  rw [output, R.output_len, arOutput_sampler, arOutput_len, len]

theorem arOutput_progs (V : Prog × Prog × Prog) (lam : ℕ) :
    (arOutput I A V lam).progs = (arSamplerProg I A lam, arLenProg I A lam,
      A.compute ((I.samplerProg lam, I.lenProg lam, I.compute (V, lam)), lam, mu I A,
        sigma I lam)) := by
  rw [TailoredVerifier.progs, arOutput_sampler, arOutput_len, ← arSamplerProg_eq,
    ← arLenProg_eq, arOutput, A.output_lp, TailoredVerifier.progs, I.output_sampler,
    I.output_len, I.output_lp, I.samplerProg_eq, I.lenProg_eq]

theorem output_lp (V : Prog × Prog × Prog) (lam : ℕ) :
    (output I A R V lam).lp.prog = compress I A R (V, lam) := by
  rw [output, R.output_lp, arOutput_progs]
  rfl

/-! ## The accounting -/

/-- A bound on the size of the encoded parameters `(λ, μ, σ(λ))`. -/
noncomputable def pArg (lam : ℕ) : ℕ :=
  4 * Nat.size lam + 1 + (esize (mu I A) + (4 * Nat.size (sigma I lam) + 1) + 1) + 1

theorem esize_params_le (lam : ℕ) : esize (lam, mu I A, sigma I lam) ≤ pArg I A lam := by
  simp only [esize_prod, pArg]
  have := esize_nat_le lam
  have := esize_nat_le (sigma I lam)
  omega

/-- A bound on the size of the answer-reduced verifier, as a function of `λ`. -/
noncomputable def wSize (lam : ℕ) : ℕ :=
  A.samplerProg.timeBound.eval (sizeOf I.samplerProg lam + pArg I A lam + 1) +
    A.lenProg.timeBound.eval (pArg I A lam) +
    A.compute.timeBound.eval (sizeOf I.samplerProg lam + sizeOf I.lenProg lam +
      I.C * (lam + 1) ^ I.C + 2 + pArg I A lam + 1)

theorem arOutput_size_le (V : Prog × Prog × Prog) (lam : ℕ) :
    (arOutput I A V lam).size ≤ wSize I A lam := by
  have hp := esize_params_le I A lam
  have hS := esize_le_sizeOf I.samplerProg lam
  have hL := esize_le_sizeOf I.lenProg lam
  have hP : esize (I.compute (V, lam)) ≤ I.C * (lam + 1) ^ I.C := by
    rw [← I.output_lp]; exact I.lp_size V lam
  have hprogs := arOutput_progs I A V lam
  simp only [TailoredVerifier.progs, Prod.mk.injEq] at hprogs
  obtain ⟨e1, e2, e3⟩ := hprogs
  refine max_le ?_ (max_le ?_ ?_)
  · show esize (arOutput I A V lam).sampler.prog ≤ _
    rw [e1, arSamplerProg, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, paramsF_apply]
    have hx : esize (I.samplerProg lam, lam, mu I A, sigma I lam) ≤
        sizeOf I.samplerProg lam + pArg I A lam + 1 := by
      simp only [esize_prod] at hp ⊢; omega
    refine (A.samplerProg.esize_apply_le _).trans ((polynomial_eval_mono _ hx).trans ?_)
    unfold wSize; omega
  · show esize (arOutput I A V lam).len.prog ≤ _
    rw [e2, arLenProg, PolyTimeFun.comp_apply, paramsF_apply]
    refine (A.lenProg.esize_apply_le _).trans ((polynomial_eval_mono _ hp).trans ?_)
    unfold wSize; omega
  · show esize (arOutput I A V lam).lp.prog ≤ _
    rw [e3]
    have hx : esize ((I.samplerProg lam, I.lenProg lam, I.compute (V, lam)), lam, mu I A,
        sigma I lam) ≤ sizeOf I.samplerProg lam + sizeOf I.lenProg lam +
          I.C * (lam + 1) ^ I.C + 2 + pArg I A lam + 1 := by
      simp only [esize_prod] at hp ⊢; omega
    refine (A.compute.esize_apply_le _).trans ((polynomial_eval_mono _ hx).trans ?_)
    unfold wSize; omega

/-- The bound of the answer-reduced verifier at `(λ, n)`. -/
noncomputable def arBound (lam n : ℕ) : ℕ :=
  AnswerReduction.outBound A.bound lam (mu I A) (sigma I lam) n

/-- The answer-reduced verifier's input-size degree. -/
noncomputable def arDegree : ℕ := AnswerReduction.outDegree A.deg (mu I A)

/-- The running-time bound of the compressed verifier at `(λ, n)`. -/
noncomputable def timeB (lam n : ℕ) : ℕ :=
  R.bound.eval (TailoredRepetition.arg lam (tau I A R) n
    (Budget.uniform (arBound I A lam n) (arDegree I A)) (wSize I A lam))

/-- The length bound of the compressed verifier at `(λ, n)`. -/
noncomputable def lenB (lam n : ℕ) : ℕ := Repetition.reps lam (tau I A R) n * arBound I A lam n

/-- Both bounds, as one function of `z = n + λ`. -/
noncomputable def G (z : ℕ) : ℕ := timeB I A R z z + lenB I A R z z

attribute [local gcongr] polynomial_eval_mono Nat.size_le_size MIPRE.Pipeline.sigmaFun_mono

theorem arBound_mono {lam n lam' n' : ℕ} (hl : lam ≤ lam') (hn : n ≤ n') :
    arBound I A lam n ≤ arBound I A lam' n' := by
  unfold arBound AnswerReduction.outBound AnswerReduction.arg sigma
  gcongr

theorem timeB_mono {lam n lam' n' : ℕ} (hl : lam ≤ lam') (hn : n ≤ n') :
    timeB I A R lam n ≤ timeB I A R lam' n' := by
  have ha := arBound_mono I A hl hn
  unfold timeB TailoredRepetition.arg Repetition.reps wSize pArg sizeOf sigma
  simp only [Budget.uniform_S, Budget.uniform_d, Budget.uniform_D, Budget.uniform_B,
    Budget.uniform_k]
  gcongr

theorem lenB_mono {lam n lam' n' : ℕ} (hl : lam ≤ lam') (hn : n ≤ n') :
    lenB I A R lam n ≤ lenB I A R lam' n' := by
  unfold lenB Repetition.reps
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by gcongr))
    (arBound_mono I A hl hn)

theorem timeB_le_G (lam n : ℕ) : timeB I A R lam n ≤ G I A R (n + lam) :=
  (timeB_mono I A R (by omega) (by omega)).trans (Nat.le_add_right _ _)

theorem lenB_le_G (lam n : ℕ) : lenB I A R lam n ≤ G I A R (n + lam) :=
  (lenB_mono I A R (by omega) (by omega)).trans (Nat.le_add_left _ _)

theorem polyBounded_G : PolyBounded (G I A R) := by
  have hz : PolyBounded fun z : ℕ => z * z + 1 := (PolyBounded.id.mul PolyBounded.id).add_const 1
  have hpow2 : ∀ e : ℕ, PolyBounded fun z : ℕ => 2 ^ (e * (Nat.size z + Nat.size z)) := fun e =>
    (PolyBounded.two_pow_size 0 (2 * e)).mono fun z => le_of_eq (by ring_nf)
  have hsig : PolyBounded fun z : ℕ => sigma I z := MIPRE.Pipeline.polyBounded_sigmaFun (Csig I)
  have hp : PolyBounded fun z : ℕ => pArg I A z := by
    unfold pArg
    exact ((((PolyBounded.size.const_mul 4).add_const 1).add
      ((PolyBounded.const _).add (((PolyBounded.size.comp hsig).const_mul 4).add_const 1)
        |>.add_const 1)).add_const 1)
  have hS := polyBounded_sizeOf I.samplerProg
  have hL := polyBounded_sizeOf I.lenProg
  have hw : PolyBounded fun z : ℕ => wSize I A z := by
    unfold wSize
    exact ((PolyBounded.eval _ ((hS.add hp).add_const 1)).add (PolyBounded.eval _ hp)).add
      (PolyBounded.eval _ (((((hS.add hL).add ((PolyBounded.const I.C).mul
        ((PolyBounded.id.add_const 1).pow I.C))).add_const 2).add hp).add_const 1))
  have har : PolyBounded fun z : ℕ => arBound I A z z :=
    (PolyBounded.eval _ ((((hz.pow _).add hsig).add PolyBounded.id).add PolyBounded.id)).pow _
  have ht : PolyBounded fun z : ℕ => timeB I A R z z := by
    unfold timeB TailoredRepetition.arg
    simp only [Budget.uniform_S, Budget.uniform_d, Budget.uniform_D, Budget.uniform_B,
      Budget.uniform_k]
    exact PolyBounded.eval _ (((((((hpow2 _).add har).add har).add har).add har).add hw)
      |>.add PolyBounded.id |>.add (PolyBounded.const _) |>.add PolyBounded.id
      |>.add (PolyBounded.const _))
  have hl : PolyBounded fun z : ℕ => lenB I A R z z := by
    unfold lenB Repetition.reps
    exact (hpow2 _).mul har
  exact ht.add hl

/-- The polynomial `poly(n, λ)` of the compression theorem. -/
noncomputable def bound : Polynomial ℕ := (polyBounded_G I A R).poly

theorem timeB_le_bound (lam n : ℕ) : timeB I A R lam n ≤ (bound I A R).eval (n + lam) :=
  (timeB_le_G I A R lam n).trans ((polyBounded_G I A R).le_poly_eval _)

theorem lenB_le_bound (lam n : ℕ) : lenB I A R lam n ≤ (bound I A R).eval (n + lam) :=
  (lenB_le_G I A R lam n).trans ((polyBounded_G I A R).le_poly_eval _)

/-- The introspective verifier is within answer reduction's input budget. -/
theorem introOutput_within (V : Prog × Prog × Prog) (lam n : ℕ) :
    (I.output V lam).Within n (AnswerReduction.inBudget lam (mu I A) n) := by
  refine (I.within V lam n).mono ⟨?_, ?_, ?_, C_le_mu I A, ?_⟩ <;>
    simp only [Introspection.budget, AnswerReduction.inBudget, Introspection.ansBound,
      AnswerReduction.inAns]
  · exact Nat.pow_le_pow_right (by omega) (C_le_mu I A)
  · exact Nat.pow_le_pow_right (by omega) (C_le_mu I A)
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) (C_le_mu I A))
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) (C_le_mu I A))

/-- The answer-reduced verifier is within its bound. -/
theorem arOutput_within (V : Prog × Prog × Prog) (lam n : ℕ) :
    (arOutput I A V lam).Within n (Budget.uniform (arBound I A lam n) (arDegree I A)) :=
  A.within (I.output V lam) lam (mu I A) (sigma I lam) n (introOutput_within I A V lam n)
    (size_le_sigma I V lam)

/-- The compressed verifier is within its bounds. -/
theorem output_within (V : Prog × Prog × Prog) (lam n : ℕ) :
    (output I A R V lam).Within n
      ⟨timeB I A R lam n, timeB I A R lam n, timeB I A R lam n, R.deg * (arDegree I A + 1),
        lenB I A R lam n⟩ := by
  have h := R.within (arOutput I A V lam) lam (tau I A R) n _ (arOutput_within I A V lam n)
  have hs := arOutput_size_le I A V lam
  refine h.mono ⟨?_, ?_, ?_, le_rfl, le_rfl⟩ <;>
  · show R.bound.eval _ ≤ timeB I A R lam n
    unfold timeB
    exact polynomial_eval_mono _ (by unfold TailoredRepetition.arg; omega)

/-- `(λn + 1)^τ ≤ k(n)`, and the answer-reduced lengths are at most `(λn + 1)^β`. -/
theorem arBound_le_pow' {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    arBound I A lam n ≤ (lam * n + 1) ^ beta I A := by
  have hz : 2 ≤ lam * n + 1 := by nlinarith
  have hs : sigma I lam ≤ sigma I (lam * n + 1) := sigma_mono I (by nlinarith)
  calc arBound I A lam n ≤
        (A.bound.eval ((lam * n + 1) ^ mu I A + sigma I (lam * n + 1) + (lam * n + 1) +
          (lam * n + 1))) ^ (mu I A + 1) :=
        Nat.pow_le_pow_left (polynomial_eval_mono _ (by
          unfold AnswerReduction.arg
          have h1 : lam ≤ lam * n + 1 := by nlinarith
          have h2 : n ≤ lam * n + 1 := by nlinarith
          omega)) _
    _ ≤ (lam * n + 1) ^ beta I A := arBound_le_pow I A _ hz

/-! ## The value chain -/

theorem one_le_of_isBounded {ℓ : ℕ} {V : TailoredVerifier ℓ} {lam : ℕ} (hB : V.IsBounded lam) :
    1 ≤ lam :=
  le_trans (le_trans (Data.size_pos _) (le_max_left _ _)) hB.2

/-- **Completeness of `Compress`**: the three completeness clauses chained. -/
theorem output_hasPerfectZPC (V : TailoredVerifier 7) (lam n : ℕ) (hB : V.IsBounded lam)
    (hn : C₀ I A R ≤ n) (h : V.HasPerfectZPC (2 ^ n)) :
    (output I A R V.progs lam).HasPerfectZPC n := by
  obtain ⟨-, -, -, -, hC, -⟩ := C₀_spec I A R hn
  have hlam := one_le_of_isBounded hB
  have h₁ := I.completeness V lam n hB h
  have h₂ := A.completeness (I.output V.progs lam) lam (mu I A) (sigma I lam) n hC hlam
    (one_le_mu I A) (introOutput_within I A _ lam n) (size_le_sigma I _ lam) h₁
  exact R.completeness _ lam (tau I A R) n h₂

/-- **Soundness of `Compress`**, value form: the three soundness clauses, contrapositively,
through the margins. -/
theorem output_valStar_le (V : TailoredVerifier 7) (lam n : ℕ) (hB : V.IsBounded lam)
    (hn : C₀ I A R ≤ n) (h : V.valStar (2 ^ n) ≤ 1 / 2) :
    (output I A R V.progs lam).valStar n ≤ 1 / 2 := by
  obtain ⟨h2, hC₁, hN₁, hN₂, hC, htau⟩ := C₀_spec I A R hn
  have hlam := one_le_of_isBounded hB
  set x : ℝ := (lam : ℝ) * n with hx
  have hnx : (n : ℝ) ≤ x := by
    rw [hx]; exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hlam)
  have hx1 : 1 ≤ x := le_trans (by exact_mod_cast (show 1 ≤ n by omega)) hnx
  have hx0 : 0 < x := by linarith
  set s : ℝ := (sigma I lam : ℝ) with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact_mod_cast one_le_sigma I lam
  have hsx : s ≤ x ^ (K I : ℝ) := by
    have h1 : sigma I lam ≤ (lam * n) ^ K I :=
      (sigma_mono I (by nlinarith)).trans (sigma_le_pow I _ (by nlinarith))
    rw [hs, hx, Real.rpow_natCast]
    exact_mod_cast h1
  set ε₁ := MIPRE.Pipeline.eps1 I.a I.b x with hε₁
  set ε₂ := MIPRE.Pipeline.eps2 I.a I.b A.a A.b (mu I A) s x with hε₂
  have hε₁0 : 0 < ε₁ := MIPRE.Pipeline.eps1_pos I.one_le_a hx0
  have hε₂0 : 0 < ε₂ := MIPRE.Pipeline.eps2_pos I.one_le_a (by linarith) hx0
  have hε₂1 : ε₂ ≤ 1 :=
    MIPRE.Pipeline.eps2_le_one I.one_le_a I.b_pos A.one_le_a A.b_pos hs1 hx1
  -- step 1: the introspective verifier has value at most `1 - ε₁`
  have h₁ : (I.output V.progs lam).valStar n ≤ 1 - ε₁ := by
    by_contra hc
    push Not at hc
    have hsound := I.soundness V lam n ε₁ hB (by omega) hε₁0 hc
    have hC₁' : (4 * I.a) ^ (1 / I.b) ≤ x := by
      have := Nat.le_ceil ((4 * I.a) ^ (1 / I.b))
      have : ((C₁ I : ℕ) : ℝ) ≤ n := by exact_mod_cast hC₁
      unfold C₁ at this
      linarith
    have hm := MIPRE.Pipeline.intro_margin I.one_le_a I.b_pos hx1 hC₁'
    unfold Introspection.delta at hsound
    linarith
  -- step 2: the answer-reduced verifier has value at most `1 - ε₂`
  have h₂ : (arOutput I A V.progs lam).valStar n ≤ 1 - ε₂ := by
    by_contra hc
    push Not at hc
    have hsound := A.soundness (I.output V.progs lam) lam (mu I A) (sigma I lam) n ε₂ hC h2 hlam
      (introOutput_within I A _ lam n) (size_le_sigma I _ lam) hε₂0 hc
    have hN₁' : (N₁ I A : ℝ) ≤ x := le_trans (by exact_mod_cast hN₁) hnx
    have hm := MIPRE.Pipeline.ar_margin I.one_le_a A.b_pos (by linarith : 0 < s) hx0
      (margin_spec I A x hN₁' s hs1 hsx)
    unfold AnswerReduction.delta at hsound
    linarith
  -- step 3: repetition
  have hlen : LenBound (arOutput I A V.progs lam).len n (arBound I A lam n) :=
    (arOutput_within I A V.progs lam n).2.2.2.2
  have h₄ := R.soundness _ lam (tau I A R) n (arBound I A lam n) ε₂ hε₂0 hε₂1 hlen h₂
  refine h₄.trans ?_
  have hz : (tau I A R : ℝ) ≤ ((lam * n + 1 : ℕ) : ℝ) := by
    have : tau I A R ≤ lam * n + 1 := by nlinarith
    exact_mod_cast this
  have hxz : x ≤ ((lam * n + 1 : ℕ) : ℝ) := by rw [hx]; push_cast; linarith
  have hlow : ((lam * n + 1 : ℕ) : ℝ) ^ (-(P I A : ℝ)) ≤ ε₂ := by
    refine le_trans ?_ (eps2_lower_spec I A x (le_trans (by exact_mod_cast hN₂) hnx) s hs1 hsx)
    rw [Real.rpow_neg hx0.le, Real.rpow_neg (by positivity)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx0 _) (Real.rpow_le_rpow hx0.le hxz (by positivity))
  have hk : ((lam * n + 1 : ℕ) : ℝ) ^ tau I A R ≤ (Repetition.reps lam (tau I A R) n : ℝ) := by
    exact_mod_cast MIPRE.Pipeline.pow_le_reps hlam (tau I A R)
  have hBle : (arBound I A lam n : ℝ) ≤ ((lam * n + 1 : ℕ) : ℝ) ^ beta I A := by
    exact_mod_cast arBound_le_pow' I A hlam (by omega)
  exact tau_spec I A R _ hz _ hk _ (by positivity) hBle ε₂ hε₂0 hlow

end Compose

open Compose in
/-- **Tailored compression from its stages** (paper II, `thm:h_level_compression`, II:5643,
value form): a `TailoredIntrospection 7`, a `TailoredAnswerReduction 5` and a
`TailoredRepetition 7` give a `TailoredGapCompression 7`. -/
noncomputable def TailoredGapCompression.ofTailoredPipeline (I : TailoredIntrospection 7)
    (A : TailoredAnswerReduction 5) (R : TailoredRepetition 7) : TailoredGapCompression 7 where
  C₀ := Compose.C₀ I A R
  sampler := Compose.sampler I A R
  samplerProg := Compose.samplerProg I A R
  samplerProg_eq := Compose.samplerProg_eq I A R
  len := Compose.len I A R
  lenProg := Compose.lenProg I A R
  lenProg_eq := Compose.lenProg_eq I A R
  compress := Compose.compress I A R
  output := Compose.output I A R
  output_sampler := Compose.output_sampler I A R
  output_len := Compose.output_len I A R
  output_lp := Compose.output_lp I A R
  bound := Compose.bound I A R
  deg := R.deg * (Compose.arDegree I A + 1)
  sampler_time lam n := by
    have h := (Compose.output_within I A R (.nil, .nil, .nil) lam n).1
    rw [Compose.output_sampler] at h
    exact h.mono (Compose.timeB_le_bound I A R lam n) le_rfl
  sampler_dim lam n := by
    have h := (Compose.output_within I A R (.nil, .nil, .nil) lam n).2.1
    rw [Compose.output_sampler] at h
    exact h.trans (Compose.timeB_le_bound I A R lam n)
  len_time lam n := by
    have h := (Compose.output_within I A R (.nil, .nil, .nil) lam n).2.2.1
    rw [Compose.output_len] at h
    exact h.mono (Compose.timeB_le_bound I A R lam n) le_rfl
  lp_time V lam n :=
    (Compose.output_within I A R V lam n).2.2.2.1.mono (Compose.timeB_le_bound I A R lam n)
      le_rfl
  len_bound lam n := by
    have h := (Compose.output_within I A R (.nil, .nil, .nil) lam n).2.2.2.2
    rw [Compose.output_len] at h
    exact fun x κ k hk => (h x κ k hk).trans (Compose.lenB_le_bound I A R lam n)
  len_total lam n := by
    have hA := A.len_total (I.output (.nil, .nil, .nil) lam) lam (Compose.mu I A)
      (Compose.sigma I lam) n
    rw [← A.output_len, ← A.output_sampler] at hA
    have h := R.len_total (Compose.arOutput I A (.nil, .nil, .nil) lam) lam (Compose.tau I A R)
      n hA
    change LenTotal (Compose.output I A R (.nil, .nil, .nil) lam).len n
      ((Compose.output I A R (.nil, .nil, .nil) lam).sampler.dim n) at h
    rw [Compose.output_len, Compose.output_sampler] at h
    exact h
  completeness V lam n hB hn h := Compose.output_hasPerfectZPC I A R V lam n hB hn h
  soundness V lam n hB hn h := Compose.output_valStar_le I A R V lam n hB hn h

end MIPRE.Tailored

end
