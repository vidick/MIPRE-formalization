/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Complete
public import MIPRE.Background.Introspection.AmbientRawGame
public import MIPRE.Background.Introspection.Compiler
public import MIPRE.Tailored.Extend
public import MIPRE.Tailored.Data.Presents
public import MIPRE.Tailored.OfTNFVT

@[expose] public section

/-!
# The output tailored verifier of the introspection presentation, from its specification

The output tailored verifier at `λ` has `seven`'s sampler and two programs, an answer-length
calculator `L` and a linear-constraints processor `P`. At an index `n` they meet the
specification `IntroSpec` when, at every question `vectorEquiv x` of the detyped presentation,
`L` outputs the presented game's lengths and `P` its constraints. Then the output's `n`-th game
extends the presented one along `vectorEquiv` (`extends_presented`), so it has its value and its
perfect ZPC strategies.

On the other side, the detyped game the presentation is compared with is the reference
verifier's game read along `vectorEquiv` (`quantumValue_H`), whose value is the value of
`seven`'s output (`output_val_eq_reference`). So the output's `val*` is at most the value of
`seven`'s output at the same index (`valStar_output_le`).
-/

namespace MIPRE.Tailored.Intro.Output

open Cost CL MIPRE.SAT MIPRE.Introspection MIPRE.QLD SourceCompiler PauliSamplerParameters
open DecisionCompiler CL.Detyping.DeciderProgram Typed Classical

variable (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ) (U : ClockedUniversalMachine)
  (V : Verifier 7)

/-- The reference verifier at index `n`. -/
noncomputable abbrev Ref : Verifier 5 :=
  reference c hc he U (V.sampler.prog, V.decider.prog) lam n

/-- **The detyped game is the reference verifier's game, read along `vectorEquiv`.** -/
theorem quantumValue_H :
    quantumValue (Sound.H c hc he lam n U V) =
      quantumValue ((Ref c hc he lam n U V).game n (outerBound c lam n)) := by
  refine quantumValue_eq_of_equiv_support ((Ref c hc he lam n U V).game n (outerBound c lam n))
    (Sound.H c hc he lam n U V) (vectorEquiv (PauliSampler.dimension c lam n))
    (vectorEquiv (PauliSampler.dimension c lam n)) (.refl _) (.refl _) (fun x y => ?_)
    (fun x y _ a b => ?_)
  · exact (verifier_game_mu graph (extendedSampler c hc he lam) _ _ _ _ n x y).symm
  · exact (verifier_game_D graph (extendedSampler c hc he lam) _ _ _ _ n x y a b).symm

variable {c hc he lam n U V} in
/-- **The presentation's value is at most that of `seven`'s output**, on the input's normal
form verifier. -/
theorem valStar_presented_le_output (T : TailoredVerifier 7) (hc2 : 2 ≤ c)
    {hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n}
    {kg : ∀ S : Finset (Fin (registerBits c lam n)), CL.RegLinear 𝔽₂ S →
      List (Fin (registerBits c lam n) → 𝔽₂)}
    (hkg : KerGens (registerBits c lam n) kg) (hacc : AcceptsAsInput T V n)
    (hV : V.IsBounded lam) (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    (presented graph (Sound.H c hc he lam n U V) (Sound.tdata c hc he lam n T V hs kg)).valStar ≤
      (output c hc he U (V.sampler.prog, V.decider.prog) lam).val .tensor n
        (outerBound c lam n) := by
  rw [output_val_eq_reference .tensor c hc he U _ hl hn le_rfl, ValueModel.tensor_val,
    ← quantumValue_H]
  exact Sound.valStar_tpresented_le hc2 hkg hacc U hV hn

/-! ## The output tailored verifier and its specification -/

/-- The output tailored verifier with programs `L` and `P`: `seven`'s sampler. -/
noncomputable def outTV (L P : Decider) : TailoredVerifier 5 :=
  ⟨PauliSampler.finalSampler c hc he 7 lam, L, P⟩

variable {lam n} in
include U V in
/-- The detyped questions, as the output's questions. -/
noncomputable def qe (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    (CL.Detyping.Coord DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)) → ZMod 2) ≃
      (Fin ((PauliSampler.finalSampler c hc he 7 lam).dim n) → 𝔽₂) :=
  (vectorEquiv (PauliSampler.dimension c lam n)).trans
    (Verifier.dimensionEquiv (samplerAgreement_reference c hc he U (V.sampler.prog,
      V.decider.prog) hl hn).symm.dimension)

variable {lam n} in
/-- **The specification of the output's two programs at index `n`**: at every detyped question
the answer-length calculator outputs the presented game's lengths, and the linear-constraints
processor its constraints. -/
structure IntroSpec (hl : 1 ≤ lam) (hn : 1 ≤ n)
    (G : TailoredGame (CL.Detyping.Coord DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)) → ZMod 2))
    (L P : Decider) : Prop where
  lenR_eq : ∀ x, LenIs L n (toBits (qe c hc he U V hl hn x)) false (G.lenR x)
  lenL_eq : ∀ x, LenIs L n (toBits (qe c hc he U V hl hn x)) true (G.lenL x)
  cons_eq : ∀ x y aR bR,
    LpIs P n (toBits (qe c hc he U V hl hn x)) (toBits (qe c hc he U V hl hn y)) aR bR (G.cons x y aR bR)

theorem lenOf_eq_of {ℓ : ℕ} {W : TailoredVerifier ℓ} {n : ℕ} {x : BitStr} {κ : Bool} {k : ℕ}
    (h : LenIs W.len n x κ k) : W.lenOf n x κ = k := by
  have hex : ∃ m, LenIs W.len n x κ m := ⟨_, h⟩
  rw [TailoredVerifier.lenOf, dite_eq_left hex]
  exact hex.choose_spec.unique h

variable {c hc he lam n U V} in
/-- **The output's game extends the presented game along the detyped questions.** -/
theorem extends_presented {hl : 1 ≤ lam} {hn : 1 ≤ n} {T : TailoredVerifier 7}
    {hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n}
    {kg : ∀ S : Finset (Fin (registerBits c lam n)), CL.RegLinear 𝔽₂ S →
      List (Fin (registerBits c lam n) → 𝔽₂)} {L P : Decider}
    (h : IntroSpec c hc he U V hl hn (presented graph (Sound.H c hc he lam n U V)
      (Sound.tdata c hc he lam n T V hs kg)) L P) :
    ((outTV c hc he lam L P).tgame n).Extends
      (presented graph (Sound.H c hc he lam n U V) (Sound.tdata c hc he lam n T V hs kg))
      (qe c hc he U V hl hn).toEmbedding where
  μ_eq x y := by
    have h1 := Verifier.game_mu_dimensionEquiv (T := 0)
      (samplerAgreement_reference c hc he U (V.sampler.prog, V.decider.prog) hl hn).symm
      (vectorEquiv _ x) (vectorEquiv _ y)
    exact h1.trans (verifier_game_mu graph (extendedSampler c hc he lam) _ _ _ _ n x y)
  support x' y' _ := ⟨⟨_, (qe c hc he U V hl hn).apply_symm_apply x'⟩, ⟨_, (qe c hc he U V hl hn).apply_symm_apply y'⟩⟩
  lenR_eq x := lenOf_eq_of (h.lenR_eq x)
  lenL_eq x := lenOf_eq_of (h.lenL_eq x)
  cons_eq x y := by
    funext aR bR
    exact TailoredVerifier.consOf_eq_of _
      (fun κ => Bool.casesOn (motive := fun κ => ∃ k, LenIs L n _ κ k) κ
        ⟨_, h.lenR_eq x⟩ ⟨_, h.lenL_eq x⟩)
      (fun κ => Bool.casesOn (motive := fun κ => ∃ k, LenIs L n _ κ k) κ
        ⟨_, h.lenR_eq y⟩ ⟨_, h.lenL_eq y⟩) (h.cons_eq x y aR bR)

/-! ## Soundness -/

variable {c hc he lam n U V} in
/-- **The output's `val*` is at most the value of `seven`'s output.** -/
theorem valStar_outTV_le {hl : 1 ≤ lam} {hn : 1 ≤ n} (T : TailoredVerifier 7) (hc2 : 2 ≤ c)
    {hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n}
    {kg : ∀ S : Finset (Fin (registerBits c lam n)), CL.RegLinear 𝔽₂ S →
      List (Fin (registerBits c lam n) → 𝔽₂)} {L P : Decider}
    (hkg : KerGens (registerBits c lam n) kg) (hacc : AcceptsAsInput T V n)
    (hV : V.IsBounded lam)
    (h : IntroSpec c hc he U V hl hn (presented graph (Sound.H c hc he lam n U V)
      (Sound.tdata c hc he lam n T V hs kg)) L P) :
    (outTV c hc he lam L P).valStar n ≤
      (output c hc he U (V.sampler.prog, V.decider.prog) lam).val .tensor n
        (outerBound c lam n) := by
  rw [TailoredVerifier.valStar, (extends_presented h).valStar_eq]
  exact valStar_presented_le_output T hc2 hkg hacc hV hl hn

/-- **Soundness of the output, through `seven`.** -/
theorem soundness_seven {lam n : ℕ} {V : Verifier 7} {hl : 1 ≤ lam} {hn : 1 ≤ n}
    (T : TailoredVerifier 7)
    {hs : V.sampler.dim (2 ^ n) ≤ registerBits sevenConstant lam n}
    {kg : ∀ S : Finset (Fin (registerBits sevenConstant lam n)), CL.RegLinear 𝔽₂ S →
      List (Fin (registerBits sevenConstant lam n) → 𝔽₂)} {L P : Decider}
    (hkg : KerGens (registerBits sevenConstant lam n) kg) (hacc : AcceptsAsInput T V n)
    (hV : V.IsBounded lam)
    (h : IntroSpec sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
      selfClockedUniversal V hl hn
      (presented graph (Sound.H sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 lam n
        selfClockedUniversal V)
        (Sound.tdata sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 lam n T V hs kg))
      L P)
    {ε : ℝ} (hε : 0 < ε)
    (hv : 1 - ε < (outTV sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 lam L P).valStar n) :
    1 - delta (CompiledSoundness.coefficient sevenConstant) CompiledSoundness.exponent lam n ε ≤
      V.val .tensor (2 ^ n) ((2 ^ n) ^ lam) := by
  apply sevenOutput_soundness .tensor ValueModel.tensor_projApprox QLD.approxSoundIn_tensor
    V lam n ε hV hn hε
  have hB : outerBound sevenConstant lam n ≤ ansBound sevenC lam n := by
    simpa only [DecisionCompiler.cutoffAt, show ¬(lam = 0 ∨ n = 0) by omega, ↓reduceIte] using
      sevenC_spec.2.2 lam n
  rw [output_val_cutoff .tensor _ _ _ _ _ hl hn hB]
  exact hv.trans_le (valStar_outTV_le T sevenConstant_spec.1 hkg hacc hV h)

/-! ## Completeness -/

variable {c hc he lam n U V} in
/-- **Completeness of the output**: a perfect PCC strategy of the reference verifier's typed game
meeting the three conditions of `Complete.hasPerfectZPC_tpresented` gives a perfect ZPC strategy
of the output's `n`-th game. -/
theorem hasPerfectZPC_outTV {hl : 1 ≤ lam} {hn : 1 ≤ n} (T : TailoredVerifier 7) (hc2 : 2 ≤ c)
    {hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n}
    {kg : ∀ S : Finset (Fin (registerBits c lam n)), CL.RegLinear 𝔽₂ S →
      List (Fin (registerBits c lam n) → 𝔽₂)} {L P : Decider}
    (hkg : KerGens (registerBits c lam n) kg) (hacc : AcceptsAsInput T V n)
    (hV : V.IsBounded lam)
    (h : IntroSpec c hc he U V hl hn (presented graph (Sound.H c hc he lam n U V)
      (Sound.tdata c hc he lam n T V hs kg)) L P)
    (R : SyncStrategy (rawGame c hc he U (V.sampler.prog, V.decider.prog) lam n).doubled)
    (hR : R.IsPCC) (hval : R.value = 1)
    (hsupp : ∀ q a, ¬Complete.okT T V c lam hs q.2 a → R.P.M q a = 0)
    (hperm : ∀ q (i : ℕ), IsSignedPerm
      (pvmObs (R.P.M q) fun a => bitSign ((Complete.encT T V c lam hs q.2 a).getD i false)))
    (hdiag : ∀ q (i : ℕ), i < (Sound.tdata c hc he lam n T V hs kg).lenR q.2.1 →
      (pvmObs (R.P.M q) fun a =>
        bitSign ((Complete.encT T V c lam hs q.2 a).getD i false)).IsDiag) :
    (outTV c hc he lam L P).HasPerfectZPC n :=
  (extends_presented h).doubled.hasPerfectZPC
    (Complete.hasPerfectZPC_tpresented hc2 hkg hacc U hV hn R hR hval hsupp hperm hdiag)

/-! ## The input's normal form verifier -/

/-- **The input's normal form verifier accepts as the input does.** -/
theorem acceptsAsInput_ofTNFVT (T : TailoredVerifier 7) (U0 : UniversalMachine) (n : ℕ) :
    AcceptsAsInput T (T.ofTNFVT U0) n := by
  intro xs ys a b hx hy
  have ex : toBits (ofBits (T.sampler.dim (2 ^ n)) xs) = xs := toBits_ofBits hx
  have ey : toBits (ofBits (T.sampler.dim (2 ^ n)) ys) = ys := toBits_ofBits hy
  have h := T.ofTNFVT_accepts_iff U0 (2 ^ n) (ofBits _ xs) (ofBits _ ys) a b
  rw [ex, ey] at h
  rw [h]
  simp only [TailoredGame.Accepts, TailoredGame.len, TailoredVerifier.tgame, ex, ey]

/-! ## The loss -/

/-- **A larger parameter in the loss is absorbed by the coefficient**: for `C ≥ 1`, `a ≥ 1`,
`δ(a, b, Cλ, n, ε) ≤ δ(a C^a, b, λ, n, ε)` when `λ n ≥ 1`. -/
theorem delta_mul_le {a b : ℝ} (ha : 1 ≤ a) (hb : 0 < b) {C lam n : ℕ} (hC : 1 ≤ C)
    (hl : 1 ≤ lam) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 ≤ ε) :
    delta a b (C * lam) n ε ≤ delta (a * (C : ℝ) ^ a) b lam n ε := by
  unfold delta
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hx : (1 : ℝ) ≤ (lam : ℝ) * n := by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hx0 : (0 : ℝ) ≤ (lam : ℝ) * n := by linarith
  have hCa : (1 : ℝ) ≤ (C : ℝ) ^ a := Real.one_le_rpow hC' (by linarith)
  have ha' : a ≤ a * (C : ℝ) ^ a := le_mul_of_one_le_right (by linarith) hCa
  push_cast
  rw [show (C : ℝ) * lam * n = C * (lam * n) by ring,
    Real.mul_rpow (by linarith) hx0]
  have heb : 0 ≤ ε ^ b := Real.rpow_nonneg hε b
  have h1 : (C : ℝ) ^ a * ((lam : ℝ) * n) ^ a ≤ (C : ℝ) ^ a * ((lam : ℝ) * n) ^ (a * (C : ℝ) ^ a) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ha') (by positivity)
  have h2 : ((C : ℝ) * (lam * n)) ^ (-b) ≤ ((lam : ℝ) * n) ^ (-b) := by
    apply Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by linarith)
    nlinarith
  have h3 : 0 ≤ ((lam : ℝ) * n) ^ (-b) := Real.rpow_nonneg hx0 _
  calc a * ((C : ℝ) ^ a * ((lam : ℝ) * n) ^ a * ε ^ b + ((C : ℝ) * (lam * n)) ^ (-b))
      ≤ a * ((C : ℝ) ^ a * ((lam : ℝ) * n) ^ (a * (C : ℝ) ^ a) * ε ^ b + ((lam : ℝ) * n) ^ (-b)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact add_le_add (mul_le_mul_of_nonneg_right h1 heb) h2
    _ ≤ a * (C : ℝ) ^ a * (((lam : ℝ) * n) ^ (a * (C : ℝ) ^ a) * ε ^ b + ((lam : ℝ) * n) ^ (-b)) := by
        have : 0 ≤ ((lam : ℝ) * n) ^ (a * (C : ℝ) ^ a) * ε ^ b :=
          mul_nonneg (Real.rpow_nonneg hx0 _) heb
        nlinarith

/-! ## Soundness in the contract's form -/

theorem lenOf_le_of_isBounded {T : TailoredVerifier 7} {lam m : ℕ} (hT : T.IsBounded lam)
    (hm : 2 ≤ m) (x : BitStr) (κ : Bool) : T.lenOf m x κ ≤ m ^ lam := by
  unfold TailoredVerifier.lenOf
  split_ifs with h
  · exact (hT.1 m hm).2.2.2.2 x κ _ h.choose_spec
  · exact Nat.zero_le _

/-- A `λ`-bounded tailored verifier's answers at index `m ≥ 2` have at most `m^(λ+1)` bits. -/
theorem maxLen_le_of_isBounded {T : TailoredVerifier 7} {lam m : ℕ} (hT : T.IsBounded lam)
    (hm : 2 ≤ m) : (T.tgame m).maxLen ≤ m ^ (lam + 1) := by
  apply Finset.sup_le
  intro x _
  have h1 := lenOf_le_of_isBounded hT hm (toBits x) false
  have h2 := lenOf_le_of_isBounded hT hm (toBits x) true
  change T.lenOf m (toBits x) false + T.lenOf m (toBits x) true ≤ _
  rw [pow_succ]
  nlinarith

/-- **Soundness of the output, in the contract's form**: for a `λ`-bounded input whose normal
form verifier is `Cλ`-bounded (`C ≥ 2`), when the output's programs meet the specification at
`Cλ`, `val*` of the output above `1 - ε` gives `val*` of the input at `2^n` at least
`1 - δ(a C^a, b, λ, n, ε)`, with `seven`'s `a` and `b`. -/
theorem soundness_contract (T : TailoredVerifier 7) (U0 : UniversalMachine) {C lam n : ℕ}
    (hC : 2 ≤ C) (hl : 1 ≤ lam) (hn : 1 ≤ n) (hT : T.IsBounded lam)
    (hV : (T.ofTNFVT U0).IsBounded (C * lam))
    {hs : (T.ofTNFVT U0).sampler.dim (2 ^ n) ≤ registerBits sevenConstant (C * lam) n}
    {kg : ∀ S : Finset (Fin (registerBits sevenConstant (C * lam) n)), CL.RegLinear 𝔽₂ S →
      List (Fin (registerBits sevenConstant (C * lam) n) → 𝔽₂)} {L P : Decider}
    (hkg : KerGens (registerBits sevenConstant (C * lam) n) kg)
    {hl' : 1 ≤ C * lam}
    (h : IntroSpec sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
      selfClockedUniversal (T.ofTNFVT U0) hl' hn
      (presented graph (Sound.H sevenConstant one_le_sevenConstant sevenConstant_spec.2.1
        (C * lam) n selfClockedUniversal (T.ofTNFVT U0))
        (Sound.tdata sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 (C * lam) n T
          (T.ofTNFVT U0) hs kg)) L P)
    {ε : ℝ} (hε : 0 < ε)
    (hv : 1 - ε < (outTV sevenConstant one_le_sevenConstant sevenConstant_spec.2.1 (C * lam)
      L P).valStar n) :
    1 - delta (CompiledSoundness.coefficient sevenConstant * (C : ℝ) ^
        CompiledSoundness.coefficient sevenConstant) CompiledSoundness.exponent lam n ε ≤
      T.valStar (2 ^ n) := by
  have h7 := soundness_seven T hkg (acceptsAsInput_ofTNFVT T U0 n) hV h hε hv
  have hm : 2 ≤ 2 ^ n := (two_le_exp_index_iff n).mpr hn
  have hlen : (T.tgame (2 ^ n)).maxLen ≤ (2 ^ n) ^ (C * lam) :=
    (maxLen_le_of_isBounded hT hm).trans (Nat.pow_le_pow_right (by omega) (by nlinarith))
  rw [Verifier.val_tensor, T.valStar_ofTNFVT U0 _ _ hlen] at h7
  have hd := delta_mul_le (CompiledSoundness.coefficient_one_le sevenConstant)
    CompiledSoundness.exponent_pos (by omega : 1 ≤ C) hl hn hε.le (n := n)
  linarith

end MIPRE.Tailored.Intro.Output

end
