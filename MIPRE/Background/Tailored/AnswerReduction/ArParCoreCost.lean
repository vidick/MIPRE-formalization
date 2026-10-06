/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.ArParCore
public import MIPRE.Background.AnswerReduction.ParamsCost

@[expose] public section

/-!
# The running time of the parameter program

Slice P4i of `planning/aldous-lyons-track.md`: the parameter program `arParCore κ` runs within
`(c (W + 1)^m X^e)^{μ + 1}` for every `W ≥ (λn + 1)^μ + σ + λ + n` (`arParCore_time`), the
routine's `ArRoutine.ParTime`.

Its loops run as long as the values they write: `Q, μ, σ` (the budgets' routine, by
`MIPRE.AnswerReduction.budCore_time`), `r`, `s` and `2^j`. All of them are dominated
(`vals_pdom`): `◇ = (μ + 2)(Q + 4)` and `K = E₁ (μ + 1)(oW + Q + 4)` are products of quantities
below `W` and below `μ + 1`, which the exponent `μ + 1` of the bound absorbs (`PDom.ofLeK`);
`T = 2^K` is only written in binary, of `K + 1` bits; `r ≤ c (|T| + |σ'| + 1)` and
`s ≤ P(|n| + |T| + Q + σ')` by the window describer's bounds; and `2^j ≤ 2m + 1`. The sizes of
the data between the stages are dominated as the outputs of runs (`PRuns.size_le`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost Cost.PolyTimeFun MIPRE.CL MIPRE.SAT MIPRE.Pipeline CL.Detyping.Program

namespace ArPar

/-- **The running time of a loop stage**: the data and the number written dominated. -/
theorem pushU_time (g : PolyTimeFun Data ℕ) (c m e c' m' e' : ℕ) : ∃ C M E, ∀ {W X K : ℕ}
    (x : Data), 1 ≤ X → PDom W X K c m e x.size → PDom W X K c' m' e' (g x) →
    PRuns W X K C M E (pushU g) x (.cons (encode (unary (g x))) x) := by
  obtain ⟨cu, mu, eu, hu⟩ := PRuns.toUnary c' m' e'
  obtain ⟨cs, ms, es, hs⟩ := PRuns.stage (ap₂ treePair (encoded.comp g) (PolyTimeFun.id Data))
    AnswerReduction.ParRoutine.postKeep c m e cu mu eu
  exact ⟨_, _, _, fun {W X K} x hX hx hv => by
    have h := hs (W := W) (K := K) toUnaryProg_closed x (encode (g x)) x _ hX (by simp) hx
      (hu (W := W) (K := K) (g x) hX hv)
    simp only [AnswerReduction.ParRoutine.postKeep, ap₂_apply, treePair_apply, fst_apply,
      snd_apply] at h
    exact h⟩

theorem two_pow_size_le (m : ℕ) : 2 ^ Nat.size m ≤ 2 * m + 1 := by
  rcases h : Nat.size m with _ | k
  · simp
  · have : 2 ^ k ≤ m := Nat.lt_size.mp (by omega)
    rw [pow_succ]
    omega

theorem size_le_self (m : ℕ) : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self

/-- **The values the loops write are dominated.** -/
theorem vals_pdom (κ : Params.ArConsts) : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ), 1 ≤ X →
    AnswerReduction.arg lam mu sigma n ≤ W →
    PDom W X mu c m e (Params.pQ lam mu n + mu + sigma + Params.pR κ lam mu sigma n +
      Params.pS κ lam mu sigma n + 2 ^ Params.pJ κ lam mu sigma n) := by
  obtain ⟨cr, hr⟩ := windowDescriber.r₀_le
  obtain ⟨P, hP⟩ := windowDescriber.s₀_le
  exact ⟨_, _, _, fun {W X} lam mu sigma n hX hW => by
    simp only [AnswerReduction.arg] at hW
    -- the atoms
    have hQW : Params.pQ lam mu n ≤ W := by show (lam * n + 1) ^ mu ≤ W; omega
    have eDm : Params.pDm lam mu n = (mu + 1 + 1) * (Params.pQ lam mu n + 4) := rfl
    have eK : Params.pK κ lam mu n =
        κ.E₁ * (mu + 1) * (3 * Params.pQ lam mu n + 3 * Params.pDm lam mu n + 10) := by
      simp only [Params.pK, Params.pOW, Params.pEll]
      ring
    have eSig : Params.pSig κ lam mu sigma n =
        κ.c₀ + 5 * sigma + 4 * (Params.pQ lam mu n + Params.pDm lam mu n) + 8 := rfl
    have eT : Nat.size (Params.pT κ lam mu n) = Params.pK κ lam mu n + 1 := Nat.size_pow
    have hsS := size_le_self (Params.pSig κ lam mu sigma n)
    have hsn := size_le_self n
    have eR : Params.pR κ lam mu sigma n ≤
        cr * (Params.pK κ lam mu n + 1 + Params.pSig κ lam mu sigma n + 1) := by
      refine (hr _ _).trans (Nat.mul_le_mul_left _ ?_)
      rw [eT]
      omega
    have eS : Params.pS κ lam mu sigma n ≤ P.eval (n + Params.pK κ lam mu n + 1 +
        Params.pQ lam mu n + Params.pSig κ lam mu sigma n) := by
      refine (hP _ _ _ _).trans (polynomial_eval_mono _ ?_)
      rw [eT]
      omega
    have eM : (Params.pL κ lam mu sigma n).m = 4 * Params.pQ lam mu n +
        3 * Params.pDm lam mu n + 3 * Params.pR κ lam mu sigma n + Params.pS κ lam mu sigma n +
          15 := by
      simp only [PcpDims.m, PcpDims.nIn, PcpDims.oW, Params.pL_ℓ, Params.pL_dm, Params.pL_r,
        Params.pL_s, Params.pEll]
      omega
    have e2J := two_pow_size_le (Params.pL κ lam mu sigma n).m
    -- the bounds
    have hQ : PDom W X mu 1 1 0 (Params.pQ lam mu n) := PDom.ofLeW hQW
    have hσ : PDom W X mu 1 1 0 sigma := PDom.ofLeW (by omega)
    have hn : PDom W X mu 1 1 0 n := PDom.ofLeW (by omega)
    have hμ : PDom W X mu 2 0 0 (mu + 1) := PDom.ofLeK le_rfl
    have hDm := ((hμ.add hX (PDom.const 1)).mul (hQ.add hX (PDom.const 4))).of_le
      (le_of_eq eDm)
    have hK := (((PDom.const κ.E₁).mul hμ).mul ((((PDom.const 3).mul hQ).add hX
      ((PDom.const 3).mul hDm)).add hX (PDom.const 10))).of_le (le_of_eq eK)
    have hS' := ((((PDom.const κ.c₀).add hX ((PDom.const 5).mul hσ)).add hX ((PDom.const 4).mul
      (hQ.add hX hDm))).add hX (PDom.const 8)).of_le (le_of_eq eSig)
    have hR := ((PDom.const cr).mul ((((hK.add hX (PDom.const 1)).add hX hS').add hX
      (PDom.const 1)))).of_le eR
    have hS := ((((((hn.add hX hK).add hX (PDom.const 1)).add hX hQ).add hX hS').poly hX P)).of_le
      eS
    have hM := (((((((PDom.const 4).mul hQ).add hX ((PDom.const 3).mul hDm)).add hX
      ((PDom.const 3).mul hR)).add hX hS).add hX (PDom.const 15)))
    have h2J := (((PDom.const 2).mul hM).add hX (PDom.const 1)).of_le
      (show 2 ^ Params.pJ κ lam mu sigma n ≤ 2 * (4 * Params.pQ lam mu n +
        3 * Params.pDm lam mu n + 3 * Params.pR κ lam mu sigma n + Params.pS κ lam mu sigma n +
          15) + 1 by rw [← eM]; exact e2J)
    exact (((((hQ.add hX (hμ.of_le (Nat.le_succ mu))).add hX hσ).add hX hR).add hX hS).add hX
      h2J)⟩

end ArPar

open ArPar AnswerReduction.ParRoutine in
/-- **The running time of the parameter program**: within `(c (W + 1)^m X^e)^{μ + 1}` for every
`W ≥ (λn + 1)^μ + σ + λ + n`. -/
theorem arParCore_time (κ : Params.ArConsts) : ∃ c m e, ∀ {W X : ℕ} (lam mu sigma n : ℕ),
    1 ≤ X → AnswerReduction.arg lam mu sigma n ≤ W →
    PRuns W X mu c m e (arParCore κ) (encode (((lam, mu, sigma), n) : (ℕ × ℕ × ℕ) × ℕ))
      (encode (arParams (Params.pTw κ lam mu sigma n) (Params.pJ κ lam mu sigma n) Params.pD
        (Params.pL κ lam mu sigma n) (Params.pExtra κ lam mu sigma n))) := by
  obtain ⟨cb, mb, eb, hb⟩ := AnswerReduction.budCore_time
  obtain ⟨cA, mA, eA, hA⟩ := PRuns.stage (ap₂ treePair (PolyTimeFun.id Data)
    (PolyTimeFun.id Data)) postKeep AnswerReduction.linC 1 0 cb mb eb
  obtain ⟨cv, mv, ev, hv⟩ := vals_pdom κ
  obtain ⟨c2, m2, e2, h2⟩ := pushU_time gQ cA mA eA cv mv ev
  obtain ⟨c3, m3, e3, h3⟩ := pushU_time gMu c2 m2 e2 cv mv ev
  obtain ⟨c4, m4, e4, h4⟩ := pushU_time gSig c3 m3 e3 cv mv ev
  obtain ⟨c5, m5, e5, h5⟩ := PRuns.ptf (f6 κ) c4 m4 e4
  obtain ⟨c6, m6, e6, h6⟩ := pushU_time gR c5 m5 e5 cv mv ev
  obtain ⟨c7, m7, e7, h7⟩ := pushU_time gS c6 m6 e6 cv mv ev
  obtain ⟨c8, m8, e8, h8⟩ := pushU_time g2J c7 m7 e7 cv mv ev
  obtain ⟨c9, m9, e9, h9⟩ := PRuns.ptf (f10 κ) c8 m8 e8
  exact ⟨_, _, _, fun {W X} lam mu sigma n hX hW => by
    have V := hv lam mu sigma n hX hW (W := W)
    have hW' := hW
    simp only [AnswerReduction.arg] at hW'
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four mu
    have es := esize_nat_le_four sigma
    have en := esize_nat_le_four n
    have hX0 := AnswerReduction.size_X0 lam mu sigma n
    have h2p := Nat.zero_le (2 ^ Params.pJ κ lam mu sigma n)
    have S1 := hA (W := W) (K := mu) budCore_closed (x0 lam mu sigma n) (x0 lam mu sigma n)
      (x0 lam mu sigma n) _ hX (by simp)
      (AnswerReduction.pdLin hX (by simp only [x0, encode_prod] at hX0 ⊢; omega))
      (hb (W := W) lam mu sigma n hX (by show (lam * n + 1) ^ mu ≤ W; omega) (by omega)
        (by omega) (by omega))
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S1
    have S2 := h2 (W := W) (K := mu) (x1 lam mu sigma n) hX S1.size_le
      (V.of_le (by rw [gQ_apply]; omega))
    rw [gQ_apply] at S2
    have S3 := h3 (W := W) (K := mu) (x2 lam mu sigma n) hX S2.size_le
      (V.of_le (by rw [gMu_apply]; omega))
    rw [gMu_apply] at S3
    have S4 := h4 (W := W) (K := mu) (x3 lam mu sigma n) hX S3.size_le
      (V.of_le (by rw [gSig_apply]; omega))
    rw [gSig_apply] at S4
    have S5 := h5 (W := W) (K := mu) (x4 lam mu sigma n) hX
      (by simpa only [esize_data] using S4.size_le)
    rw [encode_data, f6_apply] at S5
    have S6 := h6 (W := W) (K := mu) (y6 κ lam mu sigma n) hX S5.size_le
      (V.of_le (by rw [gR_apply]; omega))
    rw [gR_apply] at S6
    have S7 := h7 (W := W) (K := mu) (y7 κ lam mu sigma n) hX S6.size_le
      (V.of_le (by rw [gS_apply]; omega))
    rw [gS_apply] at S7
    have S8 := h8 (W := W) (K := mu) (y8 κ lam mu sigma n) hX S7.size_le
      (V.of_le (by rw [g2J_apply]; omega))
    rw [g2J_apply] at S8
    have S9 := h9 (W := W) (K := mu) (y9 κ lam mu sigma n) hX
      (by simpa only [esize_data] using S8.size_le)
    rw [encode_data, f10_apply] at S9
    have c := fun g => pushU_closed g
    exact PRuns.seq hX (tailProg_closed κ) S1 <|
      PRuns.seq hX (seqProg_closed (c _) <| seqProg_closed (c _) <|
        seqProg_closed (PolyTimeFun.closed _) <| seqProg_closed (c _) <| seqProg_closed (c _) <|
        seqProg_closed (c _) (PolyTimeFun.closed _)) S2 <|
      PRuns.seq hX (seqProg_closed (c _) <| seqProg_closed (PolyTimeFun.closed _) <|
        seqProg_closed (c _) <| seqProg_closed (c _) <| seqProg_closed (c _)
          (PolyTimeFun.closed _)) S3 <|
      PRuns.seq hX (seqProg_closed (PolyTimeFun.closed _) <| seqProg_closed (c _) <|
        seqProg_closed (c _) <| seqProg_closed (c _) (PolyTimeFun.closed _)) S4 <|
      PRuns.seq hX (seqProg_closed (c _) <| seqProg_closed (c _) <| seqProg_closed (c _)
        (PolyTimeFun.closed _)) S5 <|
      PRuns.seq hX (seqProg_closed (c _) <| seqProg_closed (c _) (PolyTimeFun.closed _)) S6 <|
      PRuns.seq hX (seqProg_closed (c _) (PolyTimeFun.closed _)) S7 <|
      PRuns.seq hX (PolyTimeFun.closed _) S8 S9⟩

end MIPRE.Tailored.AnsRed.Typed

end

end
