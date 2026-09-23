/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundIsolate
import MIPRE.Background.LIDT.Simultaneous

/-!
# Soundness of answer reduction: the extracted low-degree measurements

Piece AR-5c of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`): the quantum soundness
of the seeded CL test (`LIDT.Simul.clSoundness`) applied to each per-seed strategy of
`MIPRE/Background/AnswerReduction/SoundIsolate`, giving for each copy and each oracle half a pair of
projective measurements of polynomials, one on each player's space (`GA1`, `GB1` for copies
`1`–`5`, `JA`, `JB` for the sixth copy), each consistent with the other player's point
measurements and with each other, at the error `δ_sim` of that seed's failure.

The errors are averaged over the seeds by Jensen's inequality (`sum_deltaSim_le`): `δ_sim` is
concave in the failure, so the average error is at most the error of the average failure, which
is at most `324` times the typed failure.
-/

noncomputable section

namespace MIPRE.LIDT.Simul

open Finset

/-- **Jensen's inequality for `ε ↦ ε^b`**, `0 ≤ b ≤ 1`, on a finite family with average at most
`E`. -/
theorem sum_rpow_le {ι : Type*} [Fintype ι] {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ε : ι → ℝ)
    (hε : ∀ i, 0 ≤ ε i) {E : ℝ} (hE : ∑ i, ε i ≤ Fintype.card ι * E) :
    ∑ i, ε i ^ b ≤ Fintype.card ι * E ^ b := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
    simp
  · set N : ℝ := (Fintype.card ι : ℝ) with hNdef
    have hN : 0 < N := by rw [hNdef]; exact_mod_cast h
    have hJ := (Real.concaveOn_rpow hb0 hb1).le_map_sum (t := univ) (w := fun _ => N⁻¹)
      (p := ε) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef, mul_inv_cancel₀ hN.ne'])
      (fun i _ => Set.mem_Ici.mpr (hε i))
    simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
    have havg : N⁻¹ * ∑ i, ε i ≤ E := by
      rw [inv_mul_le_iff₀ hN]
      exact hE
    have h0 : 0 ≤ N⁻¹ * ∑ i, ε i :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hε i)
    have hpow := Real.rpow_le_rpow h0 havg hb0
    calc ∑ i, ε i ^ b = N * (N⁻¹ * ∑ i, ε i ^ b) := by field_simp
      _ ≤ N * (N⁻¹ * ∑ i, ε i) ^ b := by gcongr
      _ ≤ N * E ^ b := by gcongr

/-- **`δ_sim` averages**: the average of `δ_sim` over a family of failures is at most `δ_sim` of
any bound on their average. -/
theorem sum_deltaSim_le {ι : Type*} [Fintype ι] (q m d r : ℕ) (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i)
    {E : ℝ} (hE : ∑ i, ε i ≤ Fintype.card ι * E) :
    ∑ i, deltaSim q m d r (ε i) ≤ Fintype.card ι * deltaSim q m d r E := by
  have hb0 := clB_pos
  have hb1 := clB_lt_one
  have h := sum_rpow_le hb0.le hb1.le ε hε hE
  have hA : 0 ≤ simA * ((d * m * r : ℕ) : ℝ) ^ simA := by
    have := forty_le_simA
    positivity
  simp only [deltaSim]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have := mul_le_mul_of_nonneg_left h hA
  nlinarith

end MIPRE.LIDT.Simul

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT SAT Pcp

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ) (T : TensorProductStrategy (typedGame V n P hk S S' check B))

/-- The failure of the per-seed strategy of copy `i ≤ 5` at role `r` and oracle half `y`. -/
def eps1 (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  1 - (copyStrategy V n P hk S S' check B T r i y).value

/-- The failure of the sixth copy's per-seed strategy at oracle half `y`. -/
def eps6 (y : Fin (V.sampler.dim n) → 𝔽₂) : ℝ :=
  1 - (copyStrategy6 V n P hk S S' check B T y).value

theorem eps1_nonneg (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂) :
    0 ≤ eps1 V n P hk S S' check B T r i y :=
  sub_nonneg.mpr (TensorProductStrategy.value_le_one _)

theorem eps6_nonneg (y : Fin (V.sampler.dim n) → 𝔽₂) : 0 ≤ eps6 V n P hk S S' check B T y :=
  sub_nonneg.mpr (TensorProductStrategy.value_le_one _)

/-- The polynomial measurements of copy `i ≤ 5`: tuples of one polynomial in `m` variables. -/
abbrev Poly1 (P : PcpParams) (hk : 1 ≤ P.k) :=
  Fin 1 → LIDT.LowIndDegPoly (F := Fq P hk) (m := P.m) (d := dPcp)

/-- The polynomial measurements of the sixth copy: `m' + 6` polynomials in `m'` variables. -/
abbrev Poly6 (P : PcpParams) (hk : 1 ≤ P.k) :=
  Fin (P.m' + 6) → LIDT.LowIndDegPoly (F := Fq P hk) (m := P.m') (d := dPcp)

omit [NeZero P.m] in
theorem card_fq : Fintype.card (Fq P hk) = 2 ^ P.k := (shoupBinField P.k hk).card_carrier

omit [NeZero P.m] in
theorem one_le_dPcp : 1 ≤ dPcp := by
  show 1 ≤ PcpParams.d
  simp [PcpParams.d]

theorem exists_ext1 (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂) :
    ∃ GA : ProjectiveMeasurement Unit (Poly1 P hk) (Matrix (Fin T.dA) (Fin T.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (Poly1 P hk) (Matrix (Fin T.dB) (Fin T.dB) ℂ),
      inconsistency (uniform (Fin P.m → Fq P hk)) T.ψ
          (Simul.tuplePOVMA hm (copyStrategy V n P hk S S' check B T r i y))
          (Simul.evalTuplePOVM GB)
          ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (eps1 V n P hk S S' check B T r i y)
        ∧ inconsistency (uniform (Fin P.m → Fq P hk)) T.ψ (Simul.evalTuplePOVM GA)
          (Simul.tuplePOVMB hm (copyStrategy V n P hk S S' check B T r i y))
          ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (eps1 V n P hk S S' check B T r i y)
        ∧ inconsistency (uniform Unit) T.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1
            (eps1 V n P hk S S' check B T r i y) :=
  Simul.clSoundness (card_fq P hk) hm one_le_dPcp le_rfl
    (copyStrategy V n P hk S S' check B T r i y) _ (eps1_nonneg V n P hk S S' check B T r i y)
    (by rw [eps1]; linarith)

theorem exists_ext6 (y : Fin (V.sampler.dim n) → 𝔽₂) :
    ∃ GA : ProjectiveMeasurement Unit (Poly6 P hk) (Matrix (Fin T.dA) (Fin T.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (Poly6 P hk) (Matrix (Fin T.dB) (Fin T.dB) ℂ),
      inconsistency (uniform (Fin P.m' → Fq P hk)) T.ψ
          (Simul.tuplePOVMA hm' (copyStrategy6 V n P hk S S' check B T y))
          (Simul.evalTuplePOVM GB)
          ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
            (eps6 V n P hk S S' check B T y)
        ∧ inconsistency (uniform (Fin P.m' → Fq P hk)) T.ψ (Simul.evalTuplePOVM GA)
          (Simul.tuplePOVMB hm' (copyStrategy6 V n P hk S S' check B T y))
          ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
            (eps6 V n P hk S S' check B T y)
        ∧ inconsistency (uniform Unit) T.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
            (eps6 V n P hk S S' check B T y) :=
  Simul.clSoundness (card_fq P hk) hm' one_le_dPcp (by omega)
    (copyStrategy6 V n P hk S S' check B T y) _ (eps6_nonneg V n P hk S S' check B T y)
    (by rw [eps6]; linarith)

/-- **Alice's polynomial measurement** of copy `i ≤ 5` at role `r` and oracle half `y`. -/
def GA1 (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂) :
    ProjectiveMeasurement Unit (Poly1 P hk) (Matrix (Fin T.dA) (Fin T.dA) ℂ) :=
  (exists_ext1 V n P hk S S' check B T r i y).choose

/-- **Bob's polynomial measurement** of copy `i ≤ 5` at role `r` and oracle half `y`. -/
def GB1 (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂) :
    ProjectiveMeasurement Unit (Poly1 P hk) (Matrix (Fin T.dB) (Fin T.dB) ℂ) :=
  (exists_ext1 V n P hk S S' check B T r i y).choose_spec.choose

/-- **Alice's simultaneous polynomial measurement** of the sixth copy at oracle half `y`. -/
def JA (y : Fin (V.sampler.dim n) → 𝔽₂) :
    ProjectiveMeasurement Unit (Poly6 P hk) (Matrix (Fin T.dA) (Fin T.dA) ℂ) :=
  (exists_ext6 V n P hk S S' check B T y).choose

/-- **Bob's simultaneous polynomial measurement** of the sixth copy at oracle half `y`. -/
def JB (y : Fin (V.sampler.dim n) → 𝔽₂) :
    ProjectiveMeasurement Unit (Poly6 P hk) (Matrix (Fin T.dB) (Fin T.dB) ℂ) :=
  (exists_ext6 V n P hk S S' check B T y).choose_spec.choose

/-- The three conclusions for copies `1`–`5`. -/
theorem ext1_spec (r : Role) (i : Fin 5) (y : Fin (V.sampler.dim n) → 𝔽₂) :
    inconsistency (uniform (Fin P.m → Fq P hk)) T.ψ
        (Simul.tuplePOVMA hm (copyStrategy V n P hk S S' check B T r i y))
        (Simul.evalTuplePOVM (GB1 V n P hk S S' check B T r i y))
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (eps1 V n P hk S S' check B T r i y)
      ∧ inconsistency (uniform (Fin P.m → Fq P hk)) T.ψ
        (Simul.evalTuplePOVM (GA1 V n P hk S S' check B T r i y))
        (Simul.tuplePOVMB hm (copyStrategy V n P hk S S' check B T r i y))
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (eps1 V n P hk S S' check B T r i y)
      ∧ inconsistency (uniform Unit) T.ψ (fun _ => (GA1 V n P hk S S' check B T r i y).toPOVM ())
          (fun _ => (GB1 V n P hk S S' check B T r i y).toPOVM ())
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1
          (eps1 V n P hk S S' check B T r i y) :=
  (exists_ext1 V n P hk S S' check B T r i y).choose_spec.choose_spec

/-- The three conclusions for the sixth copy. -/
theorem ext6_spec (y : Fin (V.sampler.dim n) → 𝔽₂) :
    inconsistency (uniform (Fin P.m' → Fq P hk)) T.ψ
        (Simul.tuplePOVMA hm' (copyStrategy6 V n P hk S S' check B T y))
        (Simul.evalTuplePOVM (JB V n P hk S S' check B T y))
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T y)
      ∧ inconsistency (uniform (Fin P.m' → Fq P hk)) T.ψ
        (Simul.evalTuplePOVM (JA V n P hk S S' check B T y))
        (Simul.tuplePOVMB hm' (copyStrategy6 V n P hk S S' check B T y))
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T y)
      ∧ inconsistency (uniform Unit) T.ψ (fun _ => (JA V n P hk S S' check B T y).toPOVM ())
          (fun _ => (JB V n P hk S S' check B T y).toPOVM ())
        ≤ Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
          (eps6 V n P hk S S' check B T y) :=
  (exists_ext6 V n P hk S S' check B T y).choose_spec.choose_spec

/-- **The averaged error of copies `1`–`5`**, at a role pair where the copy is tested. -/
theorem sum_deltaSim1_le {r : Role} {i : Fin 5} (hr : LDStep r i) :
    ∑ x₀, Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1
        (eps1 V n P hk S S' check B T r i ((roleFamily (V.sampler.cl n) r).eval x₀))
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) *
        Simul.deltaSim (Fintype.card (Fq P hk)) P.m dPcp 1 (324 * (1 - T.value)) :=
  Simul.sum_deltaSim_le _ _ _ _ _ (fun _ => eps1_nonneg V n P hk S S' check B T _ _ _)
    (sum_one_sub_value_copyStrategy_le V n P hk S S' check B T hr)

/-- **The averaged error of the sixth copy.** -/
theorem sum_deltaSim6_le :
    ∑ x₀, Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6)
        (eps6 V n P hk S S' check B T ((roleFamily (V.sampler.cl n) .oracle).eval x₀))
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) *
        Simul.deltaSim (Fintype.card (Fq P hk)) P.m' dPcp (P.m' + 6) (324 * (1 - T.value)) :=
  Simul.sum_deltaSim_le _ _ _ _ _ (fun _ => eps6_nonneg V n P hk S S' check B T _)
    (sum_one_sub_value_copyStrategy6_le V n P hk S S' check B T)

end MIPRE.AnswerReduction

end
