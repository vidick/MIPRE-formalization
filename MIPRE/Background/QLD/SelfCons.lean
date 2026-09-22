/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.ChainAssembly

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

section Generic

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in
/-- **Lemma `lem:qld-povm-to-obs` in the state-norm form the chain's conclusion takes.** A
weighted sum of measurement elements is close to the corresponding weighted sum of the other
family's, at the cost of a factor the size of the outcome set: the triangle inequality over the
outcomes, then Cauchy--Schwarz against the constant one. -/
theorem snorm_sq_obs_sub_le {Λ : Type*} [Fintype Λ] (w : N → ℂ) (α : Λ → ℂ)
    (hα : ∀ a, ‖α a‖ ≤ 1) (A B : Λ → Matrix N N ℂ) :
    snorm w ((∑ a, α a • A a) - ∑ a, α a • B a) ^ 2
      ≤ (Fintype.card Λ : ℝ) * ∑ a, snorm w (A a - B a) ^ 2 := by
  classical
  have hsub : (∑ a, α a • A a) - ∑ a, α a • B a = ∑ a, α a • (A a - B a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => (smul_sub _ _ _).symm
  have htri : snorm w ((∑ a, α a • A a) - ∑ a, α a • B a) ≤ ∑ a, snorm w (A a - B a) := by
    rw [hsub]
    refine (snorm_sum_le w univ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [snorm_smul]
    calc ‖α a‖ * snorm w (A a - B a) ≤ 1 * snorm w (A a - B a) :=
          mul_le_mul_of_nonneg_right (hα a) (snorm_nonneg w _)
      _ = snorm w (A a - B a) := one_mul _
  calc snorm w ((∑ a, α a • A a) - ∑ a, α a • B a) ^ 2
      ≤ (∑ a, snorm w (A a - B a)) ^ 2 := pow_le_pow_left₀ (snorm_nonneg w _) htri 2
    _ ≤ (Fintype.card Λ : ℝ) * ∑ a, snorm w (A a - B a) ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ fun a => snorm_nonneg w _

omit [Fintype N] [DecidableEq N] in
/-- **Regrouping a weighted sum by the fibres of a relabelling.** -/
theorem sum_fibre_smul {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
    (f : Λ → Λ') (α : Λ' → ℂ) (X : Λ → Matrix N N ℂ) :
    (∑ c : Λ', α c • ∑ a ∈ univ.filter fun a => f a = c, X a)
      = ∑ a : Λ, α (f a) • X a := by
  classical
  rw [← Finset.sum_fiberwise (univ : Finset Λ) f fun a => α (f a) • X a]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2]

end Generic

section Swap

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] in
/-- The swap carries a finite sum of vectors. -/
theorem swapVec_sum {ι : Type*} (s : Finset ι) (f : ι → dA × dB → ℂ) :
    swapVec (∑ i ∈ s, f i) = ∑ i ∈ s, swapVec (f i) := by
  funext p
  simp only [swapVec, Finset.sum_apply]

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [DecidableEq dA] [DecidableEq dB] in
/-- **A sum of Kronecker products applied to the swapped state** is the swap of the exchanged
sum applied to the state. -/
theorem mulVec_kron_sum_swapVec {ι : Type*} (s : Finset ι) (X : ι → Matrix dB dB ℂ)
    (Y : ι → Matrix dA dA ℂ) (ψ : dA × dB → ℂ) :
    (∑ i ∈ s, (X i ⊗ₖ Y i)) *ᵥ swapVec ψ = swapVec ((∑ i ∈ s, (Y i ⊗ₖ X i)) *ᵥ ψ) := by
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec, swapVec_sum]
  exact Finset.sum_congr rfl fun i _ => mulVec_kronecker_swapVec _ _ _

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m]
  [DecidableEq dB] in
/-- **The swap exchanges the two parties in the chain's conclusion.** -/
theorem snorm_swapVec_aOp_sub_kron_sum {ι : Type*} (s : Finset ι) (ψ : dA × dB → ℂ)
    (Z : Matrix dB dB ℂ) (X : ι → Matrix dB dB ℂ) (Y : ι → Matrix dA dA ℂ) :
    snorm (swapVec ψ) ((aOp Z : Matrix (dB × dA) (dB × dA) ℂ) - ∑ i ∈ s, (X i ⊗ₖ Y i))
      = snorm ψ ((bOp Z : Matrix (dA × dB) (dA × dB) ℂ) - ∑ i ∈ s, (Y i ⊗ₖ X i)) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, mulVec_kron_sum_swapVec,
    show (aOp Z : Matrix (dB × dA) (dB × dA) ℂ) = Z ⊗ₖ (1 : Matrix dA dA ℂ) from rfl,
    show (bOp Z : Matrix (dA × dB) (dA × dB) ℂ) = (1 : Matrix dA dA ℂ) ⊗ₖ Z from rfl,
    mulVec_kronecker_swapVec, ← swapVec_sub, norm_swapVec]

end Swap

section Physical

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

set_option synthInstance.maxSize 1000

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **Alice's exact Pauli observable**, the signed sum of her measurement's elements. -/
def aliceWTilde (W : Bas) (e : F) (v : Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.toFirst.wTildeAt W e v

/-- **Bob's.** -/
def bobWTilde (W : Bas) (e : F) (v : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.toSecond.wTildeAt W e v

set_option maxHeartbeats 4000000 in
/-- **The chain's endpoint does not care which party's pair carries the label.** Reindexing by
the exchange of the two pairs is a bijection of the index set (`swap_mem_coupledIdx`), and it
turns the one reading into the other. -/
theorem endOp_swap_sum (W : Bas) (v : Anc F m) (a : F) :
    (∑ q ∈ coupledIdx (F := F) (m := m) (d := d) v a,
        (M.toFirst.chainOp W q.2) ⊗ₖ (M.toSecond.chainOp W q.1))
      = M.endOp W v a :=
  Finset.sum_equiv (Equiv.prodComm (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m))
    (fun _ => swap_mem_coupledIdx.symm) fun _ _ => rfl

set_option maxHeartbeats 4000000 in
/-- **Display `eq:qld-pulling-cons` for Alice**, with the average over the sampled point dropped:
neither side depends on it. -/
theorem sum_snorm_sq_aliceMTilde_endOp_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, snorm M.physVec
        ((aOp (M.aliceMTilde W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m))
            ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ) - M.endOp W v a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  have h := M.sum_uniform_snorm_sq_mTildeAnc_endOp_le (hm := hm) hψ hfail hprojA hprojB hd W v
  rwa [← Finset.sum_mul, sum_uniform_eq_one, one_mul] at h

set_option maxHeartbeats 4000000 in
/-- **The same at the mirror, read on the physical state.** The mirror of a `MirrorSimul` is a
`MirrorSimul`, its physical state is this one with the parties written in the other order, and
its endpoint is this one read from the other side. -/
theorem snorm_endOp_bobMTilde_eq (W : Bas) (v : Anc F m) (a : F) :
    snorm M.mirror.physVec (aOp (M.mirror.aliceMTilde W v a) - M.mirror.endOp W v a)
      = snorm M.physVec (M.endOp W v a
          - (bOp (M.bobMTilde W v a)
            : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
                × (((dB × Anc F m) × M.Eb) × Anc F m))
              ((((dA × Anc F m) × M.Ea) × Anc F m)
                × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)) := by
  have h1 := snorm_swapVec_aOp_sub_kron_sum (coupledIdx (F := F) (m := m) (d := d) v a)
    M.physVec (M.bobMTilde W v a) (fun q => M.toSecond.chainOp W q.1)
    (fun q => M.toFirst.chainOp W q.2)
  have h2 := congrArg (fun X => snorm M.physVec ((bOp (M.bobMTilde W v a)
      : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m))
        ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ) - X)) (M.endOp_swap_sum W v a)
  rw [show M.mirror.physVec = swapVec M.physVec from M.mirror_physVec]
  exact (h1.trans h2).trans (snorm_sub_comm M.physVec _ _)

set_option maxHeartbeats 4000000 in
/-- **Display `eq:qld-pulling-cons` for Bob.** -/
theorem sum_snorm_sq_endOp_bobMTilde_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, snorm M.physVec (M.endOp W v a
        - (bOp (M.bobMTilde W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m))
            ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  have h := M.mirror.sum_snorm_sq_aliceMTilde_endOp_le (hm := hm) (swapVec_unit hψ)
    (povmValue_swapped_le hfail) hprojB hprojA hd W v
  refine le_trans (le_of_eq ?_) h
  exact (Finset.sum_congr rfl fun a _ =>
    congrArg (· ^ 2) (M.snorm_endOp_bobMTilde_eq W v a)).symm

set_option maxHeartbeats 4000000 in
/-- **Lemma `lem:qld-pauli-selfcons` at the level of the two exact Pauli measurements**: they
agree on the physical state, at four times what each costs to reach the chain's endpoint. -/
theorem sum_selfConsGap_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ a : F, M.selfConsGap W v a)
      ≤ 4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F)) := by
  have h := sum_xSqNorm_le_of_endOp M W v
    (M.sum_snorm_sq_aliceMTilde_endOp_le (hm := hm) hψ hfail hprojA hprojB hd W v)
    (M.sum_snorm_sq_endOp_bobMTilde_le (hm := hm) hψ hfail hprojA hprojB hd W v)
  have hgap : (∑ a : F, M.selfConsGap W v a)
      = ∑ a : F, xSqNorm M.physVec (M.aliceMTilde W v a) (M.bobMTilde W v a) := rfl
  rw [hgap]
  linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma `lem:qld-pauli-selfcons`**: the two parties' exact Pauli *observables* agree.

The passage from the measurements to the observable is the paper's, and it is not
Lemma `lem:qld-povm-to-obs` applied to the whole outcome set --- that would cost a factor the
size of the field. The family is coarse-grained first, along the character the observable reads
(`sum_xSqNorm_fibre_le`, which is free for projective families), and only the resulting
*two*-outcome family is turned into an observable. The factor is therefore two. -/
theorem snorm_sq_wTilde_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (e : F) (v : Anc F m) :
    snorm M.physVec ((aOp (M.aliceWTilde W e v)
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
        - bOp (M.bobWTilde W e v)) ^ 2
      ≤ 2 * (4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F))) := by
  classical
  have hA : (aOp (M.aliceWTilde W e v)
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
      = ∑ c : ZMod 2, sgn c • aOp (∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.aliceMTilde W v a) := by
    have h1 : (∑ c : ZMod 2, sgn c • ∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.aliceMTilde W v a)
        = M.aliceWTilde W e v :=
      sum_fibre_smul (fun a : F => Algebra.trace (ZMod 2) F (e * a)) sgn (M.aliceMTilde W v)
    rw [← h1, aOp_sum]
    exact Finset.sum_congr rfl fun c _ => aOp_smul _ _
  have hB : (bOp (M.bobWTilde W e v)
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m))
          ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
      = ∑ c : ZMod 2, sgn c • bOp (∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.bobMTilde W v a) := by
    have h1 : (∑ c : ZMod 2, sgn c • ∑ a ∈ univ.filter
          fun a : F => Algebra.trace (ZMod 2) F (e * a) = c, M.bobMTilde W v a)
        = M.bobWTilde W e v :=
      sum_fibre_smul (fun a : F => Algebra.trace (ZMod 2) F (e * a)) sgn (M.bobMTilde W v)
    rw [← h1, bOp_sum]
    exact Finset.sum_congr rfl fun c _ => bOp_smul _ _
  have hcoarse := sum_xSqNorm_fibre_le (ψ := M.physVec) M.physVec_unit
    (M.toFirst.isPVM_mTildeAnc W v) (M.toSecond.isPVM_mTildeAnc W v)
    fun a : F => Algebra.trace (ZMod 2) F (e * a)
  have hgap := M.sum_selfConsGap_le (hm := hm) hψ hfail hprojA hprojB hd W v
  have hfib : (∑ c : ZMod 2, snorm M.physVec
        ((aOp (∑ a ∈ univ.filter fun a : F => Algebra.trace (ZMod 2) F (e * a) = c,
            M.aliceMTilde W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m))
            ((((dA × Anc F m) × M.Ea) × Anc F m)
              × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ)
          - bOp (∑ a ∈ univ.filter fun a : F => Algebra.trace (ZMod 2) F (e * a) = c,
              M.bobMTilde W v a)) ^ 2)
      ≤ 4 * (9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F)) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ =>
      (xSqNorm_eq_snorm_sq M.physVec _ _).symm)) ?_
    exact le_trans hcoarse hgap
  rw [hA, hB]
  refine le_trans (snorm_sq_obs_sub_le M.physVec sgn (fun c => le_of_eq (norm_sgn c)) _ _) ?_
  rw [show (Fintype.card (ZMod 2) : ℝ) = 2 from by norm_num]
  exact mul_le_mul_of_nonneg_left hfib (by norm_num)

end MirrorSimul

end Physical

end MIPRE.QLD
