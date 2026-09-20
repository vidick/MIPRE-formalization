/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Combine

/-!
# The padded line measurement's consistency

Blueprint `lem:qld-padded-lines`, the analytic half. `Combine.lean` built the measurement; this file
proves it consistent with the padded point measurement on the padded line-point law.

The paper chains three Cauchy--Schwarz claims here. They are not needed for this construction, and
`reports/padded-lines-product-law.md` says why: the joint law of the two sublines-with-points is
*exactly* a product of the two marginals at a fixed padded seed, so the product form of the
pairs-of-lines lemma applies directly. What is left is a single coarse-graining step, and that is
what this file adds.

* **Coarse-graining both sides the same way can only increase agreement.**
  `sum_bornProb_le_fibre`, for bare matrix families rather than `POVM` structures --- which is what
  the pasted line measurement is.
* **The two coarse-grained families.** `ptComb` is the combined point measurement read along the
  linear form `(a, b)`, the paper's `Q-hat^{x,z,alpha,beta}`; `lineComb` is the pasted line
  measurement coarse-grained by the combining map. `lineComb_eq_sum_pasteFib` identifies the second
  as a coarse-graining of the first coarse-graining, which is what makes them comparable.
* **The bound.** `padded_lines_consistency`: the two disagree by at most `m^2 * delta_P` on the
  padded line-point law, at every padded seed and line type.

The `m^2` and the functional form are discussed in the report: it is `poly(m) * poly(eps, md/q)`
rather than the `m * poly(eps, md/q)` the blueprint statement advertises, which
`lem:qld-simultaneous`'s `a(md)^a` prefactor absorbs.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

/-! ## Coarse-graining a Born sum -/

section Born

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **Coarse-graining both sides the same way can only increase agreement.** The `POVM`-structure
version is `MIPRE.sum_bornProb_le_map`; here the families are bare, which is the shape the pasted
line measurement comes in. -/
theorem sum_bornProb_le_fibre {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ψ : dA × dB → ℂ) (P : ι → Matrix dA dA ℂ) (Q : ι → Matrix dB dB ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hQ : ∀ i, (Q i).PosSemidef) (f : ι → κ) :
    ∑ i, bornProb ψ (P i) (Q i)
      ≤ ∑ k : κ, bornProb ψ (∑ i ∈ univ.filter fun i => f i = k, P i)
          (∑ i ∈ univ.filter fun i => f i = k, Q i) := by
  classical
  refine le_trans (le_of_eq (sum_fiber f fun _ i => bornProb ψ (P i) (Q i)))
    (Finset.sum_le_sum fun k _ => ?_)
  rw [bornProb_sum_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Finset.single_le_sum (f := fun j => bornProb ψ (P i) (Q j))
    (fun j _ => bornProb_nonneg ψ (hP i) (hQ j)) hi

/-- **A Born sum on the diagonal of two POVMs is at most one.** -/
theorem sum_bornProb_diag_le_one {ι : Type*} [Fintype ι] {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (P : ι → Matrix dA dA ℂ) (Q : ι → Matrix dB dB ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hQ : ∀ i, (Q i).PosSemidef)
    (hPs : ∑ i, P i = 1) (hQs : ∑ i, Q i = 1) :
    ∑ i, bornProb ψ (P i) (Q i) ≤ 1 := by
  classical
  have h1 : bornProb ψ (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) = 1 := by
    rw [bornProb, Matrix.one_kronecker_one, Matrix.one_mulVec, hψ, Complex.one_re]
  refine le_trans ?_ (le_of_eq h1)
  rw [← hPs, ← hQs, bornProb_sum_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => bornProb ψ (P i) (Q j))
    (fun j _ => bornProb_nonneg ψ (hP i) (hQ j)) (mem_univ i)

end Born

/-! ## The two coarse-grained families -/

section Comb

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}

/-- The pasted line measurement's own outcome map: each side's polynomial read at the parameter of
its own subline. -/
def pasteEval (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (cX cZ : Content F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) : F × F :=
  (LinePoly.eval q.1 (PX.param cX), LinePoly.eval q.2 (PZ.param cZ))

/-- The pasted line measurement coarse-grained by that map --- the family the product form of
`lem:qld-pairs-of-lines` bounds. -/
def pasteFib (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) dB) (cX cZ : Content F m) (r : F × F) :
    Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ :=
  ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
      LinePoly.eval q.1 (PX.param cX) = r.1 ∧ LinePoly.eval q.2 (PZ.param cZ) = r.2,
    pasteLine PX PZ d M cX cZ q

theorem pasteFib_eq (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) dB) (cX cZ : Content F m) (r : F × F) :
    pasteFib PX PZ d M cX cZ r
      = ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
          pasteEval PX PZ cX cZ q = r, pasteLine PX PZ d M cX cZ q := by
  classical
  refine Finset.sum_congr (Finset.filter_congr fun q _ => ?_) fun _ _ => rfl
  rw [pasteEval, Prod.ext_iff]

theorem posSemidef_pasteFib {M : Question F m → POVM (Answer F m d) dB}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (cX cZ : Content F m) (r : F × F) :
    (pasteFib PX PZ d M cX cZ r).PosSemidef :=
  Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    fun q _ => posSemidef_pasteLine hM PX PZ cX cZ q

theorem sum_pasteFib {M : Question F m → POVM (Answer F m d) dB}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (cX cZ : Content F m) :
    ∑ r : F × F, pasteFib PX PZ d M cX cZ r = 1 := by
  classical
  rw [Finset.sum_congr rfl fun r (_ : r ∈ (univ : Finset (F × F))) =>
    pasteFib_eq PX PZ d M cX cZ r,
    ← sum_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) => pasteEval PX PZ cX cZ q)
      fun _ q => pasteLine PX PZ d M cX cZ q]
  exact sum_pasteLine hM PX PZ cX cZ

/-- **The combined point measurement along the linear form `(a, b)`**: the paper's
`Q-hat^{x,z,alpha,beta}`. -/
def ptComb {N : Type*} [Fintype N] [DecidableEq N] (Q : F × F → Matrix N N ℂ) (a b : F) (v : F) :
    Matrix N N ℂ :=
  ∑ r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v, Q r

/-- **The pasted line measurement coarse-grained by the combining map at `(a, b)`.** Averaged over
the fresh randomness this is `padLineMats` read at the sampled point; see
`sum_filter_padLineMats`. -/
def lineComb (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) dB) (cX cZ : Content F m) (a b : F) (v : F) :
    Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ :=
  ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
      a * LinePoly.eval q.1 (PX.param cX) + b * LinePoly.eval q.2 (PZ.param cZ) = v,
    pasteLine PX PZ d M cX cZ q

/-- **The line side is a coarse-graining of the fibre family**, along the same linear form. This is
what lets the two be compared by `sum_bornProb_le_fibre`. -/
theorem lineComb_eq_sum_pasteFib (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) dB) (cX cZ : Content F m) (a b : F) (v : F) :
    lineComb PX PZ d M cX cZ a b v
      = ∑ r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v,
        pasteFib PX PZ d M cX cZ r := by
  classical
  rw [Finset.sum_congr rfl fun r (_ : r ∈ univ.filter fun r : F × F => a * r.1 + b * r.2 = v) =>
    pasteFib_eq PX PZ d M cX cZ r,
    sum_filter_fiber (fun q : LinePoly F (m * d) × LinePoly F (m * d) => pasteEval PX PZ cX cZ q)
      (fun r : F × F => a * r.1 + b * r.2 = v) fun q => pasteLine PX PZ d M cX cZ q]
  rfl

end Comb

/-! ## The consistency bound -/

section Main

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

set_option maxHeartbeats 1600000 in
/-- **`lem:qld-padded-lines`, the consistency bound.** On the padded line-point law, at every padded
seed and line type, the combined point measurement read along `(alpha, beta)` at the sampled point
agrees with the pasted line measurement coarse-grained by the combining map, up to
`m^2 * delta_P`.

The proof is the coarse-graining step and then the two domination lemmas: agreement only increases
under a common coarse-graining, the padded law is at most `m^2` times the product law
(`avgSub_le_mul_avgAll`), and `(alpha, beta)` is uniform and independent of both sublines
(`avgSubAB_le_of_forall`). The paper's Claims 17-1 to 17-3 are not used; see
`reports/padded-lines-product-law.md`. -/
theorem padded_lines_consistency (hm4 : 4 * m ∣ Fintype.card F) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z)
    (hfacX : FactorsX PX) (hfacZ : FactorsZ PZ)
    (hX1 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ f : LinePoly F (m * d),
        xSqNorm (hatVec (F := F) (m := m) ψ) (PX.lineMats d MA c f)
          (PX.lineMats d MB c f) ≤ 172 * ε)
    (hX2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .X (c.pt .X) a)
          (PX.lineEvalMats d MB c a) ≤ 172 * ε)
    (hZ2 : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ b : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA .Z (c.pt .Z) b)
          (PZ.lineEvalMats d MB c b) ≤ 172 * ε)
    {εc : ℝ} (hcoll : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
      collProb PX d c ≤ εc) (ty : CL.Ty) (s : F) :
    ∃ QA : LPData F m × LPData F m → F × F →
        Matrix ((dA × Anc F m) × (F × F)) ((dA × Anc F m) × (F × F)) ℂ,
      (∀ p, IsPVM (QA p))
      ∧ (∀ p r, (ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))ᴴ
            * (QA p r * ancillaEmbed (dA × Anc F m) ((0 : F), (0 : F)))
          = sand (hatMats MA .X p.1.pt) (hatMats MA .Z p.2.pt) r)
      ∧ 1 - avgSubAB hm4 hm ty s (fun a b cX cZ =>
            ∑ v : F, bornProb (extHat (m := m) ψ) (ptComb (QA (cX, cZ)) a b v)
              (lineComb PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
        ≤ (m : ℝ) * (m : ℝ) * deltaPairs ε εc := by
  classical
  obtain ⟨QA, hPA, hkA, hbound⟩ := pairs_of_lines_prod_of_items hψ hfail hprojA hprojB PX PZ
    hfacX hfacZ hX1 hX2 hZ2 hcoll
  refine ⟨QA, hPA, hkA, ?_⟩
  have hunit : star (extHat (m := m) ψ) ⬝ᵥ (extHat (m := m) ψ) = 1 :=
    extVec2_unit (hatVec_unit hψ) ((0 : F), (0 : F)) ((0 : F), (0 : F))
  -- the product-law bound on the fine agreement, `pasteFib` being the filter sum by definition
  have hfineb : 1 - avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
          (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
      ≤ deltaPairs ε εc := by
    rw [avgAll_prod_eq_uniform]
    exact hbound
  -- every fine agreement is at most one
  have hQpsd : ∀ (p : LPData F m × LPData F m) (r : F × F), (QA p r).PosSemidef :=
    fun p r => (hPA p).posSemidef r
  have hTpsd : ∀ (p : LPData F m × LPData F m) (r : F × F),
      (pasteFib PX PZ d MB (pairCX p) (pairCZ p) r).PosSemidef :=
    fun p r => posSemidef_pasteFib hprojB PX PZ (pairCX p) (pairCZ p) r
  have hTsum : ∀ p : LPData F m × LPData F m,
      ∑ r : F × F, pasteFib PX PZ d MB (pairCX p) (pairCZ p) r = 1 :=
    fun p => sum_pasteFib hprojB PX PZ (pairCX p) (pairCZ p)
  have hfine1 : ∀ p : LPData F m × LPData F m,
      (∑ r : F × F, bornProb (extHat (m := m) ψ) (QA p r)
        (pasteFib PX PZ d MB (pairCX p) (pairCZ p) r)) ≤ 1 := fun p =>
    sum_bornProb_diag_le_one (ι := F × F) hunit (QA p)
      (pasteFib PX PZ d MB (pairCX p) (pairCZ p))
      (hQpsd p) (hTpsd p) (hPA p).sum_eq_one (hTsum p)
  -- coarse-graining only increases agreement
  have hcoarse : ∀ (a b : F) (p : LPData F m × LPData F m),
      (∑ r : F × F, bornProb (extHat (m := m) ψ) (QA p r)
          (pasteFib PX PZ d MB (pairCX p) (pairCZ p) r))
        ≤ ∑ v : F, bornProb (extHat (m := m) ψ) (ptComb (QA p) a b v)
            (lineComb PX PZ d MB (pairCX p) (pairCZ p) a b v) := by
    intro a b p
    refine le_trans (sum_bornProb_le_fibre (ι := F × F) (κ := F) (extHat (m := m) ψ) (QA p)
      (pasteFib PX PZ d MB (pairCX p) (pairCZ p)) (fun r => (hPA p).posSemidef r)
      (fun r => posSemidef_pasteFib hprojB PX PZ _ _ r)
      (fun r : F × F => a * r.1 + b * r.2)) (le_of_eq (Finset.sum_congr rfl fun v _ => ?_))
    rw [ptComb, lineComb_eq_sum_pasteFib]
  -- the deficit of the fine agreement, on the product law
  have hinner : ∀ cX : LPData F m,
      avgAll (fun cZ : LPData F m => 1 - ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
            (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
        = 1 - avgAll (fun cZ : LPData F m => ∑ r : F × F,
          bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
            (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) := fun cX => by
    rw [avgAll_sub (fun _ : LPData F m => (1 : ℝ)), avgAll_one]
  have houter : avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        1 - ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
          (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r))
      = 1 - avgAll (fun cX : LPData F m => avgAll fun cZ : LPData F m =>
        ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
          (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) := by
    rw [congrArg avgAll (funext hinner), avgAll_sub (fun _ : LPData F m => (1 : ℝ)), avgAll_one]
  -- the padded law, at each fixed `(alpha, beta)`
  have hstep : ∀ a b : F, avgSub hm4 hm ty s (fun cX cZ =>
        1 - ∑ v : F, bornProb (extHat (m := m) ψ) (ptComb (QA (cX, cZ)) a b v)
          (lineComb PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
      ≤ (m : ℝ) * (m : ℝ) * deltaPairs ε εc := by
    intro a b
    refine le_trans (avgSub_mono hm4 hm ty s (g' := fun cX cZ =>
      1 - ∑ r : F × F, bornProb (extHat (m := m) ψ) (QA (cX, cZ) r)
        (pasteFib PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) r)) fun cX cZ => by
      have h := hcoarse a b (cX, cZ)
      linarith) ?_
    refine le_trans (avgSub_le_mul_avgAll hm4 hm ty s fun cX cZ => by
      have h := hfine1 (cX, cZ)
      linarith) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [houter]
    linarith [hfineb]
  -- and back to the joint law
  have hsub := avgSubAB_sub hm4 hm ty s (fun _ _ _ _ => (1 : ℝ))
    (fun (a b : F) (cX cZ : LPData F m) => ∑ v : F,
      bornProb (extHat (m := m) ψ) (ptComb (QA (cX, cZ)) a b v)
        (lineComb PX PZ d MB (pairCX (cX, cZ)) (pairCZ (cX, cZ)) a b v))
  rw [avgSubAB_one] at hsub
  have hle := avgSubAB_le_of_forall hm4 hm ty s hstep
  linarith [hsub, hle]

end Main

end MIPRE.QLD
