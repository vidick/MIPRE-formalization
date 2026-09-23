/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.PcpPresentation
import MIPRE.Foundations.CL.Product
import MIPRE.Foundations.CL.Downsize
import MIPRE.Foundations.OracularTyped
import MIPRE.Foundations.SAT.FieldCoordinates

/-!
# The binary CL family of the answer-reduced sampler

Piece AR-3c of `planning/answer-reduction.md`: the typed CL functions of the answer-reduced
sampler `Ŝ^ar` (`sec:ar-verifier`, `ld_compiler.tex`), over `𝔽₂`, one for each type
`(r, t) ∈ Role × PcpTy`.

* **The PCP half is downsized along the Shoup polynomial basis** (`pcpBin`), whose coordinates
  are the field elements' bits `fld.toBits`, the representation the PCP verifier reads
  (`shoupCoordinateEquiv_encoding`). This is finding 1 of the plan: questions need no change of
  basis before the PCP verifier sees them.
* **The oracle half** is the oracularized sampler's `roleFamily` of the input sampler.
* Both are padded to `L = max (ℓ + 1) 3` levels and put side by side on
  `Fin (dim) ⊕ (Coord P × Fin k)` (`fam`), then numbered by the explicit bijection `index` with
  `Fin (dim + (10m + 2s + 16) k)` (`cl`).

`cl_exactlyOn` is the exactness a `CL.TypedSampler` asks for, and `oraclePart_eval`,
`pcpPart_eval` say what the question of a type carries: the oracle's question in the oracle
coordinates, the downsized PCP question in the others.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.CL.CLFun SAT Pcp

/-! ## Numbering the coordinates -/

/-- The number of coordinates of `V^pcp`. -/
def pcpDim (P : PcpParams) : ℕ := 10 * P.m + 2 * P.s + 16

/-- An explicit numbering of the coordinates of `V^pcp`: the five point registers, the five
direction registers, the six seeds, the auxiliary point and direction registers, in that order. -/
def coordIndex (P : PcpParams) : Coord P ≃ Fin (pcpDim P) :=
  (Coord.equivSum P).trans <|
  (Equiv.sumCongr finProdFinEquiv (Equiv.sumCongr finProdFinEquiv
    (Equiv.sumCongr (Equiv.refl (Fin 6)) finSumFinEquiv))).trans <|
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)).trans <|
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans <|
  finSumFinEquiv.trans (finCongr (by simp only [pcpDim]; ring))

/-- The numbering of the answer-reduced sampler's coordinates: the input sampler's first, then
the bits of `V^pcp`, coordinate by coordinate. -/
def index (d : ℕ) (P : PcpParams) (k : ℕ) : Fin d ⊕ (Coord P × Fin k) ≃ Fin (d + pcpDim P * k) :=
  (Equiv.sumCongr (Equiv.refl _) (((coordIndex P).prodCongr (Equiv.refl _)).trans
    finProdFinEquiv)).trans finSumFinEquiv

/-! ## The family -/

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)

/-- The field of the PCP, `F_q` with `q = 2^k`, in its Shoup representation. -/
abbrev Fq := (shoupBinField P.k hk).carrier

/-- The Shoup polynomial basis of `F_q` over `𝔽₂`: its coordinates are the bits of an element. -/
abbrev basis : Module.Basis (Fin P.k) (ZMod 2) (Fq P hk) := shoupPowerBasis P.k hk

/-- The common level `max (ℓ + 1) 3`. -/
abbrev level (ℓ : ℕ) : ℕ := max (ℓ + 1) 3

/-- The dimension of the answer-reduced sampler at index `n`. -/
abbrev dim : ℕ := V.sampler.dim n + pcpDim P * P.k

variable [NeZero P.m] (hm : P.m ∣ Fintype.card (Fq P hk)) (hm' : P.m' ∣ Fintype.card (Fq P hk))

/-- The downsized PCP presentation of a PCP type. -/
def pcpBin (t : PcpTy) : CLFun 𝔽₂ (Coord P × Fin P.k) 3 :=
  (Pcp.pres P hm hm' t).downsize (basis P hk)

/-- The two halves side by side, at the common level. -/
def fam (rt : Role × PcpTy) : CLFun 𝔽₂ (Fin (V.sampler.dim n) ⊕ (Coord P × Fin P.k)) (level ℓ) :=
  ((roleFamily (V.sampler.cl n) rt.1).liftTo univ (level ℓ) (le_max_left _ _)).prod
    ((pcpBin P hk hm hm' rt.2).liftTo univ (level ℓ) (le_max_right _ _))

/-- **The typed CL function** of the answer-reduced sampler at the type `rt`, on the numbered
coordinates. -/
def cl (rt : Role × PcpTy) : CLFun 𝔽₂ (Fin (dim V n P)) (level ℓ) :=
  (fam V n P hk hm hm' rt).reindex (index (V.sampler.dim n) P P.k)

theorem pcpBin_exactlyOn (t : PcpTy) : (pcpBin P hk hm hm' t).ExactlyOn univ := by
  have h := (Pcp.pres_exactlyOn P hm hm' t).downsize (basis P hk)
  rwa [Finset.univ_product_univ] at h

theorem fam_exactlyOn (rt : Role × PcpTy) : (fam V n P hk hm hm' rt).ExactlyOn univ :=
  ExactlyOn.prod ((exactlyOn_roleFamily (V.sampler.cl_exactlyOn n) rt.1).liftTo _ _)
    ((pcpBin_exactlyOn P hk hm hm' rt.2).liftTo _ _)

theorem cl_exactlyOn (rt : Role × PcpTy) : (cl V n P hk hm hm' rt).ExactlyOn univ := by
  have h := (fam_exactlyOn V n P hk hm hm' rt).reindex (index (V.sampler.dim n) P P.k)
  rwa [Finset.map_univ_equiv] at h

/-! ## What a question carries -/

/-- The oracle coordinates of a vector. -/
def oraclePart (y : Fin (dim V n P) → 𝔽₂) : Fin (V.sampler.dim n) → 𝔽₂ :=
  fun i => y (index (V.sampler.dim n) P P.k (.inl i))

/-- The PCP coordinates of a vector, read back as a vector of `V^pcp`. -/
def pcpPart (y : Fin (dim V n P) → 𝔽₂) : Coord P → Fq P hk :=
  (downsizeEquiv (basis P hk)).symm fun p => y (index (V.sampler.dim n) P P.k (.inr p))

theorem fam_eval (rt : Role × PcpTy) (x : Fin (V.sampler.dim n) ⊕ (Coord P × Fin P.k) → 𝔽₂) :
    (fam V n P hk hm hm' rt).eval x
      = Sum.elim ((roleFamily (V.sampler.cl n) rt.1).eval fun i => x (.inl i))
          (downsizeEquiv (basis P hk) ((Pcp.pres P hm hm' rt.2).eval
            ((downsizeEquiv (basis P hk)).symm fun p => x (.inr p)))) := by
  rw [fam, eval_prod _ _ ((exactlyOn_roleFamily (V.sampler.cl_exactlyOn n) rt.1).liftTo _ _)
    ((pcpBin_exactlyOn P hk hm hm' rt.2).liftTo _ _), eval_liftTo, eval_liftTo, pcpBin,
    eval_downsize']

/-- **The oracle half of a question** is the oracularized sampler's question. -/
theorem oraclePart_eval (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    oraclePart V n P ((cl V n P hk hm hm' rt).eval y)
      = (roleFamily (V.sampler.cl n) rt.1).eval (oraclePart V n P y) := by
  funext i
  simp only [oraclePart, cl, eval_reindex', reindexEquiv_apply, fam_eval,
    Equiv.symm_apply_apply, Sum.elim_inl, reindexEquiv_symm_apply]
  rfl

/-- **The PCP half of a question** is the PCP presentation's question. -/
theorem pcpPart_eval (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    pcpPart V n P hk ((cl V n P hk hm hm' rt).eval y)
      = (Pcp.pres P hm hm' rt.2).eval (pcpPart V n P hk y) := by
  simp only [pcpPart, cl, eval_reindex', reindexEquiv_apply, fam_eval,
    Equiv.symm_apply_apply, Sum.elim_inr, reindexEquiv_symm_apply]
  exact (downsizeEquiv (basis P hk)).symm_apply_apply _

end MIPRE.AnswerReduction

end
