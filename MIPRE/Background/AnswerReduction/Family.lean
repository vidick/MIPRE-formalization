/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Layout
import MIPRE.Foundations.CL.ProductSampler
import MIPRE.Foundations.OracularTyped

/-!
# The binary CL family of the answer-reduced sampler

Piece AR-3c of `planning/answer-reduction.md`: the typed CL functions of the answer-reduced
sampler `Ŝ^ar` (`sec:ar-verifier`, `ld_compiler.tex`), over `𝔽₂`, one for each type
`(r, t) ∈ Role × PcpTy`.

* **The PCP half is downsized along the Shoup polynomial basis** (`pcpBin`), whose coordinates
  are the field elements' bits `fld.toBits`, the representation the PCP verifier reads
  (`shoupCoordinateEquiv_encoding`). This is finding 1 of the plan: questions need no change of
  basis before the PCP verifier sees them. Its bits are numbered by `Pcp.bitIndex` (`pcpCl`).
* **The oracle half** is the oracularized sampler's `roleFamily` of the input sampler.
* Both are padded to `L = max (ℓ + 1) 3` levels and put side by side, the oracle half first
  (`cl`, the product `CLFun.prodCL` of `MIPRE/Foundations/CL/ProductSampler`).

`cl_exactlyOn` is the exactness a `CL.TypedSampler` asks for, and `oraclePart_eval`,
`pcpPart_eval` say what the question of a type carries: the oracle's question in the oracle
coordinates, the downsized PCP question in the others.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.CL.CLFun SAT Pcp

/-! ## The family -/

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)

/-- The field of the PCP, `F_q` with `q = 2^k`, in its Shoup representation. -/
abbrev Fq := (shoupBinField P.k hk).carrier

/-- The Shoup polynomial basis of `F_q` over `𝔽₂`: its coordinates are the bits of an element. -/
abbrev basis : Module.Basis (Fin P.k) (ZMod 2) (Fq P hk) := shoupPowerBasis P.k hk

/-- The common level `max (ℓ + 1) 3`. -/
abbrev level (ℓ : ℕ) : ℕ := max (ℓ + 1) 3

/-- The dimension of the answer-reduced sampler at index `n`. -/
abbrev dim : ℕ := V.sampler.dim n + Pcp.pcpDim P * P.k

variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')

/-- The downsized PCP presentation of a PCP type. -/
def pcpBin (t : PcpTy) : CLFun 𝔽₂ (Coord P × Fin P.k) 3 :=
  (Pcp.pres P S S' t).downsize (basis P hk)

/-- The downsized PCP presentation, on the numbered bits. -/
def pcpCl (t : PcpTy) : CLFun 𝔽₂ (Fin (Pcp.pcpDim P * P.k)) 3 :=
  (pcpBin P hk S S' t).reindex (Pcp.bitIndex P P.k)

/-- **The typed CL function** of the answer-reduced sampler at the type `rt`: the oracle half on
the first coordinates, the PCP half on the rest, at the common level. -/
def cl (rt : Role × PcpTy) : CLFun 𝔽₂ (Fin (dim V n P)) (level ℓ) :=
  prodCL (level ℓ) (roleFamily (V.sampler.cl n) rt.1) (pcpCl P hk S S' rt.2)
    (le_max_left _ _) (le_max_right _ _)

theorem pcpBin_exactlyOn (t : PcpTy) : (pcpBin P hk S S' t).ExactlyOn univ := by
  have h := (Pcp.pres_exactlyOn P S S' t).downsize (basis P hk)
  rwa [Finset.univ_product_univ] at h

theorem pcpCl_exactlyOn (t : PcpTy) : (pcpCl P hk S S' t).ExactlyOn univ := by
  have h := (pcpBin_exactlyOn P hk S S' t).reindex (Pcp.bitIndex P P.k)
  rwa [Finset.map_univ_equiv] at h

theorem cl_exactlyOn (rt : Role × PcpTy) : (cl V n P hk S S' rt).ExactlyOn univ :=
  ExactlyOn.prodCL _ (exactlyOn_roleFamily (V.sampler.cl_exactlyOn n) rt.1)
    (pcpCl_exactlyOn P hk S S' rt.2) _ _

theorem pcpCl_eval (t : PcpTy) (v : Coord P → Fq P hk) :
    (pcpCl P hk S S' t).eval (reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk) v)) =
      reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk)
        ((Pcp.pres P S S' t).eval v)) := by
  rw [pcpCl, eval_reindex, pcpBin, eval_downsize]

/-! ## What a question carries -/

/-- The oracle coordinates of a vector. -/
def oraclePart (y : Fin (dim V n P) → 𝔽₂) : Fin (V.sampler.dim n) → 𝔽₂ := leftPart y

/-- The PCP coordinates of a vector, read back as a vector of `V^pcp`. -/
def pcpPart (y : Fin (dim V n P) → 𝔽₂) : Coord P → Fq P hk :=
  (downsizeEquiv (basis P hk)).symm ((reindexEquiv (Pcp.bitIndex P P.k)).symm (rightPart y))

theorem eval_cl (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    (cl V n P hk S S' rt).eval y = Fin.append ((roleFamily (V.sampler.cl n) rt.1).eval
      (leftPart y)) ((pcpCl P hk S S' rt.2).eval (rightPart y)) := by
  rw [← truncate_self (cl V n P hk S S' rt), cl, eval_truncate_prodCL _
    (exactlyOn_roleFamily (V.sampler.cl_exactlyOn n) rt.1) (pcpCl_exactlyOn P hk S S' rt.2),
    eval_truncate_of_le _ (le_max_left _ _), eval_truncate_of_le _ (le_max_right _ _)]

/-- **The oracle half of a question** is the oracularized sampler's question. -/
theorem oraclePart_eval (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    oraclePart V n P ((cl V n P hk S S' rt).eval y)
      = (roleFamily (V.sampler.cl n) rt.1).eval (oraclePart V n P y) := by
  rw [oraclePart, eval_cl, leftPart_append]
  rfl

/-- **The PCP half of a question** is the PCP presentation's question. -/
theorem pcpPart_eval (rt : Role × PcpTy) (y : Fin (dim V n P) → 𝔽₂) :
    pcpPart V n P hk ((cl V n P hk S S' rt).eval y)
      = (Pcp.pres P S S' rt.2).eval (pcpPart V n P hk y) := by
  rw [pcpPart, eval_cl, rightPart_append]
  have : rightPart y = reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk)
      (pcpPart V n P hk y)) := by
    simp only [pcpPart, LinearEquiv.apply_symm_apply]
  rw [this, pcpCl_eval]
  simp only [LinearEquiv.symm_apply_apply]

end MIPRE.AnswerReduction

end
