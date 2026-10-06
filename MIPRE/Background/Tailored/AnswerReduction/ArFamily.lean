/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.Complete
public import MIPRE.Foundations.OracularTyped

@[expose] public section

/-!
# The CL functions of the answer-reduced sampler

The answer-reduced sampler (`defn:combi_ans_red`, II:10285) is the direct sum of the oracularized
input sampler and the seeded low-degree test's presentation, downsized over `F₂` along the Shoup
basis (as in the MIP* answer reduction's `MIPRE.AnswerReduction.cl`). Here are its CL functions,
one per type `(r, S) ∈ Role × LIDT.CL.Ty`, the same for both players:

* the oracularized half is `roleFamily` of the input sampler's CL functions, lifted one level
  (the oracle reads the seed itself, an isolated player its own question);
* the low-degree half is the presentation `LIDT.CL.Regs.pres` of the type, downsized and
  numbered (`ldCl`);
* both padded to `max (ℓ + 2) 5` levels, the oracularized half first (`arCl`).

`arSampler_arCl`: they form an answer-reduced sampler (`ArSampler`), the hypothesis under which
`hasPerfectZPC_ar` holds.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open MIPRE.CL MIPRE.CL.CLFun MIPRE.SAT

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM) {ℓ : ℕ} (V : TailoredVerifier ℓ) (n : ℕ)

/-- The input sampler's CL functions at index `n`, one level up. -/
def liftedCl : Player → CLFun 𝔽₂ (Fin (V.sampler.dim n)) (ℓ + 1) :=
  fun w => (V.sampler.cl n w).liftTo Finset.univ (ℓ + 1) (Nat.le_succ ℓ)

theorem liftedCl_exactlyOn (w : Player) : (liftedCl V n w).ExactlyOn Finset.univ :=
  (V.sampler.cl_exactlyOn n w).liftTo _ _

variable (t ht) in
/-- **The low-degree half**: the presentation of the seeded low-degree test at a type, downsized
along the Shoup basis and numbered. -/
def ldCl (S : LIDT.CL.Ty) : CLFun 𝔽₂ (Fin (D j * t)) 3 :=
  (((regs j).pres sel S).downsize (shoupPowerBasis t ht)).reindex finProdFinEquiv

theorem ldCl_exactlyOn (S : LIDT.CL.Ty) : (ldCl t ht sel S).ExactlyOn Finset.univ := by
  have h := ((regs j).pres_exactlyOn sel S).downsize (shoupPowerBasis t ht)
  rw [Finset.univ_product_univ] at h
  have h' := h.reindex finProdFinEquiv
  rwa [Finset.map_univ_equiv] at h'

/-- **The CL function of the answer-reduced sampler** at a type: the oracularized input question on
the first coordinates, the seeded low-degree test's question on the rest. -/
def arCl (u : Role × LIDT.CL.Ty) :
    CLFun 𝔽₂ (Fin (V.sampler.dim n + D j * t)) (max (ℓ + 2) 5) :=
  prodCL (max (ℓ + 2) 5) (roleFamily (liftedCl V n) u.1) (ldCl t ht sel u.2) (by omega)
    (by omega)

theorem arCl_exactlyOn (u : Role × LIDT.CL.Ty) : (arCl sel V n u).ExactlyOn Finset.univ :=
  ExactlyOn.prodCL _ (exactlyOn_roleFamily (liftedCl_exactlyOn V n) u.1)
    (ldCl_exactlyOn sel u.2) _ _

theorem eval_arCl (u : Role × LIDT.CL.Ty) (s : Fin (V.sampler.dim n + D j * t) → 𝔽₂) :
    (arCl sel V n u).eval s = Fin.append ((roleFamily (liftedCl V n) u.1).eval (leftPart s))
      ((ldCl t ht sel u.2).eval (rightPart s)) := by
  rw [← truncate_self (arCl sel V n u), arCl, eval_truncate_prodCL _
    (exactlyOn_roleFamily (liftedCl_exactlyOn V n) u.1) (ldCl_exactlyOn sel u.2),
    eval_truncate_of_le _ (by omega), eval_truncate_of_le _ (by omega)]

/-- **The oracularized half of a question** is the oracularized question of the seed's input part,
in the type's role. -/
theorem rolePart_arCl (u : Role × LIDT.CL.Ty) (s : Fin (V.sampler.dim n + D j * t) → 𝔽₂) :
    rolePart t j (V.sampler.dim n) ((arCl sel V n u).eval s) =
      ((inSeeded V n).oquestion u.1 (leftPart s)).2 := by
  rw [rolePart, eval_arCl, leftPart_append]
  obtain ⟨r, S⟩ := u
  cases r
  · exact eval_ident _ _
  · exact eval_liftTo _ _ (Nat.le_succ ℓ) _ _
  · exact eval_liftTo _ _ (Nat.le_succ ℓ) _ _

/-- **The low-degree half of a question** is the seeded test's question of the seed's low-degree
part. -/
theorem ldPart_arCl (u : Role × LIDT.CL.Ty) (s : Fin (V.sampler.dim n + D j * t) → 𝔽₂) :
    ldPart t ht j (V.sampler.dim n) ((arCl sel V n u).eval s) =
      ((regs j).pres sel u.2).eval (ldPart t ht j (V.sampler.dim n) s) := by
  rw [ldPart, eval_arCl, rightPart_append]
  have e : rightPart s = reindexEquiv finProdFinEquiv (downsizeEquiv (shoupPowerBasis t ht)
      (ldPart t ht j (V.sampler.dim n) s)) := by
    simp only [ldPart, LinearEquiv.apply_symm_apply]
  rw [e, ldCl, eval_reindex, eval_downsize]
  simp only [LinearEquiv.symm_apply_apply]

/-- **The answer-reduced sampler's CL functions form an answer-reduced sampler.** -/
theorem arSampler_arCl : ArSampler hM sel V n fun _ u => arCl sel V n u where
  exactlyOn _ u := arCl_exactlyOn sel V n u
  role _ u s := rolePart_arCl sel V n u s
  ld _ u s := ldPart_arCl sel V n u s

end MIPRE.Tailored.AnsRed.Typed

end
