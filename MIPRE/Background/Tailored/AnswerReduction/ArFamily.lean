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

* the oracularized half is `roleFamily` of the input sampler's CL functions (the oracle reads the
  seed itself, an isolated player its own question), for an input of level `ℓ + 1`;
* the low-degree half is the presentation `LIDT.CL.Regs.pres` of the type, downsized and
  numbered (`ldCl`);
* both padded to `max (ℓ + 1) 3` levels, the oracularized half first (`arCl`). Detyping adds two
  levels (`CL.Detyping.sampler`), so the output sampler has `max (ℓ + 1) 3 + 2` levels, the
  `max ((ℓ + 1) + 2) 5` of `TailoredAnswerReduction`, as in the MIP* answer reduction's
  `MIPRE.AnswerReduction.level`.

`arSampler_arCl`: they form an answer-reduced sampler (`ArSampler`), the hypothesis under which
`hasPerfectZPC_ar` and `valStar_ar_sound` hold. The oracularized game of the input
(`inSeeded`) reads the input's CL functions lifted one level (`liftedCl`), which have the same
values.
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

section Family

variable {k : ℕ} (W : TailoredVerifier (k + 1))

/-- **The CL function of the answer-reduced sampler** at a type: the oracularized input question on
the first coordinates, the seeded low-degree test's question on the rest. -/
def arCl (u : Role × LIDT.CL.Ty) :
    CLFun 𝔽₂ (Fin (W.sampler.dim n + D j * t)) (max (k + 1) 3) :=
  prodCL (max (k + 1) 3) (roleFamily (W.sampler.cl n) u.1) (ldCl t ht sel u.2) (le_max_left _ _)
    (le_max_right _ _)

theorem arCl_exactlyOn (u : Role × LIDT.CL.Ty) : (arCl sel n W u).ExactlyOn Finset.univ :=
  ExactlyOn.prodCL _ (exactlyOn_roleFamily (W.sampler.cl_exactlyOn n) u.1)
    (ldCl_exactlyOn sel u.2) _ _

theorem eval_arCl (u : Role × LIDT.CL.Ty) (s : Fin (W.sampler.dim n + D j * t) → 𝔽₂) :
    (arCl sel n W u).eval s = Fin.append ((roleFamily (W.sampler.cl n) u.1).eval (leftPart s))
      ((ldCl t ht sel u.2).eval (rightPart s)) := by
  rw [← truncate_self (arCl sel n W u), arCl, eval_truncate_prodCL _
    (exactlyOn_roleFamily (W.sampler.cl_exactlyOn n) u.1) (ldCl_exactlyOn sel u.2),
    eval_truncate_of_le _ (by omega), eval_truncate_of_le _ (by omega)]

/-- **The oracularized half of a question** is the oracularized question of the seed's input part,
in the type's role. -/
theorem rolePart_arCl (u : Role × LIDT.CL.Ty) (s : Fin (W.sampler.dim n + D j * t) → 𝔽₂) :
    rolePart t j (W.sampler.dim n) ((arCl sel n W u).eval s) =
      ((inSeeded W n).oquestion u.1 (leftPart s)).2 := by
  rw [rolePart, eval_arCl, leftPart_append]
  obtain ⟨r, S⟩ := u
  cases r
  · exact eval_ident _ _
  · rfl
  · rfl

/-- **The low-degree half of a question** is the seeded test's question of the seed's low-degree
part. -/
theorem ldPart_arCl (u : Role × LIDT.CL.Ty) (s : Fin (W.sampler.dim n + D j * t) → 𝔽₂) :
    ldPart t ht j (W.sampler.dim n) ((arCl sel n W u).eval s) =
      ((regs j).pres sel u.2).eval (ldPart t ht j (W.sampler.dim n) s) := by
  rw [ldPart, eval_arCl, rightPart_append]
  have e : rightPart s = reindexEquiv finProdFinEquiv (downsizeEquiv (shoupPowerBasis t ht)
      (ldPart t ht j (W.sampler.dim n) s)) := by
    simp only [ldPart, LinearEquiv.apply_symm_apply]
  rw [e, ldCl, eval_reindex, eval_downsize]
  simp only [LinearEquiv.symm_apply_apply]

/-- **The answer-reduced sampler's CL functions form an answer-reduced sampler.** -/
theorem arSampler_arCl : ArSampler hM sel W n fun _ u => arCl sel n W u where
  exactlyOn _ u := arCl_exactlyOn sel n W u
  role _ u s := rolePart_arCl sel n W u s
  ld _ u s := ldPart_arCl sel n W u s

end Family

end MIPRE.Tailored.AnsRed.Typed

end
