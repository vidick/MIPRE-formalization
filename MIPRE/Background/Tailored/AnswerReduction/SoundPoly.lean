/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.SoundRelations

@[expose] public section

/-!
# Soundness of the answer-reduced game: the polynomials of the roles agree

From evaluations to polynomials, by Schwartz–Zippel (II:10708): an isolated role's polynomial
measurement and the oracle's, read in the role's slots, disagree at most as often as their
evaluations at a uniform point do, plus `M d / q` (`BipartiteModel.dis_le_sum_dis_map_add`, with
`sum_uniform_evalR_eq_le`), since two distinct tuples of polynomials of individual degree `d` in
`M` variables agree at a uniform point with probability at most `M d / q`. With the triangles of
`SoundRelations`, the two disagreements average to at most `errP` over the seeds
(`sum_dis_GAr_GBO_poly_le`, `sum_dis_GAO_GBr_poly_le`).

No lifting is needed: unlike the MIP* answer reduction, every polynomial of the game lives on the
same `M = 2^j` variables, the isolated role's codewords being the oracle's in the role's slots.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset MIPRE.CL MIPRE.SAT MIPRE.LIDT

/-- **Schwartz–Zippel for tuples**: two distinct tuples of polynomials of individual degree `d` in
`n` variables agree at a uniform point with probability at most `n d / q`. -/
theorem sum_uniform_tuple_eq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d k : ℕ}
    {g g' : Fin k → LowIndDegPoly (F := F) (m := n) (d := d)} (h : g ≠ g') :
    ∑ u : Point F n, uniform (Point F n) u *
        (if (fun c => (g c).eval u) = (fun c => (g' c).eval u) then 1 else 0)
      ≤ (n : ℝ) * d / Fintype.card F := by
  obtain ⟨c, hc⟩ := Function.ne_iff.mp h
  refine le_trans (Finset.sum_le_sum fun u _ => ?_) (sum_uniform_eval_eq_le hc)
  refine mul_le_mul_of_nonneg_left ?_ (by simp [uniform])
  by_cases h1 : (fun c => (g c).eval u) = (fun c => (g' c).eval u)
  · rw [ite_eq_left h1, ite_eq_left (congrFun h1 c)]
  · rw [ite_eq_right h1]
    split_ifs <;> norm_num

section Points

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ}

/-- **Schwartz–Zippel on the registers**: at the point the registers of a uniform vector carry,
two distinct tuples of polynomials agree with probability at most `M d / q`. -/
theorem sum_uniform_evalR_eq_le {k : ℕ}
    {g g' : Fin k → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)} (h : g ≠ g') :
    ∑ w : Fin (D j) → Fq t ht, uniform (Fin (D j) → Fq t ht) w *
        (if evalR ((regs j).ptOf w) g = evalR ((regs j).ptOf w) g' then 1 else 0)
      ≤ ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht) := by
  have hc := LIDT.CL.Regs.card_mul_card_points (regs j) (F := Fq t ht)
  have hs := LIDT.CL.Regs.sum_ptOf (regs j)
    (fun u => (if evalR u g = evalR u g' then (1 : ℝ) else 0))
  have key := sum_uniform_tuple_eq_le h
  simp only [uniform, ← Finset.mul_sum] at key ⊢
  rw [hs, nsmul_eq_mul]
  refine le_trans (le_of_eq ?_) key
  have hP : (0 : ℝ) < Fintype.card (Fin (2 ^ j) → Fq t ht) := by positivity
  have hW : ((Fintype.card (Fin (D j) → Fq t ht) : ℕ) : ℝ) =
      ((Fintype.card (Fq t ht) ^ (Fintype.card (Fin (D j)) - 2 ^ j) : ℕ) : ℝ) *
        Fintype.card (Fin (2 ^ j) → Fq t ht) := by
    rw [← Nat.cast_mul, hc]
  rw [hW]
  have hq : (0 : ℝ) < ((Fintype.card (Fq t ht) ^ (Fintype.card (Fin (D j)) - 2 ^ j) : ℕ) : ℝ) :=
    by positivity
  field_simp
  rfl

end Points

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-- **From evaluations to polynomials**: two measurements of tuples of polynomials disagree at most
as often as their evaluations at the point of a uniform vector, plus `M d / q`. -/
theorem dis_le_avg_evalR_add {t : ℕ} {ht : 1 ≤ t} {j d k : ℕ} (hψ : ‖M.ψ‖ = 1)
    (P' : POVMIn (Fin k → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)) 𝒜)
    (Q' : POVMIn (Fin k → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)) ℬ) :
    M.dis P' Q' ≤ (∑ w : Fin (D j) → Fq t ht, M.dis (P'.map (evalR ((regs j).ptOf w)))
        (Q'.map (evalR ((regs j).ptOf w)))) / Fintype.card (Fin (D j) → Fq t ht)
      + ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht) := by
  have h := M.dis_le_sum_dis_map_add hψ P' Q' (ν := uniform (Fin (D j) → Fq t ht))
    (fun _ => by simp [uniform]) (by simp [uniform, Finset.card_univ])
    (fun w g => evalR ((regs j).ptOf w) g) (by positivity)
    fun g g' hg => sum_uniform_evalR_eq_le hg
  refine h.trans (le_of_eq ?_)
  simp only [uniform, ← Finset.mul_sum]
  rw [inv_mul_eq_div]

variable (t : ℕ) (ht : 1 ≤ t) (j d : ℕ) (L : PcpDims) in
/-- **The error of the agreement of a role's polynomials with the oracle's**, at typed failure
`θ`: the triangle's, then Schwartz–Zippel's. -/
def errP (r : Role) (θ : ℝ) : ℝ :=
  11 * (dS t ht j d L r (9 * θ) + 81 * θ + dS t ht j d L .oracle (9 * θ))
    + ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht)

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}
  (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B)) (hL : LIDT.Simul.SoundIn M)
  (hd : 1 ≤ d) (hP : ArSampler hM sel V n P)

/-- Averaging the per-seed bound of `dis_le_avg_evalR_add` over the seeds. -/
theorem sum_dis_le_of_evalR {k : ℕ} (hψ : ‖M.ψ‖ = 1)
    (PA' : V.Questions n → POVMIn (Fin k → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)) 𝒜)
    (QB' : V.Questions n → POVMIn (Fin k → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)) ℬ)
    {E : ℝ} (hE : ∑ z, ∑ w : Fin (D j) → Fq t ht, M.dis ((PA' z).map (evalR ((regs j).ptOf w)))
        ((QB' z).map (evalR ((regs j).ptOf w)))
      ≤ Fintype.card (V.Questions n) * (Fintype.card (Fin (D j) → Fq t ht) * E)) :
    ∑ z, M.dis (PA' z) (QB' z) ≤ Fintype.card (V.Questions n) *
      (E + ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht)) := by
  have hW : (0 : ℝ) < Fintype.card (Fin (D j) → Fq t ht) := by positivity
  calc ∑ z, M.dis (PA' z) (QB' z)
      ≤ ∑ z, ((∑ w : Fin (D j) → Fq t ht, M.dis ((PA' z).map (evalR ((regs j).ptOf w)))
          ((QB' z).map (evalR ((regs j).ptOf w)))) / Fintype.card (Fin (D j) → Fq t ht)
          + ((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht)) :=
        Finset.sum_le_sum fun z _ => dis_le_avg_evalR_add hψ _ _
    _ = (∑ z, ∑ w : Fin (D j) → Fq t ht, M.dis ((PA' z).map (evalR ((regs j).ptOf w)))
          ((QB' z).map (evalR ((regs j).ptOf w)))) / Fintype.card (Fin (D j) → Fq t ht)
          + Fintype.card (V.Questions n) * (((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht)) := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ ≤ Fintype.card (V.Questions n) * (Fintype.card (Fin (D j) → Fq t ht) * E)
          / Fintype.card (Fin (D j) → Fq t ht)
          + Fintype.card (V.Questions n) * (((2 ^ j : ℕ) : ℝ) * d / Fintype.card (Fq t ht)) := by
        gcongr
    _ = _ := by
        field_simp

include hP in
/-- **An isolated role's polynomials agree with the oracle's in its slots**, on average over the
seeds, up to `errP`. -/
theorem sum_dis_GAr_GBO_poly_le {r : Role} (hr : r ≠ .oracle) :
    ∑ z, M.dis (GA T hL hd r (oq V n r z))
        ((GB T hL hd .oracle (oq V n .oracle z)).map (restr L r))
      ≤ Fintype.card (V.Questions n) * errP t ht j d L r (1 - T.value) := by
  have h := sum_dis_GAr_GBO_le T hL hd hP hr
  have e : ∀ z w, ((GB T hL hd .oracle (oq V n .oracle z)).map (restr L r)).map
      (evalR ((regs j).ptOf w)) = (GB T hL hd .oracle (oq V n .oracle z)).map
        fun f => evalR ((regs j).ptOf w) (restr L r f) := fun z w => by
    rw [POVMIn.map_map]
  have h' := sum_dis_le_of_evalR T.ψ_unit (fun z => GA T hL hd r (oq V n r z))
    (fun z => (GB T hL hd .oracle (oq V n .oracle z)).map (restr L r))
    (E := 11 * (dS t ht j d L r (9 * (1 - T.value)) + 81 * (1 - T.value) +
      dS t ht j d L .oracle (9 * (1 - T.value)))) (by
      simp only [e]
      refine h.trans (le_of_eq ?_)
      ring)
  refine h'.trans (le_of_eq ?_)
  rw [errP]

include hP in
/-- **The oracle's polynomials in an isolated role's slots agree with the role's**, on average
over the seeds, up to `errP`. -/
theorem sum_dis_GAO_GBr_poly_le {r : Role} (hr : r ≠ .oracle) :
    ∑ z, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map (restr L r))
        (GB T hL hd r (oq V n r z))
      ≤ Fintype.card (V.Questions n) * errP t ht j d L r (1 - T.value) := by
  have h := sum_dis_GAO_GBr_le T hL hd hP hr
  have e : ∀ z w, ((GA T hL hd .oracle (oq V n .oracle z)).map (restr L r)).map
      (evalR ((regs j).ptOf w)) = (GA T hL hd .oracle (oq V n .oracle z)).map
        fun f => evalR ((regs j).ptOf w) (restr L r f) := fun z w => by
    rw [POVMIn.map_map]
  have h' := sum_dis_le_of_evalR T.ψ_unit
    (fun z => (GA T hL hd .oracle (oq V n .oracle z)).map (restr L r))
    (fun z => GB T hL hd r (oq V n r z))
    (E := 11 * (dS t ht j d L r (9 * (1 - T.value)) + 81 * (1 - T.value) +
      dS t ht j d L .oracle (9 * (1 - T.value)))) (by
      simp only [e]
      refine h.trans (le_of_eq ?_)
      ring)
  refine h'.trans (le_of_eq ?_)
  rw [errP]

end MIPRE.Tailored.AnsRed.Typed

end
