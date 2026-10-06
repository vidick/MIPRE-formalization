/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.SoundIndiff

@[expose] public section

/-!
# Soundness of the answer-reduced game: the proof check

The proof check (II:10491, check 4) at the oracle's point question, read on the oracle's
polynomials (II:10697): the outcomes of Alice's polynomial measurement at the oracle whose
evaluations pass the thirteen checks on at most a fraction `m (5 + 6(d + 1)) / q` of the points
(`Dense` fails) weigh at most twice the extraction's error plus the failure at the type pair
`(O, Point), (O, Point)` (`badDense_le`, `sum_badDense_le`). An outcome's evaluations at a point
pass whenever Bob's point answer passes and agrees with them (`sum_ite_read_le`), and the typed
data checks Bob's point answer (`passV_of_arDt`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset MIPRE.CL MIPRE.SAT MIPRE.LIDT

section Defs

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} (L : PcpDims) (hLM : L.m ≤ 2 ^ j)

/-- The oracle's codeword in a slot. -/
def ocs (s : Slot L) : Fin (slotsOf L .oracle).length := ⟨idxO s, idxO_lt s⟩

/-- **The proof check on a tuple of the oracle's values** at the point `u`, for the circuit's
polynomial `Tc`. -/
def PassV (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (u : Fin (2 ^ j) → Fq t ht)
    (v : Fin (slotsOf L .oracle).length → Fq t ht) : Prop :=
  PassesV Tc (fun s => v (ocs L s)) (ptm L hLM u)

open Classical in
/-- **An outcome of the oracle passes the proof check densely**: its evaluations pass at more than
a fraction `m (5 + 6(d + 1)) / q` of the points, the threshold of the PCP's soundness
(`accepts_of_dense`). -/
def Dense (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (f : PolyR t ht j d L .oracle) : Prop :=
  (L.m : ℝ) * chkDeg 5 d / Fintype.card (Fq t ht) <
    ((univ.filter fun u => PassV L hLM Tc u (evalR u f)).card : ℝ) /
      Fintype.card (Fin (2 ^ j) → Fq t ht)

end Defs

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}

/-- **The proof check** of the second answer at the oracle's point question. -/
theorem passV_of_arDt {z : V.Questions n} {x : Fin (2 ^ j) → Fq t ht} {a b : Verifier.Answers B}
    (h : arDt d hM sel L hLM V n Cc hm B (arQr sel _ .oracle (oq V n .oracle z) (.point x))
      (arQr sel _ .oracle (oq V n .oracle z) (.point x)) a b = true) :
    PassV L hLM (circOf L V n Cc hm z) x (pvR t ht j d L .oracle b) := by
  have h6 := (arPred_of_arDt h).2.2.2.2.2 rfl
  rw [ldQ_arQr, rolePart_arQr] at h6
  exact h6

variable (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B)) (hL : LIDT.Simul.SoundIn M)
  (hd : 1 ≤ d) (hP : ArSampler hM sel V n P)

open Classical in
/-- **Where Alice's polynomials fail the proof check**, at one seed: at most the extraction's
error and the failure at the type pair `(O, Point), (O, Point)`. -/
theorem sum_notPass_le (z : V.Questions n) :
    ∑ w : Fin (D j) → Fq t ht, ∑ f, (if ¬PassV L hLM (circOf L V n Cc hm z) ((regs j).ptOf w)
        (evalR ((regs j).ptOf w) f)
        then M.bornProb ((GA T hL hd .oracle (oq V n .oracle z)).op f) 1 else 0)
      ≤ ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map (evalR ((regs j).ptOf w)))
          ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
            (pvR t ht j d L .oracle))
        + ∑ w, edgeFail T ((.oracle, .point), (.oracle, .point)) z w := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  refine (sum_ite_read_le M T.ψ_unit _ _ (evalR ((regs j).ptOf w)) (pvR t ht j d L .oracle)
    (fun v => ¬PassV L hLM (circOf L V n Cc hm z) ((regs j).ptOf w) v)).trans
    (add_le_add le_rfl ?_)
  exact M.sum_ite_bornProb_le_condFail T.ψ_unit
    (fun b => ¬PassV L hLM (circOf L V n Cc hm z) ((regs j).ptOf w) (pvR t ht j d L .oracle b))
    fun a b h hb => hb (passV_of_arDt (x := (regs j).ptOf w) h)

open Classical in
/-- **The oracle outcomes of Alice that pass the proof check sparsely**, at one seed: at most twice
the errors of `sum_notPass_le`, per vector, once the field has `2 m (5 + 6(d + 1))`
elements. -/
theorem badDense_le (hτ : 2 * (L.m * chkDeg 5 d) ≤ Fintype.card (Fq t ht))
    (z : V.Questions n) :
    ∑ f, (if Dense L hLM (circOf L V n Cc hm z) f then 0
        else M.bornProb ((GA T hL hd .oracle (oq V n .oracle z)).op f) 1)
      ≤ 2 / Fintype.card (Fin (D j) → Fq t ht) *
        (∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map (evalR ((regs j).ptOf w)))
          ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
            (pvR t ht j d L .oracle))
        + ∑ w, edgeFail T ((.oracle, .point), (.oracle, .point)) z w) := by
  set G := GA T hL hd .oracle (oq V n .oracle z)
  set Tc : MvPolynomial (Fin L.m) (Fq t ht) := circOf L V n Cc hm z
  have hW0 : (0 : ℝ) < Fintype.card (Fin (D j) → Fq t ht) := by positivity
  have hq0 : (0 : ℝ) < Fintype.card (Fq t ht) := by positivity
  -- an outcome passing sparsely fails at at least half the vectors
  have hhalf : ∀ f : PolyR t ht j d L .oracle, ¬Dense L hLM Tc f →
      (Fintype.card (Fin (D j) → Fq t ht) : ℝ) / 2 ≤ ∑ w : Fin (D j) → Fq t ht,
        (if ¬PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f) then 1 else 0) := by
    intro f hf
    have hc := LIDT.CL.Regs.card_mul_card_points (regs j) (F := Fq t ht)
    have hs := LIDT.CL.Regs.sum_ptOf (regs j)
      (fun u => (if PassV L hLM Tc u (evalR u f) then (1 : ℝ) else 0))
    simp only [Finset.sum_boole] at hs
    have hcompl : ∑ w : Fin (D j) → Fq t ht,
        (if ¬PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f) then (1 : ℝ) else 0)
        = Fintype.card (Fin (D j) → Fq t ht) - ∑ w : Fin (D j) → Fq t ht,
          (if PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f) then 1 else 0) := by
      have e : ∀ w : Fin (D j) → Fq t ht,
          (if ¬PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f) then (1 : ℝ) else 0)
          = 1 - (if PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f)
            then 1 else 0) := fun w => by
        by_cases h : PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f) <;> simp [h]
      simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
    rw [hcompl]
    simp only [Finset.sum_boole]
    rw [hs, nsmul_eq_mul]
    have hτ' : (L.m : ℝ) * chkDeg 5 d / Fintype.card (Fq t ht) ≤ 1 / 2 := by
      rw [div_le_iff₀ hq0]
      have : ((2 * (L.m * chkDeg 5 d) : ℕ) : ℝ) ≤ Fintype.card (Fq t ht) := by
        exact_mod_cast hτ
      push_cast at this
      linarith
    have hd' : ((univ.filter fun u => PassV L hLM Tc u (evalR u f)).card : ℝ)
        ≤ Fintype.card (Fin (2 ^ j) → Fq t ht) / 2 := by
      have hP0 : (0 : ℝ) < Fintype.card (Fin (2 ^ j) → Fq t ht) := by positivity
      have := not_lt.mp hf
      rw [div_le_iff₀ hP0] at this
      nlinarith
    have hWc : (Fintype.card (Fin (D j) → Fq t ht) : ℝ) =
        ((Fintype.card (Fq t ht) ^ (Fintype.card (Fin (D j)) - 2 ^ j) : ℕ) : ℝ) *
          Fintype.card (Fin (2 ^ j) → Fq t ht) := by
      rw [← Nat.cast_mul, hc]
    rw [hWc]
    have hm0 : (0 : ℝ) ≤ ((Fintype.card (Fq t ht) ^ (Fintype.card (Fin (D j)) - 2 ^ j) : ℕ) : ℝ) :=
      by positivity
    nlinarith
  have hsum := sum_notPass_le T hL hd z (hLM := hLM) (Cc := Cc) (hm := hm)
  have hswap : ∑ w : Fin (D j) → Fq t ht, ∑ f,
      (if ¬PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f)
        then M.bornProb (G.op f) 1 else 0)
      = ∑ f, M.bornProb (G.op f) 1 * ∑ w : Fin (D j) → Fq t ht,
        (if ¬PassV L hLM Tc ((regs j).ptOf w) (evalR ((regs j).ptOf w) f) then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_ite, mul_one, mul_zero]
  rw [hswap] at hsum
  have hle : (Fintype.card (Fin (D j) → Fq t ht) : ℝ) / 2 *
      ∑ f, (if Dense L hLM Tc f then 0 else M.bornProb (G.op f) 1)
      ≤ ∑ w, M.dis (G.map (evalR ((regs j).ptOf w)))
          ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
            (pvR t ht j d L .oracle))
        + ∑ w, edgeFail T ((.oracle, .point), (.oracle, .point)) z w := by
    refine le_trans ?_ hsum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    have hβ := M.bornProb_nonneg (G.op_nonneg f) zero_le_one
    by_cases hg : Dense L hLM Tc f
    · rw [ite_eq_left hg, mul_zero]
      exact mul_nonneg hβ (Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num)
    · rw [ite_eq_right hg, mul_comm]
      exact mul_le_mul_of_nonneg_left (hhalf f hg) hβ
  have hpos : (0 : ℝ) < (Fintype.card (Fin (D j) → Fq t ht) : ℝ) / 2 := by positivity
  rw [← le_div_iff₀' hpos] at hle
  refine hle.trans (le_of_eq ?_)
  field_simp

include hP in
open Classical in
/-- **The oracle outcomes of Alice that pass the proof check sparsely**, averaged over the seeds:
at most twice the extraction's error plus `162` times the typed failure. -/
theorem sum_badDense_le (hτ : 2 * (L.m * chkDeg 5 d) ≤ Fintype.card (Fq t ht)) :
    ∑ z, ∑ f, (if Dense L hLM (circOf L V n Cc hm z) f then 0
        else M.bornProb ((GA T hL hd .oracle (oq V n .oracle z)).op f) 1)
      ≤ Fintype.card (V.Questions n) * (2 * dS t ht j d L .oracle (9 * (1 - T.value))
        + 162 * (1 - T.value)) := by
  have hW0 : (0 : ℝ) < Fintype.card (Fin (D j) → Fq t ht) := by positivity
  have hE2 := sum_dis_GA_MB_le T hL hd hP .oracle
  have hF := sum_edge_le T hP ((.oracle, .point), (.oracle, .point))
  calc _ ≤ ∑ z, 2 / Fintype.card (Fin (D j) → Fq t ht) *
          (∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
              (evalR ((regs j).ptOf w)))
            ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
              (pvR t ht j d L .oracle))
          + ∑ w, edgeFail T ((.oracle, .point), (.oracle, .point)) z w) :=
        Finset.sum_le_sum fun z _ => badDense_le T hL hd hτ z
    _ = 2 / Fintype.card (Fin (D j) → Fq t ht) *
          (∑ z, ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
              (evalR ((regs j).ptOf w)))
            ((T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
              (pvR t ht j d L .oracle))
          + ∑ z, ∑ w, edgeFail T ((.oracle, .point), (.oracle, .point)) z w) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 / Fintype.card (Fin (D j) → Fq t ht) *
          (Fintype.card (V.Questions n) * (Fintype.card (Fin (D j) → Fq t ht) *
            dS t ht j d L .oracle (9 * (1 - T.value)))
          + 81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht)) *
            (1 - T.value)) := by
        gcongr
    _ = _ := by
        field_simp
        ring

end MIPRE.Tailored.AnsRed.Typed

end
