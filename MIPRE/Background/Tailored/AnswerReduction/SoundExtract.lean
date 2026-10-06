/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.SoundSetup

@[expose] public section

/-!
# Soundness of the answer-reduced game: the polynomial measurements

The soundness of the seeded low-degree test in the model (`LIDT.Simul.SoundIn`), applied to each
per-role strategy of `SoundSetup` (II:10623, the first perturbation): at each role `r` and
oracularized question `y`, projective measurements `GA r y`, `GB r y` of tuples of polynomials of
individual degree at most `d` in `M = 2^j` variables, one per codeword of the role, whose
evaluations at a uniform point are consistent with the role's point answers, and which are
consistent with each other, up to `δ_sim` of the per-role failure (`extR_spec`).

Averaged over the seeds of the input sampler, the error is at most `δ_sim` of `9` times the typed
failure (`sum_deltaSimR_le`), by Jensen's inequality (`LIDT.Simul.sum_deltaSim_le`).
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset MIPRE.CL MIPRE.SAT MIPRE.LIDT

variable (t : ℕ) (ht : 1 ≤ t) (j d : ℕ) (L : PcpDims) in
/-- The outcomes of a role's polynomial measurement: a polynomial of individual degree at most
`d` in `2^j` variables for each of the role's codewords. -/
abbrev PolyR (r : Role) : Type :=
  Fin (slotsOf L r).length → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)

variable (t : ℕ) (ht : 1 ≤ t) (j d : ℕ) (L : PcpDims) in
/-- The error of the seeded test's soundness at a role, as a function of its failure. -/
abbrev dS (r : Role) (ε : ℝ) : ℝ :=
  Simul.deltaSim (Fintype.card (Fq t ht)) (2 ^ j) d (slotsOf L r).length ε

theorem card_fq {t : ℕ} (ht : 1 ≤ t) : Fintype.card (Fq t ht) = 2 ^ t :=
  (shoupBinField t ht).card_carrier

theorem one_le_length_slotsOf (L : PcpDims) (r : Role) : 1 ≤ (slotsOf L r).length := by
  cases r <;> simp [slotsOf, rOf, lOf, rSlots]

theorem dS_nonneg {t : ℕ} (ht : 1 ≤ t) (j d : ℕ) (L : PcpDims) (r : Role) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ dS t ht j d L r ε :=
  Simul.deltaSim_nonneg _ _ _ _ hε

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}
  (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B)) (hL : LIDT.Simul.SoundIn M)
  (hd : 1 ≤ d)

/-- The failure of the per-role strategy at role `r` and oracularized question `y`. -/
def epsR (r : Role) (y : V.Questions n) : ℝ := 1 - (roleStrat T r y).value

theorem epsR_nonneg (r : Role) (y : V.Questions n) : 0 ≤ epsR T r y :=
  sub_nonneg.mpr (BipartiteModel.ProjStrat.value_le_one _)

include hL hd in
theorem exists_extR (r : Role) (y : V.Questions n) :
    ∃ GA : POVMIn (PolyR t ht j d L r) 𝒜, ∃ GB : POVMIn (PolyR t ht j d L r) ℬ,
      IsPVMIn GA.op ∧ IsPVMIn GB.op ∧
      M.inconsistency (uniform (Fin (2 ^ j) → Fq t ht))
          (Simul.tuplePOVMAIn hM (roleStrat T r y)) (Simul.evalTuplePOVMIn GB)
          ≤ dS t ht j d L r (epsR T r y)
        ∧ M.inconsistency (uniform (Fin (2 ^ j) → Fq t ht)) (Simul.evalTuplePOVMIn GA)
          (Simul.tuplePOVMBIn hM (roleStrat T r y)) ≤ dS t ht j d L r (epsR T r y)
        ∧ M.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
          ≤ dS t ht j d L r (epsR T r y) :=
  hL (card_fq ht) hM hd (one_le_length_slotsOf L r) (roleStrat T r y) _ (epsR_nonneg T r y)
    (by rw [epsR]; linarith)

/-- **Alice's polynomial measurement** at role `r` and oracularized question `y`. -/
def GA (r : Role) (y : V.Questions n) : POVMIn (PolyR t ht j d L r) 𝒜 :=
  (exists_extR T hL hd r y).choose

/-- **Bob's polynomial measurement** at role `r` and oracularized question `y`. -/
def GB (r : Role) (y : V.Questions n) : POVMIn (PolyR t ht j d L r) ℬ :=
  (exists_extR T hL hd r y).choose_spec.choose

/-- The polynomial measurements are projective. -/
theorem extR_proj (r : Role) (y : V.Questions n) :
    IsPVMIn (GA T hL hd r y).op ∧ IsPVMIn (GB T hL hd r y).op :=
  ⟨(exists_extR T hL hd r y).choose_spec.choose_spec.1,
    (exists_extR T hL hd r y).choose_spec.choose_spec.2.1⟩

/-- **The three conclusions** of the seeded test's soundness at role `r` and question `y`. -/
theorem extR_spec (r : Role) (y : V.Questions n) :
    M.inconsistency (uniform (Fin (2 ^ j) → Fq t ht))
        (Simul.tuplePOVMAIn hM (roleStrat T r y)) (Simul.evalTuplePOVMIn (GB T hL hd r y))
        ≤ dS t ht j d L r (epsR T r y)
      ∧ M.inconsistency (uniform (Fin (2 ^ j) → Fq t ht))
        (Simul.evalTuplePOVMIn (GA T hL hd r y)) (Simul.tuplePOVMBIn hM (roleStrat T r y))
        ≤ dS t ht j d L r (epsR T r y)
      ∧ M.inconsistency (uniform Unit) (fun _ => GA T hL hd r y) (fun _ => GB T hL hd r y)
        ≤ dS t ht j d L r (epsR T r y) :=
  (exists_extR T hL hd r y).choose_spec.choose_spec.2.2

/-- **The averaged error of the seeded test's soundness** at a role: at most `δ_sim` of `9` times
the typed failure. -/
theorem sum_deltaSimR_le (hP : ArSampler hM sel V n P) (r : Role) :
    ∑ z, dS t ht j d L r (epsR T r (oq V n r z))
      ≤ Fintype.card (V.Questions n) * dS t ht j d L r (9 * (1 - T.value)) :=
  Simul.sum_deltaSim_le _ _ _ _ _ (fun _ => epsR_nonneg T _ _)
    (sum_one_sub_value_roleStrat_le T hP r)

end MIPRE.Tailored.AnsRed.Typed

end
