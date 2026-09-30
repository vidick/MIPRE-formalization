/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.ConditionalConsistency
public import MIPRE.Foundations.Introspection.TypedEstimates

@[expose] public section

/-! # The conditional estimate for the actual adjacent hiding test

The earlier answer is processed using the question reported in the later
answer. This is a conditional measurement, not a single fixed coarse-graining.
The resulting estimate is derived from the parsed game and its actual uniform
ordered-edge law, including the malformed-answer outcomes.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`).
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

section Conditional

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {A B Y Z : Type*} [Fintype A] [Fintype B] [DecidableEq B]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- Squared error of the conditional coarse comparison, retaining Bob's
conditioning index and summing every coarse outcome. -/
def conditionalCoarseDistance (M : POVMIn A 𝒜) (N : POVMIn B ℬ)
    (f : Y → A → Z) (g : B → Y × Z) : ℝ :=
  ∑ p : Y × Z, Ψ.snorm
    (Ψ.πB ((N.map g).op p) -
      Ψ.πA ((M.map (f p.1)).op p.2) * Ψ.πB (∑ z, (N.map g).op (p.1, z))) ^ 2

/-- Data processing when Alice's outcome map depends on a retained part of
Bob's outcome. The dependency remains inside the Born sum. -/
theorem conditional_bornProb_map (M : POVMIn A 𝒜) (N : POVMIn B ℬ)
    (f : Y → A → Z) (g : B → Y × Z) :
    (∑ p : Y × Z, Ψ.bornProb ((M.map (f p.1)).op p.2) ((N.map g).op p)) =
    ∑ b, ∑ a, (if f (g b).1 a = (g b).2 then (1 : ℝ) else 0) *
      Ψ.bornProb (M.op a) (N.op b) := by
  calc
    _ = ∑ p : Y × Z, ∑ b ∈ univ.filter (fun b => g b = p),
        Ψ.bornProb ((M.map (f (g b).1)).op (g b).2) (N.op b) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [POVMIn.map_op g N p, Ψ.bornProb_sum_right]
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Finset.mem_filter.mp hb).2]
    _ = ∑ b, Ψ.bornProb ((M.map (f (g b).1)).op (g b).2) (N.op b) :=
      Finset.sum_fiberwise _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [POVMIn.map_op, Ψ.bornProb_sum_left, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp

/-- Conditional consistency for an actual pair of measurements and explicit
outcome maps. The acceptance premise is solely a scalar tested probability. -/
theorem conditional_coarse_consistency (hΨ : ‖Ψ.ψ‖ = 1)
    (M : POVMIn A 𝒜) (N : POVMIn B ℬ) (hN : IsPVMIn N.op)
    (f : Y → A → Z) (g : B → Y × Z) (test : A → B → Bool)
    {δ : ℝ}
    (hwin : 1 - δ ≤ ∑ a, ∑ b,
      (if test a b = true then (1 : ℝ) else 0) * Ψ.bornProb (M.op a) (N.op b))
    (hcheck : ∀ a b, test a b = true → f (g b).1 a = (g b).2) :
    conditionalCoarseDistance Ψ M N f g ≤ 2 * δ := by
  let P (p : Y × Z) := (N.map g).op p
  let R y := ∑ z, P (y, z)
  let C (p : Y × Z) : 𝒞 := Ψ.πA ((M.map (f p.1)).op p.2) * Ψ.πB (R p.1)
  have hP : IsPVMIn P := by
    rw [show P = _ from funext (POVMIn.map_op g N)]
    exact hN.coarse g
  have hR : IsPVMIn R := hP.marg_left
  have hCsa p : star (C p) = C p := by
    simp only [C, star_mul, ← map_star, POVMIn.star_op, hR.star_eq]
    exact (Ψ.commute _ _).eq.symm
  have hC0 p : 0 ≤ Ψ.π (C p) := by
    have hc : Commute (Ψ.π (Ψ.πA ((M.map (f p.1)).op p.2))) (Ψ.π (Ψ.πB (R p.1))) :=
      (Ψ.commute _ _).map Ψ.π
    simp only [C, map_mul]
    exact hc.mul_nonneg (Ψ.π_πA_nonneg (POVMIn.op_nonneg _ _)) (Ψ.π_πB_nonneg (hR.nonneg _))
  have hCsum : ∑ p, Ψ.π (C p) ≤ 1 := by
    apply le_of_eq
    rw [← map_sum]
    simp only [C, Fintype.sum_prod_type, ← Finset.sum_mul, ← map_sum, POVMIn.sum_op, map_one,
      one_mul]
    rw [hR.sum_eq_one, map_one, map_one]
  have hprod p : Ψ.πB (P p) * C p = Ψ.πA ((M.map (f p.1)).op p.2) * Ψ.πB (P p) := by
    obtain ⟨y, z⟩ := p
    dsimp only [C, R]
    rw [← mul_assoc, ← (Ψ.commute _ _).eq, mul_assoc, ← map_mul, joint_mul_marginal hP]
  have hdist := submeasurement_agreement_dist Ψ.toStateModel hΨ (fun p => Ψ.πB (P p)) C
    (hP.map Ψ.πB) hCsa hC0 hCsum
  have heq p : Ψ.qform (Ψ.πB (P p) * C p) =
      Ψ.bornProb ((M.map (f p.1)).op p.2) (P p) := by
    rw [hprod]
    rfl
  simp_rw [heq] at hdist
  have hagree : 1 - δ ≤ ∑ p : Y × Z,
      Ψ.bornProb ((M.map (f p.1)).op p.2) (P p) := by
    rw [show (∑ p : Y × Z, Ψ.bornProb ((M.map (f p.1)).op p.2) (P p)) =
      ∑ b, ∑ a, (if f (g b).1 a = (g b).2 then (1 : ℝ) else 0) *
        Ψ.bornProb (M.op a) (N.op b) from conditional_bornProb_map Ψ M N f g]
    refine hwin.trans ?_
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro a _
    by_cases h : test a b = true
    · rw [ite_eq_left h, ite_eq_left (hcheck a b h)]
    · rw [ite_eq_right h, zero_mul]
      exact mul_nonneg (by split_ifs <;> norm_num)
        (Ψ.bornProb_nonneg (M.op_nonneg a) (N.op_nonneg b))
  exact hdist.trans (by linarith)

end Conditional

namespace CLChecks

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Projecting an arbitrary claimed prefix recovers its first branch and the
remaining claimed prefix. No image-membership hypothesis is needed. -/
theorem proj_outputPrefix_cons {S T : Finset ι} {L : CL.RegLinear F S}
    {next : (ι → F) → CL.CLFun F ι ℓ}
    (hP : (CL.CLFun.cons S L next).SupportedOn T) (k : ℕ) (y : ι → F) :
    CL.proj S ((CL.CLFun.cons S L next).outputPrefix (k + 1) y) = CL.proj S y ∧
    CL.proj Sᶜ ((CL.CLFun.cons S L next).outputPrefix (k + 1) y) =
      (next (CL.proj S y)).outputPrefix k (CL.proj Sᶜ y) := by
  have hsub : prefixRegister (next (CL.proj S y)) k (CL.proj Sᶜ y) ⊆ Sᶜ := by
    intro i hi
    exact mem_compl.mpr (mem_sdiff.mp (prefixRegister_subset (hP.2 _) k _ hi)).2
  have hd : Disjoint S (prefixRegister (next (CL.proj S y)) k (CL.proj Sᶜ y)) :=
    disjoint_of_subset_right hsub disjoint_compl_right
  have hrest := proj_prefixRegister (hP.2 (CL.proj S y)) k (CL.proj Sᶜ y)
  rw [CL.CLFun.outputPrefix_cons]
  constructor
  · rw [map_add, CL.proj_proj_self, ← hrest, CL.proj_proj_of_disjoint hd, add_zero]
  · rw [map_add, CL.proj_proj_of_disjoint disjoint_compl_left, zero_add,
      ← hrest, CL.proj_proj_of_subset' hsub]

/-- The register of the next stage is already fixed by the reported prefix. -/
theorem prefixRegister_outputPrefix_succ {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    prefixRegister P (k + 1) (P.outputPrefix k y) = prefixRegister P (k + 1) y := by
  induction P generalizing T k y with
  | zero => simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := proj_outputPrefix_cons hP k y
      simp only [prefixRegister]
      rw [hfirst, hrest, ih _ (hP.2 _) k _]

/-- The next dual readout depends only on the preceding reported prefix. -/
theorem dualReadout_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y x : ι → F) :
    dualReadout P k (P.outputPrefix k y) x = dualReadout P k y x := by
  induction P generalizing T k y with
  | zero => simp [dualReadout]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := proj_outputPrefix_cons hP k y
      simp only [dualReadout]
      rw [hfirst, hrest, ih _ (hP.2 _) k _]

end CLChecks

namespace TypedEstimates

section Parsed

variable {PauliType PauliAnswer F ι κ A : Type*}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- Retain exactly the later hiding answer's preceding question prefix as
the conditioning index. Malformed answers retain a separate index. -/
def hidingNextCondition (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option (ι → F)
  | .hide y _ _ => some (P.outputPrefix (k + 1) y)
  | _ => none

/-- Process the earlier answer using the later reported question. The output
retains the earlier prefix, the new dual readout, and the untouched tail. -/
def hidingNextEarlier (P : CL.CLFun F ι ℓ) (k : ℕ) (v : Option (ι → F)) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × (ι → F) × (ι → F))
  | .hide y _ x => v.map fun z =>
      (P.outputPrefix k y, CLChecks.dualReadout P (k + 1) z x,
        CL.proj (CLChecks.prefixRegister P (k + 2) z)ᶜ x)
  | _ => none

/-- The actual coarse later answer. Both the factor for the new dual output
and the tail projector use that answer's own reported question. -/
def hidingNextLater (P : CL.CLFun F ι ℓ) (k : ℕ)
    (a : ParsedAnswer (ι → F) A PauliAnswer) :
    Option (ι → F) × Option ((ι → F) × (ι → F) × (ι → F)) :=
  (hidingNextCondition P k a, match a with
    | .hide y yp x => some
        (P.outputPrefix k y,
          CL.proj (P.factorOfPrefix (k + 1) (P.outputPrefix (k + 1) y)) yp,
          CL.proj (CLChecks.prefixRegister P (k + 2) y)ᶜ x)
    | _ => none)

/-- The parsed adjacent-hiding check supplies the conditional accepted-answer
relation; no condition on honestly sampled or in-image answers is imposed. -/
theorem hiding_next_accepts_conditional
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
    hidingNextEarlier (L w) k.val (hidingNextLater (L w) k.val b).1 a =
      (hidingNextLater (L w) k.val b).2 := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a with
  | pauli a => simp [TypedPredicate.fits] at hf
  | pair y a => simp [TypedPredicate.fits] at hf
  | read y yp a => simp [TypedPredicate.fits] at hf
  | hide y yp x =>
    cases b with
    | pauli b => simp [TypedPredicate.fits] at hf
    | pair z b => simp [TypedPredicate.fits] at hf
    | read z zp b => simp [TypedPredicate.fits] at hf
    | hide z zp t =>
      have hc := TypedPredicate.check_hiding_next L X Z projectPauli D DP w k j hk h
      simp only [hidingNextEarlier, hidingNextLater, hidingNextCondition, Option.map_some,
        CLChecks.dualReadout_outputPrefix hL,
        show k.val + 2 = (k.val + 1) + 1 by omega,
        CLChecks.prefixRegister_outputPrefix_succ hL]
      exact congrArg some (Prod.ext hc.1 (Prod.ext hc.2.2.2.symm hc.2.2.1))

/-- **Actual adjacent-hiding conditional estimate.** The source induction's
first step follows from the parsed verifier with error `2 |E| ε`. Alice's
coarse measurement depends on Bob's retained question; Bob's marginal is the
sum over all tested coarse answers. This is not an unconditional marginal
distance and does not assume the later ideal hiding form. -/
theorem hiding_next_conditional_estimate
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ψ : BipartiteModel 𝒞 𝒜 ℬ) (hΨ : ‖Ψ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) 𝒜)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) ℬ)
    {ε : ℝ} (hfail : 1 - Ψ.povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤ ε)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    (hMB : IsPVMIn (MB (QuestionType.hide w j, 0)).op) :
    conditionalCoarseDistance Ψ (MA (QuestionType.hide w k, 0)) (MB (QuestionType.hide w j, 0))
      (hidingNextEarlier (L w) k.val) (hidingNextLater (L w) k.val) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  let G := parsedGame E X Z P L projectPauli D DP
  let q : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (QuestionType.hide w k, 0)
  let r : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (QuestionType.hide w j, 0)
  have hterm := Ψ.sum_mul_condFail_le (G := G) (MA := MA) (MB := MB) hΨ hfail {(q, r)}
  simp only [sum_singleton] at hterm
  change (TypedPresentation.game E X Z ℓ P (questionCheck L X Z projectPauli D DP)).μ
    (.inr (.hide k, w), 0) (.inr (.hide j, w), 0) * Ψ.condFail G MA MB q r ≤ ε at hterm
  rw [TypedPresentation.mu_aux E X Z P (questionCheck L X Z projectPauli D DP)
    (.hide k) (.hide j) w w (TypeGraph.adj_hide_next E X Z w k j hk), inv_mul_eq_div] at hterm
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hcond := (div_le_iff₀ hc).mp hterm
  have hwin : 1 - (TypeGraph.edges E X Z ℓ).card * ε ≤ Ψ.condWin G MA MB q r := by
    unfold BipartiteModel.condFail at hcond
    nlinarith
  have h := conditional_coarse_consistency Ψ hΨ (MA q) (MB r) hMB (hidingNextEarlier (L w) k.val) (hidingNextLater (L w) k.val)
    (G.D q r)
    (δ := (TypeGraph.edges E X Z ℓ).card * ε)
    hwin
    (fun a b hab => hiding_next_accepts_conditional L X Z projectPauli D
      (fun p s => DP p s 0 0) w k j hk hL hab)
  dsimp only [q, r] at h
  exact h.trans_eq (mul_assoc (2 : ℝ) (TypeGraph.edges E X Z ℓ).card ε).symm

end Parsed

end TypedEstimates

end MIPRE.Introspection

end

end
