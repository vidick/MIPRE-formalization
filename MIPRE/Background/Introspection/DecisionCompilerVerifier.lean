/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionCompilerTime
import MIPRE.Background.Introspection.PauliSamplerTotal

/-! # The compiled five-level verifier and its complete resource contract -/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost

theorem graphDim_label : CL.Detyping.graphDim DecisionKernel.Label =
    4*(Fintype.card QLD.Ty+2*7+6) := by
  simp only [CL.Detyping.graphDim, CL.Graph.Coord, DecisionKernel.Label,
    Fintype.card_prod, Fintype.card_bool, QuestionType.card]
  omega

def output (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (source : Prog × Prog) (lam : ℕ) : Verifier 5 where
  sampler := PauliSampler.finalSampler c hc he 7 lam
  decider := decider c U source.1 source.2 lam
  accepts_length n x y a b h := by
    by_cases hz : lam = 0 ∨ n = 0
    · have hh := (accepts_zero c U source.1 source.2 lam n hz x y a b).mp h
      have hzero : lam*n = 0 := by rcases hz with hz | hz <;> simp [hz]
      rw [PauliSampler.finalSampler_dim_zero c hc he 7 lam n hzero, hh.1, hh.2.1]
      exact ⟨rfl,rfl⟩
    · have hh := accepts_positive_bounds c U source.1 source.2
        (by omega : 1 ≤ lam) (by omega : 1 ≤ n) x y a b h
      rw [PauliSampler.finalSampler_dim_pos c hc he 7 lam n (by omega) (by omega),
        PauliSampler.fullSampler_dim]
      simpa only [graphDim_label, PauliSampler.dimension] using
        (show x.length = _ ∧ y.length = _ from ⟨hh.1,hh.2.1⟩)

@[simp] theorem output_sampler (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) (lam : ℕ) :
    (output c hc he U source lam).sampler = PauliSampler.finalSampler c hc he 7 lam := rfl

@[simp] theorem output_decider (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (U : ClockedUniversalMachine) (source : Prog × Prog) (lam : ℕ) :
    (output c hc he U source lam).decider.prog = compute c U (source,lam) := rfl

/-- All compiler inputs and all indices satisfy the pipeline's exact `Within`
contract, with the same fixed exponent also bounding output descriptions. -/
theorem resources_with_cutoff (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine) :
    ∃ C, (∀ source lam n, (output c hc he U source lam).Within n (budget C lam n)) ∧
      (∀ source lam, (output c hc he U source lam).decider.size ≤ C*(lam+1)^C) ∧
      ∀ lam n, cutoffAt c lam n ≤ ansBound C lam n := by
  obtain ⟨Cs,hs⟩ := PauliSampler.finalSampler_uniform_bound c hc he 7
  obtain ⟨Cd,hd⟩ := time_bound hc U
  obtain ⟨Ca,ha⟩ := cutoffAt_ansBound hc
  obtain ⟨Cl,_,hl⟩ := compute_size c U
  let C := Cs+Cd+Ca+Cl
  have hCs : Cs ≤ C := by dsimp [C]; omega
  have hCd : Cd ≤ C := by dsimp [C]; omega
  have hCa : Ca ≤ C := by dsimp [C]; omega
  have hCl : Cl ≤ C := by dsimp [C]; omega
  have hpow (lam n : ℕ) {i : ℕ} (hi : i ≤ C) : (lam*n+1)^i ≤ (lam*n+1)^C :=
    Nat.pow_le_pow_right (by omega) hi
  have hans (lam n : ℕ) {i : ℕ} (hi : i ≤ C) : ansBound i lam n ≤ ansBound C lam n :=
    Nat.pow_le_pow_right (by decide) (hpow lam n hi)
  refine ⟨C,?_,?_,?_⟩
  · rintro ⟨S,D⟩ lam n
    obtain ⟨hst,hsd⟩ := hs lam n
    refine ⟨hst.mono (hpow lam n hCs) hCs,hsd.trans (hpow lam n hCs),
      (hd S D lam n).mono (hans lam n hCd) hCd,?_⟩
    intro x y a b hlong haccept
    change ansBound C lam n < a.length ∨ ansBound C lam n < b.length at hlong
    have hcut := accepts_cutoff c U S D lam n x y a b haccept
    have hbound := (ha lam n).trans (hans lam n hCa)
    rcases hlong with hlong | hlong <;> omega
  · rintro ⟨S,D⟩ lam
    exact (hl S D lam).trans (Nat.mul_le_mul hCl (Nat.pow_le_pow_right (by omega) hCl))
  · intro lam n
    exact (ha lam n).trans (hans lam n hCa)

theorem resources (c : ℕ) (hc : 1 ≤ c) (he : Even c) (U : ClockedUniversalMachine) :
    ∃ C, (∀ source lam n, (output c hc he U source lam).Within n (budget C lam n)) ∧
      ∀ source lam, (output c hc he U source lam).decider.size ≤ C*(lam+1)^C := by
  obtain ⟨C,hw,hs,_⟩ := resources_with_cutoff c hc he U
  exact ⟨C,hw,hs⟩

end MIPRE.Introspection.DecisionCompiler
