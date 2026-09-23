/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionCompiler

/-! # All-index ambient time bounds for the actual decision compiler -/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost Polynomial

theorem positive_time_bound {c : ℕ} (hc : 1 ≤ c) (U : ClockedUniversalMachine) :
    ∃ C, ∀ S D lam n, 1 ≤ lam → 1 ≤ n →
      (decider c U S D lam).TimeBoundAt n (ansBound C lam n) C := by
  obtain ⟨d,hd⟩ := (PolyBounded.eval
    (DecisionPreparation.compiledPoly c (untypedKernel U)) PolyBounded.id).exists_le_pow
  obtain ⟨C,hC⟩ := polynomial_ansBound (6*(32*X)^(d+1)) 5
  refine ⟨max C (d+1),fun S D lam n hl hn payload => ?_⟩
  let M := SourceDescriptionCompiler.clamp ((S,D),lam)
  let B := ansBound 5 lam n
  let v := (32*B)*(payload.size+1)
  have hi : ClockSimulation.indexReader (.cons (encode n) payload) = n :=
    CL.Detyping.Program.readNat_encode n
  have hB : 2 ≤ B := by
    change 2^1 ≤ 2^((lam*n+1)^5)
    exact Nat.pow_le_pow_right (by decide) (Nat.one_le_pow _ _ (by omega))
  have hlB : lam ≤ B := (ClockArithmetic.clock_arguments_le (by decide : 1 ≤ 5) hl hn).1
  have hnB : n ≤ B := (ClockArithmetic.clock_arguments_le (by decide : 1 ≤ 5) hl hn).2.1
  have hM := SourceDescriptionCompiler.clamp_size S D lam
  have hmB : esize M ≤ 26*B := by dsimp only [M]; omega
  have hnSize := ClockArithmetic.esize_le_value hnB
  have hv : 2 ≤ v := by dsimp [v]; nlinarith
  have hz : esize M + (Data.cons (encode n) payload).size + 1 ≤ v := by
    change esize M + (esize n + payload.size + 1) + 1 ≤ v
    dsimp [v]
    nlinarith
  have hb : ansBound 5 M.2 (ClockSimulation.indexReader (.cons (encode n) payload)) ≤ v := by
    rw [hi]
    change B ≤ v
    dsimp [v]
    nlinarith
  obtain ⟨t,ht,hr⟩ := DecisionPreparation.compiler_runs_poly hc (untypedKernel U) M
    (.cons (encode n) payload) hl (by simpa only [hi] using hn) hz hb
  have hrun := zeroWrap_runs_pos
    (DecisionPreparation.compiler_closed c (untypedKernel U) M) hn payload _ t hr
  have hs : (Data.cons (encode n) payload).size + 4 ≤ 5*v := by omega
  have htd : t ≤ v^d := ht.trans (hd v hv)
  have hd1 : v^d ≤ v^(d+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hv1 : v ≤ v^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ v) (by omega : 1 ≤ d+1)
  have htime : t + (Data.cons (encode n) payload).size + 4 ≤
      6*(32*B)^(d+1)*(payload.size+1)^(d+1) := by
    have ht' : t + (Data.cons (encode n) payload).size + 4 ≤ 6*v^(d+1) := by omega
    simpa only [v,mul_pow,mul_assoc] using ht'
  have hcoef : 6*(32*B)^(d+1) ≤ ansBound C lam n := by
    simpa only [eval_mul, eval_ofNat, eval_pow, eval_X] using hC lam n hl hn
  have hmono : ansBound C lam n ≤ ansBound (max C (d+1)) lam n := by
    unfold ansBound
    exact Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_right (by omega) (le_max_left C (d+1)))
  have hbnd := htime.trans (Nat.mul_le_mul (hcoef.trans hmono)
    (Nat.pow_le_pow_right (by omega) (le_max_right C (d+1))))
  refine ⟨encode (untypedKernel U (DecisionPreparation.kernelInput c M
    (.cons (encode n) payload))),t + (Data.cons (encode n) payload).size + 4,hbnd,?_⟩
  change (compute c U ((S,D),lam)).Runs _ _ _
  rw [compute_apply, if_neg (by omega : lam ≠ 0)]
  exact hrun

/-- The zero cases and positive branch share one fixed degree and the exact
all-index exponential coefficient required by the pipeline. -/
theorem time_bound {c : ℕ} (hc : 1 ≤ c) (U : ClockedUniversalMachine) :
    ∃ C, ∀ S D lam n,
      (decider c U S D lam).TimeBoundAt n (ansBound C lam n) C := by
  obtain ⟨Cp,hp⟩ := positive_time_bound hc U
  obtain ⟨Cz,hz⟩ := zero_time_bound
  obtain ⟨Cn,hn⟩ := zeroWrap_zero_time_bound
  let C := max Cp (max Cz Cn)
  have hpC : Cp ≤ C := le_max_left _ _
  have hzC : Cz ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hnC : Cn ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,fun S D lam n => ?_⟩
  by_cases hl : lam = 0
  · subst lam
    intro payload
    obtain ⟨t,ht,hr⟩ := hz (encode n) payload
    refine ⟨encode (zeroTest payload),t,ht.trans ?_,?_⟩
    · simpa only [ansBound, Nat.zero_mul, Nat.zero_add, one_pow, pow_one] using
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) hzC :
          (payload.size+1)^Cz ≤ (payload.size+1)^C)
    · change (compute c U ((S,D),0)).Runs _ _ _
      simpa only [compute_apply, ↓reduceIte] using hr
  · by_cases hzero : n = 0
    · subst n
      intro payload
      obtain ⟨t,ht,hr⟩ := hn (positiveCompiler c U (SourceDescriptionCompiler.clamp ((S,D),lam))) payload
      refine ⟨encode (zeroTest payload),t,ht.trans ?_,?_⟩
      · simpa only [ansBound, Nat.mul_zero, Nat.zero_add, one_pow, pow_one] using
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) hnC :
            (payload.size+1)^Cn ≤ (payload.size+1)^C)
      · change (compute c U ((S,D),lam)).Runs _ _ _
        simpa only [compute_apply, if_neg hl] using hr
    · apply (hp S D lam n (by omega) (by omega)).mono _ hpC
      unfold ansBound
      exact Nat.pow_le_pow_right (by decide)
        (Nat.pow_le_pow_right (by omega) hpC)

end MIPRE.Introspection.DecisionCompiler
