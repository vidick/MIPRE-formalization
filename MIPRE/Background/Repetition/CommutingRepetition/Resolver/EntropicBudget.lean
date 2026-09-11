/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/EntropicBudget.lean
-/
/-
# The telescoped entropy budget from the kernel entropy inequality (node 1.2.6)

Abstract form of the budget argument of 05_prerounding.tex (eqs
positive-functional, functional-probability-bridge, positive-functional-jensen,
random-martingale-increment): given

* positive contractions `Fs i` (`i` in a finite index set),
* a monotone ℝ-linear functional `ω` of mass `ω 1 ≤ 1`,
* vectors `Φ i` whose squared increments are the `ω`-values of the polarized
  kernel `K(Fᵢ,Fᵢ) − K(Fᵢ,Fᵢ') − K(Fᵢ',Fᵢ) + K(Fᵢ',Fᵢ')`,
* a finite effect martingale (law, index path, deterministic start) whose
  tower condition is the mass-weighted mean condition for `Fs`,

the law-weighted total squared increment along the martingale is at most
`negMulLog (ω (F_{i₀}))`: one kernel entropy inequality per index fiber
(`Resolver/ResolverKernel.lean`), evaluation by `ω`, summation over fibers,
telescoping over time, dropping the nonnegative terminal entropy, and the
operator Jensen inequality (`Resolver/OperatorJensen.lean`) at the start.
Nothing here is a manuscript statement (proof-side helper for node 1.2.6).
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.ResolverKernel
import MIPRE.Background.Repetition.CommutingRepetition.Resolver.OperatorJensen

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace Resolver

open scoped BigOperators

set_option linter.unusedSectionVars false

/-- Telescoping over `Fin n`. -/
theorem telescope {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ s : Fin n, (f s.castSucc - f s.succ) = f 0 - f (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun t => f t.castSucc)
    have e1 : ∀ s : Fin n, (f s.castSucc.castSucc - f s.castSucc.succ)
        = (f s.castSucc.castSucc - f s.succ.castSucc) := by
      intro s; rw [Fin.succ_castSucc]
    simp only [e1]
    rw [h]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    ring

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The telescoped entropy budget.** -/
theorem entropy_budget {I : Type} [Fintype I] [DecidableEq I]
    (Fs : I → A) (hF0 : ∀ i, 0 ≤ Fs i) (hF1 : ∀ i, Fs i ≤ 1)
    (ω : A →ₗ[ℝ] ℝ) (hmono : ∀ {a b : A}, a ≤ b → ω a ≤ ω b) (hm1 : ω 1 ≤ 1)
    {V : Type*} [NormedAddCommGroup V] (Φ : I → V)
    (hinc : ∀ i i', ‖Φ i - Φ i'‖ ^ 2
      = ω (kern (Fs i) (Fs i) - kern (Fs i) (Fs i') - kern (Fs i') (Fs i) + kern (Fs i') (Fs i')))
    {steps : ℕ} {Ω : Type} [Fintype Ω] (law : Ω → ℝ) (hlaw : ∀ ω, 0 ≤ law ω)
    (hsum : ∑ ω, law ω = 1) (idx : Fin (steps + 1) → Ω → I)
    (hidx0 : ∀ ω ω', idx 0 ω = idx 0 ω')
    (htower : ∀ (s : Fin steps) (i : I),
      ∑ ω, (if idx s.castSucc ω = i then law ω else 0) • Fs (idx s.succ ω)
        = (∑ ω, if idx s.castSucc ω = i then law ω else 0) • Fs i)
    (ω₀ : Ω) :
    ∑ s : Fin steps, ∑ ω, law ω * ‖Φ (idx s.succ ω) - Φ (idx s.castSucc ω)‖ ^ 2
      ≤ Real.negMulLog (ω (Fs (idx 0 ω₀))) := by
  -- the entropy functional at time `t`
  set h : Fin (steps + 1) → ℝ :=
    fun t => ∑ ω', law ω' * ω (cfc Real.negMulLog (Fs (idx t ω'))) with hdef
  have hH0 : ∀ i, 0 ≤ ω (cfc Real.negMulLog (Fs i)) := fun i => by
    have := hmono (cfc_negMulLog_nonneg (hF0 i) (hF1 i))
    rwa [map_zero] at this
  -- one step
  have hstep : ∀ s : Fin steps,
      ∑ ω', law ω' * ‖Φ (idx s.succ ω') - Φ (idx s.castSucc ω')‖ ^ 2
        ≤ h s.castSucc - h s.succ := by
    intro s
    -- the fiber bound
    have hfib : ∀ i : I,
        ∑ ω', (if idx s.castSucc ω' = i then law ω' else 0) * ‖Φ (idx s.succ ω') - Φ i‖ ^ 2
          ≤ (∑ ω', if idx s.castSucc ω' = i then law ω' else 0) * ω (cfc Real.negMulLog (Fs i))
            - ∑ ω', (if idx s.castSucc ω' = i then law ω' else 0)
                * ω (cfc Real.negMulLog (Fs (idx s.succ ω'))) := by
      intro i
      have hw : ∀ ω', 0 ≤ (if idx s.castSucc ω' = i then law ω' else 0) := fun ω' => by
        split_ifs
        · exact hlaw ω'
        · exact le_rfl
      have hk := kern_entropy_le (fun ω' => if idx s.castSucc ω' = i then law ω' else 0) hw
        (fun ω' => Fs (idx s.succ ω')) (Fs i) (fun ω' => hF0 _) (fun ω' => hF1 _) (hF0 i) (hF1 i)
        (htower s i)
      have hk' := hmono hk
      rw [map_sum, map_sub, map_smul, map_sum] at hk'
      simp only [map_smul, smul_eq_mul] at hk'
      simp only [hinc]
      exact hk'
    -- sum over fibers
    have hswap1 : ∑ ω', law ω' * ‖Φ (idx s.succ ω') - Φ (idx s.castSucc ω')‖ ^ 2
        = ∑ i, ∑ ω', (if idx s.castSucc ω' = i then law ω' else 0)
            * ‖Φ (idx s.succ ω') - Φ i‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    have hswap2 : ∑ i, (∑ ω', if idx s.castSucc ω' = i then law ω' else 0)
          * ω (cfc Real.negMulLog (Fs i)) = h s.castSucc := by
      simp only [hdef, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    have hswap3 : ∑ i, ∑ ω', (if idx s.castSucc ω' = i then law ω' else 0)
          * ω (cfc Real.negMulLog (Fs (idx s.succ ω'))) = h s.succ := by
      simp only [hdef]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    rw [hswap1, ← hswap2, ← hswap3, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => hfib i
  -- telescope
  have htel : ∑ s : Fin steps, (h s.castSucc - h s.succ) = h 0 - h (Fin.last steps) :=
    telescope h
  have hlast : 0 ≤ h (Fin.last steps) :=
    Finset.sum_nonneg fun ω' _ => mul_nonneg (hlaw ω') (hH0 _)
  have h0 : h 0 = ω (cfc Real.negMulLog (Fs (idx 0 ω₀))) := by
    simp only [hdef]
    rw [Finset.sum_congr rfl fun ω' _ => by rw [hidx0 ω' ω₀], ← Finset.sum_mul, hsum, one_mul]
  calc ∑ s : Fin steps, ∑ ω', law ω' * ‖Φ (idx s.succ ω') - Φ (idx s.castSucc ω')‖ ^ 2
      ≤ ∑ s : Fin steps, (h s.castSucc - h s.succ) := Finset.sum_le_sum fun s _ => hstep s
    _ = h 0 - h (Fin.last steps) := htel
    _ ≤ h 0 := by linarith
    _ = ω (cfc Real.negMulLog (Fs (idx 0 ω₀))) := h0
    _ ≤ Real.negMulLog (ω (Fs (idx 0 ω₀))) :=
        jensen_negMulLog ω hmono hm1 (hF0 _) (hF1 _)

end Resolver

end CommutingRepetition
