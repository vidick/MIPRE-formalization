/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.CLExplicitSeed
import MIPRE.Background.QLD.LineRepresentative
import MIPRE.Foundations.Introspection.SeededLineProg

/-! # Correctness of the executable seeded Pauli line stages

The fixed axis and diagonal programs compute the precise canonical maps in the
explicit-selector CL presentation. The legacy forms also identify their output
with the original QLD line maps after the proved seed permutation.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Introspection.SeedProgram Introspection.SeededLineProgram SAT

theorem axisRepresentativeProg_canonLin (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    axisRepresentativeProg ((Cost.unary k, Cost.unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u) =
      (shoupBinField k hk).vecBits (CL.canonLin (Submodule.span
        (shoupBinField k hk).carrier {Pi.single (selector (shoupBinField k hk) j hj s) 1}) u) := by
  rw [axisRepresentativeProg_correct k hk j hj s u, LIDT.Adapter.rep_single]
  apply congrArg (shoupBinField k hk).vecBits
  funext i
  by_cases hi : i = selector (shoupBinField k hk) j hj s
  · simp [hi]
  · simp [hi]

theorem diagonalRepresentativeProg_canonLin (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u v : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    let v' := fun i => if i < selector (shoupBinField k hk) j hj s then 0 else v i
    diagonalRepresentativeProg ((Cost.unary k, Cost.unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u, (shoupBinField k hk).vecBits v) =
      ((shoupBinField k hk).vecBits
          (CL.canonLin (Submodule.span (shoupBinField k hk).carrier {v'}) u),
        (shoupBinField k hk).vecBits v') := by
  rw [diagonalRepresentativeProg_correct k hk j hj s u v, representative_eq_canonLin]

/-- The seed change is the same permutation used to prove the exact existing
QLD sampled law, so the executable axis stage computes its actual line map. -/
theorem axisRepresentativeProg_legacy (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    axisRepresentativeProg ((Cost.unary k, Cost.unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u) =
      (shoupBinField k hk).vecBits (LIDT.CL.rep
        (Pi.single (LIDT.CL.chi (ExplicitSeed.dyadic_divides (shoupBinField k hk) j hj)
          (ExplicitSeed.seedPermutation (shoupBinField k hk) s)) 1) u) := by
  rw [ExplicitSeed.chi_seedPermutation (shoupBinField k hk) j hj _ s]
  exact axisRepresentativeProg_canonLin k hk j hj s u

/-- This includes the all-zero selected direction: the point then remains
unchanged, exactly as in the existing QLD diagonal sampler. -/
theorem diagonalRepresentativeProg_legacy (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u v : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    let i := LIDT.CL.chi (ExplicitSeed.dyadic_divides (shoupBinField k hk) j hj)
      (ExplicitSeed.seedPermutation (shoupBinField k hk) s)
    let v' := LIDT.CL.zeroBelow i v
    diagonalRepresentativeProg ((Cost.unary k, Cost.unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u, (shoupBinField k hk).vecBits v) =
      ((shoupBinField k hk).vecBits (LIDT.CL.rep v' u), (shoupBinField k hk).vecBits v') := by
  dsimp only
  rw [ExplicitSeed.chi_seedPermutation (shoupBinField k hk) j hj _ s]
  rw [diagonalRepresentativeProg_canonLin k hk j hj s u v]
  rfl

end MIPRE.QLD.PauliCL
end
