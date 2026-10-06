/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Tailored.Intro.AuxCons
public import MIPRE.Foundations.LowDegree.BinaryKernel

@[expose] public section

/-!
# Kernel generators of a register-local linear map, as the image of a program

The constraint families of `MIPRE.Tailored.Intro.AuxCons` are parametric in lists of
generators of the kernels of register-local linear maps (`KerGens`). This file supplies one,
as the image of a single polynomial-time program.

The program is the existing binary kernel solver `LowDegree.BinaryLinear.kernelGeneratorsProg`:
it eliminates the columns of the matrix together with an identity certificate and prints the
reduced certificate of each standard basis vector, that is the images of the standard basis
under a projection onto the kernel. Here its correctness is restated in the coordinates of the
sampler (`CL.toBits`, `CL.ofBits`):

* `kernelGens`: the program, on the column count `s` in unary and the rows of the matrix;
* `kernelGens_correct`: for `A : Matrix (Fin m) (Fin s) 𝔽₂` given by its rows, every output
  vector has length `s` and lies in the kernel of `A`, and every kernel vector is in their span;
* `regKerGens`, `kerGens_regKerGens`: for a register-local map `M` on `𝔽₂^Q`, the program run on
  the rows of the matrix of `M` gives generators of the kernel of `M`, so `regKerGens` satisfies
  `KerGens Q`.
-/

namespace MIPRE.Tailored.Intro

open Cost CL MIPRE.LowDegree.BinaryLinear

/-- Generators of the kernel of an `m × s` binary matrix, computed in polynomial time from `s`
in unary and the matrix rows as bit strings of length `s`. -/
noncomputable abbrev kernelGens : PolyTimeFun (Unary × List BitStr) (List BitStr) :=
  kernelGeneratorsProg

theorem vectorBits_eq_toBits {s : ℕ} (v : Fin s → 𝔽₂) : vectorBits v = toBits v := rfl

theorem vectorValue_eq_ofBits (s : ℕ) (l : BitStr) : vectorValue s l = ofBits s l := rfl

theorem matrixBits_eq {m s : ℕ} (A : Matrix (Fin m) (Fin s) 𝔽₂) :
    matrixBits A = List.ofFn fun i => toBits (A i) := rfl

/-- **The kernel generators program is correct.** Every output vector has length `s` and lies
in the kernel of `A`; every vector of the kernel is in the span of the outputs. -/
theorem kernelGens_correct {m s : ℕ} (A : Matrix (Fin m) (Fin s) 𝔽₂) :
    (∀ v ∈ kernelGens (unary s, List.ofFn fun i => toBits (A i)),
      v.length = s ∧ A.mulVec (ofBits s v) = 0) ∧
    ∀ z : Fin s → 𝔽₂, A.mulVec z = 0 →
      z ∈ Submodule.span 𝔽₂
        {x | ∃ v ∈ kernelGens (unary s, List.ofFn fun i => toBits (A i)), ofBits s v = x} := by
  obtain ⟨-, hmem, hspan⟩ := kernelGeneratorsProg_correct A
  rw [← matrixBits_eq]
  refine ⟨fun v hv => hmem v hv, fun z hz => ?_⟩
  change z ∈ Submodule.span 𝔽₂
    {x | ∃ v ∈ kernelGeneratorsProg (unary s, matrixBits A), vectorValue s v = x}
  rw [hspan]
  exact hz

/-- The rows of the standard matrix of a linear map on `𝔽₂^Q`, as bit strings. -/
noncomputable def linRows {Q : ℕ} (f : (Fin Q → 𝔽₂) →ₗ[𝔽₂] (Fin Q → 𝔽₂)) : List BitStr :=
  List.ofFn fun i => toBits (LinearMap.toMatrix' f i)

/-- Generators of the kernel of every register-local linear map on `𝔽₂^Q`: the output of
`kernelGens` on the rows of its standard matrix. -/
noncomputable def regKerGens (Q : ℕ) (S : Finset (Fin Q)) (M : CL.RegLinear 𝔽₂ S) :
    List (Fin Q → 𝔽₂) :=
  (kernelGens (unary Q, linRows M.toLinearMap)).map (ofBits Q)

/-- **The program's kernel generators satisfy `KerGens`.** -/
theorem kerGens_regKerGens (Q : ℕ) : KerGens Q (regKerGens Q) := by
  intro S M
  have hA : ∀ z, (LinearMap.toMatrix' M.toLinearMap).mulVec z = M z := fun z =>
    LinearMap.toMatrix'_mulVec M.toLinearMap z
  obtain ⟨hmem, hspan⟩ := kernelGens_correct (LinearMap.toMatrix' M.toLinearMap)
  refine ⟨fun g hg => ?_, fun z hz => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    rw [← hA]
    exact (hmem v hv).2
  · have h := hspan z (by rw [hA]; exact hz)
    convert h using 3
    simp [regKerGens, linRows]

end MIPRE.Tailored.Intro

end
