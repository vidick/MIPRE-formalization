/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Simultaneous
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

/-!
# The low-individual-degree test in a bipartite model

Phase 3 of `planning/mipco-track.md`. The one fact about the low-individual-degree test that the
soundness of answer reduction uses is the quantum soundness of the seeded CL test,
`LIDT.Simul.clSoundness`. `LIDT.Simul.SoundIn M` is that fact as a hypothesis on a bipartite
model `M`, in the exact shape of `clSoundness`: a projective strategy in `M` passing the seeded
test with `r` codewords with probability at least `1 - ε` admits projective measurements of
`r`-tuples of polynomials in the two players' algebras, each consistent with the other player's
point measurements and with each other, at the error `δ_sim`.

* **Its tensor-product instance** (`soundIn_tensor`) is `clSoundness`, and through it the
  vendored `mainFormal`: a projective strategy in the tensor-product model of a state on
  `Fin a × Fin b` is a `TensorProductStrategy` (`BipartiteModel.ProjStrat.toTensor`), and the
  matrix inconsistency is the model's (`inconsistency_eq_tensor`).
* **Its commuting-operator form** (`SoundCo`: the test is sound in the model of every
  commuting-operator strategy) is the hypothesis `MIPRE.mipco_eq_core_of_stages` carries for
  answer reduction, and Phase 6 of the plan.

The measurements the conclusion extracts are single POVMs (`POVMIn`) rather than families over a
one-point index; the third conclusion keeps the one-point index of `clSoundness`
(`BipartiteModel.inconsistency_uniform_unit` reads it as a disagreement).
-/

noncomputable section

namespace MIPRE.LIDT.Simul

open Finset MIPRE.LIDT.CL
open scoped MatrixOrder

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-! ## The readings of the conclusions -/

section Readings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d r : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)

/-- The first player's point measurements of a projective strategy for the seeded test, read as
the tuple of values a point answer carries (the model form of `tuplePOVMA`). -/
def tuplePOVMAIn (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) (y : Point F m) :
    POVMIn (Fin r → F) 𝒜 :=
  (S.PA (.point y)).map valsOf

/-- The second player's point measurements, as for `tuplePOVMAIn`. -/
def tuplePOVMBIn (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) (y : Point F m) :
    POVMIn (Fin r → F) ℬ :=
  (S.PB (.point y)).map valsOf

variable {hm} in
/-- A measurement of `r`-tuples of polynomials, evaluated at a point (the model form of
`evalTuplePOVM`). -/
def evalTuplePOVMIn {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (G : POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) R) (y : Point F m) :
    POVMIn (Fin r → F) R :=
  G.map fun g j => (g j).eval y

end Readings

/-! ## Soundness in a model -/

/-- **The seeded CL test is sound in the bipartite model `M`** (`def:lidt-sound-in`), in the shape
of `clSoundness`: for `q` a power of two, `m ∣ q` and `d, r ≥ 1`, a projective strategy in `M`
passing the seeded test with `r` codewords with probability at least `1 - ε` admits projective
measurements `GA` in the first player's algebra and `GB` in the second's, of `r`-tuples of
polynomials of individual degree `d`, whose evaluations at a uniform point are consistent with
the other player's point measurements, and which are consistent with each other, all with error
`δ_sim(ε, q, m, d, r)`. -/
def SoundIn (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] {m d r k : ℕ} [NeZero m],
    Fintype.card F = 2 ^ k → ∀ (hm : m ∣ Fintype.card F), 1 ≤ d → 1 ≤ r →
    ∀ (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) (ε : ℝ), 0 ≤ ε → 1 - ε ≤ S.value →
    ∃ GA : POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) 𝒜,
    ∃ GB : POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) ℬ,
      IsPVMIn GA.op ∧ IsPVMIn GB.op ∧
      M.inconsistency (uniform (Point F m)) (tuplePOVMAIn hm S) (evalTuplePOVMIn GB)
          ≤ deltaSim (Fintype.card F) m d r ε ∧
        M.inconsistency (uniform (Point F m)) (evalTuplePOVMIn GA) (tuplePOVMBIn hm S)
          ≤ deltaSim (Fintype.card F) m d r ε ∧
        M.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
          ≤ deltaSim (Fintype.card F) m d r ε

/-! ## The tensor-product instance -/

section Tensor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d r : ℕ} [NeZero m]
  {hm : m ∣ Fintype.card F} {a b : ℕ} {ψ : Fin a × Fin b → ℂ}

theorem tuplePOVMA_toTensor
    (S : (BipartiteModel.tensor ψ).ProjStrat (clGame (d := d) (ldc := r) hm)) (y : Point F m) :
    (tuplePOVMA hm S.toTensor y).toIn = tuplePOVMAIn hm S y := by
  rw [tuplePOVMA, POVM.toIn_map]
  rfl

theorem tuplePOVMB_toTensor
    (S : (BipartiteModel.tensor ψ).ProjStrat (clGame (d := d) (ldc := r) hm)) (y : Point F m) :
    (tuplePOVMB hm S.toTensor y).toIn = tuplePOVMBIn hm S y := by
  rw [tuplePOVMB, POVM.toIn_map]
  rfl

omit [NeZero m] in
theorem evalTuplePOVM_toIn {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
      (Matrix n n ℂ)) (y : Point F m) :
    (evalTuplePOVM G y).toIn = evalTuplePOVMIn (G.toPOVM ()).toIn y := by
  rw [evalTuplePOVM, POVM.toIn_map]
  rfl

end Tensor

/-- **The seeded CL test is sound in the tensor-product model** of every state on
`Fin a × Fin b`: `clSoundness`, for the tensor-product strategy the projective strategy is. -/
theorem soundIn_tensor {a b : ℕ} (ψ : Fin a × Fin b → ℂ) :
    SoundIn (BipartiteModel.tensor ψ) := by
  intro F _ _ _ m d r k _ hq hm hd hr S ε hε hS
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    clSoundness hq hm hd hr S.toTensor ε hε (by rw [S.value_toTensor]; exact hS)
  refine ⟨(GA.toPOVM ()).toIn, (GB.toPOVM ()).toIn, by classical exact (GA.isPVM_at ()).toIn,
    by classical exact (GB.isPVM_at ()).toIn, ?_, ?_, ?_⟩
  · rw [inconsistency_eq_tensor] at h1
    simp only [tuplePOVMA_toTensor, evalTuplePOVM_toIn] at h1
    exact h1
  · rw [inconsistency_eq_tensor] at h2
    simp only [tuplePOVMB_toTensor, evalTuplePOVM_toIn] at h2
    exact h2
  · rw [inconsistency_eq_tensor] at h3
    exact h3

/-! ## The commuting-operator model -/

/-- **The seeded CL test is sound in the commuting-operator model** (`def:lidt-sound-in`): in the
model of every commuting-operator strategy, whose algebras are the commutant of the second
player's operators and its commutant. This is Phase 6 of `planning/mipco-track.md`, and the
hypothesis on the low-individual-degree test of `MIPRE.mipco_eq_core_of_stages`. -/
def SoundCo : Prop :=
  ∀ {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (S : CommutingOperatorStrategy X Y A B), SoundIn S.toModel

end MIPRE.LIDT.Simul

end

end
