/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Soundness
public import MIPRE.Foundations.ModelStrategy

@[expose] public section

/-!
# The model chain, part 1: the canonical-line test in a bipartite model

The first file of the model chain from the canonical-line theorem to `MIPRE.LIDT.Simul.SoundIn`,
in the port of `planning/c6b-plan.md` (milestone M14, unit M14-3). It has no vendored counterpart:
it restates, over any bipartite model `M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with the instance set of
`SoundIn` (the two players' algebras star-ordered `⋆`-rings), the vocabulary of the repository's
matrix statement `MIPRE.LIDT.lowIndividualDegree_soundness` (`MIPRE/Background/LIDT/Game.lean`,
`Soundness.lean`), which stays: it is the tensor instance, and serves `soundIn_tensor`.

* `pointPOVMAIn S u` and `pointPOVMBIn S u`: the point measurements of a projective strategy
  `S : M.ProjStrat (lidtGame F m d)`, read as POVMs with outcomes in `F` (the model forms of
  `MIPRE.LIDT.pointPOVMA`, `pointPOVMB`);
* `evalPOVMIn G u`: a POVM with outcomes in the polynomials of individual degree `d`, evaluated at
  `u` (the model form of `MIPRE.LIDT.evalPOVM`, for a single `POVMIn` rather than a projective
  measurement over a one-point index);
* `SoundLidtIn M`, **the canonical-line theorem in `M`**: `T(M)` of `reports/lidt-co-audit.md`
  §3.2, the statement of `lowIndividualDegree_soundness` read in `M`, with `1 ≤ d` added. That is
  the only extra hypothesis, and `SoundIn` supplies it. The measurements it returns are single
  projective POVMs in the two players' algebras (`IsPVMIn GA.op`, `IsPVMIn GB.op`), as in
  `SoundIn`, and the error measure is `M.inconsistency`.

`soundLidtIn_tensor` checks the statement against the matrix theorem: in the tensor-product model
of a state on `Fin a × Fin b` it is `lowIndividualDegree_soundness`, through
`BipartiteModel.ProjStrat.toTensor` and `inconsistency_eq_tensor`, exactly as `soundIn_tensor`
reads `clSoundness`.

## Not ported

Nothing of `Game.lean` or `Soundness.lean` is redeclared: the game, its alphabets, `lidtError`
and `LowIndDegPoly.eval` are classical, imported. The matrix readings `pointPOVMA`, `pointPOVMB`
and `evalPOVM` keep their matrix form (they serve the tensor instance), and their model forms
here carry the suffix `In`, as `MIPRE.LIDT.Simul.tuplePOVMAIn` does for `tuplePOVMA`.

## New here

- `pointPOVMAIn`, `pointPOVMBIn`, `evalPOVMIn`, `SoundLidtIn`: above.
- `pointPOVMA_toTensor`, `pointPOVMB_toTensor`, `evalPOVM_toIn`, `soundLidtIn_tensor`: the tensor
  instance.
-/

noncomputable section

namespace MIPRE.LIDT.Co.Chain

open MIPRE.LIDT (Point LowIndDegPoly LowIndDegPoly.eval Answer.toValue lidtGame lidtError
  pointPOVMA pointPOVMB evalPOVM lowIndividualDegree_soundness)
open scoped MatrixOrder

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-! ## The readings of the conclusions -/

section Readings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

/-- The first player's point measurements of a projective strategy for the canonical-line test,
as POVMs with outcomes in `F` (the model form of `MIPRE.LIDT.pointPOVMA`). -/
def pointPOVMAIn [NeZero m] (S : M.ProjStrat (lidtGame F m d)) (u : Point F m) : POVMIn F 𝒜 :=
  (S.PA (.point u)).map Answer.toValue

/-- The second player's point measurements, as for `pointPOVMAIn` (the model form of
`MIPRE.LIDT.pointPOVMB`). -/
def pointPOVMBIn [NeZero m] (S : M.ProjStrat (lidtGame F m d)) (u : Point F m) : POVMIn F ℬ :=
  (S.PB (.point u)).map Answer.toValue

/-- A POVM with outcomes in the polynomials of individual degree `d`, evaluated at `u` (the model
form of `MIPRE.LIDT.evalPOVM`): the outcome `a` gets the sum of the operators of the polynomials
`g` with `g(u) = a`. -/
def evalPOVMIn {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (G : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) R) (u : Point F m) : POVMIn F R :=
  G.map fun g => g.eval u

end Readings

/-! ## The canonical-line theorem in a model -/

/-- **The canonical-line theorem in the bipartite model `M`** (`T(M)` of
`reports/lidt-co-audit.md` §3.2): `MIPRE.LIDT.lowIndividualDegree_soundness` read in `M`, with
`1 ≤ d` added. A projective strategy in `M` passing the `(m, q, d)`-low individual degree test
with probability at least `1 - ε` admits, for every positive `k ≥ 400 m d`, projective
measurements `GA` in the first player's algebra and `GB` in the second's, with outcomes the
polynomials of individual degree `d`, whose evaluations at a uniform point are consistent with
the other player's point measurements, and which are consistent with each other, all with error
`lidtError m d q k ε`. -/
def SoundLidtIn (M : BipartiteModel 𝒞 𝒜 ℬ) : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m], 1 ≤ d →
    ∀ (S : M.ProjStrat (lidtGame F m d)) (ε : ℝ), 1 - ε ≤ S.value →
    ∀ k : ℕ, 400 * m * d ≤ k → 0 < k →
    ∃ GA : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) 𝒜,
    ∃ GB : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) ℬ,
      IsPVMIn GA.op ∧ IsPVMIn GB.op ∧
      M.inconsistency (uniform (Point F m)) (pointPOVMAIn S) (evalPOVMIn GB)
          ≤ lidtError m d (Fintype.card F) k ε ∧
        M.inconsistency (uniform (Point F m)) (evalPOVMIn GA) (pointPOVMBIn S)
          ≤ lidtError m d (Fintype.card F) k ε ∧
        M.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
          ≤ lidtError m d (Fintype.card F) k ε

/-! ## The tensor-product instance -/

section Tensor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m] {a b : ℕ}
  {ψ : Fin a × Fin b → ℂ}

/-- The matrix point measurements of the tensor-product strategy are the model's. -/
theorem pointPOVMA_toTensor (S : (BipartiteModel.tensor ψ).ProjStrat (lidtGame F m d))
    (u : Point F m) : (pointPOVMA S.toTensor u).toIn = pointPOVMAIn S u := by
  rw [pointPOVMA, POVM.toIn_map]
  rfl

/-- The matrix point measurements of the tensor-product strategy are the model's. -/
theorem pointPOVMB_toTensor (S : (BipartiteModel.tensor ψ).ProjStrat (lidtGame F m d))
    (u : Point F m) : (pointPOVMB S.toTensor u).toIn = pointPOVMBIn S u := by
  rw [pointPOVMB, POVM.toIn_map]
  rfl

omit [NeZero m] in
/-- The matrix evaluation of a projective measurement is the model's evaluation of its POVM. -/
theorem evalPOVM_toIn {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d)) (Matrix n n ℂ))
    (u : Point F m) : (evalPOVM G u).toIn = evalPOVMIn (G.toPOVM ()).toIn u := by
  rw [evalPOVM, POVM.toIn_map]
  rfl

end Tensor

/-- **The canonical-line theorem holds in the tensor-product model** of every state on
`Fin a × Fin b`: `lowIndividualDegree_soundness`, for the tensor-product strategy the projective
strategy is (the hypothesis `1 ≤ d` is not used). -/
theorem soundLidtIn_tensor {a b : ℕ} (ψ : Fin a × Fin b → ℂ) :
    SoundLidtIn (BipartiteModel.tensor ψ) := by
  intro F _ _ _ m d _ _ S ε hS k hk hk0
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    lowIndividualDegree_soundness S.toTensor ε (by rw [S.value_toTensor]; exact hS) k hk hk0
  refine ⟨(GA.toPOVM ()).toIn, (GB.toPOVM ()).toIn, by classical exact (GA.isPVM_at ()).toIn,
    by classical exact (GB.isPVM_at ()).toIn, ?_, ?_, ?_⟩
  · rw [inconsistency_eq_tensor] at h1
    simp only [pointPOVMA_toTensor, evalPOVM_toIn] at h1
    exact h1
  · rw [inconsistency_eq_tensor] at h2
    simp only [pointPOVMB_toTensor, evalPOVM_toIn] at h2
    exact h2
  · rw [inconsistency_eq_tensor] at h3
    exact h3

end MIPRE.LIDT.Co.Chain

end

end
