/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.OracularModel
public import MIPRE.Foundations.POVMMix
public import MIPRE.Foundations.RegisterReindex

@[expose] public section

/-!
# Soundness of oracularization, for bipartite strategies

Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of
games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for
`MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so
`val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`.

`MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That
is not the statement a verifier-level consumer can use: `Verifier.valStar` is a supremum over
`TensorProductStrategy`, and so is the detyping transport (`restrictAmbient_value_ge`), while the
only bridge from synchronous to bipartite values, `thm:almost-sync`, is off the critical path.
The paper's `thm:oracle-soundness` is bipartite; this is its game-level form.

The argument is the one of `MIPRE/Foundations/OracularModel.lean`, which proves it once for
projective strategies in a bipartite model (`SeededGame.povmValue_sound_ge`); this file is its
reading in the tensor-product model of the strategy. Every `TensorProductStrategy` is projective
(`ProjectiveMeasurement.isPVM_at`), so no Naimark dilation is needed, and the extracted strategy
(`tensorSound`) is the adapter `TensorProductStrategy.adapt`: the first player's isolated-Alice
measurement and the second player's isolated-Bob measurement, relabelled along
`OAns.singlePart` so that an oracle-shaped answer is grouped into one distinguished outcome.
-/

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

/-- The operators of a projective measurement at one question form a PVM. -/
theorem ProjectiveMeasurement.isPVM_at {X A : Type*} [Fintype A] {n : Type*} [Fintype n]
    [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) :
    IsPVM (P.M x) where
  isSelfAdjoint a := by rw [← Matrix.star_eq_conjTranspose]; exact P.selfAdjoint x a
  idem a := P.projective x a
  sum_eq_one := P.normalized x

@[simp] theorem ProjectiveMeasurement.toPOVM_mats_val {X A : Type*} [Fintype A] {n : Type*}
    [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) (a : A) :
    ((P.toPOVM x).mats a).val = P.M x a := rfl

namespace SeededGame

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)

/-! ## The extracted strategy -/

/-- **The strategy extracted from a bipartite strategy for the oracularization**: Alice plays the
first player's isolated-Alice measurement, Bob the second player's isolated-Bob measurement, both
relabelled along `OAns.singlePart`, so that an oracle-shaped answer is grouped into one
distinguished outcome. Same state, same Hilbert spaces. -/
noncomputable def tensorSound (N : TensorProductStrategy S.oracular.toGame) :
    TensorProductStrategy S.toGame :=
  N.adapt S.toGame (fun x => (Role.alice, x)) (fun y => (Role.bob, y))
    (fun _ => OAns.singlePart) (fun _ => OAns.singlePart)

omit [Inhabited A] in
theorem tensorSound_ψ (N : TensorProductStrategy S.oracular.toGame) [Inhabited A] :
    (S.tensorSound N).ψ = N.ψ := rfl

variable {S}

/-! ## Soundness -/

/-- **Soundness of oracularization, for bipartite strategies** (item 2 of blueprint
`thm:oracularization`, `lem:oracular-soundness-tensor`): a tensor-product strategy of value at
least `1 - ε` for the oracularized game yields one of value at least `1 - 24√ε` for the input
game, on the same state — `SeededGame.povmValue_sound_ge` in the tensor-product model of the
strategy. -/
theorem tensorSound_value_ge (N : TensorProductStrategy S.oracular.toGame) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hval : 1 - ε ≤ N.value) :
    1 - 24 * √ε ≤ (S.tensorSound N).value := by
  rw [tensorSound, TensorProductStrategy.value_adapt]
  rw [TensorProductStrategy.value_eq_tensor_povmValue] at hval
  exact S.povmValue_sound_ge (BipartiteModel.tensor N.ψ) (fun x => (N.PA.toPOVM x).toIn)
    (fun y => (N.PB.toPOVM y).toIn) (norm_evec_eq_one N.ψ_unit)
    (fun q => (N.PA.isPVM_at q).toIn) (fun q => (N.PB.isPVM_at q).toIn) hε0 hε1 hval

variable (S)

/-- **Soundness of oracularization, in quantum values**: `val*` of the oracularized game above
`1 - ε` puts `val*` of the input game at least `1 - 24√ε`. This is the form a verifier-level
statement consumes, `Verifier.valStar` being a quantum value. -/
theorem quantumValue_ge_of_oracular {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue S.oracular.toGame) :
    1 - 24 * √ε ≤ quantumValue S.toGame := by
  by_cases hε1 : ε ≤ 1
  · by_contra hcon
    rw [not_le] at hcon
    have hall : ∀ N : TensorProductStrategy S.oracular.toGame, N.value ≤ 1 - ε := by
      intro N
      by_contra hN
      rw [not_le] at hN
      have h1 := tensorSound_value_ge N hε.le hε1 hN.le
      have h2 : (S.tensorSound N).value ≤ quantumValue S.toGame :=
        le_ciSup (TensorProductStrategy.bddAbove_range_value _) (S.tensorSound N)
      linarith
    have h3 : quantumValue S.oracular.toGame ≤ 1 - ε := Real.iSup_le hall (by linarith)
    linarith
  · rw [not_le] at hε1
    have h1 : 1 < √ε := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt zero_le_one hε1
    have h2 := quantumValue_nonneg S.toGame
    linarith

end SeededGame

end MIPRE

end
