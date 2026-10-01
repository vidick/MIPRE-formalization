/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Repetition.TracialApprox
public import MIPRE.Background.Repetition.CommutingRepetition.VN.TensorPower
public import MIPRE.Foundations.DyadicPair

@[expose] public section

/-!
# Amplification by an algebra with dyadic matrix units

The orthonormalization step of the C6b port applies in dyadic pairs (`BipartiteModel.IsDyadicPair`,
`MIPRE/Foundations/DyadicPair.lean`), and the finite pairs that `commutingFinitePairApprox` builds
are the ancilla extensions of standard-form models `stdModel M ψ` of tracial algebras `M`, which
need not have any matrix units. This file tensors them with a fixed tracial algebra `B` that has
unital dyadic matrix units, at no cost in value (`reports/c6b-paper-proofs.md`, §3, Theorems A and
T).

* **The standard-form pair of `M ⊗ B` is dyadic** (`isDyadicPair_stdModel_tensorStep`, Theorem
  A): the units `1 ⊗ fᵢⱼ` of `M ⊗ B` act on the left in `R(M ⊗ B)'` and, through the opposite
  algebra, on the right in `R(M ⊗ B)''`. So are its ancilla extensions with nonempty registers
  (`BipartiteModel.IsDyadicPair.expand`), whence both hypotheses `hII` of the orthonormalization
  step.
* **Amplification** (`amplify`, Theorem T): a tracial strategy `(σ, E, F)` in `M` gives the
  tracial strategy `(σ ⊗ 1, E ⊗ 1, F ⊗ 1)` in `M ⊗ B`, of the same correlation
  (`amplify_correlation`), the trace of `M ⊗ B` restricting to that of `M` on `M ⊗ 1`.
* **The value consequence** (`exists_tracialStrategy_isDyadicPair`): strict tracial reduction
  with a strategy whose standard-form model is dyadic in every state, which is what
  `commutingFinitePairApprox` needs to land in dyadic pairs.
-/

namespace MIPRE.Repetition

open CommutingRepetition (StdTracialAlgebra TracialStrategy IsPosElem)
open CommutingRepetition.StdTracialAlgebra (tensorStep stepInclLeft stepInclRight)

/-! ## The standard-form pair of an amplified algebra -/

section StdPair

variable (M : StdTracialAlgebra.{0})

/-- **The left action as a ∗-homomorphism into `R(𝒜)'`**: `StdTracialAlgebra.L`, corestricted to
the first player's algebra of the standard-form model. -/
noncomputable def leftVNHom : M.A →⋆ₐ[ℂ] M.vnAlg :=
  StarAlgHom.codRestrict M.L M.vnAlg fun a => M.L_mem_vnAlg a

/-- **The right action as a ∗-homomorphism into `R(𝒜)''`**: `StdTracialAlgebra.R`, on the
opposite algebra, corestricted to the second player's algebra of the standard-form model. -/
noncomputable def rightVNHom : M.Aᵐᵒᵖ →⋆ₐ[ℂ] rightVN M :=
  StarAlgHom.codRestrict M.R (rightVN M) fun a => Rop_mem_rightVN M a.unop

/-- **The standard-form model of a tracial algebra with unital dyadic matrix units is a dyadic
pair** (`lem:amplification-dyadic`, item A), in every state: the units act on the left in `R(𝒜)'` and, through the opposite algebra,
on the right in `R(𝒜)''`. -/
theorem isDyadicPair_stdModel (hM : HasDyadicUnits M.A) (ψ : M.H) :
    (stdModel M ψ).IsDyadicPair :=
  ⟨isFinitePair_stdModel M ψ, hM.map (leftVNHom M), hM.op.map (rightVNHom M)⟩

variable (B : StdTracialAlgebra.{0})

/-- **`M ⊗ B` has unital dyadic matrix units when `B` has** (`lem:amplification-dyadic`, item A):
the units `1 ⊗ fᵢⱼ`. -/
theorem hasDyadicUnits_tensorStep (hB : HasDyadicUnits B.A) :
    HasDyadicUnits (tensorStep M B).A :=
  hB.map (stepInclRight M B)

/-- **The standard-form pair of `M ⊗ B` is a dyadic pair** (`lem:amplification-dyadic`, item A;
Theorem A of `reports/c6b-paper-proofs.md`, §3) when `B` has unital dyadic matrix units, in every
state. -/
theorem isDyadicPair_stdModel_tensorStep (hB : HasDyadicUnits B.A) (ψ : (tensorStep M B).H) :
    (stdModel (tensorStep M B) ψ).IsDyadicPair :=
  isDyadicPair_stdModel _ (hasDyadicUnits_tensorStep M B hB) ψ

/-- **The embedding `a ↦ a ⊗ 1` of `M` into `M ⊗ B`**: `StdTracialAlgebra.stepInclLeft`, typed
into the carrier of `tensorStep M B`, so that its images carry that algebra's instances. -/
noncomputable def inclLeft : M.A →⋆ₐ[ℂ] (tensorStep M B).A :=
  stepInclLeft M B

/-- **The trace of `M ⊗ B` restricts to that of `M`** on `M ⊗ 1`. -/
theorem τ_inclLeft (a : M.A) : (tensorStep M B).τ (inclLeft M B a) = M.τ a := by
  have := M.stepτ_inclLeft_mul_inclRight B a 1
  rw [map_one, mul_one, B.τ_one, mul_one] at this
  exact this

end StdPair

/-! ## Amplification of a tracial strategy -/

/-- **A ∗-homomorphism maps positive elements to positive elements**: it carries a sum of squares
`∑ cᵢ⋆ cᵢ` to the sum of squares of the images. Unlike `IsPosElem.starAlgHom_map`, it asks for no
`StarModule` instance, which instance search does not find on the carrier of `tensorStep`. -/
theorem isPosElem_map {R S F : Type*} [NonUnitalNonAssocSemiring R] [StarRing R]
    [NonUnitalNonAssocSemiring S] [StarRing S] [FunLike F R S] [NonUnitalRingHomClass F R S]
    [StarHomClass F R S] (φ : F) {a : R} (h : IsPosElem a) : IsPosElem (φ a) := by
  obtain ⟨k, c, rfl⟩ := h
  exact ⟨k, fun i => φ (c i), by simp only [map_sum, map_mul, map_star]⟩

section Amplify

variable {X Y A' B' : Type} [Fintype X] [Fintype Y] [Fintype A'] [Fintype B']
  (T : TracialStrategy.{0} X Y A' B') (B : StdTracialAlgebra.{0})

/-- **The amplified strategy** (`lem:amplification-dyadic`, item T; Theorem T of
`reports/c6b-paper-proofs.md`, §3): the density `σ ⊗ 1` and the measurements `E ⊗ 1` and `F ⊗ 1` in
`M ⊗ B`, for a tracial strategy `(σ, E, F)` in `M`. -/
noncomputable def amplify : TracialStrategy.{0} X Y A' B' where
  M := tensorStep T.M B
  σ := inclLeft T.M B T.σ
  σ_pos := isPosElem_map _ T.σ_pos
  σ_normalized := by
    rw [← map_star, ← map_mul, τ_inclLeft, T.σ_normalized]
  E x a := inclLeft T.M B (T.E x a)
  F y b := inclLeft T.M B (T.F y b)
  E_pos x a := isPosElem_map _ (T.E_pos x a)
  F_pos y b := isPosElem_map _ (T.F_pos y b)
  E_sum x := by rw [← map_sum, T.E_sum, map_one]
  F_sum y := by rw [← map_sum, T.F_sum, map_one]

/-- **The amplified strategy has the same correlation** (`lem:amplification-dyadic`, item T), the
trace of `M ⊗ B` restricting to that of `M` on `M ⊗ 1`. -/
theorem amplify_correlation : (amplify T B).correlation = T.correlation := by
  funext x y a b
  show ((tensorStep T.M B).τ (star (inclLeft T.M B T.σ) * (inclLeft T.M B (T.E x a) *
    inclLeft T.M B T.σ * inclLeft T.M B (T.F y b)))).re = _
  rw [← map_star, ← map_mul, ← map_mul, ← map_mul, τ_inclLeft]
  rfl

/-- **The standard-form model of an amplified strategy is a dyadic pair**
(`lem:amplification-dyadic`), in every state, when `B` has unital dyadic matrix units. -/
theorem isDyadicPair_stdModel_amplify (hB : HasDyadicUnits B.A) (ψ : (amplify T B).M.H) :
    (stdModel (amplify T B).M ψ).IsDyadicPair :=
  isDyadicPair_stdModel_tensorStep T.M B hB ψ

end Amplify

/-- **Strict tracial reduction into dyadic pairs** (`lem:amplification-dyadic`, its consequence):
below `ω_co(H)` lies the winning probability of a tracial strategy whose standard-form model is a
dyadic pair in every state, given one tracial algebra `B` with unital dyadic matrix units. It is
`CommutingRepetition.strict_tracial_reduction` followed by amplification by `B`, which keeps the
correlation (`amplify_correlation`). -/
theorem exists_tracialStrategy_isDyadicPair {X Y A' B' : Type} [Fintype X] [Fintype Y]
    [Fintype A'] [Fintype B'] [Nonempty X] [Nonempty Y] [Nonempty A'] [Nonempty B']
    (B : StdTracialAlgebra.{0}) (hB : HasDyadicUnits B.A) (H : CommutingRepetition.Game X Y A' B')
    {lam : ℝ} (hlam : lam < H.omegaCO) :
    ∃ T : TracialStrategy.{0} X Y A' B', lam < H.win T.correlation ∧
      ∀ ψ : T.M.H, (stdModel T.M ψ).IsDyadicPair := by
  obtain ⟨T, hT⟩ := CommutingRepetition.strict_tracial_reduction H hlam
  exact ⟨amplify T B, by rwa [amplify_correlation], isDyadicPair_stdModel_amplify T B hB⟩

end MIPRE.Repetition

end
