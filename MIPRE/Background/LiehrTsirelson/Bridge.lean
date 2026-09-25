/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core
import MIPRE.Foundations.Tsirelson.Closed
import MIPRE.Foundations.StrategyDilation
import MIPRE.Foundations.RegisterReindex

/-!
# The bridge to the `lukasliehr/MIPRE` core

The vendored `Tsirelson.*` core (`MIPRE/Background/LiehrTsirelson/Upstream/`) states games,
tensor-product and commuting-operator strategies, the correlation sets `C_q`, `C_qa`, `C_qc` and
the two values independently of this repository, on `EuclideanSpace` operators rather than
matrices and with POVMs on both sides. This file identifies the two vocabularies:

* a game `G : MIPRE.Game X Y A B` on nonempty alphabets is a `Tsirelson.NonlocalGame`
  (`toLiehr`), with the same payoff on every correlation (`payoff_toLiehr`);
* the commuting-operator strategies of the two developments are the same data, so the two
  commuting correlation sets coincide (`commutingCorrelations_eq_Cqc`) and so do the two
  commuting values (`valCo_toLiehr`);
* a tensor-product strategy of the vendored core, whose measurements are POVMs, has the
  correlation of one of this repository's projective strategies, by Naimark dilation
  (`exists_projective_dilation_povm`) followed by a reindexing of the registers
  (`tensorCorrelations_subset_Cq`). Hence the vendored `C_qa` is contained in this repository's
  and the vendored `valStar` is bounded by `quantumValue` (`valStar_toLiehr_le`).

`MIPRE/Background/LiehrTsirelson/Main.lean` derives the three terminal propositions of the
vendored `MainStatement.lean` from `MIPRE.separation`.
-/

namespace MIPRE.Liehr

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder InnerProductSpace

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## Games -/

/-- A game of this repository, read as a game of the vendored core. -/
def toLiehr [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] (G : Game X Y A B) :
    Tsirelson.NonlocalGame X Y A B where
  nonemptyX := inferInstance
  nonemptyY := inferInstance
  nonemptyA := inferInstance
  nonemptyB := inferInstance
  questions :=
    { prob := fun q => G.μ q.1 q.2
      nonneg := fun q => G.μ_nonneg q.1 q.2
      sum_eq_one := by rw [Fintype.sum_prod_type]; exact G.μ_sum_one }
  accept := G.D

/-- The two payoffs agree on every correlation. -/
theorem payoff_toLiehr [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] (G : Game X Y A B)
    (p : X → Y → A → B → ℝ) : Tsirelson.payoff (toLiehr G) p = G.payoff p := by
  rw [Tsirelson.payoff_eq_sum_sum, Game.payoff]
  simp only [Finset.mul_sum, mul_assoc]
  rfl

/-! ## Commuting-operator strategies -/

/-- A commuting-operator strategy of this repository, as one of the vendored core. -/
def commutingToLiehr (S : CommutingOperatorStrategy X Y A B) :
    Tsirelson.CommutingStrategy X Y A B where
  H := S.H
  ψ := S.ψ
  unit_ψ := S.ψ_norm
  alice x := ⟨S.E x, S.E_pos x, S.E_sum x⟩
  bob y := ⟨S.F y, S.F_pos y, S.F_sum y⟩
  commuting x y a b := (S.commutes x y a b).eq

theorem corr_commutingToLiehr (S : CommutingOperatorStrategy X Y A B) :
    (commutingToLiehr S).corr = S.correlation := rfl

/-- A commuting-operator strategy of the vendored core, as one of this repository. -/
def commutingOfLiehr (S : Tsirelson.CommutingStrategy X Y A B) :
    CommutingOperatorStrategy X Y A B where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.unit_ψ
  E x := (S.alice x).effect
  F y := (S.bob y).effect
  E_pos x a := (S.alice x).positive a
  F_pos y b := (S.bob y).positive b
  E_sum x := (S.alice x).sum_eq_one
  F_sum y := (S.bob y).sum_eq_one
  commutes x y a b := S.commuting x y a b

theorem correlation_commutingOfLiehr (S : Tsirelson.CommutingStrategy X Y A B) :
    (commutingOfLiehr S).correlation = S.corr := rfl

/-- **The two commuting correlation sets coincide.** -/
theorem commutingCorrelations_eq_Cqc :
    Tsirelson.CommutingCorrelations X Y A B = Cqc X Y A B := by
  ext p
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨commutingOfLiehr S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨commutingToLiehr S, rfl⟩

/-- **The two commuting-operator values coincide.** -/
theorem valCo_toLiehr [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] (G : Game X Y A B) :
    Tsirelson.valCo (toLiehr G) = commutingOperatorValue G := by
  show sSup _ = sSup _
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_range, commutingCorrelations_eq_Cqc, Cqc,
    payoff_toLiehr, CommutingOperatorStrategy.value_eq_payoff]
  constructor
  · rintro ⟨p, ⟨S, rfl⟩, rfl⟩
    exact ⟨S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.correlation, ⟨S, rfl⟩, rfl⟩

/-! ## Tensor-product strategies -/

/-- A POVM of the vendored core on `ℂ^d`, as a POVM of this repository on `Fin d`. -/
noncomputable def povmOfLiehr {d : ℕ} (M : Tsirelson.POVM (Tsirelson.FinH d) A) :
    POVM A (Fin d) where
  mats a := ⟨Tsirelson.toMat (M.effect a), by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    exact (Tsirelson.posSemidef_toMat (M.positive a)).isHermitian⟩
  nonneg a := Subtype.coe_le_coe.mp
    (Matrix.nonneg_iff_posSemidef.mpr (Tsirelson.posSemidef_toMat (M.positive a)))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ∑ a, Tsirelson.toMat (M.effect a) = 1
    simp only [Tsirelson.toMat]
    rw [← map_sum, M.sum_eq_one, map_one]

@[simp] theorem povmOfLiehr_mats {d : ℕ} (M : Tsirelson.POVM (Tsirelson.FinH d) A) (a : A) :
    ((povmOfLiehr M).mats a).val = Tsirelson.toMat (M.effect a) := rfl

/-- The state of a vendored tensor strategy, as a unit vector of `Fin dA × Fin dB → ℂ`. -/
theorem ofLp_unit (S : Tsirelson.TensorStrategy X Y A B) :
    star (WithLp.ofLp S.ψ) ⬝ᵥ WithLp.ofLp S.ψ = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    S.unit_ψ]
  simp

/-- The correlation of a vendored tensor strategy is the Born probability of its matrices. -/
theorem corr_eq_bornProb (S : Tsirelson.TensorStrategy X Y A B) (x : X) (y : Y) (a : A)
    (b : B) :
    S.corr x y a b = bornProb (WithLp.ofLp S.ψ) (Tsirelson.toMat ((S.alice x).effect a))
      (Tsirelson.toMat ((S.bob y).effect b)) := by
  simp only [Tsirelson.TensorStrategy.corr, Tsirelson.born, Tsirelson.kronCLM, bornProb]
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, dotProduct_comm]

/-- **Every vendored tensor correlation is a projective tensor correlation of this repository**:
Naimark dilation of both POVM families, on the twice-extended state, then a reindexing of the
two registers to `Fin`. -/
theorem tensorCorrelations_subset_Cq [Nonempty A] [Nonempty B] :
    Tsirelson.TensorCorrelations X Y A B ⊆ Cq X Y A B := by
  classical
  rintro p ⟨S, rfl⟩
  have hψ := ofLp_unit S
  obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
  obtain ⟨b₀⟩ := (inferInstance : Nonempty B)
  obtain ⟨PA, hPA⟩ := exists_projective_dilation_povm (fun x => povmOfLiehr (S.alice x)) a₀
  obtain ⟨PB, hPB⟩ := exists_projective_dilation_povm (fun y => povmOfLiehr (S.bob y)) b₀
  let eA : Fin S.dA × A ≃ Fin (S.dA * Fintype.card A) :=
    (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin A)).trans finProdFinEquiv
  let eB : Fin S.dB × B ≃ Fin (S.dB * Fintype.card B) :=
    (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin B)).trans finProdFinEquiv
  refine ⟨S.dA * Fintype.card A, S.dB * Fintype.card B,
    reindexVec eA eB (extVec2 (WithLp.ofLp S.ψ) a₀ b₀),
    reindexVec_unit eA eB (extVec2_unit hψ a₀ b₀),
    PA.map (reindexStarAlgEquiv eA), PB.map (reindexStarAlgEquiv eB), ?_⟩
  funext x y a b
  have hA : ancCompress a₀ (PA.M x a) = Tsirelson.toMat ((S.alice x).effect a) :=
    congrArg (fun M : POVM A (Fin S.dA) => (M.mats a).val) (hPA x)
  have hB : ancCompress b₀ (PB.M y b) = Tsirelson.toMat ((S.bob y).effect b) :=
    congrArg (fun M : POVM B (Fin S.dB) => (M.mats b).val) (hPB y)
  rw [corr_eq_bornProb, ← hA, ← hB]
  show bornProb _ _ _ = bornProb (reindexVec eA eB (extVec2 (WithLp.ofLp S.ψ) a₀ b₀))
    (Matrix.reindex eA eA (PA.M x a)) (Matrix.reindex eB eB (PB.M y b))
  rw [bornProb_reindex, bornProb_extVec2]
  rfl

/-- The vendored `C_qa` is contained in this repository's. -/
theorem tensorCorrelationClosure_subset_Cqa [Nonempty A] [Nonempty B] :
    Tsirelson.TensorCorrelationClosure X Y A B ⊆ Cqa X Y A B :=
  closure_mono tensorCorrelations_subset_Cq

/-- The vendored finite-dimensional value is at most the quantum value of this repository. -/
theorem valStar_toLiehr_le [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (G : Game X Y A B) : Tsirelson.valStar (toLiehr G) ≤ quantumValue G :=
  Tsirelson.valStar_le_of_forall _ (quantumValue_nonneg G) fun p hp => by
    rw [payoff_toLiehr]
    exact payoff_le_quantumValue_of_mem_Cq G (tensorCorrelations_subset_Cq hp)

end MIPRE.Liehr
