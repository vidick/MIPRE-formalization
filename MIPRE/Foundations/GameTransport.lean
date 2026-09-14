/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Games

/-!
# Transport of games and strategies

Bookkeeping lemmas about the quantum value under changes of presentation of a game, used to
identify a verifier's game with its tabulation as a game description and to compare the same
game under different answer-length bounds (blueprint `rem:compression-abstract`):

* **Relabeling.** `quantumValue_eq_of_equiv`: two games related by equivalences of their four
  alphabets, with matching distribution and decision predicate, have the same quantum value.
  Strategies are transported by `TensorProductStrategy.relabel`.
* **Monotonicity.** `quantumValue_mono`: accepting more answer tuples, on the same alphabets
  and distribution, can only raise the value.
* **Answer extension.** `quantumValue_extendAnswers`: enlarging the answer alphabets by
  answers that are always rejected does not change the value. From the small game to the
  large one a strategy extends by zero operators (`ProjectiveMeasurement.extend`); from the
  large game to the small one the new answers are merged into an old one
  (`ProjectiveMeasurement.merge`), which needs the orthogonality of the outcomes of a
  projective measurement (`ProjectiveMeasurement.mul_eq_zero_of_ne`) and can only raise the
  value.
* The synchronous counterparts for PCC strategies: `SyncStrategy.extend` keeps the value and
  the PCC property, and the constant strategy `SyncStrategy.const` is PCC with value the
  acceptance mass of a fixed answer pair.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder

/-! ## Projective measurements: relabeling, zero extension, merging -/

namespace ProjectiveMeasurement

variable {X A : Type*} [Fintype A] {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜]

/-- Relabel the questions along a function and the answers along an equivalence. -/
def reindex {X' A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜) (eX : X' → X)
    (eA : A' ≃ A) : ProjectiveMeasurement X' A' 𝒜 where
  M x' a' := P.M (eX x') (eA a')
  selfAdjoint x' a' := P.selfAdjoint _ _
  projective x' a' := P.projective _ _
  normalized x' := by rw [eA.sum_comp fun a => P.M (eX x') a]; exact P.normalized _

@[simp] theorem reindex_M {X' A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (eX : X' → X) (eA : A' ≃ A) (x' : X') (a' : A') :
    (P.reindex eX eA).M x' a' = P.M (eX x') (eA a') := rfl

/-- Extend the answer alphabet along an embedding, with the zero operator on the new
answers. -/
noncomputable def extend {A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (ι : A ↪ A') :
    ProjectiveMeasurement X A' 𝒜 where
  M x a' := Function.extend ι (P.M x) 0 a'
  selfAdjoint x a' := by
    by_cases h : ∃ a, ι a = a'
    · obtain ⟨a, rfl⟩ := h
      rw [ι.injective.extend_apply]
      exact P.selfAdjoint x a
    · rw [Function.extend_apply' _ _ _ h]
      simp
  projective x a' := by
    by_cases h : ∃ a, ι a = a'
    · obtain ⟨a, rfl⟩ := h
      rw [ι.injective.extend_apply]
      exact P.projective x a
    · rw [Function.extend_apply' _ _ _ h]
      simp
  normalized x := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι)) ?_, Finset.sum_map]
    · simp only [ι.injective.extend_apply]
      exact P.normalized x
    · intro a' _ ha'
      rw [Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)]
      rfl

@[simp] theorem extend_M_apply {A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (ι : A ↪ A') (x : X) (a : A) : (P.extend ι).M x (ι a) = P.M x a :=
  ι.injective.extend_apply _ _ a

theorem extend_M_of_not_mem {A' : Type*} [Fintype A'] (P : ProjectiveMeasurement X A 𝒜)
    (ι : A ↪ A') (x : X) {a' : A'} (h : ¬∃ a, ι a = a') : (P.extend ι).M x a' = 0 :=
  Function.extend_apply' _ _ _ h

/-- The outcomes of a projective measurement on `ℂ^n` are mutually orthogonal:
`M x a * M x b = 0` for `a ≠ b`. -/
theorem mul_eq_zero_of_ne {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) {a b : A} (hab : a ≠ b) :
    P.M x a * P.M x b = 0 := by
  classical
  -- `M a = ∑ c, M a * M c * M a`, and the term `c = a` is `M a` itself
  have hsum : ∑ c ∈ Finset.univ.erase a, P.M x a * P.M x c * P.M x a = 0 := by
    have h1 : P.M x a = ∑ c, P.M x a * P.M x c * P.M x a := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, P.normalized, mul_one, P.projective]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), P.projective, P.projective] at h1
    exact (add_eq_left.1 h1.symm)
  -- each term is `(M c * M a)ᴴ * (M c * M a)`, positive semidefinite
  have hterm : ∀ c, P.M x a * P.M x c * P.M x a = (P.M x c * P.M x a)ᴴ * (P.M x c * P.M x a) := by
    intro c
    rw [conjTranspose_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose, P.selfAdjoint,
      P.selfAdjoint, mul_assoc, mul_assoc, ← mul_assoc (P.M x c), P.projective]
  have htr : ∀ c ∈ Finset.univ.erase a, (P.M x a * P.M x c * P.M x a).trace = 0 := by
    have hnn : ∀ c ∈ Finset.univ.erase a, 0 ≤ (P.M x a * P.M x c * P.M x a).trace := by
      intro c _
      rw [hterm]
      exact (posSemidef_conjTranspose_mul_self _).trace_nonneg
    have := congrArg Matrix.trace hsum
    rw [trace_sum, trace_zero] at this
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 this
  have hba : P.M x b * P.M x a = 0 := by
    have h := htr b (Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩)
    rw [hterm] at h
    exact trace_conjTranspose_mul_self_eq_zero_iff.1 h
  have : P.M x a * P.M x b = (P.M x b * P.M x a)ᴴ := by
    rw [conjTranspose_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose, P.selfAdjoint,
      P.selfAdjoint]
  rw [this, hba, conjTranspose_zero]

/-- Merge the outcomes of a projective measurement along a map `r` of the answers: the
outcome `a` is the sum of the outcomes `a'` with `r a' = a`. -/
def merge {A' : Type*} [Fintype A'] [DecidableEq A] {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A' (Matrix n n ℂ)) (r : A' → A) :
    ProjectiveMeasurement X A (Matrix n n ℂ) where
  M x a := ∑ a' ∈ Finset.univ.filter (fun a' => r a' = a), P.M x a'
  selfAdjoint x a := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun a' _ => P.selfAdjoint x a'
  projective x a := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    rw [Finset.sum_eq_single a' (fun b' _ hb' => P.mul_eq_zero_of_ne x (Ne.symm hb'))
      (fun h => absurd ha' h)]
    exact P.projective x a'
  normalized x := by
    rw [Finset.sum_fiberwise]
    exact P.normalized x

@[simp] theorem merge_M {A' : Type*} [Fintype A'] [DecidableEq A] {n : Type*} [Fintype n]
    [DecidableEq n] (P : ProjectiveMeasurement X A' (Matrix n n ℂ)) (r : A' → A) (x : X)
    (a : A) : (P.merge r).M x a = ∑ a' ∈ Finset.univ.filter (fun a' => r a' = a), P.M x a' :=
  rfl

end ProjectiveMeasurement

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## Tensor-product strategies -/

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-- The same data, as a strategy for another game on the same alphabets. -/
def copy (S : TensorProductStrategy G) (G' : Game X Y A B) : TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA, S.PB⟩

/-- Accepting more answer tuples raises the value of a strategy. -/
theorem value_copy_le (S : TensorProductStrategy G) (G' : Game X Y A B)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
    (S.re_dotProduct_nonneg x y a b)
  cases h : G.D x y a b with
  | false => by_cases h' : G'.D x y a b = true <;> simp [h']
  | true => rw [hD x y a b h]

/-- Play `S` on `G'` through relabelings of the questions (any maps) and of the answers
(equivalences). -/
def relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' → X) (eY : Y' → Y)
    (eA : A' ≃ A) (eB : B' ≃ B) : TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.reindex eX eA, S.PB.reindex eY eB⟩

/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel G' eX eY eA eB).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') (eA a') ⊗ₖ S.PB.M (eY y') (eB b')) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eY.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eB.symm _ _ fun b => ?_
  rw [hμ, hD, eX.apply_symm_apply, eY.apply_symm_apply, eA.apply_symm_apply,
    eB.apply_symm_apply]

/-- Extend the answer alphabets along embeddings, with zero operators on the new answers. -/
noncomputable def extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] (S : TensorProductStrategy G)
    (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B') : TensorProductStrategy G' :=
  ⟨S.dA, S.dB, S.ψ, S.ψ_unit, S.PA.extend ιA, S.PB.extend ιB⟩

/-- Zero extension preserves the value, whatever the decision predicate does on the new
answers: their terms vanish. -/
theorem value_extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B')
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b) :
    (S.extendAnswers G' ιA ιB).value = S.value := by
  unfold value
  show (∑ x, ∑ y, ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ (((S.PA.extend ιA).M x a' ⊗ₖ (S.PB.extend ιB).M y b') *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  -- restrict the outer answer sum to the range of `ιA`
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιA)) ?_, Finset.sum_map]
  swap
  · intro a' _ ha'
    have h0 : (S.PA.extend ιA).M x a' = 0 :=
      S.PA.extend_M_of_not_mem ιA x fun ⟨a, ha⟩ => ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)
    simp [h0, Matrix.zero_mulVec]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιB)) ?_, Finset.sum_map]
  swap
  · intro b' _ hb'
    have h0 : (S.PB.extend ιB).M y b' = 0 :=
      S.PB.extend_M_of_not_mem ιB y fun ⟨b, hb⟩ => hb' (Finset.mem_map.2 ⟨b, Finset.mem_univ b, hb⟩)
    simp [h0, Matrix.zero_mulVec]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ProjectiveMeasurement.extend_M_apply]
  rw [hμ, hD]

/-- Merge the answers along maps back to smaller alphabets. -/
def mergeAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]
    {G' : Game X Y A' B'} (S' : TensorProductStrategy G') (G : Game X Y A B) (rA : A' → A)
    (rB : B' → B) : TensorProductStrategy G :=
  ⟨S'.dA, S'.dB, S'.ψ, S'.ψ_unit, S'.PA.merge rA, S'.PB.merge rB⟩

/-- Merging can only raise the value, when every accepted tuple of the large game is
accepted after merging. -/
theorem value_le_mergeAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A]
    [DecidableEq B] {G' : Game X Y A' B'} (S' : TensorProductStrategy G') (G : Game X Y A B)
    (rA : A' → A) (rB : B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA a') (rB b') = true) :
    S'.value ≤ (S'.mergeAnswers G rA rB).value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  set w : A' → B' → ℝ :=
    fun a' b' => (star S'.ψ ⬝ᵥ ((S'.PA.M x a' ⊗ₖ S'.PB.M y b') *ᵥ S'.ψ)).re with hw
  have hw0 : ∀ a' b', 0 ≤ w a' b' := fun a' b' => S'.re_dotProduct_nonneg x y a' b'
  -- the merged Born-rule weight of `(a, b)` is the sum of the weights over the fibers
  have hbil : ∀ a b, (star S'.ψ ⬝ᵥ (((S'.PA.merge rA).M x a ⊗ₖ (S'.PB.merge rB).M y b) *ᵥ
      S'.ψ)).re = ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
        ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), w a' b' := by
    intro a b
    have hsplit : (S'.PA.merge rA).M x a ⊗ₖ (S'.PB.merge rB).M y b =
        ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), S'.PA.M x a' ⊗ₖ S'.PB.M y b' := by
      ext p q
      simp only [ProjectiveMeasurement.merge_M, Matrix.sum_apply, kroneckerMap_apply,
        Finset.sum_mul_sum]
    rw [hsplit, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  show ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b' ≤
    ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S'.ψ ⬝ᵥ (((S'.PA.merge rA).M x a ⊗ₖ (S'.PB.merge rB).M y b) *ᵥ S'.ψ)).re
  simp_rw [hbil]
  calc ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * w a' b'
      ≤ ∑ a', ∑ b', G.μ x y * (if G.D x y (rA a') (rB b') then 1 else 0) * w a' b' := by
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        rw [hμ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G'.μ_nonneg x y))
          (hw0 a' b')
        cases h : G'.D x y a' b' with
        | false => by_cases h' : G.D x y (rA a') (rB b') = true <;> simp [h']
        | true => rw [hD x y a' b' h]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b),
            G.μ x y * (if G.D x y (rA a') (rB b') then 1 else 0) * w a' b' := by
        rw [Finset.sum_fiberwise Finset.univ rA]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_fiberwise Finset.univ rB]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b),
            G.μ x y * (if G.D x y a b then 1 else 0) * w a' b' := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' ha' =>
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' hb' => ?_
        rw [(Finset.mem_filter.1 ha').2, (Finset.mem_filter.1 hb').2]
    _ = ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
          ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
            ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), w a' b' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]

end TensorProductStrategy

/-! ## The quantum value under transport -/

/-- The quantum value is at most one. -/
theorem quantumValue_le_one (G : Game X Y A B) : quantumValue G ≤ 1 :=
  Real.iSup_le (fun S => S.value_le_one) zero_le_one

/-- Games related by equivalences of their alphabets, with matching distribution and
decision predicate, have the same quantum value. -/
theorem quantumValue_eq_of_equiv {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
    [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G)
      (S'.relabel G eX.symm eY.symm eA.symm eB.symm)
    rwa [S'.value_relabel G eX.symm eY.symm eA.symm eB.symm (fun x y => by simp [hμ])
      (fun x y a b => by simp [hD])] at h
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G')
      (S.relabel G' eX eY eA eB)
    rwa [S.value_relabel G' eX eY eA eB hμ hD] at h

/-- Accepting more answer tuples, on the same alphabets and distribution, raises the quantum
value. -/
theorem quantumValue_mono (G G' : Game X Y A B) (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    quantumValue G ≤ quantumValue G' := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  exact (S.value_copy_le G' hμ hD).trans
    (le_ciSup (TensorProductStrategy.bddAbove_range_value G') (S.copy G'))

/-- A game whose decision predicate rejects everything has quantum value `0`. -/
theorem quantumValue_eq_zero_of_reject (G : Game X Y A B) (hD : ∀ x y a b, G.D x y a b = false) :
    quantumValue G = 0 := by
  refine le_antisymm (Real.iSup_le (fun S => ?_) le_rfl) (quantumValue_nonneg G)
  unfold TensorProductStrategy.value
  simp [hD]

/-- Enlarging the answer alphabets by always-rejected answers does not change the quantum
value. `G'` on `A' × B'` accepts `(ιA a, ιB b)` exactly when `G` accepts `(a, b)`, and accepts
nothing off the ranges of the embeddings. -/
theorem quantumValue_extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (G : Game X Y A B) (G' : Game X Y A' B')
    (ιA : A ↪ A') (ιB : B ↪ B') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b)
    (hD' : ∀ x y a' b', G'.D x y a' b' = true → (∃ a, ιA a = a') ∧ (∃ b, ιB b = b')) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    refine (S'.value_le_mergeAnswers G (Function.invFun ιA) (Function.invFun ιB)
      (fun x y => (hμ x y).symm) ?_).trans
      (le_ciSup (TensorProductStrategy.bddAbove_range_value G) _)
    intro x y a' b' h
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hD' x y a' b' h
    rw [Function.leftInverse_invFun ιA.injective, Function.leftInverse_invFun ιB.injective,
      ← hD]
    exact h
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_extendAnswers G' ιA ιB hμ hD]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G') _

/-! ## Synchronous strategies -/

namespace SyncStrategy

variable [DecidableEq A] {G : SynchronousGame X A}

/-- The same data, as a strategy for another synchronous game on the same alphabets. -/
def copy (S : SyncStrategy G) (G' : SynchronousGame X A) : SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.P⟩

theorem value_copy (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y) (hD : ∀ x y a b, G'.D x y a b = G.D x y a b) :
    (S.copy G').value = S.value := by
  rw [value_eq, value_eq]
  show (∑ x, ∑ y, ∑ a, ∑ b, G'.μ x y * (if G'.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hμ, hD]

theorem isPCC_copy {S : SyncStrategy G} (hS : S.IsPCC) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y) : (S.copy G').IsPCC :=
  fun x y hxy a b => hS x y (by rwa [hμ] at hxy) a b

/-- Extend the answer alphabet along an embedding, with zero operators on the new answers. -/
noncomputable def extend {A' : Type*} [Fintype A'] [DecidableEq A'] (S : SyncStrategy G)
    (G' : SynchronousGame X A') (ι : A ↪ A') : SyncStrategy G' :=
  ⟨S.d, S.d_pos, S.P.extend ι⟩

/-- Zero extension preserves the value of a synchronous strategy. -/
theorem value_extend {A' : Type*} [Fintype A'] [DecidableEq A'] (S : SyncStrategy G)
    (G' : SynchronousGame X A') (ι : A ↪ A') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ι a) (ι b) = G.D x y a b) :
    (S.extend G' ι).value = S.value := by
  rw [value_eq, value_eq]
  show (∑ x, ∑ y, ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) *
      (((S.P.extend ι).M x a' * (S.P.extend ι).M y b').trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι)) ?_, Finset.sum_map]
  swap
  · intro a' _ ha'
    have h0 : (S.P.extend ι).M x a' = 0 :=
      S.P.extend_M_of_not_mem ι x fun ⟨a, ha⟩ => ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι)) ?_, Finset.sum_map]
  swap
  · intro b' _ hb'
    have h0 : (S.P.extend ι).M y b' = 0 :=
      S.P.extend_M_of_not_mem ι y fun ⟨b, hb⟩ => hb' (Finset.mem_map.2 ⟨b, Finset.mem_univ b, hb⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ProjectiveMeasurement.extend_M_apply]
  rw [hμ, hD]

/-- Zero extension preserves the PCC property. -/
theorem isPCC_extend {A' : Type*} [Fintype A'] [DecidableEq A'] {S : SyncStrategy G}
    (hS : S.IsPCC) (G' : SynchronousGame X A') (ι : A ↪ A')
    (hμ : ∀ x y, G'.μ x y = G.μ x y) : (S.extend G' ι).IsPCC := by
  intro x y hxy a' b'
  rw [hμ] at hxy
  show (S.P.extend ι).M x a' * (S.P.extend ι).M y b' = (S.P.extend ι).M y b' * (S.P.extend ι).M x a'
  by_cases ha : ∃ a, ι a = a'
  · obtain ⟨a, rfl⟩ := ha
    by_cases hb : ∃ b, ι b = b'
    · obtain ⟨b, rfl⟩ := hb
      simp only [ProjectiveMeasurement.extend_M_apply]
      exact hS x y hxy a b
    · rw [S.P.extend_M_of_not_mem ι y hb, mul_zero, zero_mul]
  · rw [S.P.extend_M_of_not_mem ι x ha, mul_zero, zero_mul]

/-- The constant strategy: one-dimensional, always answering `a₀`. -/
def const (G : SynchronousGame X A) (a₀ : A) : SyncStrategy G where
  d := 1
  d_pos := Nat.one_pos
  P :=
    { M := fun _ a => if a = a₀ then 1 else 0
      selfAdjoint := fun _ a => by split_ifs <;> simp
      projective := fun _ a => by split_ifs <;> simp
      normalized := fun _ => by simp [Finset.sum_ite_eq'] }

/-- The constant strategy is PCC. -/
theorem isPCC_const (G : SynchronousGame X A) (a₀ : A) : (const G a₀).IsPCC := by
  intro x y _ a b
  show (if a = a₀ then (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) else 0) *
      (if b = a₀ then 1 else 0) = (if b = a₀ then 1 else 0) * (if a = a₀ then 1 else 0)
  split_ifs <;> first | exact Commute.one_left _ | exact Commute.zero_left _

/-- The value of the constant strategy is the acceptance mass of the answer pair `(a₀, a₀)`. -/
theorem value_const (G : SynchronousGame X A) (a₀ : A) :
    (const G a₀).value = ∑ x, ∑ y, G.μ x y * (if G.D x y a₀ a₀ then 1 else 0) := by
  rw [value_eq]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hM : ∀ a b, ((const G a₀).P.M x a * (const G a₀).P.M y b).trace.re /
      ((const G a₀).d : ℝ) = if a = a₀ ∧ b = a₀ then 1 else 0 := by
    intro a b
    show ((if a = a₀ then (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) else 0) *
      (if b = a₀ then 1 else 0)).trace.re / ((const G a₀).d : ℝ) = _
    have hd : ((const G a₀).d : ℝ) = 1 := by simp [const]
    have h11 : (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 1 = 1 := mul_one 1
    have h10 : (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 0 = 0 := mul_zero 1
    have h01 : (0 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 1 = 0 := zero_mul 1
    have h00 : (0 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 0 = 0 := mul_zero 0
    have htr : (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ).trace = 1 := by
      rw [Matrix.trace_one, Fintype.card_fin]
      simp [const]
    split_ifs <;> simp_all
  simp_rw [hM]
  simp [Finset.sum_ite_eq', ite_and]

end SyncStrategy

end MIPRE
