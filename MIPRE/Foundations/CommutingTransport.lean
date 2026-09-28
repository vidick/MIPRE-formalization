/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Correlations
public import MIPRE.Foundations.GameDouble

@[expose] public section

/-!
# Transport of commuting-operator strategies

The commuting-operator counterparts of the transport lemmas of `GameTransport.lean` and
`GameDouble.lean`, for the bipartite commuting-operator value `ω_co`
(`MIPRE.commutingOperatorValue`), in which the `MIP^co = coRE` track reads the halting
reduction (`planning/mipco-track.md`, Phase 0):

* **Relabeling.** `commutingOperatorValue_eq_of_equiv`: games related by equivalences of their
  four alphabets, with matching distribution and decision predicate, have the same
  commuting-operator value. Strategies are transported by `CommutingOperatorStrategy.relabel`.
* **Monotonicity.** `commutingOperatorValue_mono`: accepting more answer tuples, on the same
  alphabets and distribution, can only raise the value. A commuting-operator strategy does not
  mention the game it is played in, so the *same* strategy is played.
* **Answer extension.** `commutingOperatorValue_extendAnswers`: enlarging the answer alphabets
  by answers that are always rejected does not change the value. From the small game to the
  large one a strategy extends by the zero operator on the new answers
  (`CommutingOperatorStrategy.extendAnswers`); from the large game to the small one the new
  answers are merged into an old one (`CommutingOperatorStrategy.mergeAnswers`). For POVMs the
  merge is a sum of positive operators and needs none of the orthogonality that
  `ProjectiveMeasurement.merge` does.
* **Doubling.** `commutingOperatorValue_doubled`: the doubled game (`MIPRE.Game.doubled`) has
  the commuting-operator value of the game it doubles, by the same two relabelings as
  `quantumValue_doubled` and the same computation `Game.sum_doubled`.
-/

namespace MIPRE

open scoped BigOperators InnerProductSpace

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

namespace CommutingOperatorStrategy

/-! ## Relabeling -/

/-- Play `S` through relabelings of the questions (any maps) and of the answers
(equivalences). The Hilbert space and the state are those of `S`. -/
def relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : CommutingOperatorStrategy X Y A B) (eX : X' → X) (eY : Y' → Y) (eA : A' ≃ A)
    (eB : B' ≃ B) : CommutingOperatorStrategy X' Y' A' B' where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  E x' a' := S.E (eX x') (eA a')
  F y' b' := S.F (eY y') (eB b')
  E_pos x' a' := S.E_pos _ _
  F_pos y' b' := S.F_pos _ _
  E_sum x' := by rw [eA.sum_comp fun a => S.E (eX x') a]; exact S.E_sum _
  F_sum y' := by rw [eB.sum_comp fun b => S.F (eY y') b]; exact S.F_sum _
  commutes x' y' a' b' := S.commutes _ _ _ _

@[simp] theorem relabel_correlation {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
    [Fintype B'] (S : CommutingOperatorStrategy X Y A B) (eX : X' → X) (eY : Y' → Y)
    (eA : A' ≃ A) (eB : B' ≃ B) (x' : X') (y' : Y') (a' : A') (b' : B') :
    (S.relabel eX eY eA eB).correlation x' y' a' b' =
      S.correlation (eX x') (eY y') (eA a') (eB b') := rfl

/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : CommutingOperatorStrategy X Y A B) (G : Game X Y A B) (G' : Game X' Y' A' B')
    (eX : X' ≃ X) (eY : Y' ≃ Y) (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel eX eY eA eB).value G' = S.value G := by
  unfold value
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eY.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eB.symm _ _ fun b => ?_
  simp only [hμ, hD, relabel_correlation, Equiv.apply_symm_apply]

/-- Accepting more answer tuples raises the value of a strategy. -/
theorem value_le_of_accepts_imp (S : CommutingOperatorStrategy X Y A B) (G G' : Game X Y A B)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value G ≤ S.value G' := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
    (S.correlation_nonneg x y a b)
  cases h : G.D x y a b with
  | false => by_cases h' : G'.D x y a b = true <;> simp [h']
  | true => rw [hD x y a b h]

/-! ## Answer extension and merging -/

/-- Extend the answer alphabets along embeddings, with the zero operator on the new
answers. -/
noncomputable def extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B']
    (S : CommutingOperatorStrategy X Y A B) (ιA : A ↪ A') (ιB : B ↪ B') :
    CommutingOperatorStrategy X Y A' B' where
  H := S.H
  ψ := S.ψ
  ψ_norm := S.ψ_norm
  E x a' := Function.extend ιA (S.E x) 0 a'
  F y b' := Function.extend ιB (S.F y) 0 b'
  E_pos x a' := by
    by_cases h : ∃ a, ιA a = a'
    · obtain ⟨a, rfl⟩ := h
      rw [ιA.injective.extend_apply]
      exact S.E_pos x a
    · rw [Function.extend_apply' _ _ _ h]
      exact ContinuousLinearMap.isPositive_zero
  F_pos y b' := by
    by_cases h : ∃ b, ιB b = b'
    · obtain ⟨b, rfl⟩ := h
      rw [ιB.injective.extend_apply]
      exact S.F_pos y b
    · rw [Function.extend_apply' _ _ _ h]
      exact ContinuousLinearMap.isPositive_zero
  E_sum x := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιA)) ?_, Finset.sum_map]
    · simp only [ιA.injective.extend_apply]
      exact S.E_sum x
    · intro a' _ ha'
      rw [Function.extend_apply' _ _ _ fun ⟨a, ha⟩ =>
        ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)]
      rfl
  F_sum y := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιB)) ?_, Finset.sum_map]
    · simp only [ιB.injective.extend_apply]
      exact S.F_sum y
    · intro b' _ hb'
      rw [Function.extend_apply' _ _ _ fun ⟨b, hb⟩ =>
        hb' (Finset.mem_map.2 ⟨b, Finset.mem_univ b, hb⟩)]
      rfl
  commutes x y a' b' := by
    by_cases ha : ∃ a, ιA a = a'
    · obtain ⟨a, rfl⟩ := ha
      rw [ιA.injective.extend_apply]
      by_cases hb : ∃ b, ιB b = b'
      · obtain ⟨b, rfl⟩ := hb
        rw [ιB.injective.extend_apply]
        exact S.commutes x y a b
      · rw [Function.extend_apply' _ _ _ hb]
        exact Commute.zero_right _
    · rw [Function.extend_apply' _ _ _ ha]
      exact Commute.zero_left _

section extendAnswers

variable {A' B' : Type*} [Fintype A'] [Fintype B'] (S : CommutingOperatorStrategy X Y A B)
  (ιA : A ↪ A') (ιB : B ↪ B')

@[simp] theorem extendAnswers_E_apply (x : X) (a : A) :
    (S.extendAnswers ιA ιB).E x (ιA a) = S.E x a :=
  ιA.injective.extend_apply _ _ a

theorem extendAnswers_E_of_not_mem (x : X) {a' : A'} (h : ¬∃ a, ιA a = a') :
    (S.extendAnswers ιA ιB).E x a' = 0 :=
  Function.extend_apply' _ _ _ h

@[simp] theorem extendAnswers_F_apply (y : Y) (b : B) :
    (S.extendAnswers ιA ιB).F y (ιB b) = S.F y b :=
  ιB.injective.extend_apply _ _ b

theorem extendAnswers_F_of_not_mem (y : Y) {b' : B'} (h : ¬∃ b, ιB b = b') :
    (S.extendAnswers ιA ιB).F y b' = 0 :=
  Function.extend_apply' _ _ _ h

/-- On the old answers the extended strategy has the old correlation. -/
theorem correlation_extendAnswers (x : X) (y : Y) (a : A) (b : B) :
    (S.extendAnswers ιA ιB).correlation x y (ιA a) (ιB b) = S.correlation x y a b := by
  show (⟪S.ψ, (S.extendAnswers ιA ιB).E x (ιA a) ((S.extendAnswers ιA ιB).F y (ιB b) S.ψ)⟫_ℂ).re
    = _
  rw [extendAnswers_E_apply, extendAnswers_F_apply]
  rfl

/-- Off the range of `ιA` the extended strategy has correlation `0`. -/
theorem correlation_extendAnswers_of_not_mem_left (x : X) (y : Y) {a' : A'} (b' : B')
    (h : ¬∃ a, ιA a = a') : (S.extendAnswers ιA ιB).correlation x y a' b' = 0 := by
  show (⟪(S.extendAnswers ιA ιB).ψ, (S.extendAnswers ιA ιB).E x a'
    ((S.extendAnswers ιA ιB).F y b' (S.extendAnswers ιA ιB).ψ)⟫_ℂ).re = 0
  rw [extendAnswers_E_of_not_mem _ _ _ _ h]
  simp

/-- Off the range of `ιB` the extended strategy has correlation `0`. -/
theorem correlation_extendAnswers_of_not_mem_right (x : X) (y : Y) (a' : A') {b' : B'}
    (h : ¬∃ b, ιB b = b') : (S.extendAnswers ιA ιB).correlation x y a' b' = 0 := by
  show (⟪(S.extendAnswers ιA ιB).ψ, (S.extendAnswers ιA ιB).E x a'
    ((S.extendAnswers ιA ιB).F y b' (S.extendAnswers ιA ιB).ψ)⟫_ℂ).re = 0
  rw [extendAnswers_F_of_not_mem _ _ _ _ h]
  simp

/-- Zero extension preserves the value, whatever the decision predicate does on the new
answers: their terms vanish. -/
theorem value_extendAnswers (G : Game X Y A B) (G' : Game X Y A' B')
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b) :
    (S.extendAnswers ιA ιB).value G' = S.value G := by
  unfold value
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  -- restrict the outer answer sum to the range of `ιA`
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιA)) ?_, Finset.sum_map]
  swap
  · intro a' _ ha'
    have h0 : ∀ b', (S.extendAnswers ιA ιB).correlation x y a' b' = 0 := fun b' =>
      S.correlation_extendAnswers_of_not_mem_left ιA ιB x y b' fun ⟨a, ha⟩ =>
        ha' (Finset.mem_map.2 ⟨a, Finset.mem_univ a, ha⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ιB)) ?_, Finset.sum_map]
  swap
  · intro b' _ hb'
    have h0 : (S.extendAnswers ιA ιB).correlation x y (ιA a) b' = 0 :=
      S.correlation_extendAnswers_of_not_mem_right ιA ιB x y (ιA a) fun ⟨b, hb⟩ =>
        hb' (Finset.mem_map.2 ⟨b, Finset.mem_univ b, hb⟩)
    simp [h0]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hμ, hD, correlation_extendAnswers]

end extendAnswers

/-- Merge the answers along maps back to smaller alphabets: the effect of `a` is the sum of
the effects of the answers `a'` with `r a' = a`. For POVMs this needs no orthogonality: a sum
of positive operators is positive, the fibers partition the alphabet, and sums of operators
that commute with one another commute. -/
noncomputable def mergeAnswers {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A]
    [DecidableEq B] (S' : CommutingOperatorStrategy X Y A' B') (rA : A' → A) (rB : B' → B) :
    CommutingOperatorStrategy X Y A B where
  H := S'.H
  ψ := S'.ψ
  ψ_norm := S'.ψ_norm
  E x a := ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), S'.E x a'
  F y b := ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), S'.F y b'
  E_pos x a := ContinuousLinearMap.isPositive_sum _ fun a' _ => S'.E_pos x a'
  F_pos y b := ContinuousLinearMap.isPositive_sum _ fun b' _ => S'.F_pos y b'
  E_sum x := by rw [Finset.sum_fiberwise]; exact S'.E_sum x
  F_sum y := by rw [Finset.sum_fiberwise]; exact S'.F_sum y
  commutes x y a b :=
    Commute.sum_left _ _ _ fun a' _ => Commute.sum_right _ _ _ fun b' _ => S'.commutes x y a' b'

section mergeAnswers

variable {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]
  (S' : CommutingOperatorStrategy X Y A' B') (rA : A' → A) (rB : B' → B)

@[simp] theorem mergeAnswers_E (x : X) (a : A) :
    (S'.mergeAnswers rA rB).E x a = ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), S'.E x a' :=
  rfl

@[simp] theorem mergeAnswers_F (y : Y) (b : B) :
    (S'.mergeAnswers rA rB).F y b = ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), S'.F y b' :=
  rfl

/-- The Born-rule weight of a merged answer pair is the sum of the weights over the fibers. -/
theorem correlation_mergeAnswers (x : X) (y : Y) (a : A) (b : B) :
    (S'.mergeAnswers rA rB).correlation x y a b =
      ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
        ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), S'.correlation x y a' b' := by
  show (⟪S'.ψ, (∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), S'.E x a')
    ((∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), S'.F y b') S'.ψ)⟫_ℂ).re = _
  simp only [_root_.sum_apply, map_sum, inner_sum, Complex.re_sum, correlation]
  exact Finset.sum_comm

/-- Merging can only raise the value, when every accepted tuple of the large game is
accepted after merging. -/
theorem value_le_mergeAnswers (G' : Game X Y A' B') (G : Game X Y A B)
    (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA a') (rB b') = true) :
    S'.value G' ≤ (S'.mergeAnswers rA rB).value G := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  simp_rw [correlation_mergeAnswers]
  calc ∑ a', ∑ b', G'.μ x y * (if G'.D x y a' b' then 1 else 0) * S'.correlation x y a' b'
      ≤ ∑ a', ∑ b', G.μ x y * (if G.D x y (rA a') (rB b') then 1 else 0) *
          S'.correlation x y a' b' := by
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        rw [hμ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G'.μ_nonneg x y))
          (S'.correlation_nonneg x y a' b')
        cases h : G'.D x y a' b' with
        | false => by_cases h' : G.D x y (rA a') (rB b') = true <;> simp [h']
        | true => rw [hD x y a' b' h]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b),
            G.μ x y * (if G.D x y (rA a') (rB b') then 1 else 0) * S'.correlation x y a' b' := by
        rw [Finset.sum_fiberwise Finset.univ rA]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_fiberwise Finset.univ rB]
    _ = ∑ a, ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a), ∑ b,
          ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b),
            G.μ x y * (if G.D x y a b then 1 else 0) * S'.correlation x y a' b' := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' ha' =>
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' hb' => ?_
        rw [(Finset.mem_filter.1 ha').2, (Finset.mem_filter.1 hb').2]
    _ = ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
          ∑ a' ∈ Finset.univ.filter (fun a' => rA a' = a),
            ∑ b' ∈ Finset.univ.filter (fun b' => rB b' = b), S'.correlation x y a' b' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]

end mergeAnswers

end CommutingOperatorStrategy

/-! ## The commuting-operator value under transport -/

/-- Games related by equivalences of their alphabets, with matching distribution and
decision predicate, have the same commuting-operator value. -/
theorem commutingOperatorValue_eq_of_equiv {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y']
    [Fintype A'] [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X)
    (eY : Y' ≃ Y) (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    commutingOperatorValue G' = commutingOperatorValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (commutingOperatorValue_nonneg _)
    have h := (S'.relabel eX.symm eY.symm eA.symm eB.symm).value_le_commutingOperatorValue G
    rwa [S'.value_relabel G' G eX.symm eY.symm eA.symm eB.symm (fun x y => by simp [hμ])
      (fun x y a b => by simp [hD])] at h
  · refine Real.iSup_le (fun S => ?_) (commutingOperatorValue_nonneg _)
    have h := (S.relabel eX eY eA eB).value_le_commutingOperatorValue G'
    rwa [S.value_relabel G G' eX eY eA eB hμ hD] at h

/-- Accepting more answer tuples, on the same alphabets and distribution, raises the
commuting-operator value. -/
theorem commutingOperatorValue_mono (G G' : Game X Y A B) (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    commutingOperatorValue G ≤ commutingOperatorValue G' :=
  Real.iSup_le (fun S => (S.value_le_of_accepts_imp G G' hμ hD).trans
    (S.value_le_commutingOperatorValue G')) (commutingOperatorValue_nonneg _)

/-- A game whose decision predicate rejects everything has commuting-operator value `0`. -/
theorem commutingOperatorValue_eq_zero_of_reject (G : Game X Y A B)
    (hD : ∀ x y a b, G.D x y a b = false) : commutingOperatorValue G = 0 := by
  refine le_antisymm (Real.iSup_le (fun S => ?_) le_rfl) (commutingOperatorValue_nonneg G)
  unfold CommutingOperatorStrategy.value
  simp [hD]

/-- Enlarging the answer alphabets by always-rejected answers does not change the
commuting-operator value. `G'` on `A' × B'` accepts `(ιA a, ιB b)` exactly when `G` accepts
`(a, b)`, and accepts nothing off the ranges of the embeddings. -/
theorem commutingOperatorValue_extendAnswers {A' B' : Type*} [Fintype A'] [Fintype B']
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B] (G : Game X Y A B)
    (G' : Game X Y A' B') (ιA : A ↪ A') (ιB : B ↪ B') (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G'.D x y (ιA a) (ιB b) = G.D x y a b)
    (hD' : ∀ x y a' b', G'.D x y a' b' = true → (∃ a, ιA a = a') ∧ (∃ b, ιB b = b')) :
    commutingOperatorValue G' = commutingOperatorValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (commutingOperatorValue_nonneg _)
    refine (S'.value_le_mergeAnswers (Function.invFun ιA) (Function.invFun ιB) G' G
      (fun x y => (hμ x y).symm) ?_).trans
      ((S'.mergeAnswers _ _).value_le_commutingOperatorValue G)
    intro x y a' b' h
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hD' x y a' b' h
    rw [Function.leftInverse_invFun ιA.injective, Function.leftInverse_invFun ιB.injective,
      ← hD]
    exact h
  · refine Real.iSup_le (fun S => ?_) (commutingOperatorValue_nonneg _)
    rw [← S.value_extendAnswers ιA ιB G G' hμ hD]
    exact (S.extendAnswers ιA ιB).value_le_commutingOperatorValue G'

/-! ## The doubled game -/

namespace CommutingOperatorStrategy

variable [DecidableEq A]

/-- A strategy for the doubled game, read on the original: the first player keeps the effects
at `(false, ·)`, the second those at `(true, ·)`. -/
def undouble (S : CommutingOperatorStrategy (Bool × X) (Bool × X) A A) :
    CommutingOperatorStrategy X X A A :=
  S.relabel (fun x => (false, x)) (fun y => (true, y)) (Equiv.refl A) (Equiv.refl A)

/-- A strategy for the original game, read on the doubled one: both players ignore the tag. -/
def double (S : CommutingOperatorStrategy X X A A) :
    CommutingOperatorStrategy (Bool × X) (Bool × X) A A :=
  S.relabel (fun p => p.2) (fun q => q.2) (Equiv.refl A) (Equiv.refl A)

theorem value_undouble (G : Game X X A A)
    (S : CommutingOperatorStrategy (Bool × X) (Bool × X) A A) :
    S.undouble.value G = S.value G.doubled.toGame := by
  rw [show S.value G.doubled.toGame = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) * S.correlation p q a b from rfl,
    Game.sum_doubled]
  rfl

theorem value_double (G : Game X X A A) (S : CommutingOperatorStrategy X X A A) :
    S.double.value G.doubled.toGame = S.value G := by
  rw [show S.double.value G.doubled.toGame = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) * S.correlation p.2 q.2 a b from rfl,
    Game.sum_doubled]
  rfl

end CommutingOperatorStrategy

/-- **The doubling preserves the commuting-operator value.** Each direction is one strategy
transported and one comparison with the supremum. -/
theorem commutingOperatorValue_doubled [DecidableEq A] (G : Game X X A A) :
    commutingOperatorValue G.doubled.toGame = commutingOperatorValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (commutingOperatorValue_nonneg _)
    rw [← S.value_undouble G]
    exact S.undouble.value_le_commutingOperatorValue G
  · refine Real.iSup_le (fun S => ?_) (commutingOperatorValue_nonneg _)
    rw [← S.value_double G]
    exact S.double.value_le_commutingOperatorValue G.doubled.toGame

end MIPRE

end
