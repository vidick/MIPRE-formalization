/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Stability
public import MIPRE.Tailored.Sofic.Double
public import MIPRE.Tailored.Sofic.Local
public import MIPRE.Tailored.Sofic.Significance

@[expose] public section

/-!
# Perturbing an action to pass Checks 1–3

The construction of Proposition I:2267, on an action `τ` of the associated test's generators that
comes with a fixed-point-free involution `s` commuting with every letter (`SwapData`; the doubled
action of `MIPRE/Tailored/Sofic/Double.lean` has one):

1. `J₁ = invFix J₀`, the involution near `J₀ = τ(J)` (Claim I:2561);
2. `J₂`, the fixed-point-free involution near `J₁`, sending the fixed points of `J₁` along `s`
   (Claim I:2582);
3. at each vertex `x`, the variables `X(x, i)`, `i < ℓ(x)`, repaired by `commFix` with the central
   involution `J₂` (Claims I:2600 and I:2643 together, and the readable repair of the paper's
   last step); the other generators are unchanged.

The result `perturbed τ S` passes Checks 1–3 at every point (`checks_perturbed`). The distances
moved are bounded by the numbers of points at which the relations of Checks 1–3 fail
(`diffCard_J₂_le`, `diffCard_Xfix_le`, `card_bad_le`), which the next file bounds by the
probability of losing the test.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue Finset

/-- A fixed-point-free involution of the points of `τ` commuting with every letter. -/
structure SwapData {n : ℕ} (τ : FiniteAction n) where
  s : Equiv.Perm (Fin τ.N)
  invol : ∀ q, s (s q) = q
  free : ∀ q, s q ≠ q
  comm : ∀ l q, τ.letterPerm l (s q) = s (τ.letterPerm l q)

/-- The swap of the doubled action. -/
def dblSwapData {n : ℕ} (σ : FiniteAction n) : SwapData (double σ) where
  s := dblSwap σ
  invol := dblSwap_invol σ
  free := dblSwap_free σ
  comm := dblSwap_comm σ

variable {g : TailoredGameData} (τ : FiniteAction (nGen g)) (S : SwapData τ)

/-- `J₀ = τ(J)`. -/
abbrev J₀ : Equiv.Perm (Fin τ.N) := genPerm τ genJ

/-- Step 1: the involution `J₁` near `J₀`. -/
def J₁ : Equiv.Perm (Fin τ.N) := invFix (J₀ τ)

theorem J₁_comm (q : Fin τ.N) : J₁ τ (S.s q) = S.s (J₁ τ q) :=
  invFix_comm _ _ (S.comm (genJ, false)) q

/-- Step 2: the fixed-point-free involution `J₂` near `J₁`. -/
def J₂ : Equiv.Perm (Fin τ.N) :=
  fpfFix (J₁ τ) S.s (invFix_invol _) S.invol (J₁_comm τ S)

theorem J₂_invol (q : Fin τ.N) : J₂ τ S (J₂ τ S q) = q := fpfFix_invol q

theorem J₂_free (q : Fin τ.N) : J₂ τ S q ≠ q := fpfFix_free S.free q

/-- The variables at the vertex `x`. -/
abbrev Xv (g : TailoredGameData) (τ : FiniteAction (nGen g)) (x : ℕ) : ℕ → Equiv.Perm (Fin τ.N) :=
  fun i => genPerm τ (genX g x i)

/-- Step 3: the repaired variables at the vertex `x`. -/
noncomputable def Xfix (x i : ℕ) : Equiv.Perm (Fin τ.N) :=
  commFix (Xv g τ x) (g.lenAt x) (g.lenRAt x) (J₂ τ S) i

/-- The perturbed generators: `J₂` for `J`, the repaired variables for the `X(x, i)`, `i < ℓ(x)`,
and the other generators unchanged. -/
noncomputable def ρPert (k : Fin (nGen g)) : Equiv.Perm (Fin τ.N) :=
  if k.val = genJ then J₂ τ S
  else if (k.val - 1) / g.ansLen < g.nV + 1 ∧
      (k.val - 1) % g.ansLen < g.lenAt ((k.val - 1) / g.ansLen) then
    Xfix τ S ((k.val - 1) / g.ansLen) ((k.val - 1) % g.ansLen)
  else τ.σ k

/-- **The perturbed action.** -/
noncomputable def perturbed : FiniteAction (nGen g) := withPerms τ (ρPert τ S)

theorem genX_lt_nGen {x i : ℕ} (hx : x < g.nV + 1) (hi : i < g.ansLen) :
    genX g x i < nGen g := by
  unfold genX nGen
  have : x * g.ansLen + g.ansLen ≤ (g.nV + 1) * g.ansLen := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hx
  omega

theorem genJ_lt_nGen : genJ < nGen g := by unfold genJ nGen; omega

theorem genPerm_eq (σ : FiniteAction (nGen g)) {k : ℕ} (hk : k < nGen g) :
    genPerm σ k = σ.σ ⟨k, hk⟩ := by
  simp [genPerm, FiniteAction.letterPerm, hk]

theorem genX_decode {x i : ℕ} (hi : i < g.ansLen) :
    (genX g x i - 1) / g.ansLen = x ∧ (genX g x i - 1) % g.ansLen = i := by
  have hL : 0 < g.ansLen := by omega
  have e : genX g x i - 1 = i + g.ansLen * x := by unfold genX; rw [Nat.mul_comm]; omega
  rw [e, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hi, zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hi]
  exact ⟨rfl, rfl⟩

theorem perturbed_J : genPerm (perturbed τ S) genJ = J₂ τ S := by
  rw [genPerm_eq _ genJ_lt_nGen]
  simp [perturbed, ρPert]

theorem perturbed_X {x i : ℕ} (hx : x < g.nV + 1) (hi : i < g.lenAt x) :
    genPerm (perturbed τ S) (genX g x i) = Xfix τ S x i := by
  have hiL : i < g.ansLen := lt_of_lt_of_le hi (lenAt_le_ansLen hx)
  rw [genPerm_eq _ (genX_lt_nGen hx hiL)]
  obtain ⟨h1, h2⟩ := genX_decode (g := g) (x := x) hiL
  simp only [perturbed, withPerms, ρPert]
  rw [ite_eq_right (genX_ne_genJ x i), h1, h2, ite_eq_left ⟨hx, hi⟩]

theorem perturbed_other (k : Fin (nGen g)) (hk : k.val ≠ genJ)
    (hx : ¬((k.val - 1) / g.ansLen < g.nV + 1 ∧
      (k.val - 1) % g.ansLen < g.lenAt ((k.val - 1) / g.ansLen))) :
    ρPert τ S k = τ.σ k := by
  simp only [ρPert]
  rw [ite_eq_right hk, ite_eq_right hx]

/-- **The perturbed action passes Checks 1–3** (Proposition I:2267). -/
theorem checks_perturbed : Checks g (perturbed τ S) where
  J_invol p := by rw [perturbed_J]; exact J₂_invol τ S p
  J_free p := by rw [perturbed_J]; exact J₂_free τ S p
  J_comm x i hx hi := by
    rw [perturbed_J, perturbed_X τ S hx hi]
    exact commFix_J (J₂_invol τ S) hi
  X_invol x i hx hi p := by
    rw [perturbed_X τ S hx hi]
    exact commFix_invol i p
  X_comm x i i' hx hi hi' := by
    rw [perturbed_X τ S hx hi, perturbed_X τ S hx hi']
    exact commFix_comm hi hi'
  readable x i hx hi p := by
    rw [perturbed_J, perturbed_X τ S hx (lt_of_lt_of_le hi (lenRAt_le_lenAt x))]
    exact commFix_readable (lenRAt_le_lenAt x) hi p

/-! ## Distances -/

/-- The number of fixed points of `J₀`. -/
def fixJ : ℕ := (univ.filter fun q => J₀ τ q = q).card

/-- The number of points `J₀²` moves. -/
def sqJ : ℕ := (univ.filter fun q => J₀ τ (J₀ τ q) ≠ q).card

theorem diffCard_J₂_le : diffCard (J₂ τ S) (J₀ τ) ≤ fixJ τ + 2 * sqJ τ := by
  have h1 : diffCard (J₁ τ) (J₀ τ) ≤ sqJ τ := diffCard_invFix _
  have h2 : diffCard (J₂ τ S) (J₁ τ) ≤ (univ.filter fun q => J₁ τ q = q).card := diffCard_fpfFix
  have h3 : (univ.filter fun q => J₁ τ q = q).card ≤ fixJ τ + diffCard (J₁ τ) (J₀ τ) := by
    unfold fixJ diffCard
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro q
    simp only [mem_filter, mem_univ, true_and, mem_union]
    intro h
    by_cases h' : J₀ τ q = q
    · exact Or.inl h'
    · right; rw [h]; exact fun e => h' e.symm
  have := diffCard_triangle (J₂ τ S) (J₁ τ) (J₀ τ)
  omega

/-- The points at which the relations of Checks 1–3 at `x` fail for the variables and `J₂`. -/
noncomputable def badX (x : ℕ) : ℕ := by
  classical
  exact (univ.filter fun q => ¬LocGood (Xv g τ x) (g.lenAt x) (g.lenRAt x) (J₂ τ S) q).card

theorem diffCard_Xfix_le {x i : ℕ} (hi : i < g.lenAt x) :
    diffCard (Xfix τ S x i) (genPerm τ (genX g x i)) ≤ 2 ^ (g.lenAt x + 1) * badX τ S x := by
  classical
  have := diffCard_commFix (X := Xv g τ x) (ℓR := g.lenRAt x) (J := J₂ τ S) hi
  unfold badX Xfix
  convert this using 3

/-- The relations at `x`, for `J₀`, each failing at no more than `B` points. -/
structure LocalBounds (x B : ℕ) : Prop where
  comm : ∀ i < g.lenAt x, ∀ j < g.lenAt x,
    (univ.filter fun q => genPerm τ (genX g x i) (genPerm τ (genX g x j) q) ≠
      genPerm τ (genX g x j) (genPerm τ (genX g x i) q)).card ≤ B
  sq : ∀ i < g.lenAt x,
    (univ.filter fun q => genPerm τ (genX g x i) (genPerm τ (genX g x i) q) ≠ q).card ≤ B
  J : ∀ i < g.lenAt x,
    (univ.filter fun q => J₀ τ (genPerm τ (genX g x i) q) ≠
      genPerm τ (genX g x i) (J₀ τ q)).card ≤ B
  read : ∀ i < g.lenRAt x,
    (univ.filter fun q => ¬(genPerm τ (genX g x i) q = q ∨
      J₀ τ (genPerm τ (genX g x i) q) = q)).card ≤ B

/-- The challenges at `(x, y)` and `(y, x)` bound the relations at `x`. -/
theorem localBounds_left (x y : ℕ) : LocalBounds τ x (npass τ g x y) where
  comm _ hi _ hj := card_XX_le τ (Or.inl rfl) hi hj
  sq _ hi := card_X_sq_le τ (Or.inl rfl) hi
  J _ hi := card_JX_le τ (Or.inl rfl) hi
  read _ hi := card_read_le τ (Or.inl rfl) hi

theorem localBounds_right (x y : ℕ) : LocalBounds τ x (npass τ g y x) where
  comm _ hi _ hj := card_XX_le τ (Or.inr rfl) hi hj
  sq _ hi := card_X_sq_le τ (Or.inr rfl) hi
  J _ hi := card_JX_le τ (Or.inr rfl) hi
  read _ hi := card_read_le τ (Or.inr rfl) hi

/-- A union bound over the indices below `ℓ`. -/
private theorem card_exists_lt_le {α : Type*} [Fintype α] [DecidableEq α] (ℓ : ℕ)
    (P : ℕ → α → Prop) [∀ i, DecidablePred (P i)] (B : ℕ)
    (h : ∀ i < ℓ, (univ.filter (P i)).card ≤ B) :
    (univ.filter fun q => ∃ i < ℓ, P i q).card ≤ ℓ * B := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have h1 : (univ.filter fun q => ∃ i < ℓ + 1, P i q) ⊆
        (univ.filter fun q => ∃ i < ℓ, P i q) ∪ univ.filter (P ℓ) := by
      intro q
      simp only [mem_filter, mem_univ, true_and, mem_union]
      rintro ⟨i, hi, hP⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, hP⟩
      · exact Or.inr hP
    refine (card_le_card h1).trans ((card_union_le _ _).trans ?_)
    have := ih (fun i hi => h i (by omega))
    have := h ℓ (by omega)
    rw [Nat.succ_mul]
    omega

/-- The bad points at `x` number at most `(ℓ² + 3ℓ) B + 3ℓ d(J₂, J₀)`. -/
theorem card_bad_le {x B : ℕ} (hB : LocalBounds τ x B) :
    badX τ S x ≤ (g.lenAt x ^ 2 + 3 * g.lenAt x) * B +
      3 * g.lenAt x * diffCard (J₂ τ S) (J₀ τ) := by
  classical
  set ℓ := g.lenAt x
  set dJ := diffCard (J₂ τ S) (J₀ τ)
  set X := Xv g τ x
  set J := J₂ τ S
  have hdJ' : (univ.filter fun q => J q ≠ J₀ τ q).card = dJ := rfl
  -- the four kinds of failure
  have hsub : (univ.filter fun q => ¬LocGood X ℓ (g.lenRAt x) J q) ⊆
      (((univ.filter fun q => ∃ i < ℓ, ∃ j < ℓ, X i (X j q) ≠ X j (X i q)) ∪
        univ.filter fun q => ∃ i < ℓ, X i (X i q) ≠ q) ∪
        univ.filter fun q => ∃ i < ℓ, J (X i q) ≠ X i (J q)) ∪
        univ.filter fun q => ∃ i < g.lenRAt x, ¬(X i q = q ∨ X i q = J q) := by
    intro q
    simp only [mem_filter, mem_univ, true_and, mem_union]
    intro h
    by_contra h'
    simp only [not_or, not_exists, not_and, not_not] at h'
    exact h ⟨h'.1.1.1, h'.1.1.2, h'.1.2, fun i hi => or_iff_not_imp_left.mpr (h'.2 i hi)⟩
  have hc1 : (univ.filter fun q => ∃ i < ℓ, ∃ j < ℓ, X i (X j q) ≠ X j (X i q)).card ≤
      ℓ * (ℓ * B) :=
    card_exists_lt_le ℓ _ _ (fun i hi =>
      card_exists_lt_le ℓ (fun j q => X i (X j q) ≠ X j (X i q)) B (fun j hj => hB.comm i hi j hj))
  have hc2 : (univ.filter fun q => ∃ i < ℓ, X i (X i q) ≠ q).card ≤ ℓ * B :=
    card_exists_lt_le ℓ _ _ (fun i hi => hB.sq i hi)
  have hc3 : (univ.filter fun q => ∃ i < ℓ, J (X i q) ≠ X i (J q)).card ≤ ℓ * (B + 2 * dJ) := by
    refine card_exists_lt_le ℓ _ _ (fun i hi => ?_)
    have hXi : (univ.filter fun q => J (X i q) ≠ J₀ τ (X i q)).card = dJ :=
      card_filter_comp_perm (X i) (fun q => J q ≠ J₀ τ q)
    have hsub' : (univ.filter fun q => J (X i q) ≠ X i (J q)) ⊆
        ((univ.filter fun q => J₀ τ (X i q) ≠ X i (J₀ τ q)) ∪
          univ.filter fun q => J (X i q) ≠ J₀ τ (X i q)) ∪ univ.filter fun q => J q ≠ J₀ τ q := by
      intro q
      simp only [mem_filter, mem_univ, true_and, mem_union]
      intro h
      by_contra h'
      simp only [not_or, not_not] at h'
      apply h
      rw [h'.1.2, h'.2]
      exact h'.1.1
    refine (card_le_card hsub').trans ((card_union_le _ _).trans ?_)
    have := card_union_le (univ.filter fun q => J₀ τ (X i q) ≠ X i (J₀ τ q))
      (univ.filter fun q => J (X i q) ≠ J₀ τ (X i q))
    have : (univ.filter fun q => J₀ τ (X i q) ≠ X i (J₀ τ q)).card ≤ B := hB.J i hi
    omega
  have hc4 : (univ.filter fun q => ∃ i < g.lenRAt x, ¬(X i q = q ∨ X i q = J q)).card ≤
      g.lenRAt x * (B + dJ) := by
    refine card_exists_lt_le _ _ _ (fun i hi => ?_)
    have hinv : (univ.filter fun q => J⁻¹ q ≠ (J₀ τ)⁻¹ q).card = dJ := diffCard_inv _ _
    have hJinv : ∀ q, J⁻¹ q = J q := by
      intro q; rw [Equiv.Perm.inv_eq_iff_eq]; exact (J₂_invol τ S q).symm
    have hsub' : (univ.filter fun q => ¬(X i q = q ∨ X i q = J q)) ⊆
        (univ.filter fun q => ¬(X i q = q ∨ J₀ τ (X i q) = q)) ∪
          univ.filter fun q => J⁻¹ q ≠ (J₀ τ)⁻¹ q := by
      intro q
      simp only [mem_filter, mem_univ, true_and, mem_union]
      intro h
      by_contra h'
      rw [not_or, not_not, not_not] at h'
      apply h
      rcases h'.1 with h1 | h1
      · exact Or.inl h1
      · right
        rw [← hJinv, h'.2, eq_comm, Equiv.Perm.inv_eq_iff_eq]
        exact h1.symm
    refine (card_le_card hsub').trans ((card_union_le _ _).trans ?_)
    have : (univ.filter fun q => ¬(X i q = q ∨ J₀ τ (X i q) = q)).card ≤ B := hB.read i hi
    omega
  have hR : g.lenRAt x ≤ ℓ := lenRAt_le_lenAt x
  unfold badX
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  have := card_union_le
    ((univ.filter fun q => ∃ i < ℓ, ∃ j < ℓ, X i (X j q) ≠ X j (X i q)) ∪
        univ.filter fun q => ∃ i < ℓ, X i (X i q) ≠ q)
    (univ.filter fun q => ∃ i < ℓ, J (X i q) ≠ X i (J q))
  have := card_union_le (univ.filter fun q => ∃ i < ℓ, ∃ j < ℓ, X i (X j q) ≠ X j (X i q))
    (univ.filter fun q => ∃ i < ℓ, X i (X i q) ≠ q)
  have h4 : g.lenRAt x * (B + dJ) ≤ ℓ * (B + dJ) := Nat.mul_le_mul_right _ hR
  nlinarith

end MIPRE.Tailored.Sofic

end
