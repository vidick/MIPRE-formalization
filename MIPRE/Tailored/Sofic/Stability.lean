/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Hamming
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import MIPRE.Tactics

@[expose] public section

/-!
# Stability of involutions, fixed-point-free involutions and commuting involutions

The group-stability facts of paper I's interlude (I:2558–2649), in the form the perturbation
argument (Proposition I:2267) uses them:

* `invFix` (Claim I:2561): a permutation `ζ` is within `#{x | ζ² x ≠ x}` points of an involution,
  the one that agrees with `ζ` where `ζ² x = x` and fixes the other points.
* `fpfFix` (Claim I:2582): an involution `τ` commuting with a fixed-point-free involution `s` is
  within `#{x | τ x = x}` points of a fixed-point-free involution: send the fixed points of `τ`
  along `s`. The paper instead pads an odd set by a point and matches the fixed points; here the
  perturbation first doubles the action, which supplies `s` (the swap of the two copies) and
  makes every set even.
* `commFix` (Claims I:2600 and I:2643, combined): involutions `X i`, `i < ℓ`, with a central
  involution `J`, and readable ones (`i < ℓR`) acting as `1` or `J`, all hold at every point of
  the set `U` of points `p` such that every ordered product `X_{i₁} ⋯ X_{iᵣ} p` (and the same
  at `J p`) is a point at which these relations hold. `U` is invariant under every `X i` and `J`,
  so restricting the `X i` to `U` and setting them to the identity off it gives commuting
  involutions, commuting with `J`, the readable ones aligned with `J`, and at most
  `2^{ℓ+1}` times the number of bad points are changed. This replaces the paper's
  Glebsky–Rivera step (Claim I:2643, applied to `F₂^ℓ` with a `4^ℓ` loss) and its separate
  repairs of the involution, commutation-with-`J` and readability conditions, with a `2^{ℓ+1}`
  loss.
-/

namespace MIPRE.Tailored.Sofic

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Almost involutions -/

/-- The involution near a permutation `ζ` (Claim I:2561): `ζ` where `ζ² x = x`, the identity
elsewhere. -/
def invFix (ζ : Equiv.Perm α) : Equiv.Perm α :=
  Function.Involutive.toPerm (fun x => if ζ (ζ x) = x then ζ x else x) (by
    intro x
    by_cases h : ζ (ζ x) = x
    · simp [h]
    · simp [h])

omit [Fintype α] in
theorem invFix_apply (ζ : Equiv.Perm α) (x : α) :
    invFix ζ x = if ζ (ζ x) = x then ζ x else x := rfl

omit [Fintype α] in
theorem invFix_invol (ζ : Equiv.Perm α) (x : α) : invFix ζ (invFix ζ x) = x :=
  Function.Involutive.toPerm_involutive _ x

theorem diffCard_invFix (ζ : Equiv.Perm α) :
    diffCard (invFix ζ) ζ ≤ (univ.filter fun x => ζ (ζ x) ≠ x).card := by
  unfold diffCard
  refine card_le_card ?_
  intro x
  simp only [mem_filter, mem_univ, true_and]
  intro h h'
  apply h
  rw [invFix_apply, ite_eq_left h']

omit [Fintype α] in
theorem invFix_comm (ζ s : Equiv.Perm α) (h : ∀ x, ζ (s x) = s (ζ x)) (x : α) :
    invFix ζ (s x) = s (invFix ζ x) := by
  simp only [invFix_apply, h]
  by_cases hx : ζ (ζ x) = x
  · simp [hx]
  · rw [ite_eq_right hx, ite_eq_right (fun h' => hx (s.injective h'))]

/-! ## Almost fixed-point-free involutions -/

/-- The fixed-point-free involution near an involution `τ` that commutes with a fixed-point-free
involution `s` (Claim I:2582): `s` on the fixed points of `τ`, `τ` elsewhere. -/
def fpfFix (τ s : Equiv.Perm α) (hτ : ∀ x, τ (τ x) = x) (hs : ∀ x, s (s x) = x)
    (hc : ∀ x, τ (s x) = s (τ x)) : Equiv.Perm α :=
  Function.Involutive.toPerm (fun x => if τ x = x then s x else τ x) (by
    intro x
    by_cases h : τ x = x
    · have h' : τ (s x) = s x := by rw [hc, h]
      simp [h, h', hs]
    · have h' : τ (τ x) ≠ τ x := by rw [hτ]; exact fun e => h e.symm
      dsimp only
      rw [ite_eq_right h, ite_eq_right h', hτ])

variable {τ s : Equiv.Perm α} {hτ : ∀ x, τ (τ x) = x} {hs : ∀ x, s (s x) = x}
  {hc : ∀ x, τ (s x) = s (τ x)}

omit [Fintype α] in
theorem fpfFix_apply (x : α) :
    fpfFix τ s hτ hs hc x = if τ x = x then s x else τ x := rfl

omit [Fintype α] in
theorem fpfFix_invol (x : α) : fpfFix τ s hτ hs hc (fpfFix τ s hτ hs hc x) = x :=
  Function.Involutive.toPerm_involutive _ x

omit [Fintype α] in
theorem fpfFix_free (hfree : ∀ x, s x ≠ x) (x : α) : fpfFix τ s hτ hs hc x ≠ x := by
  rw [fpfFix_apply]
  split_ifs with h
  · exact hfree x
  · exact h

theorem diffCard_fpfFix :
    diffCard (fpfFix τ s hτ hs hc) τ ≤ (univ.filter fun x => τ x = x).card := by
  unfold diffCard
  refine card_le_card ?_
  intro x
  simp only [mem_filter, mem_univ, true_and]
  intro h
  by_contra h'
  apply h
  rw [fpfFix_apply, ite_eq_right h']

/-! ## Ordered products -/

/-- The ordered product `X_j^{[j ∈ S]} X_{j+1}^{[j+1 ∈ S]} ⋯ X_{j+n-1}^{[j+n-1 ∈ S]}`. -/
def ordProd (X : ℕ → Equiv.Perm α) (S : Finset ℕ) : ℕ → ℕ → Equiv.Perm α
  | _, 0 => 1
  | j, n + 1 => (if j ∈ S then X j else 1) * ordProd X S (j + 1) n

variable (X : ℕ → Equiv.Perm α)

omit [Fintype α] [DecidableEq α] in
theorem ordProd_succ (S : Finset ℕ) (j n : ℕ) :
    ordProd X S j (n + 1) = (if j ∈ S then X j else 1) * ordProd X S (j + 1) n := rfl

omit [Fintype α] [DecidableEq α] in
theorem ordProd_congr (S S' : Finset ℕ) :
    ∀ n j, (∀ m, j ≤ m → m < j + n → (m ∈ S ↔ m ∈ S')) → ordProd X S j n = ordProd X S' j n
  | 0, _, _ => rfl
  | n + 1, j, h => by
    rw [ordProd_succ, ordProd_succ, ordProd_congr S S' n (j + 1)
      (fun m h1 h2 => h m (by omega) (by omega))]
    congr 1
    exact if_congr (h j le_rfl (by omega)) rfl rfl

omit [Fintype α] [DecidableEq α] in
theorem ordProd_skip (S : Finset ℕ) (n : ℕ) :
    ∀ k j, (∀ m, j ≤ m → m < j + k → m ∉ S) → ordProd X S j (k + n) = ordProd X S (j + k) n
  | 0, _, _ => by rw [Nat.zero_add, Nat.add_zero]
  | k + 1, j, h => by
    rw [show k + 1 + n = (k + n) + 1 by omega, ordProd_succ, ite_eq_right (h j le_rfl (by omega)),
      one_mul, ordProd_skip S n k (j + 1) (fun m h1 h2 => h m (by omega) (by omega)),
      show j + 1 + k = j + (k + 1) by omega]

omit [Fintype α] [DecidableEq α] in
/-- A suffix of an ordered product is the full product over the tail of `S`. -/
theorem ordProd_suffix (S : Finset ℕ) (ℓ j : ℕ) (hj : j ≤ ℓ) :
    ordProd X S j (ℓ - j) = ordProd X (S.filter (j ≤ ·)) 0 ℓ := by
  have h1 := ordProd_skip X (S.filter (j ≤ ·)) (ℓ - j) j 0
    (fun m _ h2 => by simp only [mem_filter, not_and, not_le]; intro _; omega)
  rw [show j + (ℓ - j) = ℓ by omega, zero_add] at h1
  rw [h1]
  exact ordProd_congr X S _ (ℓ - j) j (fun m h1 _ => by simp [h1])

omit [Fintype α] [DecidableEq α] in
@[simp] theorem ordProd_empty : ∀ n j, ordProd X ∅ j n = 1
  | 0, _ => rfl
  | n + 1, j => by rw [ordProd_succ, ordProd_empty n (j + 1)]; simp

/-! ## Commuting involutions -/

variable (ℓ ℓR : ℕ) (J : Equiv.Perm α)

/-- The relations of Checks 1–3 at a point `q`: the `X i`, `i < ℓ`, commute and are involutions
at `q`, commute with `J` at `q`, and the readable ones act at `q` as `1` or `J`. -/
def LocGood (q : α) : Prop :=
  (∀ i < ℓ, ∀ j < ℓ, X i (X j q) = X j (X i q)) ∧ (∀ i < ℓ, X i (X i q) = q) ∧
    (∀ i < ℓ, J (X i q) = X i (J q)) ∧ (∀ i < ℓR, X i q = q ∨ X i q = J q)

/-- The good set: every ordered product of the `X i` takes `p`, and `J p`, to a point at which
the relations hold. -/
def InGood (p : α) : Prop :=
  ∀ S ∈ (range ℓ).powerset, LocGood X ℓ ℓR J (ordProd X S 0 ℓ p) ∧
    LocGood X ℓ ℓR J (ordProd X S 0 ℓ (J p))

variable {X ℓ ℓR J}

omit [Fintype α] [DecidableEq α] in
theorem locGood_of_inGood {p : α} (h : InGood X ℓ ℓR J p) : LocGood X ℓ ℓR J p := by
  simpa using (h ∅ (by simp)).1

omit [Fintype α] [DecidableEq α] in
/-- Every suffix of an ordered product takes a good point to a point where the relations hold. -/
private theorem locGood_suffix {p : α}
    (h : ∀ S ∈ (range ℓ).powerset, LocGood X ℓ ℓR J (ordProd X S 0 ℓ p))
    {S : Finset ℕ} (hS : S ⊆ range ℓ) {j : ℕ} (hj : j ≤ ℓ) :
    LocGood X ℓ ℓR J (ordProd X S j (ℓ - j) p) := by
  rw [ordProd_suffix X S ℓ j hj]
  exact h _ (mem_powerset.mpr ((filter_subset _ _).trans hS))

omit [Fintype α] [DecidableEq α] in
/-- A generator `X k` passes through an ordered product of later generators. -/
private theorem ordProd_pass {p : α}
    (h : ∀ S ∈ (range ℓ).powerset, LocGood X ℓ ℓR J (ordProd X S 0 ℓ p))
    {S : Finset ℕ} (hS : S ⊆ range ℓ) :
    ∀ n j k, j + n = ℓ → k < j → ordProd X S j n (X k p) = X k (ordProd X S j n p)
  | 0, _, _, _, _ => rfl
  | n + 1, j, k, hn, hk => by
    rw [ordProd_succ, Equiv.Perm.mul_apply, ordProd_pass h hS n (j + 1) k (by omega) (by omega),
      Equiv.Perm.mul_apply]
    split_ifs with hjS
    · have hg := locGood_suffix h hS (j := j + 1) (by omega)
      rw [show ℓ - (j + 1) = n by omega] at hg
      exact hg.1 j (by omega) k (by omega)
    · rfl

omit [Fintype α] in
/-- A generator `X k` merges into an ordered product: the bubble-sort identity. -/
private theorem ordProd_absorb {p : α}
    (h : ∀ S ∈ (range ℓ).powerset, LocGood X ℓ ℓR J (ordProd X S 0 ℓ p))
    {S : Finset ℕ} (hS : S ⊆ range ℓ) :
    ∀ n j k, j + n = ℓ → j ≤ k → k < ℓ →
      ordProd X S j n (X k p) = ordProd X (symmDiff S {k}) j n p
  | 0, _, _, hn, hk, hkl => by omega
  | n + 1, j, k, hn, hk, hkl => by
    rw [ordProd_succ, ordProd_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · rw [ordProd_pass h hS n (j + 1) j (by omega) (by omega),
        ordProd_congr X (symmDiff S {j}) S n (j + 1)
          (fun m h1 _ => by
            have hne : m ≠ j := by omega
            simp [mem_symmDiff, hne])]
      have hg := locGood_suffix h hS (j := j + 1) (by omega)
      rw [show ℓ - (j + 1) = n by omega] at hg
      by_cases hjS : j ∈ S
      · rw [ite_eq_left hjS, ite_eq_right (by simp [mem_symmDiff, hjS])]
        exact hg.2.1 j (by omega)
      · rw [ite_eq_right hjS, ite_eq_left (by simp [mem_symmDiff, hjS])]
        simp
    · rw [ordProd_absorb h hS n (j + 1) k (by omega) (by omega) hkl]
      have hne : j ≠ k := by omega
      have : (j ∈ symmDiff S {k}) ↔ j ∈ S := by simp [mem_symmDiff, hne]
      rw [if_congr this rfl rfl]

omit [Fintype α] in
theorem inGood_X {p : α} (h : InGood X ℓ ℓR J p) {k : ℕ} (hk : k < ℓ) :
    InGood X ℓ ℓR J (X k p) := by
  have h1 : ∀ S ∈ (range ℓ).powerset, LocGood X ℓ ℓR J (ordProd X S 0 ℓ p) :=
    fun S hS => (h S hS).1
  have h2 : ∀ S ∈ (range ℓ).powerset, LocGood X ℓ ℓR J (ordProd X S 0 ℓ (J p)) :=
    fun S hS => (h S hS).2
  have hsd : ∀ S ∈ (range ℓ).powerset, symmDiff S {k} ∈ (range ℓ).powerset := by
    intro S hS
    rw [mem_powerset] at hS ⊢
    intro m hm
    rw [mem_symmDiff] at hm
    rcases hm with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact hS hm
    · rw [mem_singleton] at hm; rw [mem_range]; omega
  intro S hS
  have hS' := mem_powerset.mp hS
  refine ⟨?_, ?_⟩
  · rw [ordProd_absorb h1 hS' ℓ 0 k (by omega) (by omega) hk]
    exact h1 _ (hsd S hS)
  · rw [(locGood_of_inGood h).2.2.1 k hk, ordProd_absorb h2 hS' ℓ 0 k (by omega) (by omega) hk]
    exact h2 _ (hsd S hS)

omit [Fintype α] [DecidableEq α] in
theorem inGood_J (hJ : ∀ x, J (J x) = x) {p : α} (h : InGood X ℓ ℓR J p) :
    InGood X ℓ ℓR J (J p) := by
  intro S hS
  rw [hJ]
  exact ⟨(h S hS).2, (h S hS).1⟩

omit [Fintype α] [DecidableEq α] in
theorem inGood_of_J (hJ : ∀ x, J (J x) = x) {p : α} (h : InGood X ℓ ℓR J (J p)) :
    InGood X ℓ ℓR J p := by
  simpa [hJ] using inGood_J (X := X) (ℓ := ℓ) (ℓR := ℓR) hJ h

open Classical in
/-- The commuting repair of `X i` (Claims I:2600 and I:2643): `X i` on the good set, the
identity off it. -/
noncomputable def commFix (X : ℕ → Equiv.Perm α) (ℓ ℓR : ℕ) (J : Equiv.Perm α) (i : ℕ) :
    Equiv.Perm α :=
  Function.Involutive.toPerm (fun q => if i < ℓ ∧ InGood X ℓ ℓR J q then X i q else q) (by
    intro q
    by_cases h : i < ℓ ∧ InGood X ℓ ℓR J q
    · have h' : i < ℓ ∧ InGood X ℓ ℓR J (X i q) := ⟨h.1, inGood_X h.2 h.1⟩
      simp only [ite_eq_left h, ite_eq_left h']
      exact (locGood_of_inGood h.2).2.1 i h.1
    · simp only [ite_eq_right h])

open Classical in
omit [Fintype α] in
theorem commFix_apply (i : ℕ) (q : α) :
    commFix X ℓ ℓR J i q = if i < ℓ ∧ InGood X ℓ ℓR J q then X i q else q := rfl

omit [Fintype α] in
theorem commFix_of_good {i : ℕ} (hi : i < ℓ) {q : α} (h : InGood X ℓ ℓR J q) :
    commFix X ℓ ℓR J i q = X i q := by
  rw [commFix_apply, ite_eq_left ⟨hi, h⟩]

omit [Fintype α] in
theorem commFix_of_bad (i : ℕ) {q : α} (h : ¬InGood X ℓ ℓR J q) :
    commFix X ℓ ℓR J i q = q := by
  rw [commFix_apply, ite_eq_right (fun h' => h h'.2)]

omit [Fintype α] in
theorem commFix_invol (i : ℕ) (q : α) : commFix X ℓ ℓR J i (commFix X ℓ ℓR J i q) = q :=
  Function.Involutive.toPerm_involutive _ q

omit [Fintype α] in
theorem commFix_comm {i i' : ℕ} (hi : i < ℓ) (hi' : i' < ℓ) :
    commFix X ℓ ℓR J i * commFix X ℓ ℓR J i' = commFix X ℓ ℓR J i' * commFix X ℓ ℓR J i := by
  ext q
  simp only [Equiv.Perm.mul_apply]
  by_cases h : InGood X ℓ ℓR J q
  · rw [commFix_of_good hi' h, commFix_of_good hi h, commFix_of_good hi (inGood_X h hi'),
      commFix_of_good hi' (inGood_X h hi)]
    exact (locGood_of_inGood h).1 i hi i' hi'
  · simp only [commFix_of_bad _ h]

omit [Fintype α] in
theorem commFix_J (hJ : ∀ x, J (J x) = x) {i : ℕ} (hi : i < ℓ) :
    J * commFix X ℓ ℓR J i = commFix X ℓ ℓR J i * J := by
  ext q
  simp only [Equiv.Perm.mul_apply]
  by_cases h : InGood X ℓ ℓR J q
  · rw [commFix_of_good hi h, commFix_of_good hi (inGood_J hJ h)]
    exact (locGood_of_inGood h).2.2.1 i hi
  · rw [commFix_of_bad i h, commFix_of_bad i (fun h' => h (inGood_of_J hJ h'))]

omit [Fintype α] in
theorem commFix_readable (hR : ℓR ≤ ℓ) {i : ℕ} (hi : i < ℓR) (q : α) :
    commFix X ℓ ℓR J i q = q ∨ commFix X ℓ ℓR J i q = J q := by
  by_cases h : InGood X ℓ ℓR J q
  · rw [commFix_of_good (by omega) h]
    exact (locGood_of_inGood h).2.2.2 i hi
  · left; exact commFix_of_bad i h

open Classical in
/-- The repair changes `X i` at most at `2^{ℓ+1}` times as many points as there are points where
the relations fail. -/
theorem diffCard_commFix {i : ℕ} (hi : i < ℓ) :
    diffCard (commFix X ℓ ℓR J i) (X i) ≤
      2 ^ (ℓ + 1) * (univ.filter fun q => ¬LocGood X ℓ ℓR J q).card := by
  have hsub : (univ.filter fun q => commFix X ℓ ℓR J i q ≠ X i q) ⊆
      (range ℓ).powerset.biUnion fun S =>
        (univ.filter fun q => ¬LocGood X ℓ ℓR J (ordProd X S 0 ℓ q)) ∪
          (univ.filter fun q => ¬LocGood X ℓ ℓR J ((ordProd X S 0 ℓ * J) q)) := by
    intro q
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_union]
    intro hq
    have hbad : ¬InGood X ℓ ℓR J q := fun hg => hq (commFix_of_good hi hg)
    unfold InGood at hbad
    simp only [not_forall, not_and_or] at hbad
    obtain ⟨S, hS, hS'⟩ := hbad
    exact ⟨S, hS, hS'⟩
  unfold diffCard
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  have hterm : ∀ S ∈ (range ℓ).powerset,
      ((univ.filter fun q => ¬LocGood X ℓ ℓR J (ordProd X S 0 ℓ q)) ∪
          (univ.filter fun q => ¬LocGood X ℓ ℓR J ((ordProd X S 0 ℓ * J) q))).card ≤
        2 * (univ.filter fun q => ¬LocGood X ℓ ℓR J q).card := by
    intro S _
    refine (card_union_le _ _).trans ?_
    rw [card_filter_comp_perm (ordProd X S 0 ℓ) (fun q => ¬LocGood X ℓ ℓR J q),
      card_filter_comp_perm (ordProd X S 0 ℓ * J) (fun q => ¬LocGood X ℓ ℓR J q)]
    omega
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_powerset, card_range, smul_eq_mul, pow_succ]
  ring_nf
  exact le_rfl

end MIPRE.Tailored.Sofic

end
