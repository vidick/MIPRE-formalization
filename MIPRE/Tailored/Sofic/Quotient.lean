/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.ConsWord
public import MIPRE.Tactics

@[expose] public section

/-!
# The quotient of an action by a fixed-point-free involution

Paper I, Proposition I:2279, first half: an action passing Checks 1–3 of the associated test is a
Z-aligned permutation strategy. Let `J` be a fixed-point-free involution of `Fin N`. Its orbits
are the pairs `{p, J p}`, with representatives `Reps J`, the points `p < J p`. A permutation `τ`
commuting with `J` (`CommJ J τ`) permutes the orbits, and the choice of representatives makes
this a signed permutation `ind J τ` of `Reps J`: the representative `r` goes to the
representative of `τ r`, with sign `-` when `τ r` is not itself a representative. This is the
action of `τ` on the `(-1)`-eigenspace of `J`, in the basis `e_r - e_{J r}`.

* `ind_mul`, `ind_one`, `ind_J`: `ind J` is multiplicative on the centralizer of `J`, and sends
  `J` to `-1`.
* `ind_fix_iff`: `ind J τ` fixes `r` with sign `+` exactly when `τ` fixes `r`.
* `quotStrat σ hσ`: for an action `σ` passing Checks 1–3, the Z-aligned permutation strategy of
  the signed permutations `ind J X(x, i)`, transported to `Fin m`, `m = |Reps J| = N / 2`.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue

section Involution

variable {N : ℕ} (J : Equiv.Perm (Fin N))

/-- `τ` commutes with `J`. -/
def CommJ (τ : Equiv.Perm (Fin N)) : Prop := ∀ p, τ (J p) = J (τ p)

/-- `J` is a fixed-point-free involution. -/
def FFInvol : Prop := (∀ p, J (J p) = p) ∧ ∀ p, J p ≠ p

/-- The representatives of the `J`-orbits: the points `p < J p`. -/
abbrev Reps : Type := {p : Fin N // p < J p}

/-- The representative of the orbit of `p`. -/
def rep (p : Fin N) : Fin N := if p < J p then p else J p

variable {J}

theorem CommJ.one : CommJ J 1 := fun _ => rfl

theorem CommJ.mul {τ₁ τ₂ : Equiv.Perm (Fin N)} (h₁ : CommJ J τ₁) (h₂ : CommJ J τ₂) :
    CommJ J (τ₁ * τ₂) := fun p => by
  simp only [Equiv.Perm.mul_apply, h₂ p]
  exact h₁ _

theorem CommJ.inv {τ : Equiv.Perm (Fin N)} (h : CommJ J τ) : CommJ J τ⁻¹ := fun p => by
  rw [Equiv.Perm.inv_eq_iff_eq, h]
  simp

theorem CommJ.self : CommJ J J := fun _ => rfl

variable (hJ : FFInvol J)
include hJ

theorem FFInvol.lt_J_J_iff (p : Fin N) : J p < J (J p) ↔ ¬p < J p := by
  rw [hJ.1 p]
  constructor
  · intro h h'; exact lt_asymm h h'
  · intro h; exact lt_of_le_of_ne (not_lt.mp h) (hJ.2 p)

theorem FFInvol.decide_lt_J_J (p : Fin N) :
    decide (J p < J (J p)) = !decide (p < J p) := by
  by_cases h : p < J p
  · simp [h, (hJ.lt_J_J_iff p).not.mpr (not_not.mpr h)]
  · simp [h, (hJ.lt_J_J_iff p).mpr h]

theorem FFInvol.rep_lt (p : Fin N) : rep J p < J (rep J p) := by
  unfold rep
  split_ifs with h
  · exact h
  · exact (hJ.lt_J_J_iff p).mpr h

omit hJ in
theorem FFInvol.rep_of_lt {p : Fin N} (h : p < J p) : rep J p = p := by
  simp [rep, h]

theorem FFInvol.rep_J (p : Fin N) : rep J (J p) = rep J p := by
  unfold rep
  by_cases h : p < J p
  · rw [ite_eq_right ((hJ.lt_J_J_iff p).not.mpr (not_not.mpr h)), hJ.1 p, ite_eq_left h]
  · rw [ite_eq_left ((hJ.lt_J_J_iff p).mpr h), ite_eq_right h]

omit hJ in
theorem FFInvol.rep_eq (p : Fin N) : rep J p = p ∨ rep J p = J p := by
  unfold rep; split_ifs <;> simp

theorem FFInvol.rep_rep_comm {τ : Equiv.Perm (Fin N)} (hτ : CommJ J τ) (p : Fin N) :
    rep J (τ (rep J p)) = rep J (τ p) := by
  rcases FFInvol.rep_eq p with h | h <;> rw [h]
  rw [hτ, hJ.rep_J]

end Involution

/-! ## The induced signed permutation -/

section Induced

variable {N : ℕ} {J : Equiv.Perm (Fin N)}

/-- The permutation of the representatives induced by `τ`. -/
def indPerm (hJ : FFInvol J) (τ : Equiv.Perm (Fin N)) (hτ : CommJ J τ) : Equiv.Perm (Reps J) where
  toFun r := ⟨rep J (τ r.1), hJ.rep_lt _⟩
  invFun r := ⟨rep J (τ⁻¹ r.1), hJ.rep_lt _⟩
  left_inv r := Subtype.ext (by
    simp only
    rw [hJ.rep_rep_comm hτ.inv]
    simpa using FFInvol.rep_of_lt r.2)
  right_inv r := Subtype.ext (by
    simp only
    rw [hJ.rep_rep_comm hτ]
    simpa using FFInvol.rep_of_lt r.2)

open Classical in
/-- **The signed permutation of the representatives induced by `τ`**: `r ↦ ± rep(τ r)`, with
sign `-` when `τ r` is not a representative (the identity when `J` is not a fixed-point-free
involution or `τ` does not commute with it). -/
noncomputable def ind (J : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin N)) : SignedPerm (Reps J) :=
  if h : FFInvol J ∧ CommJ J τ then ⟨indPerm h.1 τ h.2, fun r => decide ¬(τ r.1 < J (τ r.1))⟩
  else 1

variable (hJ : FFInvol J)
include hJ

theorem ind_perm_apply {τ : Equiv.Perm (Fin N)} (hτ : CommJ J τ) (r : Reps J) :
    ((ind J τ).perm r).1 = rep J (τ r.1) := by
  simp [ind, hJ, hτ, indPerm]

theorem ind_sign {τ : Equiv.Perm (Fin N)} (hτ : CommJ J τ) (r : Reps J) :
    (ind J τ).sign r = decide ¬(τ r.1 < J (τ r.1)) := by
  simp [ind, hJ, hτ]

theorem ind_mul {τ₁ τ₂ : Equiv.Perm (Fin N)} (h₁ : CommJ J τ₁) (h₂ : CommJ J τ₂) :
    ind J (τ₁ * τ₂) = ind J τ₁ * ind J τ₂ := by
  ext r
  · simp only [SignedPerm.mul_perm, Equiv.Perm.mul_apply]
    rw [ind_perm_apply hJ (h₁.mul h₂), ind_perm_apply hJ h₁, ind_perm_apply hJ h₂,
      Equiv.Perm.mul_apply, hJ.rep_rep_comm h₁]
  · simp only [SignedPerm.mul_sign]
    rw [ind_sign hJ (h₁.mul h₂), ind_sign hJ h₁, ind_sign hJ h₂, ind_perm_apply hJ h₂]
    simp only [Equiv.Perm.mul_apply]
    by_cases h : τ₂ r.1 < J (τ₂ r.1)
    · rw [FFInvol.rep_of_lt h]; simp [h]
    · have hr : rep J (τ₂ r.1) = J (τ₂ r.1) := by simp [rep, h]
      rw [hr, h₁]
      have h3 := hJ.lt_J_J_iff (τ₁ (τ₂ r.1))
      by_cases h4 : τ₁ (τ₂ r.1) < J (τ₁ (τ₂ r.1))
      · have h5 : ¬J (τ₁ (τ₂ r.1)) < J (J (τ₁ (τ₂ r.1))) := fun h' => h3.mp h' h4
        simp [h, h4, h5]
      · simp [h, h4, h3.mpr h4]

theorem ind_one : ind J 1 = 1 := by
  ext r
  · rw [ind_perm_apply hJ CommJ.one, SignedPerm.one_perm, Equiv.Perm.coe_one, id,
      Equiv.Perm.coe_one, id, FFInvol.rep_of_lt r.2]
  · rw [ind_sign hJ CommJ.one]; simp [r.2]

theorem ind_J : ind J J = SignedPerm.negOne := by
  ext r
  · rw [ind_perm_apply hJ CommJ.self, hJ.rep_J, FFInvol.rep_of_lt r.2]; rfl
  · rw [ind_sign hJ CommJ.self]
    simp only [decide_not, hJ.decide_lt_J_J]
    simp [r.2, SignedPerm.negOne]

/-- **`ind J τ` fixes `r` with sign `+` exactly when `τ` fixes `r`.** -/
theorem ind_fix_iff {τ : Equiv.Perm (Fin N)} (hτ : CommJ J τ) (r : Reps J) :
    ((ind J τ).perm r = r ∧ (ind J τ).sign r = false) ↔ τ r.1 = r.1 := by
  rw [ind_sign hJ hτ, Subtype.ext_iff, ind_perm_apply hJ hτ, decide_eq_false_iff_not, not_not]
  constructor
  · rintro ⟨h1, h2⟩
    rwa [FFInvol.rep_of_lt h2] at h1
  · intro h
    rw [h]
    exact ⟨FFInvol.rep_of_lt r.2, r.2⟩

/-- A readable variable induces a diagonal signed permutation. -/
theorem ind_perm_eq_one {τ : Equiv.Perm (Fin N)} (hτ : CommJ J τ)
    (hr : ∀ p, τ p = p ∨ τ p = J p) : (ind J τ).perm = 1 := by
  ext r
  rw [ind_perm_apply hJ hτ, Equiv.Perm.coe_one, id]
  rcases hr r.1 with h | h <;> rw [h]
  · rw [FFInvol.rep_of_lt r.2]
  · rw [hJ.rep_J, FFInvol.rep_of_lt r.2]

theorem ind_sign_eq {τ : Equiv.Perm (Fin N)} (hτ : CommJ J τ)
    (hr : ∀ p, τ p = p ∨ τ p = J p) (r : Reps J) : (ind J τ).sign r = decide (τ r.1 ≠ r.1) := by
  rw [ind_sign hJ hτ]
  rcases hr r.1 with h | h <;> rw [h]
  · simp [r.2]
  · simp only [decide_not, hJ.decide_lt_J_J]
    simp [r.2, hJ.2 r.1]

/-- **There are `N / 2` orbits**: `N ≤ 2 |Reps J|`. -/
theorem card_le_two_mul_card_reps : N ≤ 2 * Fintype.card (Reps J) := by
  classical
  rw [Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun p => p < J p)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun p => ¬p < J p).card ≤
      (Finset.univ.filter fun p => p < J p).card := by
    refine Finset.card_le_card_of_injOn J (fun p hp => ?_) (fun p _ q _ hpq => J.injective hpq)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    exact (hJ.lt_J_J_iff p).mpr hp
  omega

theorem reps_nonempty (hN : 0 < N) : Nonempty (Reps J) :=
  ⟨⟨rep J ⟨0, hN⟩, hJ.rep_lt _⟩⟩

end Induced

/-! ## The quotient strategy -/

section Strategy

variable {g : TailoredGameData} {σ : FiniteAction (nGen g)}

theorem Checks.ffInvol (hσ : Checks g σ) : FFInvol (genPerm σ genJ) := ⟨hσ.J_invol, hσ.J_free⟩

theorem Checks.commJ_X (hσ : Checks g σ) {x i : ℕ} (hx : x < g.nV + 1) (hi : i < g.lenAt x) :
    CommJ (genPerm σ genJ) (genPerm σ (genX g x i)) := fun p => by
  have h := congrArg (fun τ : Equiv.Perm (Fin σ.N) => τ p) (hσ.J_comm x i hx hi)
  simpa using h.symm

theorem Checks.readable' (hσ : Checks g σ) {x i : ℕ} (hx : x < g.nV + 1) (hi : i < g.lenRAt x) :
    ∀ p, genPerm σ (genX g x i) p = p ∨ genPerm σ (genX g x i) p = genPerm σ genJ p :=
  hσ.readable x i hx hi

/-- The enumeration of the representatives. -/
noncomputable def repEquiv (σ : FiniteAction (nGen g)) : Reps (genPerm σ genJ) ≃
    Fin (Fintype.card (Reps (genPerm σ genJ))) :=
  Fintype.equivFin _

/-- The induced signed permutation, on `Fin m`. -/
noncomputable def indF (σ : FiniteAction (nGen g)) (τ : Equiv.Perm (Fin σ.N)) :
    SignedPerm (Fin (Fintype.card (Reps (genPerm σ genJ)))) :=
  (ind (genPerm σ genJ) τ).map (repEquiv σ)

theorem SignedPerm.map_mul' {Ω Ω' : Type*} (e : Ω ≃ Ω') (s t : SignedPerm Ω) :
    (s * t).map e = s.map e * t.map e := by
  ext j
  · simp [SignedPerm.map, Equiv.permCongr_mul]
  · simp [SignedPerm.map, Equiv.permCongr_apply]

theorem SignedPerm.map_one' {Ω Ω' : Type*} (e : Ω ≃ Ω') : (1 : SignedPerm Ω).map e = 1 := by
  ext j
  · simp [SignedPerm.map]
  · simp [SignedPerm.map]

theorem indF_mul (hσ : Checks g σ) {τ₁ τ₂ : Equiv.Perm (Fin σ.N)}
    (h₁ : CommJ (genPerm σ genJ) τ₁) (h₂ : CommJ (genPerm σ genJ) τ₂) :
    indF σ (τ₁ * τ₂) = indF σ τ₁ * indF σ τ₂ := by
  rw [indF, ind_mul hσ.ffInvol h₁ h₂, SignedPerm.map_mul']; rfl

theorem indF_one (hσ : Checks g σ) : indF σ 1 = 1 := by
  rw [indF, ind_one hσ.ffInvol, SignedPerm.map_one']

theorem toMatrix_indF_J (hσ : Checks g σ) : (indF σ (genPerm σ genJ)).toMatrix = -1 := by
  rw [indF, ind_J hσ.ffInvol]
  have : (SignedPerm.negOne : SignedPerm (Reps (genPerm σ genJ))).map (repEquiv σ) =
      SignedPerm.negOne := by
    ext j
    · simp [SignedPerm.map, SignedPerm.negOne]
    · simp [SignedPerm.map, SignedPerm.negOne]
  rw [this, SignedPerm.toMatrix_negOne]

/-- The point of `Fin N` representing the basis point `j`. -/
noncomputable def repPt (σ : FiniteAction (nGen g)) (j : Fin (Fintype.card (Reps (genPerm σ genJ)))) :
    Fin σ.N :=
  ((repEquiv σ).symm j).1

theorem indF_fix_iff (hσ : Checks g σ) {τ : Equiv.Perm (Fin σ.N)} (hτ : CommJ (genPerm σ genJ) τ)
    (j : Fin (Fintype.card (Reps (genPerm σ genJ)))) :
    ((indF σ τ).perm j = j ∧ (indF σ τ).sign j = false) ↔ τ (repPt σ j) = repPt σ j := by
  rw [repPt, ← ind_fix_iff hσ.ffInvol hτ]
  simp only [indF, SignedPerm.map, Equiv.permCongr_apply, Function.comp_apply]
  rw [← Equiv.eq_symm_apply]

theorem indF_perm_eq_one (hσ : Checks g σ) {τ : Equiv.Perm (Fin σ.N)}
    (hτ : CommJ (genPerm σ genJ) τ) (hr : ∀ p, τ p = p ∨ τ p = genPerm σ genJ p) :
    (indF σ τ).perm = 1 := by
  ext j
  simp [indF, SignedPerm.map, Equiv.permCongr_apply, ind_perm_eq_one hσ.ffInvol hτ hr]

theorem indF_sign_eq (hσ : Checks g σ) {τ : Equiv.Perm (Fin σ.N)}
    (hτ : CommJ (genPerm σ genJ) τ) (hr : ∀ p, τ p = p ∨ τ p = genPerm σ genJ p)
    (j : Fin (Fintype.card (Reps (genPerm σ genJ)))) :
    (indF σ τ).sign j = decide (τ (repPt σ j) ≠ repPt σ j) := by
  simp only [indF, SignedPerm.map, Function.comp_apply]
  exact ind_sign_eq hσ.ffInvol hτ hr _

/-- The observable of the quotient strategy, before packaging. -/
noncomputable def quotU (σ : FiniteAction (nGen g)) (x : Fin (g.nV + 1)) (i : Fin g.ansLen) :
    Matrix (Fin (Fintype.card (Reps (genPerm σ genJ))))
      (Fin (Fintype.card (Reps (genPerm σ genJ)))) ℂ :=
  if i.val < g.lenAt x.val then (indF σ (genPerm σ (genX g x.val i.val))).toMatrix else 1

/-- **The quotient strategy** (Proposition I:2279): an action passing Checks 1–3 gives a Z-aligned
permutation strategy on the `J`-orbits. -/
noncomputable abbrev quotStrat (σ : FiniteAction (nGen g)) (hσ : Checks g σ) : ZStrat g where
  m := Fintype.card (Reps (genPerm σ genJ))
  m_pos := @Fintype.card_pos _ _ (reps_nonempty hσ.ffInvol σ.N_pos)
  U := quotU σ
  signedPerm x i := by
    unfold quotU
    split_ifs
    · exact SignedPerm.isSignedPerm_toMatrix _
    · exact IsSignedPerm.one
  invol x i := by
    unfold quotU
    split_ifs with hi
    · have hc := hσ.commJ_X x.isLt hi
      rw [← SignedPerm.toMatrix_mul, ← indF_mul hσ hc hc]
      have : genPerm σ (genX g x.val i.val) * genPerm σ (genX g x.val i.val) = 1 :=
        Equiv.ext fun p => hσ.X_invol x.val i.val x.isLt hi p
      rw [this, indF_one hσ, SignedPerm.toMatrix_one]
    · exact Matrix.one_mul 1
  comm x i j := by
    unfold quotU
    split_ifs with hi hj hj
    · rw [← SignedPerm.toMatrix_mul, ← SignedPerm.toMatrix_mul,
        ← indF_mul hσ (hσ.commJ_X x.isLt hi) (hσ.commJ_X x.isLt hj),
        ← indF_mul hσ (hσ.commJ_X x.isLt hj) (hσ.commJ_X x.isLt hi),
        hσ.X_comm x.val i.val j.val x.isLt hi hj]
    · rw [Matrix.mul_one, Matrix.one_mul]
    · rw [Matrix.mul_one, Matrix.one_mul]
    · rfl
  pad x i hi := by
    unfold quotU
    rw [ite_eq_right (not_lt.mpr hi)]
  zAligned x i hi := by
    have hi' : i.val < g.lenAt x.val := lt_of_lt_of_le hi (Nat.le_add_right _ _)
    unfold quotU
    rw [ite_eq_left hi', SignedPerm.isDiag_toMatrix_iff]
    exact indF_perm_eq_one hσ (hσ.commJ_X x.isLt hi') (hσ.readable' x.isLt hi)

end Strategy

end MIPRE.Tailored.Sofic

end
