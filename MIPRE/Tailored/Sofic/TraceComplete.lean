/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.TraceSound
public import MIPRE.Tactics

@[expose] public section

/-!
# Completeness of the associated test (Theorem I:2126 (1))

A perfect Z-aligned permutation strategy of `g` gives an action of value `1` on the associated
test (`exists_value_one_of_hasPerfectZPC`). A signed permutation `s` of `Fin m` is a permutation
`liftSP s` of `Bool × Fin m`, `(b, j) ↦ (b ⊕ s_j, s(j))`, multiplicatively; the action lets the
generator `J` act as the lift of `-1` and `X(x, i)` as the lift of the signed permutation of
`U x i`, on `Fin (2m) ≃ Bool × Fin m`. It passes Checks 1–3, and a point `(b, j)` passes the
challenge at `(x, y)` when every constraint word of the readable class of `j` fixes `(b, j)`:
when the matrix of the word has `1` at `(j, j)`. The trace identity at value `1` gives exactly
this for the pairs of positive weight (`consMat_apply_self_eq_one`). Commutation along edges is
not used.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue

/-! ## Lifting signed permutations -/

section Lift

variable {Ω : Type*}

/-- A signed permutation of `Ω` as a permutation of `Bool × Ω`. -/
def liftSP (s : SignedPerm Ω) : Equiv.Perm (Bool × Ω) where
  toFun q := (xor q.1 (s.sign q.2), s.perm q.2)
  invFun q := (xor q.1 (s.sign (s.perm⁻¹ q.2)), s.perm⁻¹ q.2)
  left_inv q := by simp
  right_inv q := by simp

@[simp] theorem liftSP_apply (s : SignedPerm Ω) (b : Bool) (j : Ω) :
    liftSP s (b, j) = (xor b (s.sign j), s.perm j) := rfl

theorem liftSP_mul (s t : SignedPerm Ω) : liftSP (s * t) = liftSP s * liftSP t := by
  ext ⟨b, j⟩
  · simp only [liftSP_apply, SignedPerm.mul_sign, SignedPerm.mul_perm, Equiv.Perm.mul_apply]
    cases b <;> cases s.sign (t.perm j) <;> cases t.sign j <;> rfl
  · simp

theorem liftSP_one : liftSP (1 : SignedPerm Ω) = 1 := by
  ext ⟨b, j⟩ <;> simp

/-- The lift as a homomorphism to the permutations of `Fin N`, along `e`. -/
def liftHom {N : ℕ} (e : Bool × Ω ≃ Fin N) : SignedPerm Ω →* Equiv.Perm (Fin N) where
  toFun s := e.permCongr (liftSP s)
  map_one' := by rw [liftSP_one]; ext p; simp [Equiv.permCongr_apply]
  map_mul' s t := by rw [liftSP_mul, Equiv.permCongr_mul]

theorem liftHom_apply {N : ℕ} (e : Bool × Ω ≃ Fin N) (s : SignedPerm Ω) (b : Bool) (j : Ω) :
    liftHom e s (e (b, j)) = e (xor b (s.sign j), s.perm j) := by
  simp [liftHom, Equiv.permCongr_apply]

theorem liftHom_fix_iff {N : ℕ} (e : Bool × Ω ≃ Fin N) (s : SignedPerm Ω) (b : Bool) (j : Ω) :
    liftHom e s (e (b, j)) = e (b, j) ↔ s.perm j = j ∧ s.sign j = false := by
  rw [liftHom_apply, e.apply_eq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by cases b <;> cases h : s.sign j <;> simp_all⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

theorem negOne_mul_negOne : (SignedPerm.negOne : SignedPerm Ω) * SignedPerm.negOne = 1 := by
  ext j <;> simp [SignedPerm.negOne]

end Lift

theorem re_half_one_sub_eq_zero {Ω : Type*} [DecidableEq Ω] (s : SignedPerm Ω) (j : Ω)
    (h : ((1 / 2 : ℂ) * (1 - s.toMatrix j j)).re = 0) : s.perm j = j ∧ s.sign j = false := by
  rw [toMatrix_apply_self] at h
  by_cases hp : s.perm j = j
  · cases hs : s.sign j
    · exact ⟨hp, rfl⟩
    · simp [hp, hs, bitSign] at h
  · simp [hp] at h

/-! ## The action of a Z-aligned permutation strategy -/

namespace ZStrat

variable {g : TailoredGameData} (S : ZStrat g)

/-- The signed permutation of an observable. -/
noncomputable def spU (x : Fin (g.nV + 1)) (i : Fin g.ansLen) : SignedPerm (Fin S.m) :=
  Classical.choose (isSignedPerm_iff.mp (S.signedPerm x i))

theorem toMatrix_spU (x : Fin (g.nV + 1)) (i : Fin g.ansLen) : (S.spU x i).toMatrix = S.U x i :=
  Classical.choose_spec (isSignedPerm_iff.mp (S.signedPerm x i))

/-- The signed permutation of each generator: `-1` for `J`, that of `U x i` for `X(x, i)`. -/
noncomputable def genSP (k : ℕ) : SignedPerm (Fin S.m) :=
  if k = 0 then SignedPerm.negOne
  else if h : (k - 1) / g.ansLen < g.nV + 1 ∧ (k - 1) % g.ansLen < g.ansLen then
    S.spU ⟨(k - 1) / g.ansLen, h.1⟩ ⟨(k - 1) % g.ansLen, h.2⟩
  else 1

theorem genSP_J : S.genSP genJ = SignedPerm.negOne := rfl

theorem genSP_X (x : Fin (g.nV + 1)) (i : Fin g.ansLen) :
    S.genSP (genX g x.val i.val) = S.spU x i := by
  have hΛ : 0 < g.ansLen := i.pos
  have hk : genX g x.val i.val - 1 = x.val * g.ansLen + i.val := by unfold genX; omega
  have hdiv : (x.val * g.ansLen + i.val) / g.ansLen = x.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hΛ, Nat.div_eq_of_lt i.isLt, zero_add]
  have hmod : (x.val * g.ansLen + i.val) % g.ansLen = i.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  unfold genSP
  rw [ite_eq_right (by unfold genX; omega)]
  simp only [hk, hdiv, hmod, x.isLt, i.isLt, and_self, dite_true]

theorem genSP_of_ge (k : ℕ) (hk : nGen g ≤ k) : S.genSP k = 1 := by
  unfold genSP nGen at *
  rw [ite_eq_right (by omega)]
  rw [dite_eq_right]
  rintro ⟨h1, h2⟩
  have hΛ : 0 < g.ansLen := Nat.pos_of_ne_zero fun h => by simp [h] at h2
  have : (g.nV + 1) * g.ansLen ≤ k - 1 := by omega
  have := (Nat.le_div_iff_mul_le hΛ).mpr this
  omega

theorem toMatrix_genSP_X (z : Fin (g.nV + 1)) (i : ℕ) (hi : i < g.lenAt z.val) :
    (S.genSP (genX g z.val i)).toMatrix = S.Unat z i := by
  have hΛ : i < g.ansLen := hi.trans_le (lenAt_le_ansLen g z)
  rw [show i = (⟨i, hΛ⟩ : Fin g.ansLen).val from rfl, genSP_X, toMatrix_spU]
  simp [ZStrat.Unat, hΛ]

theorem spU_mul_self (x : Fin (g.nV + 1)) (i : Fin g.ansLen) : S.spU x i * S.spU x i = 1 := by
  rw [← SignedPerm.toMatrix_inj, SignedPerm.toMatrix_mul, toMatrix_spU, SignedPerm.toMatrix_one,
    S.invol]

theorem spU_comm (x : Fin (g.nV + 1)) (i j : Fin g.ansLen) :
    S.spU x i * S.spU x j = S.spU x j * S.spU x i := by
  rw [← SignedPerm.toMatrix_inj, SignedPerm.toMatrix_mul, SignedPerm.toMatrix_mul, toMatrix_spU,
    toMatrix_spU, S.comm]

theorem spU_perm (x : Fin (g.nV + 1)) (i : Fin g.ansLen) (hi : i.val < g.lenRAt x.val) :
    (S.spU x i).perm = 1 := by
  rw [← SignedPerm.isDiag_toMatrix_iff, toMatrix_spU]
  exact S.zAligned x i hi

/-- The points `Bool × Fin m` as `Fin (2m)`. -/
def ptEquiv (m : ℕ) : Bool × Fin m ≃ Fin (2 * m) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl _)).trans finProdFinEquiv

/-- **The action of a Z-aligned permutation strategy.** -/
noncomputable abbrev toAction : FiniteAction (nGen g) where
  N := 2 * S.m
  N_pos := by have := S.m_pos; omega
  σ k := liftHom (ptEquiv S.m) (S.genSP k.val)

theorem genPerm_toAction (k : ℕ) :
    genPerm S.toAction k = liftHom (ptEquiv S.m) (S.genSP k) := by
  unfold genPerm FiniteAction.letterPerm
  by_cases hk : k < nGen g
  · simp [hk, toAction]
  · simp only [hk, dite_false, S.genSP_of_ge k (not_lt.mp hk), map_one]

theorem wordPerm_toAction (w : Word) :
    S.toAction.wordPerm w = liftHom (ptEquiv S.m) (wordSP S.genSP w) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    obtain ⟨k, b⟩ := l
    rw [wordPerm_cons, ih, letterPerm_eq, genPerm_toAction]
    simp only [wordSP, List.map_cons, List.prod_cons, map_mul]
    cases b <;> simp

theorem exists_pt (p : Fin S.toAction.N) : ∃ b j, p = ptEquiv S.m (b, j) :=
  ⟨((ptEquiv S.m).symm p).1, ((ptEquiv S.m).symm p).2, by simp⟩

/-- **The action passes Checks 1–3.** -/
theorem checks_toAction : Checks g S.toAction where
  J_invol p := by
    rw [genPerm_toAction, genSP_J, ← Equiv.Perm.mul_apply, ← map_mul, negOne_mul_negOne, map_one,
      Equiv.Perm.one_apply]
  J_free p := by
    obtain ⟨b, j, rfl⟩ := S.exists_pt p
    rw [genPerm_toAction, genSP_J, Ne, liftHom_fix_iff]
    simp [SignedPerm.negOne]
  J_comm x i hx hi := by
    rw [genPerm_toAction, genPerm_toAction, ← map_mul, ← map_mul, genSP_J, SignedPerm.negOne_comm]
  X_invol x i hx hi p := by
    have hΛ : i < g.ansLen := hi.trans_le (lenAt_le_ansLen g ⟨x, hx⟩)
    rw [genPerm_toAction, ← Equiv.Perm.mul_apply, ← map_mul,
      show x = (⟨x, hx⟩ : Fin (g.nV + 1)).val from rfl,
      show i = (⟨i, hΛ⟩ : Fin g.ansLen).val from rfl, genSP_X, spU_mul_self, map_one,
      Equiv.Perm.one_apply]
  X_comm x i i' hx hi hi' := by
    have hΛ : i < g.ansLen := hi.trans_le (lenAt_le_ansLen g ⟨x, hx⟩)
    have hΛ' : i' < g.ansLen := hi'.trans_le (lenAt_le_ansLen g ⟨x, hx⟩)
    rw [genPerm_toAction, genPerm_toAction, ← map_mul, ← map_mul,
      show x = (⟨x, hx⟩ : Fin (g.nV + 1)).val from rfl,
      show i = (⟨i, hΛ⟩ : Fin g.ansLen).val from rfl,
      show i' = (⟨i', hΛ'⟩ : Fin g.ansLen).val from rfl, genSP_X, genSP_X, spU_comm]
  readable x i hx hi p := by
    obtain ⟨b, j, rfl⟩ := S.exists_pt p
    have hΛ : i < g.ansLen :=
      (lt_of_lt_of_le hi (Nat.le_add_right _ _)).trans_le (lenAt_le_ansLen g ⟨x, hx⟩)
    rw [genPerm_toAction, genPerm_toAction, genSP_J,
      show x = (⟨x, hx⟩ : Fin (g.nV + 1)).val from rfl,
      show i = (⟨i, hΛ⟩ : Fin g.ansLen).val from rfl, genSP_X, liftHom_apply, liftHom_apply,
      S.spU_perm _ _ hi]
    cases S.spU ⟨x, hx⟩ ⟨i, hΛ⟩ |>.sign j <;> simp [SignedPerm.negOne]

theorem rbit_eq (x : Fin (g.nV + 1)) (i : ℕ) (hi : i < g.lenRAt x.val) (j : Fin S.m) :
    S.rbit x i j = (S.genSP (genX g x.val i)).sign j := by
  have hΛ : i < g.ansLen :=
    (lt_of_lt_of_le hi (Nat.le_add_right _ _)).trans_le (lenAt_le_ansLen g x)
  rw [show i = (⟨i, hΛ⟩ : Fin g.ansLen).val from rfl, genSP_X]
  unfold ZStrat.rbit
  rw [dite_eq_left hΛ, ← toMatrix_spU, toMatrix_apply_self, S.spU_perm x _ hi]
  simp only [Equiv.Perm.coe_one, id, ite_true]
  cases (S.spU x ⟨i, hΛ⟩).sign j <;> norm_num [bitSign]

theorem rdv_toAction (x y : Fin (g.nV + 1)) (b : Bool) (j : Fin S.m) :
    rdv S.toAction x y (ptEquiv S.m (b, j)) = S.rsgn x j ++ S.rsgn y j := by
  simp only [ZStrat.rsgn, rdv, readVars, List.map_append, List.map_map]
  have key : ∀ z : Fin (g.nV + 1), ∀ i ∈ List.range (g.lenRAt z.val),
      decide (S.toAction.wordPerm (wX g z.val i) (ptEquiv S.m (b, j)) ≠ ptEquiv S.m (b, j)) =
        S.rbit z i j := by
    intro z i hi
    have hi' := List.mem_range.mp hi
    have hΛ : i < g.ansLen :=
      (lt_of_lt_of_le hi' (Nat.le_add_right _ _)).trans_le (lenAt_le_ansLen g z)
    have hX := S.genSP_X z ⟨i, hΛ⟩
    simp only at hX
    rw [S.rbit_eq z i hi', wordPerm_wX, genPerm_toAction]
    simp only [ne_eq, liftHom_fix_iff]
    rw [hX, S.spU_perm z _ hi']
    cases (S.spU z ⟨i, hΛ⟩).sign j <;> simp
  congr 1
  · exact List.map_congr_left (key x)
  · exact List.map_congr_left (key y)

theorem consMat_eq (x y : Fin (g.nV + 1)) (c : List Bool) :
    S.consMat x y c = (wordSP S.genSP (consWord g x y c)).toMatrix :=
  (S.toMatrix_wordSP_consWord x y _ (by rw [genSP_J, SignedPerm.toMatrix_negOne])
    (fun z i hi => S.toMatrix_genSP_X z i hi) c).symm

open Classical in
/-- **At value `1`, every constraint word of a pair of positive weight has `1` on the diagonal of
its readable class.** -/
theorem consMat_apply_self_eq_one (hS : S.value = 1) (x y : Fin (g.nV + 1))
    (hμ : 0 < g.toGame.μ x y) {e : ℕ × ℕ × List Bool × List Bool} (he : e ∈ consAt g x y)
    (j : Fin S.m) (hj : S.rsgn x j ++ S.rsgn y j = e.2.2.1) :
    (wordSP S.genSP (consWord g x y e.2.2.2)).perm j = j ∧
      (wordSP S.genSP (consWord g x y e.2.2.2)).sign j = false := by
  -- the rejection probability vanishes
  have hrej : S.rej x y = 0 := by
    have hsum : ∑ x, ∑ y, g.toGame.μ x y * S.rej x y = 0 := by
      have h := S.value_eq_sum_rej
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, g.toGame.μ_sum_one] at h
      linarith
    have hnn : ∀ x y, 0 ≤ g.toGame.μ x y * S.rej x y :=
      fun x y => mul_nonneg (g.toGame.μ_nonneg x y) (S.rej_nonneg x y)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
      Finset.sum_nonneg fun y _ => hnn x y).mp hsum x (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn x y).mp h1 y (Finset.mem_univ _)
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hμ.ne'
    · exact h
  set w := consWord g x y e.2.2.2
  set M := (wordSP S.genSP w).toMatrix
  -- the violations of the word `w` have probability zero
  have hviol : ∑ a, ∑ b, (if ViolW g x y w a b then
      (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0) = 0 := by
    refine le_antisymm (le_of_le_of_eq ?_ hrej) (Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => by
        split_ifs
        · exact div_nonneg (S.re_trace_proj_mul_proj_nonneg x y a b) (Nat.cast_nonneg _)
        · rfl)
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hV : ViolW g x y w a b
    · obtain ⟨e', he', hw', hr, hs⟩ := hV
      have hA : ¬g.Accepts x y a b := fun hA => by
        obtain ⟨h1, h2, h3⟩ := mem_consAt.mp he'
        exact hs (hA.2.2.2 e' h1 h2 h3 hr)
      rw [ite_eq_left ⟨e', he', hw', hr, hs⟩, ite_eq_right hA, one_mul]
    · rw [ite_eq_right hV]
      exact mul_nonneg (by split_ifs <;> norm_num)
        (div_nonneg (S.re_trace_proj_mul_proj_nonneg x y a b) (Nat.cast_nonneg _))
  have h0 := S.sum_viol_eq x y w M (fun e' he' hw' => by rw [S.consMat_eq, hw'])
  rw [hviol] at h0
  have hm : (0 : ℝ) < S.m := Nat.cast_pos.mpr S.m_pos
  have h1 := (div_eq_zero_iff.mp h0.symm).resolve_right hm.ne'
  rw [Complex.re_sum] at h1
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin S.m)), 0 ≤ (if ReadW g x y w (S.rsgn x j ++ S.rsgn y j)
      then (1 / 2 : ℂ) * (1 - M j j) else 0).re := fun j _ => by
    split_ifs
    · exact re_one_sub_toMatrix_apply_self_nonneg _ _
    · simp
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h1 j (Finset.mem_univ _)
  rw [ite_eq_left ⟨e, he, rfl, hj.symm⟩] at h2
  exact re_half_one_sub_eq_zero _ j h2

end ZStrat

/-- **Completeness of the associated test** (Theorem I:2126 (1)): a tailored game with a perfect
Z-aligned permutation strategy (commuting along edges, which is not used) has an associated test
of value `1`. -/
theorem exists_value_one_of_hasPerfectZPC (g : TailoredGameData) (h : g.HasPerfectZPC) :
    ∃ σ : FiniteAction (nGen g), (assocTest g).value σ = 1 := by
  obtain ⟨S, hS⟩ := h
  have hZ : S.toZStrat.value = 1 := hS
  refine ⟨S.toZStrat.toAction, ?_⟩
  rw [value_eq_sum]
  have hpass : ∀ x y : Fin (g.nV + 1),
      g.toGame.μ x y * S.toZStrat.toAction.passProb (words g x y) (clauses g x y) =
        g.toGame.μ x y := by
    intro x y
    rcases (g.toGame.μ_nonneg x y).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
    · have hall : ∀ p, S.toZStrat.toAction.Passes (words g x y) (clauses g x y) p := by
        intro p
        obtain ⟨b, j, rfl⟩ := S.toZStrat.exists_pt p
        rw [passes_iff S.toZStrat.checks_toAction x.isLt y.isLt]
        intro e he her
        rw [S.toZStrat.rdv_toAction] at her
        obtain ⟨h1, h2⟩ := S.toZStrat.consMat_apply_self_eq_one hZ x y hpos he j her.symm
        show S.toZStrat.toAction.wordPerm _ _ = _
        rw [S.toZStrat.wordPerm_toAction, liftHom_fix_iff]
        exact ⟨h1, h2⟩
      have hN : (S.toZStrat.toAction.N : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr S.toZStrat.toAction.N_pos.ne'
      unfold FiniteAction.passProb
      rw [Finset.filter_true_of_mem (fun p _ => hall p), Finset.card_univ, Fintype.card_fin,
        div_self hN, mul_one]
  simp only [hpass]
  exact g.toGame.μ_sum_one

end MIPRE.Tailored.Sofic

end
