/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Quotient
public import MIPRE.Tactics

@[expose] public section

/-!
# Soundness of the associated test (Proposition I:2279)

An action `σ` passing Checks 1–3 of `assocTest g` everywhere gives the Z-aligned permutation
strategy `quotStrat σ hσ`, whose rejection probability at each question pair `(x, y)` is at most
`2 |consWords x y|` times the probability that `σ` fails the challenge at `(x, y)`
(`rej_quotStrat_le`). With at most `2^{2(Λ+1)}` distinct constraint words, this gives
(`gameValue_ge_of_checks`)

`1 - Cq · 2^{2(Λ+1)} · (1 - val(T̃, σ)) ≤ val(G)`, `Cq = 2`.

The proof, for each distinct constraint word `w` at `(x, y)`:

* a rejected answer pair with nonzero weight violates some constraint, whose word is one of the
  `w` (`rej_le_sum_viol`): malformed answers have zero projection, unequal answers at a loop
  orthogonal ones;
* the probability of violating a constraint with word `w` is
  `(1/m) ∑_{j ∈ R_w} Re ((1 - M_w)/2)_{jj}`, `R_w` the basis points whose readable signs are the
  readable value of such a constraint (`sum_viol_eq`, from the trace identity); all constraints
  with the word `w` have the same matrix `M_w`, the induced signed permutation of `w`, so the
  violated ones are those of sign `-1`;
* `((1 - M_w)/2)_{jj}` vanishes when `w` fixes the representative `j`, and the representatives
  of `R_w` that `w` moves fail the challenge (`passes_iff`).
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue

/-- The constant of Proposition I:2279. -/
def Cq : ℝ := 2

variable {g : TailoredGameData}

open Classical in
/-- The answer pair `(a, b)` violates a constraint at `(x, y)` whose word is `w`. -/
def ViolW (g : TailoredGameData) (x y : Fin (g.nV + 1)) (w : Word) (a b : Fin g.ansLen → Bool) :
    Prop :=
  ∃ e ∈ consAt g x y, consWord g x y e.2.2.2 = w ∧ e.2.2.1 = g.readable x a ++ g.readable y b ∧
    ¬TailoredGameData.Satisfies e.2.2.2 (g.full x a ++ g.full y b ++ [true])

/-- The readable value `r` carries a constraint at `(x, y)` whose word is `w`. -/
def ReadW (g : TailoredGameData) (x y : Fin (g.nV + 1)) (w : Word) (r : List Bool) : Prop :=
  ∃ e ∈ consAt g x y, consWord g x y e.2.2.2 = w ∧ e.2.2.1 = r

theorem mem_consAt {x y : ℕ} {e : ℕ × ℕ × List Bool × List Bool} :
    e ∈ consAt g x y ↔ e ∈ g.cons ∧ e.1 = x ∧ e.2.1 = y := by
  simp [consAt]

namespace ZStrat

variable (S : ZStrat g)

open Classical in
/-- **A rejected answer pair violates a constraint** (union bound over the distinct words). -/
theorem rej_le_sum_viol (x y : Fin (g.nV + 1)) :
    S.rej x y ≤ ∑ w ∈ (consWords g x y).toFinset, ∑ a, ∑ b,
      (if ViolW g x y w a b then (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0) := by
  unfold rej
  have hswap : ∀ F : (Fin g.ansLen → Bool) → (Fin g.ansLen → Bool) → Word → ℝ,
      ∑ a, ∑ b, ∑ w ∈ (consWords g x y).toFinset, F a b w =
        ∑ w ∈ (consWords g x y).toFinset, ∑ a, ∑ b, F a b w := by
    intro F
    calc ∑ a, ∑ b, ∑ w ∈ (consWords g x y).toFinset, F a b w
        = ∑ a, ∑ w ∈ (consWords g x y).toFinset, ∑ b, F a b w :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  refine le_of_le_of_eq (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    (?_ : (if g.Accepts x y a b then (0 : ℝ) else 1) *
      ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ)) ≤ ∑ w ∈ (consWords g x y).toFinset,
        if ViolW g x y w a b then (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0))
    (hswap fun a b w =>
      if ViolW g x y w a b then (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0)
  have hτ : 0 ≤ (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) :=
    div_nonneg (S.re_trace_proj_mul_proj_nonneg x y a b) (Nat.cast_nonneg _)
  have hnn : 0 ≤ ∑ w ∈ (consWords g x y).toFinset,
      (if ViolW g x y w a b then (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0) :=
    Finset.sum_nonneg fun w _ => by split_ifs <;> simp [hτ]
  by_cases hA : g.Accepts x y a b
  · rw [ite_eq_left hA, zero_mul]
    exact hnn
  rw [ite_eq_right hA, one_mul]
  by_cases hbad : (x = y ∧ a ≠ b) ∨ ¬g.WellFormatted x a ∨ ¬g.WellFormatted y b
  · have h0 : S.proj x a * S.proj y b = 0 := by
      rcases hbad with ⟨rfl, hab⟩ | ha | hb
      · exact S.proj_mul_proj_of_ne x hab
      · rw [S.proj_eq_zero_of_not_wellFormatted x a ha, Matrix.zero_mul]
      · rw [S.proj_eq_zero_of_not_wellFormatted y b hb, Matrix.mul_zero]
    rw [h0, Matrix.trace_zero, Complex.zero_re, zero_div]
    exact Finset.sum_nonneg fun w _ => by split_ifs <;> rfl
  push Not at hbad
  obtain ⟨hxy, ha, hb⟩ := hbad
  have hviol : ∃ e ∈ g.cons, e.1 = x.val ∧ e.2.1 = y.val ∧
      e.2.2.1 = g.readable x a ++ g.readable y b ∧
      ¬TailoredGameData.Satisfies e.2.2.2 (g.full x a ++ g.full y b ++ [true]) := by
    by_contra hcon
    push Not at hcon
    exact hA ⟨hxy, ha, hb, fun e he h1 h2 h3 => hcon e he h1 h2 h3⟩
  obtain ⟨e, he, h1, h2, h3, h4⟩ := hviol
  have he' : e ∈ consAt g x y := mem_consAt.mpr ⟨he, h1, h2⟩
  have hw : consWord g x y e.2.2.2 ∈ (consWords g x y).toFinset :=
    List.mem_toFinset.mpr (consWord_mem_consWords he')
  refine le_trans ?_ (Finset.single_le_sum (f := fun w =>
    if ViolW g x y w a b then (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0)
    (fun w _ => by split_ifs <;> simp [hτ]) hw)
  rw [ite_eq_left ⟨e, he', rfl, h3, h4⟩]

open Classical in
/-- **The probability of violating a constraint with word `w`, by the trace identity**, for a
matrix `M` that is the matrix of every constraint with word `w`. -/
theorem sum_viol_eq (x y : Fin (g.nV + 1)) (w : Word) (M : Matrix (Fin S.m) (Fin S.m) ℂ)
    (hM : ∀ e ∈ consAt g x y, consWord g x y e.2.2.2 = w → S.consMat x y e.2.2.2 = M) :
    ∑ a, ∑ b, (if ViolW g x y w a b then
        (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0) =
      (∑ j, if ReadW g x y w (S.rsgn x j ++ S.rsgn y j) then
        ((1 / 2 : ℂ) * (1 - M j j)) else 0).re / (S.m : ℝ) := by
  have key : ∀ a b, (if ViolW g x y w a b then
      (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) else 0) =
      (if ReadW g x y w (g.readable x a ++ g.readable y b) then
        (S.proj x a * ((1 / 2 : ℂ) • (1 - M)) * S.proj y b).trace else 0).re / (S.m : ℝ) := by
    intro a b
    by_cases hV : ViolW g x y w a b
    · obtain ⟨e, he, hw, hr, hs⟩ := hV
      rw [ite_eq_left ⟨e, he, hw, hr, hs⟩, ite_eq_left ⟨e, he, hw, hr⟩, ← hM e he hw,
        ← S.ite_satisfies_smul, ite_eq_right hs, one_smul]
    · rw [ite_eq_right hV]
      by_cases hR : ReadW g x y w (g.readable x a ++ g.readable y b)
      · obtain ⟨e, he, hw, hr⟩ := hR
        have hs : TailoredGameData.Satisfies e.2.2.2 (g.full x a ++ g.full y b ++ [true]) := by
          by_contra hs; exact hV ⟨e, he, hw, hr, hs⟩
        rw [ite_eq_left ⟨e, he, hw, hr⟩, ← hM e he hw, ← S.ite_satisfies_smul, ite_eq_left hs,
          zero_smul, Matrix.trace_zero, Complex.zero_re, zero_div]
      · rw [ite_eq_right hR, Complex.zero_re, zero_div]
  simp_rw [key, ← Finset.sum_div, ← Complex.re_sum]
  congr 2
  rw [S.sum_trace_proj_mul_mul_proj x y (ReadW g x y w)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq]
  · rfl

end ZStrat

/-! ## The quotient strategy -/

section Quotient

variable {σ : FiniteAction (nGen g)} (hσ : Checks g σ)
include hσ

theorem unat_quotStrat (z : Fin (g.nV + 1)) (i : ℕ) (hi : i < g.lenAt z.val) :
    (quotStrat σ hσ).Unat z i = (indF σ (genPerm σ (genX g z.val i))).toMatrix := by
  unfold ZStrat.Unat
  rw [dite_eq_left (hi.trans_le (lenAt_le_ansLen g z))]
  show quotU σ z _ = _
  unfold quotU
  rw [ite_eq_left hi]

theorem consMat_quotStrat (x y : Fin (g.nV + 1)) (c : List Bool) :
    (quotStrat σ hσ).consMat x y c =
      (wordSP (fun k => indF σ (genPerm σ k)) (consWord g x y c)).toMatrix :=
  ((quotStrat σ hσ).toMatrix_wordSP_consWord x y _ (toMatrix_indF_J hσ)
    (fun z i hi => (unat_quotStrat hσ z i hi).symm) c).symm

omit hσ in
theorem mem_consWord {x y : Fin (g.nV + 1)} {c : List Bool} {l : Letter}
    (hl : l ∈ consWord g x y c) :
    l = (genJ, false) ∨ ∃ z : Fin (g.nV + 1), ∃ i < g.lenAt z.val, l = (genX g z.val i, false) := by
  unfold consWord at hl
  by_cases hc : c.length = g.lenAt x.val + g.lenAt y.val + 1
  · rw [ite_eq_left hc] at hl
    simp only [List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · by_cases hJ : c.getD (g.lenAt x.val + g.lenAt y.val) false = true
      · rw [ite_eq_left hJ] at hl
        left; simpa [wJ, genW] using hl
      · rw [ite_eq_right hJ] at hl
        simp at hl
    · obtain ⟨i, hi, hl⟩ := List.mem_flatMap.mp hl
      right
      exact ⟨x, i, List.mem_range.mp (List.mem_filter.mp hi).1, by simpa [wX, genW] using hl⟩
    · obtain ⟨i, hi, hl⟩ := List.mem_flatMap.mp hl
      right
      exact ⟨y, i, List.mem_range.mp (List.mem_filter.mp hi).1, by simpa [wX, genW] using hl⟩
  · rw [ite_eq_right hc] at hl
    left; simpa [wJ, genW] using hl

theorem indF_wordPerm (w : Word)
    (hw : ∀ l ∈ w, l.2 = false ∧ CommJ (genPerm σ genJ) (genPerm σ l.1)) :
    CommJ (genPerm σ genJ) (σ.wordPerm w) ∧
      indF σ (σ.wordPerm w) = wordSP (fun k => indF σ (genPerm σ k)) w := by
  induction w with
  | nil => exact ⟨CommJ.one, by rw [wordPerm_nil, indF_one hσ, wordSP_nil]⟩
  | cons l w ih =>
    obtain ⟨hc, hi⟩ := ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    obtain ⟨hl2, hl1⟩ := hw l List.mem_cons_self
    have hlp : σ.letterPerm l = genPerm σ l.1 := by
      obtain ⟨k, b⟩ := l
      simp only at hl2
      rw [hl2, letterPerm_eq]
      rfl
    rw [wordPerm_cons, hlp]
    refine ⟨hl1.mul hc, ?_⟩
    rw [indF_mul hσ hl1 hc, hi]
    simp [wordSP, hl2]

theorem consWord_indF (x y : Fin (g.nV + 1)) (c : List Bool) :
    CommJ (genPerm σ genJ) (σ.wordPerm (consWord g x y c)) ∧
      (quotStrat σ hσ).consMat x y c = (indF σ (σ.wordPerm (consWord g x y c))).toMatrix := by
  have hw : ∀ l ∈ consWord g x y c, l.2 = false ∧ CommJ (genPerm σ genJ) (genPerm σ l.1) := by
    intro l hl
    rcases mem_consWord hl with rfl | ⟨z, i, hi, rfl⟩
    · exact ⟨rfl, CommJ.self⟩
    · exact ⟨rfl, hσ.commJ_X z.isLt hi⟩
  obtain ⟨hc, he⟩ := indF_wordPerm hσ _ hw
  exact ⟨hc, by rw [consMat_quotStrat hσ, he]⟩

theorem rbit_quotStrat (x : Fin (g.nV + 1)) (i : ℕ) (hi : i < g.lenRAt x.val)
    (j : Fin (quotStrat σ hσ).m) :
    (quotStrat σ hσ).rbit x i j =
      decide (genPerm σ (genX g x.val i) (repPt σ j) ≠ repPt σ j) := by
  have hi' : i < g.lenAt x.val := lt_of_lt_of_le hi (Nat.le_add_right _ _)
  have hc := hσ.commJ_X x.isLt hi'
  have hr := hσ.readable' x.isLt hi
  have key : ∀ j' : Fin (Fintype.card (Reps (genPerm σ genJ))),
      (indF σ (genPerm σ (genX g x.val i))).toMatrix j' j' =
        bitSign (decide (genPerm σ (genX g x.val i) (repPt σ j') ≠ repPt σ j')) := by
    intro j'
    rw [toMatrix_apply_self, indF_perm_eq_one hσ hc hr, indF_sign_eq hσ hc hr]
    simp
  unfold ZStrat.rbit
  rw [dite_eq_left (hi'.trans_le (lenAt_le_ansLen g x))]
  show decide (quotU σ x _ j j = -1) = _
  simp only [quotU, hi', ite_true]
  rw [key j]
  by_cases h : genPerm σ (genX g x.val i) (repPt σ j) = repPt σ j <;> norm_num [h, bitSign]

theorem rsgn_quotStrat (x y : Fin (g.nV + 1)) (j : Fin (quotStrat σ hσ).m) :
    (quotStrat σ hσ).rsgn x j ++ (quotStrat σ hσ).rsgn y j = rdv σ x y (repPt σ j) := by
  simp only [ZStrat.rsgn, rdv, readVars, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    rw [rbit_quotStrat hσ x i (List.mem_range.mp hi)]
    simp
  · refine List.map_congr_left fun i hi => ?_
    rw [rbit_quotStrat hσ y i (List.mem_range.mp hi)]
    simp

omit hσ in
/-- The failure probability of a challenge. -/
theorem one_sub_passProb (K : List Word) (cl : List (List (ℕ × Bool))) :
    1 - σ.passProb K cl =
      ((Finset.univ.filter fun p => ¬σ.Passes K cl p).card : ℝ) / σ.N := by
  have hN : (σ.N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr σ.N_pos.ne'
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin σ.N)))
    (fun p => σ.Passes K cl p)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h' : (σ.N : ℝ) = ((Finset.univ.filter fun p => σ.Passes K cl p).card : ℝ) +
      ((Finset.univ.filter fun p => ¬σ.Passes K cl p).card : ℝ) := by exact_mod_cast h.symm
  unfold FiniteAction.passProb
  rw [eq_div_iff hN, sub_mul, div_mul_cancel₀ _ hN, one_mul, h']
  ring

open Classical in
/-- **The rejection probability of the quotient strategy at a question pair** is at most
`2 |consWords|` times the failure probability of the challenge. -/
theorem rej_quotStrat_le (x y : Fin (g.nV + 1)) :
    (quotStrat σ hσ).rej x y ≤
      2 * (consWords g x y).length * (1 - σ.passProb (words g x y) (clauses g x y)) := by
  set F := Finset.univ.filter fun p => ¬σ.Passes (words g x y) (clauses g x y) p
  have hm : (0 : ℝ) < (quotStrat σ hσ).m := Nat.cast_pos.mpr (quotStrat σ hσ).m_pos
  have hNm : (σ.N : ℝ) ≤ 2 * (quotStrat σ hσ).m := by
    exact_mod_cast card_le_two_mul_card_reps hσ.ffInvol
  -- each distinct word contributes at most `2 (1 - passProb)`
  have hw : ∀ w ∈ (consWords g x y).toFinset, ∑ a, ∑ b,
      (if ViolW g x y w a b then ((quotStrat σ hσ).proj x a * (quotStrat σ hσ).proj y b).trace.re / ((quotStrat σ hσ).m : ℝ) else 0) ≤
        2 * (1 - σ.passProb (words g x y) (clauses g x y)) := by
    intro w hw
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp (List.mem_toFinset.mp hw))
    obtain ⟨hcomm, hM₀⟩ := consWord_indF hσ x y e₀.2.2.2
    rw [(quotStrat σ hσ).sum_viol_eq x y _ _ (fun e he hew => by
      rw [(consWord_indF hσ x y e.2.2.2).2, hew, ← hM₀])]
    rw [one_sub_passProb, Complex.re_sum]
    -- the diagonal bound
    have hdiag : ∀ j, (if ReadW g x y (consWord g x y e₀.2.2.2) ((quotStrat σ hσ).rsgn x j ++ (quotStrat σ hσ).rsgn y j) then
        (1 / 2 : ℂ) * (1 - (quotStrat σ hσ).consMat x y e₀.2.2.2 j j) else 0).re ≤
          if ¬σ.Passes (words g x y) (clauses g x y) (repPt σ j) then 1 else 0 := by
      intro j
      by_cases hR : ReadW g x y (consWord g x y e₀.2.2.2) ((quotStrat σ hσ).rsgn x j ++ (quotStrat σ hσ).rsgn y j)
      · rw [ite_eq_left hR, hM₀]
        refine (re_one_sub_toMatrix_apply_self_le
          (indF σ (σ.wordPerm (consWord g x y e₀.2.2.2))) j).trans ?_
        by_cases hP : σ.Passes (words g x y) (clauses g x y) (repPt σ j)
        · obtain ⟨e, he, hew, her⟩ := hR
          rw [rsgn_quotStrat hσ] at her
          have hfix := (passes_iff hσ x.isLt y.isLt _).mp hP e he her
          rw [ite_eq_left ((indF_fix_iff hσ hcomm j).mpr (hew ▸ hfix))]
          rw [ite_eq_right (not_not.mpr hP)]
        · rw [ite_eq_left hP]
          split_ifs <;> norm_num
      · rw [ite_eq_right hR, Complex.zero_re]
        split_ifs <;> norm_num
    have hN : (0 : ℝ) < σ.N := Nat.cast_pos.mpr σ.N_pos
    have hc : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
    have hsum : (∑ j, (if ReadW g x y (consWord g x y e₀.2.2.2) ((quotStrat σ hσ).rsgn x j ++ (quotStrat σ hσ).rsgn y j) then
        (1 / 2 : ℂ) * (1 - (quotStrat σ hσ).consMat x y e₀.2.2.2 j j) else 0).re) ≤ F.card := by
      calc _ ≤ ∑ j : Fin (quotStrat σ hσ).m,
            (if ¬σ.Passes (words g x y) (clauses g x y) (repPt σ j) then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun j _ => hdiag j
        _ = ((Finset.univ.filter fun j : Fin (quotStrat σ hσ).m =>
              ¬σ.Passes (words g x y) (clauses g x y) (repPt σ j)).card : ℝ) := by
            rw [Finset.sum_boole]
        _ ≤ F.card := by
            exact_mod_cast Finset.card_le_card_of_injOn (repPt σ)
              (fun j hj => by
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, F]
                  at hj ⊢
                exact hj)
              (fun j _ k _ hjk => (repEquiv σ).symm.injective (Subtype.val_injective hjk))
    calc _ ≤ (F.card : ℝ) / (quotStrat σ hσ).m := div_le_div_of_nonneg_right hsum hm.le
      _ ≤ 2 * ((F.card : ℝ) / σ.N) := by
        rw [div_le_iff₀ hm]
        calc (F.card : ℝ) = F.card / σ.N * σ.N := by field_simp
          _ ≤ F.card / σ.N * (2 * (quotStrat σ hσ).m) := mul_le_mul_of_nonneg_left hNm (div_nonneg hc hN.le)
          _ = 2 * (F.card / σ.N) * (quotStrat σ hσ).m := by ring
  calc (quotStrat σ hσ).rej x y ≤ ∑ w ∈ (consWords g x y).toFinset,
        2 * (1 - σ.passProb (words g x y) (clauses g x y)) :=
        ((quotStrat σ hσ).rej_le_sum_viol x y).trans (Finset.sum_le_sum hw)
    _ = 2 * (consWords g x y).length * (1 - σ.passProb (words g x y) (clauses g x y)) := by
        rw [Finset.sum_const, List.toFinset_card_of_nodup
          (show (consWords g x y).Nodup from List.nodup_dedup _), nsmul_eq_mul]
        ring

end Quotient

/-! ## Proposition I:2279 -/

theorem length_consWords_le_pow (x y : Fin (g.nV + 1)) :
    ((consWords g x y).length : ℝ) ≤ 2 ^ (2 * (g.ansLen + 1)) := by
  have h := length_consWords_le (g := g) x y
  have hx := lenAt_le_ansLen g x
  have hy := lenAt_le_ansLen g y
  have h2 : 2 ^ (g.lenAt x + g.lenAt y + 1) + 1 ≤ 2 ^ (2 * (g.ansLen + 1)) := by
    have h3 : 2 ^ (g.lenAt x + g.lenAt y + 1) ≤ 2 ^ (2 * g.ansLen + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ (2 * g.ansLen + 1) := Nat.one_le_two_pow
    calc _ ≤ 2 ^ (2 * g.ansLen + 1) + 2 ^ (2 * g.ansLen + 1) := by omega
      _ = 2 ^ (2 * (g.ansLen + 1)) := by ring
  exact_mod_cast h.trans h2

theorem passProb_le_one {n : ℕ} (σ : FiniteAction n) (K : List Word)
    (cl : List (List (ℕ × Bool))) : σ.passProb K cl ≤ 1 := by
  unfold FiniteAction.passProb
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  have := Finset.card_filter_le (Finset.univ : Finset (Fin σ.N)) (fun x => σ.Passes K cl x)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

/-- **Soundness half of Proposition I:2279**: an action passing Checks 1–3 everywhere loses the
game at most `Cq · 2^{2(Λ+1)}` times as often as it loses the test. -/
theorem gameValue_ge_of_checks (g : TailoredGameData) (σ : FiniteAction (nGen g))
    (hσ : Checks g σ) :
    1 - Cq * 2 ^ (2 * (g.ansLen + 1)) * (1 - (assocTest g).value σ) ≤
      HaltingGameValue.gameValue g.toGame := by
  set K : ℝ := Cq * 2 ^ (2 * (g.ansLen + 1))
  have hrej : ∀ x y : Fin (g.nV + 1), (quotStrat σ hσ).rej x y ≤
      K * (1 - σ.passProb (words g x y) (clauses g x y)) := by
    intro x y
    refine (rej_quotStrat_le hσ x y).trans ?_
    have h1 : 0 ≤ 1 - σ.passProb (words g x y) (clauses g x y) := by
      linarith [passProb_le_one σ (words g x y) (clauses g x y)]
    have h2 := length_consWords_le_pow (g := g) x y
    simp only [K, Cq]
    exact mul_le_mul_of_nonneg_right (by linarith) h1
  calc 1 - K * (1 - (assocTest g).value σ)
      = ∑ x, ∑ y, g.toGame.μ x y * (1 - K * (1 - σ.passProb (words g x y) (clauses g x y))) := by
        have e : ∀ x y : Fin (g.nV + 1),
            g.toGame.μ x y * (1 - K * (1 - σ.passProb (words g x y) (clauses g x y))) =
              (1 - K) * g.toGame.μ x y +
                K * (g.toGame.μ x y * σ.passProb (words g x y) (clauses g x y)) :=
          fun x y => by ring
        simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, g.toGame.μ_sum_one]
        rw [value_eq_sum σ]
        ring
    _ ≤ ∑ x, ∑ y, g.toGame.μ x y * (1 - (quotStrat σ hσ).rej x y) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (by linarith [hrej x y]) (g.toGame.μ_nonneg x y)
    _ = (quotStrat σ hσ).value := ((quotStrat σ hσ).value_eq_sum_rej).symm
    _ ≤ HaltingGameValue.gameValue g.toGame := (quotStrat σ hσ).value_le_gameValue


end MIPRE.Tailored.Sofic

end
