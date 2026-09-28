/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Paper.Decider

@[expose] public section

/-!
# The halting verifier along the paper's route: the values at level `C`

Blueprint `thm:halting` in the paper's form, at a fixed level, from the decider of
`Paper/Decider.lean` and gap-preserving compression: for a machine `M` and a parameter `λ`
such that `𝒱^halt_{M,λ}` is `λ`-bounded (the accounting of `Paper/Cost.lean` supplies one),

* if `M` halts on the empty input, `𝒱^halt` has a value-`1` PCC strategy at level `C`;
* if it does not, `val*(𝒱^halt_C) ≤ 1/2`;

with `C = max C₀ 2` and answers of length at most `G.bound (C + λ)`.

The argument is the criterion's (`Cost.compressibility_criterion_levels`) at the fixed level
`C`, along the levels `C, 2 ^ C, 2 ^ (2 ^ C), …` of the recursion (`lv`): the two classes are
`A n`, a value-`1` PCC strategy at level `n` with answers of length at most `n ^ λ`, and `B n`,
value at most `1/2` there; `GapCompression.completeness` and `soundness` carry `A (2 ^ n) → A n`
and `B (2 ^ n) → B n` at every level where neither of the decider's first two branches fires
(`lem:dhalt-values`, the acceptance agreement with the compressed verifier); branch 1 puts a
level in `A` outright and branch 2 in `B`; and the search halts exactly when the start level
has value above `1/2` (`exists_semL`, `tabL_value`), which is what rules the search out below
the level where `M` halts, and rules the start level out of `B`'s complement when `M` does not.
-/

namespace MIPRE.Halting

open Cost Cost.Prog

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-- The level the reduction outputs: `max C₀ 2`, so that the time clauses of `IsBounded` apply
there. -/
def C (G : GapCompression) : ℕ := max G.C₀ 2

theorem two_le_C : 2 ≤ C G := le_max_right _ _

theorem C₀_le_C : G.C₀ ≤ C G := le_max_left _ _

/-- The levels of the recursion started at `C`: `C, 2 ^ C, 2 ^ (2 ^ C), …`. -/
def lv (G : GapCompression) : ℕ → ℕ
  | 0 => C G
  | j + 1 => 2 ^ lv G j

@[simp] theorem lv_zero : lv G 0 = C G := rfl

@[simp] theorem lv_succ (j : ℕ) : lv G (j + 1) = 2 ^ lv G j := rfl

theorem two_pow_le_lv : ∀ j, 2 ^ j ≤ lv G j
  | 0 => (Nat.pow_le_pow_right two_pos (Nat.zero_le 1)).trans (two_le_C G)
  | j + 1 => by
    rw [lv_succ, pow_succ]
    have h := two_pow_le_lv j
    have h2 : 2 ^ j * 2 ≤ 2 ^ 2 ^ j := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right two_pos (Nat.lt_two_pow_self)
    exact h2.trans (Nat.pow_le_pow_right two_pos h)

theorem C_le_lv : ∀ j, C G ≤ lv G j
  | 0 => le_rfl
  | j + 1 => by
    rw [lv_succ]
    exact (C_le_lv j).trans Nat.lt_two_pow_self.le

theorem lv_mono {j k : ℕ} (h : j ≤ k) : lv G j ≤ lv G k := by
  induction k with
  | zero => rw [Nat.le_zero.1 h]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (by rw [lv_succ]; exact Nat.lt_two_pow_self.le)
    · rw [Nat.le_antisymm h hge]

theorem exists_le_size_lv (k : ℕ) : ∃ j, k ≤ Nat.size (lv G j) := by
  refine ⟨k, ?_⟩
  have h := Nat.size_le_size (two_pow_le_lv G k)
  rw [Nat.size_pow] at h
  omega

section

variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)

include hS' hsem hb hpoly

/-- The compressed verifier of `𝒱^halt`, the same at every level. -/
noncomputable abbrev W (S' M : Prog) (lam : ℕ) : Verifier 7 :=
  G.output ((Vhalt G U UT S' M lam).sampler.prog, (Vhalt G U UT S' M lam).decider.prog) lam

/-- The first branch fires: `M` halts within `Nat.size n`. -/
def branch1 (M : Prog) (n : ℕ) : Prop := (evalWithin M .nil (Nat.size n)).isSome = true

/-- The second branch fires: the search halts within `Nat.size n`. -/
def branch2 (S' M : Prog) (lam n : ℕ) : Prop :=
  (evalWithin (searchP S' lam (dec G U UT S' M lam)) .nil (Nat.size n)).isSome = true

omit hS' hsem hb hpoly in
theorem branch_mono {p : Prog} {n n' : ℕ} (h : Nat.size n ≤ Nat.size n')
    (hp : (evalWithin p .nil (Nat.size n)).isSome = true) :
    (evalWithin p .nil (Nat.size n')).isSome = true := by
  obtain ⟨r, t, ht, hr⟩ := (evalWithin_isSome_iff _ _ _).1 hp
  exact (evalWithin_isSome_iff _ _ _).2 ⟨r, t, ht.trans h, hr⟩

omit hS' hsem hb hpoly in
theorem branch1_of_halts {M : Prog} (hM : Halts M .nil) :
    ∃ k, ∀ n, k ≤ Nat.size n → branch1 M n := by
  obtain ⟨r, t, hr⟩ := hM
  exact ⟨t, fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r, t, hn, hr⟩⟩

omit hS' hsem hb hpoly in
theorem not_branch1_of_not_halts {M : Prog} (hM : ¬ Halts M .nil) (n : ℕ) : ¬ branch1 M n := by
  intro h
  obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
  exact hM ⟨r, t, hr⟩

/-! ## The acceptance of `𝒱^halt` at a level, by branch -/

omit hS' hsem hb hpoly in
theorem accepts_diag_of_branch1 {n : ℕ} (h1 : branch1 M n)
    (x y : (Vhalt G U UT S' M lam).Questions n) :
    (Vhalt G U UT S' M lam).decider.Accepts n (CL.toBits x) (CL.toBits y) [] [] := by
  unfold branch1 at h1
  rw [accepts_iff, if_pos h1]
  exact ⟨CL.length_toBits _, CL.length_toBits _, trivial⟩

omit hS' hsem hb hpoly in
theorem rejects_all_of_branch2 {n : ℕ} (h1 : ¬ branch1 M n) (h2 : branch2 G U UT S' M lam n)
    (x y a b : BitStr) : ¬ (Vhalt G U UT S' M lam).decider.Accepts n x y a b := by
  unfold branch1 at h1
  unfold branch2 at h2
  rw [accepts_iff, if_neg h1, if_pos h2]
  exact fun h => h.2.2

omit hS' hsem hb hpoly in
theorem accepts_iff_W {n : ℕ} (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (x y a b : BitStr) :
    (Vhalt G U UT S' M lam).decider.Accepts n x y a b ↔
      (W G U UT S' M lam).decider.Accepts n x y a b := by
  unfold branch1 at h1
  unfold branch2 at h2
  rw [accepts_iff, if_neg h1, if_neg h2]
  constructor
  · exact fun h => h.2.2
  · intro h
    have hl := (W G U UT S' M lam).accepts_length n x y a b h
    rw [G.output_sampler] at hl
    exact ⟨hl.1, hl.2, h⟩

omit hS' hsem hb hpoly in
theorem W_sampler : (W G U UT S' M lam).sampler = (Vhalt G U UT S' M lam).sampler :=
  G.output_sampler _ _

omit hS' hsem hb hpoly in
/-- Below the first branch, `𝒱^halt` rejects every answer longer than the compressed bound. -/
theorem rejectsLong_of_not_branch1 {n : ℕ} (h1 : ¬ branch1 M n) :
    (Vhalt G U UT S' M lam).RejectsLong n (G.bound.eval (n + lam)) := by
  intro x y a b hab hacc
  unfold branch1 at h1
  rw [accepts_iff, if_neg h1] at hacc
  split_ifs at hacc with h2
  · exact hacc.2.2
  · exact G.output_rejects_long _ _ _ _ _ _ _ hab hacc.2.2

/-! ## The two classes and the compression steps -/

/-- The class `A` at level `n`: a value-`1` PCC strategy with answers of length at most `n ^ λ`. -/
def A (S' M : Prog) (lam n : ℕ) : Prop := (Vhalt G U UT S' M lam).HasPerfectPCC n (n ^ lam)

/-- The class `B` at level `n`: value at most `1/2` with answers of length at most `n ^ λ`. -/
def B (S' M : Prog) (lam n : ℕ) : Prop := (Vhalt G U UT S' M lam).valStar n (n ^ lam) ≤ 1 / 2

omit hS' hsem hb hpoly in
theorem A_of_branch1 {n : ℕ} (h1 : branch1 M n) : A G U UT S' M lam n :=
  (Vhalt G U UT S' M lam).hasPerfectPCC_of_accepts_diagonal ⟨[], by simp⟩
    (accepts_diag_of_branch1 G U UT M lam h1)

omit hS' hsem hb hpoly in
theorem B_of_branch2 {n : ℕ} (h1 : ¬ branch1 M n) (h2 : branch2 G U UT S' M lam n) :
    B G U UT S' M lam n := by
  unfold B
  rw [(Vhalt G U UT S' M lam).valStar_eq_zero_of_rejects_all
    (rejects_all_of_branch2 G U UT M lam h1 h2)]
  norm_num

omit hS' hsem hpoly in
/-- **Completeness carried down a level**, where neither branch fires. -/
theorem A_step {n : ℕ} (hn : C G ≤ n) (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (hA : A G U UT S' M lam (2 ^ n)) :
    (Vhalt G U UT S' M lam).HasPerfectPCC n (G.bound.eval (n + lam)) := by
  have hW := G.completeness _ lam n hb ((C₀_le_C G).trans hn) hA
  exact ((Vhalt G U UT S' M lam).hasPerfectPCC_congr (W_sampler G U UT M lam)
    (accepts_iff_W G U UT M lam h1 h2)).2 hW

omit hS' hsem in
theorem A_step' {n : ℕ} (hn : C G ≤ n) (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (hA : A G U UT S' M lam (2 ^ n)) : A G U UT S' M lam n :=
  (Vhalt G U UT S' M lam).hasPerfectPCC_of_le (hpoly n ((two_le_C G).trans hn))
    (A_step G U UT M lam hb hn h1 h2 hA)

omit hS' hsem in
/-- **Soundness carried down a level**, where neither branch fires. -/
theorem B_step {n : ℕ} (hn : C G ≤ n) (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (hB : B G U UT S' M lam (2 ^ n)) : B G U UT S' M lam n := by
  have hW := G.soundness _ lam n hb ((C₀_le_C G).trans hn) hB
  have hV : (Vhalt G U UT S' M lam).valStar n (G.bound.eval (n + lam)) ≤ 1 / 2 := by
    rw [(Vhalt G U UT S' M lam).valStar_congr (W_sampler G U UT M lam)
      (accepts_iff_W G U UT M lam h1 h2)]
    exact hW
  unfold B
  rw [(Vhalt G U UT S' M lam).valStar_eq_of_rejects (hpoly n ((two_le_C G).trans hn))
    (rejectsLong_of_not_branch1 G U UT M lam h1)]
  exact hV

/-! ## The search and the start level -/

omit hpoly in
/-- The search halts exactly when the start level has value above `1/2`. -/
theorem halts_search_iff :
    Halts (searchP S' lam (dec G U UT S' M lam)) .nil ↔
      (1 : ℝ) / 2 < (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) := by
  rw [halts_searchP_iff hS', hsem]
  have hb' : (Vof G U (descOf lam (dec G U UT S' M lam))).IsBounded
      (descLam (descOf lam (dec G U UT S' M lam))) := by
    rw [descLam_descOf, ← Vhalt_eq_Vof]; exact hb
  rw [tabL_value G U _ _ hb' (two_le_C G), ansBound, descLam_descOf, ← Vhalt_eq_Vof]

omit hpoly in
theorem branch2_of_lt (h : (1 : ℝ) / 2 <
      (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam))) :
    ∃ k, ∀ n, k ≤ Nat.size n → branch2 G U UT S' M lam n := by
  obtain ⟨r, t, hr⟩ := (halts_search_iff G U UT hS' hsem M lam hb).2 h
  exact ⟨t, fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r, t, hn, hr⟩⟩

omit hpoly in
theorem lt_of_branch2 {n : ℕ} (h2 : branch2 G U UT S' M lam n) :
    (1 : ℝ) / 2 < (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) := by
  rw [← halts_search_iff G U UT hS' hsem M lam hb]
  obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h2
  exact ⟨r, t, hr⟩

omit hS' hsem hb in
/-- The start level is in `B` only if its value is at most `1/2` — with the answer bound of the
statement, once the first branch does not fire there. -/
theorem le_of_B_start (h1 : ¬ branch1 M (C G)) (hB : B G U UT S' M lam (C G)) :
    (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2 := by
  unfold B at hB
  rwa [(Vhalt G U UT S' M lam).valStar_eq_of_rejects (hpoly _ (two_le_C G))
    (rejectsLong_of_not_branch1 G U UT M lam h1)] at hB

/-! ## The two cases -/

omit hS' hsem in
/-- Below a level where the search fires while `M` has not halted, every level of the recursion
is in `B`. -/
theorem B_below (j₀ : ℕ) (hnot : ¬ branch1 M (lv G j₀))
    (hfire : branch2 G U UT S' M lam (lv G j₀)) :
    ∀ i j, j + i = j₀ → B G U UT S' M lam (lv G j) := by
  intro i
  induction i with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj
    subst hj
    exact B_of_branch2 G U UT M lam hnot hfire
  | succ i ih =>
    intro j hj
    have hjle : Nat.size (lv G j) ≤ Nat.size (lv G j₀) :=
      Nat.size_le_size (lv_mono G (by omega))
    have h1 : ¬ branch1 M (lv G j) := fun h => hnot (branch_mono hjle h)
    by_cases h2 : branch2 G U UT S' M lam (lv G j)
    · exact B_of_branch2 G U UT M lam h1 h2
    · have hnext := ih (j + 1) (by omega)
      rw [lv_succ] at hnext
      exact B_step G U UT M lam hb hpoly (C_le_lv G j) h1 h2 hnext

/-- **The halting case**: `𝒱^halt` has a value-`1` PCC strategy at level `C`. -/
theorem hasPerfectPCC_of_halts (hM : Halts M .nil) :
    (Vhalt G U UT S' M lam).HasPerfectPCC (C G) (G.bound.eval (C G + lam)) := by
  obtain ⟨T₀, hT₀⟩ := branch1_of_halts hM
  -- the search never fires while `M` has not halted: it would put the start level in `B`
  have hno2 : ∀ j, ¬ branch1 M (lv G j) → ¬ branch2 G U UT S' M lam (lv G j) := by
    intro j h1 h2
    have hB := B_below G U UT M lam hb hpoly j h1 h2 j 0 (by omega)
    rw [lv_zero] at hB
    have h1C : ¬ branch1 M (C G) := fun h =>
      h1 (branch_mono (Nat.size_le_size (C_le_lv G j)) h)
    exact absurd (lt_of_branch2 G U UT hS' hsem M lam hb h2)
      (not_lt.2 (le_of_B_start G U UT M lam hpoly h1C hB))
  -- from a level where `M` has halted, every level of the recursion is in `A`
  have hA : ∀ k j, T₀ ≤ Nat.size (lv G (j + k)) → A G U UT S' M lam (lv G j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      exact A_of_branch1 G U UT M lam (hT₀ _ hj)
    | succ k ih =>
      intro j hj
      by_cases h1 : branch1 M (lv G j)
      · exact A_of_branch1 G U UT M lam h1
      · have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
        rw [lv_succ] at hnext
        exact A_step' G U UT M lam hb hpoly (C_le_lv G j) h1 (hno2 j h1) hnext
  -- at the start level
  by_cases h1 : branch1 M (C G)
  · exact (Vhalt G U UT S' M lam).hasPerfectPCC_of_accepts_diagonal ⟨[], by simp⟩
      (accepts_diag_of_branch1 G U UT M lam h1)
  · have h2 : ¬ branch2 G U UT S' M lam (C G) := hno2 0 h1
    obtain ⟨k, hk⟩ := exists_le_size_lv G T₀
    have hk' : T₀ ≤ Nat.size (lv G (1 + k)) := by
      rw [show 1 + k = k + 1 by omega, lv_succ]
      exact hk.trans (Nat.size_le_size Nat.lt_two_pow_self.le)
    have hnext := hA k 1 hk'
    rw [lv_succ, lv_zero] at hnext
    exact A_step G U UT M lam hb le_rfl h1 h2 hnext

/-- **The non-halting case**: `val*(𝒱^halt_C) ≤ 1/2`. -/
theorem valStar_le_of_not_halts (hM : ¬ Halts M .nil) :
    (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2 := by
  have hfalse := not_branch1_of_not_halts hM
  by_contra hlt
  obtain ⟨k₁, hk₁⟩ := branch2_of_lt G U UT hS' hsem M lam hb (not_le.1 hlt)
  have hB : ∀ k j, k₁ ≤ Nat.size (lv G (j + k)) → B G U UT S' M lam (lv G j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      exact B_of_branch2 G U UT M lam (hfalse _) (hk₁ _ hj)
    | succ k ih =>
      intro j hj
      by_cases h2 : branch2 G U UT S' M lam (lv G j)
      · exact B_of_branch2 G U UT M lam (hfalse _) h2
      · have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
        rw [lv_succ] at hnext
        exact B_step G U UT M lam hb hpoly (C_le_lv G j) (hfalse _) h2 hnext
  obtain ⟨k, hk⟩ := exists_le_size_lv G k₁
  have hfin := hB k 0 (by simpa using hk)
  rw [lv_zero] at hfin
  exact hlt (le_of_B_start G U UT M lam hpoly (hfalse _) hfin)

end

end MIPRE.Halting

end
