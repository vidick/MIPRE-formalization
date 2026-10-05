/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Halting.Decider

@[expose] public section

/-!
# The tailored halting verifier: the values at level `C`

Paper II, II:2021–2066 (the main theorem from compression), along the route of
`MIPRE/Foundations/Halting/Paper/Induction.lean`, which this file parallels: for a machine `M`
and a parameter `λ` such that `V^{M,λ}` is `λ`-bounded,

* if `M` halts on the empty input, `V^{M,λ}` has a perfect ZPC strategy at level `C`;
* if it does not, `val*(V^{M,λ}_C) ≤ 1/2`;

with `C = max C₀ 2`. The argument runs along the levels `C, 2 ^ C, 2 ^ (2 ^ C), …` of the
recursion (`lv`). The two classes are `A n`, a perfect ZPC strategy at level `n`, and `B n`,
value at most `1/2` there. `TailoredGapCompression.completeness` and `soundness` carry
`A (2 ^ n) → A n` and `B (2 ^ n) → B n` at every level where neither of the processor's first
two branches fires (`lem:dhalt-values`); branch 1 puts a level in `A` outright and branch 2 in
`B`; and the search halts exactly when the start level has value above `1/2`, which rules the
search out below the level where `M` halts, and the start level out of `B`'s complement when
`M` does not.

Unlike the existing halting layer, there is no answer bound to carry along: the answers of a
tailored game have the lengths its answer-length calculator gives them.

The search program is a parameter, with its specification `SearchSpec`: on the description of a
`λ`-bounded tailored verifier `(S^λ, L^λ, P)` it halts exactly when the value at level `C`
exceeds `1/2`. A program meeting it comes from tabulating a tailored verifier at a fixed level,
the next part of the plan.
-/

namespace MIPRE.Tailored.Halting

open Cost Cost.Prog

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ) (U : UniversalMachine)
  (UT : ClockedUniversalMachine)

/-! ## The levels -/

/-- The level the reduction outputs: `max C₀ 2`, so that the time clauses of `IsBounded` apply
there. -/
def C : ℕ := max TG.C₀ 2

theorem two_le_C : 2 ≤ C TG := le_max_right _ _

theorem C₀_le_C : TG.C₀ ≤ C TG := le_max_left _ _

/-- The levels of the recursion started at `C`: `C, 2 ^ C, 2 ^ (2 ^ C), …`. -/
def lv : ℕ → ℕ
  | 0 => C TG
  | j + 1 => 2 ^ lv j

@[simp] theorem lv_zero : lv TG 0 = C TG := rfl

@[simp] theorem lv_succ (j : ℕ) : lv TG (j + 1) = 2 ^ lv TG j := rfl

theorem two_pow_le_lv : ∀ j, 2 ^ j ≤ lv TG j
  | 0 => (Nat.pow_le_pow_right two_pos (Nat.zero_le 1)).trans (two_le_C TG)
  | j + 1 => by
    rw [lv_succ, pow_succ]
    have h := two_pow_le_lv j
    have h2 : 2 ^ j * 2 ≤ 2 ^ 2 ^ j := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right two_pos Nat.lt_two_pow_self
    exact h2.trans (Nat.pow_le_pow_right two_pos h)

theorem C_le_lv : ∀ j, C TG ≤ lv TG j
  | 0 => le_rfl
  | j + 1 => by
    rw [lv_succ]
    exact (C_le_lv j).trans Nat.lt_two_pow_self.le

theorem lv_mono {j k : ℕ} (h : j ≤ k) : lv TG j ≤ lv TG k := by
  induction k with
  | zero => rw [Nat.le_zero.1 h]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (by rw [lv_succ]; exact Nat.lt_two_pow_self.le)
    · rw [Nat.le_antisymm h hge]

theorem exists_le_size_lv (k : ℕ) : ∃ j, k ≤ Nat.size (lv TG j) := by
  refine ⟨k, ?_⟩
  have h := Nat.size_le_size (two_pow_le_lv TG k)
  rw [Nat.size_pow] at h
  omega

/-! ## The branches along the levels -/

theorem branch_mono {p : Prog} {n n' : ℕ} (h : Nat.size n ≤ Nat.size n')
    (hp : (evalWithin p .nil (Nat.size n)).isSome = true) :
    (evalWithin p .nil (Nat.size n')).isSome = true := by
  obtain ⟨r, t, ht, hr⟩ := (evalWithin_isSome_iff _ _ _).1 hp
  exact (evalWithin_isSome_iff _ _ _).2 ⟨r, t, ht.trans h, hr⟩

theorem branch1_of_halts {M : Prog} (hM : Halts M .nil) :
    ∃ k, ∀ n, k ≤ Nat.size n → branch1 M n := by
  obtain ⟨r, t, hr⟩ := hM
  exact ⟨t, fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r, t, hn, hr⟩⟩

theorem not_branch1_of_not_halts {M : Prog} (hM : ¬ Halts M .nil) (n : ℕ) : ¬ branch1 M n := by
  intro h
  obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
  exact hM ⟨r, t, hr⟩

/-! ## The search -/

/-- The tailored verifier `(S^λ, L^λ, P)` that a parameter and a processor describe. -/
def vof (lam : ℕ) (P : Decider) : TailoredVerifier ℓ := ⟨TG.sampler lam, TG.len lam, P⟩

theorem Vhalt_eq_vof (S' M : Prog) (lam : ℕ) :
    Vhalt TG U UT S' M lam = vof TG lam (lp TG U UT S' M lam) := rfl

/-- **The specification of the search program** at the level `m`: on the description
`descOf λ P` of a `λ`-bounded tailored verifier `(S^λ, L^λ, P)`, it halts exactly when the value
at level `m` exceeds `1/2`. -/
def SearchSpec (S' : Prog) (m : ℕ) : Prop :=
  ∀ (lam : ℕ) (P : Decider), (vof TG lam P).IsBounded lam →
    (Halts S' (encode (MIPRE.Halting.descOf lam P.prog)) ↔
      (1 : ℝ) / 2 < (vof TG lam P).valStar m)

/-! ## The two classes -/

/-- The class `A` at level `n`: a perfect ZPC strategy. -/
def A (S' M : Prog) (lam n : ℕ) : Prop := (Vhalt TG U UT S' M lam).HasPerfectZPC n

/-- The class `B` at level `n`: value at most `1/2`. -/
def B (S' M : Prog) (lam n : ℕ) : Prop := (Vhalt TG U UT S' M lam).valStar n ≤ 1 / 2

theorem A_of_branch1 {S' M : Prog} {lam n : ℕ} (h1 : branch1 M n) : A TG U UT S' M lam n :=
  hasPerfectZPC_of_branch1 TG U UT S' M lam h1

theorem B_of_branch2 {S' M : Prog} {lam n : ℕ} (h1 : ¬ branch1 M n)
    (h2 : branch2 TG U UT S' M lam n) : B TG U UT S' M lam n := by
  unfold B
  rw [valStar_eq_zero_of_branch2 TG U UT S' M lam h1 h2]
  norm_num

section

variable {S' : Prog} {M : Prog} {lam : ℕ} (hb : (Vhalt TG U UT S' M lam).IsBounded lam)
include hb

/-- **Completeness carried down a level**, where neither branch fires. -/
theorem A_step {n : ℕ} (hn : C TG ≤ n) (h1 : ¬ branch1 M n) (h2 : ¬ branch2 TG U UT S' M lam n)
    (hA : A TG U UT S' M lam (2 ^ n)) : A TG U UT S' M lam n :=
  (hasPerfectZPC_iff_W TG U UT S' M lam h1 h2).2
    (TG.completeness _ lam n hb ((C₀_le_C TG).trans hn) hA)

/-- **Soundness carried down a level**, where neither branch fires. -/
theorem B_step {n : ℕ} (hn : C TG ≤ n) (h1 : ¬ branch1 M n) (h2 : ¬ branch2 TG U UT S' M lam n)
    (hB : B TG U UT S' M lam (2 ^ n)) : B TG U UT S' M lam n := by
  unfold B
  rw [valStar_eq_W TG U UT S' M lam h1 h2]
  exact TG.soundness _ lam n hb ((C₀_le_C TG).trans hn) hB

/-- Below a level where the search fires while `M` has not halted, every level of the recursion
is in `B`. -/
theorem B_below (j₀ : ℕ) (hnot : ¬ branch1 M (lv TG j₀))
    (hfire : branch2 TG U UT S' M lam (lv TG j₀)) :
    ∀ i j, j + i = j₀ → B TG U UT S' M lam (lv TG j) := by
  intro i
  induction i with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj
    subst hj
    exact B_of_branch2 TG U UT hnot hfire
  | succ i ih =>
    intro j hj
    have hjle : Nat.size (lv TG j) ≤ Nat.size (lv TG j₀) :=
      Nat.size_le_size (lv_mono TG (by omega))
    have h1 : ¬ branch1 M (lv TG j) := fun h => hnot (branch_mono hjle h)
    by_cases h2 : branch2 TG U UT S' M lam (lv TG j)
    · exact B_of_branch2 TG U UT h1 h2
    · have hnext := ih (j + 1) (by omega)
      rw [lv_succ] at hnext
      exact B_step TG U UT hb (C_le_lv TG j) h1 h2 hnext

variable (hS' : S'.WellScoped 1) (hsem : SearchSpec TG S' (C TG))
include hS' hsem

/-- The search halts exactly when the start level has value above `1/2`. -/
theorem halts_search_iff :
    Halts (MIPRE.Halting.searchP S' lam (lpProg TG U UT S' M lam)) .nil ↔
      (1 : ℝ) / 2 < (Vhalt TG U UT S' M lam).valStar (C TG) := by
  rw [MIPRE.Halting.halts_searchP_iff hS']
  exact hsem lam (lp TG U UT S' M lam) hb

theorem branch2_of_lt (h : (1 : ℝ) / 2 < (Vhalt TG U UT S' M lam).valStar (C TG)) :
    ∃ k, ∀ n, k ≤ Nat.size n → branch2 TG U UT S' M lam n := by
  obtain ⟨r, t, hr⟩ := (halts_search_iff TG U UT hb hS' hsem).2 h
  exact ⟨t, fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r, t, hn, hr⟩⟩

theorem lt_of_branch2 {n : ℕ} (h2 : branch2 TG U UT S' M lam n) :
    (1 : ℝ) / 2 < (Vhalt TG U UT S' M lam).valStar (C TG) := by
  rw [← halts_search_iff TG U UT hb hS' hsem]
  obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h2
  exact ⟨r, t, hr⟩

/-! ## The two cases -/

/-- **The halting case**: `V^{M,λ}` has a perfect ZPC strategy at level `C`. -/
theorem hasPerfectZPC_of_halts (hM : Halts M .nil) :
    (Vhalt TG U UT S' M lam).HasPerfectZPC (C TG) := by
  obtain ⟨T₀, hT₀⟩ := branch1_of_halts hM
  -- the search never fires while `M` has not halted: it would put the start level in `B`
  have hno2 : ∀ j, ¬ branch1 M (lv TG j) → ¬ branch2 TG U UT S' M lam (lv TG j) := by
    intro j h1 h2
    have hB := B_below TG U UT hb j h1 h2 j 0 (by omega)
    rw [lv_zero] at hB
    exact absurd (lt_of_branch2 TG U UT hb hS' hsem h2) (not_lt.2 hB)
  -- from a level where `M` has halted, every level of the recursion is in `A`
  have hA : ∀ k j, T₀ ≤ Nat.size (lv TG (j + k)) → A TG U UT S' M lam (lv TG j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      exact A_of_branch1 TG U UT (hT₀ _ hj)
    | succ k ih =>
      intro j hj
      by_cases h1 : branch1 M (lv TG j)
      · exact A_of_branch1 TG U UT h1
      · have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
        rw [lv_succ] at hnext
        exact A_step TG U UT hb (C_le_lv TG j) h1 (hno2 j h1) hnext
  obtain ⟨k, hk⟩ := exists_le_size_lv TG T₀
  have hfin := hA k 0 (by simpa using hk)
  rwa [lv_zero] at hfin

/-- **The non-halting case**: `val*(V^{M,λ}_C) ≤ 1/2`. -/
theorem valStar_le_of_not_halts (hM : ¬ Halts M .nil) :
    (Vhalt TG U UT S' M lam).valStar (C TG) ≤ 1 / 2 := by
  have hfalse := not_branch1_of_not_halts hM
  by_contra hlt
  obtain ⟨k₁, hk₁⟩ := branch2_of_lt TG U UT hb hS' hsem (not_le.1 hlt)
  have hB : ∀ k j, k₁ ≤ Nat.size (lv TG (j + k)) → B TG U UT S' M lam (lv TG j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      exact B_of_branch2 TG U UT (hfalse _) (hk₁ _ hj)
    | succ k ih =>
      intro j hj
      by_cases h2 : branch2 TG U UT S' M lam (lv TG j)
      · exact B_of_branch2 TG U UT (hfalse _) h2
      · have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
        rw [lv_succ] at hnext
        exact B_step TG U UT hb (C_le_lv TG j) (hfalse _) h2 hnext
  obtain ⟨k, hk⟩ := exists_le_size_lv TG k₁
  have hfin := hB k 0 (by simpa using hk)
  rw [lv_zero] at hfin
  exact hlt hfin

end

end MIPRE.Tailored.Halting

end
