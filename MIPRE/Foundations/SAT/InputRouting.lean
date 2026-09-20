/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Tseitin

/-!
# Routing repeated input reads through their preceding copies

`Circuit.WellFormed` bounds gate fan-out, but permits arbitrarily many gates to
read the same external input. For bounded-degree consistency polynomials, the
first such gate reads the external variable and each later one reads the
preceding input gate's variable. This changes neither the variables nor the
Boolean gate values. Each variable supplies at most one of these copy links.
-/

namespace MIPRE.SAT.Circuit

/-- One plus the last gate reading input `i` before gate `k`, or zero if none. -/
def inputOwner (C : Circuit) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, i => if C.gates.getD k (.const false) = .input i then k + 1 else inputOwner C k i

theorem inputOwner_le (C : Circuit) (k i : ℕ) : C.inputOwner k i ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [inputOwner]; split <;> omega

theorem inputOwner_mono (C : Circuit) (i : ℕ) : Monotone (fun k => C.inputOwner k i) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [inputOwner]
  split
  · have := inputOwner_le C k i; omega
  · exact le_rfl

theorem inputOwner_spec (C : Circuit) (k i : ℕ) (h : C.inputOwner k i ≠ 0) :
    C.gates.getD (C.inputOwner k i - 1) (.const false) = .input i := by
  induction k with
  | zero => exact False.elim (h rfl)
  | succ k ih =>
    by_cases hg : C.gates.getD k (.const false) = .input i
    · simp only [inputOwner, if_pos hg, Nat.add_sub_cancel]
      exact hg
    · simp only [inputOwner, if_neg hg] at h ⊢
      exact ih h

theorem inputOwner_after (C : Circuit) {a b i : ℕ} (hab : a < b)
    (ha : C.gates.getD a (.const false) = .input i) : a + 1 ≤ C.inputOwner b i := by
  have h := inputOwner_mono C i (show a + 1 ≤ b by omega)
  change C.inputOwner (a + 1) i ≤ C.inputOwner b i at h
  rw [inputOwner, if_pos ha] at h
  exact h

/-- The input-copy link: external input on the first read, previous gate thereafter. -/
def inputRef (C : Circuit) (k i : ℕ) : ℕ ⊕ ℕ :=
  if C.inputOwner k i = 0 then .inl i else .inr (C.inputOwner k i - 1)

private theorem inputRef_ne_of_lt (C : Circuit) {a b i j : ℕ} (hab : a < b)
    (ha : C.gates.getD a (.const false) = .input i)
    (he : C.inputRef a i = C.inputRef b j) : False := by
  by_cases h₁ : C.inputOwner a i = 0 <;> by_cases h₂ : C.inputOwner b j = 0
  · simp only [inputRef, h₁, h₂, if_true, Sum.inl.injEq] at he
    subst j
    have := inputOwner_after C hab ha
    omega
  · simp [inputRef, h₁, h₂] at he
  · simp [inputRef, h₁, h₂] at he
  · simp only [inputRef, h₁, h₂, if_false, Sum.inr.injEq] at he
    have howner : C.inputOwner a i = C.inputOwner b j := by omega
    have hi := inputOwner_spec C a i h₁
    have hj := inputOwner_spec C b j h₂
    rw [howner, hj] at hi
    have hij : i = j := by injection hi with h; exact h.symm
    subst j
    have hl := inputOwner_le C a i
    have hr := inputOwner_after C hab ha
    omega

/-- Each external input or previous input gate is used by at most one copy link. -/
theorem inputRef_injective (C : Circuit) {a b i j : ℕ}
    (ha : C.gates.getD a (.const false) = .input i)
    (hb : C.gates.getD b (.const false) = .input j)
    (he : C.inputRef a i = C.inputRef b j) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim (inputRef_ne_of_lt C h ha he)
  · exact h
  · exact False.elim (inputRef_ne_of_lt C h hb he.symm)

/-- A copy link points to an input variable or to a strictly earlier gate. -/
theorem inputRef_cases (C : Circuit) (k i : ℕ) :
    C.inputRef k i = .inl i ∨
      ∃ u < k, C.inputRef k i = .inr u ∧ C.gates.getD u (.const false) = .input i := by
  by_cases h : C.inputOwner k i = 0
  · exact Or.inl (by simp [inputRef, h])
  · refine Or.inr ⟨C.inputOwner k i - 1, ?_, ?_, inputOwner_spec C k i h⟩
    · have := inputOwner_le C k i; omega
    · simp [inputRef, h]

/-- Consistency equations after replacing repeated external reads by copy links. -/
def RoutedConsistent (C : Circuit) (x w : ℕ → Bool) : Prop :=
  ∀ k < C.size, w k = (C.gates.getD k (.const false)).eval
    (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)

private theorem inputRef_value (C : Circuit) (x w : ℕ → Bool) (k i : ℕ)
    (hw : ∀ u < k, w u = C.valueAt x u) : Sum.elim x w (C.inputRef k i) = x i := by
  rcases inputRef_cases C k i with he | ⟨u, hu, he, hg⟩
  · rw [he]; rfl
  · rw [he]
    change w u = x i
    rw [hw u hu, valueAt_eq, hg]
    rfl

/-- Routing imposes exactly the original gate values on all the same variables. -/
theorem routedConsistent_iff (C : Circuit) (x w : ℕ → Bool) :
    C.RoutedConsistent x w ↔ ∀ k < C.size, w k = C.valueAt x k := by
  constructor
  · intro hc k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hw : ∀ u < k, w u = C.valueAt x u := fun u hu => ih u hu (by omega)
      have hi : (fun i => Sum.elim x w (C.inputRef k i)) = x :=
        funext (inputRef_value C x w k · hw)
      have hv : (List.ofFn fun j : Fin k => w j) =
          (List.ofFn fun j : Fin k => C.valueAt x j) := by
        congr 1
        funext j
        exact hw j j.isLt
      rw [hc k hk, hi, hv, valueAt_eq]
  · intro hw k hk
    have hprev : ∀ u < k, w u = C.valueAt x u := fun u hu => hw u (by omega)
    have hi : (fun i => Sum.elim x w (C.inputRef k i)) = x :=
      funext (inputRef_value C x w k · hprev)
    have hv : (List.ofFn fun j : Fin k => w j) =
        (List.ofFn fun j : Fin k => C.valueAt x j) := by
      congr 1
      funext j
      exact hprev j j.isLt
    rw [hi, hv, hw k hk, valueAt_eq]

/-- The routed consistency equations and the output literal characterize
acceptance, using exactly the original input and gate variables. -/
theorem eval_iff_routedConsistent (C : Circuit) (hne : C.gates ≠ []) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ w, C.RoutedConsistent x w ∧ w (C.size - 1) = true := by
  have hsize : 0 < C.size := List.length_pos_iff.mpr hne
  constructor
  · intro h
    refine ⟨C.valueAt x, (routedConsistent_iff C x _).mpr (by simp), ?_⟩
    simpa [Circuit.eval, hne, size] using h
  · rintro ⟨w, hw, ho⟩
    have hvals := (routedConsistent_iff C x w).mp hw
    rw [hvals _ (by omega)] at ho
    simpa [Circuit.eval, hne, size] using ho

end MIPRE.SAT.Circuit
