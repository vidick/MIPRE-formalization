/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Reader

/-!
# Capped arithmetic on unary numerals, and indexed lists

Milestone M4 of `planning/universal-machine.md`. The universal machine's program works with
numbers that are small whenever the machine description it decodes is well formed — states,
symbols, table positions are all below the description's length — but that are written in
binary in the description and may be huge when it is not. It therefore computes in *capped*
unary: every number is replaced by its minimum with a cap, which costs nothing on the
well-formed descriptions and keeps every intermediate polynomial on the others. This file
gives the comparisons, the capped product and power, capped conversion from binary digits,
and lookup and update at a unary index.
-/

namespace MIPRE.Cost.PolyTimeFun

open Polynomial

variable {α : Type*} [SizedEncoding α]

/-! ## Tests -/

/-- Whether a list is empty. -/
noncomputable def isNil : PolyTimeFun (List α) Bool :=
  congr ((casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _)))
    (fun l => l.isEmpty) (by intro l; cases l <;> rfl)

@[simp] theorem isNil_apply (l : List α) : isNil l = l.isEmpty := rfl

/-- `a ≤ b` on unary numerals. -/
noncomputable def leU : PolyTimeFun (Unary × Unary) Bool :=
  congr (isNil.comp drop) (fun p => decide (p.1.length ≤ p.2.length)) (by
    rintro ⟨a, b⟩
    simp only [comp_apply, drop_apply, isNil_apply]
    by_cases h : a.length ≤ b.length <;> simp [List.isEmpty_iff, List.drop_eq_nil_iff, h])

@[simp] theorem leU_apply (p : Unary × Unary) :
    leU p = decide (p.1.length ≤ p.2.length) := rfl

/-- `a < b` on unary numerals. -/
noncomputable def ltU : PolyTimeFun (Unary × Unary) Bool :=
  congr (ite (leU.comp (snd.pair fst)) (const false) (const true))
    (fun p => decide (p.1.length < p.2.length)) (by
      rintro ⟨a, b⟩
      show (if decide (b.length ≤ a.length) = true then false else true) =
        decide (a.length < b.length)
      by_cases h : b.length ≤ a.length
      · rw [if_pos (decide_eq_true h)]
        exact (decide_eq_false (by omega)).symm
      · rw [if_neg (by simpa using h)]
        exact (decide_eq_true (by omega)).symm)

@[simp] theorem ltU_apply (p : Unary × Unary) :
    ltU p = decide (p.1.length < p.2.length) := rfl

/-- `a = b` on unary numerals. -/
noncomputable def eqU : PolyTimeFun (Unary × Unary) Bool :=
  congr (ite leU (leU.comp (snd.pair fst)) (const false))
    (fun p => decide (p.1.length = p.2.length)) (by
      rintro ⟨a, b⟩
      show (if decide (a.length ≤ b.length) = true then decide (b.length ≤ a.length)
        else false) = decide (a.length = b.length)
      by_cases h : a.length ≤ b.length
      · rw [if_pos (decide_eq_true h)]
        by_cases h' : b.length ≤ a.length
        · rw [decide_eq_true h', decide_eq_true (by omega)]
        · rw [decide_eq_false h', decide_eq_false (by omega)]
      · rw [if_neg (by simpa using h), decide_eq_false (by omega)])

@[simp] theorem eqU_apply (p : Unary × Unary) :
    eqU p = decide (p.1.length = p.2.length) := rfl

/-! ## Indexed lists -/

/-- The entry at a unary index, or a default. -/
noncomputable def nthU (d : α) : PolyTimeFun (List α × Unary) α :=
  congr ((headD d).comp drop) (fun p => p.1.getD p.2.length d) (by
    rintro ⟨l, u⟩
    simp only [comp_apply, drop_apply, headD_apply]
    rw [List.headD_eq_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_drop]
    simp)

@[simp] theorem nthU_apply (d : α) (p : List α × Unary) : nthU d p = p.1.getD p.2.length d :=
  rfl

/-- Replace the entry at a unary index (appending it past the end). -/
noncomputable def setU : PolyTimeFun (List α × (Unary × α)) (List α) :=
  congr (append.comp ((take.comp (fst.pair (fst.comp snd))).pair
      ((snd.comp snd).cons (drop.comp (fst.pair ((const ()).cons (fst.comp snd)))))))
    (fun p => p.1.take p.2.1.length ++ p.2.2 :: p.1.drop (p.2.1.length + 1)) (by
      rintro ⟨l, u, x⟩
      rfl)

theorem setU_apply_of_lt (p : List α × (Unary × α)) (h : p.2.1.length < p.1.length) :
    setU p = p.1.set p.2.1.length p.2.2 := by
  rw [List.set_eq_take_append_cons_drop, if_pos h]
  rfl

/-! ## Capped arithmetic -/

/-- The minimum with a cap. -/
noncomputable def minU : PolyTimeFun (Unary × Unary) Unary := take

@[simp] theorem minU_apply (p : Unary × Unary) : minU p = unary (min p.1.length p.2.length) := by
  simp only [minU, take_apply]
  rw [← unary_length (p.1.take _), List.length_take, Nat.min_comm]

theorem esize_unary_le_of_length_le {u v : Unary} (h : u.length ≤ v.length) :
    esize u ≤ esize v := by
  rw [← unary_length u, ← unary_length v, esize_unary, esize_unary]
  omega

/-- One step of the capped product: add `b` to the accumulator, capped at `c`. -/
def mulStep (s : Unary × (Unary × Unary)) (_ : Unit) : Unary × (Unary × Unary) :=
  ((s.1 ++ s.2.1).take s.2.2.length, s.2)

/-- The step of the capped product, as a program. -/
noncomputable def mulStepF :
    PolyTimeFun ((Unary × (Unary × Unary)) × Unit) (Unary × (Unary × Unary)) :=
  congr ((take.comp ((append.comp ((fst.comp fst).pair (fst.comp (snd.comp fst)))).pair
      (snd.comp (snd.comp fst)))).pair (snd.comp fst))
    (fun p => mulStep p.1 p.2) (fun _ => rfl)

theorem foldl_mulStep (b c : Unary) :
    ∀ (k : Unary) (acc : Unary), acc.length ≤ c.length →
      (k.foldl mulStep (acc, (b, c))).2 = (b, c) ∧
      (k.foldl mulStep (acc, (b, c))).1.length = min (acc.length + k.length * b.length) c.length
  | [], acc, h => by simp [Nat.min_eq_left h]
  | () :: k, acc, h => by
    rw [List.foldl_cons]
    simp only [mulStep]
    have h' : ((acc ++ b).take c.length).length ≤ c.length := by simp
    obtain ⟨h1, h2⟩ := foldl_mulStep b c k _ h'
    refine ⟨h1, ?_⟩
    rw [h2, List.length_take, List.length_append, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem mulStepF_bounded : FoldBounded mulStepF (2 * X) := by
  intro l s₀ pre xs _
  obtain ⟨acc, b, c⟩ := s₀
  have key : ∀ (k : Unary) (acc : Unary),
      (k.foldl mulStepF.step (acc, (b, c))).2 = (b, c) ∧
      (k.foldl mulStepF.step (acc, (b, c))).1.length ≤ max acc.length c.length := by
    intro k
    induction k with
    | nil => intro acc; simp
    | cons u k ih =>
      intro acc
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih ((acc ++ b).take c.length)
      refine ⟨h1, h2.trans ?_⟩
      simp only [List.length_take]
      omega
  obtain ⟨h1, h2⟩ := key pre acc
  have hs : pre.foldl mulStepF.step (acc, (b, c)) =
      ((pre.foldl mulStepF.step (acc, (b, c))).1, (b, c)) := Prod.ext rfl h1
  rw [hs]
  have he : esize (pre.foldl mulStepF.step (acc, (b, c))).1 ≤ esize acc + esize c := by
    rcases le_max_iff.mp h2 with h | h
    · have := esize_unary_le_of_length_le h; omega
    · have := esize_unary_le_of_length_le h; omega
  simp only [esize_prod, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- **The capped product** `min (a * b) c`. -/
noncomputable def mulCap : PolyTimeFun (Unary × (Unary × Unary)) Unary :=
  congr (fst.comp ((foldl mulStepF (2 * X) mulStepF_bounded).comp
      (fst.pair ((const []).pair snd))))
    (fun p => unary (min (p.1.length * p.2.1.length) p.2.2.length)) (by
      rintro ⟨a, b, c⟩
      show (a.foldl mulStep ([], (b, c))).1 = _
      rw [← unary_length (a.foldl mulStep ([], (b, c))).1,
        (foldl_mulStep b c a [] (by simp)).2]
      simp)

@[simp] theorem mulCap_apply (p : Unary × (Unary × Unary)) :
    mulCap p = unary (min (p.1.length * p.2.1.length) p.2.2.length) := rfl

theorem min_min_mul (x a c : ℕ) : min (min x c * a) c = min (x * a) c := by
  rcases Nat.le_total x c with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · rw [Nat.min_eq_right (Nat.le_mul_of_pos_right c ha),
        Nat.min_eq_right ((Nat.le_mul_of_pos_right c ha).trans (Nat.mul_le_mul_right a h))]

/-- One step of the capped power: multiply by `a`, capped at `c`. -/
def powStep (s : Unary × (Unary × Unary)) (_ : Unit) : Unary × (Unary × Unary) :=
  (unary (min (s.1.length * s.2.1.length) s.2.2.length), s.2)

/-- The step of the capped power, as a program. -/
noncomputable def powStepF :
    PolyTimeFun ((Unary × (Unary × Unary)) × Unit) (Unary × (Unary × Unary)) :=
  congr ((mulCap.comp fst).pair (snd.comp fst)) (fun p => powStep p.1 p.2) (fun _ => rfl)

theorem foldl_powStep (a c : Unary) :
    ∀ (k : Unary) (acc : Unary),
      (k.foldl powStep (acc, (a, c))).2 = (a, c) ∧
      (k.foldl powStep (acc, (a, c))).1 =
        if k = [] then acc else unary (min (acc.length * a.length ^ k.length) c.length)
  | [], acc => by simp
  | () :: k, acc => by
    rw [List.foldl_cons]
    simp only [powStep]
    obtain ⟨h1, h2⟩ := foldl_powStep a c k (unary (min (acc.length * a.length) c.length))
    refine ⟨h1, ?_⟩
    rw [h2]
    simp only [length_unary, List.cons_ne_nil, if_false, List.length_cons]
    split_ifs with hk
    · subst hk; simp
    · rw [min_min_mul, pow_succ]
      congr 2
      ring

theorem powStepF_bounded : FoldBounded powStepF (2 * X) := by
  intro l s₀ pre xs _
  obtain ⟨acc, a, c⟩ := s₀
  obtain ⟨h1, h2⟩ := foldl_powStep a c pre acc
  have h1' : (pre.foldl powStepF.step (acc, (a, c))).2 = (a, c) := h1
  have hs : pre.foldl powStepF.step (acc, (a, c)) =
      ((pre.foldl powStepF.step (acc, (a, c))).1, (a, c)) := Prod.ext rfl h1'
  rw [hs]
  have he : esize (pre.foldl powStepF.step (acc, (a, c))).1 ≤ esize acc + esize c := by
    show esize (pre.foldl powStep (acc, (a, c))).1 ≤ _
    rw [h2]
    split_ifs
    · omega
    · have := esize_unary_le_of_length_le (u := unary (min (acc.length * a.length ^ pre.length)
        c.length)) (v := c) (by simp)
      omega
  simp only [esize_prod, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- **The capped power** `min (a ^ k) c`. -/
noncomputable def powCap : PolyTimeFun (Unary × (Unary × Unary)) Unary :=
  congr (fst.comp ((foldl powStepF (2 * X) powStepF_bounded).comp
      ((fst.comp snd).pair ((minU.comp ((const [()]).pair (snd.comp snd))).pair
        (fst.pair (snd.comp snd))))))
    (fun p => unary (min (p.1.length ^ p.2.1.length) p.2.2.length)) (by
      rintro ⟨a, k, c⟩
      show (k.foldl powStep (([()] : Unary).take c.length, (a, c))).1 = _
      have h1 : ([()] : Unary).take c.length = unary (min 1 c.length) := by
        cases c <;> simp [unary]
      rw [h1, (foldl_powStep a c k _).2]
      split_ifs with hk
      · subst hk; simp
      · simp only [length_unary]
        congr 1
        rcases Nat.eq_zero_or_pos c.length with h | h
        · simp [h]
        · rw [Nat.min_eq_left (show 1 ≤ c.length by omega), one_mul])

@[simp] theorem powCap_apply (p : Unary × (Unary × Unary)) :
    powCap p = unary (min (p.1.length ^ p.2.1.length) p.2.2.length) := rfl

/-! ## Binary digits to capped unary -/

/-- The value of a little-endian digit string (as `Turing.bitsToNat`). -/
def digitsVal (l : List Bool) : ℕ := l.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0

/-- One step of the capped conversion: double and add a digit, capped at `c`. -/
def digitStep (s : Unary × Unary) (b : Bool) : Unary × Unary :=
  ((s.1 ++ s.1 ++ (if b then [()] else [])).take s.2.length, s.2)

/-- The step of the capped conversion, as a program. -/
noncomputable def digitStepF : PolyTimeFun ((Unary × Unary) × Bool) (Unary × Unary) :=
  congr ((take.comp ((append.comp ((append.comp ((fst.comp fst).pair (fst.comp fst))).pair
      (ite snd (const [()]) (const [])))).pair (snd.comp fst))).pair (snd.comp fst))
    (fun p => digitStep p.1 p.2) (by
      rintro ⟨⟨acc, c⟩, b⟩
      cases b <;> rfl)

theorem min_two_mul_add (x e c : ℕ) : min (2 * min x c + e) c = min (2 * x + e) c := by
  rcases Nat.le_total x c with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

theorem foldr_digitStep (c : Unary) :
    ∀ l : List Bool, (l.foldr (fun b s => digitStep s b) ([], c)).2 = c ∧
      (l.foldr (fun b s => digitStep s b) ([], c)).1.length = min (digitsVal l) c.length
  | [] => by simp [digitsVal]
  | b :: l => by
    obtain ⟨h1, h2⟩ := foldr_digitStep c l
    rw [List.foldr_cons]
    generalize l.foldr (fun b s => digitStep s b) ([], c) = s at h1 h2 ⊢
    obtain ⟨acc, c'⟩ := s
    simp only at h1 h2
    subst h1
    refine ⟨rfl, ?_⟩
    simp only [digitStep, List.length_take, List.length_append, h2, digitsVal, List.foldr_cons]
    have := min_two_mul_add (digitsVal l) (if b then 1 else 0) c'.length
    simp only [digitsVal] at this
    cases b <;> simp_all <;> omega

theorem digitStepF_bounded : FoldBounded digitStepF (2 * X) := by
  intro l s₀ pre xs _
  obtain ⟨acc, c⟩ := s₀
  have key : ∀ (k : List Bool) (acc : Unary),
      (k.foldl digitStepF.step (acc, c)).2 = c ∧
      (k.foldl digitStepF.step (acc, c)).1.length ≤ max acc.length c.length := by
    intro k
    induction k with
    | nil => intro acc; simp
    | cons b k ih =>
      intro acc
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih ((acc ++ acc ++ (if b then [()] else [])).take c.length)
      refine ⟨h1, h2.trans ?_⟩
      simp only [List.length_take]
      omega
  obtain ⟨h1, h2⟩ := key pre acc
  have hs : pre.foldl digitStepF.step (acc, c) = ((pre.foldl digitStepF.step (acc, c)).1, c) :=
    Prod.ext rfl h1
  rw [hs]
  have he : esize (pre.foldl digitStepF.step (acc, c)).1 ≤ esize acc + esize c := by
    rcases le_max_iff.mp h2 with h | h
    · have := esize_unary_le_of_length_le h; omega
    · have := esize_unary_le_of_length_le h; omega
  simp only [esize_prod, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

/-- **Capped conversion of little-endian binary digits** to unary: `min (value l) c`. -/
noncomputable def digitsCap : PolyTimeFun (List Bool × Unary) Unary :=
  congr (fst.comp ((foldl digitStepF (2 * X) digitStepF_bounded).comp
      ((reverse.comp fst).pair ((const []).pair snd))))
    (fun p => unary (min (digitsVal p.1) p.2.length)) (by
      rintro ⟨l, c⟩
      show (l.reverse.foldl digitStep ([], c)).1 = _
      rw [List.foldl_reverse, ← unary_length (l.foldr (fun b s => digitStep s b) ([], c)).1,
        (foldr_digitStep c l).2])

@[simp] theorem digitsCap_apply (p : List Bool × Unary) :
    digitsCap p = unary (min (digitsVal p.1) p.2.length) := rfl

end MIPRE.Cost.PolyTimeFun
