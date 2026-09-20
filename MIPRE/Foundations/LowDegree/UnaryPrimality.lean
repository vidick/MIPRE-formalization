/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.UnaryDegreeArithmetic

/-! # Polynomial-time trial primality for unary degree parameters -/

noncomputable section

namespace MIPRE.LowDegree.DegreeArithmetic

open Cost Cost.PolyTimeFun Polynomial

private theorem tail_empty_iff (u : Unary) : u.tail.isEmpty = true ↔ u.length ≤ 1 := by
  rw [List.isEmpty_iff_length_eq_zero, List.length_tail, Nat.sub_eq_zero_iff_le]

/-- Ignore candidate divisors zero and one, and reject every other actual divisor. -/
def trialCheck (q d : Unary) : Bool := decide (d.length ≤ 1 ∨ ¬d.length ∣ q.length)

private def trialCheckProg : PolyTimeFun (Unary × Unary) Bool :=
  congr (ite (isEmptyProg.comp (tail.comp snd)) (const true)
    (ite (dvdUnaryProg.comp (snd.pair fst)) (const false) (const true)))
    (fun s => trialCheck s.1 s.2) (by
      rintro ⟨q, d⟩
      change (if d.tail.isEmpty then true else if decide (d.length ∣ q.length) then false else true) = _
      by_cases hd : d.length ≤ 1
      · have he := (tail_empty_iff d).mpr hd
        simp [he, trialCheck, hd]
      · have he : d.tail.isEmpty = false := Bool.eq_false_iff.mpr (fun h => hd ((tail_empty_iff d).mp h))
        simp [he, trialCheck, hd])

private abbrev PrimeState := Unary × Bool

private def primeStep (s : PrimeState) (d : Unary) : PrimeState :=
  (s.1, s.2 && trialCheck s.1 d)

private theorem fold_primeStep (ds : List Unary) (q : Unary) (b : Bool) :
    ds.foldl primeStep (q, b) = (q, b && ds.all (trialCheck q)) := by
  induction ds generalizing b with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons]
    change ds.foldl primeStep (q, b && trialCheck q d) = _
    rw [ih, List.all_cons, Bool.and_assoc]

private def primeStepProg : PolyTimeFun (PrimeState × Unary) PrimeState :=
  let q := fst.comp fst
  congr (q.pair (ite (snd.comp fst) (trialCheckProg.comp (q.pair snd)) (const false)))
    (fun s => primeStep s.1 s.2) (by
      rintro ⟨⟨q, b⟩, d⟩
      cases b <;> rfl)

private theorem primeStep_growth (s : PrimeState) (d : Unary) :
    esize (primeStepProg (s, d)) ≤ esize s + (2 : Polynomial ℕ).eval (esize d) := by
  rcases s with ⟨q, b⟩
  change esize (q, b && trialCheck q d) ≤ _
  have hb : esize (b && trialCheck q d) ≤ 3 := by cases b && trialCheck q d <;> decide
  have hb₀ : 1 ≤ esize b := by cases b <;> decide
  simp only [esize_prod, eval_ofNat]
  omega

private def allTrialsProg : PolyTimeFun (List Unary × Unary) Bool :=
  let scan := foldlAdd primeStepProg 2 primeStep_growth
  congr (snd.comp (scan.comp (fst.pair (snd.pair (const true)))))
    (fun s => s.1.all (trialCheck s.2)) (by
      rintro ⟨ds, q⟩
      change (ds.foldl primeStep (q, true)).2 = _
      rw [fold_primeStep]
      rfl)

/-- The raw trial-division predicate. -/
def primeUnary (q : Unary) : Bool :=
  if q.tail.isEmpty then false else (descendingUnary q.tail).all (trialCheck q)

/-- Trial division through all smaller unary candidates is exactly primality. -/
theorem primeUnary_eq (q : Unary) : primeUnary q = decide q.length.Prime := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, Nat.prime_def_lt']
  unfold primeUnary
  by_cases hq : q.length ≤ 1
  · have he : q.tail.isEmpty = true := (tail_empty_iff q).mpr hq
    simp [he]
    omega
  · have he : q.tail.isEmpty = false := by
      exact Bool.eq_false_iff.mpr (fun h => hq ((tail_empty_iff q).mp h))
    simp only [he, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, trialCheck, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨by omega, ?_⟩
      intro m hm hmq
      have hd : unary m ∈ descendingUnary q.tail :=
        (mem_descendingUnary_iff _ _).mpr (by simp; omega)
      have hh := h (unary m) hd
      simp only [length_unary] at hh
      exact hh.resolve_left (by omega)
    · rintro ⟨hq₂, h⟩ d hd
      have hlt := (mem_descendingUnary_iff _ _).mp hd
      simp only [List.length_tail] at hlt
      by_cases hd₁ : d.length ≤ 1
      · exact Or.inl hd₁
      · exact Or.inr (h d.length (by omega) (by omega))

/-- One polynomial-time primality program on every unary input. -/
def primeUnaryProg : PolyTimeFun Unary Bool :=
  congr (ite (isEmptyProg.comp tail) (const false)
    (allTrialsProg.comp ((descendingUnaryProg.comp tail).pair (PolyTimeFun.id _))))
    (fun q => decide q.length.Prime) (by
      intro q
      change primeUnary q = _
      exact primeUnary_eq q)

@[simp] theorem primeUnaryProg_apply (q : Unary) : primeUnaryProg q = decide q.length.Prime := rfl

end MIPRE.LowDegree.DegreeArithmetic

end
