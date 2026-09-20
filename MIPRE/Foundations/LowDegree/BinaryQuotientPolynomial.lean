/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryOrbitDescent

/-! # Polynomial arithmetic with supplied binary-quotient coefficient vectors -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

/-- Add coefficient lists, keeping unmatched final coefficients. -/
def addCoeffLists : List BitStr → List BitStr → List BitStr
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => xorBits a b :: addCoeffLists as bs

@[simp] theorem addCoeffLists_nil_right (as : List BitStr) : addCoeffLists as [] = as := by
  cases as <;> rfl

@[simp] theorem length_addCoeffLists (as bs : List BitStr) :
    (addCoeffLists as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [addCoeffLists]
  | cons a as ih =>
    cases bs <;> simp [addCoeffLists, ih, Nat.succ_max_succ]

/-- Addition keeps all correctly sized coefficients correctly sized. -/
theorem addCoeffLists_width (as bs : List BitStr) (n : ℕ)
    (ha : ∀ a ∈ as, a.length = n) (hb : ∀ b ∈ bs, b.length = n) :
    ∀ c ∈ addCoeffLists as bs, c.length = n := by
  induction as generalizing bs with
  | nil => exact hb
  | cons a as ih =>
    cases bs with
    | nil => exact ha
    | cons b bs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [ha a (by simp), hb b (by simp)]
      · exact ih bs (fun d hd => ha d (by simp [hd])) (fun d hd => hb d (by simp [hd])) c hc

/-- Addition cannot exceed a common bound on the input coefficient widths. -/
theorem addCoeffLists_width_le (as bs : List BitStr) (n : ℕ)
    (ha : ∀ a ∈ as, a.length ≤ n) (hb : ∀ b ∈ bs, b.length ≤ n) :
    ∀ c ∈ addCoeffLists as bs, c.length ≤ n := by
  induction as generalizing bs with
  | nil => exact hb
  | cons a as ih =>
    cases bs with
    | nil => exact ha
    | cons b bs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (by rw [length_xorBits]; exact (min_le_left _ _).trans (ha a (by simp)))
      · exact ih bs (fun d hd => ha d (by simp [hd])) (fun d hd => hb d (by simp [hd])) c hc

variable {R : Type*} [CommRing R]

/-- Coefficient-list addition implements addition of the interpreted polynomials. -/
theorem coeffPolynomial_addCoeffLists [CharP R 2] (z : R) (as bs : List BitStr) (n : ℕ)
    (ha : ∀ a ∈ as, a.length = n) (hb : ∀ b ∈ bs, b.length = n) :
    coeffPolynomial z (addCoeffLists as bs) = coeffPolynomial z as + coeffPolynomial z bs := by
  induction as generalizing bs with
  | nil => simp [addCoeffLists]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffLists]
    | cons b bs =>
      rw [addCoeffLists, coeffPolynomial_cons,
        evalBits_xor z a b ((ha a (by simp)).trans (hb b (by simp)).symm),
        ih bs (fun d hd => ha d (by simp [hd])) (fun d hd => hb d (by simp [hd]))]
      simp only [coeffPolynomial_cons, map_add]
      ring

private abbrev AddState := List BitStr × List BitStr

private def addStep (s : AddState) (a : BitStr) : AddState :=
  match s.1 with
  | [] => ([], a :: s.2)
  | b :: bs => (bs, xorBits a b :: s.2)

private def finishAdd (s : AddState) : List BitStr := s.2.reverse ++ s.1

private theorem finishAdd_fold (as bs acc : List BitStr) :
    finishAdd (as.foldl addStep (bs, acc)) = acc.reverse ++ addCoeffLists as bs := by
  induction as generalizing bs acc with
  | nil => rfl
  | cons a as ih =>
    cases bs with
    | nil =>
      rw [List.foldl_cons]
      change finishAdd (as.foldl addStep ([], a :: acc)) = _
      rw [ih]
      simp [addCoeffLists, List.append_assoc]
    | cons b bs =>
      rw [List.foldl_cons]
      change finishAdd (as.foldl addStep (bs, xorBits a b :: acc)) = _
      rw [ih]
      simp [addCoeffLists, List.append_assoc]

private def addStepProg : PolyTimeFun (AddState × BitStr) AddState :=
  let nilCase : PolyTimeFun (AddState × BitStr) AddState :=
    (const []).pair (cons snd (snd.comp fst))
  let consCase : PolyTimeFun ((AddState × BitStr) × (BitStr × List BitStr)) AddState :=
    (snd.comp snd).pair
      (cons (xorBitsProg.comp ((snd.comp fst).pair (fst.comp snd)))
        (snd.comp (fst.comp fst)))
  (casesList nilCase consCase).comp ((PolyTimeFun.id _).pair (fst.comp fst))

private theorem addStepProg_apply (s : AddState) (a : BitStr) :
    addStepProg (s, a) = addStep s a := by
  rcases s with ⟨bs, acc⟩
  cases bs <;> rfl

private theorem addStep_growth (s : AddState) (a : BitStr) :
    esize (addStepProg (s, a)) ≤ esize s + (5 * X + 5 : Polynomial ℕ).eval (esize a) := by
  rw [addStepProg_apply]
  rcases s with ⟨bs, acc⟩
  cases bs with
  | nil => simp [addStep, esize_prod, esize_list_cons]; omega
  | cons b bs =>
    have hw : (xorBits a b).length ≤ a.length := by rw [length_xorBits]; exact min_le_left _ _
    have hs := esize_bitStr_le (xorBits a b)
    have ha := length_le_esize_bitStr a
    simp only [addStep, esize_prod, esize_list_cons, eval_add, eval_mul, eval_ofNat, eval_X]
    omega

/-- One globally polynomial-time coefficient addition program. -/
def addCoeffListsProg : PolyTimeFun (List BitStr × List BitStr) (List BitStr) :=
  let scan := foldl addStepProg (X + X * (5 * X + 5))
    (foldBounded_of_additive addStepProg (5 * X + 5) addStep_growth)
  congr (append.comp ((reverse.comp (snd.comp (scan.comp (fst.pair (snd.pair (const [])))))).pair
    (fst.comp (scan.comp (fst.pair (snd.pair (const [])))))))
    (fun q => addCoeffLists q.1 q.2) (by
      rintro ⟨as, bs⟩
      have hstep : addStepProg.step = addStep := by
        funext s a
        exact addStepProg_apply s a
      change finishAdd (as.foldl addStepProg.step (bs, [])) = _
      rw [hstep]
      exact finishAdd_fold as bs [])

@[simp] theorem addCoeffListsProg_apply (as bs : List BitStr) :
    addCoeffListsProg (as, bs) = addCoeffLists as bs := rfl


/-- Horner multiplication of two polynomial coefficient lists. -/
def mulCoeffLists (p : BitStr) : List BitStr → List BitStr → List BitStr
  | [], _ => []
  | a :: as, bs => addCoeffLists (bs.map (mulReduce p a)) (zeroBits p :: mulCoeffLists p as bs)

/-- Each multiplication output has at most the sum of the input coefficient counts. -/
theorem length_mulCoeffLists_le (p : BitStr) (as bs : List BitStr) :
    (mulCoeffLists p as bs).length ≤ as.length + bs.length := by
  induction as with
  | nil => simp [mulCoeffLists]
  | cons a as ih =>
    simp only [mulCoeffLists, length_addCoeffLists, List.length_map, List.length_cons]
    omega

/-- Multiplication preserves valid quotient coefficient widths. -/
theorem mulCoeffLists_width (p : BitStr) (as bs : List BitStr)
    (ha : ∀ a ∈ as, a.length = p.length) :
    ∀ c ∈ mulCoeffLists p as bs, c.length = p.length := by
  induction as with
  | nil => simp [mulCoeffLists]
  | cons a as ih =>
    apply addCoeffLists_width
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact length_mulReduce _ _ _ (ha a (by simp))
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact length_zeroBits p
      · exact ih (fun d hd => ha d (by simp [hd])) c hc

/-- Scalar multiplication has the expected polynomial interpretation. -/
theorem coeffPolynomial_scale [CharP R 2] (z : R) (p a : BitStr) (bs : List BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    coeffPolynomial z (bs.map (mulReduce p a)) = C (evalBits z a) * coeffPolynomial z bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, coeffPolynomial_cons, evalBits_mulReduce z p a b ha hz, ih, map_mul]
    ring

/-- Horner multiplication agrees with multiplication of the interpreted polynomials. -/
theorem coeffPolynomial_mulCoeffLists [CharP R 2] (z : R) (p : BitStr) (as bs : List BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : ∀ a ∈ as, a.length = p.length) :
    coeffPolynomial z (mulCoeffLists p as bs) = coeffPolynomial z as * coeffPolynomial z bs := by
  induction as with
  | nil => simp [mulCoeffLists]
  | cons a as ih =>
    have ha₀ := ha a (by simp)
    have ha₁ : ∀ b ∈ as, b.length = p.length := fun b hb => ha b (by simp [hb])
    rw [mulCoeffLists, coeffPolynomial_addCoeffLists z _ _ p.length]
    · rw [coeffPolynomial_scale z p a bs hz ha₀, coeffPolynomial_cons, evalBits_zeroBits,
        map_zero, zero_add, ih ha₁, coeffPolynomial_cons]
      ring
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact length_mulReduce _ _ _ ha₀
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact length_zeroBits p
      · exact mulCoeffLists_width p as bs ha₁ c hc

private abbrev MulState := BitStr × List BitStr × List BitStr

private def mulStep (s : MulState) (a : BitStr) : MulState :=
  (s.1, s.2.1, addCoeffLists (s.2.1.map (mulReduce s.1 a)) (zeroBits s.1 :: s.2.2))

private theorem fold_mulStep_shape (pre : List BitStr) (p : BitStr) (bs cs : List BitStr) :
    (pre.foldl mulStep (p, bs, cs)).1 = p ∧ (pre.foldl mulStep (p, bs, cs)).2.1 = bs ∧
      (pre.foldl mulStep (p, bs, cs)).2.2.length ≤ max bs.length cs.length + pre.length := by
  induction pre generalizing cs with
  | nil => exact ⟨rfl, rfl, by simp⟩
  | cons a pre ih =>
    have h := ih (addCoeffLists (bs.map (mulReduce p a)) (zeroBits p :: cs))
    refine ⟨h.1, h.2.1, ?_⟩
    simp only [length_addCoeffLists, List.length_map, List.length_cons] at h
    change (pre.foldl mulStep (p, bs, addCoeffLists (bs.map (mulReduce p a))
      (zeroBits p :: cs))).2.2.length ≤ _
    simp only [List.length_cons]
    omega

private theorem fold_mulStep_width (pre : List BitStr) (p : BitStr) (bs cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (ha : ∀ a ∈ pre, a.length ≤ N) (hc : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (pre.foldl mulStep (p, bs, cs)).2.2, c.length ≤ N := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons a pre ih =>
    apply ih _ (fun d hd => ha d (by simp [hd]))
    apply addCoeffLists_width_le
    · intro c hc'
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc'
      exact (length_mulReduce_le p a b).trans (ha a (by simp))
    · intro c hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · simpa using hp
      · exact hc c hc'

private theorem fold_mulStep_eq (as : List BitStr) (p : BitStr) (bs cs : List BitStr) :
    as.foldl mulStep (p, bs, cs) =
      (p, bs, as.foldl (fun acc a => addCoeffLists (bs.map (mulReduce p a)) (zeroBits p :: acc)) cs) := by
  induction as generalizing cs with
  | nil => rfl
  | cons a as ih => exact ih _

private def mulStepProg : PolyTimeFun (MulState × BitStr) MulState :=
  let p := fst.comp fst
  let bs := fst.comp (snd.comp fst)
  let cs := snd.comp (snd.comp fst)
  let a := snd
  congr (p.pair (bs.pair (addCoeffListsProg.comp
    ((scaleCoeffProg.comp (bs.pair (p.pair a))).pair (cons (zeroBitsProg.comp p) cs)))))
    (fun q => mulStep q.1 q.2) (by
      rintro ⟨⟨p, bs, cs⟩, a⟩
      change (p, bs, addCoeffLists (scaleCoeffProg (bs, p, a)) (zeroBits p :: cs)) = _
      rfl)

private theorem mulStep_bounded : FoldBounded mulStepProg (20 * X ^ 2 + 20 * X + 20) := by
  intro as s pre post heq
  rcases s with ⟨p, bs, cs⟩
  let N := esize (as, p, bs, cs)
  have hs : N = esize as + esize p + esize bs + esize cs + 3 := by simp [N, esize_prod]; omega
  have hp : p.length ≤ N := by have := length_le_esize_bitStr p; omega
  have hb : bs.length ≤ N := by have := length_le_esize_list bs; omega
  have hc : cs.length ≤ N := by have := length_le_esize_list cs; omega
  have hpre : pre.length ≤ N := by
    have := length_le_esize_list as
    have he := congrArg List.length heq
    simp only [List.length_append] at he
    omega
  have ha : ∀ a ∈ pre, a.length ≤ N := by
    intro a ha
    have hm : a ∈ as := by rw [heq]; exact List.mem_append_left _ ha
    have h₁ := esize_mem_le hm
    have h₂ := length_le_esize_bitStr a
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    omega
  have hshape := fold_mulStep_shape pre p bs cs
  have hsize := esize_coefficients_le _ N (fold_mulStep_width pre p bs cs N hp ha hw)
  have hn : (pre.foldl mulStep (p, bs, cs)).2.2.length ≤ 3 * N := by omega
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl mulStep (p, bs, cs)) ≤ _
  rw [esize_prod, esize_prod, hshape.1, hshape.2.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + (esize bs + esize (pre.foldl mulStep (p, bs, cs)).2.2 + 1) + 1 ≤
    20 * N ^ 2 + 20 * N + 20
  nlinarith

/-- A globally polynomial-time product of two supplied-quotient coefficient lists. -/
def mulCoeffListsProg : PolyTimeFun (BitStr × List BitStr × List BitStr) (List BitStr) :=
  let scan := foldl mulStepProg (20 * X ^ 2 + 20 * X + 20) mulStep_bounded
  congr ((snd.comp snd).comp (scan.comp
    ((PolyTimeFun.reverse.comp (fst.comp snd)).pair (fst.pair ((snd.comp snd).pair (const []))))))
    (fun q => mulCoeffLists q.1 q.2.1 q.2.2) (by
      rintro ⟨p, as, bs⟩
      change (as.reverse.foldl mulStep (p, bs, [])).2.2 = _
      rw [fold_mulStep_eq, List.foldl_reverse]
      induction as with
      | nil => rfl
      | cons a as ih =>
        dsimp only at ih ⊢
        simp only [List.foldr_cons, mulCoeffLists, ih])

@[simp] theorem mulCoeffListsProg_apply (p : BitStr) (as bs : List BitStr) :
    mulCoeffListsProg (p, as, bs) = mulCoeffLists p as bs := rfl


/-- A common width bound for the left coefficients and modulus bounds every product coefficient. -/
theorem mulCoeffLists_width_le (p : BitStr) (as bs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (ha : ∀ a ∈ as, a.length ≤ N) :
    ∀ c ∈ mulCoeffLists p as bs, c.length ≤ N := by
  induction as with
  | nil => simp [mulCoeffLists]
  | cons a as ih =>
    apply addCoeffLists_width_le
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact (length_mulReduce_le _ _ _).trans (ha a (by simp))
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simpa using hp
      · exact ih (fun d hd => ha d (by simp [hd])) c hc

end MIPRE.LowDegree.BinaryQuotient

end
