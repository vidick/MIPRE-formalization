/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotientFrobenius
import MIPRE.Foundations.LowDegree.BinaryConstants
import MIPRE.Foundations.Cost.Iterates

/-! # Polynomial products with coefficients in an explicit binary quotient -/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial

variable {R : Type*} [CommRing R]

/-- Interpret a list of binary coefficient vectors as a polynomial. -/
def coeffPolynomial (z : R) : List BitStr → Polynomial R
  | [] => 0
  | c :: cs => C (evalBits z c) + X * coeffPolynomial z cs

@[simp] theorem coeffPolynomial_nil (z : R) : coeffPolynomial z [] = 0 := rfl

@[simp] theorem coeffPolynomial_cons (z : R) (c : BitStr) (cs : List BitStr) :
    coeffPolynomial z (c :: cs) = C (evalBits z c) + X * coeffPolynomial z cs := rfl

/-- Multiply by a linear factor, with an extra constant coefficient carried in. -/
def linearMulCarry (p a carry : BitStr) (cs : List BitStr) : List BitStr :=
  (carry :: cs).zipWith xorBits ((cs.map (mulReduce p a)) ++ [zeroBits p])

/-- Multiplication by `X + a` on encoded coefficient lists. -/
def linearMulBits (p a : BitStr) (cs : List BitStr) : List BitStr :=
  linearMulCarry p a (zeroBits p) cs

@[simp] theorem length_linearMulCarry (p a carry : BitStr) (cs : List BitStr) :
    (linearMulCarry p a carry cs).length = cs.length + 1 := by
  simp [linearMulCarry]

@[simp] theorem length_linearMulBits (p a : BitStr) (cs : List BitStr) :
    (linearMulBits p a cs).length = cs.length + 1 := length_linearMulCarry ..

/-- The carried linear multiplication preserves correct coefficient widths. -/
theorem linearMulCarry_width (p a carry : BitStr) (cs : List BitStr)
    (ha : a.length = p.length) (hc : carry.length = p.length)
    (hs : ∀ c ∈ cs, c.length = p.length) :
    ∀ c ∈ linearMulCarry p a carry cs, c.length = p.length := by
  induction cs generalizing carry with
  | nil =>
    simp only [linearMulCarry, List.map_nil, List.nil_append, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.mem_singleton]
    intro c he
    subst c
    simp [hc]
  | cons c cs ih =>
    have hhead := hs c (by simp)
    have htail : ∀ d ∈ cs, d.length = p.length := fun d hd => hs d (by simp [hd])
    change ∀ d ∈ xorBits carry (mulReduce p a c) :: linearMulCarry p a c cs,
      d.length = p.length
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · simp [hc, length_mulReduce p a c ha]
    · exact ih c hhead htail d hd

/-- Linear multiplication has exactly the expected polynomial semantics. -/
theorem coeffPolynomial_linearMulCarry [CharP R 2] (z : R)
    (p a carry : BitStr) (cs : List BitStr)
    (hz : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hc : carry.length = p.length)
    (hs : ∀ c ∈ cs, c.length = p.length) :
    coeffPolynomial z (linearMulCarry p a carry cs) =
      C (evalBits z carry) + (X + C (evalBits z a)) * coeffPolynomial z cs := by
  induction cs generalizing carry with
  | nil =>
    simp only [linearMulCarry, List.map_nil, List.nil_append, List.zipWith_cons_cons,
      List.zipWith_nil_left, coeffPolynomial_cons, coeffPolynomial_nil, mul_zero, add_zero]
    rw [evalBits_xor z _ _ (by simp [hc]), evalBits_zeroBits, add_zero]
  | cons c cs ih =>
    have hhead := hs c (by simp)
    have htail : ∀ d ∈ cs, d.length = p.length := fun d hd => hs d (by simp [hd])
    change C (evalBits z (xorBits carry (mulReduce p a c))) +
      X * coeffPolynomial z (linearMulCarry p a c cs) = _
    rw [evalBits_xor z _ _ (hc.trans (length_mulReduce p a c ha).symm),
      evalBits_mulReduce z p a c ha hz, ih c hhead htail, coeffPolynomial_cons]
    simp only [map_add, map_mul]
    ring

/-- Multiplication by a linear factor is correct in any represented binary algebra. -/
theorem coeffPolynomial_linearMulBits [CharP R 2] (z : R) (p a : BitStr)
    (cs : List BitStr) (hz : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hs : ∀ c ∈ cs, c.length = p.length) :
    coeffPolynomial z (linearMulBits p a cs) =
      (X + C (evalBits z a)) * coeffPolynomial z cs := by
  rw [linearMulBits, coeffPolynomial_linearMulCarry z p a _ cs hz ha (length_zeroBits p) hs,
    evalBits_zeroBits, map_zero, zero_add]

/-- Scalar multiplication of all coefficient vectors by a supplied quotient element. -/
def scaleCoeffProg : PolyTimeFun (List BitStr × BitStr × BitStr) (List BitStr) :=
  mapWith (mulReduceProg.comp ((fst.comp snd).pair ((snd.comp snd).pair fst)))

/-- A uniform linear-factor multiplication program on arbitrary nested lists. -/
def linearMulCarryProg : PolyTimeFun (BitStr × BitStr × BitStr × List BitStr) (List BitStr) :=
  let p := fst
  let a := fst.comp snd
  let carry := fst.comp (snd.comp snd)
  let cs := snd.comp (snd.comp snd)
  let scaled := scaleCoeffProg.comp (cs.pair (p.pair a))
  let padded := append.comp (scaled.pair (cons (zeroBitsProg.comp p) (const [])))
  (map xorBitsProg).comp (zip.comp ((cons carry cs).pair padded))

@[simp] theorem linearMulCarryProg_apply (p a carry : BitStr) (cs : List BitStr) :
    linearMulCarryProg (p, a, carry, cs) = linearMulCarry p a carry cs := by
  change (((carry :: cs).zip ((cs.map (mulReduce p a)) ++ [zeroBits p])).map
    (fun pair => xorBits pair.1 pair.2)) = _
  exact List.map_zip_eq_zipWith

/-- Polynomial-time multiplication by one encoded monic linear factor. -/
def linearMulBitsProg : PolyTimeFun (BitStr × BitStr × List BitStr) (List BitStr) :=
  linearMulCarryProg.comp
    (fst.pair ((fst.comp snd).pair ((zeroBitsProg.comp fst).pair (snd.comp snd))))

@[simp] theorem linearMulBitsProg_apply (p a : BitStr) (cs : List BitStr) :
    linearMulBitsProg (p, a, cs) = linearMulBits p a cs := by
  change linearMulCarryProg (p, a, zeroBits p, cs) = _
  rw [linearMulCarryProg_apply]
  rfl

/-- Malformed coefficient arithmetic cannot increase a retained coefficient width. -/
theorem linearMulCarry_width_le (p a carry : BitStr) (cs : List BitStr) (N : ℕ)
    (hc : carry.length ≤ N) (hs : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ linearMulCarry p a carry cs, c.length ≤ N := by
  induction cs generalizing carry with
  | nil =>
    intro c he
    have heq : c = xorBits carry (zeroBits p) := by simpa [linearMulCarry] using he
    rw [heq, length_xorBits]
    exact (min_le_left _ _).trans hc
  | cons c cs ih =>
    change ∀ d ∈ xorBits carry (mulReduce p a c) :: linearMulCarry p a c cs, d.length ≤ N
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [length_xorBits]
      exact (min_le_left _ _).trans hc
    · exact ih c (hs c (by simp)) (fun d hd => hs d (by simp [hd])) d hd

/-- Modulus and accumulated coefficient list for a product of linear factors. -/
abbrev ProductState := BitStr × List BitStr

/-- Multiply the accumulated polynomial by the next supplied linear factor. -/
def productStep (s : ProductState) (a : BitStr) : ProductState :=
  (s.1, linearMulBits s.1 a s.2)

/-- The product loop retains its modulus and adds one coefficient per iteration. -/
theorem fold_productStep_shape (bs : List BitStr) (s : ProductState) :
    (bs.foldl productStep s).1 = s.1 ∧
      (bs.foldl productStep s).2.length = s.2.length + bs.length := by
  induction bs generalizing s with
  | nil => simp
  | cons a bs ih =>
    have h := ih (productStep s a)
    simpa only [List.foldl_cons, productStep, length_linearMulBits, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 bs.length] using h

/-- Every coefficient width remains bounded independently of the number of factors. -/
theorem fold_productStep_width (bs : List BitStr) (p : BitStr) (cs : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hs : ∀ c ∈ cs, c.length ≤ N) :
    ∀ c ∈ (bs.foldl productStep (p, cs)).2, c.length ≤ N := by
  induction bs generalizing cs with
  | nil => exact hs
  | cons a bs ih =>
    apply ih (linearMulBits p a cs)
    exact linearMulCarry_width_le p a (zeroBits p) cs N (by simpa using hp) hs

/-- Valid fixed-width coefficients remain valid through the product loop. -/
theorem fold_productStep_width_eq (bs : List BitStr) (p : BitStr) (cs : List BitStr)
    (hb : ∀ a ∈ bs, a.length = p.length) (hs : ∀ c ∈ cs, c.length = p.length) :
    ∀ c ∈ (bs.foldl productStep (p, cs)).2, c.length = p.length := by
  induction bs generalizing cs with
  | nil => exact hs
  | cons a bs ih =>
    apply ih (linearMulBits p a cs) (fun b hb' => hb b (by simp [hb']))
    exact linearMulCarry_width p a _ cs (hb a (by simp)) (length_zeroBits p) hs

/-- The accumulated coefficient polynomial is the product of all supplied factors. -/
theorem coeffPolynomial_fold_productStep [CharP R 2] (z : R) (p : BitStr)
    (bs cs : List BitStr) (hz : z ^ p.length = evalBits z p)
    (hb : ∀ a ∈ bs, a.length = p.length) (hs : ∀ c ∈ cs, c.length = p.length) :
    coeffPolynomial z (bs.foldl productStep (p, cs)).2 =
      (bs.map (fun a => X + C (evalBits z a))).prod * coeffPolynomial z cs := by
  induction bs generalizing cs with
  | nil => simp
  | cons a bs ih =>
    have ha := hb a (by simp)
    have ht : ∀ b ∈ bs, b.length = p.length := fun b hb' => hb b (by simp [hb'])
    have hc := linearMulCarry_width p a (zeroBits p) cs ha (length_zeroBits p) hs
    change coeffPolynomial z (bs.foldl productStep (p, linearMulBits p a cs)).2 = _
    rw [ih (linearMulBits p a cs) ht hc, coeffPolynomial_linearMulBits z p a cs hz ha hs]
    simp only [List.map_cons, List.prod_cons]
    ring

/-- Product of the monic linear factors with the supplied roots. -/
def linearProductBits (p : BitStr) (bs : List BitStr) : List BitStr :=
  (bs.foldl productStep (p, [oneBits p])).2

/-- The encoded product has the expected polynomial semantics. -/
theorem coeffPolynomial_linearProductBits [CharP R 2] (z : R) (p : BitStr)
    (bs : List BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p)
    (hb : ∀ a ∈ bs, a.length = p.length) :
    coeffPolynomial z (linearProductBits p bs) =
      (bs.map (fun a => X + C (evalBits z a))).prod := by
  rw [linearProductBits, coeffPolynomial_fold_productStep z p bs [oneBits p] hz hb
    (by intro c hc; obtain rfl := List.mem_singleton.mp hc; exact length_oneBits p)]
  simp [evalBits_oneBits z p hp]

private def productStepProg : PolyTimeFun (ProductState × BitStr) ProductState :=
  congr ((fst.comp fst).pair (linearMulBitsProg.comp
    ((fst.comp fst).pair (snd.pair (snd.comp fst)))))
    (fun q => productStep q.1 q.2) (by
      rintro ⟨⟨p, cs⟩, a⟩
      change (p, linearMulBitsProg (p, a, cs)) = (p, linearMulBits p a cs)
      rw [linearMulBitsProg_apply])

/-- Nested coefficient-list encoded size is polynomial in count and width. -/
theorem esize_coefficients_le (cs : List BitStr) (N : ℕ)
    (hs : ∀ c ∈ cs, c.length ≤ N) : esize cs ≤ cs.length * (4 * N + 2) + 1 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := esize_bitStr_le c
    have hl := hs c (by simp)
    have ht := ih (fun d hd => hs d (by simp [hd]))
    rw [esize_list_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem productStep_bounded : FoldBounded productStepProg (10 * X ^ 2 + 10 * X + 10) := by
  intro bs s pre post heq
  rcases s with ⟨p, cs⟩
  let N := esize (bs, p, cs)
  have hp : p.length ≤ N := by
    have h := length_le_esize_list p
    simp only [N, esize_prod]
    omega
  have hc : cs.length ≤ N := by
    have h := length_le_esize_list cs
    simp only [N, esize_prod]
    omega
  have hb : pre.length ≤ N := by
    have h := length_le_esize_list bs
    have he := congrArg List.length heq
    simp only [N, esize_prod, List.length_append] at *
    omega
  have hw : ∀ c ∈ cs, c.length ≤ N := by
    intro c hc'
    have h₁ := esize_mem_le hc'
    have h₂ := length_le_esize_bitStr c
    simp only [N, esize_prod]
    omega
  have hs := fold_productStep_shape pre (p, cs)
  have hsize := esize_coefficients_le _ N (fold_productStep_width pre p cs N hp hw)
  have hlen : (pre.foldl productStep (p, cs)).2.length = cs.length + pre.length := hs.2
  have hn : (pre.foldl productStep (p, cs)).2.length ≤ 2 * N := by omega
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  have hpe : esize p ≤ N := by simp only [N, esize_prod]; omega
  change esize (pre.foldl productStep (p, cs)) ≤ _
  rw [esize_prod, hs.1]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + esize (pre.foldl productStep (p, cs)).2 + 1 ≤ 10 * N ^ 2 + 10 * N + 10
  nlinarith

/-- One globally polynomial-time program for a product of encoded linear factors. -/
def linearProductBitsProg : PolyTimeFun (BitStr × List BitStr) (List BitStr) :=
  snd.comp ((foldl productStepProg (10 * X ^ 2 + 10 * X + 10) productStep_bounded).comp
    (snd.pair (fst.pair (cons (oneBitsProg.comp fst) (const [])))))

@[simp] theorem linearProductBitsProg_apply (p : BitStr) (bs : List BitStr) :
    linearProductBitsProg (p, bs) = linearProductBits p bs := rfl

/-- State for successive Frobenius powers, retaining the modulus. -/
abbrev SquareState := BitStr × BitStr

/-- One repeated-squaring step in a supplied binary quotient. -/
def squareStep (s : SquareState) : SquareState := (s.1, mulReduce s.1 s.2 s.2)

/-- Squaring cannot increase the width even on malformed inputs. -/
theorem iterate_squareStep_shape (n : ℕ) (s : SquareState) :
    (squareStep^[n] s).1 = s.1 ∧ (squareStep^[n] s).2.length ≤ s.2.length := by
  induction n generalizing s with
  | zero => exact ⟨rfl, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hm, hw⟩ := ih (squareStep s)
    exact ⟨hm, hw.trans (length_mulReduce_le ..)⟩

/-- Repeated squaring preserves the fixed-width representation. -/
theorem iterate_squareStep_width (n : ℕ) (p a : BitStr) (ha : a.length = p.length) :
    (squareStep^[n] (p, a)).2.length = p.length := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (length_mulReduce p a a ha)

/-- Repeated squaring computes the corresponding Frobenius power. -/
theorem evalBits_iterate_squareStep [CharP R 2] (z : R) (n : ℕ) (p a : BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (squareStep^[n] (p, a)).2 = evalBits z a ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change evalBits z (squareStep^[n] (p, mulReduce p a a)).2 = _
    rw [ih _ (length_mulReduce p a a ha), evalBits_mulReduce z p a a ha hz]
    rw [← pow_two, ← pow_mul, pow_succ, Nat.mul_comm (2 ^ n) 2]

private def squareStepProg : PolyTimeFun SquareState SquareState := fst.pair squareProg

private theorem squareStep_bounded (n : ℕ) (s : SquareState) :
    esize ((squareStepProg : SquareState → SquareState)^[n] s) ≤
      (5 * X + 5 : Polynomial ℕ).eval (esize s) := by
  change esize (squareStep^[n] s) ≤ _
  obtain ⟨hm, hw⟩ := iterate_squareStep_shape n s
  have ha := esize_bitStr_le (squareStep^[n] s).2
  have hb := length_le_esize_bitStr s.2
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hm]
  simp only [eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- The first Frobenius powers of a supplied represented element. -/
def orbitBits (u : Unary) (p a : BitStr) : List BitStr :=
  (recordIterates squareStep u (p, a)).map Prod.snd

/-- The orbit list has exactly its unary budget of elements. -/
@[simp] theorem length_orbitBits (u : Unary) (p a : BitStr) :
    (orbitBits u p a).length = u.length := by simp [orbitBits, recordIterates]

/-- Every orbit element has the supplied modulus width. -/
theorem orbitBits_width (u : Unary) (p a : BitStr) (ha : a.length = p.length) :
    ∀ b ∈ orbitBits u p a, b.length = p.length := by
  intro b hb
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  exact iterate_squareStep_width i p a ha

/-- The orbit encodes exactly the specified list of Frobenius powers. -/
theorem map_evalBits_orbitBits [CharP R 2] (z : R) (u : Unary) (p a : BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    (orbitBits u p a).map (evalBits z) =
      List.ofFn (fun i : Fin u.length => evalBits z a ^ (2 ^ (i : ℕ))) := by
  simp only [orbitBits, recordIterates, List.map_ofFn]
  congr 1
  funext i
  exact evalBits_iterate_squareStep z i p a hz ha

/-- A polynomial-time orbit printer, valid on every raw input. -/
def orbitBitsProg : PolyTimeFun (Unary × BitStr × BitStr) (List BitStr) :=
  (map snd).comp (recordIteratesProg squareStepProg (5 * X + 5) squareStep_bounded)

@[simp] theorem orbitBitsProg_apply (u : Unary) (p a : BitStr) :
    orbitBitsProg (u, p, a) = orbitBits u p a := rfl

/-- Multiply the monic linear factors for a specified Frobenius orbit. -/
def orbitProductBits (u : Unary) (p a : BitStr) : List BitStr :=
  linearProductBits p (orbitBits u p a)

/-- A uniform polynomial-time Frobenius-orbit product program. -/
def orbitProductBitsProg : PolyTimeFun (Unary × BitStr × BitStr) (List BitStr) :=
  linearProductBitsProg.comp ((fst.comp snd).pair orbitBitsProg)

@[simp] theorem orbitProductBitsProg_apply (u : Unary) (p a : BitStr) :
    orbitProductBitsProg (u, p, a) = orbitProductBits u p a := by
  change linearProductBitsProg (p, orbitBits u p a) = _
  rw [linearProductBitsProg_apply]
  rfl

/-- The printed product equals the product of the Frobenius conjugate linear factors. -/
theorem coeffPolynomial_orbitProductBits [CharP R 2] (z : R) (u : Unary) (p a : BitStr)
    (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    coeffPolynomial z (orbitProductBits u p a) =
      (List.ofFn (fun i : Fin u.length => X + C (evalBits z a ^ (2 ^ (i : ℕ))))).prod := by
  rw [orbitProductBits, coeffPolynomial_linearProductBits z p _ hp hz (orbitBits_width u p a ha)]
  have h := congrArg (fun l : List R => (l.map (fun x => X + C x)).prod)
    (map_evalBits_orbitBits z u p a hz ha)
  simpa only [List.map_map, List.map_ofFn, Function.comp_def] using h

/-- Every printed coefficient has the prescribed quotient width. -/
theorem orbitProductBits_width (u : Unary) (p a : BitStr) (ha : a.length = p.length) :
    ∀ c ∈ orbitProductBits u p a, c.length = p.length := by
  apply fold_productStep_width_eq _ p [oneBits p] (orbitBits_width u p a ha)
  intro c hc
  obtain rfl := List.mem_singleton.mp hc
  exact length_oneBits p

/-- The orbit product has exactly one more coefficient than its orbit length. -/
@[simp] theorem length_orbitProductBits (u : Unary) (p a : BitStr) :
    (orbitProductBits u p a).length = u.length + 1 := by
  have h := (fold_productStep_shape (orbitBits u p a) (p, [oneBits p])).2
  simpa only [orbitProductBits, linearProductBits, List.length_singleton, length_orbitBits,
    Nat.add_comm 1 u.length] using h

end MIPRE.LowDegree.BinaryQuotient

end