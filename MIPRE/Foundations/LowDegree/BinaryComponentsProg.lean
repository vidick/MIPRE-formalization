/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryComponents

/-! # Polynomial-time fixed-space component separation -/

noncomputable section

namespace MIPRE.LowDegree.BinaryLinear

open Cost Cost.PolyTimeFun Polynomial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def nonzeroRowProg : PolyTimeFun BitStr Bool :=
  congr (ite (SAT.ArrayProg.eqBits.comp ((PolyTimeFun.id _).pair (map (const false))))
    (const false) (const true)) nonzeroRow (by
      intro v
      change (if decide (v = zeroRow v) then false else true) = decide (¬v = zeroRow v)
      rw [decide_not]
      cases decide (v = zeroRow v) <;> rfl)

def keepRowProg : PolyTimeFun BitStr (List BitStr) :=
  ite nonzeroRowProg (cons (PolyTimeFun.id _) (const [])) (const [])

def splitBitsProg : PolyTimeFun (BitStr × BitStr) (List BitStr) :=
  congr (append.comp ((keepRowProg.comp groupMulBitsProg).pair
    (keepRowProg.comp (BinaryPolynomial.xorBitsProg.comp (fst.pair groupMulBitsProg)))))
    (fun p => splitBits p.1 p.2) (by
      rintro ⟨e, b⟩
      change (if nonzeroRow (groupMulBitsProg (e, b)) then [groupMulBitsProg (e, b)] else []) ++
        (if nonzeroRow (BinaryPolynomial.xorBits e (groupMulBitsProg (e, b))) then
          [BinaryPolynomial.xorBits e (groupMulBitsProg (e, b))] else []) = _
      unfold splitBits
      split <;> split <;> simp_all)

def flattenBitsProg : PolyTimeFun (List (List BitStr)) (List BitStr) :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

def splitBitsCappedProg : PolyTimeFun (Unary × List BitStr × BitStr) (List BitStr) :=
  take.comp ((flattenBitsProg.comp ((mapWith splitBitsProg).comp snd)).pair fst)

@[simp] theorem splitBitsCappedProg_apply (u : Unary) (l : List BitStr) (b : BitStr) :
    splitBitsCappedProg (u, l, b) = splitBitsCapped u l b := by
  change (List.flatten (l.map (fun e => splitBits e b))).take u.length = _
  simp only [splitBitsCapped, List.flatMap_def]

def componentStep (s : Unary × List BitStr) (b : BitStr) : Unary × List BitStr :=
  (s.1, splitBitsCapped s.1 s.2 b)

def componentStepProg : PolyTimeFun ((Unary × List BitStr) × BitStr) (Unary × List BitStr) :=
  congr ((fst.comp fst).pair (splitBitsCappedProg.comp
    ((fst.comp fst).pair ((snd.comp fst).pair snd))))
    (fun p => componentStep p.1 p.2) (by rintro ⟨⟨u, l⟩, b⟩; simp [componentStep])

theorem splitBitsCapped_width (u : Unary) (l : List BitStr) (b : BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) : ∀ e ∈ splitBitsCapped u l b, e.length ≤ N := by
  intro e he
  obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp (List.mem_of_mem_take he)
  rw [splitBits_width x b e he]
  exact hl x hx

theorem fold_componentStep_width (bs : List BitStr) (u : Unary) (l : List BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) :
    ∀ e ∈ (bs.foldl componentStep (u, l)).2, e.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih => exact ih _ (splitBitsCapped_width u l b N hl)

theorem fold_componentStep_dimension (bs : List BitStr) (u : Unary) (l : List BitStr) :
    (bs.foldl componentStep (u, l)).1 = u := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih => exact ih _

theorem fold_componentStep_length (bs : List BitStr) (u : Unary) (l : List BitStr) (N : ℕ)
    (hu : u.length ≤ N) (hl : l.length ≤ N) :
    (bs.foldl componentStep (u, l)).2.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih =>
    apply ih
    exact (List.length_take_le _ _).trans hu

theorem esize_rows_of_width (l : List BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) : esize l ≤ l.length * (4 * N + 2) + 1 := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := (esize_bitStr_le e).trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 4 (hl e (by simp))) 1)
    have ht := ih (fun x hx => hl x (by simp [hx]))
    rw [esize_list_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem componentStep_bounded : FoldBounded componentStepProg (5 * X ^ 2 + 5 * X + 5) := by
  intro bs s pre post hbs
  rcases s with ⟨u, l⟩
  let N := esize (bs, u, l)
  have hu : u.length ≤ N := by
    have h := length_le_esize_list u
    simp only [N, esize_prod]
    omega
  have hl : l.length ≤ N := by
    have h := length_le_esize_list l
    simp only [N, esize_prod]
    omega
  have hw : ∀ e ∈ l, e.length ≤ N := by
    intro e he
    have h₁ := esize_mem_le he
    have h₂ := length_le_esize_bitStr e
    simp only [N, esize_prod]
    omega
  have hh := esize_rows_of_width _ N (fold_componentStep_width pre u l N hw)
  have hn := fold_componentStep_length pre u l N hu hl
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl componentStep (u, l)) ≤ _
  rw [esize_prod, fold_componentStep_dimension]
  have he : esize u ≤ N := by simp only [N, esize_prod]; omega
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize u + esize (pre.foldl componentStep (u, l)).2 + 1 ≤ 5 * N ^ 2 + 5 * N + 5
  nlinarith

/-- Split by every computed fixed-space generator. Clipping controls malformed inputs too. -/
def groupComponentsProg : PolyTimeFun Unary (List BitStr) :=
  snd.comp ((foldl componentStepProg (5 * X ^ 2 + 5 * X + 5) componentStep_bounded).comp
    (groupFixedGeneratorsProg.pair ((PolyTimeFun.id _).pair
      (cons (unitBitsProg.comp ((const 0).pair (PolyTimeFun.id _))) (const [])))))

theorem fold_componentStep_encoding {k : ℕ} [NeZero k]
    (bs l : List (AddMonoidAlgebra (ZMod 2) (Fin k)))
    (hl : ComponentFamily l) (hb : ∀ b ∈ bs, b * b = b) :
    (bs.map (fun z => vectorBits (groupCoordinates k z))).foldl componentStep
      (unary k, l.map (fun z => vectorBits (groupCoordinates k z))) =
    (unary k, (splitAllComponents l bs).map (fun z => vectorBits (groupCoordinates k z))) := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih =>
    have hbb := hb b (by simp)
    rw [List.map_cons, List.foldl_cons]
    change (bs.map _).foldl componentStep (unary k, splitBitsCapped _ _ _) = _
    rw [splitBitsCapped_encoding l hl b hbb, ih _ (hl.split hbb)
      (fun x hx => hb x (by simp [hx]))]
    rfl

theorem unitBits_group_one (k : ℕ) [NeZero k] :
    unitBits k 0 = vectorBits (groupCoordinates k (1 : AddMonoidAlgebra (ZMod 2) (Fin k))) := by
  rw [show unitBits k 0 = vectorBits (Pi.single (0 : Fin k) 1) from
    by simpa using unitBits_eq_vectorBits (0 : Fin k)]
  congr 1
  funext i
  change Pi.single (0 : Fin k) 1 i = (AddMonoidAlgebra.single 0 1).coeff i
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- The raw program prints precisely the nonzero primitive components, in deterministic order. -/
theorem groupComponentsProg_correct (k : ℕ) [NeZero k] :
    groupComponentsProg (unary k) =
      (groupComponents k).map (fun z => vectorBits (groupCoordinates k z)) := by
  have hg : groupFixedGeneratorsProg (unary k) =
      (groupFixedFamily k).map (fun z => vectorBits (groupCoordinates k z)) := by
    rw [groupFixedGeneratorsProg_correct]
    simp only [groupFixedFamily, List.map_ofFn]
    rfl
  have hu : ComponentFamily ([1] : List (AddMonoidAlgebra (ZMod 2) (Fin k))) := by
    constructor <;> simp
  change ((groupFixedGeneratorsProg (unary k)).foldl componentStep
    (unary k, [unitBits (unary k).length 0])).2 = _
  rw [hg, length_unary, unitBits_group_one]
  change ((groupFixedFamily k |>.map (fun z => vectorBits (groupCoordinates k z))).foldl
    componentStep (unary k, ([1] : List (AddMonoidAlgebra (ZMod 2) (Fin k))).map
      (fun z => vectorBits (groupCoordinates k z)))).2 = _
  rw [fold_componentStep_encoding _ _ hu (groupFixedFamily_idempotent k)]
  rfl

end MIPRE.LowDegree.BinaryLinear

end
