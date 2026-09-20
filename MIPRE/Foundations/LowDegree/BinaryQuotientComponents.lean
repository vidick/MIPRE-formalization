/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryQuotient
import MIPRE.Foundations.LowDegree.BinaryCanonical
import MIPRE.Foundations.LowDegree.BinaryComponentsProg
import MIPRE.Foundations.LowDegree.BinaryQuotientFrobenius

/-!
# Bounded component separation in binary polynomial quotients

Refine the unit by a supplied family of Frobenius-fixed vectors. The component
count is clipped to the quotient dimension on every iteration; the algebraic
orthogonality invariant proves that clipping is inert on valid inputs.
-/

noncomputable section

namespace MIPRE.LowDegree.BinaryQuotient

open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial

variable (f : Polynomial (ZMod 2)) (hf : f.Monic)

/-- Canonical encoding is injective for every monic quotient. -/
theorem toBits_injective : Function.Injective (toBits f hf) := by
  intro x y h
  have he := congrArg (ofBits f hf) h
  simpa only [ofBits_toBits] using he

/-- The zero row agrees with the canonical zero encoding. -/
theorem zeroRow_toBits (x : AdjoinRoot f) :
    BinaryLinear.zeroRow (toBits f hf x) = toBits f hf 0 := by
  simp only [BinaryLinear.zeroRow, toBits, List.map_ofFn, map_zero, Finsupp.zero_apply]
  rfl

/-- The raw zero test faithfully recognizes quotient zero on canonical encodings. -/
theorem nonzeroRow_toBits (x : AdjoinRoot f) :
    BinaryLinear.nonzeroRow (toBits f hf x) = decide (x ≠ 0) := by
  unfold BinaryLinear.nonzeroRow
  rw [zeroRow_toBits]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr (toBits_injective f hf).eq_iff

/-- Raw XOR agrees exactly with canonical encoding of quotient addition. -/
theorem xorBits_toBits (x y : AdjoinRoot f) :
    xorBits (toBits f hf x) (toBits f hf y) = toBits f hf (x + y) := by
  have h := congrArg (toBits f hf)
    (ofBits_xor f hf (toBits f hf x) (toBits f hf y) (length_toBits f hf x) (length_toBits f hf y))
  have hw : (xorBits (toBits f hf x) (toBits f hf y)).length = f.natDegree := by
    rw [length_xorBits, length_toBits, length_toBits, min_self]
  simpa only [xorBitsProg_apply, toBits_ofBits f hf _ hw, ofBits_toBits] using h

/-- Raw modular multiplication agrees with canonical quotient multiplication. -/
theorem mulReduce_toBits (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (x y : AdjoinRoot f) :
    mulReduce p (toBits f hf x) (toBits f hf y) = toBits f hf (x * y) := by
  have h := congrArg (toBits f hf)
    (ofBits_mulReduce f hf p (toBits f hf x) (toBits f hf y) hp hpoly
      (length_toBits f hf x) (length_toBits f hf y))
  simpa only [mulReduceProg_apply, toBits_ofBits f hf _
    ((length_mulReduce _ _ _ ((length_toBits f hf x).trans hp.symm)).trans hp), ofBits_toBits] using h

/-- One quotient split uses modular multiplication, XOR, and a zero test. -/
def splitBits (p e b : BitStr) : List BitStr :=
  let x := mulReduce p e b
  [x, xorBits e x].filter BinaryLinear.nonzeroRow

/-- Splitting never increases any component's coefficient width. -/
theorem splitBits_width (p e b : BitStr) : ∀ x ∈ splitBits p e b, x.length ≤ e.length := by
  intro x hx
  have hm := (List.mem_filter.mp hx).1
  rcases List.mem_cons.mp hm with rfl | hm
  · exact length_mulReduce_le _ _ _
  · rw [List.mem_singleton.mp hm, length_xorBits]
    exact min_le_left _ _

/-- The encoded split is exactly the abstract idempotent split. -/
theorem splitBits_encoding (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (e b : AdjoinRoot f) :
    splitBits p (toBits f hf e) (toBits f hf b) =
      (splitComponent e b).map (toBits f hf) := by
  unfold splitBits
  rw [mulReduce_toBits f hf p hp hpoly]
  dsimp only
  rw [xorBits_toBits]
  have he : e + e * b = e * (1 - b) := by
    nontriviality (AdjoinRoot f)
    let : CharP (AdjoinRoot f) 2 :=
      charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
    rw [CharTwo.sub_eq_add, mul_add, mul_one]
  rw [he]
  unfold splitComponent
  by_cases h₁ : e * b = 0 <;> by_cases h₂ : e * (1 - b) = 0 <;>
    simp [nonzeroRow_toBits, h₁, h₂]

/-- Refine the component list and retain at most the quotient dimension. -/
def splitBitsCapped (p : BitStr) (l : List BitStr) (b : BitStr) : List BitStr :=
  (l.flatMap (fun e => splitBits p e b)).take p.length

include hf in
/-- The quotient dimension is the degree of the monic modulus. -/
theorem finrank_eq : Module.finrank (ZMod 2) (AdjoinRoot f) = f.natDegree := by
  rw [(coordinateEquiv f hf).finrank_eq]
  simp

/-- The list cap is inert on a genuine family of orthogonal quotient idempotents. -/
theorem splitBitsCapped_encoding (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true]))
    (l : List (AdjoinRoot f)) (hl : ComponentFamily l)
    (b : AdjoinRoot f) (hb : b * b = b) :
    splitBitsCapped p (l.map (toBits f hf)) (toBits f hf b) =
      (splitComponents l b).map (toBits f hf) := by
  have he : (l.map (toBits f hf)).flatMap (fun e => splitBits p e (toBits f hf b)) =
      (splitComponents l b).map (toBits f hf) := by
    simp only [List.flatMap_map, splitBits_encoding f hf p hp hpoly,
      splitComponents, List.map_flatMap]
  unfold splitBitsCapped
  rw [he, List.take_of_length_le]
  let : Module.Finite (ZMod 2) (AdjoinRoot f) :=
    Module.Finite.equiv (coordinateEquiv f hf).symm
  simpa only [List.length_map, finrank_eq f hf, hp] using (hl.split hb).length_le_finrank

/-- Quotient modulus together with its current component list. -/
abbrev ComponentState := BitStr × List BitStr

/-- Refine once by the next supplied fixed-space generator. -/
def componentStep (s : ComponentState) (b : BitStr) : ComponentState :=
  (s.1, splitBitsCapped s.1 s.2 b)

/-- Refinement retains the modulus. -/
theorem fold_componentStep_modulus (bs : List BitStr) (p : BitStr) (l : List BitStr) :
    (bs.foldl componentStep (p, l)).1 = p := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Refined lists retain the original coefficient-width bound. -/
theorem splitBitsCapped_width (p : BitStr) (l : List BitStr) (b : BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) : ∀ e ∈ splitBitsCapped p l b, e.length ≤ N := by
  intro e he
  obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp (List.mem_of_mem_take he)
  exact (splitBits_width p x b e he).trans (hl x hx)

/-- Every partial refinement has the original maximum component width. -/
theorem fold_componentStep_width (bs : List BitStr) (p : BitStr) (l : List BitStr) (N : ℕ)
    (hl : ∀ e ∈ l, e.length ≤ N) :
    ∀ e ∈ (bs.foldl componentStep (p, l)).2, e.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih => exact ih _ (splitBitsCapped_width p l b N hl)

/-- The cap bounds the number of components even for malformed inputs. -/
theorem fold_componentStep_length (bs : List BitStr) (p : BitStr) (l : List BitStr) (N : ℕ)
    (hp : p.length ≤ N) (hl : l.length ≤ N) :
    (bs.foldl componentStep (p, l)).2.length ≤ N := by
  induction bs generalizing l with
  | nil => exact hl
  | cons b bs ih => exact ih _ ((List.length_take_le _ _).trans hp)

/-- A single raw component split as a polynomial-time ambient program. -/
def splitBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) (List BitStr) :=
  let e := fst.comp snd
  congr (append.comp ((BinaryLinear.keepRowProg.comp mulReduceProg).pair
    (BinaryLinear.keepRowProg.comp (xorBitsProg.comp (e.pair mulReduceProg)))))
    (fun s => splitBits s.1 s.2.1 s.2.2) (by
      intro s
      change (if BinaryLinear.nonzeroRow (mulReduce s.1 s.2.1 s.2.2)
        then [mulReduce s.1 s.2.1 s.2.2] else []) ++
        (if BinaryLinear.nonzeroRow (xorBits s.2.1 (mulReduce s.1 s.2.1 s.2.2))
        then [xorBits s.2.1 (mulReduce s.1 s.2.1 s.2.2)] else []) = _
      unfold splitBits
      split <;> split <;> simp_all)

/-- Refine a raw list with one generator and apply the dimension cap. -/
def splitBitsCappedProg : PolyTimeFun (BitStr × List BitStr × BitStr) (List BitStr) :=
  let split : PolyTimeFun (BitStr × (BitStr × BitStr)) (List BitStr) :=
    splitBitsProg.comp ((fst.comp snd).pair (fst.pair (snd.comp snd)))
  congr (take.comp ((BinaryLinear.flattenBitsProg.comp ((mapWith split).comp
    ((fst.comp snd).pair (fst.pair (snd.comp snd))))).pair (length.comp fst)))
    (fun s => splitBitsCapped s.1 s.2.1 s.2.2) (by
      intro s
      change (List.flatten (s.2.1.map (fun e => splitBits s.1 e s.2.2))).take
        (unary s.1.length).length = _
      simp only [length_unary, splitBitsCapped, List.flatMap_def])

@[simp] theorem splitBitsCappedProg_apply (p : BitStr) (l : List BitStr) (b : BitStr) :
    splitBitsCappedProg (p, l, b) = splitBitsCapped p l b := rfl

private def componentStepProg : PolyTimeFun (ComponentState × BitStr) ComponentState :=
  (fst.comp fst).pair (splitBitsCappedProg.comp
    ((fst.comp fst).pair ((snd.comp fst).pair snd)))

private theorem componentStep_bounded : FoldBounded componentStepProg (5 * X ^ 2 + 5 * X + 5) := by
  intro bs s pre post _
  rcases s with ⟨p, l⟩
  let N := esize (bs, p, l)
  have hp : p.length ≤ N := by
    have h := length_le_esize_list p
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
  have hh := BinaryLinear.esize_rows_of_width _ N (fold_componentStep_width pre p l N hw)
  have hn := fold_componentStep_length pre p l N hp hl
  have hm := Nat.mul_le_mul_right (4 * N + 2) hn
  change esize (pre.foldl componentStep (p, l)) ≤ _
  rw [esize_prod, fold_componentStep_modulus]
  have he : esize p ≤ N := by simp only [N, esize_prod]; omega
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  change esize p + esize (pre.foldl componentStep (p, l)).2 + 1 ≤ 5 * N ^ 2 + 5 * N + 5
  nlinarith

/-- Refine the unit by the supplied fixed-space generator list. -/
def componentsBits (p : BitStr) (bs : List BitStr) : List BitStr :=
  (bs.foldl componentStep (p, [oneBits p])).2

/-- Uniform polynomial-time quotient component separation. -/
def componentsBitsProg : PolyTimeFun (BitStr × List BitStr) (List BitStr) :=
  snd.comp ((foldl componentStepProg (5 * X ^ 2 + 5 * X + 5) componentStep_bounded).comp
    (snd.pair (fst.pair (cons (oneBitsProg.comp fst) (const [])))))

@[simp] theorem componentsBitsProg_apply (p : BitStr) (bs : List BitStr) :
    componentsBitsProg (p, bs) = componentsBits p bs := rfl

/-- The complete encoded refinement agrees with abstract component refinement. -/
theorem fold_componentStep_encoding (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true]))
    (bs l : List (AdjoinRoot f)) (hl : ComponentFamily l)
    (hb : ∀ b ∈ bs, b * b = b) :
    (bs.map (toBits f hf)).foldl componentStep (p, l.map (toBits f hf)) =
      (p, (splitAllComponents l bs).map (toBits f hf)) := by
  induction bs generalizing l with
  | nil => rfl
  | cons b bs ih =>
    have hbb := hb b (by simp)
    rw [List.map_cons, List.foldl_cons]
    change (bs.map _).foldl componentStep (p, splitBitsCapped _ _ _) = _
    rw [splitBitsCapped_encoding f hf p hp hpoly l hl b hbb, ih _ (hl.split hbb)
      (fun x hx => hb x (by simp [hx]))]
    rfl

/-- The Frobenius-fixed family in the program's specified deterministic order. -/
def fixedFamily : List (AdjoinRoot f) := List.ofFn (fixedGenerator f hf)

/-- The abstract component family produced by separating all fixed-space generators. -/
def components : List (AdjoinRoot f) := splitAllComponents [1] (fixedFamily f hf)

/-- Every generator in the computed fixed-space family is idempotent. -/
theorem fixedFamily_idempotent : ∀ b ∈ fixedFamily f hf, b * b = b := by
  intro b hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  exact fixedGenerator_idempotent f hf j

/-- All quotient idempotents lie in the span of the computed family. -/
theorem fixedFamily_spans (z : AdjoinRoot f) (hz : z * z = z) :
    z ∈ Submodule.span (ZMod 2) {b | b ∈ fixedFamily f hf} := by
  have hs : {b | b ∈ fixedFamily f hf} = Set.range (fixedGenerator f hf) := by
    ext b
    simp [fixedFamily]
  rw [hs]
  exact fixedGenerator_spans f hf z hz

/-- The computed abstract components are complete nonzero orthogonal idempotents. -/
theorem components_family [Nontrivial (AdjoinRoot f)] : ComponentFamily (components f hf) := by
  have hu : ComponentFamily ([1] : List (AdjoinRoot f)) := by constructor <;> simp
  exact hu.splitAll (fixedFamily_idempotent f hf)

/-- Separation of the complete fixed space makes every returned component primitive. -/
theorem components_primitive [Nontrivial (AdjoinRoot f)] :
    ∀ e ∈ components f hf, PrimitiveBinaryComponent e := by
  have hu : ComponentFamily ([1] : List (AdjoinRoot f)) := by constructor <;> simp
  exact splitAllComponents_primitive hu (fixedFamily_idempotent f hf) (fixedFamily_spans f hf)

/-- Fixed-width one is the canonical encoding of the quotient unit. -/
theorem oneBits_toBits (p : BitStr) (hp : p.length = f.natDegree) (hp0 : p ≠ []) :
    oneBits p = toBits f hf 1 := by
  apply (evalBits_eq_iff f hf _ _ ((length_oneBits p).trans hp) (length_toBits f hf 1)).mp
  rw [evalBits_oneBits _ p hp0, evalBits_toBits]

/-- Compute the primitive component encodings from the monic modulus alone. -/
def quotientComponentsProg : PolyTimeFun BitStr (List BitStr) :=
  componentsBitsProg.comp ((PolyTimeFun.id _).pair fixedGeneratorsProg)

/-- The uniform program computes precisely the abstract primitive components. -/
theorem quotientComponentsProg_correct (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) :
    quotientComponentsProg p = (components f hf).map (toBits f hf) := by
  have hdegree : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf.ne_zero]
    have hlen : 0 < p.length := List.length_pos_iff.mpr hp0
    exact_mod_cast (show f.natDegree ≠ 0 by omega)
  let : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f hdegree
  have hg : fixedGeneratorsProg p = (fixedFamily f hf).map (toBits f hf) := by
    rw [fixedGeneratorsProg_correct f hf p hp hpoly]
    simp only [fixedFamily, List.map_ofFn]
    rfl
  have hu : ComponentFamily ([1] : List (AdjoinRoot f)) := by constructor <;> simp
  change ((fixedGeneratorsProg p).foldl componentStep (p, [oneBits p])).2 = _
  rw [hg, oneBits_toBits f hf p hp hp0]
  change (((fixedFamily f hf).map (toBits f hf)).foldl componentStep
    (p, ([1] : List (AdjoinRoot f)).map (toBits f hf))).2 = _
  rw [fold_componentStep_encoding f hf p hp hpoly _ _ hu (fixedFamily_idempotent f hf)]
  rfl

end MIPRE.LowDegree.BinaryQuotient

end
