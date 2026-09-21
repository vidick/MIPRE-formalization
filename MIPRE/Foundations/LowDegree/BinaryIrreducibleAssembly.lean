/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryPrimePowerDispatch
import MIPRE.Foundations.LowDegree.BinaryComposedSum

/-! # A globally bounded assembly of coprime prime-power irreducibles -/

noncomputable section

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial BinaryQuotient DegreeArithmetic

/-- Lower coefficients of the normalized composed-sum polynomial. -/
def composedLowerBits (p g : BitStr) : BitStr :=
  (normalizeBits (composedSumBits p g)).dropLast

/-- The composed-sum lower coefficients preserve irreducibility and multiply degrees. -/
theorem composedLowerBits_correct (p g : BitStr)
    (hp : Irreducible (polyOfBits (p ++ [true])))
    (hg : (polyOfBits g).Monic) (hgi : Irreducible (polyOfBits g))
    (hcop : p.length.Coprime (polyOfBits g).natDegree) :
    Irreducible (polyOfBits (composedLowerBits p g ++ [true])) ∧
      (composedLowerBits p g).length = p.length * (polyOfBits g).natDegree := by
  let f := polyOfBits (p ++ [true])
  let : Fact (Irreducible f) := ⟨hp⟩
  have hf := monic_polyOfBits_append_true p
  have h := composedSumBits_correct f hf p g (natDegree_polyOfBits_append_true p).symm rfl
    hg hgi (by simpa only [f, natDegree_polyOfBits_append_true] using hcop)
  have hn := length_normalizeBits (composedSumBits p g) h.1.ne_zero
  have hc : (normalizeBits (composedSumBits p g)).getLastD false = true := by
    rcases normalizeBits_getLast (composedSumBits p g) with hz | hz
    · exact (h.1.ne_zero ((normalizeBits_eq_nil_iff _).mp hz)).elim
    · exact hz
  constructor
  · rw [composedLowerBits, dropLast_append_true _ hc, polyOfBits_normalizeBits]
    exact h.2.1
  · rw [composedLowerBits, List.length_dropLast, hn, h.2.2]
    simp only [f, natDegree_polyOfBits_append_true, Nat.add_sub_cancel]

/-- The unary target-degree cap and the current monic lower coefficients. -/
abbrev AssemblyState := Unary × BitStr

/-- Every step clips its new modulus to the original unary target-degree cap. -/
def assemblyStep (s : AssemblyState) (g : BitStr) : AssemblyState :=
  (s.1, (composedLowerBits s.2 g).take s.1.length)

/-- The cap is inert whenever the intended next degree is within the target. -/
theorem assemblyStep_correct (u : Unary) (p g : BitStr)
    (hp : Irreducible (polyOfBits (p ++ [true])))
    (hg : (polyOfBits g).Monic) (hgi : Irreducible (polyOfBits g))
    (hcop : p.length.Coprime (polyOfBits g).natDegree)
    (hcap : p.length * (polyOfBits g).natDegree ≤ u.length) :
    Irreducible (polyOfBits ((assemblyStep (u, p) g).2 ++ [true])) ∧
      (assemblyStep (u, p) g).2.length = p.length * (polyOfBits g).natDegree := by
  have h := composedLowerBits_correct p g hp hg hgi hcop
  have ht : (composedLowerBits p g).take u.length = composedLowerBits p g :=
    List.take_of_length_le (h.2.trans_le hcap)
  simpa only [assemblyStep, ht] using h

/-- No raw fold state can exceed its initial width or the supplied cap. -/
theorem fold_assemblyStep_shape (l : List BitStr) (s : AssemblyState) :
    (l.foldl assemblyStep s).1 = s.1 ∧
    (l.foldl assemblyStep s).2.length ≤ max s.2.length s.1.length := by
  induction l generalizing s with
  | nil => exact ⟨rfl, le_max_left _ _⟩
  | cons g l ih =>
    have h := ih (assemblyStep s g)
    refine ⟨h.1, h.2.trans ?_⟩
    change max ((composedLowerBits s.2 g).take s.1.length).length s.1.length ≤ _
    exact max_le ((List.length_take_le _ _).trans (le_max_right _ _)) (le_max_right _ _)

private theorem degree_prod_pos (l : List BitStr)
    (h : ∀ g ∈ l, Irreducible (polyOfBits g)) :
    0 < (l.map (fun g => (polyOfBits g).natDegree)).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (h g (by simp)).natDegree_pos (ih (fun a ha => h a (by simp [ha])))

/-- The bounded fold multiplies any pairwise coprime list of certified degrees. -/
theorem fold_assemblyStep_correct (l : List BitStr) (u : Unary) (p : BitStr)
    (hp : Irreducible (polyOfBits (p ++ [true])))
    (hl : ∀ g ∈ l, (polyOfBits g).Monic ∧ Irreducible (polyOfBits g))
    (hpair : l.Pairwise (fun g h => (polyOfBits g).natDegree.Coprime (polyOfBits h).natDegree))
    (hcop : ∀ g ∈ l, p.length.Coprime (polyOfBits g).natDegree)
    (hcap : p.length * (l.map (fun g => (polyOfBits g).natDegree)).prod ≤ u.length) :
    Irreducible (polyOfBits ((l.foldl assemblyStep (u, p)).2 ++ [true])) ∧
      (l.foldl assemblyStep (u, p)).2.length =
        p.length * (l.map (fun g => (polyOfBits g).natDegree)).prod := by
  induction l generalizing p with
  | nil => simpa using hp
  | cons g l ih =>
    have hg := hl g (by simp)
    have htail : ∀ a ∈ l, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) :=
      fun a ha => hl a (by simp [ha])
    obtain ⟨hhead, hpairs⟩ := List.pairwise_cons.mp hpair
    have hpos := degree_prod_pos l (fun a ha => (htail a ha).2)
    have hbound : p.length * (polyOfBits g).natDegree ≤ u.length := by
      simp only [List.map_cons, List.prod_cons, ← Nat.mul_assoc] at hcap
      have hmul := Nat.le_mul_of_pos_right (p.length * (polyOfBits g).natDegree) hpos
      exact hmul.trans hcap
    have hs := assemblyStep_correct u p g hp hg.1 hg.2 (hcop g (by simp)) hbound
    let p' := (assemblyStep (u, p) g).2
    have hcop' : ∀ a ∈ l, p'.length.Coprime (polyOfBits a).natDegree := by
      intro a ha
      change (assemblyStep (u, p) g).2.length.Coprime _
      rw [hs.2]
      exact (hcop a (by simp [ha])).mul_left (hhead a ha)
    have hcap' : p'.length * (l.map (fun a => (polyOfBits a).natDegree)).prod ≤ u.length := by
      change (assemblyStep (u, p) g).2.length * _ ≤ _
      rw [hs.2]
      simpa only [List.map_cons, List.prod_cons, Nat.mul_assoc] using hcap
    have hout := ih p' hs.1 htail hpairs hcop' hcap'
    change Irreducible (polyOfBits ((l.foldl assemblyStep (u, p')).2 ++ [true])) ∧ _
    refine ⟨hout.1, ?_⟩
    change (l.foldl assemblyStep (u, p')).2.length = _
    rw [hout.2]
    change (assemblyStep (u, p) g).2.length * _ = _
    rw [hs.2]
    simp only [List.map_cons, List.prod_cons, Nat.mul_assoc]

private def assemblyStepProg : PolyTimeFun (AssemblyState × BitStr) AssemblyState :=
  let cap := fst.comp fst
  let p := snd.comp fst
  cap.pair (take.comp ((dropLastBitsProg.comp (normalizeBitsProg.comp
    (composedSumBitsProg.comp (p.pair snd)))).pair cap))

private theorem assemblyStepProg_apply (s : AssemblyState) (g : BitStr) :
    assemblyStepProg (s, g) = assemblyStep s g := by
  simp only [assemblyStepProg, comp_apply, pair_apply, fst_apply, snd_apply, take_apply,
    dropLastBitsProg_apply, normalizeBitsProg_apply, composedSumBitsProg_apply]
  rfl

private theorem assemblyStep_bounded : FoldBounded assemblyStepProg (5 * X + 5) := by
  intro l s pre post _
  have hstep : assemblyStepProg.step = assemblyStep := by
    funext a g
    exact assemblyStepProg_apply a g
  change esize (pre.foldl assemblyStepProg.step s) ≤ _
  rw [hstep]
  obtain ⟨hu, hp⟩ := fold_assemblyStep_shape pre s
  have he := esize_bitStr_le (pre.foldl assemblyStep s).2
  have hp0 := length_le_esize_bitStr s.2
  have hu0 := length_le_esize_list s.1
  have hs : esize s = esize s.1 + esize s.2 + 1 := rfl
  rw [esize_prod, hu]
  simp only [esize_prod, eval_add, eval_mul, eval_ofNat, eval_X]
  omega

/-- One uniform program assembles the supplied polynomial list with a global width cap. -/
def assembleBitsProg : PolyTimeFun (List BitStr × Unary × BitStr) BitStr :=
  snd.comp (foldl assemblyStepProg (5 * X + 5) assemblyStep_bounded)

/-- The bounded assembly program executes the specified fold. -/
theorem assembleBitsProg_apply (l : List BitStr) (u : Unary) (p : BitStr) :
    assembleBitsProg (l, u, p) = (l.foldl assemblyStep (u, p)).2 := by
  have hstep : assemblyStepProg.step = assemblyStep := by
    funext a g
    exact assemblyStepProg_apply a g
  change (l.foldl assemblyStepProg.step (u, p)).2 = _
  rw [hstep]

end MIPRE.LowDegree.BinaryPolynomial

end
