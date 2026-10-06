/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Lower

@[expose] public section

/-!
# The lower approximation is primitive recursive

`primrec_lowerSeq`: the numerators `lowerSeq T t` of Main Theorem I (1) are a primitive recursive
function of the test and the stage. `mainTheoremI_one` packages clause (1) of Main Theorem I
(I:592): a primitive recursive dyadic sequence, non-decreasing and tending to the sofic value.
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue Primrec Filter Topology

/-! ## Rewritings -/

theorem any_eq_foldr {α : Type*} (l : List α) (f : α → Bool) :
    l.any f = l.foldr (fun a b => f a || b) false := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem all_eq_foldr {α : Type*} (l : List α) (f : α → Bool) :
    l.all f = l.foldr (fun a b => f a && b) true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem length_filter_eq_foldr {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length = l.foldr (fun a n => if p a then n + 1 else n) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

theorem sum_eq_foldr (l : List ℕ) : l.sum = l.foldr (fun a n => a + n) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ## Primitive recursion -/

theorem primrec_two_pow : Primrec fun t : ℕ => 2 ^ t :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (const 2) Primrec.id

theorem primrec_nGen : Primrec SubgroupTestData.nGen :=
  fst.comp (Primrec.of_equiv (e := SubgroupTestData.equivTuple))

theorem primrec_challenges : Primrec SubgroupTestData.challenges :=
  snd.comp (Primrec.of_equiv (e := SubgroupTestData.equivTuple))

theorem primrec_totalWeight : Primrec SubgroupTestData.totalWeight := by
  have h : Primrec fun T : SubgroupTestData => ((T.challenges.map (·.1)).foldr
      (fun a n => a + n) 0) :=
    list_foldr (list_map primrec_challenges (fst.comp snd).to₂) (const 0)
      (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂
  exact h.of_eq fun T => by rw [SubgroupTestData.totalWeight, sum_eq_foldr]

theorem idxOf_nat (l : List ℕ) (a : ℕ) : l.idxOf a = @List.idxOf _ instBEqOfDecidableEq a l := by
  congr

theorem primrec_applyLetter :
    Primrec fun q : List (List ℕ) × Letter × ℕ => applyLetter q.1 q.2.1 q.2.2 := by
  have hrow : Primrec fun q : List (List ℕ) × Letter × ℕ => q.1.getD q.2.1.1 [] :=
    (list_getD []).comp fst (fst.comp (fst.comp snd))
  have hc : PrimrecPred fun q : List (List ℕ) × Letter × ℕ => q.2.1.1 < q.1.length :=
    nat_lt.comp (fst.comp (fst.comp snd)) (list_length.comp fst)
  have hidx : Primrec fun q : List (List ℕ) × Letter × ℕ => (q.1.getD q.2.1.1 []).idxOf q.2.2 :=
    (list_idxOf.comp (snd.comp snd) hrow).of_eq fun q => (idxOf_nat _ _).symm
  have hget : Primrec fun q : List (List ℕ) × Letter × ℕ => (q.1.getD q.2.1.1 []).getD q.2.2 0 :=
    (list_getD 0).comp hrow (snd.comp snd)
  exact (Primrec.ite hc (Primrec.cond (snd.comp (fst.comp snd)) hidx hget) (snd.comp snd)).of_eq
    fun q => by unfold applyLetter; cases q.2.1.2 <;> rfl

theorem primrec_applyWord :
    Primrec fun q : List (List ℕ) × Word × ℕ => applyWord q.1 q.2.1 q.2.2 :=
  list_foldr (fst.comp snd) (snd.comp snd)
    (primrec_applyLetter.comp ((fst.comp fst).pair snd)).to₂

/-- The arguments `(P, K, y, lit)` of `litC`. -/
abbrev LitArgs := List (List ℕ) × List Word × ℕ × (ℕ × Bool)

theorem primrec_litC : Primrec fun q : LitArgs => litC q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hlit : Primrec fun q : LitArgs => q.2.2.2 := snd.comp (snd.comp snd)
  have hK : Primrec fun q : LitArgs => q.2.1 := fst.comp snd
  have hy : Primrec fun q : LitArgs => q.2.2.1 := fst.comp (snd.comp snd)
  have hw : Primrec fun q : LitArgs => applyWord q.1 (q.2.1.getD q.2.2.2.1 []) q.2.2.1 :=
    primrec_applyWord.comp (fst.pair (((list_getD []).comp hK (fst.comp hlit)).pair hy))
  exact Primrec.and.comp (nat_lt.decide.comp (fst.comp hlit) (list_length.comp hK))
    (Primrec.beq.comp (Primrec.eq.decide.comp hw hy) (snd.comp hlit))

/-- The arguments `(P, K, cl, y)` of `passC`. -/
abbrev PassArgs := List (List ℕ) × List Word × List (List (ℕ × Bool)) × ℕ

theorem primrec_passC : Primrec fun q : PassArgs => passC q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  -- the literal, with `(q, c)` and then `((q, c), lit)` in context
  have hlit : Primrec₂ fun (x : PassArgs × List (ℕ × Bool)) (p : (ℕ × Bool) × Bool) =>
      litC x.1.1 x.1.2.1 x.1.2.2.2 p.1 && p.2 :=
    (Primrec.and.comp (primrec_litC.comp ((fst.comp (fst.comp fst)).pair
      ((fst.comp (snd.comp (fst.comp fst))).pair ((snd.comp (snd.comp (snd.comp (fst.comp fst)))).pair
        (fst.comp snd))))) (snd.comp snd)).to₂
  have hall : Primrec₂ fun (q : PassArgs) (p : List (ℕ × Bool) × Bool) =>
      (p.1.foldr (fun lit b => litC q.1 q.2.1 q.2.2.2 lit && b) true) || p.2 :=
    (Primrec.or.comp (list_foldr (fst.comp snd) (const true)
      (hlit.comp (fst.comp fst |>.pair (fst.comp (snd.comp fst))) snd).to₂) (snd.comp snd)).to₂
  refine (list_foldr (f := fun q : PassArgs => q.2.2.1) (fst.comp (snd.comp snd))
    (const false) hall).of_eq fun q => ?_
  unfold passC
  rw [any_eq_foldr]
  congr 1
  funext c b
  rw [all_eq_foldr]

/-- The arguments `(c, K, cl)` of `countC`. -/
abbrev CountArgs := ActCode × List Word × List (List (ℕ × Bool))

theorem primrec_countC : Primrec fun q : CountArgs => countC q.1 q.2.1 q.2.2 := by
  have hp : Primrec₂ fun (q : CountArgs) (p : ℕ × ℕ) =>
      if passC q.1.2 q.2.1 q.2.2 p.1 = true then p.2 + 1 else p.2 :=
    (Primrec.ite (Primrec.eq.comp (primrec_passC.comp ((snd.comp (fst.comp fst)).pair
      ((fst.comp (snd.comp fst)).pair ((snd.comp (snd.comp fst)).pair (fst.comp snd)))))
        (const true)) (succ.comp (snd.comp snd)) (snd.comp snd)).to₂
  refine (list_foldr (list_range.comp (fst.comp fst)) (const 0) hp).of_eq fun q => ?_
  rw [countC, length_filter_eq_foldr]

theorem primrec_numC : Primrec₂ numC := by
  have hm : Primrec₂ fun (q : SubgroupTestData × ActCode)
      (ch : ℕ × List Word × List (List (ℕ × Bool))) => ch.1 * countC q.2 ch.2.1 ch.2.2 :=
    (nat_mul.comp (fst.comp snd) (primrec_countC.comp ((snd.comp fst).pair
      ((fst.comp (snd.comp snd)).pair (snd.comp (snd.comp snd)))))).to₂
  have h : Primrec fun q : SubgroupTestData × ActCode =>
      ((q.1.challenges.map fun ch => ch.1 * countC q.2 ch.2.1 ch.2.2).foldr
        (fun a n => a + n) 0) :=
    list_foldr (list_map (primrec_challenges.comp fst) hm) (const 0)
      (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂
  exact h.to₂.of_eq fun T c => by rw [numC, sum_eq_foldr]

theorem primrecRel_mem : PrimrecRel fun (a : ℕ) (l : List ℕ) => a ∈ l :=
  ((PrimrecRel.exists_mem_list (Primrec.eq (α := ℕ))).comp snd fst).of_eq fun p => by simp

theorem primrecPred_validC : PrimrecPred fun q : ℕ × ActCode => ValidC q.1 q.2 := by
  have hR : PrimrecRel fun (p : List ℕ) (N : ℕ) =>
      p.length = N ∧ (∀ v ∈ p, v < N) ∧ ∀ y < N, y ∈ p :=
    PrimrecPred.and (Primrec.eq.comp (list_length.comp fst) snd)
      (PrimrecPred.and ((PrimrecRel.forall_mem_list nat_lt).comp fst snd)
        (((PrimrecRel.forall_mem_list primrecRel_mem).comp (list_range.comp snd) fst).of_eq
          fun p => by simp))
  exact PrimrecPred.and (nat_lt.comp (const 0) (fst.comp snd))
    (PrimrecPred.and (Primrec.eq.comp (list_length.comp (snd.comp snd)) fst)
      ((PrimrecRel.forall_mem_list hR).comp (snd.comp snd) (fst.comp snd)))

theorem primrec_lowerC :
    Primrec fun q : SubgroupTestData × ActCode × ℕ => lowerC q.1 q.2.1 q.2.2 := by
  have hv : PrimrecPred fun q : SubgroupTestData × ActCode × ℕ => ValidC q.1.nGen q.2.1 :=
    primrecPred_validC.comp ((primrec_nGen.comp fst).pair (fst.comp snd))
  exact Primrec.ite hv (nat_div.comp (nat_mul.comp (primrec_two_pow.comp (snd.comp snd))
      (primrec_numC.comp fst (fst.comp snd)))
    (nat_mul.comp (fst.comp (fst.comp snd)) (primrec_totalWeight.comp fst))) (const 0)

theorem primrec_lowerAt :
    Primrec fun q : SubgroupTestData × ℕ × ℕ => lowerAt q.1 q.2.1 q.2.2 := by
  refine (Primrec.option_casesOn (Primrec.decode.comp (fst.comp snd)) (const 0)
    (primrec_lowerC.comp ((fst.comp fst).pair (snd.pair (snd.comp (snd.comp fst))))).to₂).of_eq
      fun q => ?_
  unfold lowerAt
  cases Encodable.decode (α := ActCode) q.2.1 <;> rfl

/-- **The lower approximation is primitive recursive.** -/
theorem primrec_lowerSeq : Primrec₂ lowerSeq := by
  have hm : Primrec₂ fun (q : SubgroupTestData × ℕ) (n : ℕ) => lowerAt q.1 n q.2 :=
    (primrec_lowerAt.comp ((fst.comp fst).pair (snd.pair (snd.comp fst)))).to₂
  exact (list_foldr (list_map (list_range.comp (succ.comp snd)) hm) (const 0)
    (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂).to₂

/-- **Main Theorem I (1)** (I:592): a primitive recursive sequence of dyadic numbers
`α T t / 2^t`, non-decreasing in `t`, at most the sofic value and tending to it. -/
theorem mainTheoremI_one : ∃ α : SubgroupTestData → ℕ → ℕ, Primrec₂ α ∧ ∀ T : SubgroupTestData,
    Monotone (fun t => dyadic (α T t) t) ∧ (∀ t, dyadic (α T t) t ≤ T.valSof) ∧
      Tendsto (fun t => dyadic (α T t) t) atTop (𝓝 T.valSof) :=
  ⟨lowerSeq, primrec_lowerSeq, fun T => ⟨lowerSeq_monotone T, lowerSeq_le T, tendsto_lowerSeq T⟩⟩

end MIPRE.Tailored.Sofic.Measure

end
