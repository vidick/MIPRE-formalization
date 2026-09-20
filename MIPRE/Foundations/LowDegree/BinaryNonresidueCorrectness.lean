/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.LowDegree.BinaryNonresidueLoop
import MIPRE.Foundations.LowDegree.BinaryFactorizationCanonical
import MIPRE.Foundations.LowDegree.BinaryPrimePowerBounds
import MIPRE.Foundations.LowDegree.BinaryKummerComposition

/-! # Correctness of the bounded odd-prime auxiliary construction -/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Polynomial

/-- The executable loop's invariant, including the primitive-order progress counter. -/
structure NonresidueInvariant (q m i : ℕ) (s : NonresidueState) : Prop where
  exponent : s.1.length + 1 = q
  cap : s.2.1.length = m + 1
  canonical : s.2.2.2.getLastD false = true
  irreducible : Irreducible (polyOfBits s.2.2.2)
  degree : (polyOfBits s.2.2.2).natDegree = m
  stopped : s.2.2.1 = true →
    ∀ b : AdjoinRoot (polyOfBits s.2.2.2), b ^ q ≠ AdjoinRoot.root (polyOfBits s.2.2.2)
  running : s.2.2.1 = false → polyOfBits s.2.2.2 ∣ cyclotomic (q ^ (i + 1)) (ZMod 2)

/-- The exact specification of the factorization query made by a valid running state. -/
theorem liftCandidates_spec (q m i : ℕ) (s : NonresidueState)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s)
    (hd : s.2.2.1 = false) :
    liftCandidates s ≠ [] ∧
    ((liftCandidates s).map polyOfBits).prod = (polyOfBits s.2.2.2).comp (X ^ q) ∧
    (∀ b ∈ liftCandidates s, b.getLastD false = true ∧
      (polyOfBits b).Monic ∧ Irreducible (polyOfBits b)) ∧
    ((liftCandidates s).tail.isEmpty = true ↔
      Irreducible ((polyOfBits s.2.2.2).comp (X ^ q))) := by
  let a := substitutePowerBits s.2.2.2 s.1
  have he : polyOfBits a = (polyOfBits s.2.2.2).comp (X ^ q) := by
    rw [polyOfBits_substitutePowerBits, hv.exponent]
  have hm := (monic_polyOfBits_of_getLast _ hv.canonical).comp (monic_X.pow q)
    (by simpa using hq.ne_zero)
  have hcan : a.getLastD false = true := by
    rcases normalizeBits_getLast (s.2.2.2.flatMap
      (fun b => b :: List.replicate s.1.length false)) with hn | hn
    · change a = [] at hn
      have hzero : polyOfBits a = 0 := by rw [hn]; simp [polyOfBits]
      rw [he] at hzero
      exact (hm.ne_zero hzero).elim
    · exact hn
  have hp : 0 < (polyOfBits a).natDegree := by
    rw [he, natDegree_comp, natDegree_X_pow]
    exact Nat.mul_pos hv.irreducible.natDegree_pos hq.pos
  have hs : Squarefree (polyOfBits a) := by
    rw [he]
    exact squarefree_comp_power_of_dvd_cyclotomic _ q (i + 1) hq hq2 (hv.running hd)
  refine ⟨BinaryQuotient.factor_dropLast_ne_nil a hcan hp hs, ?_,
    BinaryQuotient.factor_dropLast_factors a hcan hp hs, ?_⟩
  · exact (BinaryQuotient.factor_dropLast_prod a hcan hp hs).trans he
  · rw [← he]
    exact BinaryQuotient.factor_dropLast_tail_isEmpty_iff a hcan hp hs

/-- On a nonterminal query, the selected factor has precisely the seed degree. -/
theorem liftCandidates_degree (q m i : ℕ) (s : NonresidueState)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s)
    (hd : s.2.2.1 = false) (ht : (liftCandidates s).tail.isEmpty = false) :
    ∀ b ∈ liftCandidates s, (polyOfBits b).natDegree = m := by
  let f := polyOfBits s.2.2.2
  have hf : f.Monic := monic_polyOfBits_of_getLast _ hv.canonical
  have hi : Irreducible f := hv.irreducible
  let : Fact (Irreducible f) := ⟨hi⟩
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (BinaryQuotient.coordinateEquiv f hf).symm.toEquiv
  have hs := liftCandidates_spec q m i s hq hq2 hv hd
  have hred : ¬ Irreducible (f.comp (X ^ q)) := by
    intro h
    have htrue := hs.2.2.2.mpr h
    rw [ht] at htrue
    contradiction
  obtain ⟨z, hz⟩ := residue_of_not_irreducible_comp f hf hi q hq hq2 hred
  let : NeZero ((q ^ (i + 1) : ℕ) : ZMod 2) :=
    ⟨oddPrimePower_cast_ne_zero q (i + 1) hq hq2⟩
  let : NeZero ((q ^ (i + 1) : ℕ) : AdjoinRoot f) :=
    NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot f)).injective
  have hr : IsPrimitiveRoot (AdjoinRoot.root f) (q ^ (i + 1)) :=
    primitiveRoot_of_aeval_dvd_cyclotomic f _ (hv.running hd) _ (by simp)
  have hcard : Fintype.card (AdjoinRoot f) = Nat.card (ZMod 2) ^ f.natDegree := by
    rw [← Nat.card_eq_fintype_card, card_adjoinRoot_binary f hf]
    simp
  have hqdiv : q ∣ Fintype.card (AdjoinRoot f) - 1 := by
    have hpdiv := primitive_root_order_dvd_card f hf hi (q ^ (i + 1))
      (pow_ne_zero _ hq.ne_zero) hr
    have hdq := (dvd_pow_self q (by omega : i + 1 ≠ 0)).trans hpdiv
    simpa only [← Nat.card_eq_fintype_card, card_adjoinRoot_binary f hf] using hdq
  intro b hb
  have hbdiv : polyOfBits b ∣ f.comp (X ^ q) := by
    rw [← hs.2.1]
    exact List.dvd_prod (List.mem_map.mpr ⟨b, hb, rfl⟩)
  exact (residue_factor_natDegree f (polyOfBits b) hf hi (hs.2.2.1 b hb).2.2
    hcard (AdjoinRoot.root f) z (by simp) (hr.ne_zero (pow_ne_zero _ hq.ne_zero))
    q hqdiv hz hbdiv).trans hv.degree

set_option maxHeartbeats 1000000 in
/-- Every executable step either certifies a nonresidue or advances primitive order. -/
theorem nonresidueStep_invariant (q m i : ℕ) (s : NonresidueState) (b : Bool)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s) :
    NonresidueInvariant q m (i + 1) (nonresidueStep s b) := by
  cases hd : s.2.2.1 with
  | true =>
    rw [nonresidueStep_done s b hd]
    exact ⟨hv.exponent, hv.cap, hv.canonical, hv.irreducible, hv.degree,
      hv.stopped, by intro h; rw [hd] at h; contradiction⟩
  | false =>
    have hs := liftCandidates_spec q m i s hq hq2 hv hd
    cases ht : (liftCandidates s).tail.isEmpty with
    | true =>
      have he : nonresidueStep s b = (s.1, s.2.1, true, s.2.2.2) := by
        simp [nonresidueStep, hd, ht]
      rw [he]
      refine ⟨hv.exponent, hv.cap, hv.canonical, hv.irreducible, hv.degree, ?_,
        by intro h; contradiction⟩
      intro _
      let f := polyOfBits s.2.2.2
      let : Fact (Irreducible f) := ⟨hv.irreducible⟩
      let : Module.Finite (ZMod 2) (AdjoinRoot f) :=
        (AdjoinRoot.powerBasis hv.irreducible.ne_zero).finite
      exact nonresidue_of_irreducible_comp f (monic_polyOfBits_of_getLast _ hv.canonical)
        (AdjoinRoot.powerBasis hv.irreducible.ne_zero).finrank hv.irreducible.natDegree_pos
        q hq.one_lt (AdjoinRoot.root f) (by simp) (hs.2.2.2.mp ht)
    | false =>
      let a := (liftCandidates s).headD []
      have ha : a ∈ liftCandidates s := by
        cases hl : liftCandidates s with
        | nil => exact (hs.1 hl).elim
        | cons c l => simp [a, hl]
      have hac := hs.2.2.1 a ha
      have had := liftCandidates_degree q m i s hq hq2 hv hd ht a ha
      have hal : a.length = m + 1 := by
        rw [← natDegree_add_one_of_getLast a hac.1, had]
      have htake : a.take s.2.1.length = a := by
        apply List.take_of_length_le
        rw [hal, hv.cap]
      have he : nonresidueStep s b = (s.1, s.2.1, false, a) := by
        simp only [nonresidueStep, hd, ht, Bool.false_eq_true, if_false]
        change (s.1, s.2.1, false, a.take s.2.1.length) = (s.1, s.2.1, false, a)
        rw [htake]
      rw [he]
      refine ⟨hv.exponent, hv.cap, hac.1, hac.2.2, had, by intro h; contradiction, ?_⟩
      intro _
      apply lifted_factor_dvd_cyclotomic _ _ q (i + 1) hq hq2 (by omega) hac.2.2
        (hv.running hd)
      rw [← hs.2.1]
      exact List.dvd_prod (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- The bounded loop preserves its invariant with one progress count per fuel bit. -/
theorem fold_nonresidueStep_invariant (l : BitStr) (q m i : ℕ) (s : NonresidueState)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s) :
    NonresidueInvariant q m (i + l.length) (l.foldl nonresidueStep s) := by
  induction l generalizing i s with
  | nil => simpa using hv
  | cons b l ih =>
    have h := ih (i + 1) (nonresidueStep s b)
      (nonresidueStep_invariant q m i s b hq hq2 hv)
    simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 l.length] using h

/-- A valid state cannot still be running after the seed-degree budget is exhausted. -/
theorem nonresidueInvariant_stopped (q m i : ℕ) (s : NonresidueState)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s) (hi : m ≤ i) :
    s.2.2.1 = true := by
  by_contra hd
  have hd' : s.2.2.1 = false := Bool.eq_false_iff.mpr hd
  let f := polyOfBits s.2.2.2
  have hf : f.Monic := monic_polyOfBits_of_getLast _ hv.canonical
  let : Fact (Irreducible f) := ⟨hv.irreducible⟩
  let : NeZero ((q ^ (i + 1) : ℕ) : ZMod 2) :=
    ⟨oddPrimePower_cast_ne_zero q (i + 1) hq hq2⟩
  let : NeZero ((q ^ (i + 1) : ℕ) : AdjoinRoot f) :=
    NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot f)).injective
  have hr : IsPrimitiveRoot (AdjoinRoot.root f) (q ^ (i + 1)) :=
    primitiveRoot_of_aeval_dvd_cyclotomic f _ (hv.running hd') _ (by simp)
  have hb := prime_power_lift_bound f hf hv.irreducible q (i + 1) hq hr
  change i + 1 ≤ (polyOfBits s.2.2.2).natDegree at hb
  rw [hv.degree] at hb
  omega

/-- The initial seed uses exactly its degree plus one coefficients. -/
theorem cyclotomicSeedBits_canonical (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    (cyclotomicSeedBits (unary q)).getLastD false = true := by
  have hi := (cyclotomicSeedBits_correct q hq hq2).2.1
  cases hl : BinaryQuotient.factorBitsProg (cyclotomicLowerBits (unary q)) with
  | nil =>
    have he : cyclotomicSeedBits (unary q) = [] := by unfold cyclotomicSeedBits; rw [hl]; rfl
    exact (hi.ne_zero (by rw [he]; simp [polyOfBits])).elim
  | cons a l =>
    have hcan := BinaryQuotient.factorBitsProg_canonical (cyclotomicLowerBits (unary q))
      a (by rw [hl]; exact List.mem_cons_self)
    have he : cyclotomicSeedBits (unary q) = a := by unfold cyclotomicSeedBits; rw [hl]; rfl
    rw [he] at hi ⊢
    rcases hcan with hn | hn
    · exact (hi.ne_zero (by rw [hn]; simp [polyOfBits])).elim
    · exact hn

/-- Explicit execution of the seed-initialized auxiliary loop. -/
theorem nonresidueLiftStateProg_apply (u : Unary) :
    nonresidueLiftStateProg u = (cyclotomicSeedBits u).tail.foldl nonresidueStep
      (u.tail, unary (cyclotomicSeedBits u).length, false, cyclotomicSeedBits u) := by
  simp only [nonresidueLiftStateProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.tail_apply,
    Cost.PolyTimeFun.length_apply, Cost.PolyTimeFun.const_apply,
    cyclotomicSeedBitsProg_apply, nonresidueLoopProg_apply]

/-- The polynomial-time auxiliary constructor returns a monic irreducible polynomial
of the seed degree whose specified root is an odd-prime nonresidue. -/
theorem nonresidueLiftBitsProg_correct (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let f := polyOfBits (nonresidueLiftBitsProg (unary q))
    (nonresidueLiftBitsProg (unary q)).getLastD false = true ∧
    f.Monic ∧ Irreducible f ∧
    f.natDegree = (polyOfBits (cyclotomicSeedBits (unary q))).natDegree ∧
    ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f := by
  let a := cyclotomicSeedBits (unary q)
  let m := (polyOfBits a).natDegree
  let s : NonresidueState := ((unary q).tail, unary a.length, false, a)
  have ha := cyclotomicSeedBits_canonical q hq hq2
  have hc := cyclotomicSeedBits_correct q hq hq2
  have hlen : a.length = m + 1 := (natDegree_add_one_of_getLast a ha).symm
  have hv : NonresidueInvariant q m 0 s := by
    refine ⟨?_, ?_, ha, hc.2.1, rfl, by intro h; contradiction, ?_⟩
    · change (unary q).tail.length + 1 = q
      rw [List.length_tail, length_unary]
      exact Nat.sub_add_cancel hq.one_le
    · change (unary a.length).length = m + 1
      rw [length_unary, hlen]
    · intro _
      simpa only [Nat.zero_add, pow_one] using hc.2.2
  have hvf := fold_nonresidueStep_invariant a.tail q m 0 s hq hq2 hv
  have hbudget : a.tail.length = m := by rw [List.length_tail, hlen]; omega
  have hdone := nonresidueInvariant_stopped q m (0 + a.tail.length)
    (a.tail.foldl nonresidueStep s) hq hq2 hvf (by omega)
  have hout : nonresidueLiftBitsProg (unary q) =
      (a.tail.foldl nonresidueStep s).2.2.2 := by
    simp only [nonresidueLiftBitsProg, Cost.PolyTimeFun.comp_apply,
      Cost.PolyTimeFun.snd_apply, nonresidueLiftStateProg_apply]
    rfl
  dsimp only
  rw [hout]
  exact ⟨hvf.canonical, monic_polyOfBits_of_getLast _ hvf.canonical,
    hvf.irreducible, hvf.degree, hvf.stopped hdone⟩

/-- The auxiliary degree is exactly the multiplicative order of two modulo the prime. -/
theorem nonresidueLiftBits_order (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    orderOf (2 : ZMod q) = (polyOfBits (nonresidueLiftBitsProg (unary q))).natDegree := by
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  rw [(nonresidueLiftBitsProg_correct q hq hq2).2.2.2.1,
    cyclotomicSeedBits_natDegree q hq hq2 hcop, ← orderOf_units, ZMod.coe_unitOfCoprime]
  simp

/-- The auxiliary degree is coprime to the requested odd prime. -/
theorem nonresidueLiftBits_degree_coprime (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    q.Coprime (polyOfBits (nonresidueLiftBitsProg (unary q))).natDegree := by
  rw [(nonresidueLiftBitsProg_correct q hq hq2).2.2.2.1]
  exact (cyclotomicSeedBits_degree_coprime q hq hq2).symm

end MIPRE.LowDegree.BinaryPolynomial
