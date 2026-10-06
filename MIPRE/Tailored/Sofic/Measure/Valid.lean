/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Local

@[expose] public section

/-!
# The upper approximation bounds the ergodic value

Paper I, the proof of Main Theorem I (2), first half (I:1196–1203): every IRS restricts to a point
of the polytope, so the polytope optimum is at least the ergodic value. Here the restriction of an
IRS `μ` to the stage words is a distribution `m` on patterns; it is carried by locally good
patterns, its marginals on the shorter words are conjugation invariant, and it computes the value
once the stage covers the challenge words. Rounding `m` to the grid of step `1/M`
(`exists_rounding`, an `ℓ¹` error at most `2P`) gives a feasible grid point whose value is within
`2P/M = 2/2^t` of `val(T, μ)` (`valOn_le_upperSeq`).
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue MeasureTheory

/-! ## Patterns of sets of words -/

/-- The sets of words with a given pattern on `J`. -/
def restrSet (J : List Word) (q : List Bool) : Set WordSpace := {A | J.map A = q}

theorem isClopen_restrSet (J : List Word) (q : List Bool) : IsClopen (restrSet J q) := by
  induction J generalizing q with
  | nil =>
    cases q with
    | nil => simp [restrSet, isClopen_univ]
    | cons b q => simp [restrSet, isClopen_empty]
  | cons w J ih =>
    cases q with
    | nil => simp [restrSet, isClopen_empty]
    | cons b q =>
      have : restrSet (w :: J) (b :: q) = {A | A w = b} ∩ restrSet J q := by
        ext A; simp [restrSet]
      rw [this]
      exact ((isClopen_discrete {b}).preimage (continuous_apply w)).inter (ih q)

theorem measurableSet_restrSet (J : List Word) (q : List Bool) : MeasurableSet (restrSet J q) :=
  (isClopen_restrSet J q).isOpen.measurableSet

/-- **The partition by patterns**: the measure of a set given by a pattern on `W` is the sum over
the patterns. -/
theorem measureReal_partition (ν : Measure WordSpace) [IsFiniteMeasure ν] (W : List Word)
    (Φ : List Bool → Bool) :
    ν.real {A | Φ (W.map A) = true} =
      ∑ p ∈ (allBits W.length).toFinset, if Φ p = true then ν.real (restrSet W p) else 0 := by
  classical
  rw [← Finset.sum_filter, ← measureReal_biUnion_finset]
  · congr 1
    ext A
    simp [restrSet, mem_allBits]
  · intro p _ p' _ hpp'
    exact Set.disjoint_left.2 fun A h h' => hpp' (h.symm.trans h')
  · exact fun p _ => measurableSet_restrSet W p

/-! ## Rounding to the grid -/

theorem abs_floor_sub_le {x : ℝ} (hx : 0 ≤ x) : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  rw [abs_le]; constructor <;> linarith

/-- **Rounding a distribution to the grid of step `1/M`**, with `ℓ¹` error at most twice the
number of points and no new support. -/
theorem exists_rounding {α : Type*} [DecidableEq α] (F : Finset α) (m : α → ℝ)
    (hm : ∀ p ∈ F, 0 ≤ m p) (h1 : ∑ p ∈ F, m p = 1) (M : ℕ) :
    ∃ nf : α → ℕ, ∑ p ∈ F, nf p = M ∧ (∀ p ∈ F, 0 < nf p → 0 < m p) ∧
      ∑ p ∈ F, |(nf p : ℝ) - M * m p| ≤ 2 * F.card := by
  obtain ⟨p₀, hp₀, hpos⟩ : ∃ p₀ ∈ F, 0 < m p₀ := by
    by_contra h
    push Not at h
    have : ∑ p ∈ F, m p ≤ 0 := Finset.sum_nonpos h
    linarith
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set S := ∑ p ∈ F.erase p₀, ⌊(M : ℝ) * m p⌋₊ with hSdef
  have hfl : ∀ p ∈ F.erase p₀, 0 ≤ (M : ℝ) * m p := fun p hp =>
    mul_nonneg hM (hm p (Finset.mem_of_mem_erase hp))
  have hS : (S : ℝ) ≤ ∑ p ∈ F.erase p₀, (M : ℝ) * m p := by
    rw [hSdef]; push_cast
    exact Finset.sum_le_sum fun p hp => Nat.floor_le (hfl p hp)
  have hsplit : (M : ℝ) = M * m p₀ + ∑ p ∈ F.erase p₀, (M : ℝ) * m p := by
    rw [← Finset.mul_sum, ← mul_add, Finset.add_sum_erase _ _ hp₀, h1, mul_one]
  have hSM : S ≤ M := by
    have : (S : ℝ) ≤ M := by nlinarith [mul_nonneg hM (hm p₀ hp₀)]
    exact_mod_cast this
  have hrest : ∀ p ∈ F.erase p₀, (if p = p₀ then M - S else ⌊(M : ℝ) * m p⌋₊) =
      ⌊(M : ℝ) * m p⌋₊ := fun p hp => ite_eq_right_of_eq_false _ _ (eq_false (Finset.ne_of_mem_erase hp))
  refine ⟨fun p => if p = p₀ then M - S else ⌊(M : ℝ) * m p⌋₊, ?_, ?_, ?_⟩
  · rw [← Finset.add_sum_erase _ _ hp₀, Finset.sum_congr rfl hrest, ite_eq_left rfl, ← hSdef]
    omega
  · intro p hp hpos'
    by_cases h : p = p₀
    · subst h; exact hpos
    · simp only [h, ite_false] at hpos'
      have h1' := Nat.floor_pos.1 hpos'
      by_contra hneg
      push Not at hneg
      nlinarith [hm p hp]
  · rw [← Finset.add_sum_erase _ _ hp₀]
    beta_reduce
    rw [ite_eq_left rfl, Finset.sum_congr rfl (fun p hp => by rw [hrest p hp])]
    have hr : ∑ p ∈ F.erase p₀, |(⌊(M : ℝ) * m p⌋₊ : ℝ) - M * m p| ≤ (F.erase p₀).card := by
      refine (Finset.sum_le_sum fun p hp => abs_floor_sub_le (hfl p hp)).trans ?_
      simp
    have hf : |((M - S : ℕ) : ℝ) - M * m p₀| ≤ (F.erase p₀).card := by
      rw [Nat.cast_sub hSM]
      have e : (M : ℝ) - S - M * m p₀ =
          ∑ p ∈ F.erase p₀, ((M : ℝ) * m p - ⌊(M : ℝ) * m p⌋₊) := by
        rw [Finset.sum_sub_distrib, hSdef]; push_cast; linarith
      rw [e, abs_of_nonneg (Finset.sum_nonneg fun p hp => by
        linarith [Nat.floor_le (hfl p hp)])]
      refine (Finset.sum_le_sum fun p hp => ?_).trans (by simp : ∑ p ∈ F.erase p₀, (1 : ℝ) ≤ _)
      linarith [Nat.lt_floor_add_one ((M : ℝ) * m p)]
    have hc : ((F.erase p₀).card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_erase_le
    linarith

/-- Summing over the values of a key. -/
theorem sum_ite_key {α β : Type*} [DecidableEq β] (F : Finset α) (G : Finset β) (key : α → β)
    (hk : ∀ p ∈ F, key p ∈ G) (c : α → ℝ) :
    ∑ q ∈ G, ∑ p ∈ F, (if key p = q then c p else 0) = ∑ p ∈ F, c p := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p hp => by rw [Finset.sum_ite_eq, ite_eq_left (hk p hp)]

/-- **The invariance error of a rounding** is at most twice its `ℓ¹` error. -/
theorem sum_abs_cnt_le {α β : Type*} [DecidableEq β] (F : Finset α) (G : Finset β)
    (key key' : α → β) (hk : ∀ p ∈ F, key p ∈ G) (hk' : ∀ p ∈ F, key' p ∈ G) (a b : α → ℝ)
    (hb : ∀ q ∈ G, ∑ p ∈ F, (if key p = q then b p else 0) =
      ∑ p ∈ F, (if key' p = q then b p else 0)) :
    ∑ q ∈ G, |∑ p ∈ F, (if key p = q then a p else 0) - ∑ p ∈ F, (if key' p = q then a p else 0)|
      ≤ 2 * ∑ p ∈ F, |a p - b p| := by
  have h : ∀ q ∈ G, |∑ p ∈ F, (if key p = q then a p else 0) -
      ∑ p ∈ F, (if key' p = q then a p else 0)| ≤
      ∑ p ∈ F, (if key p = q then |a p - b p| else 0) +
        ∑ p ∈ F, (if key' p = q then |a p - b p| else 0) := by
    intro q hq
    have e : ∑ p ∈ F, (if key p = q then a p else 0) - ∑ p ∈ F, (if key' p = q then a p else 0) =
        ∑ p ∈ F, (if key p = q then a p - b p else 0) -
          ∑ p ∈ F, (if key' p = q then a p - b p else 0) := by
      have h1 : ∀ k : α → β, ∑ p ∈ F, (if k p = q then a p - b p else 0) =
          ∑ p ∈ F, (if k p = q then a p else 0) - ∑ p ∈ F, (if k p = q then b p else 0) := by
        intro k
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      rw [h1, h1, hb q hq]; ring
    rw [e]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;>
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, sum_ite_key F G key hk, sum_ite_key F G key' hk']
  ring

/-! ## Lists as finite sums -/

theorem zip_map_self {α β : Type*} (f : α → β) (l : List α) :
    (l.map f).zip l = l.map fun p => (f p, p) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cntR_map {Pt : List (List Bool)} (hPt : Pt.Nodup) (nf : List Bool → ℕ)
    (f : List Bool → Bool) :
    (cntR (Pt.map nf) Pt f : ℝ) = ∑ p ∈ Pt.toFinset, if f p = true then (nf p : ℝ) else 0 := by
  rw [cntR, zip_map_self, List.map_map, Nat.cast_list_sum, List.map_map,
    ← List.sum_toFinset _ hPt]
  exact Finset.sum_congr rfl fun p _ => by simp only [Function.comp_apply]; split_ifs <;> simp

/-! ## The restriction of an IRS -/

section Restriction

variable (T : SubgroupTestData) (t : ℕ)

theorem mem_stageW {u : Word} : u ∈ stageW T t ↔ u.length ≤ t + 2 ∧ ∀ l ∈ u, l.1 < T.nGen + t :=
  mem_wordsUpTo

theorem stageD_sub {u : Word} (hu : u ∈ stageD T t) : u ∈ stageW T t := by
  rw [stageD, mem_wordsUpTo] at hu
  exact (mem_stageW T t).2 ⟨by omega, hu.2⟩

theorem conj_mem_stageW {g : Letter} (hg : g.1 < T.nGen) {u : Word} (hu : u ∈ stageD T t) :
    invW [g] ++ u ++ [g] ∈ stageW T t := by
  rw [stageD, mem_wordsUpTo] at hu
  rw [mem_stageW]
  refine ⟨by simp [invW]; omega, fun l hl => ?_⟩
  have hu2 := hu.2
  simp only [invW, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | hl) | rfl
  · simp only; omega
  · have := hu2 l hl; omega
  · omega

/-- The pattern on the stage of the image of a set of words, on the comparison words. -/
theorem stageD_map_extW (A : WordSpace) :
    (stageD T t).map (extW (stageW T t) ((stageW T t).map A)) = (stageD T t).map A :=
  List.map_congr_left fun _ hu => extW_map A (stageD_sub T t hu)

theorem stageD_map_conjW {g : Letter} (hg : g.1 < T.nGen) (A : WordSpace) :
    (stageD T t).map (conjW g (extW (stageW T t) ((stageW T t).map A))) =
      (stageD T t).map (conjW g A) :=
  List.map_congr_left fun _ hu => extW_map A (conj_mem_stageW T t hg hu)

end Restriction

/-- A weighted sum of pointwise bounds. -/
theorem list_weighted_bound {α : Type*} (l : List α) (w a b : α → ℝ) (E : ℝ)
    (hw : ∀ x ∈ l, 0 ≤ w x) (h : ∀ x ∈ l, |a x - b x| ≤ E) :
    (l.map fun x => w x * a x).sum - E * (l.map w).sum ≤ (l.map fun x => w x * b x).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := ih (fun y hy => hw y (by simp [hy])) (fun y hy => h y (by simp [hy]))
    have h2 := abs_le.1 (h x (by simp))
    have h3 := hw x (by simp)
    nlinarith [h2.1]

/-! ## Validity -/

theorem ceilDiv_ge {x D : ℕ} (hD : 0 < D) : (x : ℝ) / D ≤ ceilDiv x D := by
  rw [div_le_iff₀ (by exact_mod_cast hD)]
  exact_mod_cast (ceilDiv_spec (x := x) hD).1

theorem stagePt_nodup (T : SubgroupTestData) (t : ℕ) : (stagePt T t).Nodup := nodup_allBits _

theorem stageP_eq_card (T : SubgroupTestData) (t : ℕ) :
    stageP T t = (stagePt T t).toFinset.card := by
  rw [stageP, List.toFinset_card_of_nodup (stagePt_nodup T t)]

/-- **The rounding of an IRS**: a feasible grid point whose value is within `2P/M` of the IRS's
once the stage covers the challenge words. -/
theorem exists_feasible_of_irs (T : SubgroupTestData) (t : ℕ)
    {μ : ProbabilityMeasure (SubgroupSpace T.nGen)} (hμ : μ ∈ IRS T.nGen) :
    ∃ n ∈ allVecs (stageP T t) (stageM T t), Feasible T t n ∧ (Covers T t → 0 < T.totalWeight →
      (stageM T t : ℝ) * T.totalWeight * T.valOn μ - 2 * stageP T t * T.totalWeight ≤
        numG T t n) := by
  classical
  set W := stageW T t
  set D := stageD T t
  set Pt := stagePt T t
  set P := stageP T t
  set M := stageM T t
  set Wt := T.totalWeight
  set F := Pt.toFinset
  set ν₀ : Measure WordSpace := (μ : Measure (SubgroupSpace T.nGen)).map (wordEval T.nGen)
  have : IsProbabilityMeasure ν₀ := inferInstance
  set m : List Bool → ℝ := fun p => ν₀.real (restrSet W p)
  have hPt : Pt.Nodup := stagePt_nodup T t
  -- the restriction is a distribution
  have hm0 : ∀ p ∈ F, 0 ≤ m p := fun p _ => measureReal_nonneg
  have hm1 : ∑ p ∈ F, m p = 1 := by
    have := measureReal_partition ν₀ W (fun _ => true)
    simp only [Set.ofPred_true, probReal_univ, ite_true] at this
    exact this.symm
  obtain ⟨nf, hsum, hpos, herr⟩ := exists_rounding F m hm0 hm1 M
  set n := Pt.map nf
  have hcard : (F.card : ℝ) = P := by exact_mod_cast (stageP_eq_card T t).symm
  -- the grid point
  have hnmem : n ∈ allVecs P M := by
    rw [mem_allVecs]
    refine ⟨by simp only [n, List.length_map]; rfl, fun a ha => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (List.mem_toFinset.2 hp)
  have hnsum : n.sum = M := by
    rw [← hsum, List.sum_toFinset _ hPt]
  -- support
  have hgood : ∀ x ∈ n.zip Pt, 0 < x.1 → goodP T.nGen W x.2 = true := by
    intro x hx hx1
    rw [zip_map_self] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have hmp := hpos p (List.mem_toFinset.2 hp) hx1
    have hne : ν₀ (restrSet W p) ≠ 0 := by
      intro h0; simp [m, measureReal_def, h0] at hmp
    rw [Measure.map_apply (measurable_wordEval T.nGen) (measurableSet_restrSet W p)] at hne
    obtain ⟨H, hH⟩ := nonempty_of_measure_ne_zero hne
    simp only [Set.mem_preimage, restrSet, Set.mem_ofPred_eq] at hH
    rw [← hH]
    exact goodP_map (wordEval_mem_good H)
  -- invariance
  have hinv : ∀ g ∈ letters T.nGen, invErr T t g n ≤ 4 * P := by
    intro g hg
    have hg' : g.1 < T.nGen := mem_letters.1 hg
    set G := (allBits D.length).toFinset
    have hkey : ∀ p ∈ F, D.map (extW W p) ∈ G := fun p _ => by simp [G, mem_allBits]
    have hkey' : ∀ p ∈ F, D.map (conjW g (extW W p)) ∈ G := fun p _ => by simp [G, mem_allBits]
    have hb : ∀ q ∈ G, ∑ p ∈ F, (if D.map (extW W p) = q then (M : ℝ) * m p else 0) =
        ∑ p ∈ F, (if D.map (conjW g (extW W p)) = q then (M : ℝ) * m p else 0) := by
      intro q _
      have hD : ∀ A : WordSpace, D.map (extW W (W.map A)) = D.map A := stageD_map_extW T t
      have hC : ∀ A : WordSpace, D.map (conjW g (extW W (W.map A))) = D.map (conjW g A) :=
        stageD_map_conjW T t hg'
      have h1 : ν₀.real {A | (D.map (extW W (W.map A)) == q) = true} =
          ∑ p ∈ F, if (D.map (extW W p) == q) = true then m p else 0 :=
        measureReal_partition ν₀ W (fun p => D.map (extW W p) == q)
      have h2 : ν₀.real {A | (D.map (conjW g (extW W (W.map A))) == q) = true} =
          ∑ p ∈ F, if (D.map (conjW g (extW W p)) == q) = true then m p else 0 :=
        measureReal_partition ν₀ W (fun p => D.map (conjW g (extW W p)) == q)
      simp only [beq_iff_eq, hD, hC] at h1 h2
      have h3 : ν₀.real {A | D.map (conjW g A) = q} = ν₀.real {A | D.map A = q} := by
        have : {A : WordSpace | D.map (conjW g A) = q} = conjW g ⁻¹' restrSet D q := rfl
        rw [this, ← map_measureReal_apply (measurable_conjW g) (measurableSet_restrSet D q)]
        rw [map_wordEval_conjW hμ g]; rfl
      have e : ∀ k : List Bool → List Bool, ∑ p ∈ F, (if k p = q then (M : ℝ) * m p else 0) =
          M * ∑ p ∈ F, (if k p = q then m p else 0) := fun k => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
      rw [e, e, ← h1, ← h2, h3]
    have key := sum_abs_cnt_le F G _ _ hkey hkey' (fun p => (nf p : ℝ)) (fun p => M * m p) hb
    have hcnt : ∀ f, (cntR n Pt f : ℝ) = ∑ p ∈ F, if f p = true then (nf p : ℝ) else 0 :=
      fun f => cntR_map hPt nf f
    have hreal : (invErr T t g n : ℝ) ≤ 4 * P := by
      show (((allBits D.length).map fun q => ndist (cntR n Pt fun p => D.map (extW W p) == q)
        (cntR n Pt fun p => D.map (conjW g (extW W p)) == q)).sum : ℕ) ≤ (4 * P : ℝ)
      rw [Nat.cast_list_sum, List.map_map, ← List.sum_toFinset _ (nodup_allBits _)]
      simp only [Function.comp_apply, ndist_cast, hcnt, beq_iff_eq]
      refine key.trans ?_
      rw [hcard] at herr; linarith
    exact_mod_cast hreal
  have hfeas : Feasible T t n := ⟨hnsum, hgood, hinv⟩
  -- the value
  refine ⟨n, hnmem, hfeas, fun hcov hW => ?_⟩
  · have hWt : (Wt : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
    have hpass : ∀ ch ∈ T.challenges, ν₀.real (passSetW id ch.2.1 ch.2.2) =
        ∑ p ∈ F, if passW ch.2.1 ch.2.2 (extW W p) = true then m p else 0 := by
      intro ch hch
      have h : ν₀.real {A | passW ch.2.1 ch.2.2 (extW W (W.map A)) = true} =
          ∑ p ∈ F, if passW ch.2.1 ch.2.2 (extW W p) = true then m p else 0 :=
        measureReal_partition ν₀ W (fun p => passW ch.2.1 ch.2.2 (extW W p))
      rw [← h]
      congr 1
      ext A
      simp only [passSetW, id, Set.mem_ofPred_eq]
      rw [passW_congr ch.2.2 (fun k hk => (extW_map A (hcov ch hch k hk)))]
    have hcnt : ∀ f, (cntR n Pt f : ℝ) = ∑ p ∈ F, if f p = true then (nf p : ℝ) else 0 :=
      fun f => cntR_map hPt nf f
    have hv : T.valOn μ = (T.challenges.map fun ch =>
        (ch.1 : ℝ) * ν₀.real (passSetW id ch.2.1 ch.2.2)).sum / Wt := by
      rw [valOn_eq_valΩ]; rfl
    have hn : (numG T t n : ℝ) = (T.challenges.map fun ch =>
        (ch.1 : ℝ) * (cntR n Pt fun p => passW ch.2.1 ch.2.2 (extW W p) : ℝ)).sum := by
      unfold numG
      rw [Nat.cast_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro ch _
      simp only [Function.comp_apply, Nat.cast_mul]
      rfl
    have hWs : (Wt : ℝ) = (T.challenges.map fun ch => (ch.1 : ℝ)).sum := by
      show (((T.challenges.map (·.1)).sum : ℕ) : ℝ) = _
      rw [Nat.cast_list_sum, List.map_map]
      rfl
    have hb := list_weighted_bound T.challenges (fun ch => (ch.1 : ℝ))
      (fun ch => M * ν₀.real (passSetW id ch.2.1 ch.2.2))
      (fun ch => (cntR n Pt fun p => passW ch.2.1 ch.2.2 (extW W p) : ℝ)) (2 * P)
      (fun _ _ => Nat.cast_nonneg _) (fun ch hch => by
        rw [hpass ch hch, hcnt, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun p _ => ?_).trans (herr.trans (by rw [hcard]))
        split_ifs <;> simp [abs_sub_comm])
    rw [hv, hn, mul_assoc, mul_div_cancel₀ _ hWt, hWs]
    have e1 : (M : ℝ) * (T.challenges.map fun ch =>
        (ch.1 : ℝ) * ν₀.real (passSetW id ch.2.1 ch.2.2)).sum = (T.challenges.map fun ch =>
          (ch.1 : ℝ) * (M * ν₀.real (passSetW id ch.2.1 ch.2.2))).sum := by
      rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro ch _; ring
    rw [e1]; linarith [hb]

/-- **Every IRS is below the upper approximation.** -/
theorem valOn_le_upperSeq (T : SubgroupTestData) (t : ℕ)
    {μ : ProbabilityMeasure (SubgroupSpace T.nGen)} (hμ : μ ∈ IRS T.nGen) :
    T.valOn μ ≤ dyadic (upperSeq T t) t := by
  classical
  unfold upperSeq
  split_ifs with hcov
  swap
  · rw [dyadic, Nat.cast_pow, Nat.cast_two, div_self (by positivity)]
    exact T.valOn_le_one μ
  rcases Nat.eq_zero_or_pos T.totalWeight with hW | hW
  · have : T.valOn μ = 0 := by
      simp [SubgroupTestData.valOn, valGen, hW]
    rw [this]; exact dyadic_nonneg _ _
  obtain ⟨n, hnmem, hfeas, hval⟩ := exists_feasible_of_irs T t hμ
  have hval := hval hcov hW
  set P := stageP T t
  set M := stageM T t
  set Wt := T.totalWeight
  -- the bound
  have hmax : numG T t n ≤ maxNum T t :=
    le_foldr_max (List.mem_map.2 ⟨n, List.mem_filter.2 ⟨hnmem, by simpa using hfeas⟩, rfl⟩)
  have hMW : (0 : ℝ) < M * Wt := by
    have := stageM_pos T t
    positivity
  have hceil := ceilDiv_ge (x := 2 ^ t * (maxNum T t + 2 * P * Wt)) (D := M * Wt)
    (by have := stageM_pos T t; positivity)
  unfold dyadic
  rw [le_div_iff₀ (by positivity)]
  refine le_trans ?_ hceil
  rw [le_div_iff₀ (by exact_mod_cast hMW)]
  push_cast
  have : (numG T t n : ℝ) ≤ maxNum T t := by exact_mod_cast hmax
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) t]

end MIPRE.Tailored.Sofic.Measure

end
