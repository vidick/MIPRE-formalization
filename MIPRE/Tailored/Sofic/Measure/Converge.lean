/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.Limit

@[expose] public section

/-!
# The upper approximation converges to the ergodic value

Paper I, the proof of Main Theorem I (2), clause (3) (I:1204–1217). A feasible grid point is a
probability measure on sets of words (`liftMeasure`, the distribution `n/M` on the sets of words
of the patterns). For the best feasible grid point at each stage, these measures satisfy the
hypotheses of `eventually_valΩ_le`: a locally good pattern avoids the bad sets within the stage
(`extW_not_mem_badSet`), and the invariance error bounds the change of the measure of a cylinder
under conjugation (`abs_lift_cyl_sub_le`). Their values are within `2/2^t` of the polytope
optimum, so the upper approximation tends to the ergodic value (`tendsto_upperSeq`).
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue MeasureTheory Filter Topology

/-! ## Grid points as measures -/

/-- The distribution `n/M` on the sets of words of the patterns `Pt` on `W`. -/
noncomputable def liftMeasure (W : List Word) (Pt : List (List Bool)) (n : List ℕ) (M : ℕ) :
    Measure WordSpace :=
  (M : ENNReal)⁻¹ • ((n.zip Pt).map fun x => (x.1 : ENNReal) • Measure.dirac (extW W x.2)).sum

open Classical in
theorem listSum_dirac_apply (L : List (ℕ × List Bool)) (f : List Bool → WordSpace)
    {E : Set WordSpace} (hE : MeasurableSet E) :
    ((L.map fun x => (x.1 : ENNReal) • Measure.dirac (f x.2)).sum) E =
      (((L.map fun x => if decide (f x.2 ∈ E) = true then x.1 else 0).sum : ℕ) : ENNReal) := by
  classical
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, Measure.coe_add, Pi.add_apply, Measure.coe_smul,
      Pi.smul_apply, Measure.dirac_apply' _ hE, ih, Nat.cast_add, smul_eq_mul]
    by_cases h : f x.2 ∈ E <;> simp [h, Set.indicator]

open Classical in
theorem liftMeasure_apply (W : List Word) (Pt : List (List Bool)) (n : List ℕ) (M : ℕ)
    {E : Set WordSpace} (hE : MeasurableSet E) :
    liftMeasure W Pt n M E = (M : ENNReal)⁻¹ * (cntR n Pt fun p => decide (extW W p ∈ E) : ℕ) := by
  rw [liftMeasure, Measure.smul_apply, listSum_dirac_apply _ _ hE, smul_eq_mul]
  rfl

open Classical in
theorem liftMeasure_real (W : List Word) (Pt : List (List Bool)) (n : List ℕ) (M : ℕ)
    {E : Set WordSpace} (hE : MeasurableSet E) :
    (liftMeasure W Pt n M).real E = (cntR n Pt fun p => decide (extW W p ∈ E) : ℕ) / M := by
  rw [measureReal_def, liftMeasure_apply W Pt n M hE, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, inv_mul_eq_div]

theorem cntR_true {n : List ℕ} {Pt : List (List Bool)} (h : n.length ≤ Pt.length) :
    cntR n Pt (fun _ => true) = n.sum := by
  unfold cntR
  simp only [ite_true]
  rw [show (fun x : ℕ × List Bool => x.1) = Prod.fst from rfl, List.map_fst_zip h]

theorem isProbabilityMeasure_liftMeasure (W : List Word) {Pt : List (List Bool)} {n : List ℕ}
    {M : ℕ} (hM : 0 < M) (hlen : n.length ≤ Pt.length) (hsum : n.sum = M) :
    IsProbabilityMeasure (liftMeasure W Pt n M) := by
  constructor
  rw [liftMeasure_apply W Pt n M MeasurableSet.univ]
  simp only [Set.mem_univ, decide_true]
  rw [cntR_true hlen, hsum]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hM.ne') (ENNReal.natCast_ne_top _)

/-! ## The cylinders under conjugation -/

theorem list_abs_sum_le {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map fun x => |f x|).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem list_sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem sum_single {α : Type*} [DecidableEq α] {Q : List α} (hQ : Q.Nodup) {a : α} (ha : a ∈ Q)
    (g : α → ℝ) : (Q.map fun q => if a = q then g q else 0).sum = g a := by
  rw [← List.sum_toFinset _ hQ, Finset.sum_ite_eq, ite_eq_left (List.mem_toFinset.2 ha)]

theorem list_sum_comm {α β : Type*} (l₁ : List α) (l₂ : List β) (f : α → β → ℝ) :
    (l₁.map fun a => (l₂.map fun b => f a b).sum).sum =
      (l₂.map fun b => (l₁.map fun a => f a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

theorem cntR_comp_key (n : List ℕ) (Pt : List (List Bool)) {Q : List (List Bool)} (hQ : Q.Nodup)
    (key : List Bool → List Bool) (hk : ∀ p, key p ∈ Q) (c : List Bool → Bool) :
    (cntR n Pt (fun p => c (key p)) : ℝ) =
      (Q.map fun q => if c q = true then (cntR n Pt fun p => key p == q : ℝ) else 0).sum := by
  unfold cntR
  rw [Nat.cast_list_sum, List.map_map]
  have e : ∀ x : ℕ × List Bool, (((fun x : ℕ × List Bool => if c (key x.2) = true then x.1 else 0) x
      : ℕ) : ℝ) = (Q.map fun q => if key x.2 = q then
        (if c q = true then (x.1 : ℝ) else 0) else 0).sum := by
    intro x
    rw [sum_single hQ (hk x.2) (fun q => if c q = true then (x.1 : ℝ) else 0)]
    by_cases h : c (key x.2) = true <;> simp [h]
  have e' : ((n.zip Pt).map (Nat.cast ∘ fun x : ℕ × List Bool =>
      if c (key x.2) = true then x.1 else 0)) = (n.zip Pt).map fun x =>
        (Q.map fun q => if key x.2 = q then (if c q = true then (x.1 : ℝ) else 0) else 0).sum :=
    List.map_congr_left fun x _ => e x
  rw [e', list_sum_comm]
  congr 1
  apply List.map_congr_left
  intro q _
  rw [Nat.cast_list_sum, List.map_map]
  split_ifs with hc
  · congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply, beq_iff_eq]
    split_ifs <;> simp_all
  · simp

section Stage

variable (T : SubgroupTestData) (t : ℕ)

/-- **The change of a cylinder under conjugation**, for the distribution of a grid point: at most
the invariance error over `M`. -/
theorem abs_lift_cyl_sub_le (n : List ℕ) (g : Letter) {J : List Word}
    (hJ : ∀ u ∈ J, u ∈ stageD T t) (q₀ : List Bool) :
    |(liftMeasure (stageW T t) (stagePt T t) n (stageM T t)).real (restrSet J q₀) -
      (liftMeasure (stageW T t) (stagePt T t) n (stageM T t)).real (conjW g ⁻¹' restrSet J q₀)| ≤
      (invErr T t g n : ℝ) / stageM T t := by
  classical
  set W := stageW T t
  set D := stageD T t
  set Pt := stagePt T t
  have hM := stageM_pos T t
  rw [liftMeasure_real W Pt n _ (measurableSet_restrSet J q₀),
    liftMeasure_real W Pt n _ ((isClopen_conjW_restrSet g J q₀).isOpen.measurableSet),
    ← sub_div, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  set c : List Bool → Bool := fun q => decide (J.map (extW D q) = q₀)
  have hQ := nodup_allBits D.length
  have hk : ∀ p, D.map (extW W p) ∈ allBits D.length := fun p => by simp [mem_allBits]
  have hk' : ∀ p, D.map (conjW g (extW W p)) ∈ allBits D.length := fun p => by
    simp [mem_allBits]
  have hJD : ∀ A : WordSpace, J.map (extW D (D.map A)) = J.map A :=
    fun A => List.map_congr_left fun u hu => extW_map A (hJ u hu)
  have h1 : (cntR n Pt fun p => decide (extW W p ∈ restrSet J q₀)) =
      cntR n Pt fun p => c (D.map (extW W p)) := by
    congr 1; funext p
    rw [decide_eq_decide, hJD]; exact Iff.rfl
  have h2 : (cntR n Pt fun p => decide (extW W p ∈ conjW g ⁻¹' restrSet J q₀)) =
      cntR n Pt fun p => c (D.map (conjW g (extW W p))) := by
    congr 1; funext p
    rw [decide_eq_decide, hJD]; exact Iff.rfl
  rw [h1, h2, cntR_comp_key n Pt hQ _ hk c, cntR_comp_key n Pt hQ _ hk' c, ← list_sum_map_sub]
  refine (list_abs_sum_le _ _).trans ?_
  unfold invErr
  rw [Nat.cast_list_sum, List.map_map]
  refine List.sum_le_sum fun q _ => ?_
  simp only [Function.comp_apply, ndist_cast]
  split_ifs
  · exact le_rfl
  · simp

/-- The distribution of a feasible grid point is a probability measure. -/
noncomputable def liftStage (n : List ℕ) (hn : n ∈ allVecs (stageP T t) (stageM T t))
    (hf : Feasible T t n) : ProbabilityMeasure WordSpace :=
  ⟨liftMeasure (stageW T t) (stagePt T t) n (stageM T t),
    isProbabilityMeasure_liftMeasure _ (stageM_pos T t)
      (le_of_eq ((mem_allVecs.1 hn).1)) hf.1⟩

theorem valΩ_liftStage (n : List ℕ) (hn : n ∈ allVecs (stageP T t) (stageM T t))
    (hf : Feasible T t n) :
    valΩ T (liftStage T t n hn hf) = (numG T t n : ℝ) / (stageM T t * T.totalWeight) := by
  classical
  unfold valΩ valW numG
  have hM := stageM_pos T t
  rw [Nat.cast_list_sum, List.map_map, ← div_div]
  congr 1
  rw [← list_sum_map_div]
  · congr 1
    apply List.map_congr_left
    intro ch _
    simp only [Function.comp_apply, Nat.cast_mul]
    change (ch.1 : ℝ) * (liftMeasure (stageW T t) (stagePt T t) n (stageM T t)).real _ = _
    rw [liftMeasure_real _ _ n _ ((isClopen_passSetW continuous_id _ _).isOpen.measurableSet),
      mul_div_assoc]
    congr 2
    norm_cast
    congr 1
    funext p
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    rfl

theorem lift_badSet (n : List ℕ) (hn : n ∈ allVecs (stageP T t) (stageM T t))
    (hf : Feasible T t n) (b) (hb : ∀ w ∈ badWords b, w ∈ stageW T t) :
    (liftStage T t n hn hf : Measure WordSpace) (badSet T.nGen b) = 0 := by
  classical
  change liftMeasure _ _ n _ _ = 0
  rw [liftMeasure_apply _ _ n _ (isClopen_badSet _ b).isOpen.measurableSet]
  have : (cntR n (stagePt T t) fun p => decide (extW (stageW T t) p ∈ badSet T.nGen b)) = 0 := by
    unfold cntR
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    by_cases h0 : x.1 = 0
    · simp [h0]
    · have := extW_not_mem_badSet (hf.2.1 x hx (Nat.pos_of_ne_zero h0)) b hb
      have h' : decide (extW (stageW T t) x.2 ∈ badSet T.nGen b) = false := decide_eq_false this
      simp [h']
  rw [this]; simp

end Stage

/-! ## Eventually in the stage -/

theorem eventually_mem_stageD (T : SubgroupTestData) (w : Word) :
    ∀ᶠ t in atTop, w ∈ stageD T t := by
  set S := (w.map fun x : Letter => x.1).sum
  refine eventually_atTop.2 ⟨S + w.length, fun t ht => ?_⟩
  rw [stageD, mem_wordsUpTo]
  refine ⟨by omega, fun l hl => ?_⟩
  have : l.1 ≤ S := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x : Letter => x.1) hl)
  have : 0 < w.length := List.length_pos_of_mem hl
  omega

theorem eventually_forall_mem_stageD (T : SubgroupTestData) (L : List Word) :
    ∀ᶠ t in atTop, ∀ w ∈ L, w ∈ stageD T t := by
  induction L with
  | nil => simp
  | cons w L ih =>
    filter_upwards [eventually_mem_stageD T w, ih] with t h1 h2
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h1
    · exact h2 u hu

theorem eventually_forall_mem_stageW (T : SubgroupTestData) (L : List Word) :
    ∀ᶠ t in atTop, ∀ w ∈ L, w ∈ stageW T t :=
  (eventually_forall_mem_stageD T L).mono fun t h w hw => stageD_sub T t (h w hw)

theorem eventually_covers (T : SubgroupTestData) : ∀ᶠ t in atTop, Covers T t := by
  have := eventually_forall_mem_stageW T (T.challenges.flatMap (·.2.1))
  filter_upwards [this] with t ht
  intro ch hch k hk
  exact ht k (List.mem_flatMap.2 ⟨ch, hch, hk⟩)

theorem eventually_div_pow_le (c : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t : ℕ in atTop, c / 2 ^ t ≤ η := by
  have h : Tendsto (fun t : ℕ => c * (1 / 2 : ℝ) ^ t) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul c
  filter_upwards [h.eventually (gt_mem_nhds hη)] with t ht
  rw [one_div_pow] at ht
  rw [div_eq_mul_one_div]
  exact le_of_lt ht

/-! ## Convergence -/

theorem exists_max_feasible (T : SubgroupTestData) (t : ℕ) :
    ∃ n, ∃ _ : n ∈ allVecs (stageP T t) (stageM T t), Feasible T t n ∧
      maxNum T t ≤ numG T t n := by
  obtain ⟨n₀, hn₀, hf₀, -⟩ :=
    exists_feasible_of_irs T t (FiniteAction.trivial T.nGen).finDesc_mem_IRS
  rcases foldr_max_mem_or (((allVecs (stageP T t) (stageM T t)).filter (Feasible T t ·)).map
    (numG T t)) with h | h
  · exact ⟨n₀, hn₀, hf₀, by rw [maxNum, h]; exact Nat.zero_le _⟩
  · obtain ⟨n, hn, hn'⟩ := List.mem_map.1 h
    obtain ⟨hn1, hn2⟩ := List.mem_filter.1 hn
    exact ⟨n, hn1, by simpa using hn2, by rw [maxNum, ← hn']⟩

theorem valErg_eq_zero (T : SubgroupTestData) (hW : T.totalWeight = 0) : T.valErg = 0 :=
  le_antisymm (T.valErg_le (fun μ _ => by simp [SubgroupTestData.valOn, valGen, hW]) le_rfl)
    T.valErg_nonneg

theorem valErg_le_upperSeq (T : SubgroupTestData) (t : ℕ) : T.valErg ≤ dyadic (upperSeq T t) t :=
  T.valErg_le (fun _ hμ => valOn_le_upperSeq T t hμ) (dyadic_nonneg _ _)

/-- The rounding up in `upperSeq`. -/
theorem dyadic_ceilDiv_le {X D : ℕ} (t : ℕ) (hD : 0 < D) :
    dyadic (ceilDiv (2 ^ t * X) D) t ≤ (X : ℝ) / D + 1 / 2 ^ t := by
  have h := (ceilDiv_spec (x := 2 ^ t * X) hD).2
  have h' : (ceilDiv (2 ^ t * X) D : ℝ) * D < 2 ^ t * X + D := by exact_mod_cast h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold dyadic
  rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ t ≠ 0)]
  have : (ceilDiv (2 ^ t * X) D : ℝ) < 2 ^ t * X / D + 1 := by
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hD']; nlinarith
  calc (ceilDiv (2 ^ t * X) D : ℝ) ≤ 2 ^ t * X / D + 1 := this.le
    _ = X / D * 2 ^ t + 1 := by ring

/-- **The upper approximation tends to the ergodic value** (Main Theorem I (2), clause (3) of its
proof). -/
theorem tendsto_upperSeq (T : SubgroupTestData) :
    Tendsto (fun t => dyadic (upperSeq T t) t) atTop (𝓝 T.valErg) := by
  classical
  rcases Nat.eq_zero_or_pos T.totalWeight with hW | hW
  · rw [valErg_eq_zero T hW]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_covers T] with t ht
    simp [upperSeq, ht, hW, ceilDiv, dyadic]
  choose nn hnn hfeas hmax using exists_max_feasible T
  set ν : ℕ → ProbabilityMeasure WordSpace := fun t => liftStage T t (nn t) (hnn t) (hfeas t)
  have h1 : ∀ b, ∀ᶠ t in atTop, (ν t : Measure WordSpace) (badSet T.nGen b) = 0 := fun b =>
    (eventually_forall_mem_stageW T (badWords b)).mono fun t ht =>
      lift_badSet T t (nn t) (hnn t) (hfeas t) b ht
  have h2 : ∀ g : Letter, g.1 < T.nGen → ∀ J q, ∀ η > 0, ∀ᶠ t in atTop,
      |(ν t : Measure WordSpace).real (restrSet J q) -
        (ν t : Measure WordSpace).real (conjW g ⁻¹' restrSet J q)| ≤ η := by
    intro g hg J q η hη
    filter_upwards [eventually_forall_mem_stageD T J, eventually_div_pow_le 4 hη] with t hJ ht
    refine (abs_lift_cyl_sub_le T t (nn t) g hJ q).trans ?_
    have hinv := (hfeas t).2.2 g (mem_letters.2 hg)
    have hM : (stageM T t : ℝ) = stageP T t * 2 ^ t := by simp [stageM]
    have hP : (0 : ℝ) < stageP T t := by exact_mod_cast stageP_pos T t
    rw [hM, div_le_iff₀ (by positivity)]
    have : (invErr T t g (nn t) : ℝ) ≤ 4 * stageP T t := by exact_mod_cast hinv
    rw [div_le_iff₀ (by positivity)] at ht
    nlinarith
  have hlim := eventually_valΩ_le T ν h1 h2
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun t => lt_of_lt_of_le ha (valErg_le_upperSeq T t),
    fun a ha => ?_⟩
  set ε := a - T.valErg with hεdef
  have hε : 0 < ε := sub_pos.2 ha
  filter_upwards [eventually_covers T, hlim (ε / 4) (by positivity),
    eventually_div_pow_le 3 (show 0 < ε / 4 by positivity)] with t hcov hv ht
  have hM := stageM_pos T t
  have hMW : 0 < stageM T t * T.totalWeight := Nat.mul_pos hM hW
  have hup := dyadic_ceilDiv_le (X := maxNum T t + 2 * stageP T t * T.totalWeight) t hMW
  have hval := valΩ_liftStage T t (nn t) (hnn t) (hfeas t)
  change valΩ T (liftStage T t (nn t) (hnn t) (hfeas t)) ≤ _ at hv
  rw [hval] at hv
  simp only [upperSeq, hcov, ite_true]
  have hmx : (maxNum T t : ℝ) ≤ numG T t (nn t) := by exact_mod_cast hmax t
  have hMr : (stageM T t : ℝ) = stageP T t * 2 ^ t := by simp [stageM]
  have hP : (0 : ℝ) < stageP T t := by exact_mod_cast stageP_pos T t
  have hWr : (0 : ℝ) < T.totalWeight := by exact_mod_cast hW
  have e : ((maxNum T t + 2 * stageP T t * T.totalWeight : ℕ) : ℝ) /
      ((stageM T t * T.totalWeight : ℕ) : ℝ) ≤
      (numG T t (nn t) : ℝ) / (stageM T t * T.totalWeight) + 2 / 2 ^ t := by
    have e2 : (2 * stageP T t * T.totalWeight : ℝ) / (stageM T t * T.totalWeight) = 2 / 2 ^ t := by
      rw [hMr]; field_simp
    push_cast
    rw [add_div, e2]
    gcongr
  have h3 : (1 : ℝ) / 2 ^ t ≤ ε / 4 := by
    have : (3 : ℝ) / 2 ^ t ≤ ε / 4 := ht
    have h0 : (0 : ℝ) < 2 ^ t := by positivity
    rw [div_le_iff₀ h0] at this ⊢; linarith
  have h4 : (2 : ℝ) / 2 ^ t ≤ ε / 2 := by
    have : (1 : ℝ) / 2 ^ t ≤ ε / 4 := h3
    have h0 : (0 : ℝ) < 2 ^ t := by positivity
    rw [div_le_iff₀ h0] at this ⊢; linarith
  calc dyadic (ceilDiv (2 ^ t * (maxNum T t + 2 * stageP T t * T.totalWeight))
        (stageM T t * T.totalWeight)) t
      ≤ _ := hup
    _ ≤ (numG T t (nn t) : ℝ) / (stageM T t * T.totalWeight) + 2 / 2 ^ t + 1 / 2 ^ t := by
        gcongr
    _ < a := by
        have h34 : (2 : ℝ) / 2 ^ t + 1 / 2 ^ t = 3 / 2 ^ t := by ring
        linarith

end MIPRE.Tailored.Sofic.Measure

end
