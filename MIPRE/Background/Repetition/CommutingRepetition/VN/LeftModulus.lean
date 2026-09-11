/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/LeftModulus.lean
-/
/-
# The left modulus of an `L²` vector (Stage D2 of `PLAN-modulus-family.md`)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

With `E, C` the graph data of `VN/GraphModulus.lean` (`E = TT*(1+TT*)⁻¹`, `T`
left multiplication by `x`), the left modulus `|T*| = ψ(E)`, `ψ(t) = √(t/(1−t))`,
is unbounded; we only use its truncations `ψₙ = 1_{[0,aₙ]} ψ`, `aₙ = 1 − 1/(n+1)`.
The key identities are pointwise algebra: with `gₙ = 1_{[0,aₙ]}/(1−t)` and
`mₙ = 1_{[bₙ,aₙ]}/√(t(1−t))`,
`ψₙ² = gₙ · t(1−t) · gₙ`, `(1−t)gₙ = 1_{[0,aₙ]}`, `mₙ · t(1−t) · mₘ = 1_{[bₘ,aₘ]}`
(`m ≤ n`), `(1−t) mₖ ψₙ = 1_{[bₖ,aₙ]}` (`k ≥ n`). Through `C*C = E(1−E)` and
`C g(E) Ω = J ((1−t)g)(E) x` they give
`‖ψₙ(E)Ω‖² = ‖P[0,aₙ] x‖² ↑ ‖x‖²`, so `hvec := lim ψₙ(E)Ω` exists with
`‖hvec‖ = ‖x‖`, `J hvec = hvec`, `P(0,1) hvec = hvec`; and the partial isometry
`W := lim C mₙ(E)` (strong limit) has `W*W = P(0,1)` and `W hvec = J x`, so that
`v := W*` satisfies the polar relations `Rop v hvec = x`, `Rop (v v*) hvec = hvec`
of `SpectralData`. Nothing here is a manuscript statement.
-/
import Mathlib
import MIPRE.Background.Repetition.CommutingRepetition.VN.GraphModulus

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

namespace CommutingRepetition

namespace GraphMod

open scoped InnerProductSpace Topology
open Filter MeasureTheory BorelCalc

set_option linter.unusedSectionVars false

universe u

/-! ### Cutoff parameters -/

/-- `aₙ = 1 − 1/(n+1)`. -/
noncomputable def aN (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)

/-- `bₙ = 1/(n+1)`. -/
noncomputable def bN (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem bN_pos (n : ℕ) : 0 < bN n := by unfold bN; positivity

theorem bN_le_one (n : ℕ) : bN n ≤ 1 := by
  unfold bN
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem aN_eq (n : ℕ) : aN n = 1 - bN n := rfl

theorem aN_lt_one (n : ℕ) : aN n < 1 := by rw [aN_eq]; linarith [bN_pos n]

theorem aN_nonneg (n : ℕ) : 0 ≤ aN n := by rw [aN_eq]; linarith [bN_le_one n]

theorem bN_anti : Antitone bN := fun m n h => by
  unfold bN
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

theorem aN_mono : Monotone aN := fun m n h => by
  rw [aN_eq, aN_eq]; linarith [bN_anti h]

theorem exists_le_aN {t : ℝ} (ht : t < 1) : ∃ n, t ≤ aN n := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
  exact ⟨n, by rw [aN_eq, bN]; linarith⟩

theorem exists_bN_le {t : ℝ} (ht : 0 < t) : ∃ n, bN n ≤ t := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
  exact ⟨n, hn.le⟩

theorem iUnion_Icc_aN : ⋃ n, Set.Icc (0 : ℝ) (aN n) = Set.Ico 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ico]
  constructor
  · rintro ⟨n, h0, h1⟩; exact ⟨h0, h1.trans_lt (aN_lt_one n)⟩
  · rintro ⟨h0, h1⟩; obtain ⟨n, hn⟩ := exists_le_aN h1; exact ⟨n, h0, hn⟩

theorem iUnion_Icc_bN_aN : ⋃ n, Set.Icc (bN n) (aN n) = Set.Ioo 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ioo]
  constructor
  · rintro ⟨n, h0, h1⟩; exact ⟨(bN_pos n).trans_le h0, h1.trans_lt (aN_lt_one n)⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨n₁, hn₁⟩ := exists_bN_le h0
    obtain ⟨n₂, hn₂⟩ := exists_le_aN h1
    exact ⟨max n₁ n₂, (bN_anti (le_max_left n₁ n₂)).trans hn₁,
      hn₂.trans (aN_mono (le_max_right n₁ n₂))⟩

theorem iUnion_Icc_bN_const (n : ℕ) : ⋃ k, Set.Icc (bN k) (aN n) = Set.Ioc 0 (aN n) := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ioc]
  constructor
  · rintro ⟨k, h0, h1⟩; exact ⟨(bN_pos k).trans_le h0, h1⟩
  · rintro ⟨h0, h1⟩; obtain ⟨k, hk⟩ := exists_bN_le h0; exact ⟨k, hk, h1⟩

theorem iUnion_Ioc_aN : ⋃ n, Set.Ioc (0 : ℝ) (aN n) = Set.Ioo 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨n, h0, h1⟩; exact ⟨h0, h1.trans_lt (aN_lt_one n)⟩
  · rintro ⟨h0, h1⟩; obtain ⟨n, hn⟩ := exists_le_aN h1; exact ⟨n, h0, hn⟩

theorem monotone_Icc_aN : Monotone fun n => Set.Icc (0 : ℝ) (aN n) :=
  fun _ _ h => Set.Icc_subset_Icc le_rfl (aN_mono h)

theorem monotone_Icc_bN_aN : Monotone fun n => Set.Icc (bN n) (aN n) :=
  fun _ _ h => Set.Icc_subset_Icc (bN_anti h) (aN_mono h)

theorem monotone_Icc_bN_const (n : ℕ) : Monotone fun k => Set.Icc (bN k) (aN n) :=
  fun _ _ h => Set.Icc_subset_Icc (bN_anti h) le_rfl

theorem monotone_Ioc_aN : Monotone fun n => Set.Ioc (0 : ℝ) (aN n) :=
  fun _ _ h => Set.Ioc_subset_Ioc le_rfl (aN_mono h)

/-! ### The modulus function and its truncations -/

/-- `ψ(t) = √(t/(1−t))` on `(0,1)`, `0` elsewhere. -/
noncomputable def ψ (t : ℝ) : ℝ := if 0 < t ∧ t < 1 then Real.sqrt (t / (1 - t)) else 0

theorem ψ_nonneg (t : ℝ) : 0 ≤ ψ t := by
  unfold ψ; split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

theorem ψ_measurable : Measurable ψ :=
  Measurable.ite (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))
    (Real.continuous_sqrt.measurable.comp (measurable_id.div (measurable_const.sub measurable_id)))
    measurable_const

theorem ψ_of_not {t : ℝ} (h : ¬ (0 < t ∧ t < 1)) : ψ t = 0 := by unfold ψ; rw [if_neg h]

theorem ψ_of_mem {t : ℝ} (h : 0 < t ∧ t < 1) : ψ t = Real.sqrt (t / (1 - t)) := by
  unfold ψ; rw [if_pos h]

theorem ψ_pos_iff (t : ℝ) : 0 < ψ t ↔ 0 < t ∧ t < 1 := by
  constructor
  · intro h
    by_contra hc
    rw [ψ_of_not hc] at h
    exact lt_irrefl _ h
  · intro h
    rw [ψ_of_mem h]
    exact Real.sqrt_pos.mpr (div_pos h.1 (sub_pos.mpr h.2))

theorem ψ_sq {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : ψ t ^ 2 = t / (1 - t) := by
  rcases h0.lt_or_eq with h0' | h0'
  · rw [ψ_of_mem ⟨h0', h1⟩, Real.sq_sqrt (div_nonneg h0'.le (sub_pos.mpr h1).le)]
  · subst h0'; rw [ψ_of_not (fun h => lt_irrefl _ h.1)]; simp

theorem ψ_sq_le {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc 0 (aN n)) : ψ t ^ 2 ≤ (n : ℝ) + 1 := by
  rw [ψ_sq ht.1 (ht.2.trans_lt (aN_lt_one n))]
  have hb : bN n ≤ 1 - t := by rw [aN_eq] at ht; linarith [ht.2]
  have hpos : 0 < 1 - t := (bN_pos n).trans_le hb
  rw [div_le_iff₀ hpos]
  have : (1 : ℝ) ≤ ((n : ℝ) + 1) * (1 - t) := by
    have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    rw [bN, mul_one_div_cancel (by positivity)] at this
    exact this
  nlinarith [ht.1, ht.2.trans_lt (aN_lt_one n)]

/-- The truncated modulus function `ψₙ = 1_{[0,aₙ]} ψ`. -/
noncomputable def ψn (n : ℕ) : ℝ → ℝ := (Set.Icc 0 (aN n)).indicator ψ

theorem ψn_bdd (n : ℕ) : Bdd (ψn n) := by
  refine ⟨ψ_measurable.indicator measurableSet_Icc, (n : ℝ) + 1, fun t => ?_⟩
  unfold ψn
  by_cases ht : t ∈ Set.Icc 0 (aN n)
  · rw [Set.indicator_of_mem ht, abs_of_nonneg (ψ_nonneg t)]
    have h := ψ_sq_le ht
    nlinarith [ψ_nonneg t, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · rw [Set.indicator_of_notMem ht, abs_zero]; positivity

theorem ψn_nonneg (n : ℕ) (t : ℝ) : 0 ≤ ψn n t := by
  unfold ψn
  by_cases ht : t ∈ Set.Icc 0 (aN n)
  · rw [Set.indicator_of_mem ht]; exact ψ_nonneg t
  · rw [Set.indicator_of_notMem ht]

/-- `gₙ = 1_{[0,aₙ]} / (1 − t)`. -/
noncomputable def gn (n : ℕ) : ℝ → ℝ := (Set.Icc 0 (aN n)).indicator fun t => 1 / (1 - t)

theorem gn_bdd (n : ℕ) : Bdd (gn n) := by
  refine ⟨(measurable_const.div (measurable_const.sub measurable_id)).indicator measurableSet_Icc,
    (n : ℝ) + 1, fun t => ?_⟩
  unfold gn
  by_cases ht : t ∈ Set.Icc 0 (aN n)
  · rw [Set.indicator_of_mem ht]
    have hb : bN n ≤ 1 - t := by rw [aN_eq] at ht; linarith [ht.2]
    have hpos : 0 < 1 - t := (bN_pos n).trans_le hb
    rw [abs_of_pos (one_div_pos.mpr hpos), div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    rw [bN, mul_one_div_cancel (by positivity)] at this
    exact this
  · rw [Set.indicator_of_notMem ht, abs_zero]; positivity

/-- `mₙ = 1_{[bₙ,aₙ]} / √(t(1−t))`. -/
noncomputable def mn (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (bN n) (aN n)).indicator fun t => 1 / Real.sqrt (t * (1 - t))

theorem mem_Icc_bN_aN {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (bN n) (aN n)) :
    bN n ≤ t ∧ bN n ≤ 1 - t := ⟨ht.1, by rw [aN_eq] at ht; linarith [ht.2]⟩

theorem mn_bdd (n : ℕ) : Bdd (mn n) := by
  refine ⟨(measurable_const.div (Real.continuous_sqrt.measurable.comp
    (measurable_id.mul (measurable_const.sub measurable_id)))).indicator measurableSet_Icc,
    (n : ℝ) + 1, fun t => ?_⟩
  unfold mn
  by_cases ht : t ∈ Set.Icc (bN n) (aN n)
  · rw [Set.indicator_of_mem ht]
    obtain ⟨h1, h2⟩ := mem_Icc_bN_aN ht
    have hb := bN_pos n
    have hprod : bN n * bN n ≤ t * (1 - t) := mul_le_mul h1 h2 hb.le (hb.le.trans h1)
    have hsq : bN n ≤ Real.sqrt (t * (1 - t)) := by
      rw [show bN n = Real.sqrt (bN n * bN n) from (Real.sqrt_mul_self hb.le).symm]
      exact Real.sqrt_le_sqrt hprod
    have hpos : 0 < Real.sqrt (t * (1 - t)) := hb.trans_le hsq
    rw [abs_of_pos (one_div_pos.mpr hpos), div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    rw [bN, mul_one_div_cancel (by positivity)] at this
    exact this
  · rw [Set.indicator_of_notMem ht, abs_zero]; positivity

/-! ### Pointwise identities -/

theorem mem_Icc_aN_lt {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc 0 (aN n)) : t < 1 :=
  ht.2.trans_lt (aN_lt_one n)

/-- (F1) `ψₙ² = gₙ · t(1−t) · gₙ`. -/
theorem ψn_mul_ψn (n : ℕ) :
    ψn n * ψn n = fun t => gn n t * (clamp t * ((1 - clamp t) * gn n t)) := by
  funext t
  simp only [Pi.mul_apply, ψn, gn]
  by_cases ht : t ∈ Set.Icc 0 (aN n)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
      clamp_of_mem ⟨ht.1, (mem_Icc_aN_lt ht).le⟩, ← sq, ψ_sq ht.1 (mem_Icc_aN_lt ht)]
    have : (1 : ℝ) - t ≠ 0 := (sub_pos.mpr (mem_Icc_aN_lt ht)).ne'
    field_simp
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; ring

/-- (F2) `(1−t) gₙ = 1_{[0,aₙ]}`. -/
theorem one_sub_clamp_mul_gn (n : ℕ) :
    (fun t => (1 - clamp t) * gn n t) = (Set.Icc 0 (aN n)).indicator 1 := by
  funext t
  simp only [gn]
  by_cases ht : t ∈ Set.Icc 0 (aN n)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Pi.one_apply,
      clamp_of_mem ⟨ht.1, (mem_Icc_aN_lt ht).le⟩]
    have : (1 : ℝ) - t ≠ 0 := (sub_pos.mpr (mem_Icc_aN_lt ht)).ne'
    field_simp
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; ring

/-- (F3) `mₙ · t(1−t) · mₘ = 1_{[bₘ,aₘ]}` for `m ≤ n`. -/
theorem mn_mul_mn {m n : ℕ} (hmn : m ≤ n) :
    (fun t => mn n t * (clamp t * ((1 - clamp t) * mn m t))) = (Set.Icc (bN m) (aN m)).indicator 1 := by
  funext t
  simp only [mn]
  by_cases ht : t ∈ Set.Icc (bN m) (aN m)
  · have ht' : t ∈ Set.Icc (bN n) (aN n) := monotone_Icc_bN_aN hmn ht
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht', Set.indicator_of_mem ht, Pi.one_apply]
    obtain ⟨h1, h2⟩ := mem_Icc_bN_aN ht
    have hb := bN_pos m
    have h0 : 0 < t := hb.trans_le h1
    have h1' : t < 1 := by linarith [hb.trans_le h2]
    rw [clamp_of_mem ⟨h0.le, h1'.le⟩]
    have hpos : 0 < t * (1 - t) := mul_pos h0 (sub_pos.mpr h1')
    have hs := Real.mul_self_sqrt hpos.le
    have hne : Real.sqrt (t * (1 - t)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
    linarith [hs]
  · rw [Set.indicator_of_notMem ht, mul_zero, mul_zero, mul_zero,
      Set.indicator_of_notMem ht]

/-- (F4) `(1−t) mₖ ψₙ = 1_{[bₖ,aₙ]}` for `k ≥ n`. -/
theorem one_sub_clamp_mul_mn_mul_ψn {n k : ℕ} (hnk : n ≤ k) :
    (fun t => (1 - clamp t) * (mn k t * ψn n t)) = (Set.Icc (bN k) (aN n)).indicator 1 := by
  funext t
  simp only [mn, ψn]
  by_cases ht : t ∈ Set.Icc (bN k) (aN n)
  · have ht1 : t ∈ Set.Icc (bN k) (aN k) := ⟨ht.1, ht.2.trans (aN_mono hnk)⟩
    have ht2 : t ∈ Set.Icc 0 (aN n) := ⟨(bN_pos k).le.trans ht.1, ht.2⟩
    rw [Set.indicator_of_mem ht1, Set.indicator_of_mem ht2, Set.indicator_of_mem ht, Pi.one_apply]
    have h0 : 0 < t := (bN_pos k).trans_le ht.1
    have h1 : t < 1 := mem_Icc_aN_lt ht2
    rw [clamp_of_mem ⟨h0.le, h1.le⟩, ψ_of_mem ⟨h0, h1⟩]
    have hpos : 0 < 1 - t := sub_pos.mpr h1
    rw [Real.sqrt_mul h0.le, Real.sqrt_div' _ hpos.le]
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr h0
    have hs1 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr hpos
    have hs := Real.mul_self_sqrt hpos.le
    field_simp
    linarith [hs]
  · rw [Set.indicator_of_notMem ht]
    by_cases ht1 : t ∈ Set.Icc (bN k) (aN k)
    · have ht2 : t ∉ Set.Icc 0 (aN n) := fun h => ht ⟨ht1.1, h.2⟩
      rw [Set.indicator_of_notMem ht2]; ring
    · rw [Set.indicator_of_notMem ht1]; ring

/-- (F5) `ψₙ ψₘ = ψₘ²` for `m ≤ n`. -/
theorem ψn_mul_ψn_of_le {m n : ℕ} (hmn : m ≤ n) : ψn n * ψn m = ψn m * ψn m := by
  funext t
  simp only [Pi.mul_apply, ψn]
  by_cases ht : t ∈ Set.Icc 0 (aN m)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (monotone_Icc_aN hmn ht)]
  · rw [Set.indicator_of_notMem ht, mul_zero, mul_zero]

/-- (F6) `1_{(0,1)} ψₙ = ψₙ`. -/
theorem indicator_Ioo_mul_ψn (n : ℕ) : (Set.Ioo (0 : ℝ) 1).indicator 1 * ψn n = ψn n := by
  funext t
  simp only [Pi.mul_apply, ψn]
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem ht, zero_mul]
    by_cases ht' : t ∈ Set.Icc 0 (aN n)
    · rw [Set.indicator_of_mem ht', ψ_of_not ht]
    · rw [Set.indicator_of_notMem ht']

/-! ### The graph data of `x` -/

variable (M : StdTracialAlgebra.{u}) (x : M.H)

local notation "bE" => BorelCalc.bfc (Eop M x) (Eop_sa M x)
local notation "PE" => BorelCalc.P (Eop M x) (Eop_sa M x)
local notation "Ω" => M.traceVector

theorem PE_Icc_zero_one : PE (Set.Icc 0 1) = 1 :=
  BorelCalc.P_Icc_zero_one _ _ (spectrum_Eop_subset M x)

theorem PE_Ico : PE (Set.Ico 0 1) = 1 := by
  have h := BorelCalc.P_union (Eop M x) (Eop_sa M x) (measurableSet_Ico (a := (0 : ℝ)) (b := 1))
    (measurableSet_singleton 1) (Set.disjoint_singleton_right.mpr fun h => h.2.ne rfl)
  rw [Set.Ico_union_right zero_le_one, PE_Icc_zero_one, PE_singleton_one, add_zero] at h
  exact h.symm

theorem PE_Ioo_apply : PE (Set.Ioo 0 1) x = x := by
  have h := BorelCalc.P_union (Eop M x) (Eop_sa M x) (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))
    (measurableSet_singleton 0) (Set.disjoint_singleton_right.mpr fun h => h.1.ne' rfl)
  rw [Set.Ioo_union_left zero_lt_one, PE_Ico] at h
  have := congrArg (fun T => T x) h
  simp only [ContinuousLinearMap.one_apply, ContinuousLinearMap.add_apply,
    PE_singleton_zero_apply, add_zero] at this
  exact this.symm

/-- `⟪Ω, g(E) Ω⟫ = ∫ g dν_Ω`. -/
theorem inner_bE_traceVector {g : ℝ → ℝ} (hg : Bdd g) :
    ⟪Ω, bE g Ω⟫_ℂ = ((∫ t, g t ∂(BorelCalc.ν (Eop M x) (Eop_sa M x) Ω) : ℝ) : ℂ) :=
  BorelCalc.inner_bfc_self _ _ hg Ω

theorem inner_bE_bE {f g : ℝ → ℝ} (hf : Bdd f) (hg : Bdd g) (ξ η : M.H) :
    ⟪bE f ξ, bE g η⟫_ℂ = ⟪ξ, bE (f * g) η⟫_ℂ := by
  rw [← BorelCalc.inner_sa (BorelCalc.bfc_isSelfAdjoint _ _ hf), ← Resolver.Douglas.mulA,
    ← BorelCalc.bfc_mul _ _ hf hg]

/-- The norm of a truncated modulus vector: `‖ψₙ(E)Ω‖² = ‖P[0,aₙ] x‖²`. -/
theorem norm_ψn_traceVector_sq (n : ℕ) :
    ‖bE (ψn n) Ω‖ ^ 2 = ‖PE (Set.Icc 0 (aN n)) x‖ ^ 2 := by
  have h1 : ‖bE (ψn n) Ω‖ ^ 2 = (⟪Ω, bE (ψn n * ψn n) Ω⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_bE_bE M x (ψn_bdd n) (ψn_bdd n)]
    rfl
  have hb1 : Bdd fun t => (1 - clamp t) * gn n t := one_sub_clamp_bdd.mul (gn_bdd n)
  have hb2 : Bdd fun t => clamp t * ((1 - clamp t) * gn n t) := clamp_bdd.mul hb1
  have h2 : bE (gn n) * (Eop M x * ((1 - Eop M x) * bE (gn n))) = bE (ψn n * ψn n) := by
    rw [one_sub_Eop_mul_bE M x (gn_bdd n), Eop_mul_bE M x hb1,
      ← BorelCalc.bfc_mul _ _ (gn_bdd n) hb2, ψn_mul_ψn]
    rfl
  have h3 : (⟪Ω, bE (ψn n * ψn n) Ω⟫_ℂ).re = ‖Cop M x (bE (gn n) Ω)‖ ^ 2 := by
    rw [norm_Cop_apply_sq, ← h2]
    simp only [Resolver.Douglas.mulA]
    rw [← BorelCalc.inner_sa (BorelCalc.bfc_isSelfAdjoint _ _ (gn_bdd n))]
  rw [h1, h3, Cop_bfc_traceVector M x (gn_bdd n), M.norm_J, one_sub_clamp_mul_gn]
  rfl

theorem norm_PE_Icc_aN_le (n : ℕ) : ‖PE (Set.Icc 0 (aN n)) x‖ ≤ ‖x‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (BorelCalc.P_norm_le_one _ _ _))

theorem tendsto_norm_PE_Icc_aN :
    Tendsto (fun n => ‖PE (Set.Icc 0 (aN n)) x‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
  have h := (BorelCalc.P_tendsto_iUnion (Eop M x) (Eop_sa M x) (fun n => measurableSet_Icc)
    monotone_Icc_aN x).norm.pow 2
  rwa [iUnion_Icc_aN, PE_Ico, ContinuousLinearMap.one_apply] at h

/-- The polarized norms: `⟪ψₙ(E)Ω, ψₘ(E)Ω⟫ = ‖ψₘ(E)Ω‖²` for `m ≤ n`. -/
theorem inner_ψn_traceVector {m n : ℕ} (hmn : m ≤ n) :
    (⟪bE (ψn n) Ω, bE (ψn m) Ω⟫_ℂ).re = ‖bE (ψn m) Ω‖ ^ 2 := by
  rw [inner_bE_bE M x (ψn_bdd n) (ψn_bdd m), ψn_mul_ψn_of_le hmn,
    ← inner_bE_bE M x (ψn_bdd m) (ψn_bdd m)]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-! ### An abstract Cauchy criterion -/

/-- A sequence whose Gram matrix is `⟪u n, u m⟫ = c (min m n)` with `c` convergent is Cauchy. -/
theorem cauchySeq_of_inner_min {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]
    (u : ℕ → 𝓗) (c : ℕ → ℝ) (hin : ∀ m n, m ≤ n → (⟪u n, u m⟫_ℂ).re = c m)
    (hc : ∀ n, ‖u n‖ ^ 2 = c n) {l : ℝ} (hconv : Tendsto c atTop (𝓝 l)) : CauchySeq u := by
  have key : ∀ m n, m ≤ n → ‖u n - u m‖ ^ 2 = c n - c m := by
    intro m n hmn
    have := norm_sub_sq (𝕜 := ℂ) (u n) (u m)
    rw [this, hc n, hc m]
    have h := hin m n hmn
    have h' : RCLike.re (⟪u n, u m⟫_ℂ) = c m := h
    rw [h']
    ring
  have key' : ∀ m n, ‖u m - u n‖ ^ 2 = |c m - c n| := by
    intro m n
    rcases le_total m n with h | h
    · rw [norm_sub_rev, key m n h, abs_sub_comm, abs_of_nonneg]
      have := key m n h
      linarith [sq_nonneg ‖u n - u m‖]
    · rw [key n m h, abs_of_nonneg]
      have := key n m h
      linarith [sq_nonneg ‖u m - u n‖]
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (ε ^ 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h := hN m hm n hn
  rw [Real.dist_eq] at h
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (by rw [key']; exact h)

/-! ### The modulus vector `hvec` -/

theorem exists_hvec : ∃ h : M.H, Tendsto (fun n => bE (ψn n) Ω) atTop (𝓝 h) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_of_inner_min _ (fun n => ‖PE (Set.Icc 0 (aN n)) x‖ ^ 2)
      (fun m n hmn => by rw [inner_ψn_traceVector M x hmn, norm_ψn_traceVector_sq])
      (norm_ψn_traceVector_sq M x) (tendsto_norm_PE_Icc_aN M x))

/-- **The left modulus vector** `hvec = |T*| Ω = lim ψₙ(E) Ω`. -/
noncomputable def hvec : M.H := (exists_hvec M x).choose

theorem hvec_tendsto : Tendsto (fun n => bE (ψn n) Ω) atTop (𝓝 (hvec M x)) :=
  (exists_hvec M x).choose_spec

theorem norm_hvec : ‖hvec M x‖ = ‖x‖ := by
  have h1 : Tendsto (fun n => ‖bE (ψn n) Ω‖ ^ 2) atTop (𝓝 (‖hvec M x‖ ^ 2)) :=
    (hvec_tendsto M x).norm.pow 2
  have h2 : Tendsto (fun n => ‖bE (ψn n) Ω‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
    refine (tendsto_norm_PE_Icc_aN M x).congr fun n => ?_
    rw [norm_ψn_traceVector_sq]
  have := tendsto_nhds_unique h1 h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem J_bE_traceVector {g : ℝ → ℝ} (hg : Bdd g) : M.J (bE g Ω) = bE g Ω := by
  rw [M.J_apply_traceVector (bE_mem M x hg), (BorelCalc.bfc_isSelfAdjoint _ _ hg).star_eq]

theorem J_hvec : M.J (hvec M x) = hvec M x := by
  have h1 : Tendsto (fun n => M.J (bE (ψn n) Ω)) atTop (𝓝 (M.J (hvec M x))) :=
    (M.J.continuous.tendsto _).comp (hvec_tendsto M x)
  have h2 : Tendsto (fun n => M.J (bE (ψn n) Ω)) atTop (𝓝 (hvec M x)) :=
    (hvec_tendsto M x).congr fun n => (J_bE_traceVector M x (ψn_bdd n)).symm
  exact tendsto_nhds_unique h1 h2

theorem PE_Ioo_hvec : PE (Set.Ioo 0 1) (hvec M x) = hvec M x := by
  have h1 : Tendsto (fun n => PE (Set.Ioo 0 1) (bE (ψn n) Ω)) atTop
      (𝓝 (PE (Set.Ioo 0 1) (hvec M x))) :=
    ((PE (Set.Ioo 0 1)).continuous.tendsto _).comp (hvec_tendsto M x)
  have h2 : Tendsto (fun n => PE (Set.Ioo 0 1) (bE (ψn n) Ω)) atTop (𝓝 (hvec M x)) := by
    refine (hvec_tendsto M x).congr fun n => ?_
    rw [BorelCalc.P, ← Resolver.Douglas.mulA,
      ← BorelCalc.bfc_mul _ _ (Bdd.indicator measurableSet_Ioo) (ψn_bdd n), indicator_Ioo_mul_ψn]
  exact tendsto_nhds_unique h1 h2

/-! ### The partial isometry `W` -/

/-- `Wₙ = C mₙ(E)`. -/
noncomputable def Wn (n : ℕ) : M.H →L[ℂ] M.H := Cop M x * bE (mn n)

theorem Wn_mem (n : ℕ) : Wn M x n ∈ M.vnAlg := mul_mem (Cop_mem M x) (bE_mem M x (mn_bdd n))

/-- The Gram matrix of the `Wₙ`: `⟪Wₙ ζ, Wₘ ζ'⟫ = ⟪ζ, P[bₘ,aₘ] ζ'⟫` for `m ≤ n`. -/
theorem inner_Wn {m n : ℕ} (hmn : m ≤ n) (ζ ζ' : M.H) :
    ⟪Wn M x n ζ, Wn M x m ζ'⟫_ℂ = ⟪ζ, PE (Set.Icc (bN m) (aN m)) ζ'⟫_ℂ := by
  have hb1 : Bdd fun t => (1 - clamp t) * mn m t := one_sub_clamp_bdd.mul (mn_bdd m)
  have hb2 : Bdd fun t => clamp t * ((1 - clamp t) * mn m t) := clamp_bdd.mul hb1
  have hfun : (mn n * fun t => clamp t * ((1 - clamp t) * mn m t))
      = (Set.Icc (bN m) (aN m)).indicator 1 := mn_mul_mn hmn
  unfold Wn
  rw [Resolver.Douglas.mulA, Resolver.Douglas.mulA, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, ← Resolver.Douglas.mulA, star_Cop_mul_Cop]
  simp only [Resolver.Douglas.mulA]
  rw [← Resolver.Douglas.mulA (1 - Eop M x), one_sub_Eop_mul_bE M x (mn_bdd m),
    ← Resolver.Douglas.mulA (Eop M x), Eop_mul_bE M x hb1, inner_bE_bE M x (mn_bdd n) hb2, hfun,
    BorelCalc.P]

theorem norm_Wn_apply_sq (n : ℕ) (ζ : M.H) :
    ‖Wn M x n ζ‖ ^ 2 = ‖PE (Set.Icc (bN n) (aN n)) ζ‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_Wn M x le_rfl,
    BorelCalc.norm_P_apply_sq _ _ measurableSet_Icc, ← BorelCalc.re_inner_P _ _ measurableSet_Icc]
  rfl

theorem norm_Wn_apply_le (n : ℕ) (ζ : M.H) : ‖Wn M x n ζ‖ ≤ ‖ζ‖ := by
  have h := norm_Wn_apply_sq M x n ζ
  have h2 : ‖PE (Set.Icc (bN n) (aN n)) ζ‖ ≤ ‖ζ‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (BorelCalc.P_norm_le_one _ _ _))
  have h3 : ‖Wn M x n ζ‖ ^ 2 ≤ ‖ζ‖ ^ 2 := by
    rw [h]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

theorem norm_Wn_le (n : ℕ) : ‖Wn M x n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ζ => by
    rw [one_mul]; exact norm_Wn_apply_le M x n ζ

theorem tendsto_norm_PE_Icc_bN_aN (ζ : M.H) :
    Tendsto (fun n => ‖PE (Set.Icc (bN n) (aN n)) ζ‖ ^ 2) atTop
      (𝓝 (‖PE (Set.Ioo 0 1) ζ‖ ^ 2)) := by
  have h := (BorelCalc.P_tendsto_iUnion (Eop M x) (Eop_sa M x) (fun n => measurableSet_Icc)
    monotone_Icc_bN_aN ζ).norm.pow 2
  rwa [iUnion_Icc_bN_aN] at h

theorem exists_Wn_tendsto (ζ : M.H) : ∃ l, Tendsto (fun n => Wn M x n ζ) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_of_inner_min _ (fun n => ‖PE (Set.Icc (bN n) (aN n)) ζ‖ ^ 2)
      (fun m n hmn => by
        rw [inner_Wn M x hmn, BorelCalc.re_inner_P _ _ measurableSet_Icc,
          BorelCalc.norm_P_apply_sq _ _ measurableSet_Icc])
      (fun n => norm_Wn_apply_sq M x n ζ) (tendsto_norm_PE_Icc_bN_aN M x ζ))

/-- **The polar partial isometry** `W = lim C mₙ(E)`, the strong limit. -/
noncomputable def W : M.H →L[ℂ] M.H :=
  StrongLimit.pointwiseLimit (Wn M x) 1 (norm_Wn_le M x) (exists_Wn_tendsto M x)

theorem W_tendsto (ζ : M.H) : Tendsto (fun n => Wn M x n ζ) atTop (𝓝 (W M x ζ)) :=
  StrongLimit.pointwiseLimit_tendsto _ _ _ _ ζ

theorem W_mem : W M x ∈ M.vnAlg := M.mem_vnAlg_of_tendsto (Wn_mem M x) (W_tendsto M x)

/-- `W*W = P(0,1)`. -/
theorem star_W_mul_W : star (W M x) * W M x = PE (Set.Ioo 0 1) := by
  refine BorelCalc.ext_of_inner fun ζ ζ' => ?_
  rw [Resolver.Douglas.mulA, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  have h1 : Tendsto (fun n => ⟪Wn M x n ζ, Wn M x n ζ'⟫_ℂ) atTop (𝓝 ⟪W M x ζ, W M x ζ'⟫_ℂ) :=
    (W_tendsto M x ζ).inner (W_tendsto M x ζ')
  have h2 : Tendsto (fun n => ⟪Wn M x n ζ, Wn M x n ζ'⟫_ℂ) atTop
      (𝓝 ⟪ζ, PE (Set.Ioo 0 1) ζ'⟫_ℂ) := by
    have := (BorelCalc.P_tendsto_iUnion (Eop M x) (Eop_sa M x) (fun n => measurableSet_Icc)
      monotone_Icc_bN_aN ζ')
    rw [iUnion_Icc_bN_aN] at this
    refine (tendsto_const_nhds.inner this).congr fun n => ?_
    rw [inner_Wn M x le_rfl]
  exact tendsto_nhds_unique h1 h2

/-- `Wₖ ψₙ(E) Ω = J (P[bₖ,aₙ] x)` for `k ≥ n`. -/
theorem Wn_ψn {n k : ℕ} (hnk : n ≤ k) :
    Wn M x k (bE (ψn n) Ω) = M.J (PE (Set.Icc (bN k) (aN n)) x) := by
  unfold Wn
  rw [Resolver.Douglas.mulA, ← Resolver.Douglas.mulA (bE (mn k)) (bE (ψn n)) Ω,
    ← BorelCalc.bfc_mul _ _ (mn_bdd k) (ψn_bdd n),
    Cop_bfc_traceVector M x ((mn_bdd k).mul (ψn_bdd n)), BorelCalc.P,
    show (fun t => (1 - clamp t) * (mn k * ψn n) t) = (Set.Icc (bN k) (aN n)).indicator (1 : ℝ → ℝ)
      from one_sub_clamp_mul_mn_mul_ψn hnk]

theorem W_ψn (n : ℕ) : W M x (bE (ψn n) Ω) = M.J (PE (Set.Ioc 0 (aN n)) x) := by
  have h1 := W_tendsto M x (bE (ψn n) Ω)
  have h2 : Tendsto (fun k => Wn M x k (bE (ψn n) Ω)) atTop
      (𝓝 (M.J (PE (Set.Ioc 0 (aN n)) x))) := by
    have := (M.J.continuous.tendsto _).comp
      (BorelCalc.P_tendsto_iUnion (Eop M x) (Eop_sa M x) (fun k => measurableSet_Icc)
        (monotone_Icc_bN_const n) x)
    rw [iUnion_Icc_bN_const] at this
    refine this.congr' (eventually_atTop.mpr ⟨n, fun k hk => ?_⟩)
    simp only [Function.comp]
    rw [Wn_ψn M x hk]
  exact tendsto_nhds_unique h1 h2

/-- `W hvec = J x`. -/
theorem W_hvec : W M x (hvec M x) = M.J x := by
  have h1 : Tendsto (fun n => W M x (bE (ψn n) Ω)) atTop (𝓝 (W M x (hvec M x))) :=
    ((W M x).continuous.tendsto _).comp (hvec_tendsto M x)
  have h2 : Tendsto (fun n => W M x (bE (ψn n) Ω)) atTop (𝓝 (M.J x)) := by
    have := (M.J.continuous.tendsto _).comp
      (BorelCalc.P_tendsto_iUnion (Eop M x) (Eop_sa M x) (fun n => measurableSet_Ioc)
        monotone_Ioc_aN x)
    rw [iUnion_Ioc_aN, PE_Ioo_apply] at this
    refine this.congr fun n => ?_
    simp only [Function.comp]
    rw [W_ψn]
  exact tendsto_nhds_unique h1 h2

/-! ### The polar element -/

/-- `v = W*` as an element of the von Neumann algebra. -/
noncomputable def vEl : ↥M.vnAlg := ⟨star (W M x), star_mem (W_mem M x)⟩

theorem vnModel_Rop_vEl_hvec : M.vnModel.Rop (vEl M x) (hvec M x) = x := by
  rw [M.vnModel_Rop_eq]
  show (M.conjJ (star (star (W M x)))) (hvec M x) = x
  rw [star_star]
  show M.J (W M x (M.J (hvec M x))) = x
  rw [J_hvec, W_hvec, M.J_J]

theorem vnModel_Rop_vEl_mul_star_hvec :
    M.vnModel.Rop (vEl M x * star (vEl M x)) (hvec M x) = hvec M x := by
  rw [M.vnModel_Rop_eq]
  have : (star (vEl M x * star (vEl M x)) : ↥M.vnAlg).1 = PE (Set.Ioo 0 1) := by
    show star (star (W M x) * star (star (W M x))) = PE (Set.Ioo 0 1)
    rw [star_star, star_mul, star_star, star_W_mul_W]
  show M.J ((star (vEl M x * star (vEl M x)) : ↥M.vnAlg).1 (M.J (hvec M x))) = hvec M x
  rw [this, J_hvec, PE_Ioo_hvec, J_hvec]

theorem vEl_mul_star_vEl_val : (vEl M x * star (vEl M x)).1 = PE (Set.Ioo 0 1) := by
  show star (W M x) * star (star (W M x)) = _
  rw [star_star, star_W_mul_W]

end GraphMod

end CommutingRepetition
