/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.LowerPrimrec
public import MIPRE.Tailored.Sofic.Undecidable

@[expose] public section

/-!
# The Aldous–Lyons conjecture makes the sofic value approximable

Paper I, Corollary I:605 and the deduction of Corollary I:2144. Main Theorem I gives a computable
sequence increasing to the sofic value (clause (1), `mainTheoremI_one`) and one decreasing to the
ergodic value (clause (2)). Under the Aldous–Lyons conjecture the two values coincide
(`SubgroupTestData.valSof_eq_valErg`), so a search for a stage where the bounds are within
`1/(k+1)` terminates, and rounding the lower bound up to the grid of step `1/(k+1)` approximates
the sofic value to within `1/(k+1)` (`sofValueApproximable_of`). With
`not_sofValueApproximable_of` this refutes the conjecture (`aldous_lyons_false_of_upper`).

Clause (2) enters through `ErgUpperApprox`, the part of it the argument uses: a computable dyadic
sequence at least the ergodic value and tending to it. `MainTheoremITwo` is clause (2) as the
paper states it, with the sequence non-increasing.
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue Filter Topology TailoredGameValue

/-- **Upper approximation of the ergodic value**: a computable sequence of dyadic numbers
`β T t / 2^t`, each at least the ergodic value, tending to it. -/
def ErgUpperApprox : Prop :=
  ∃ β : SubgroupTestData → ℕ → ℕ, Computable₂ β ∧ ∀ T : SubgroupTestData,
    (∀ t, T.valErg ≤ dyadic (β T t) t) ∧ Tendsto (fun t => dyadic (β T t) t) atTop (𝓝 T.valErg)

/-- **Main Theorem I (2)** (I:594): a computable non-increasing sequence of dyadic numbers tending
to the ergodic value. -/
def MainTheoremITwo : Prop :=
  ∃ β : SubgroupTestData → ℕ → ℕ, Computable₂ β ∧ ∀ T : SubgroupTestData,
    Antitone (fun t => dyadic (β T t) t) ∧ Tendsto (fun t => dyadic (β T t) t) atTop (𝓝 T.valErg)

theorem MainTheoremITwo.ergUpperApprox (h : MainTheoremITwo) : ErgUpperApprox := by
  obtain ⟨β, hβ, h⟩ := h
  exact ⟨β, hβ, fun T => ⟨fun t => (h T).1.le_of_tendsto (h T).2 t, (h T).2⟩⟩

/-- Rounding up to the grid: `⌈x / D⌉` for `D > 0`. -/
def ceilDiv (x D : ℕ) : ℕ := (x + D - 1) / D

theorem ceilDiv_spec {x D : ℕ} (hD : 0 < D) : x ≤ ceilDiv x D * D ∧ ceilDiv x D * D < x + D := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (x + D - 1) D
  have h2 := Nat.mod_lt (x + D - 1) hD
  have hn : x + D - 1 + 1 = x + D := by omega
  generalize x + D - 1 = n at h1 h2 hn ⊢
  generalize n / D = F at h1 ⊢
  generalize n % D = r at h1 h2
  rw [Nat.mul_comm D F] at h1
  generalize F * D = m at h1 ⊢
  constructor <;> omega

/-- The rounded estimate: `|v − ⌈a(k+1)/2^t⌉/(k+1)| ≤ 1/(k+1)` when `v` lies between `a/2^t` and
`b/2^t` and these are within `1/(k+1)`. -/
theorem approx_of_bounds {v : ℝ} {a b t k : ℕ} (ha : dyadic a t ≤ v) (hb : v ≤ dyadic b t)
    (hab : (b - a) * (k + 1) < 2 ^ t) :
    |v - (ceilDiv (a * (k + 1)) (2 ^ t) : ℝ) / ((k : ℝ) + 1)| ≤ 1 / ((k : ℝ) + 1) := by
  have hD : 0 < 2 ^ t := by positivity
  obtain ⟨h1, h2⟩ := ceilDiv_spec (x := a * (k + 1)) hD
  set F := ceilDiv (a * (k + 1)) (2 ^ t)
  have hab' : a ≤ b := by
    have : dyadic a t ≤ dyadic b t := ha.trans hb
    unfold dyadic at this
    exact_mod_cast (div_le_div_iff_of_pos_right (by positivity)).1 this
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hD' : (0 : ℝ) < 2 ^ t := by positivity
  have r1 : (a : ℝ) * (k + 1) ≤ F * 2 ^ t := by exact_mod_cast h1
  have r2 : (F : ℝ) * 2 ^ t < a * (k + 1) + 2 ^ t := by exact_mod_cast h2
  have r3 : ((b : ℝ) - a) * (k + 1) < 2 ^ t := by
    have : ((b - a : ℕ) : ℝ) * (k + 1) < 2 ^ t := by exact_mod_cast hab
    rwa [Nat.cast_sub hab'] at this
  unfold dyadic at ha hb
  rw [le_div_iff₀ hD'] at hb
  rw [div_le_iff₀ hD'] at ha
  have hu : (F : ℝ) / ((k : ℝ) + 1) * ((k : ℝ) + 1) = F := div_mul_cancel₀ _ hk.ne'
  set u := (F : ℝ) / ((k : ℝ) + 1)
  have hka := mul_le_mul_of_nonneg_right ha hk.le
  have hkb := mul_le_mul_of_nonneg_right hb hk.le
  have A : (u - v) * ((k : ℝ) + 1) ≤ 1 := by
    have : (u - v) * ((k : ℝ) + 1) * 2 ^ t ≤ 1 * 2 ^ t := by
      have e : (u - v) * ((k : ℝ) + 1) * 2 ^ t = F * 2 ^ t - (v * 2 ^ t) * ((k : ℝ) + 1) := by
        rw [sub_mul, sub_mul, hu]; ring
      rw [e]; linarith
    exact le_of_mul_le_mul_right this hD'
  have B : (v - u) * ((k : ℝ) + 1) ≤ 1 := by
    have : (v - u) * ((k : ℝ) + 1) * 2 ^ t ≤ 1 * 2 ^ t := by
      have e : (v - u) * ((k : ℝ) + 1) * 2 ^ t = (v * 2 ^ t) * ((k : ℝ) + 1) - F * 2 ^ t := by
        rw [sub_mul, sub_mul, hu]; ring
      rw [e]; nlinarith
    exact le_of_mul_le_mul_right this hD'
  rw [abs_sub_le_iff]
  exact ⟨(le_div_iff₀ hk).2 B, (le_div_iff₀ hk).2 A⟩

/-- **The Aldous–Lyons conjecture makes the sofic value approximable** (Corollary I:605), given
the upper approximation of the ergodic value (Main Theorem I (2)). -/
theorem sofValueApproximable_of (hAL : AldousLyons) (hU : ErgUpperApprox) :
    SofValueApproximable := by
  obtain ⟨β, hβ, hU⟩ := hU
  -- the stopping condition
  let P : SubgroupTestData × ℕ → ℕ → Prop := fun p t =>
    (β p.1 t - lowerSeq p.1 t) * (p.2 + 1) < 2 ^ t
  have hP : ComputablePred fun q : (SubgroupTestData × ℕ) × ℕ => P q.1 q.2 := by
    refine ⟨inferInstance, ?_⟩
    have hβ' : Computable fun q : (SubgroupTestData × ℕ) × ℕ => β q.1.1 q.2 :=
      hβ.comp (Computable.fst.comp Computable.fst) Computable.snd
    have hα : Computable fun q : (SubgroupTestData × ℕ) × ℕ => lowerSeq q.1.1 q.2 :=
      (primrec_lowerSeq.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to_comp
    have hk : Computable fun q : (SubgroupTestData × ℕ) × ℕ => q.1.2 + 1 :=
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)).to_comp
    have hpow : Computable fun q : (SubgroupTestData × ℕ) × ℕ => 2 ^ q.2 :=
      (primrec_two_pow.comp Primrec.snd).to_comp
    exact (Primrec.nat_lt.decide.to_comp).comp
      ((Primrec.nat_mul.to_comp).comp ((Primrec.nat_sub.to_comp).comp hβ' hα) hk) hpow
  -- the search terminates under the conjecture
  have hex : ∀ p : SubgroupTestData × ℕ, ∃ t, P p t := by
    rintro ⟨T, k⟩
    have hdiff : Tendsto (fun t => dyadic (β T t) t - dyadic (lowerSeq T t) t) atTop
        (𝓝 (T.valErg - T.valSof)) := (hU T).2.sub (tendsto_lowerSeq T)
    rw [← T.valSof_eq_valErg hAL, sub_self] at hdiff
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨t, ht⟩ := (hdiff.eventually (gt_mem_nhds hk)).exists
    refine ⟨t, ?_⟩
    have hle : lowerSeq T t ≤ β T t := by
      have : dyadic (lowerSeq T t) t ≤ dyadic (β T t) t :=
        (lowerSeq_le T t).trans (T.valSof_le_valErg.trans ((hU T).1 t))
      unfold dyadic at this
      exact_mod_cast (div_le_div_iff_of_pos_right (by positivity)).1 this
    show ((β T t - lowerSeq T t) * (k + 1) < 2 ^ t)
    have hD : (0 : ℝ) < 2 ^ t := by positivity
    unfold dyadic at ht
    rw [← sub_div, div_lt_div_iff₀ hD (by positivity), one_mul] at ht
    have : (((β T t - lowerSeq T t) * (k + 1) : ℕ) : ℝ) < ((2 ^ t : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hle]; linarith
    exact_mod_cast this
  classical
  have hfind : Computable fun p : SubgroupTestData × ℕ => Nat.find (hex p) := Computable.find hP hex
  refine ⟨fun T k => ceilDiv (lowerSeq T (Nat.find (hex (T, k))) * (k + 1))
    (2 ^ Nat.find (hex (T, k))), ?_, fun T k => ?_⟩
  · have hα : Computable fun p : SubgroupTestData × ℕ => lowerSeq p.1 (Nat.find (hex p)) :=
      (primrec_lowerSeq.to_comp).comp Computable.fst hfind
    have hpow : Computable fun p : SubgroupTestData × ℕ => 2 ^ Nat.find (hex p) :=
      (primrec_two_pow.to_comp).comp hfind
    have hceil : Primrec₂ ceilDiv :=
      (Primrec.nat_div.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)
        (Primrec.const 1)) Primrec.snd).to₂
    exact (hceil.to_comp).comp ((Primrec.nat_mul.to_comp).comp hα
      ((Primrec.succ.comp Primrec.snd).to_comp)) hpow
  · set t := Nat.find (hex (T, k))
    have ht : P (T, k) t := Nat.find_spec (hex (T, k))
    exact approx_of_bounds (lowerSeq_le T t) (T.valSof_le_valErg.trans ((hU T).1 t)) ht

/-- **The Aldous–Lyons conjecture is false** (Corollary I:2144), from a halting reduction to
tailored games, Main Theorem II with a primitive recursive gap function, and the upper
approximation of the ergodic value (Main Theorem I (2)). -/
theorem aldous_lyons_false_of_upper {K : ℕ → ℕ} (hK : Primrec K) (hMT : MainTheoremII K)
    (hred : TailoredHaltingReduction) (hU : ErgUpperApprox) : ¬ AldousLyons := fun hAL =>
  not_sofValueApproximable_of hK hMT hred (sofValueApproximable_of hAL hU)

end MIPRE.Tailored.Sofic.Measure

end
