/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.Measure.UpperPrimrec

@[expose] public section

/-!
# Main Theorem I (2), and the refutation of the Aldous–Lyons conjecture

`mainTheoremI_two`: a primitive recursive, non-increasing dyadic sequence tending to the ergodic
value — the running minimum `upperMin` of the upper approximation `upperSeq`, which is at least the
ergodic value (`valErg_le_upperSeq`) and tends to it (`tendsto_upperSeq`). With Main Theorem I (1)
and the conjecture this makes the sofic value approximable (`sofValueApproximable_of_aldousLyons`,
Corollary I:605), and with Main Theorem II and a halting reduction to tailored games it refutes the
conjecture (`aldous_lyons_false_of`, Corollary I:2144).
-/

namespace MIPRE.Tailored.Sofic.Measure

open SubgroupTestValue Filter Topology TailoredGameValue Primrec

/-- **Clause (2) as used by the corollary**: the upper approximation. -/
theorem ergUpperApprox : ErgUpperApprox :=
  ⟨upperSeq, primrec_upperSeq.to_comp, fun T => ⟨valErg_le_upperSeq T, tendsto_upperSeq T⟩⟩

/-- The running minimum of the upper approximation, as a numerator over `2^t`. -/
def upperMin (T : SubgroupTestData) : ℕ → ℕ
  | 0 => upperSeq T 0
  | t + 1 => min (2 * upperMin T t) (upperSeq T (t + 1))

theorem upperMin_eq_rec (T : SubgroupTestData) (t : ℕ) :
    upperMin T t = Nat.rec (motive := fun _ => ℕ) (upperSeq T 0)
      (fun n m => min (2 * m) (upperSeq T (n + 1))) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [upperMin, ih]

theorem primrec_upperMin : Primrec₂ upperMin :=
  (nat_rec' snd (primrec_upperSeq.comp fst (const 0))
    (nat_min.comp (nat_mul.comp (const 2) (snd.comp snd))
      (primrec_upperSeq.comp (fst.comp fst) (succ.comp (fst.comp snd)))).to₂).to₂.of_eq
    fun T t => (upperMin_eq_rec T t).symm

theorem dyadic_min_succ (a b t : ℕ) :
    dyadic (min (2 * a) b) (t + 1) = min (dyadic a t) (dyadic b (t + 1)) := by
  rw [dyadic_mono_succ a t]
  unfold dyadic
  rw [Nat.cast_min, min_div_div_right (by positivity)]

theorem valErg_le_upperMin (T : SubgroupTestData) (t : ℕ) : T.valErg ≤ dyadic (upperMin T t) t := by
  induction t with
  | zero => exact valErg_le_upperSeq T 0
  | succ t ih =>
    rw [upperMin, dyadic_min_succ]
    exact le_min ih (valErg_le_upperSeq T _)

theorem upperMin_le (T : SubgroupTestData) (t : ℕ) :
    dyadic (upperMin T t) t ≤ dyadic (upperSeq T t) t := by
  cases t with
  | zero => rfl
  | succ t => rw [upperMin, dyadic_min_succ]; exact min_le_right _ _

theorem antitone_upperMin (T : SubgroupTestData) : Antitone fun t => dyadic (upperMin T t) t :=
  antitone_nat_of_succ_le fun t => by
    rw [upperMin, dyadic_min_succ]
    exact min_le_left _ _

/-- **Main Theorem I (2)** (I:594): a primitive recursive, non-increasing sequence of dyadic numbers
`β T t / 2^t` tending to the ergodic value. -/
theorem mainTheoremI_two : ∃ β : SubgroupTestData → ℕ → ℕ, Primrec₂ β ∧ ∀ T : SubgroupTestData,
    Antitone (fun t => dyadic (β T t) t) ∧ (∀ t, T.valErg ≤ dyadic (β T t) t) ∧
      Tendsto (fun t => dyadic (β T t) t) atTop (𝓝 T.valErg) :=
  ⟨upperMin, primrec_upperMin, fun T => ⟨antitone_upperMin T, valErg_le_upperMin T,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_upperSeq T)
      (valErg_le_upperMin T) (upperMin_le T)⟩⟩

theorem mainTheoremITwo : MainTheoremITwo :=
  let ⟨β, hβ, h⟩ := mainTheoremI_two
  ⟨β, hβ.to_comp, fun T => ⟨(h T).1, (h T).2.2⟩⟩

/-- **The Aldous–Lyons conjecture makes the sofic value approximable** (Corollary I:605). -/
theorem sofValueApproximable_of_aldousLyons (hAL : AldousLyons) : SofValueApproximable :=
  sofValueApproximable_of hAL ergUpperApprox

/-- **The Aldous–Lyons conjecture is false** (Corollary I:2144), from a halting reduction to
tailored games and Main Theorem II with a primitive recursive gap function. -/
theorem aldous_lyons_false_of {K : ℕ → ℕ} (hK : Primrec K) (hMT : MainTheoremII K)
    (hred : TailoredHaltingReduction) : ¬ AldousLyons :=
  aldous_lyons_false_of_upper hK hMT hred ergUpperApprox

end MIPRE.Tailored.Sofic.Measure

end
