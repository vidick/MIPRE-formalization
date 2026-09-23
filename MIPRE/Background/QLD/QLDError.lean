/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.ErrorShape
import MIPRE.Background.QLD.SwapItemTwo

/-!
# The error of `thm:qld`, named once

`MirrorSimul.swap_isometry` (`MIPRE/Background/QLD/SwapItemTwo.lean`) closes the swap isometry
lemma `lem:qld-swap` for a legal projective strategy, at the `MirrorSimul` that
`exists_mirrorSimul` builds. Its two bounds, and the hypothesis it needs, are explicit expressions
in the chain's constants. What `thm:qld` asserts is one function of `(ε, m, d, q)`, of the closed
form `a (md)^a (ε^b + q^{-b} + 2^{-bmd})` (`errShape`). This file names that function, `qldErr`,
and proves it is of the closed form (`exists_qldErr_le`). The assembly of `thm:qld` then only has
to show that each of the theorem's two items is at most `qldErr`, for which `le_qldErr` is the
interface.

## The constants

Along the chain, with `q` standing for `Fintype.card F`:

* `qldDelta = δ_S(δ_ld)`, the error of the `MirrorSimul` that `exists_mirrorSimul` returns;
* `qldHlt = 2 √X + 2 X` at `X = deltaSelfCons qldDelta`, the quantity `swap_isometry` needs below
  one (its hypothesis `hlt`);
* `qldEta = etaItemOne qldDelta`, item 1's bound on the **squared** distance to the product state
  `|aux> ⊗ |EPR_q>^M`;
* `qldBound = deltaItemTwo qldDelta … qldEta + 9 √qldEta`.

`qldBound` is chosen to dominate both items of the theorem at once. Item 1 of `thm:qld` bounds the
distance itself, not its square, so it costs `√qldEta` (`sqrt_qldEta_le_qldBound`). Item 2 costs
item 2 of `lem:qld-swap` plus the descent the paper makes after it, from conjugation by the swap
unitary `V` on the projective dilation to conjugation of the original POVM by the embedding
`φ = V ∘ (· ⊗ EPR ⊗ padding)`. That descent goes through the agreement with `τ^W` on the
*opposite* half of the pair, which local isometries carry verbatim; it moves the pairing from the
product state to the embedded state and back, at `2 r` each way with `r = √qldEta` the distance of
item 1, and the conversions between closeness and agreement double that. So it costs `8 √qldEta`
(`itemTwo_le_qldBound`), and the spare `√qldEta` is item 1's.

## Outside the regime

Two hypotheses stand between a strategy and `swap_isometry`: the regime `48 m d ≤ q`, which
`exists_mirrorSimul` needs (the paper's appendix works under `16 m d ≤ q`; the constant `48` is
where `lem:qld-global-separate` is formalized, `GlobalPair.one_sub_two_eta_ge`), and `qldHlt < 1`.
Where either fails, `thm:qld` takes a trivial bound: the distance between two unit vectors is at
most `2`, and so is the summed deviation of a sub-POVM from `τ^W` on a state that carries the pair.
The cap is `4`, the paper's bound on the state-dependent distance between any two POVMs, which is
above both. So `qldErr` is `min qldBound 4` inside and `4` outside (`qldErr_of_regime`,
`qldErr_of_not`).

That this costs nothing is `ErrSmall.of_cases` at the small quantity `g = 48 md/q + qldHlt`: where
`g < 1` both hypotheses hold, since each summand is nonnegative; and where `g ≥ 1` the constant
`4` is at most `4 g`, which is itself of the shape. This is the paper's own move in the proof of
`thm:pauli-appendix` --- enlarge `a` until the shape exceeds the trivial bound outside the
regime --- written as a closure property rather than a choice of `a`. The `min … 4` inside is what
makes `qldErr` bounded everywhere, which `of_cases` needs.

## Why every link is small

`qldDelta` is `errSmall_deltaS`, `qldHlt` is `errSmall_itemOneEta` and `qldEta` is
`errSmall_swapItemOne`, all from `MIPRE/Background/QLD/ErrorShape.lean`. The two constants of item 2
join by the same combinators: `deltaLegs δ` is linear in `δ`, `ε`, `√(688 ε)` and `md/q`
(`ErrSmall.deltaLegs_comp`), and `deltaItemTwo` is linear in `deltaLegs`, `md/q` and `√η`
(`ErrSmall.deltaItemTwo_comp`). Nonnegativity, which the assembly needs at every `ε ≥ 0` and not
only on `[0, 1]`, is proved directly (`qldDelta_nonneg`, `qldHlt_nonneg`, `qldEta_nonneg`, ...).
-/

noncomputable section

namespace MIPRE.QLD

open MIPRE.LIDT

/-! ## The constants -/

/-- **`δ` of the `MirrorSimul` the chain builds**: `δ_S` at the `GlobalPair` error `δ_ld`, as
`exists_mirrorSimul` returns it. -/
def qldDelta (ε : ℝ) (m d q : ℕ) : ℝ := deltaS q (deltaLD q m d ε) ε

/-- **The quantity `swap_isometry` needs below one** (its hypothesis `hlt`): `2 √X + 2 X` at
`X = deltaSelfCons qldDelta`. -/
def qldHlt (ε : ℝ) (m d q : ℕ) : ℝ :=
  2 * Real.sqrt (deltaSelfCons (qldDelta ε m d q) ε m d q)
    + 2 * deltaSelfCons (qldDelta ε m d q) ε m d q

/-- **Item 1's bound on the squared distance** to `|aux> ⊗ |EPR_q>^M`, along the chain. -/
def qldEta (ε : ℝ) (m d q : ℕ) : ℝ := etaItemOne (qldDelta ε m d q) ε m d q

/-- **The bound on both items of `thm:qld` inside the regime**: item 2 of `lem:qld-swap` plus
`9 √η`, which dominates item 1's `√η` and item 2's `deltaItemTwo + 8 √η`. -/
def qldBound (ε : ℝ) (m d q : ℕ) : ℝ :=
  deltaItemTwo (qldDelta ε m d q) ε m d q (qldEta ε m d q) + 9 * Real.sqrt (qldEta ε m d q)

/-- **`δ_qld`, the error of `thm:qld`.** Inside the regime `48 m d ≤ q` where `swap_isometry`'s
hypothesis `qldHlt < 1` also holds, the chain's bound, capped at the trivial bound `4`; outside,
the trivial bound. -/
def qldErr (ε : ℝ) (m d q : ℕ) : ℝ :=
  if 48 * m * d ≤ q ∧ qldHlt ε m d q < 1 then min (qldBound ε m d q) 4 else 4

theorem qldDelta_eq (ε : ℝ) (m d q : ℕ) : qldDelta ε m d q = deltaS q (deltaLD q m d ε) ε := rfl

theorem qldHlt_eq (ε : ℝ) (m d q : ℕ) :
    qldHlt ε m d q = 2 * Real.sqrt (deltaSelfCons (qldDelta ε m d q) ε m d q)
      + 2 * deltaSelfCons (qldDelta ε m d q) ε m d q := rfl

theorem qldEta_eq (ε : ℝ) (m d q : ℕ) :
    qldEta ε m d q = etaItemOne (qldDelta ε m d q) ε m d q := rfl

/-! ## Nonnegativity, at every `ε ≥ 0` -/

section Nonneg

variable {ε : ℝ}

theorem deltaLD_nonneg {q m d : ℕ} (hε : 0 ≤ ε) : 0 ≤ deltaLD q m d ε := by
  have hx := deltaGS_nonneg (q := q) (m := m) (d := d) hε
  have hA : 0 ≤ clA := by linarith [one_le_clA]
  unfold deltaLD deltaCL
  positivity

theorem deltaS_nonneg {q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) : 0 ≤ deltaS q δ ε := by
  unfold deltaS deltaSep deltaProd
  positivity

theorem qldDelta_nonneg (hε : 0 ≤ ε) (m d q : ℕ) : 0 ≤ qldDelta ε m d q :=
  deltaS_nonneg (deltaLD_nonneg hε) hε

theorem qldHlt_nonneg (hε : 0 ≤ ε) (m d q : ℕ) : 0 ≤ qldHlt ε m d q := by
  have h := deltaSelfCons_nonneg (qldDelta_nonneg hε m d q) hε m d q
  rw [qldHlt_eq]
  positivity

/-- **Item 1's bound is nonnegative, and at most twice `qldHlt`** (`two_sub_two_sqrt_one_sub`). -/
theorem qldEta_nonneg (hε : 0 ≤ ε) (m d q : ℕ) : 0 ≤ qldEta ε m d q :=
  (two_sub_two_sqrt_one_sub (qldHlt_nonneg hε m d q)).1

theorem qldEta_le_two_mul_qldHlt (hε : 0 ≤ ε) (m d q : ℕ) :
    qldEta ε m d q ≤ 2 * qldHlt ε m d q :=
  (two_sub_two_sqrt_one_sub (qldHlt_nonneg hε m d q)).2

theorem deltaLegs_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (m d q : ℕ) :
    0 ≤ deltaLegs δ ε m d q := by
  unfold deltaLegs
  positivity

theorem deltaItemTwo_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (m d q : ℕ) (η : ℝ) :
    0 ≤ deltaItemTwo δ ε m d q η := by
  have h := deltaLegs_nonneg hδ hε m d q
  unfold deltaItemTwo
  positivity

/-- Item 2's bound of `lem:qld-swap`, along the chain, is nonnegative. -/
theorem qldItemTwo_nonneg (hε : 0 ≤ ε) (m d q : ℕ) :
    0 ≤ deltaItemTwo (qldDelta ε m d q) ε m d q (qldEta ε m d q) :=
  deltaItemTwo_nonneg (qldDelta_nonneg hε m d q) hε m d q _

theorem qldBound_nonneg (hε : 0 ≤ ε) (m d q : ℕ) : 0 ≤ qldBound ε m d q := by
  have h := qldItemTwo_nonneg hε m d q
  unfold qldBound
  positivity

end Nonneg

/-! ## `qldBound` dominates both items -/

section Bound

variable {ε : ℝ}

/-- **Item 1 of `thm:qld`**: the distance itself, the square root of item 1's bound, is at most
`qldBound`. -/
theorem sqrt_qldEta_le_qldBound (hε : 0 ≤ ε) (m d q : ℕ) :
    Real.sqrt (qldEta ε m d q) ≤ qldBound ε m d q := by
  have h := qldItemTwo_nonneg hε m d q
  have hs := Real.sqrt_nonneg (qldEta ε m d q)
  unfold qldBound
  linarith

/-- **Item 2 of `thm:qld`**: item 2 of `lem:qld-swap` plus `8 √η`, the price of passing to the
embedding `φ` and down to the original strategy, is at most `qldBound`. -/
theorem itemTwo_le_qldBound (ε : ℝ) (m d q : ℕ) :
    deltaItemTwo (qldDelta ε m d q) ε m d q (qldEta ε m d q) + 8 * Real.sqrt (qldEta ε m d q)
      ≤ qldBound ε m d q := by
  have hs := Real.sqrt_nonneg (qldEta ε m d q)
  unfold qldBound
  linarith

end Bound

/-! ## `qldErr`: the chain inside the regime, the trivial bound outside -/

section Err

variable {ε : ℝ} {m d q : ℕ}

/-- **Outside the regime, the trivial bound.** -/
theorem qldErr_of_not (h : ¬ (48 * m * d ≤ q ∧ qldHlt ε m d q < 1)) : qldErr ε m d q = 4 :=
  if_neg h

/-- **Inside the regime, the chain's bound, capped at the trivial one.** -/
theorem qldErr_of_regime (hq : 48 * m * d ≤ q) (hlt : qldHlt ε m d q < 1) :
    qldErr ε m d q = min (qldBound ε m d q) 4 :=
  if_pos ⟨hq, hlt⟩

theorem qldErr_le_four : qldErr ε m d q ≤ 4 := by
  unfold qldErr
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem qldErr_le_qldBound (hq : 48 * m * d ≤ q) (hlt : qldHlt ε m d q < 1) :
    qldErr ε m d q ≤ qldBound ε m d q := by
  rw [qldErr_of_regime hq hlt]
  exact min_le_left _ _

theorem qldErr_nonneg (hε : 0 ≤ ε) : 0 ≤ qldErr ε m d q := by
  have h := qldBound_nonneg hε m d q
  unfold qldErr
  split_ifs
  · exact le_min h (by norm_num)
  · norm_num

/-- **The interface for the assembly of `thm:qld`.** A quantity that is at most the trivial bound
`4`, and at most `qldBound` wherever the chain applies, is at most `qldErr`. -/
theorem le_qldErr {x : ℝ} (h4 : x ≤ 4)
    (hB : 48 * m * d ≤ q → qldHlt ε m d q < 1 → x ≤ qldBound ε m d q) : x ≤ qldErr ε m d q := by
  by_cases h : 48 * m * d ≤ q ∧ qldHlt ε m d q < 1
  · rw [qldErr_of_regime h.1 h.2]
    exact le_min (hB h.1 h.2) h4
  · rw [qldErr_of_not h]
    exact h4

end Err

/-! ## Every link is small -/

namespace ErrSmall

variable {g η : ℝ → ℕ → ℕ → ℕ → ℝ}

/-- **The legs of `eq:qld-unitary-5`, at any small `MirrorSimul` error**: `deltaLegs` is linear in
`δ`, `ε`, `√(688 ε)` and `md/q`. -/
theorem deltaLegs_comp (hg : ErrSmall g) :
    ErrSmall fun ε m d q => deltaLegs (g ε m d q) ε m d q := by
  unfold deltaLegs
  exact (hg.add (((hg.add (errSmall_eps.const_mul (by norm_num)).sqrt).add
    errSmall_md_div_q).const_mul (by norm_num))).add (errSmall_eps.const_mul (by norm_num))

/-- **Item 2's bound of `lem:qld-swap`, at any small `MirrorSimul` error and item-1 bound.** -/
theorem deltaItemTwo_comp (hg : ErrSmall g) (hη : ErrSmall η) :
    ErrSmall fun ε m d q => deltaItemTwo (g ε m d q) ε m d q (η ε m d q) := by
  unfold deltaItemTwo
  exact (((hg.deltaLegs_comp.const_mul (by norm_num)).add errSmall_md_div_q).add
    (hη.sqrt.const_mul (by norm_num))).const_mul (by norm_num)

end ErrSmall

theorem errSmall_qldDelta : ErrSmall qldDelta := errSmall_deltaS

theorem errSmall_qldHlt : ErrSmall qldHlt := errSmall_itemOneEta

/-- **Item 1's bound, along the chain, is of the shape of `thm:qld`.** -/
theorem errSmall_qldEta : ErrSmall qldEta := errSmall_swapItemOne

theorem errSmall_deltaLegs : ErrSmall fun ε m d q => deltaLegs (qldDelta ε m d q) ε m d q :=
  errSmall_qldDelta.deltaLegs_comp

/-- **Item 2's bound, along the chain, is of the shape of `thm:qld`.** -/
theorem errSmall_deltaItemTwo :
    ErrSmall fun ε m d q => deltaItemTwo (qldDelta ε m d q) ε m d q (qldEta ε m d q) :=
  errSmall_qldDelta.deltaItemTwo_comp errSmall_qldEta

theorem errSmall_qldBound : ErrSmall qldBound :=
  (errSmall_deltaItemTwo.add (errSmall_qldEta.sqrt.const_mul (c := 9) (by norm_num))).congr
    fun _ _ _ _ _ _ _ _ _ => rfl

/-- **`δ_qld` is of the shape of `thm:qld`.** `ErrSmall.of_cases` at `g = 48 md/q + qldHlt`:
where `g < 1` both summands are below one, so the chain applies and `qldErr ≤ qldBound`; and
`qldErr ≤ 4` everywhere. -/
theorem errSmall_qldErr : ErrSmall qldErr := by
  refine errSmall_qldBound.of_cases
    ((errSmall_md_div_q.const_mul (c := 48) (by norm_num)).add errSmall_qldHlt) (C := 4)
    (by norm_num) fun ε m d q hε0 _ _ _ hq => ⟨qldErr_nonneg hε0, qldErr_le_four, fun hlt => ?_⟩
  have hlt' : 48 * ((m : ℝ) * d / q) + qldHlt ε m d q < 1 := hlt
  have hH := qldHlt_nonneg hε0 m d q
  have hq0 : (0 : ℝ) < q := by linarith [one_le_q_real hq]
  have hmd0 : 0 ≤ 48 * ((m : ℝ) * d / q) := by positivity
  have hmd : 48 * ((m : ℝ) * d / q) < 1 := by linarith
  rw [← mul_div_assoc, div_lt_one hq0] at hmd
  have hreg : 48 * m * d ≤ q := by
    have : ((48 * m * d : ℕ) : ℝ) < q := by push_cast; linarith
    exact_mod_cast this.le
  exact qldErr_le_qldBound hreg (by linarith)

/-- **`thm:qld`'s error, in closed form.** There are universal constants `a ≥ 1` and `0 < b < 1`
such that, for every `ε ≥ 0`, `m, d ≥ 1` and `q ≥ 2`, the error `qldErr` at the failure
probability `min ε 1` is at most `a (md)^a (ε^b + q^{-b} + 2^{-bmd})`. A strategy's failure
probability is at most one, so `min ε 1` is as good a failure bound as `ε`. -/
theorem exists_qldErr_le :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧ ∀ (ε : ℝ) (m d q : ℕ), 0 ≤ ε → 1 ≤ m → 1 ≤ d → 2 ≤ q →
      qldErr (min ε 1) m d q ≤ errShape a b ε m d q := by
  obtain ⟨a, b, ha, hb0, hb1, h⟩ := errSmall_qldErr.exists_le_min_one
  exact ⟨a, b, ha, hb0, hb1, fun ε m d q hε hm hd hq => (h ε m d q hε hm hd hq).2⟩

end MIPRE.QLD

end
