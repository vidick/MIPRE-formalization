/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.IndicatorProg
public import MIPRE.Tailored.CanonicalCost

@[expose] public section

/-!
# The running time of the output indicator

The time bound of `L*` (eq:time_bound_L*, II:8516) in the relative-cost reading: on an encoded
input `(n, x, y, a, b)`, the output indicator `lstarProg prm L LP` halts within `lstarBound`, an
explicit function of the time `T (|d| + 1)^k` of the calls of `L` and `LP` on inputs `(n, d)`, of
the size of the input, and of the time bound of the check, polynomial in the size of the state it
reads (`lstarProg_halts`). So it accepts what it accepts within that bound
(`lstar_acceptsWithin`), the form in which the describer of `lem:ar-window-describer` reads it.
The check is polynomial in its input and its input holds the answers `a` and `b`, so the bound is
polynomial in their lengths: on the honest answers, in `2^ℓ` and `2^◇`.
-/

namespace MIPRE.Tailored.AnsRed

open Cost Cost.PolyTimeFun Cost.Data

/-- The explicit bound on the running time of the output indicator on an encoded input of size
`S`, from the time `T Z^k` of a call whose argument has size less than `Z`. -/
noncomputable def lstarBound (prm : PolyTimeFun ℕ (Unary × Unary)) (T k S Z : ℕ) : ℕ :=
  let Y := T * Z ^ k
  let A1 := Y + S + 1
  let A2 := Y + A1 + 1
  let A3 := Y + A2 + 1
  let A4 := Y + A3 + 1
  let A5 := Y + A4 + 1
  (2 * canonIn₁.timeBound.eval S + 2 * Y + S + 8) +
    (2 * canonIn₂.timeBound.eval A1 + 2 * Y + A1 + 8) +
    (2 * canonIn₃.timeBound.eval A2 + 2 * Y + A2 + 8) +
    (2 * canonIn₄.timeBound.eval A3 + 2 * Y + A3 + 8) +
    (2 * canonIn₅.timeBound.eval A4 + 2 * Y + A4 + 8) +
    (lstarFinal prm).timeBound.eval A5 + 5

/-- **The output indicator halts within `lstarBound`** on an encoded input of index `n`, when `L`
and `LP` halt within `T (|d| + 1)^k` on every input `(n, d)`: every call's argument is a
component of the input, of size at most twice its size. -/
theorem lstarProg_halts (prm : PolyTimeFun ℕ (Unary × Unary)) {L P : Prog}
    (hL : L.WellScoped 1) (hP : P.WellScoped 1) {n T k : ℕ}
    (hLt : ∀ d : Data, HaltsWithin L (.cons (encode n) d) (T * (d.size + 1) ^ k))
    (hPt : ∀ d : Data, HaltsWithin P (.cons (encode n) d) (T * (d.size + 1) ^ k)) (i : DIn)
    (hi : i.1 = n) :
    HaltsWithin (lstarProg prm L P) (encode i)
      (lstarBound prm T k (esize i) (2 * esize i + 2)) := by
  obtain ⟨n', x, y, a, b⟩ := i
  subst hi
  have hb := esize_bool_le' false
  have hb' := esize_bool_le' true
  have hS : esize ((n', x, y, a, b) : DIn) =
      esize n' + esize x + esize y + esize a + esize b + 4 := by
    simp only [esize_prod]; omega
  obtain ⟨r₁, t₁, h₁, hr₁, ht₁⟩ := step_runs canonIn₁ hL hLt (n', x, y, a, b) rfl
    (Z := 2 * esize ((n', x, y, a, b) : DIn) + 2) (by simp only [canonIn₁_apply, esize_prod]; omega)
  obtain ⟨r₂, t₂, h₂, hr₂, ht₂⟩ := step_runs canonIn₂ hL hLt (r₁, (n', x, y, a, b)) rfl
    (Z := 2 * esize ((n', x, y, a, b) : DIn) + 2) (by simp only [canonIn₂_apply, esize_prod]; omega)
  obtain ⟨r₃, t₃, h₃, hr₃, ht₃⟩ := step_runs canonIn₃ hL hLt (r₂, r₁, (n', x, y, a, b)) rfl
    (Z := 2 * esize ((n', x, y, a, b) : DIn) + 2) (by simp only [canonIn₃_apply, esize_prod]; omega)
  obtain ⟨r₄, t₄, h₄, hr₄, ht₄⟩ := step_runs canonIn₄ hL hLt (r₃, r₂, r₁, (n', x, y, a, b)) rfl
    (Z := 2 * esize ((n', x, y, a, b) : DIn) + 2) (by simp only [canonIn₄_apply, esize_prod]; omega)
  obtain ⟨r₀, t₅, h₅, hr₀, ht₅⟩ := step_runs canonIn₅ hP hPt (r₄, r₃, r₂, r₁, (n', x, y, a, b))
    rfl (Z := 2 * esize ((n', x, y, a, b) : DIn) + 2) (by
      simp only [canonIn₅_apply, esize_prod]
      have ha : esize (a.take (spineList r₁).length) ≤ esize a := RepProg.esize_take_le a _
      have hb₂ : esize (b.take (spineList r₃).length) ≤ esize b := RepProg.esize_take_le b _
      omega)
  obtain ⟨tf, htf, hf⟩ := (lstarFinal prm).computes (r₀, r₄, r₃, r₂, r₁, (n', x, y, a, b))
  have c₄ := seqProg_runs (lstarFinal prm).closed h₅ hf
  have c₃ := seqProg_runs (lstarTail₄_wellScoped prm hP) h₄ c₄
  have c₂ := seqProg_runs (lstarTail₃_wellScoped prm hL hP) h₃ c₃
  have c₁ := seqProg_runs (lstarTail₂_wellScoped prm hL hP) h₂ c₂
  have c₀ := seqProg_runs (lstarTail₁_wellScoped prm hL hP) h₁ c₁
  refine ⟨_, _, ?_, c₀⟩
  unfold lstarBound
  dsimp only
  generalize hY : T * (2 * esize ((n', x, y, a, b) : DIn) + 2) ^ k = Y at *
  set S := esize ((n', x, y, a, b) : DIn) with hS'
  have a1 : esize (r₁, ((n', x, y, a, b) : DIn)) ≤ Y + S + 1 := by
    rw [esize_prod, esize_data]; omega
  have a2 : esize (r₂, r₁, ((n', x, y, a, b) : DIn)) ≤ Y + (Y + S + 1) + 1 := by
    rw [esize_prod, esize_data]; omega
  have a3 : esize (r₃, r₂, r₁, ((n', x, y, a, b) : DIn)) ≤ Y + (Y + (Y + S + 1) + 1) + 1 := by
    rw [esize_prod, esize_data]; omega
  have a4 : esize (r₄, r₃, r₂, r₁, ((n', x, y, a, b) : DIn)) ≤
      Y + (Y + (Y + (Y + S + 1) + 1) + 1) + 1 := by
    rw [esize_prod, esize_data]; omega
  have a5 : esize (r₀, r₄, r₃, r₂, r₁, ((n', x, y, a, b) : DIn)) ≤
      Y + (Y + (Y + (Y + (Y + S + 1) + 1) + 1) + 1) + 1 := by
    rw [esize_prod, esize_data]; omega
  have m2 := polynomial_eval_mono canonIn₂.timeBound a1
  have m3 := polynomial_eval_mono canonIn₃.timeBound a2
  have m4 := polynomial_eval_mono canonIn₄.timeBound a3
  have m5 := polynomial_eval_mono canonIn₅.timeBound a4
  have mf := polynomial_eval_mono (lstarFinal prm).timeBound a5
  omega

/-- **The output indicator accepts within `lstarBound`** whatever it accepts, on a tailored
verifier whose two programs halt within `T (|d| + 1)^k` on every input `(n, d)`. -/
theorem lstar_acceptsWithin (prm : PolyTimeFun ℕ (Unary × Unary)) {ℓ : ℕ}
    (V : TailoredVerifier ℓ) {n T k : ℕ} (hLt : V.len.TimeBoundAt n T k)
    (hPt : V.lp.TimeBoundAt n T k) {x y a b : BitStr}
    (h : (lstar prm V).Accepts n x y a b) :
    (lstar prm V).AcceptsWithin n x y a b
      (lstarBound prm T k (esize ((n, x, y, a, b) : DIn))
        (2 * esize ((n, x, y, a, b) : DIn) + 2)) := by
  obtain ⟨r, t, ht, hrun⟩ := lstarProg_halts prm V.len.closed V.lp.closed hLt hPt
    (n, x, y, a, b) rfl
  obtain ⟨t', h'⟩ := h
  obtain ⟨rfl, rfl⟩ := Eval.deterministic hrun h'
  exact ⟨t, ht, hrun⟩

end MIPRE.Tailored.AnsRed

end
