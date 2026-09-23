/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.GameTransportByQuestion

/-! # Perfect PCC strategies under question-dependent answer encoding

Answers can be encoded separately at each question. The encoding need only
preserve acceptance for nonzero effects on question pairs of positive weight.
This allows format and range facts supplied by an honest strategy's support.
-/

noncomputable section
namespace MIPRE.SyncStrategy
open Matrix Finset Classical
variable {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {G : SynchronousGame X A}

/-- Group outcomes using the encoder appropriate to each question. -/
def mergeAnswersByQuestion (S : SyncStrategy G) (H : SynchronousGame X B)
    (f : X → A → B) : SyncStrategy H :=
  ⟨S.d,S.d_pos,S.P.mergeByQuestion f⟩

theorem isPCC_mergeAnswersByQuestion (S : SyncStrategy G) (H : SynchronousGame X B)
    (f : X → A → B) (hμ : ∀ x y, H.μ x y = G.μ x y) (hS : S.IsPCC) :
    (S.mergeAnswersByQuestion H f).IsPCC := by
  intro x y hxy a b
  rw [hμ] at hxy
  change (S.P.mergeByQuestion f).M x a * (S.P.mergeByQuestion f).M y b =
    (S.P.mergeByQuestion f).M y b * (S.P.mergeByQuestion f).M x a
  simp only [ProjectiveMeasurement.mergeByQuestion_M, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => hS x y hxy v u

/-- Perfect play survives any encoder that preserves accepted supported pairs. -/
theorem perfect_mergeAnswersByQuestion (S : SyncStrategy G) (H : SynchronousGame X B)
    (f : X → A → B) (hμ : ∀ x y, H.μ x y = G.μ x y)
    (hD : ∀ x y a b, 0 < G.μ x y → S.P.M x a ≠ 0 → S.P.M y b ≠ 0 →
      G.D x y a b = true → H.D x y (f x a) (f y b) = true)
    (hv : S.value = 1) : (S.mergeAnswersByQuestion H f).value = 1 := by
  rw [value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro x y hxy a b hr
  rw [hμ] at hxy
  change ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos))
    ((S.P.mergeByQuestion f).M x a * (S.P.mergeByQuestion f).M y b)).re = 0
  rw [S.normalizedTrace_re_eq_ntr]
  simp only [ProjectiveMeasurement.mergeByQuestion_M, Finset.sum_mul, Finset.mul_sum, ntr_sum]
  apply Finset.sum_eq_zero
  intro v hv'
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hu0 : S.P.M x u = 0
  · simp [hu0]
  by_cases hv0 : S.P.M y v = 0
  · simp [hv0]
  have hd : G.D x y u v = false := by
    cases hd : G.D x y u v with
    | false => rfl
    | true =>
      have hh := hD x y u v hxy hu0 hv0 hd
      rw [(mem_filter.mp hu).2,(mem_filter.mp hv').2,hr] at hh
      cases hh
  rw [ntr_fin]
  exact S.re_eq_zero_of_value_eq_one hv hxy hd

end MIPRE.SyncStrategy
