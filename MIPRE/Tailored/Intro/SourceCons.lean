/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Forms

@[expose] public section

/-!
# The input's constraints, re-indexed into the padded layout

At the edge `(introspect false, introspect true)` the introspection verifier runs the input's
decider on the two input answers carried by the two Introspect answers. For a tailored input,
that decider accepts exactly when the input's constraints hold of the two input answers
(`MIPRE.Tailored.TailoredVerifier.tgame_accepts_iff`). In the padded layout
(`MIPRE.Tailored.Intro.enc`) an Introspect answer carries the input's readable bits at offset `Q`
and its linear bits at offset `Q + R`, so an input constraint becomes a constraint on the two
tailored answers placed in two windows of each (`reindex`), and it holds exactly when the
original holds of the input answers read off those windows (`satisfies_reindex_iff`).
-/

namespace MIPRE.Tailored.Intro

open Cost

/-- Two vectors placed at two offsets of a vector of length `n`, the first before the second. -/
def place2 (n o₁ : ℕ) (w₁ : BitStr) (o₂ : ℕ) (w₂ : BitStr) : BitStr :=
  List.replicate o₁ false ++ w₁ ++ place (n - o₁ - w₁.length) (o₂ - o₁ - w₁.length) w₂

theorem length_place2 {n o₁ o₂ : ℕ} {w₁ w₂ : BitStr} (h₁ : o₁ + w₁.length ≤ o₂)
    (h₂ : o₂ + w₂.length ≤ n) : (place2 n o₁ w₁ o₂ w₂).length = n := by
  rw [place2, List.length_append, length_place (by omega)]
  simp; omega

theorem dotL_place2 {n o₁ o₂ : ℕ} {w₁ w₂ a : BitStr} (h₁ : o₁ + w₁.length ≤ o₂)
    (h₂ : o₂ + w₂.length ≤ n) (ha : a.length = n) :
    dotL (place2 n o₁ w₁ o₂ w₂) a =
      xor (dotL w₁ ((a.drop o₁).take w₁.length)) (dotL w₂ ((a.drop o₂).take w₂.length)) := by
  unfold place2
  conv_lhs => rw [← List.take_append_drop (o₁ + w₁.length) a]
  rw [dotL_append (by simp; omega)]
  have e₁ : List.replicate o₁ false ++ w₁ = place (o₁ + w₁.length) o₁ w₁ := by
    simp [place]
  rw [e₁, dotL_place (by omega) (by simp; omega),
    dotL_place (by omega) (by simp; omega)]
  simp only [List.drop_drop]
  congr 2
  · rw [List.drop_take, List.take_take]; congr 1; omega
  · congr 2; omega

variable (Q R lRa lLa lRb lLb : ℕ)

/-- The two answer windows of an input answer in the layout: the readable bits at `Q`, the
linear ones at `Q + R`. -/
def inputOf (a : BitStr) (lR lL : ℕ) : BitStr := (a.drop Q).take lR ++ (a.drop (Q + R)).take lL

/-- **An input constraint, re-indexed** onto tailored answers of lengths `la`, `lb`; a
constraint of the wrong length (never satisfied) becomes the rejecting one. -/
def reindex (la lb : ℕ) (c : BitStr) : BitStr :=
  if c.length = lRa + lLa + (lRb + lLb) + 1 then
    place2 la Q (c.take lRa) (Q + R) ((c.drop lRa).take lLa) ++
      place2 lb Q ((c.drop (lRa + lLa)).take lRb) (Q + R)
        ((c.drop (lRa + lLa + lRb)).take lLb) ++ [c.getD (lRa + lLa + (lRb + lLb)) false]
  else rejectConstraint (la + lb)

theorem dotL_split_right {c u v : BitStr} (h : u.length ≤ c.length) :
    dotL c (u ++ v) = xor (dotL (c.take u.length) u) (dotL (c.drop u.length) v) := by
  conv_lhs => rw [← List.take_append_drop u.length c]
  exact dotL_append (by simp; omega)

/-- **The re-indexed constraint holds exactly when the original holds of the input answers.** -/
theorem satisfies_reindex_iff {la lb : ℕ} {a b : BitStr} (ha : a.length = la)
    (hb : b.length = lb) (hRa : lRa ≤ R) (hLa : Q + R + lLa ≤ la) (hRb : lRb ≤ R)
    (hLb : Q + R + lLb ≤ lb) (c : BitStr) :
    Satisfies (reindex Q R lRa lLa lRb lLb la lb c) (a ++ b ++ [true]) ↔
      Satisfies c (inputOf Q R a lRa lLa ++ inputOf Q R b lRb lLb ++ [true]) := by
  have w1 : ((a.drop Q).take lRa).length = lRa := by simp; omega
  have w2 : ((a.drop (Q + R)).take lLa).length = lLa := by simp; omega
  have w3 : ((b.drop Q).take lRb).length = lRb := by simp; omega
  have w4 : ((b.drop (Q + R)).take lLb).length = lLb := by simp; omega
  have hlen : (inputOf Q R a lRa lLa ++ inputOf Q R b lRb lLb ++ [true]).length =
      lRa + lLa + (lRb + lLb) + 1 := by
    simp only [inputOf, List.length_append, w1, w2, w3, w4, List.length_singleton]
  unfold reindex
  split_ifs with hc
  · have hca : (c.take lRa).length = lRa := by simp; omega
    have hcb : ((c.drop lRa).take lLa).length = lLa := by simp; omega
    have hcc : ((c.drop (lRa + lLa)).take lRb).length = lRb := by simp; omega
    have hcd : ((c.drop (lRa + lLa + lRb)).take lLb).length = lLb := by simp; omega
    rw [satisfies_iff_dotL (by
        rw [List.length_append, List.length_append, length_place2 (by omega) (by omega),
          length_place2 (by omega) (by omega)]; simp [ha, hb]; omega),
      satisfies_iff_dotL (by rw [hlen, hc]),
      dotL_append (by rw [List.length_append, length_place2 (by omega) (by omega),
        length_place2 (by omega) (by omega)]; simp [ha, hb]),
      dotL_append (by rw [length_place2 (by omega) (by omega), ha]),
      dotL_place2 (by omega) (by omega) ha, dotL_place2 (by omega) (by omega) hb,
      hca, hcb, hcc, hcd]
    simp only [inputOf, List.append_assoc]
    rw [dotL_split_right (u := (a.drop Q).take lRa) (by rw [w1]; omega), w1,
      dotL_split_right (u := (a.drop (Q + R)).take lLa) (by rw [w2]; simp; omega), w2,
      dotL_split_right (u := (b.drop Q).take lRb) (by rw [w3]; simp; omega), w3,
      dotL_split_right (u := (b.drop (Q + R)).take lLb) (by rw [w4]; simp; omega), w4]
    simp only [List.drop_drop]
    have hlast : c.drop (lRa + lLa + lRb + lLb) = [c.getD (lRa + lLa + (lRb + lLb)) false] := by
      apply List.ext_getElem (by simp; omega)
      intro i h1 h2
      simp only [List.length_singleton] at h2
      have hi : i = 0 := by omega
      subst hi
      simp only [List.getElem_drop, List.getElem_singleton, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (show lRa + lLa + (lRb + lLb) < c.length by omega),
        Option.getD_some]
      congr 1; omega
    rw [hlast]
    simp only [Bool.xor_assoc]
  · constructor
    · intro h
      exact absurd h (not_satisfies_rejectConstraint (la + lb) (a ++ b))
    · rintro ⟨hl, -⟩
      exact absurd (hl.trans hlen) hc

end MIPRE.Tailored.Intro

end
