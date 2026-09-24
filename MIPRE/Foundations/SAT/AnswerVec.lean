/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Pcp
import MIPRE.Foundations.SAT.FmlLib

/-!
# The answer vector of a short answer determines it

`answerVec F m a` reads the tape holding `a` followed by blanks at the `2^m` positions the `m`-bit
strings number. When the tape's `a` fits in the first half of those positions, `2 |a| ≤ 2^m`, the
vector determines `a` (`answerVec_injective`): each cell `c < 2^{m-1}` is read off its two
positions, and the cells beyond hold blanks for both strings. The soundness of answer reduction
decodes the answer polynomials of a PCP proof this way.
-/

namespace MIPRE.SAT

open Cost LowDegree

/-- **Every position is numbered by an `m`-bit string.** -/
theorem exists_bitsVal_ofFn (m p : ℕ) (hp : p < 2 ^ m) :
    ∃ w : Fin m → Bool, bitsVal (List.ofFn w) = p := by
  let f : (Fin m → Bool) → Fin (2 ^ m) := fun w => ⟨bitsVal (List.ofFn w), by
    have := bitsVal_lt (List.ofFn w)
    rwa [List.length_ofFn] at this⟩
  have hinj : Function.Injective f := by
    intro w w' h
    have h' : bitsVal (List.ofFn w) = bitsVal (List.ofFn w') := congrArg Fin.val h
    exact List.ofFn_injective (bitsVal_injective (by simp) h')
  have hsurj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp⟩ |>.2
  obtain ⟨w, hw⟩ := hsurj ⟨p, hp⟩
  exact ⟨w, congrArg Fin.val hw⟩

theorem cellBits_injective : Function.Injective cellBits := by
  intro a b h
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> first | rfl | simp [cellBits] at h

/-- **The answer vector of a short answer determines it.** -/
theorem answerVec_injective {F : Type*} [CommRing F] [Nontrivial F] (m : ℕ) {a b : BitStr}
    (ha : 2 * a.length ≤ 2 ^ m) (hb : 2 * b.length ≤ 2 ^ m)
    (h : answerVec F m a = answerVec F m b) : a = b := by
  have hofBool : Function.Injective (ofBool : Bool → F) := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [ofBool]
  have htape : ∀ p < 2 ^ m, tapeBits a p = tapeBits b p := by
    intro p hp
    obtain ⟨w, hw⟩ := exists_bitsVal_ofFn m p hp
    have := congrFun h w
    simp only [answerVec, hw] at this
    exact hofBool this
  refine List.ext_getElem? fun c => ?_
  by_cases hc : 2 * c + 1 < 2 ^ m
  · have h0 := htape (2 * c) (by omega)
    have h1 := htape (2 * c + 1) hc
    simp only [tapeBits, Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left _ two_pos] at h0
    have hodd : (2 * c + 1) % 2 = 1 := by omega
    have hdiv : (2 * c + 1) / 2 = c := by omega
    simp only [tapeBits, hodd, hdiv] at h1
    simp only [one_ne_zero, if_false] at h1
    exact cellBits_injective (Prod.ext h0 h1)
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end MIPRE.SAT
