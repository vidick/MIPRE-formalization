/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Encoded
public import MIPRE.Tailored.ZPC

@[expose] public section

/-!
# The input strategy's answer bits

The honest strategy of the introspection verifier runs the input's strategy, as the synchronous
strategy of `lem:zpc-pcc` (`PermStrategy.toSync`): at a question `x` it measures answer strings,
charging those of length `len x` with the Fourier transform of the observables at `x`. The
introspection verifier's answers carry the input's answer, re-encoded (padded), so the bit
observables of the honest strategy include those of `ansProj` along an encoding of the input's
answers. This file computes them: a bit that copies the `j`-th answer bit has observable
`U(x, j)` (`encObs_ansProj_bit`), and a constant bit has observable `±1`
(`encObs_ansProj_const`).
-/

namespace MIPRE.Tailored.PermStrategy

open Finset

variable {X : Type*} [Fintype X] {G : TailoredGame X} (S : PermStrategy G) {T k : ℕ}

/-- The bit observables of the measurement on answer strings, as weightings of the measurement
on answer vectors. -/
theorem encObs_ansProj (x : X) (hT : G.len x ≤ T) (enc : Verifier.Answers T → Fin k → Bool)
    (i : Fin k) :
    encObs (S.ansProj T x) enc i = pvmObs (S.proj x) fun v => bitSign (enc (ofVec hT v) i) := by
  rw [encObs, pvmObs, pvmObs]
  have h : ∀ a : Verifier.Answers T, bitSign (enc a i) • S.ansProj T x a =
      if a.1.length = G.len x then
        bitSign (enc (ofVec hT (bitVec (G.len x) a)) i) • S.proj x (bitVec (G.len x) a) else 0 := by
    intro a
    unfold ansProj
    split_ifs with ha
    · rw [show ofVec hT (bitVec (G.len x) a) = a from Subtype.ext (ofFn_bitVec a ha)]
    · rw [smul_zero]
  rw [Finset.sum_congr rfl fun a _ => h a]
  exact sum_answers_ite hT fun v => bitSign (enc (ofVec hT v) i) • S.proj x v

/-- **A bit copying the `j`-th answer bit has observable `U(x, j)`.** -/
theorem encObs_ansProj_bit (x : X) (hT : G.len x ≤ T) (enc : Verifier.Answers T → Fin k → Bool)
    (i : Fin k) (j : Fin (G.len x)) (h : ∀ v, enc (ofVec hT v) i = v j) :
    encObs (S.ansProj T x) enc i = S.U x j := by
  rw [encObs_ansProj S x hT]
  simp_rw [h]
  exact pvmObs_fourierProj_bit (S.invol x) (S.star_U x) (S.commute_U x) j

/-- **A constant bit has observable `±1`.** -/
theorem encObs_ansProj_const (x : X) (hT : G.len x ≤ T) (enc : Verifier.Answers T → Fin k → Bool)
    (i : Fin k) (c : Bool) (h : ∀ v, enc (ofVec hT v) i = c) :
    encObs (S.ansProj T x) enc i = bitSign c • 1 := by
  rw [encObs_ansProj S x hT]
  simp_rw [h]
  exact (S.isPVMIn_proj x).pvmObs_const _

end MIPRE.Tailored.PermStrategy

end
