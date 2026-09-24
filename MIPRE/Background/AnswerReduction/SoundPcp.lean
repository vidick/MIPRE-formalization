/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundDecoded
import MIPRE.Background.AnswerReduction.Complete
import MIPRE.Foundations.SAT.AnswerVec

/-!
# Soundness of answer reduction: the PCP's soundness

Piece AR-5e of `planning/answer-reduction.md`, concluded (`lem:ar-ora`): the hypothesis
`PcpSound` of `SoundDecoded` holds for the answer-reduced verifier's game check, with the decoder
`decAns`, which reads a polynomial's Boolean values as the answer vector of a short answer.

An outcome `f` of the extracted `J` carries a PCP proof (`pcpOf`): its five answer polynomials
are `f`'s first five components read on their blocks, its constraint polynomials are the rest.
When `f` is placed on its blocks, the evaluations the game check reads are that proof's
(`eval_ofProof_pcpOf`), so the check accepting at more than half the points is the PCP verifier
accepting the proof there, and the PCP decider's soundness (`SAT.PcpDecider.soundness`) decodes
the proof's first two answer polynomials to answers the input decider accepts. Those answers are
at most `inAns` long, since the input decider rejects longer ones, and the answer vector
determines a short answer (`SAT.answerVec_injective`), so they are what `decAns` returns.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost

/-! ## The decoder -/

section Decode

variable (P : PcpParams) (hk : 1 ≤ P.k) (B' : ℕ)

open Classical in
/-- **The decoder**: the answer of length at most `B'` whose answer vector a polynomial's Boolean
values are, where there is one. -/
def decAns (g : MvPolynomial (Fin P.m) (Fq P hk)) : Verifier.Answers B' :=
  if h : ∃ a : Verifier.Answers B', coded g = answerVec (Fq P hk) P.m a.1 then h.choose
  else default

/-- **The decoder returns the answer a polynomial encodes**, when answers of length `B'` fit in
the first half of the `2^m` positions. -/
theorem decAns_eq (h2 : 2 * B' ≤ 2 ^ P.m) {g : MvPolynomial (Fin P.m) (Fq P hk)} {a : BitStr}
    (ha : a.length ≤ B') (hg : coded g = answerVec (Fq P hk) P.m a) :
    decAns P hk B' g = ⟨a, ha⟩ := by
  have hex : ∃ a' : Verifier.Answers B', coded g = answerVec (Fq P hk) P.m a'.1 :=
    ⟨⟨a, ha⟩, hg⟩
  rw [decAns, dif_pos hex]
  have h' := hex.choose.2
  apply Subtype.ext
  show hex.choose.1 = a
  exact answerVec_injective P.m (by omega) (by omega) (hex.choose_spec.symm.trans hg)

end Decode

/-! ## The PCP proof an outcome carries -/

section Proof

variable (P : PcpParams) (hk : 1 ≤ P.k) [NeZero P.m]

/-- **The PCP proof an outcome of `J` carries**: its first five components read on their blocks,
then the remaining `m' + 1` as the constraint polynomials. -/
def pcpOf (f : Poly6 P hk) : PcpProof P (Fq P hk) where
  g i := gPoly P hk i f
  c j := (f ⟨j + 5, by have := j.isLt; omega⟩).toMv
  degreeOf_g _ i := LowIndDegPoly.degreeOf_toMv_le _ i
  degreeOf_c _ i := LowIndDegPoly.degreeOf_toMv_le _ i

/-- **The evaluations of a placed outcome are its proof's**: the sixth copy's data built from the
proof evaluates as the outcome does. -/
theorem eval_ofProof_pcpOf {f : Poly6 P hk} (hbl : BlockLocal P hk f) (z : Fin P.m' → Fq P hk) :
    (fun j => MvPolynomial.eval z ((ofProof hk (pcpOf P hk f)).c j)) = fun j => (f j).eval z := by
  funext j
  simp only [ofProof, pcpOf]
  split_ifs with h
  · conv_rhs => rw [show j = blk P ⟨j, h⟩ from Fin.ext rfl, hbl ⟨j, h⟩]
    rw [MvPolynomial.eval_rename, gPoly, LowIndDegPoly.eval_toMv, liftBlk,
      LowIndDegPoly.eval_liftIdx (blockEmb_injective _)]
    rfl
  · rw [LowIndDegPoly.eval_toMv]
    congr 2
    exact Fin.ext (by simp only; omega)

end Proof

/-! ## The PCP's soundness, for the answer-reduced verifier -/

section Final

variable (PD : PcpDecider) (lam mu sigma : ℕ) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ)

local notation "F" => family PD lam mu sigma

/-- **The PCP's soundness, as the decoded strategy needs it**, for the answer-reduced verifier's
game check and the decoder `decAns`. -/
theorem pcpSound (hF : ShoupField PD) (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hV : V.Within n (inBudget lam mu n)) (hsz : V.decider.size ≤ sigma) :
    PcpSound V n ((F).par n) ((F).hk n) (chk PD V lam mu sigma n) (inAns lam mu n)
      (decAns ((F).par n) ((F).hk n) (inAns lam mu n)) := by
  intro y f hbl hcnt
  have hE : PD.fld (PD.params n (tPcp lam mu n) (arQ lam mu n) sigma).k
      (PD.odd_k n (tPcp lam mu n) (arQ lam mu n) sigma) = fld ((F).par n) ((F).hk n) := by
    rw [hF]; rfl
  have hS := PD.soundness V.decider n (tPcp lam mu n) (arQ lam mu n) sigma _ _
    (valid_of V lam mu sigma n hlam hmu hV hsz y)
  rw [hE] at hS
  have hset : (univ.filter fun z => chk PD V lam mu sigma n y z (fun j => (f j).eval z) = true)
      = univ.filter fun z => PD.verify (pcpInput V.decider.prog n (tPcp lam mu n) (arQ lam mu n)
          sigma (toBits ((V.sampler.cl n .alice).eval y)) (toBits ((V.sampler.cl n .bob).eval y))
          ((pcpOf ((F).par n) ((F).hk n) f).rawView (fld ((F).par n) ((F).hk n)) z).1
          ((pcpOf ((F).par n) ((F).hk n) f).rawView (fld ((F).par n) ((F).hk n)) z).2) = true :=
    Finset.filter_congr fun z _ => by
      rw [← eval_ofProof_pcpOf _ _ hbl z]
      simp only [chk, gameCheck, PcpProof.rawView]
      rw [vecBits_ofProof]
  have hcard : Fintype.card (Fin ((F).par n).m' → Fq ((F).par n) ((F).hk n))
      = ((F).par n).q ^ ((F).par n).m' := by
    rw [Fintype.card_fun, Fintype.card_fin, card_fq]
    rfl
  rw [hset, hcard] at hcnt
  obtain ⟨ap, bp, hap, hbp, hacc, h0, h1⟩ := hS (pcpOf ((F).par n) ((F).hk n) f) hcnt
  have hacc' := hacc.accepts
  have hlen : ap.length ≤ inAns lam mu n ∧ bp.length ≤ inAns lam mu n := by
    by_contra hc
    rw [not_and_or, not_le, not_le] at hc
    exact hV.rejectsLong _ _ _ _ hc hacc'
  have hAT : inAns lam mu n ≤ tPcp lam mu n := show 2 ^ arQ lam mu n ≤ _ from
    Nat.pow_le_pow_right (by norm_num)
    (by have := Nat.le_mul_of_pos_right (arQ lam mu n + 5) (show 0 < mu + 1 by omega); omega)
  have h2 : 2 * inAns lam mu n ≤ 2 ^ ((F).par n).m :=
    (Nat.mul_le_mul_left 2 hAT).trans (PD.two_mul_le n (tPcp lam mu n) (arQ lam mu n) sigma)
  have hd0 := decAns_eq ((F).par n) ((F).hk n) (inAns lam mu n) h2 hlen.1 h0
  have hd1 := decAns_eq ((F).par n) ((F).hk n) (inAns lam mu n) h2 hlen.2 h1
  change (V.seeded n (inAns lam mu n)).D ((V.sampler.cl n .alice).eval y)
    ((V.sampler.cl n .bob).eval y) (decAns ((F).par n) ((F).hk n) (inAns lam mu n)
      ((pcpOf ((F).par n) ((F).hk n) f).g 0)) (decAns ((F).par n) ((F).hk n) (inAns lam mu n)
      ((pcpOf ((F).par n) ((F).hk n) f).g 1)) = true
  rw [hd0, hd1]
  simpa [SeededGame.ofCL, Verifier.game] using hacc'

/-- **The input verifier's value from a strategy for the answer-reduced typed game**: at least
`1 - 24 √(7 errD)`, `errD` the combined error of the strategy's analysis. -/
theorem valStar_ge_of_typedGame (hF : ShoupField PD) (hlam : 1 ≤ lam) (hmu : 1 ≤ mu)
    (hV : V.Within n (inBudget lam mu n)) (hsz : V.decider.size ≤ sigma) (B : ℕ)
    (T : TensorProductStrategy (typedGame V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n)
      (chk PD V lam mu sigma n) B)) :
    1 - 24 * √(7 * errD V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n)
        (chk PD V lam mu sigma n) B T) ≤ V.valStar n (inAns lam mu n) :=
  valStar_ge_decoded V n ((F).par n) ((F).hk n) ((F).sel n) ((F).sel' n)
    (chk PD V lam mu sigma n) B T (inAns lam mu n)
    (decAns ((F).par n) ((F).hk n) (inAns lam mu n))
    (pcpSound PD lam mu sigma V n hF hlam hmu hV hsz)

end Final

end MIPRE.AnswerReduction

end
