/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.Sound
public import MIPRE.Tailored.ExtendSpec

@[expose] public section

/-!
# The output verifier of the answer reduction, from its specification

Slice P4h of `planning/aldous-lyons-track.md`, its semantic half. The output tailored verifier of
the answer reduction at an index `n` *meets* the answer-reduced game presented by the typed data
`tdata` on the typed game of an answer-reduced sampler (`ArMeets`) when its sampler's distribution
is the presented game's weights along an equivalence of the questions, and its two programs
output the presented lengths and constraints (`TailoredVerifier.MeetsAt`). Then its `n`-th game
extends the presented one, and the two clauses of prop:completeness_soundness_combi_ans_red
(II:10487) carry over to it:

* `hasPerfectZPC_of_arMeets`: completeness, from `hasPerfectZPC_ar` (P4d);
* `valStar_sound_of_arMeets`: soundness, from `valStar_ar_sound` (P4e).

What remains for the contract is the output's programs and the proof that they meet the
presented game (P4h's programs), and the parameters under which the hypotheses hold (P4i).
-/

namespace MIPRE.Tailored.AnsRed.Typed

open Cost MIPRE.CL MIPRE.SAT

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}
  {ℓW : ℕ} {W : TailoredVerifier ℓW}

variable (d hM sel L hLM V n Cc hm P B) in
/-- **The answer-reduced game presented by the typed data**, on the typed game of the CL
functions `P`, with answers bounded by `B`. -/
noncomputable abbrev arPresented :
    TailoredGame (Detyping.Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t)) → ZMod 2) :=
  presented arGraph (CL.Detyping.game arGraph P (arDt d hM sel L hLM V n Cc hm B))
    (tdata t ht j d L (V.sampler.dim n) sel hLM (circOf L V n Cc hm))

variable (d hM sel L hLM V n Cc hm P B W) in
/-- **The output verifier `W` meets the presented answer-reduced game at `n`** along `e`. -/
abbrev ArMeets (e : (Detyping.Coord (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t)) →
    ZMod 2) ≃ W.Questions n) : Prop :=
  W.MeetsAt n (arPresented d hM sel L hLM V n Cc hm P B) e

/-- **Completeness of the output verifier**: a perfect ZPC strategy of the input's `n`-th game
gives one of the output's, for a degree `d ≥ 17`, an answer bound at least the types' lengths,
and circuits under which the honest PCPs of accepted answers satisfy the checks. -/
theorem hasPerfectZPC_of_arMeets {e : (Detyping.Coord (Role × LIDT.CL.Ty)
      (Fin (V.sampler.dim n + D j * t)) → ZMod 2) ≃ W.Questions n}
    (h : ArMeets d hM sel L hLM V n Cc hm P B W e) {prm : PolyTimeFun ℕ (Unary × Unary)}
    {Tt : ℕ} (H : HonestHyp L V n prm Cc Tt) (hd : 17 ≤ d) (hP : ArSampler hM sel V n P)
    (hℓ : 0 < ℓ) (hB : ∀ u, len t j d L u ≤ B) (hV : V.HasPerfectZPC n) : W.HasPerfectZPC n :=
  h.hasPerfectZPC (hasPerfectZPC_ar d hM sel L hLM V n Cc hm P H hd hP hℓ hB hV)

/-- **Soundness of the output verifier**: if the output's `n`-th game has `val* > 1 - ε`, then
`val*(𝒱_n) ≥ 1 - 24 √(errAR (16⁹ ε))`, once the field has `2 (M + 1) d` and
`2 m (5 + 6(d + 1))` elements. -/
theorem valStar_sound_of_arMeets {e : (Detyping.Coord (Role × LIDT.CL.Ty)
      (Fin (V.sampler.dim n + D j * t)) → ZMod 2) ≃ W.Questions n}
    (h : ArMeets d hM sel L hLM V n Cc hm P B W e) {prm : PolyTimeFun ℕ (Unary × Unary)}
    {Tt : ℕ} (H : HonestHyp L V n prm Cc Tt) (hd : 1 ≤ d) (hP : ArSampler hM sel V n P)
    (hℓ : 0 < ℓ) (hB : ∀ u, len t j d L u ≤ B)
    (hq : 2 * ((2 ^ j + 1) * d) ≤ Fintype.card (Fq t ht))
    (hτ : 2 * (L.m * chkDeg 5 d) ≤ Fintype.card (Fq t ht)) {ε : ℝ} (hε : 0 < ε)
    (hv : 1 - ε < W.valStar n) :
    1 - 24 * √(errAR t ht j d L (16 ^ 9 * ε)) ≤ V.valStar n :=
  valStar_ar_sound H hd hP hℓ hB hq hτ hε (by rwa [← h.valStar_eq])

end MIPRE.Tailored.AnsRed.Typed

end
