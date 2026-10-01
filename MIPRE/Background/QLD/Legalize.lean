/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Combined

@[expose] public section

/-!
# Legalizing a strategy for the Pauli basis test

The paper's strategies answer each question in the format its type prescribes: a strategy's
measurement for a `(Point, W)` question has outcomes in `F_q`, for an axis-parallel line question
outcomes of degree at most `d`, and so on. The Lean strategies of `MIPRE.QLD` are more permissive:
one answer type `Answer F m d` serves every question, so a measurement may have an element on an
answer of the wrong format. The decider rejects such an answer before running any rule
(`Question.fmtOk`), so the mass on them is controlled by the failure probability --- but "controlled
by `O(ε)`" is not "zero", and one place needs zero. `lem:qld-axis-degree` asks that the expanded
axis-parallel line measurement be *supported* on polynomials of degree at most `d`, which the
paper takes from the format and which a `dpoly` answer to an axis question breaks.

This file makes the paper's convention available at no cost. `legalize q a` keeps an answer of the
right format and replaces any other by a fixed legal default (`Question.defaultAns`); the
**legalized strategy** `legalizeStrat P` relabels every measurement along it. Four things hold, and
they are all one needs to pass to the legalized strategy without loss of generality:

* it is projective when the original is (`isPVM_legalizeStrat`);
* it has no element on an answer of the wrong format (`legalizeStrat_mats_eq_zero`,
  packaged as `LegalSupport`);
* its value in the game is at least the original's (`povmValue_le_legalizeStrat`): the decider
  rejected the answers that were changed, so no accepted pair is lost;
* every reading the rules and the conclusions use is unchanged (`rdVal_legalize_point` and its
  siblings, lifted to the measurements by `legalizeStrat_map`): the defaults read as `0`, which is
  what every reading already assigns to an ill-formatted answer. In particular the point-probe
  measurements and the hatted point measurements of the two strategies coincide
  (`ptPOVM_legalizeStrat`, `hatPtPOVM_legalizeStrat`), so a conclusion about the legalized
  strategy's point or Pauli measurements is a conclusion about the original's.

So every hypothesis of the appendix's chain holds for `legalizeStrat PA`, `legalizeStrat PB` when it
holds for `PA`, `PB`, and the extra property --- legal support --- is what
`MIPRE/Background/QLD/PaddedLines.lean` turns into the exact degree bound of `lem:qld-axis-degree`.
The campaign record had costed that lemma as "coarse-grain and pay the format-failure probability,
which changes the constants"; legalizing the strategy first costs nothing and changes no constant.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). A strategy is a family of POVMs
`P : Question F m → POVMIn (Answer F m d) R` in a player's ordered `⋆`-algebra `R`, legalizing is
the coarse-graining `POVMIn.map` along `legalize q`, and projectivity is `IsPVMIn`, which a
coarse-graining keeps (`POVMIn.isPVMIn_map`). The value comparison is the model's
(`BipartiteModel.povmValue`), by the same data processing on the Born distribution
(`BipartiteModel.sum_weight_bornProb_map`). The coarse `(Pauli, W)` measurement is unchanged by
`legalizeStrat_map` at the reading `rdPauliVec` (`rdPauliVec_legalize_pauli`,
`MIPRE/Background/QLD/Soundness.lean`). For a projective strategy `S : M.ProjStrat (qldGame hm)`
the legalized strategy is `S.adapt (qldGame hm) id id legalize legalize`, whose measurements are
`legalizeStrat S.PA` and `legalizeStrat S.PB` by definition.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare

variable {F : Type*} [Field F] {m d : ℕ}

/-! ## The default legal answer, and the legalization of an answer -/

/-- A legal answer to each question, reading as `0` under every rule's reading. -/
def Question.defaultAns : Question F m → Answer F m d
  | .point _ _ => .val 0
  | .aline _ _ _ => .apoly 0
  | .dline _ _ _ _ => .dpoly 0
  | .pauli _ => .pauliAns 0
  | .pairB _ _ => .bit 0
  | .pair _ => .bitPair 0
  | .con _ _ => .bitTriple 0
  | .var _ _ => .bit 0

theorem fmtOk_defaultAns (q : Question F m) : q.fmtOk (q.defaultAns : Answer F m d) = true := by
  cases q <;> rfl

/-- Legalize an answer: keep it if it has the question's format, replace it by the default
otherwise. -/
def legalize (q : Question F m) (a : Answer F m d) : Answer F m d :=
  if q.fmtOk a then a else q.defaultAns

theorem legalize_of_fmtOk {q : Question F m} {a : Answer F m d} (h : q.fmtOk a = true) :
    legalize q a = a :=
  if_pos h

theorem legalize_of_not_fmtOk {q : Question F m} {a : Answer F m d} (h : q.fmtOk a = false) :
    legalize q a = q.defaultAns :=
  if_neg (by rw [h]; exact Bool.false_ne_true)

/-- A legalized answer has the question's format. -/
theorem fmtOk_legalize (q : Question F m) (a : Answer F m d) : q.fmtOk (legalize q a) = true := by
  unfold legalize
  split_ifs with h
  · exact h
  · exact fmtOk_defaultAns q

/-! ## The readings are unchanged

Each rule of `fig:decider_pauli` reads an answer through one of the maps of
`MIPRE/Background/QLD/Win.lean`, all of which send an answer of the wrong format to `0`; the
defaults read as `0` too, so legalizing commutes with every reading at the question type it is
made for. -/

theorem rdVal_legalize_point (W : Bas) (y : Point F m) (a : Answer F m d) :
    rdVal (legalize (.point W y) a) = rdVal a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdVal]

theorem rdPauli_legalize_pauli (y : Point F m) (W : Bas) (a : Answer F m d) :
    rdPauli y (legalize (.pauli W) a) = rdPauli y a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdPauli, MIPRE.LowDegree.ldEnc]

theorem rdBit_legalize_pairB (W : Bas) (ω : Omega F m) (a : Answer F m d) :
    rdBit (legalize (.pairB W ω) a) = rdBit a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdBit]

theorem rdBit_legalize_var (j : Fin layout.s) (ω : Omega F m) (a : Answer F m d) :
    rdBit (legalize (.var j ω) a) = rdBit a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdBit]

theorem rdBitPair_legalize_pair (W : Bas) (ω : Omega F m) (a : Answer F m d) :
    rdBitPair W (legalize (.pair ω) a) = rdBitPair W a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdBitPair]

section Probe

variable [Algebra (ZMod 2) F]

theorem rdProbe_legalize_point (r : F) (W : Bas) (y : Point F m) (a : Answer F m d) :
    rdProbe r (legalize (.point W y) a) = rdProbe r a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdProbe, prb]

end Probe

/-! ## The legalized strategy -/

section Strategy

variable [Fintype F] [DecidableEq F] {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- A strategy is **legally supported** when it has no measurement element on an answer of the
wrong format for the question. This is the paper's standing convention on strategies. -/
def LegalSupport (P : Question F m → POVMIn (Answer F m d) R) : Prop :=
  ∀ q a, q.fmtOk a = false → (P q).op a = 0

variable [StarOrderedRing R]

/-- **The legalized strategy**: each measurement relabelled along `legalize`. -/
def legalizeStrat (P : Question F m → POVMIn (Answer F m d) R) (q : Question F m) :
    POVMIn (Answer F m d) R :=
  (P q).map (legalize q)

theorem isPVM_legalizeStrat {P : Question F m → POVMIn (Answer F m d) R}
    (hP : ∀ q, IsPVMIn (P q).op) (q : Question F m) : IsPVMIn (legalizeStrat P q).op :=
  POVMIn.isPVMIn_map (hP q) _

/-- **An answer of the wrong format has no element in the legalized strategy.** -/
theorem legalizeStrat_mats_eq_zero (P : Question F m → POVMIn (Answer F m d) R)
    {q : Question F m} {a : Answer F m d} (h : q.fmtOk a = false) :
    (legalizeStrat P q).op a = 0 := by
  rw [legalizeStrat, POVMIn.map_op]
  refine Finset.sum_eq_zero fun a' ha' => ?_
  exfalso
  have h1 : legalize q a' = a := (Finset.mem_filter.mp ha').2
  have h2 := fmtOk_legalize q a'
  rw [h1, h] at h2
  exact Bool.false_ne_true h2

theorem legalSupport_legalizeStrat (P : Question F m → POVMIn (Answer F m d) R) :
    LegalSupport (legalizeStrat P) :=
  fun _ _ h => legalizeStrat_mats_eq_zero P h

/-- **A reading that legalization does not change reads the same measurement.** -/
theorem legalizeStrat_map (P : Question F m → POVMIn (Answer F m d) R) (q : Question F m)
    {β : Type*} [Fintype β] [DecidableEq β] (rd : Answer F m d → β)
    (h : ∀ a, rd (legalize q a) = rd a) :
    (legalizeStrat P q).map rd = (P q).map rd := by
  rw [legalizeStrat, POVMIn.map_map]
  exact congrArg (fun φ => POVMIn.map φ (P q)) (funext h)

variable [Algebra (ZMod 2) F] [NeZero m]

/-- The point-probe measurements of the legalized strategy are the original's. -/
theorem ptPOVM_legalizeStrat (hm : m ∣ Fintype.card F)
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (c : Content F m) :
    ptPOVM hm (legalizeStrat P) W c = ptPOVM hm P W c :=
  legalizeStrat_map P _ _ fun a => rdProbe_legalize_point (c.omega.r W) W (c.pt W) a

/-- The point observables of the legalized strategy are the original's. -/
theorem ptObs_legalizeStrat (hm : m ∣ Fintype.card F)
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (c : Content F m) :
    ptObs hm (legalizeStrat P) W c = ptObs hm P W c := by
  rw [ptObs_eq_obs2, ptObs_eq_obs2, ptPOVM_legalizeStrat]

variable [Algebra ℂ R] [StarModule ℂ R] [StarProper R]

/-- The hatted point measurements of the legalized strategy are the original's. -/
theorem hatPtPOVM_legalizeStrat (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (u : Point F m) : hatPtPOVM (legalizeStrat P) W u = hatPtPOVM P W u := by
  rw [hatPtPOVM, hatPtPOVM, legalizeStrat_map P _ _ fun a => rdVal_legalize_point W u a]

theorem hatMats_legalizeStrat (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (u : Point F m) : hatMats (legalizeStrat P) W u = hatMats P W u := by
  funext a
  rw [hatMats, hatMats, hatPtPOVM_legalizeStrat]

end Strategy

/-! ## The value can only go up -/

section Value

variable [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] {𝒞 𝒜 ℬ : Type*} [Ring 𝒞]
  [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ]
  [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **Legalizing both strategies does not decrease the value.** The decider rejects an answer of
the wrong format before any rule runs, so an accepted pair consists of legal answers, which
legalization leaves alone; the accepted mass can only grow. -/
theorem povmValue_le_legalizeStrat (hm : m ∣ Fintype.card F) (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (PB : Question F m → POVMIn (Answer F m d) ℬ) :
    M.povmValue (qldGame hm) PA PB
      ≤ M.povmValue (qldGame hm) (legalizeStrat PA) (legalizeStrat PB) := by
  unfold BipartiteModel.povmValue
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left ?_ ((qldGame hm).μ_nonneg x y)
  unfold BipartiteModel.condWin
  have hdp := M.sum_weight_bornProb_map (PA x) (PB y) (legalize x) (legalize y)
    fun a b => if (qldGame hm).D x y a b then (1 : ℝ) else 0
  rw [show legalizeStrat PA x = (PA x).map (legalize x) from rfl,
    show legalizeStrat PB y = (PB y).map (legalize y) from rfl, hdp]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    mul_le_mul_of_nonneg_right ?_
      (M.bornProb_nonneg ((PA x).op_nonneg a) ((PB y).op_nonneg b))
  by_cases hD : (qldGame hm).D x y a b = true
  · have hleg : (qldGame hm).D x y (legalize x a) (legalize y b) = true := by
      rw [qldGame_D] at hD ⊢
      obtain ⟨ha, hb, -⟩ := of_accepts hD
      rw [legalize_of_fmtOk ha, legalize_of_fmtOk hb]
      exact hD
    rw [if_pos hD, if_pos hleg]
  · rw [if_neg hD]
    split_ifs <;> norm_num

/-- The failure probability of the legalized strategies is at most the original's: the form the
appendix's hypotheses take. -/
theorem one_sub_povmValue_legalizeStrat_le (hm : m ∣ Fintype.card F) (M : BipartiteModel 𝒞 𝒜 ℬ)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (PB : Question F m → POVMIn (Answer F m d) ℬ)
    {ε : ℝ} (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    1 - M.povmValue (qldGame hm) (legalizeStrat PA) (legalizeStrat PB) ≤ ε :=
  le_trans (sub_le_sub_left (povmValue_le_legalizeStrat hm M PA PB) 1) hfail

end Value

end MIPRE.QLD

end

end
