/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.HonestPauliLowDegree
import MIPRE.Background.Introspection.HonestPauliEdges
import MIPRE.Foundations.Introspection.HonestMagicSquareGame

/-! # Perfect PCC play of the full Pauli basis game

All question types use the actual honest field-register measurements and a
single extra qubit. The sampler's support supplies one common content for
both questions; every graph edge is handled, including its reverse and every
self-loop. Wrong-format answers retain zero effects throughout.
-/

noncomputable section
namespace MIPRE.QLD.Honest
open Matrix Finset Weyl LCS Introspection Classical
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]

-- Keep this finite predicate calculation independent of QLD's analytical
-- swap module, whose imports include the orthonormalization development.
set_option maxHeartbeats 1000000 in
private theorem pairTest_reverse (hm : m ∣ Fintype.card F)
    (x y : Question F m) (a b : Answer F m d) :
    pairTest hm x y a b = pairTest hm y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;> simp [pairTest]

private theorem accepts_reverse (hm : m ∣ Fintype.card F)
    (x y : Question F m) (a b : Answer F m d) :
    accepts hm x y a b = accepts hm y x b a := by
  have hs : subtests hm x y a b = subtests hm y x b a := by
    rw [subtests, subtests]
    by_cases h : x.ty = y.ty
    · rw [if_pos h, if_pos h.symm]
      by_cases hab : a = b
      · rw [hab]
      · rw [decide_eq_false hab, decide_eq_false (Ne.symm hab)]
    · rw [if_neg h, if_neg (fun hc => h hc.symm), pairTest_reverse]
  rw [accepts, accepts, hs]
  cases hx : x.fmtOk a <;> cases hy : y.fmtOk b <;> simp

/-- Every positive-probability question pair comes from one actual content
and an adjacent ordered pair of types. -/
theorem qldGame_positive_content (hm : m ∣ Fintype.card F)
    (x y : Question F m) (h : 0 < (qldGame (d := d) hm).μ x y) :
    ∃ (c : Content F m) (t u : Ty), adj t u = true ∧
      x = c.question hm t ∧ y = c.question hm u := by
  have hex : ∃ sm : Sample F m,
      (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = (x, y) := by
    by_contra hn
    push Not at hn
    have hz : (qldGame (d := d) hm).μ x y = 0 := by
      change (∑ sm : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
        if (sm.2.question hm sm.1.val.1, sm.2.question hm sm.1.val.2) = (x, y)
          then 1 else 0) = 0
      simp only [if_neg (hn _), mul_zero, sum_const_zero]
    rw [hz] at h
    exact (lt_irrefl 0 h).elim
  obtain ⟨⟨e, c⟩, he⟩ := hex
  exact ⟨c, e.val.1, e.val.2, e.prop,
    (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- Same-question effects commute, including zero effects of malformed answers. -/
theorem answerOp_self_commute (hm : m ∣ Fintype.card F)
    (q : Question F m) (a b : Answer F m d) :
    Commute (answerOp hm q a) (answerOp hm q b) := by
  by_cases hab : a = b
  · subst b; exact Commute.refl _
  · change answerOp hm q a * answerOp hm q b = answerOp hm q b * answerOp hm q a
    rw [(answerOp_isPVM hm q).orthogonal hab,
      (answerOp_isPVM hm q).orthogonal (Ne.symm hab)]

/-- The actual self-loop rejects only products that vanish. -/
theorem answerOp_self_reject (hm : m ∣ Fintype.card F)
    (q : Question F m) (a b : Answer F m d)
    (hr : accepts hm q q a b = false) : answerOp hm q a * answerOp hm q b = 0 := by
  by_cases hab : a = b
  · subst b
    have hf : q.fmtOk a = false := by simpa [accepts, subtests] using hr
    rw [answerOp_format_zero hm q a hf, zero_mul]
  · exact (answerOp_isPVM hm q).orthogonal hab

private theorem adjRaw_cases (t u : Ty) (h : adjRaw t u = true) :
    (∃ W, t = .aline W ∧ u = .point W) ∨
    (∃ W, t = .dline W ∧ u = .point W) ∨
    (∃ W, t = .point W ∧ u = .pauli W) ∨
    (∃ W, t = .point W ∧ u = .pairB W) ∨
    (∃ W, t = .pairB W ∧ u = .pair) ∨
    (∃ W, t = .point W ∧ u = .var (distinguished W)) ∨
    (∃ i j, t = .con i ∧ u = .var j ∧ j ∈ MagicSquare.layout.V i) := by
  revert t u
  decide

/-- Commutation on every forward non-loop type-graph edge. -/
theorem answerOp_adjRaw_commute (hm : m ∣ Fintype.card F)
    (c : Content F m) (t u : Ty) (h : adjRaw t u = true) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm t) a) (answerOp hm (c.question hm u) b) := by
  rcases adjRaw_cases t u h with ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨i, j, rfl, rfl, hj⟩
  · exact answerOp_aline_point_commute hm c W a b
  · exact answerOp_dline_point_commute hm c W a b
  · exact (answerOp_pauli_point_commute hm c W b a).symm
  · exact answerOp_point_pairB_commute hm c.omega W a b
  · exact answerOp_pairB_pair_commute hm c.omega W a b
  · exact answerOp_point_var_commute hm c.omega W a b
  · exact answerOp_con_var_commute hm c.omega i j hj a b

/-- Rejected effects vanish on every forward non-loop edge. -/
theorem answerOp_adjRaw_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (c : Content F m) (t u : Ty) (h : adjRaw t u = true) (a b : Answer F m d)
    (hr : accepts hm (c.question hm t) (c.question hm u) a b = false) :
    answerOp hm (c.question hm t) a * answerOp hm (c.question hm u) b = 0 := by
  rcases adjRaw_cases t u h with ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨i, j, rfl, rfl, hj⟩
  · exact answerOp_aline_point_reject hm hd c W a b hr
  · exact answerOp_dline_point_reject hm hd c W a b hr
  · rw [(answerOp_pauli_point_commute hm c W b a).eq.symm]
    exact answerOp_pauli_point_reject hm c W b a
      ((accepts_reverse hm _ _ b a).trans hr)
  · exact answerOp_point_pairB_reject hm c.omega W a b hr
  · exact answerOp_pairB_pair_reject hm c.omega W a b hr
  · exact answerOp_point_var_reject hm c.omega W a b hr
  · exact answerOp_con_var_reject hm c.omega i j hj a b hr

/-- Every sampled edge, including reverse edges and self-loops, commutes. -/
theorem answerOp_sampled_commute (hm : m ∣ Fintype.card F)
    (c : Content F m) (t u : Ty) (h : adj t u = true) (a b : Answer F m d) :
    Commute (answerOp hm (c.question hm t) a) (answerOp hm (c.question hm u) b) := by
  have he : t = u ∨ adjRaw t u = true ∨ adjRaw u t = true := by
    simpa only [adj, Bool.or_eq_true, decide_eq_true_eq, or_assoc] using h
  rcases he with rfl | hf | hb
  · exact answerOp_self_commute hm _ a b
  · exact answerOp_adjRaw_commute hm c t u hf a b
  · exact (answerOp_adjRaw_commute hm c u t hb b a).symm

/-- Every rejected outcome pair on the sampler's support has zero product. -/
theorem answerOp_sampled_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (c : Content F m) (t u : Ty) (h : adj t u = true) (a b : Answer F m d)
    (hr : accepts hm (c.question hm t) (c.question hm u) a b = false) :
    answerOp hm (c.question hm t) a * answerOp hm (c.question hm u) b = 0 := by
  have he : t = u ∨ adjRaw t u = true ∨ adjRaw u t = true := by
    simpa only [adj, Bool.or_eq_true, decide_eq_true_eq, or_assoc] using h
  rcases he with rfl | hf | hb
  · exact answerOp_self_reject hm _ a b hr
  · exact answerOp_adjRaw_reject hm hd c t u hf a b hr
  · rw [(answerOp_adjRaw_commute hm c u t hb b a).eq.symm]
    exact answerOp_adjRaw_reject hm hd c u t hb b a
      ((accepts_reverse hm _ _ b a).trans hr)

/-- Commutation on the actual question distribution, without replacing it
by a type-only support condition. -/
theorem answerOp_commute (hm : m ∣ Fintype.card F)
    (x y : Question F m) (h : 0 < (qldGame (d := d) hm).μ x y) (a b : Answer F m d) :
    Commute (answerOp hm x a) (answerOp hm y b) := by
  obtain ⟨c, t, u, hadj, rfl, rfl⟩ := qldGame_positive_content hm x y h
  exact answerOp_sampled_commute hm c t u hadj a b

/-- The actual Pauli-game predicate vanishes on every rejected honest product. -/
theorem answerOp_reject (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (x y : Question F m) (h : 0 < (qldGame (d := d) hm).μ x y) (a b : Answer F m d)
    (hr : (qldGame hm).D x y a b = false) : answerOp hm x a * answerOp hm y b = 0 := by
  obtain ⟨c, t, u, hadj, rfl, rfl⟩ := qldGame_positive_content hm x y h
  exact answerOp_sampled_reject hm hd c t u hadj a b hr

/-- One honest finite-dimensional strategy for all twenty-six question types. -/
def strategy (hm : m ∣ Fintype.card F) : SyncStrategy (qldGame (d := d) hm).doubled where
  d := Fintype.card (Space F m)
  d_pos := Fintype.card_pos
  P :=
    { M := fun q a => registerOp (Fintype.equivFin (Space F m)).symm (answerOp hm q.2 a)
      selfAdjoint := fun q a => by
        rw [Matrix.star_eq_conjTranspose]
        exact (registerOp_isPVM _ (answerOp_isPVM hm q.2)).isSelfAdjoint a
      projective := fun q a => (registerOp_isPVM _ (answerOp_isPVM hm q.2)).idem a
      normalized := fun q => (registerOp_isPVM _ (answerOp_isPVM hm q.2)).sum_eq_one }

private theorem doubled_positive (hm : m ∣ Fintype.card F)
    (p q : Bool × Question F m) (h : 0 < (qldGame (d := d) hm).doubled.μ p q) :
    (p.1 = false ∧ q.1 = true) ∧ 0 < (qldGame (d := d) hm).μ p.2 q.2 := by
  have ht : p.1 = false ∧ q.1 = true := by
    by_contra hn
    simp only [MIPRE.Game.doubled_μ, if_neg hn] at h
    exact (lt_irrefl 0 h).elim
  exact ⟨ht, by simpa only [MIPRE.Game.doubled_μ, if_pos ht] using h⟩

set_option backward.isDefEq.respectTransparency false in
theorem strategy_isPCC (hm : m ∣ Fintype.card F) : (strategy (d := d) hm).IsPCC := by
  intro p q h a b
  have hc := (answerOp_commute hm p.2 q.2 (doubled_positive hm p q h).2 a b).eq
  have hh := congrArg (registerOp (Fintype.equivFin (Space F m)).symm) hc
  simpa only [strategy, registerOp_mul] using hh

set_option backward.isDefEq.respectTransparency false in
theorem strategy_value (hm : m ∣ Fintype.card F) (hd : 1 ≤ d) :
    (strategy (d := d) hm).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro p q h a b hr
  obtain ⟨ht, hm'⟩ := doubled_positive hm p q h
  have hd' : (qldGame hm).D p.2 q.2 a b = false := by
    change (if p.1 = false ∧ q.1 = true then (qldGame hm).D p.2 q.2 a b else false) = false at hr
    simpa only [if_pos ht] using hr
  have hh := congrArg (registerOp (Fintype.equivFin (Space F m)).symm)
    (answerOp_reject hm hd p.2 q.2 hm' a b hd')
  rw [show registerOp (Fintype.equivFin (Space F m)).symm
    (0 : Matrix (Space F m) (Space F m) ℂ) = 0 from rfl] at hh
  have hz : (strategy (d := d) hm).P.M p a * (strategy hm).P.M q b = 0 := by
    simpa only [strategy, registerOp_mul] using hh
  rw [hz, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

/-- The actual Pauli basis game has a perfect PCC strategy, using its field
register and one additional qubit. -/
theorem exists_perfectPCC (hm : m ∣ Fintype.card F) (hd : 1 ≤ d) :
    ∃ S : SyncStrategy (qldGame (d := d) hm).doubled,
      S.IsPCC ∧ S.value = 1 ∧ S.d = 2 * Fintype.card (Register F m) := by
  refine ⟨strategy hm, strategy_isPCC hm, strategy_value hm hd, ?_⟩
  simp [strategy, Space, Fintype.card_prod, Nat.mul_comm]

end MIPRE.QLD.Honest
end
