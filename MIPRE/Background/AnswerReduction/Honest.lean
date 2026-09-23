/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Predicate
import MIPRE.Background.LIDT.CLHonest

/-!
# Honest answers of the answer-reduced verifier

Piece AR-4 of `planning/answer-reduction.md`, the combinatorial half: the decision predicate
`accepts` of `fig:decider-pcp` accepts the honest answers of two players who answer from
polynomial data that is consistent in the ways the five steps check.

A player's data (`HPolys`) is five `m`-variate polynomials `g₁ … g₅`, one for each of the first
five copies of the low-degree test, and `m' + 6` `m'`-variate polynomials `c`, the codewords of the
sixth copy. Its honest answer to a question of type `(i, τ)` (`honestAns`) is the honest answer
(`LIDT.CL.honest`) of `gᵢ`, or of `c` for the sixth copy, to the seeded question the type's
presentation computes. In the paper (`ld_compiler.tex`, the completeness part of `thm:ar`):

* an oracle's data is the PCP proof of its pair of answers: `g₁, g₂` the low-degree encodings of
  the two answers, `g₃ … g₅` the proof's other answer polynomials, and `c` the five `gᵢ` read on
  their blocks of `F^{m'}` followed by the constraint polynomials (`HPolys.Oracle`);
* an isolated player's data has for `g_v` the low-degree encoding of its own answer, `v` its
  role's index, and anything of low degree elsewhere (zero, in AR-4's instance).

`accepts_honest` is the statement: for two questions read off one PCP vector, players whose data
is of individual degree at most `d = 7` (`HPolys.LowDeg`), equal for equal roles, with the oracle's
`g_v` the isolated player `v`'s, and with an oracle's data passing its PCP check at every point,
are accepted.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp

variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A player's polynomial data**: the answer polynomials of the first five copies, and the
codewords of the sixth. -/
structure HPolys (P : PcpParams) (F : Type*) [Field F] where
  /-- The polynomials of copies `1`–`5`. -/
  g : Fin 5 → MvPolynomial (Fin P.m) F
  /-- The `m' + 6` codewords of copy `6`. -/
  c : Fin (P.m' + 6) → MvPolynomial (Fin P.m') F

namespace HPolys

/-- Every polynomial has individual degree at most `d = 7`. -/
def LowDeg (H : HPolys P F) : Prop :=
  (∀ j i, (H.g j).degreeOf i ≤ dPcp) ∧ ∀ j i, (H.c j).degreeOf i ≤ dPcp

/-- The index `j ≤ 5` of a first-five copy among the sixth copy's codewords. -/
def idx6 (j : Fin 5) : Fin (P.m' + 6) := ⟨j, by have := j.isLt; omega⟩

/-- An oracle's data: the sixth copy's first five codewords are the `gⱼ` read on their blocks,
and every point's evaluations pass the check `chk`. -/
def Oracle (H : HPolys P F) (chk : (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool) : Prop :=
  (∀ (j : Fin 5) (z : Fin P.m' → F),
      MvPolynomial.eval z (H.c (idx6 j)) = MvPolynomial.eval (P.block j z) (H.g j)) ∧
    ∀ z, chk z (fun j => MvPolynomial.eval z (H.c j)) = true

end HPolys

variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')

/-- **The honest answer** of a player with data `H` to the question of PCP type `t` read off `y`. -/
def honestAns (H : HPolys P F) (t : PcpTy) (y : Coord P → F) : Ans P F :=
  if h : (t.1 : ℕ) < 5 then
    .inl (LIDT.CL.honest hm (d := dPcp) (fun _ => H.g ⟨t.1, h⟩) (q1 S ⟨t.1, h⟩ t.2 y))
  else .inr (LIDT.CL.honest hm' (d := dPcp) H.c (q6 S' t.2 y))

theorem honestAns_lt (H : HPolys P F) {i : Fin 6} (τ : Ty) (y : Coord P → F)
    (h : (i : ℕ) < 5) : honestAns S S' H (i, τ) y =
      .inl (LIDT.CL.honest hm (d := dPcp) (fun _ => H.g ⟨i, h⟩) (q1 S ⟨i, h⟩ τ y)) := by
  simp [honestAns, h]

theorem honestAns_six (H : HPolys P F) {i : Fin 6} (τ : Ty) (y : Coord P → F)
    (h : (i : ℕ) = 5) : honestAns S S' H (i, τ) y =
      .inr (LIDT.CL.honest hm' (d := dPcp) H.c (q6 S' τ y)) := by
  simp [honestAns, h]

theorem ansFmt_honestAns (H : HPolys P F) (t : PcpTy) (y : Coord P → F) :
    ansFmt t (honestAns S S' H t y) = true := by
  obtain ⟨i, τ⟩ := t
  by_cases h : (i : ℕ) < 5
  · rw [honestAns_lt S S' H τ y h]
    cases τ <;> simp [ansFmt, tyFmt, h, q1, Sample.question, LIDT.CL.honest]
  · have h5 : (i : ℕ) = 5 := by omega
    rw [honestAns_six S S' H τ y h5]
    cases τ <;> simp [ansFmt, tyFmt, h5, q6, Sample.question, LIDT.CL.honest]

/-! ## The questions of one PCP vector -/

omit [NeZero P.m] in
theorem ptOf_point_eval {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} [NeZero n]
    {hn : n ∣ Fintype.card F} (R : Regs ι n) (Sn : Sel F n hn) (w : ι → F) :
    R.ptOf ((R.pres Sn .point).eval w) = R.ptOf w := by
  have h := Regs.questionOf_eval R Sn .point w
  simp only [Regs.questionOf, Regs.sampleOf, Sample.question, CL.Question.point.injEq] at h
  exact h

theorem pres_lt (w : Coord P → F) {i : Fin 6} (τ : Ty) (h : (i : ℕ) < 5) :
    (pres P S S' (i, τ)).eval w = ((regs P ⟨i, h⟩).pres S τ).eval w := by
  simp [pres, h]

theorem pres_six (w : Coord P → F) {i : Fin 6} (τ : Ty) (h : (i : ℕ) = 5) :
    (pres P S S' (i, τ)).eval w = ((regs6 P).pres S' τ).eval w := by
  simp [pres, h]

/-- The point of copy `v`'s register, in the `Point_v` question. -/
theorem ptOf_regs_point (w : Coord P → F) (v : Fin 5) :
    (regs P v).ptOf ((pres P S S' (v.castSucc, .point)).eval w) = (regs P v).ptOf w := by
  rw [pres_lt S S' w .point (by simp)]
  exact ptOf_point_eval _ _ w

/-- The point of copy `v`'s register, in the `Point_6` question: the `v`-th block. -/
theorem ptOf_regs_point6 (w : Coord P → F) (v : Fin 5) {i : Fin 6} (h : (i : ℕ) = 5) :
    (regs P v).ptOf ((pres P S S' (i, .point)).eval w) = (regs P v).ptOf w := by
  rw [pres_six S S' w .point h, ← block_ptOf_regs6, ptOf_point_eval, block_ptOf_regs6]

theorem q1_eval (w : Coord P → F) (v : Fin 5) (τ : Ty) :
    q1 S v τ ((pres P S S' (v.castSucc, τ)).eval w) =
      ((regs P v).sampleOf S τ w).question hm τ := by
  rw [pres_lt S S' w τ (by simp), q1]
  exact Regs.sampleOf_eval_question _ _ _ _

theorem q6_eval (w : Coord P → F) {i : Fin 6} (τ : Ty) (h : (i : ℕ) = 5) :
    q6 S' τ ((pres P S S' (i, τ)).eval w) = ((regs6 P).sampleOf S' τ w).question hm' τ := by
  rw [pres_six S S' w τ h, q6]
  exact Regs.sampleOf_eval_question _ _ _ _

theorem ptOf_regs6_point (w : Coord P → F) {i : Fin 6} (h : (i : ℕ) = 5) :
    (regs6 P).ptOf ((pres P S S' (i, .point)).eval w) = (regs6 P).ptOf w := by
  rw [pres_six S S' w .point h, ptOf_point_eval]

/-! ## Reading the honest answers -/

theorem val1_honest (H : HPolys P F) (v : Fin 5) (y : Coord P → F) :
    val1 (honestAns S S' H (v.castSucc, .point) y) =
      MvPolynomial.eval ((regs P v).ptOf y) (H.g v) := by
  rw [honestAns_lt S S' H .point y (by simp)]
  rfl

theorem val6_honest (H : HPolys P F) {i : Fin 6} (h : (i : ℕ) = 5) (j : Fin (P.m' + 6))
    (y : Coord P → F) :
    val6 j (honestAns S S' H (i, .point) y) = MvPolynomial.eval ((regs6 P).ptOf y) (H.c j) := by
  rw [honestAns_six S S' H .point y h]
  rfl

theorem vals6_honest (H : HPolys P F) {i : Fin 6} (h : (i : ℕ) = 5) (y : Coord P → F) :
    vals6 (honestAns S S' H (i, .point) y) =
      fun j => MvPolynomial.eval ((regs6 P).ptOf y) (H.c j) := by
  rw [honestAns_six S S' H .point y h]
  rfl

theorem ans1_honest (H : HPolys P F) (v : Fin 5) (τ : Ty) (y : Coord P → F) :
    ans1 (honestAns S S' H (v.castSucc, τ) y) =
      LIDT.CL.honest hm (d := dPcp) (fun _ => H.g v) (q1 S v τ y) := by
  rw [honestAns_lt S S' H τ y (by simp)]
  rfl

theorem ans6_honest (H : HPolys P F) {i : Fin 6} (h : (i : ℕ) = 5) (τ : Ty) (y : Coord P → F) :
    ans6 (honestAns S S' H (i, τ) y) = LIDT.CL.honest hm' (d := dPcp) H.c (q6 S' τ y) := by
  rw [honestAns_six S S' H τ y h]
  rfl

/-- The low-degree test of copy `v ≤ 5` on honest answers to two questions of one PCP vector. -/
theorem accepts_q1_honest {g : MvPolynomial (Fin P.m) F} (hg : ∀ i, g.degreeOf i ≤ dPcp)
    (v : Fin 5) (τ τ' : Ty) (w : Coord P → F) :
    CL.accepts hm (q1 S v τ ((pres P S S' (v.castSucc, τ)).eval w))
      (q1 S v τ' ((pres P S S' (v.castSucc, τ')).eval w))
      (LIDT.CL.honest hm (d := dPcp) (fun _ : Fin 1 => g) (q1 S v τ ((pres P S S' (v.castSucc, τ)).eval w)))
      (LIDT.CL.honest hm (d := dPcp) (fun _ : Fin 1 => g)
        (q1 S v τ' ((pres P S S' (v.castSucc, τ')).eval w))) = true := by
  rw [q1_eval, q1_eval]
  exact LIDT.CL.accepts_honest (fun _ => hg) ((regs P v).sampleOf S τ w) τ τ'

/-- The low-degree test of copy `6` on honest answers to two questions of one PCP vector. -/
theorem accepts_q6_honest {c : Fin (P.m' + 6) → MvPolynomial (Fin P.m') F}
    (hc : ∀ j i, (c j).degreeOf i ≤ dPcp) {i i' : Fin 6} (h : (i : ℕ) = 5) (h' : (i' : ℕ) = 5)
    (τ τ' : Ty) (w : Coord P → F) :
    CL.accepts hm' (q6 S' τ ((pres P S S' (i, τ)).eval w))
      (q6 S' τ' ((pres P S S' (i', τ')).eval w))
      (LIDT.CL.honest hm' (d := dPcp) c (q6 S' τ ((pres P S S' (i, τ)).eval w)))
      (LIDT.CL.honest hm' (d := dPcp) c (q6 S' τ' ((pres P S S' (i', τ')).eval w))) = true := by
  rw [q6_eval S S' w τ h, q6_eval S S' w τ' h']
  exact LIDT.CL.accepts_honest hc ((regs6 P).sampleOf S' τ w) τ τ'

/-! ## The five steps -/

variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)

/-- **The consistency of two players' data** that the five steps read: equal roles have equal
data, and an isolated player `v`'s `g_v` is an oracle's. -/
structure Consistent (rp rq : Role) (Hp Hq : HPolys P F) : Prop where
  same : rp = rq → Hp = Hq
  orc : ∀ v, rp = .oracle → roleIdx rq = some v → Hq.g v = Hp.g v

theorem roleIdx_injective {r r' : Role} {v : Fin 5} (h : roleIdx r = some v)
    (h' : roleIdx r' = some v) : r = r' := by
  cases r <;> cases r' <;> simp only [roleIdx, Option.some.injEq, reduceCtorEq] at h h' <;>
    first | rfl | (subst h; exact absurd h' (by decide))

/-- Step 2's comparison, or step 4's: an oracle's `Point_6` value on block `v` against a
`Point_v` value of data with the same `g_v`. -/
theorem val6_eq_val1 {chk : (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool} (Hp Hq : HPolys P F)
    (ho : Hp.Oracle chk) (v : Fin 5) (hg : Hq.g v = Hp.g v) {i : Fin 6} (h5 : (i : ℕ) = 5)
    (w : Coord P → F) :
    val6 (HPolys.idx6 v) (honestAns S S' Hp (i, .point) ((pres P S S' (i, .point)).eval w)) =
      val1 (honestAns S S' Hq (v.castSucc, .point) ((pres P S S' (v.castSucc, .point)).eval w)) := by
  rw [val6_honest S S' Hp h5, val1_honest, ho.1, block_ptOf_regs6, ptOf_regs_point6 S S' w v h5,
    ptOf_regs_point, hg]

theorem side_honest (tp tq : Role × PcpTy) (xp xq : X) (w : Coord P → F) (Hp Hq : HPolys P F)
    (hp : Hp.LowDeg) (hpo : tp.1 = .oracle → Hp.Oracle (check xp))
    (hc : Consistent tp.1 tq.1 Hp Hq) :
    side S S' check (tp, xp, (pres P S S' tp.2).eval w) (tq, xq, (pres P S S' tq.2).eval w)
      (honestAns S S' Hp tp.2 ((pres P S S' tp.2).eval w))
      (honestAns S S' Hq tq.2 ((pres P S S' tq.2).eval w)) = true := by
  obtain ⟨rp, ip, τp⟩ := tp
  obtain ⟨rq, iq, τq⟩ := tq
  simp only [side, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- step 2
    cases rp
    · cases hv : roleIdx rq with
      | none => rfl
      | some v =>
        simp only
        split_ifs with h
        · obtain ⟨h5, rfl, hi, rfl⟩ := h
          obtain rfl : iq = v.castSucc := Fin.ext hi
          rw [decide_eq_true_eq]
          exact val6_eq_val1 S S' Hp Hq (hpo rfl) v (hc.orc v rfl hv) h5 w
        · rfl
    all_goals cases roleIdx rq <;> rfl
  · -- step 3
    cases hvp : roleIdx rp with
    | none => rfl
    | some v =>
      cases hvq : roleIdx rq with
      | none => rfl
      | some v' =>
        simp only
        split_ifs with h
        · obtain ⟨rfl, hi, hi', rfl, -⟩ := h
          obtain rfl : ip = v.castSucc := Fin.ext hi
          obtain rfl : iq = v.castSucc := Fin.ext hi'
          have hr : rp = rq := roleIdx_injective hvp hvq
          rw [ans1_honest, ans1_honest, ← hc.same hr]
          exact accepts_q1_honest S S' (hp.1 _) _ _ _ w
        · rfl
  · -- step 4
    split
    · rename_i hoo
      obtain ⟨hr, hr'⟩ := hoo
      obtain rfl : Hp = Hq := hc.same (hr.trans hr'.symm)
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · split
        · rename_i h
          obtain ⟨-, hlt, rfl, h5, rfl⟩ := h
          obtain ⟨v, rfl⟩ : ∃ v : Fin 5, ip = v.castSucc := ⟨⟨ip, hlt⟩, Fin.ext rfl⟩
          rw [decide_eq_true_eq]
          exact (val6_eq_val1 S S' Hp Hp (hpo hr) v rfl h5 w).symm
        · rfl
      · split
        · rename_i h
          obtain ⟨-, hlt, hqi, rfl, -⟩ := h
          obtain ⟨v, hv⟩ : ∃ v : Fin 5, ip = v.castSucc := ⟨⟨ip, hlt⟩, Fin.ext rfl⟩
          subst hv
          subst hqi
          rw [ans1_honest, ans1_honest]
          exact accepts_q1_honest S S' (hp.1 v) v _ _ w
        · rfl
      · split
        · rename_i h
          obtain ⟨h5, h5', rfl, -⟩ := h
          rw [ans6_honest S S' Hp h5, ans6_honest S S' Hp h5']
          exact accepts_q6_honest S S' hp.2 h5 h5' _ _ w
        · rfl
    · rfl
  · -- step 5
    split_ifs with h
    · obtain ⟨hr, h5, rfl⟩ := h
      rw [vals6_honest S S' Hp h5]
      exact (hpo hr).2 _
    · rfl

/-- **The answer-reduced predicate accepts honest answers** to two questions read off one PCP
vector `w`, from data of low degree that is consistent both ways, an oracle's passing its PCP
check. -/
theorem accepts_honestAns (tp tq : Role × PcpTy) (xp xq : X) (w : Coord P → F)
    (Hp Hq : HPolys P F) (hp : Hp.LowDeg) (hq : Hq.LowDeg)
    (hpo : tp.1 = .oracle → Hp.Oracle (check xp)) (hqo : tq.1 = .oracle → Hq.Oracle (check xq))
    (hc : Consistent tp.1 tq.1 Hp Hq) (hc' : Consistent tq.1 tp.1 Hq Hp) :
    accepts S S' check (tp, xp, (pres P S S' tp.2).eval w) (tq, xq, (pres P S S' tq.2).eval w)
      (honestAns S S' Hp tp.2 ((pres P S S' tp.2).eval w))
      (honestAns S S' Hq tq.2 ((pres P S S' tq.2).eval w)) = true := by
  simp only [accepts, Bool.and_eq_true]
  refine ⟨⟨⟨⟨ansFmt_honestAns S S' _ _ _, ansFmt_honestAns S S' _ _ _⟩, ?_⟩,
    side_honest S S' check tp tq xp xq w Hp Hq hp hpo hc⟩,
    side_honest S S' check tq tp xq xp w Hq Hp hq hqo hc'⟩
  split
  · rename_i h
    change tp = tq at h
    subst h
    rw [hc.same rfl, decide_eq_true_eq]
  · rfl

end MIPRE.AnswerReduction

end
