/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Presentation
import MIPRE.Foundations.LowDegree.LineRestrict

/-!
# Honest answers in the seeded CL low-degree test

Piece AR-4 of `planning/answer-reduction.md` needs the completeness of the seeded CL test
(`def:lidt-cl`, `MIPRE.LIDT.CL.accepts`): a tuple of polynomials of individual degree at most `d`,
answered honestly — its values at a point, its restrictions to a line — passes the test on any
two questions of one sample.

* `honest` — the honest answer of a tuple `G` of `ldc` polynomials to a question: the values at
  a point, the coefficients of the restrictions (`MIPRE.LowDegree.lineRestrict`) to an axis-parallel
  or diagonal line.
* `accepts_honest` — the test accepts the honest answers to the two questions of a sample.
* `Regs.sampleOf_eval_question` — reading a sample back off the presentation's output gives the
  question the presentation computes: the base points it outputs are already canonical, so the
  decider's re-derivation of the base point (`rep`) changes nothing. This is what lets a decider
  that reads the sample off a question vector be fed the presentation's questions.
-/

noncomputable section

namespace MIPRE.LIDT.CL

open Finset MIPRE.CL MIPRE.LowDegree

variable {F : Type*} [Field F] {m : ℕ}

/-! ## The canonical base point -/

theorem canonLin_canonLin (S : Submodule F (Fin m → F)) (x : Fin m → F) :
    canonLin S (canonLin S x) = canonLin S x := by
  have h : canonLin S (x - canonLin S x) = 0 := by
    rw [← LinearMap.mem_ker, ker_canonLin]
    exact sub_canonLin_mem S x
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

theorem rep_rep (w u : Point F m) : rep w (rep w u) = rep w u := canonLin_canonLin _ u

/-- A point lies on the line through its canonical base point. -/
theorem exists_eq_rep_add (w u : Point F m) : ∃ t : F, u = rep w u + t • w := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_canonLin_mem (Submodule.span F {w}) u)
  exact ⟨t, by rw [rep, ht]; abel⟩

theorem zeroBelow_zeroBelow (i : Fin m) (v : Point F m) :
    zeroBelow i (zeroBelow i v) = zeroBelow i v := by
  funext k
  simp only [zeroBelow]
  split_ifs <;> rfl

/-- The parameter of a point of a line is its parameter, when the line is not a point. -/
theorem add_lineParam_smul [DecidableEq F] (u₀ w : Point F m) (t : F) :
    u₀ + lineParam u₀ w (u₀ + t • w) • w = u₀ + t • w := by
  unfold lineParam
  split_ifs with h
  · have hw := Fin.find_spec h
    congr 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    field_simp
  · simp only [not_exists, not_not] at h
    have : w = 0 := funext h
    simp [this]

/-! ## Line polynomials -/

/-- The coefficients of the restriction of `p` to the line `u₀ + t w`, as a `LinePoly` of
degree `n`. -/
def lineCo (n : ℕ) (u₀ w : Point F m) (p : MvPolynomial (Fin m) F) : LinePoly F n :=
  fun i => (lineRestrict u₀ w p).coeff i

theorem eval_lineCo {n : ℕ} {u₀ w : Point F m} {p : MvPolynomial (Fin m) F}
    (h : (lineRestrict u₀ w p).natDegree ≤ n) (t : F) :
    (lineCo n u₀ w p).eval t = MvPolynomial.eval (u₀ + t • w) p := by
  rw [LinePoly.eval, ← eval_lineRestrict u₀ w p t]
  change ∑ i : Fin (n + 1), (lineRestrict u₀ w p).coeff i * t ^ (i : ℕ) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (lineRestrict u₀ w p).coeff i * t ^ i) (n + 1)]
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h) t).symm

/-- Individual degree at most `d` in each of `m` variables is total degree at most `m d`. -/
theorem totalDegree_le_of_degreeOf_le {d : ℕ} {p : MvPolynomial (Fin m) F}
    (h : ∀ i, p.degreeOf i ≤ d) : p.totalDegree ≤ m * d := by
  classical
  refine Finset.sup_le fun s hs => ?_
  calc (s.sum fun _ e => e) = ∑ i ∈ s.support, s i := rfl
    _ ≤ ∑ i : Fin m, s i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ _i : Fin m, d :=
        Finset.sum_le_sum fun i _ => (MvPolynomial.monomial_le_degreeOf i hs).trans (h i)
    _ = m * d := by simp

/-! ## Honest answers -/

variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}

/-- **The honest answer** of the tuple `G` to a question: its values at a point, its
restrictions to a line. -/
def honest (G : Fin ldc → MvPolynomial (Fin m) F) : Question F m → Answer F m d ldc
  | .point u => .values fun j => MvPolynomial.eval u (G j)
  | .aline u₀ s => .apolys fun j => lineCo d u₀ (Pi.single (chi hm s) 1) (G j)
  | .dline u₀ _ v => .dpolys fun j => lineCo (m * d) u₀ v (G j)

omit [DecidableEq F] in
theorem fmtOk_honest (G : Fin ldc → MvPolynomial (Fin m) F) (q : Question F m) :
    q.fmtOk (honest hm (d := d) G q) = true := by
  cases q <;> rfl

variable {hm}

omit [NeZero m] in
/-- A line answer against a point on the line: the honest answers agree. -/
theorem lineVsPoint_honest {n : ℕ} {G : Fin ldc → MvPolynomial (Fin m) F} {u₀ w x : Point F m}
    (hx : ∃ t : F, x = u₀ + t • w) (hG : ∀ j, (lineRestrict u₀ w (G j)).natDegree ≤ n) :
    lineVsPoint u₀ w x (fun j => lineCo n u₀ w (G j)) (fun j => MvPolynomial.eval x (G j))
      = true := by
  obtain ⟨t, rfl⟩ := hx
  simp only [lineVsPoint, decide_eq_true_eq]
  refine ⟨⟨t, rfl⟩, fun j => ?_⟩
  rw [eval_lineCo (hG j), add_lineParam_smul]

/-- **The seeded CL test accepts honest answers** to the two questions of a sample, for any tuple
of polynomials of individual degree at most `d`. -/
theorem accepts_honest {G : Fin ldc → MvPolynomial (Fin m) F}
    (hG : ∀ j i, (G j).degreeOf i ≤ d) (sm : Sample F m) (τ τ' : Ty) :
    accepts hm (sm.question hm τ) (sm.question hm τ')
      (honest hm (d := d) G (sm.question hm τ)) (honest hm (d := d) G (sm.question hm τ'))
      = true := by
  have hA : ∀ j, (lineRestrict (rep (Pi.single (chi hm sm.s) 1) sm.u)
      (Pi.single (chi hm sm.s) 1) (G j)).natDegree ≤ d := fun j =>
    (natDegree_lineRestrict_single_le _ _ _).trans (hG j _)
  have hD : ∀ (u₀ v : Point F m) j, (lineRestrict u₀ v (G j)).natDegree ≤ m * d := fun u₀ v j =>
    (natDegree_lineRestrict_le _ _ _).trans (totalDegree_le_of_degreeOf_le (hG j))
  have hlA := exists_eq_rep_add (Pi.single (chi hm sm.s) 1) sm.u
  have hlD := exists_eq_rep_add (zeroBelow (chi hm sm.s) sm.v) sm.u
  simp only [accepts, fmtOk_honest, Bool.true_and]
  cases τ <;> cases τ' <;>
    simp only [Sample.question, honest, subtests, decide_true]
  · exact lineVsPoint_honest hlA hA
  · exact lineVsPoint_honest hlD (hD _ _)
  · exact lineVsPoint_honest hlA hA
  · exact lineVsPoint_honest hlD (hD _ _)

/-! ## Reading the sample back -/

/-- The decider's re-derivation of a question from the sample it reads: the base point made
canonical, the diagonal direction zeroed below the seed's block. -/
def recanon (q : Question F m) : Question F m :=
  match q with
  | .point u => .point u
  | .aline u₀ s => .aline (rep (Pi.single (chi hm s) 1) u₀) s
  | .dline u₀ s v =>
      .dline (rep (zeroBelow (chi hm s) v) u₀) s (zeroBelow (chi hm s) v)

omit [DecidableEq F] in
/-- The sample's own questions are already canonical. -/
theorem recanon_question (sm : Sample F m) (τ : Ty) :
    recanon (hm := hm) (sm.question hm τ) = sm.question hm τ := by
  cases τ <;> simp [recanon, Sample.question, rep_rep, zeroBelow_zeroBelow]

namespace Regs

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : Regs ι m) (S : Sel F m hm)

omit [DecidableEq ι] [Fintype ι] in
theorem sampleOf_question (τ : Ty) (y : ι → F) :
    (R.sampleOf S τ y).question hm τ = recanon (hm := hm) (R.questionOf S τ y) := by
  cases τ <;> rfl

/-- **Reading the sample back off the presentation's output** gives the question it computes. -/
theorem sampleOf_eval_question (τ : Ty) (x : ι → F) :
    (R.sampleOf S τ ((R.pres S τ).eval x)).question hm τ = (R.sampleOf S τ x).question hm τ := by
  rw [sampleOf_question, questionOf_eval, recanon_question]

end Regs

end MIPRE.LIDT.CL

end
