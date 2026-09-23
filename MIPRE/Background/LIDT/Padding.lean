/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Extraction
import MIPRE.Background.LIDT.CLGame
import MIPRE.Background.LIDT.Adapter.Seeds
import MIPRE.Background.LIDT.Adapter.Geometry
import MIPRE.Background.LIDT.Adapter.Reparam
import MIPRE.Foundations.GameAdapt

/-!
# The padded game adapter

Blueprint `lem:lidt-ldc-adapter`, the paper's Steps 1--2 and Claims 1--3 of the general-`ldc`
proof of `lem:ld-soundness` (`ldt.tex`). A strategy for the seeded test with `r` codewords in
`m` variables is played as a strategy for the seeded test with one codeword in `K + m` variables:
a combined point `(x, y)` is answered by `∑_{j<r} x_j b_j` from the original point answer `b` at
`y`, and a combined line by the matching polynomial built from the original line answer.

## The seed choice, and how it differs from the paper's

Each combined question is sent to an original question. The only freedom is the original seed,
and the paper draws it independently for each player, diagonal seeds from a law proportional to
`q^{j-1}`; the independence then has to be paid for on the two same-type line subtests, by a
chain of three consistency links and a `d / q` term.

Here both players share one seed *offset* `σ`, and the original seed's block is determined by the
combined seed's block `i` as `j = max(i - K, 0)`. Then **every simulated question pair is the
image of a single original sample**: `sampleMap` sends the combined sample `(u, s, v)` to the
original sample `(y-part of u, seedOf j σ, y-part of v)`, with types collapsed to `point` where
the combined line does not move the original coordinates (`qmap_question`). Acceptance transfers
subtest by subtest --- the same-type line subtests to the original equality subtest --- and the
push-forward bound is a count of the fibres of `sampleMap`.

## The decider on a sample

`accepts_sample_imp` and `accepts_sample_of` characterize the seeded test's decider on the two
questions of one sample: formats, then equality for equal types, nothing for the two cross
pairs, and otherwise equality of the two answers' *values at the sample's point* (`valAt`). Both
games are instances, and the transfer is checked on values.
-/

noncomputable section

namespace MIPRE.LIDT.Simul

open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter

/-! ## The decider on the two questions of a sample -/

section Interface

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]

/-- **The value of an answer at a point**: a point answer itself, a line answer evaluated at the
parameter of the point on the question's line. This is what the decider compares in the
line-versus-point subtests. -/
def valAt (hm : m ∣ Fintype.card F) (x : CL.Question F m) (u : Point F m) :
    CL.Answer F m d ldc → Fin ldc → F
  | .values a => a
  | .apolys f => fun j => (f j).eval (lineParam x.base (x.dir hm) u)
  | .dpolys f => fun j => (f j).eval (lineParam x.base (x.dir hm) u)

/-- The two cross type pairs, on which the decider checks nothing but the formats. -/
def IsCross : CL.Ty → CL.Ty → Prop
  | .aline, .dline => True
  | .dline, .aline => True
  | _, _ => False

instance (t t' : CL.Ty) : Decidable (IsCross t t') := by
  cases t <;> cases t' <;> simp only [IsCross] <;> infer_instance

/-- The relation the decider checks on the answers to a sample's two questions, once the
formats are right. -/
def SampleRel (hm : m ∣ Fintype.card F) (sm : CL.Sample F m) (a b : CL.Answer F m d ldc) :
    Prop :=
  if sm.tyA = sm.tyB then a = b
  else if IsCross sm.tyA sm.tyB then True
  else valAt hm (sm.question hm sm.tyA) sm.u a = valAt hm (sm.question hm sm.tyB) sm.u b

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- The sample's point lies on the line of each of its line questions. -/
theorem sample_mem_line (w u : Point F m) :
    ∃ t : F, u = rep w u + t • w := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (MIPRE.CL.sub_canonLin_mem
    (Submodule.span F {w}) u)
  exact ⟨t, by rw [rep, ht]; abel⟩

/-- **What an accepted pair of answers satisfies**, on the two questions of a sample. -/
theorem accepts_sample_imp (hm : m ∣ Fintype.card F) (sm : CL.Sample F m)
    {a b : CL.Answer F m d ldc}
    (h : CL.accepts hm (sm.question hm sm.tyA) (sm.question hm sm.tyB) a b = true) :
    (sm.question hm sm.tyA).fmtOk a = true ∧ (sm.question hm sm.tyB).fmtOk b = true ∧
      SampleRel hm sm a b := by
  obtain ⟨tA, tB, u, s, v⟩ := sm
  unfold CL.accepts at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hfa, hfb⟩, hsub⟩ := h
  refine ⟨hfa, hfb, ?_⟩
  unfold SampleRel
  cases tA <;> cases tB <;> cases a <;> cases b <;>
    simp_all [CL.Sample.question, CL.Question.fmtOk, subtests, IsCross, lineVsPoint, valAt,
      CL.Question.base, CL.Question.dir, funext_iff]

/-- **When a pair of answers is accepted**, on the two questions of a sample. -/
theorem accepts_sample_of (hm : m ∣ Fintype.card F) (sm : CL.Sample F m)
    {a b : CL.Answer F m d ldc} (hfa : (sm.question hm sm.tyA).fmtOk a = true)
    (hfb : (sm.question hm sm.tyB).fmtOk b = true) (hrel : SampleRel hm sm a b) :
    CL.accepts hm (sm.question hm sm.tyA) (sm.question hm sm.tyB) a b = true := by
  obtain ⟨tA, tB, u, s, v⟩ := sm
  have hmemA := sample_mem_line (Pi.single (chi hm s) 1) u
  have hmemD := sample_mem_line (zeroBelow (chi hm s) v) u
  unfold CL.accepts
  simp only [Bool.and_eq_true]
  refine ⟨⟨hfa, hfb⟩, ?_⟩
  unfold SampleRel at hrel
  cases tA <;> cases tB <;> cases a <;> cases b <;>
    simp_all [CL.Sample.question, CL.Question.fmtOk, subtests, IsCross, lineVsPoint, valAt,
      CL.Question.base, CL.Question.dir, funext_iff, rep]

end Interface

/-! ## Lines through a sample's point -/

section Lines

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

omit [Fintype F] in
/-- **A point, its canonical base point and its parameter**: `u = rep w u + (lineParam …) • w`,
whether or not `w` vanishes. -/
theorem eq_rep_add_lineParam (w u : Point F n) :
    u = rep w u + lineParam (rep w u) w u • w := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (MIPRE.CL.sub_canonLin_mem (Submodule.span F {w}) u)
  have hu : u = rep w u + t • w := by rw [rep, ht]; abel
  by_cases hw : ∃ j, w j ≠ 0
  · have h := lineParam_eq_of_mem hw (rep w u) t
    rw [← hu] at h
    rw [h]
    exact hu
  · have hw0 : w = 0 := funext fun j => not_not.mp fun h => hw ⟨j, h⟩
    subst hw0
    rw [smul_zero, add_zero] at hu ⊢
    exact hu

/-- The shift from a point to the canonical base point of the line through it. -/
def shiftOf (w y : Point F n) : F := by
  classical
  exact if h : ∃ j, w j ≠ 0 then
    y (Fin.find (fun j => w j ≠ 0) h) / w (Fin.find (fun j => w j ≠ 0) h) else 0

omit [Fintype F] in
theorem eq_rep_add_shiftOf {w : Point F n} (hw : ∃ j, w j ≠ 0) (y : Point F n) :
    y = rep w y + shiftOf w y • w := by
  classical
  rw [rep, rep_eq hw, shiftOf, dif_pos hw]
  abel

omit [Fintype F] in
/-- **The parameter of a point on a rebased line.** If `y = y₀ + t w` then the parameter of `y` on
the line through `y₀` with base point `rep w y₀` is `t` plus the shift of `y₀`. -/
theorem lineParam_rep_add {w : Point F n} (hw : ∃ j, w j ≠ 0) (y₀ : Point F n) (t : F) :
    lineParam (rep w y₀) w (y₀ + t • w) = t + shiftOf w y₀ := by
  have e : y₀ + t • w = rep w y₀ + (t + shiftOf w y₀) • w := by
    have h0 := eq_rep_add_shiftOf hw y₀
    calc y₀ + t • w = (rep w y₀ + shiftOf w y₀ • w) + t • w := by rw [← h0]
      _ = _ := by rw [add_smul]; abel
  rw [e, lineParam_eq_of_mem hw]

omit [Fintype F] [DecidableEq F] in
/-- The base point of a line does not see the point it was built from. -/
theorem rep_add_smul' (w y : Point F n) (t : F) : rep w (y + t • w) = rep w y :=
  rep_add_smul w y t

end Lines

/-! ## The combining and original blocks -/

section Blocks

variable {F : Type*} [Field F] {K m : ℕ}

@[simp] theorem yOf_add (u v : Point F (K + m)) : yOf (u + v) = yOf u + yOf v := rfl
@[simp] theorem yOf_smul (c : F) (u : Point F (K + m)) : yOf (c • u) = c • yOf u := rfl
@[simp] theorem xOf_add (u v : Point F (K + m)) : xOf (u + v) = xOf u + xOf v := rfl
@[simp] theorem xOf_smul (c : F) (u : Point F (K + m)) : xOf (c • u) = c • xOf u := rfl
@[simp] theorem yOf_zero : yOf (0 : Point F (K + m)) = 0 := rfl

/-- The original block index of a combined index: `i - K`, or `0` for a combining index. -/
def jIdx [NeZero m] (i : Fin (K + m)) : Fin m :=
  if h : K ≤ (i : ℕ) then ⟨(i : ℕ) - K, by omega⟩ else ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

theorem jIdx_of_le [NeZero m] {i : Fin (K + m)} (h : K ≤ (i : ℕ)) :
    ((jIdx i : Fin m) : ℕ) = (i : ℕ) - K := by
  rw [jIdx, dif_pos h]

theorem yOf_single_of_le [NeZero m] {i : Fin (K + m)} (h : K ≤ (i : ℕ)) :
    yOf (Pi.single i (1 : F) : Point F (K + m)) = Pi.single (jIdx i) 1 := by
  classical
  funext k
  simp only [yOf, Pi.single_apply]
  have : (Fin.natAdd K k = i) ↔ (k = jIdx i) := by
    constructor
    · intro hk; apply Fin.ext; rw [jIdx_of_le h, ← hk]; simp
    · intro hk; apply Fin.ext; rw [hk]; simp [jIdx_of_le h]; omega
  simp only [this]

theorem yOf_single_of_lt {i : Fin (K + m)} (h : (i : ℕ) < K) :
    yOf (Pi.single i (1 : F) : Point F (K + m)) = 0 := by
  classical
  funext k
  simp only [yOf, Pi.single_apply, Pi.zero_apply]
  rw [if_neg]
  intro hk
  have := congrArg Fin.val hk
  simp at this
  omega

theorem xOf_single_of_le {i : Fin (K + m)} (h : K ≤ (i : ℕ)) :
    xOf (Pi.single i (1 : F) : Point F (K + m)) = 0 := by
  classical
  funext k
  simp only [xOf, Pi.single_apply, Pi.zero_apply]
  rw [if_neg]
  intro hk
  have := congrArg Fin.val hk
  simp at this
  omega

theorem yOf_zeroBelow [NeZero m] (i : Fin (K + m)) (v : Point F (K + m)) :
    yOf (zeroBelow i v) = zeroBelow (jIdx i) (yOf v) := by
  funext k
  simp only [yOf, zeroBelow]
  by_cases h : K ≤ (i : ℕ)
  · rw [jIdx_of_le h]
    simp only [Fin.val_natAdd]
    split_ifs <;> first | rfl | omega
  · have hj : ((jIdx i : Fin m) : ℕ) = 0 := by rw [jIdx, dif_neg h]
    rw [hj]
    simp only [Fin.val_natAdd]
    split_ifs <;> first | rfl | omega

theorem yOf_rep_single_of_le [NeZero m] [DecidableEq F] {i : Fin (K + m)} (h : K ≤ (i : ℕ))
    (u : Point F (K + m)) :
    yOf (rep (Pi.single i 1) u) = yOf u + (-u i) • Pi.single (jIdx i) 1 := by
  rw [rep, rep_single, ← yOf_single_of_le h, sub_eq_add_neg, ← neg_smul]
  rfl

theorem yOf_rep_single_of_lt [DecidableEq F] {i : Fin (K + m)} (h : (i : ℕ) < K)
    (u : Point F (K + m)) : yOf (rep (Pi.single i 1) u) = yOf u := by
  rw [rep, rep_single, sub_eq_add_neg, ← neg_smul]
  show yOf u + (-u i) • yOf (Pi.single i (1 : F) : Point F (K + m)) = yOf u
  rw [yOf_single_of_lt h, smul_zero, add_zero]

theorem exists_yOf_rep [Fintype F] [DecidableEq F] (w u : Point F (K + m)) :
    ∃ t : F, yOf (rep w u) = yOf u + t • yOf w := by
  refine ⟨-lineParam (rep w u) w u, ?_⟩
  have e := congrArg yOf (eq_rep_add_lineParam w u)
  rw [yOf_add, yOf_smul] at e
  rw [neg_smul, e]
  abel

end Blocks

/-! ## The question map and the sample map -/

section Maps

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m : ℕ} [NeZero m] [NeZero (K + m)]
  (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)

/-- The original seed block of a combined seed. -/
def jOf (s : F) : Fin m := jIdx (chi hM s)

/-- **The type map**: an axis-parallel line along a combining coordinate, and a diagonal line
whose original part is constant, become point questions. -/
def tyMap (i : Fin (K + m)) (wy : Point F m) : CL.Ty → CL.Ty
  | .point => .point
  | .aline => if K ≤ (i : ℕ) then .aline else .point
  | .dline => if wy = 0 then .point else .dline

/-- **The question map**, with the shared seed offset `σ`. -/
def qmap (σ : Fin (Fintype.card F / m)) : CL.Question F (K + m) → CL.Question F m
  | .point u => .point (yOf u)
  | .aline u₀ s =>
      if K ≤ (chi hM s : ℕ) then
        .aline (rep (Pi.single (jOf hM s) 1) (yOf u₀)) (seedOf hm (jOf hM s) σ)
      else .point (yOf u₀)
  | .dline u₀ s w =>
      if yOf w = 0 then .point (yOf u₀)
      else .dline (rep (yOf w) (yOf u₀)) (seedOf hm (jOf hM s) σ) (yOf w)

/-- The original part of a combined sample's diagonal direction. -/
def wyOf (sm : CL.Sample F (K + m)) : Point F m := yOf (zeroBelow (chi hM sm.s) sm.v)

/-- **The sample map**: one original sample for the whole combined sample. -/
def sampleMap (σ : Fin (Fintype.card F / m)) (sm : CL.Sample F (K + m)) : CL.Sample F m :=
  ⟨tyMap (chi hM sm.s) (wyOf hM sm) sm.tyA, tyMap (chi hM sm.s) (wyOf hM sm) sm.tyB,
    yOf sm.u, seedOf hm (jOf hM sm.s) σ, yOf sm.v⟩

/-- **Every simulated question is the mapped sample's question.** -/
theorem qmap_question (σ : Fin (Fintype.card F / m)) (sm : CL.Sample F (K + m)) (t : CL.Ty) :
    qmap hm hM σ (sm.question hM t)
      = (sampleMap hm hM σ sm).question hm (tyMap (chi hM sm.s) (wyOf hM sm) t) := by
  obtain ⟨tA, tB, u, s, v⟩ := sm
  have hchi : chi hm (seedOf hm (jOf hM s) σ) = jOf hM s := chi_seedOf hm _ σ
  cases t with
  | point => rfl
  | aline =>
    by_cases h : K ≤ (chi hM s : ℕ)
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, h, if_true, hchi]
      rw [yOf_rep_single_of_le h, show jIdx (chi hM s) = jOf hM s from rfl, rep_add_smul']
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, h, if_false]
      rw [yOf_rep_single_of_lt (not_le.mp h)]
  | dline =>
    obtain ⟨t, ht⟩ := exists_yOf_rep (zeroBelow (chi hM s) v) u
    have hz : zeroBelow (jOf hM s) (yOf v) = yOf (zeroBelow (chi hM s) v) :=
      (yOf_zeroBelow _ _).symm
    by_cases h : yOf (zeroBelow (chi hM s) v) = 0
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, wyOf, h, if_true]
      rw [ht, h, smul_zero, add_zero]
    · simp only [CL.Sample.question, qmap, tyMap, sampleMap, wyOf, h, if_false, hchi]
      rw [hz, ht, rep_add_smul']

end Maps

/-! ## The answer map -/

section Answers

open Polynomial

variable {F : Type*} [Field F] {K r : ℕ}

/-- The first `r` combining coordinates. -/
def xr (hr : r ≤ K) (x : Point F K) : Fin r → F := fun k => x (Fin.castLE hr k)

@[simp] theorem xr_add (hr : r ≤ K) (x x' : Point F K) : xr hr (x + x') = xr hr x + xr hr x' :=
  rfl

@[simp] theorem xr_smul (hr : r ≤ K) (c : F) (x : Point F K) : xr hr (c • x) = c • xr hr x := rfl

@[simp] theorem xr_zero (hr : r ≤ K) : xr hr (0 : Point F K) = 0 := rfl

/-- **The combined point answer** `∑_{k<r} x_k b_k`. -/
def linEval (hr : r ≤ K) (b : Fin r → F) (x : Point F K) : F := ∑ k, xr hr x k * b k

theorem eval_linPoly_padB {d : ℕ} (hd : 1 ≤ d) (hr : r ≤ K) (b : Fin r → F) (x : Point F K) :
    (linPoly (d := d) hd (padB b)).eval x = linEval hr b x := by
  classical
  rw [eval_linPoly, linEval]
  have hinj : Function.Injective (Fin.castLE hr) := Fin.castLE_injective hr
  calc ∑ i, padB (K := K) b i * x i
      = ∑ i ∈ Finset.univ.image (Fin.castLE hr), padB (K := K) b i * x i := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
        have : ¬ (i : ℕ) < r := fun h =>
          hi (Finset.mem_image.mpr ⟨⟨i, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [padB, this]
    _ = ∑ k, padB (K := K) b (Fin.castLE hr k) * x (Fin.castLE hr k) :=
        Finset.sum_image fun a _ b _ h => hinj h
    _ = _ := Finset.sum_congr rfl fun k _ => by rw [padB_castLE, mul_comm]; rfl

/-- The affine-in-`t` combination `∑_k (α_k + β_k t) P_k(t + c)`. -/
def affPoly (α β : Fin r → F) (c : F) (P : Fin r → F[X]) : F[X] :=
  ∑ k, (C (α k) + C (β k) * X) * (P k).comp (X + C c)

theorem eval_affPoly (α β : Fin r → F) (c : F) (P : Fin r → F[X]) (t : F) :
    (affPoly α β c P).eval t = ∑ k, (α k + β k * t) * (P k).eval (t + c) := by
  simp [affPoly, eval_finsetSum, eval_comp]

theorem natDegree_affPoly_le {α β : Fin r → F} {c : F} {P : Fin r → F[X]} {D : ℕ}
    (h : ∀ k, (P k).natDegree ≤ D) : (affPoly α β c P).natDegree ≤ D + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_mul_le).trans ?_
  have h1 : (C (α k) + C (β k) * X).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  have h2 : ((P k).comp (X + C c)).natDegree ≤ D := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
    exact h k
  omega

theorem natDegree_affPoly_le_of_zero {α : Fin r → F} {c : F} {P : Fin r → F[X]} {D : ℕ}
    (h : ∀ k, (P k).natDegree ≤ D) : (affPoly α 0 c P).natDegree ≤ D := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  simp only [Pi.zero_apply, map_zero, zero_mul, add_zero]
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_comp, natDegree_X_add_C, mul_one]
  exact h k

variable {m d : ℕ} [NeZero m]

/-- The coordinates of a point answer; `0` for the wrong format. -/
def valsOf : CL.Answer F m d r → Fin r → F
  | .values b => b
  | _ => 0

/-- The `r` polynomials an answer carries: constants for a point answer. -/
def polysOf : CL.Answer F m d r → Fin r → F[X]
  | .values b => fun k => C (b k)
  | .apolys g => fun k => toPoly (g k)
  | .dpolys g => fun k => toPoly (g k)

variable [Fintype F] [DecidableEq F] [NeZero (K + m)]

/-- The combined line answer on the line through `u₀` in direction `w`: at the parameter `t`,
the combined point answer at `u₀ + t w`. -/
def lineAns (hr : r ≤ K) (u₀ w : Point F (K + m)) (a : CL.Answer F m d r) : F[X] :=
  affPoly (xr hr (xOf u₀)) (xr hr (xOf w)) (shiftOf (yOf w) (yOf u₀)) (polysOf a)

variable (hM : (K + m) ∣ Fintype.card F)

/-- **The answer map.** -/
def rmap (hr : r ≤ K) : CL.Question F (K + m) → CL.Answer F m d r → CL.Answer F (K + m) d 1
  | .point u, a => .values fun _ => linEval hr (valsOf a) (xOf u)
  | .aline u₀ s, a => .apolys fun _ => ofPoly (lineAns hr u₀ (Pi.single (chi hM s) 1) a)
  | .dline u₀ _ w, a => .dpolys fun _ => ofPoly (lineAns hr u₀ w a)

omit [NeZero m] in
theorem fmtOk_rmap (hr : r ≤ K) (x : CL.Question F (K + m)) (a : CL.Answer F m d r) :
    x.fmtOk (rmap hM hr x a) = true := by
  cases x <;> rfl

end Answers

/-! ## Values transfer -/

section Transfer

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

omit [Fintype F] in
/-- A point on a line is the base point moved by its parameter. -/
theorem base_add_lineParam {n : ℕ} {u₀ w u : Point F n} (h : ∃ t : F, u = u₀ + t • w) :
    u₀ + lineParam u₀ w u • w = u := by
  obtain ⟨t, rfl⟩ := h
  by_cases hw : ∃ j, w j ≠ 0
  · rw [lineParam_eq_of_mem hw]
  · have hw0 : w = 0 := funext fun j => not_not.mp fun h => hw ⟨j, h⟩
    simp [hw0]

omit [Fintype F] [NeZero m] [NeZero (K + m)] in
theorem eval_lineAns_eq {u₀ w : Point F (K + m)} {a : CL.Answer F m d r} {t : F}
    {V : Fin r → F} (h : ∀ k, (polysOf a k).eval (t + shiftOf (yOf w) (yOf u₀)) = V k) :
    (lineAns hr u₀ w a).eval t = linEval hr V (xOf (u₀ + t • w)) := by
  rw [lineAns, eval_affPoly, linEval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h k]
  simp only [xOf_add, xOf_smul, xr_add, xr_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype F] [NeZero m] [NeZero (K + m)] in
theorem valAt_line_aux {D : ℕ} {P : F[X]} (hP : P.natDegree ≤ D) {u₀ w u : Point F (K + m)}
    (hu : ∃ t : F, u = u₀ + t • w) (V : Point F m → Fin r → F)
    (hPV : ∀ t, P.eval t = linEval hr (V (yOf (u₀ + t • w))) (xOf (u₀ + t • w))) :
    (ofPoly P : LinePoly F D).eval (lineParam u₀ w u) = linEval hr (V (yOf u)) (xOf u) := by
  rw [eval_ofPoly hP, hPV, base_add_lineParam hu]

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem natDegree_polysOf_values (b : Fin r → F) (k : Fin r) :
    (polysOf (m := m) (d := d) (.values b) k).natDegree ≤ 0 := by
  simp [polysOf]

/-- **The value transfer.** On a point `u` of a combined question's line, the combined answer's
value is the combined point answer `∑_{k<r} x_k b_k`, with `b` the original answer's value at the
original part of `u`. -/
theorem valAt_rmap (hd : 1 ≤ d) (hK : 1 ≤ K) (σ : Fin (Fintype.card F / m))
    (x : CL.Question F (K + m)) {u : Point F (K + m)}
    (hu : ∃ t : F, u = x.base + t • x.dir hM) {a : CL.Answer F m d r}
    (hf : (qmap hm hM σ x).fmtOk a = true) (k : Fin 1) :
    valAt hM x u (rmap hM hr x a) k
      = linEval hr (valAt hm (qmap hm hM σ x) (yOf u) a) (xOf u) := by
  cases x with
  | point u₀ =>
    obtain ⟨t, rfl⟩ := hu
    cases a with
    | values b => simp [valAt, rmap, CL.Question.base, CL.Question.dir, valsOf]
    | apolys g => simp [qmap, CL.Question.fmtOk] at hf
    | dpolys g => simp [qmap, CL.Question.fmtOk] at hf
  | aline u₀ s =>
    simp only [CL.Question.base, CL.Question.dir] at hu
    rw [show valAt hM (.aline u₀ s) u (rmap hM hr (.aline u₀ s) a) k
      = (ofPoly (lineAns hr u₀ (Pi.single (chi hM s) 1) a) : LinePoly F d).eval
          (lineParam u₀ (Pi.single (chi hM s) 1) u) from rfl]
    have hchi : chi hm (seedOf hm (jOf hM s) σ) = jOf hM s := chi_seedOf hm _ σ
    by_cases h : K ≤ (chi hM s : ℕ)
    · have hq : qmap hm hM σ (.aline u₀ s)
          = .aline (rep (Pi.single (jOf hM s) 1) (yOf u₀)) (seedOf hm (jOf hM s) σ) := by
        simp [qmap, h]
      rw [hq] at hf ⊢
      cases a with
      | apolys g =>
        have hx0 : xr hr (xOf (Pi.single (chi hM s) (1 : F) : Point F (K + m))) = 0 := by
          rw [xOf_single_of_le h]; rfl
        refine valAt_line_aux hr (D := d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · rw [lineAns, hx0]
          exact natDegree_affPoly_le_of_zero fun k' => natDegree_toPoly_le _
        · simp only [polysOf, eval_toPoly, valAt, CL.Question.base, CL.Question.dir, hchi]
          rw [yOf_add, yOf_smul, yOf_single_of_le h,
            show jIdx (chi hM s) = jOf hM s from rfl,
            lineParam_rep_add ⟨jOf hM s, by simp⟩]
      | values b => simp [CL.Question.fmtOk] at hf
      | dpolys g => simp [CL.Question.fmtOk] at hf
    · have hq : qmap hm hM σ (.aline u₀ s) = .point (yOf u₀) := by simp [qmap, h]
      rw [hq] at hf ⊢
      cases a with
      | values b =>
        refine valAt_line_aux hr (D := d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · exact (natDegree_affPoly_le (natDegree_polysOf_values b)).trans hd
        · simp [polysOf, valAt]
      | apolys g => simp [CL.Question.fmtOk] at hf
      | dpolys g => simp [CL.Question.fmtOk] at hf
  | dline u₀ s w =>
    simp only [CL.Question.base, CL.Question.dir] at hu
    rw [show valAt hM (.dline u₀ s w) u (rmap hM hr (.dline u₀ s w) a) k
      = (ofPoly (lineAns hr u₀ w a) : LinePoly F ((K + m) * d)).eval (lineParam u₀ w u) from rfl]
    have hchi : chi hm (seedOf hm (jOf hM s) σ) = jOf hM s := chi_seedOf hm _ σ
    by_cases h : yOf w = 0
    · have hq : qmap hm hM σ (.dline u₀ s w) = .point (yOf u₀) := by simp [qmap, h]
      rw [hq] at hf ⊢
      cases a with
      | values b =>
        refine valAt_line_aux hr (D := (K + m) * d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · refine (natDegree_affPoly_le (natDegree_polysOf_values b)).trans ?_
          have : 1 ≤ K + m := Nat.pos_of_ne_zero (NeZero.ne _)
          nlinarith
        · simp [polysOf, valAt]
      | apolys g => simp [CL.Question.fmtOk] at hf
      | dpolys g => simp [CL.Question.fmtOk] at hf
    · have hq : qmap hm hM σ (.dline u₀ s w)
          = .dline (rep (yOf w) (yOf u₀)) (seedOf hm (jOf hM s) σ) (yOf w) := by
        simp [qmap, h]
      have hw : ∃ j, yOf w j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      rw [hq] at hf ⊢
      cases a with
      | dpolys g =>
        refine valAt_line_aux hr (D := (K + m) * d) ?_ hu (fun y => valAt hm _ y _)
          fun t => eval_lineAns_eq hr fun k' => ?_
        · refine (natDegree_affPoly_le fun k' => natDegree_toPoly_le _).trans ?_
          nlinarith
        · simp only [polysOf, eval_toPoly, valAt, CL.Question.base, CL.Question.dir]
          rw [yOf_add, yOf_smul, lineParam_rep_add hw]
      | values b => simp [CL.Question.fmtOk] at hf
      | apolys g => simp [CL.Question.fmtOk] at hf

end Transfer

/-! ## Acceptance transfer -/

section Accept

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

omit [DecidableEq F] in
/-- The sample's point lies on each of its questions' lines. -/
theorem sample_question_mem {n : ℕ} [NeZero n] (hn : n ∣ Fintype.card F) (sm : CL.Sample F n)
    (t : CL.Ty) : ∃ τ : F, sm.u = (sm.question hn t).base + τ • (sm.question hn t).dir hn := by
  cases t with
  | point => exact ⟨0, by simp [CL.Sample.question, CL.Question.base, CL.Question.dir]⟩
  | aline => exact sample_mem_line _ _
  | dline => exact sample_mem_line _ _

theorem valAt_eq_of_sampleRel {n : ℕ} [NeZero n] (hn : n ∣ Fintype.card F) {sm : CL.Sample F n}
    {a b : CL.Answer F n d r} (h : SampleRel hn sm a b) (hc : ¬ IsCross sm.tyA sm.tyB) :
    valAt hn (sm.question hn sm.tyA) sm.u a = valAt hn (sm.question hn sm.tyB) sm.u b := by
  unfold SampleRel at h
  split_ifs at h with h1
  · rw [h1, h]
  · exact h

theorem eq_point_of_not_cross {t t' : CL.Ty} (h1 : t ≠ t') (h2 : ¬ IsCross t t') :
    t = .point ∨ t' = .point := by
  cases t <;> cases t' <;> simp_all [IsCross]

theorem not_isCross_point_left (t : CL.Ty) : ¬ IsCross .point t := by
  cases t <;> simp [IsCross]

theorem not_isCross_point_right (t : CL.Ty) : ¬ IsCross t .point := by
  cases t <;> simp [IsCross]

/-- **Acceptance transfers** from the mapped original sample to the combined sample. -/
theorem accepts_rmap (hd : 1 ≤ d) (hK : 1 ≤ K) (σ : Fin (Fintype.card F / m))
    (sm : CL.Sample F (K + m)) {a b : CL.Answer F m d r}
    (h : CL.accepts hm (qmap hm hM σ (sm.question hM sm.tyA))
      (qmap hm hM σ (sm.question hM sm.tyB)) a b = true) :
    CL.accepts hM (sm.question hM sm.tyA) (sm.question hM sm.tyB)
      (rmap hM hr (sm.question hM sm.tyA) a) (rmap hM hr (sm.question hM sm.tyB) b) = true := by
  rw [qmap_question, qmap_question] at h
  obtain ⟨hfa, hfb, hrel⟩ := accepts_sample_imp hm (sampleMap hm hM σ sm) h
  refine accepts_sample_of hM sm (fmtOk_rmap hM hr _ _) (fmtOk_rmap hM hr _ _) ?_
  unfold SampleRel
  split_ifs with h1 h2
  · have h1' : (sampleMap hm hM σ sm).tyA = (sampleMap hm hM σ sm).tyB := by
      simp only [sampleMap, h1]
    unfold SampleRel at hrel
    rw [if_pos h1'] at hrel
    rw [h1, hrel]
  · have hc : ¬ IsCross (sampleMap hm hM σ sm).tyA (sampleMap hm hM σ sm).tyB := by
      rcases eq_point_of_not_cross h1 h2 with h3 | h3
      · simp only [sampleMap, h3, tyMap]; exact not_isCross_point_left _
      · simp only [sampleMap, h3, tyMap]; exact not_isCross_point_right _
    have hv := valAt_eq_of_sampleRel hm hrel hc
    have hA := qmap_question hm hM σ sm sm.tyA
    have hB := qmap_question hm hM σ sm sm.tyB
    funext k
    rw [valAt_rmap hm hM hr hd hK σ _ (sample_question_mem hM sm _) (by rw [hA]; exact hfa),
      valAt_rmap hm hM hr hd hK σ _ (sample_question_mem hM sm _) (by rw [hB]; exact hfb),
      hA, hB]
    exact congrArg (fun V => linEval hr V (xOf sm.u)) hv

/-- The acceptance hypothesis of `exists_one_sub_value_adapt_le`, for the padded adapter. -/
theorem clGame_D_rmap (hd : 1 ≤ d) (hK : 1 ≤ K) (σ : Fin (Fintype.card F / m))
    (x y : CL.Question F (K + m)) (a b : CL.Answer F m d r)
    (hμ : (clGame (d := d) (ldc := 1) hM).μ x y ≠ 0)
    (h : (clGame (d := d) (ldc := r) hm).D (qmap hm hM σ x) (qmap hm hM σ y) a b = true) :
    (clGame (d := d) (ldc := 1) hM).D x y (rmap hM hr x a) (rmap hM hr y b) = true := by
  obtain ⟨sm, _, hsm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ
  have hq : (sm.question hM sm.tyA, sm.question hM sm.tyB) = (x, y) := by
    by_contra hc
    exact hsm (by rw [if_neg hc, mul_zero])
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
  exact accepts_rmap hm hM hr hd hK σ sm h

end Accept

/-! ## The fibre count -/

section Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)

/-- The samples as a product. -/
def sampleEquiv (n : ℕ) : CL.Sample F n ≃ CL.Ty × CL.Ty × Point F n × F × Point F n where
  toFun sm := (sm.tyA, sm.tyB, sm.u, sm.s, sm.v)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_ty : Fintype.card CL.Ty = 3 := rfl

omit [Field F] [DecidableEq F] in
theorem card_sample (n : ℕ) :
    Fintype.card (CL.Sample F n)
      = 9 * (Fintype.card F ^ n * (Fintype.card F * Fintype.card F ^ n)) := by
  rw [Fintype.card_congr (sampleEquiv n)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, card_ty]
  ring

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] [NeZero (K + m)] in
theorem eq_of_xOf_yOf {u u' : Point F (K + m)} (hx : xOf u = xOf u') (hy : yOf u = yOf u') :
    u = u' := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · exact congrFun hx a
  · exact congrFun hy b

/-- A seed block of the original test collects at most `K + 1` blocks of the combined test. -/
theorem card_jOf_fiber_le (j : Fin m) :
    #{s : F | jOf hM s = j} ≤ (K + 1) * (Fintype.card F / (K + m)) := by
  classical
  set I := (Finset.univ : Finset (Fin (K + m))).filter (fun i => jIdx i = j)
  have hsub : ((Finset.univ : Finset F).filter fun s => jOf hM s = j)
      ⊆ I.biUnion fun i => (Finset.univ : Finset F).filter fun s => chi hM s = i := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact Finset.mem_biUnion.mpr ⟨chi hM s, by simpa [I, jOf] using hs, by simp⟩
  have hI : I.card ≤ K + 1 := by
    have := Finset.card_le_card_of_injOn (s := I) (t := (Finset.univ : Finset (Fin (K + 1))))
      (fun i => ⟨min (i : ℕ) K, by omega⟩) (fun _ _ => Finset.mem_univ _) ?_
    · simpa using this
    intro i hi i' hi' h
    simp only [I, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hi'
    have h' := congrArg Fin.val h
    simp only at h'
    apply Fin.ext
    by_cases h1 : K ≤ (i : ℕ) <;> by_cases h2 : K ≤ (i' : ℕ)
    · have e1 := jIdx_of_le h1
      have e2 := jIdx_of_le h2
      rw [hi] at e1
      rw [hi'] at e2
      omega
    all_goals omega
  calc #{s : F | jOf hM s = j}
      ≤ (I.biUnion fun i => (Finset.univ : Finset F).filter fun s => chi hM s = i).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, ((Finset.univ : Finset F).filter fun s => chi hM s = i).card :=
        Finset.card_biUnion_le
    _ = ∑ _i ∈ I, Fintype.card F / (K + m) :=
        Finset.sum_congr rfl fun i _ => card_chi_fiber hM i
    _ = I.card * (Fintype.card F / (K + m)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (K + 1) * (Fintype.card F / (K + m)) := Nat.mul_le_mul_right _ hI

/-- **The fibres of the sample map**, over the seed offset and the combined sample, have at most
`9 (K + 1) (q / (K + m)) q^{2K}` elements: the types have three preimages each, the combining
coordinates of the point and the direction are free, the combined seed ranges over `K + 1`
blocks, and the offset is then determined. -/
theorem card_sampleMap_fiber_le (sm : CL.Sample F m) :
    #{p : Fin (Fintype.card F / m) × CL.Sample F (K + m) | sampleMap hm hM p.1 p.2 = sm}
      ≤ 9 * ((K + 1) * (Fintype.card F / (K + m))) * Fintype.card F ^ K
          * Fintype.card F ^ K := by
  classical
  set S := (Finset.univ : Finset F).filter fun s => jOf hM s = chi hm sm.s
  let g : Fin (Fintype.card F / m) × CL.Sample F (K + m) →
      CL.Ty × CL.Ty × Point F K × F × Point F K :=
    fun p => (p.2.tyA, p.2.tyB, xOf p.2.u, p.2.s, xOf p.2.v)
  have hmaps : ∀ p ∈ (Finset.univ.filter fun p : Fin (Fintype.card F / m) × CL.Sample F (K + m) =>
      sampleMap hm hM p.1 p.2 = sm),
      g p ∈ (Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ ×ˢ S ×ˢ Finset.univ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hs : chi hm sm.s = jOf hM p.2.s := by rw [← hp]; exact chi_seedOf hm _ _
    simp [g, S, hs]
  have hinj : Set.InjOn g (Finset.univ.filter fun p : Fin (Fintype.card F / m) ×
      CL.Sample F (K + m) => sampleMap hm hM p.1 p.2 = sm) := by
    rintro ⟨σ, ⟨tA, tB, u, s, v⟩⟩ hp ⟨σ', ⟨tA', tB', u', s', v'⟩⟩ hp' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, hx, rfl, hxv⟩ := h
    rw [← hp'] at hp
    simp only [sampleMap, CL.Sample.mk.injEq] at hp
    obtain ⟨-, -, hy, hseed, hyv⟩ := hp
    rw [seedOf_injective hm _ hseed, eq_of_xOf_yOf hx hy, eq_of_xOf_yOf hxv hyv]
  have hS : S.card ≤ (K + 1) * (Fintype.card F / (K + m)) := card_jOf_fiber_le hM _
  calc _ ≤ (Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ ×ˢ S ×ˢ
        (Finset.univ : Finset (Point F K))).card := Finset.card_le_card_of_injOn g hmaps hinj
    _ = 3 * 3 * Fintype.card F ^ K * S.card * Fintype.card F ^ K := by
        simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          card_ty]
        ring
    _ ≤ 3 * 3 * Fintype.card F ^ K * ((K + 1) * (Fintype.card F / (K + m)))
          * Fintype.card F ^ K := by gcongr
    _ = _ := by ring

/-- The mass the seeded test puts on the fibre of a pair of question maps. -/
theorem clGame_mu_fibre {n l : ℕ} [NeZero n] (hn : n ∣ Fintype.card F) {X : Type*}
    [DecidableEq X] (qA qB : CL.Question F n → X) (x y : X) :
    ∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), (clGame (d := d) (ldc := l) hn).μ x' y'
      = ∑ sm : CL.Sample F n, (Fintype.card (CL.Sample F n) : ℝ)⁻¹ *
          if qA (sm.question hn sm.tyA) = x ∧ qB (sm.question hn sm.tyB) = y then 1 else 0 := by
  simp only [clGame]
  rw [Finset.sum_congr rfl fun x' _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun sm _ => ?_
  simp only [← Finset.mul_sum]
  congr 1
  simp only [Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel]

/-- **The push-forward bound** of the padded adapter, averaged over the seed offset, with
`C = 9 (K + 1)`. -/
theorem sum_mu_qmap_le (x y : CL.Question F m) :
    (∑ σ : Fin (Fintype.card F / m),
        ∑ x' ∈ Finset.univ.filter (fun x' => qmap hm hM σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmap hm hM σ y' = y),
          (clGame (d := d) (ldc := 1) hM).μ x' y')
      ≤ (Fintype.card (Fin (Fintype.card F / m)) : ℝ)
          * ((9 * (K + 1) : ℝ) * (clGame (d := d) (ldc := r) hm).μ x y) := by
  classical
  set q := Fintype.card F
  set P : CL.Sample F m → Prop := fun sm =>
    sm.question hm sm.tyA = x ∧ sm.question hm sm.tyB = y
  set f : CL.Sample F m → ℝ := fun sm => if P sm then 1 else 0
  have hf0 : ∀ sm, 0 ≤ f sm := fun sm => by simp only [f]; split_ifs <;> norm_num
  set Φ : ℕ := 9 * ((K + 1) * (q / (K + m))) * q ^ K * q ^ K
  have hcond : ∀ σ (sm : CL.Sample F (K + m)),
      (if qmap hm hM σ (sm.question hM sm.tyA) = x ∧ qmap hm hM σ (sm.question hM sm.tyB) = y
        then (1 : ℝ) else 0) = f (sampleMap hm hM σ sm) := by
    intro σ sm
    simp only [f, P]
    rw [qmap_question, qmap_question]
    rfl
  have hL : (∑ σ : Fin (q / m),
        ∑ x' ∈ Finset.univ.filter (fun x' => qmap hm hM σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmap hm hM σ y' = y),
          (clGame (d := d) (ldc := 1) hM).μ x' y')
      = (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ *
          ∑ p : Fin (q / m) × CL.Sample F (K + m), f (sampleMap hm hM p.1 p.2) := by
    simp_rw [clGame_mu_fibre, hcond, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type]
  have hcount : ∑ p : Fin (q / m) × CL.Sample F (K + m), f (sampleMap hm hM p.1 p.2)
      ≤ ∑ sm : CL.Sample F m, (Φ : ℝ) * f sm := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin (q / m) × CL.Sample F (K + m)))
      (fun p => sampleMap hm hM p.1 p.2)]
    refine Finset.sum_le_sum fun sm _ => ?_
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2],
      Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_sampleMap_fiber_le hm hM sm)
      (hf0 sm)
  have hR : (clGame (d := d) (ldc := r) hm).μ x y
      = (Fintype.card (CL.Sample F m) : ℝ)⁻¹ * ∑ sm : CL.Sample F m, f sm := by
    simp only [clGame, f, P, Prod.mk.injEq, Finset.mul_sum]
  have hq : 0 < q := Fintype.card_pos
  have hdiv : q / (K + m) ≤ q / m := Nat.div_le_div_left (by omega)
    (Nat.pos_of_ne_zero (NeZero.ne m))
  have hnat : Φ * Fintype.card (CL.Sample F m)
      ≤ q / m * (9 * (K + 1)) * Fintype.card (CL.Sample F (K + m)) := by
    rw [card_sample, card_sample]
    simp only [Φ, pow_add]
    have := Nat.mul_le_mul_right (9 * (K + 1) * q ^ K * q ^ K * (9 * (q ^ m * (q * q ^ m)))) hdiv
    nlinarith [this]
  have hN : (0 : ℝ) < Fintype.card (CL.Sample F m) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(⟨.point, .point, 0, 0, 0⟩ : CL.Sample F m)⟩
  have hN' : (0 : ℝ) < Fintype.card (CL.Sample F (K + m)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(⟨.point, .point, 0, 0, 0⟩ : CL.Sample F (K + m))⟩
  have hreal : (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ * Φ
      ≤ (q / m : ℕ) * (9 * (K + 1)) * (Fintype.card (CL.Sample F m) : ℝ)⁻¹ := by
    rw [inv_mul_eq_div, mul_comm _ ((Fintype.card (CL.Sample F m) : ℝ)⁻¹), inv_mul_eq_div,
      div_le_div_iff₀ hN' hN]
    exact_mod_cast hnat
  rw [hL, hR, Fintype.card_fin]
  have hS0 : 0 ≤ ∑ sm : CL.Sample F m, f sm := Finset.sum_nonneg fun sm _ => hf0 sm
  calc (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ *
        ∑ p : Fin (q / m) × CL.Sample F (K + m), f (sampleMap hm hM p.1 p.2)
      ≤ (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ * ∑ sm : CL.Sample F m, (Φ : ℝ) * f sm :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ((Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ * Φ) * ∑ sm : CL.Sample F m, f sm := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((q / m : ℕ) * (9 * (K + 1)) * (Fintype.card (CL.Sample F m) : ℝ)⁻¹)
          * ∑ sm : CL.Sample F m, f sm := mul_le_mul_of_nonneg_right hreal hS0
    _ = _ := by ring

end Count

/-! ## The padded strategy -/

section Strategy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

/-- The point measurements of player A in a strategy for the seeded test with `r` codewords, as
POVMs with outcomes in `F^r`; answers of the wrong format are read as `0`. -/
noncomputable def tuplePOVMA (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm))
    (y : Point F m) : POVM (Fin r → F) (Fin S.dA) :=
  (S.PA.toPOVM (.point y)).map valsOf

/-- The point measurements of player B, as for `tuplePOVMA`. -/
noncomputable def tuplePOVMB (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm))
    (y : Point F m) : POVM (Fin r → F) (Fin S.dB) :=
  (S.PB.toPOVM (.point y)).map valsOf

theorem toPOVM_mergeAt {X X' A A' : Type*} [Fintype A] [Fintype A'] [DecidableEq A'] {n : Type*}
    [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (qX : X' → X)
    (rX : X' → A → A') (x : X') :
    (P.mergeAt qX rX).toPOVM x = (P.toPOVM (qX x)).map (rX x) := by
  refine POVM.ext' fun a' => ?_
  rw [POVM.map_mats]
  rfl

/-- The padded strategy for the seeded test with one codeword in `K + m` variables. -/
noncomputable def padded (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm))
    (σ : Fin (Fintype.card F / m)) : TensorProductStrategy (clGame (d := d) (ldc := 1) hM) :=
  S.adapt (clGame (d := d) (ldc := 1) hM) (qmap hm hM σ) (qmap hm hM σ) (rmap hM hr) (rmap hM hr)

/-- **The padded adapter loses a factor `9 (K + 1)`** (blueprint `lem:lidt-ldc-adapter`): some
seed offset makes the padded strategy fail at most `9 (K + 1)` times as often as `S`. -/
theorem exists_padded_value (hd : 1 ≤ d) (hK : 1 ≤ K)
    (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm)) :
    ∃ σ : Fin (Fintype.card F / m),
      1 - (padded hm hM hr S σ).value ≤ 9 * (K + 1) * (1 - S.value) := by
  have : Nonempty (Fin (Fintype.card F / m)) := ⟨⟨0, card_div_pos hm⟩⟩
  obtain ⟨σ, hσ⟩ := TensorProductStrategy.exists_one_sub_value_adapt_le S
    (clGame (d := d) (ldc := 1) hM) (fun σ => qmap hm hM σ) (fun σ => qmap hm hM σ)
    (fun _ => rmap hM hr) (fun _ => rmap hM hr) (9 * (K + 1))
    (fun σ x y a b hμ h => clGame_D_rmap hm hM hr hd hK σ x y a b hμ h)
    (fun x y => sum_mu_qmap_le hm hM x y)
  exact ⟨σ, hσ⟩

/-- **The padded strategy's point measurements are the combined ones**: at the padded point
`(x, y)`, measure the original point measurement at `y` and answer `∑_{k<r} x_k b_k`. -/
theorem pointPOVMA_padded (hd : 1 ≤ d)
    (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm)) (σ : Fin (Fintype.card F / m))
    (u : Point F (K + m)) :
    CL.pointPOVMA (padded hm hM hr S σ) u = combPOVM hd (tuplePOVMA hm S) u := by
  rw [CL.pointPOVMA, combPOVM, tuplePOVMA, POVM.map_map]
  show ((S.PA.mergeAt (qmap hm hM σ) (rmap hM hr)).toPOVM (.point u)).map _ = _
  rw [toPOVM_mergeAt, POVM.map_map]
  congr 1
  funext a
  rw [eval_linPoly_padB hd hr]
  rfl

/-- The same for player B. -/
theorem pointPOVMB_padded (hd : 1 ≤ d)
    (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm)) (σ : Fin (Fintype.card F / m))
    (u : Point F (K + m)) :
    CL.pointPOVMB (padded hm hM hr S σ) u = combPOVM hd (tuplePOVMB hm S) u := by
  rw [CL.pointPOVMB, combPOVM, tuplePOVMB, POVM.map_map]
  show ((S.PB.mergeAt (qmap hm hM σ) (rmap hM hr)).toPOVM (.point u)).map _ = _
  rw [toPOVM_mergeAt, POVM.map_map]
  congr 1
  funext a
  rw [eval_linPoly_padB hd hr]
  rfl

end Strategy

end MIPRE.LIDT.Simul

end
