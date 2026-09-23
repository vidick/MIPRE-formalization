/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.SoundCopy
import MIPRE.Background.AnswerReduction.TypedGame
import MIPRE.Foundations.GameAdapt
import MIPRE.Foundations.SampledGame

/-!
# Soundness of answer reduction: the per-seed low-degree games

Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`, `def:ar-seed-index`).
A strategy for the typed answer-reduced game, restricted to one copy of the low-degree test at a
role pair where that copy is tested and to one seed of the input sampler, is a strategy for the
seeded CL test of the copy's parameters (`copyStrategy`): its question maps a CL question to the
typed question whose PCP half the copy's presentation computes (`Regs.embedQ`) and whose oracle
half the seed's role family gives, and its answers are parsed and read as answers of the copy's
test. The seeds are indexed by the full seed of the input sampler, as the blueprint's
`def:ar-seed-index` asks.

The per-seed failures average to at most a constant times the typed failure
(`sum_one_sub_value_copyStrategy_le`): the copy's nine type pairs are a fixed fraction of the
typed game's, and the copy's registers of a uniform PCP vector carry a uniform sample
(`Regs.sum_sampleOf`).
-/

noncomputable section

namespace MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
  (hm : m ∣ Fintype.card F)

/-- The seeded test's distribution is the push-forward of the uniform sample. -/
theorem clGame_μ (x y : Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y =
      SampledGame.dist (fun sm : Sample F m => sm.question hm sm.tyA)
        (fun sm : Sample F m => sm.question hm sm.tyB) x y := by
  simp only [clGame, SampledGame.dist, Finset.mul_sum]
  refine Finset.sum_congr rfl fun sm _ => ?_
  congr 1
  split_ifs <;> rfl

/-- **The seeded test's failure is the average failure over samples.** -/
theorem one_sub_value_clGame (T : TensorProductStrategy (clGame (d := d) (ldc := ldc) hm)) :
    1 - T.value = (∑ sm : Sample F m, T.failAt (sm.question hm sm.tyA) (sm.question hm sm.tyB))
      / Fintype.card (Sample F m) := by
  rw [T.one_sub_value_eq_sum_failAt]
  simp_rw [clGame_μ]
  exact SampledGame.sum_dist_mul _ _ T.failAt

end MIPRE.LIDT.CL

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.CL.CLFun MIPRE.LIDT SAT Pcp Cost

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)

/-- The bits of a vector of `V^pcp`, in the numbering of a question's PCP half. -/
def pcpBits (w : Coord P → Fq P hk) : Fin (Pcp.pcpDim P * P.k) → 𝔽₂ :=
  reindexEquiv (Pcp.bitIndex P P.k) (downsizeEquiv (basis P hk) w)

theorem pcpPart_append (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    pcpPart V n P hk (Fin.append x (pcpBits P hk w)) = w := by
  simp [pcpPart, pcpBits, rightPart_append]

theorem oraclePart_append (x : Fin (V.sampler.dim n) → 𝔽₂) (w : Coord P → Fq P hk) :
    oraclePart V n P (Fin.append x (pcpBits P hk w)) = x := by
  simp [oraclePart, leftPart_append]

variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool) (B : ℕ)

/-- **The typed question of a CL question** of copy `i ≤ 5`, at role `r` and oracle half `x`. -/
def arQ1 (r : Role) (i : Fin 5) (x : Fin (V.sampler.dim n) → 𝔽₂)
    (q : LIDT.CL.Question (Fq P hk) P.m) : Detyping.Question ArTy (Fin (dim V n P)) :=
  ((r, (i.castSucc, q.ty)), Fin.append x (pcpBits P hk ((regs P i).embedQ S q)))

/-- **An answer read as an answer of copy `i`'s test**: parsed at the question's type, then read by
`ans1`; a failed parse reads as the zero point answer. -/
def readAns1 (i : Fin 5) (q : LIDT.CL.Question (Fq P hk) P.m) (a : Verifier.Answers B) :
    LIDT.CL.Answer (Fq P hk) P.m dPcp 1 :=
  ans1 ((parse (fld P hk) (i.castSucc, q.ty) a.1).getD (.inl (.values 0)))

/-- **The per-seed low-degree strategy** of copy `i ≤ 5` at role `r` and seed `x₀` of the input
sampler: the typed strategy played through `arQ1` and `readAns1`, both players at role `r`. -/
def copyStrategy (T : TensorProductStrategy (typedGame V n P hk S S' check B)) (r : Role)
    (i : Fin 5) (x₀ : Fin (V.sampler.dim n) → 𝔽₂) :
    TensorProductStrategy (LIDT.CL.clGame (d := dPcp) (ldc := 1) hm) :=
  T.adapt _ (arQ1 V n P hk S r i ((roleFamily (V.sampler.cl n) r).eval x₀))
    (arQ1 V n P hk S r i ((roleFamily (V.sampler.cl n) r).eval x₀))
    (readAns1 P hk B i) (readAns1 P hk B i)

/-- **The per-seed strategy loses no acceptance**: on the question pair of a sample of the copy's
test, an answer pair the typed predicate accepts at the corresponding typed questions is read as
one the copy's test accepts, at a role pair where the copy is tested. -/
theorem copy_accepts {r : Role} {i : Fin 5} (hr : LDStep r i) (x₀ : Fin (V.sampler.dim n) → 𝔽₂)
    (sm : LIDT.CL.Sample (Fq P hk) P.m) {a b : Verifier.Answers B}
    (h : typedPred V n P hk S S' check B (arQ1 V n P hk S r i x₀ (sm.question hm sm.tyA))
      (arQ1 V n P hk S r i x₀ (sm.question hm sm.tyB)) a b = true) :
    LIDT.CL.accepts hm (sm.question hm sm.tyA) (sm.question hm sm.tyB) (readAns1 P hk B i
      (sm.question hm sm.tyA) a) (readAns1 P hk B i (sm.question hm sm.tyB) b) = true := by
  obtain ⟨u, v, hu, hv, hacc⟩ := accepts_of_typedPred V n P hk S S' check h
  have hu' : parse (fld P hk) (i.castSucc, (sm.question hm sm.tyA).ty) a.1 = some u := hu
  have hv' : parse (fld P hk) (i.castSucc, (sm.question hm sm.tyB).ty) b.1 = some v := hv
  simp only [readAns1, hu', hv', Option.getD_some]
  simp only [decodeQ, arQ1, oraclePart_append, pcpPart_append] at hacc
  have hc := cl_accepts_of_accepts S S' check hr _ _ hacc
  simp only [q1, LIDT.CL.Sample.question_ty] at hc
  rw [LIDT.CL.Regs.sampleOf_embedQ, LIDT.CL.Regs.sampleOf_embedQ] at hc
  exact hc

/-- The typed question pair of sample `sm` at seed `x₀`, and `T`'s failure there. -/
def copyFail (T : TensorProductStrategy (typedGame V n P hk S S' check B)) (r : Role) (i : Fin 5)
    (x₀ : Fin (V.sampler.dim n) → 𝔽₂) (sm : LIDT.CL.Sample (Fq P hk) P.m) : ℝ :=
  T.failAt (arQ1 V n P hk S r i ((roleFamily (V.sampler.cl n) r).eval x₀) (sm.question hm sm.tyA))
    (arQ1 V n P hk S r i ((roleFamily (V.sampler.cl n) r).eval x₀) (sm.question hm sm.tyB))

/-- **The per-seed failure** is at most the average of `T`'s failures at the typed questions of
the copy's samples. -/
theorem one_sub_value_copyStrategy_le (T : TensorProductStrategy (typedGame V n P hk S S' check B))
    {r : Role} {i : Fin 5} (hr : LDStep r i) (x₀ : Fin (V.sampler.dim n) → 𝔽₂) :
    1 - (copyStrategy V n P hk S S' check B T r i x₀).value
      ≤ (∑ sm, copyFail V n P hk S S' check B T r i x₀ sm)
        / Fintype.card (LIDT.CL.Sample (Fq P hk) P.m) := by
  rw [LIDT.CL.one_sub_value_clGame]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sm _ => ?_) (by positivity)
  exact TensorProductStrategy.failAt_adapt_le T _ _ _ _ _ _ _
    fun a b h => copy_accepts V n P hk S S' check B hr _ sm h

omit [NeZero P.m] in
/-- The bits of a vector of `V^pcp`, as an equivalence. -/
def pcpBitsEquiv : (Coord P → Fq P hk) ≃ (Fin (Pcp.pcpDim P * P.k) → 𝔽₂) :=
  ((downsizeEquiv (basis P hk)).trans (reindexEquiv (Pcp.bitIndex P P.k))).toEquiv

omit [NeZero P.m] in
theorem pcpBitsEquiv_apply (w : Coord P → Fq P hk) : pcpBitsEquiv P hk w = pcpBits P hk w := rfl

/-- **The typed question of copy `i` at type `τ`**, on the vector whose oracle half is `x` and whose
PCP half is `w`: the typed question `arQ1` of the sample copy `i`'s registers carry. -/
theorem cl_eval_append (r : Role) (i : Fin 5) (τ : LIDT.CL.Ty) (x : Fin (V.sampler.dim n) → 𝔽₂)
    (w : Coord P → Fq P hk) :
    (((r, (i.castSucc, τ)) : ArTy), (cl V n P hk S S' (r, (i.castSucc, τ))).eval
      (Fin.append x (pcpBits P hk w)))
      = arQ1 V n P hk S r i ((roleFamily (V.sampler.cl n) r).eval x)
        (((regs P i).sampleOf S τ w).question hm τ) := by
  rw [arQ1, LIDT.CL.Sample.question_ty, eval_cl, leftPart_append, rightPart_append, pcpBits,
    pcpCl_eval, pres_lt S S' w τ (by simp), ← LIDT.CL.Regs.pres_eval]
  rfl

set_option maxRecDepth 10000 in
/-- **The copy's edges inside the typed failure**: the nine type pairs of copy `i` at role `r`,
summed over the seeds and the samples, weigh at most the typed game's failure. -/
theorem sum_copyFail_le (T : TensorProductStrategy (typedGame V n P hk S S' check B)) (r : Role)
    (i : Fin 5) :
    (Fintype.card (Fq P hk) ^ (Fintype.card (Coord P) - (2 * P.m + 1)) : ℝ) *
        ∑ x₀, ∑ sm, copyFail V n P hk S S' check B T r i x₀ sm
      ≤ (Fintype.card (ArTy × ArTy) * Fintype.card (Fin (dim V n P) → 𝔽₂)) * (1 - T.value) := by
  have hpos : (0 : ℝ) < Fintype.card (ArTy × ArTy) * Fintype.card (Fin (dim V n P) → 𝔽₂) := by
    positivity
  set f : ArTy × ArTy → (Fin (dim V n P) → 𝔽₂) → ℝ := fun uv z =>
    T.failAt (uv.1, (cl V n P hk S S' uv.1).eval z) (uv.2, (cl V n P hk S S' uv.2).eval z)
  have hT : 1 - T.value = (∑ uv ∈ Graph.edges graph, ∑ z, f uv z) /
      ((Graph.edges graph).card * Fintype.card (Fin (dim V n P) → 𝔽₂)) :=
    Detyping.typed_failure graph graph_nonempty (fun _ => cl V n P hk S S')
      (typedPred V n P hk S S' check B) T
  have hE : Graph.edges graph = Finset.univ := Finset.eq_univ_of_forall mem_graph_edges
  rw [hE, Finset.card_univ] at hT
  rw [hT, mul_div_cancel₀ _ hpos.ne']
  have hf : ∀ uv z, 0 ≤ f uv z := fun _ _ => T.failAt_nonneg _ _
  -- the nine type pairs of the copy
  let e : LIDT.CL.Ty × LIDT.CL.Ty → ArTy × ArTy := fun ab => ((r, (i.castSucc, ab.1)),
    (r, (i.castSucc, ab.2)))
  have he : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [e, Prod.mk.injEq, true_and] at h
    rw [h.1, h.2]
  calc (Fintype.card (Fq P hk) ^ (Fintype.card (Coord P) - (2 * P.m + 1)) : ℝ) *
        ∑ x₀, ∑ sm, copyFail V n P hk S S' check B T r i x₀ sm
      = ∑ ab : LIDT.CL.Ty × LIDT.CL.Ty, ∑ z, f (e ab) z := by
        rw [Finset.mul_sum]
        simp_rw [← Nat.cast_pow, ← nsmul_eq_mul]
        simp_rw [← LIDT.CL.Regs.sum_sampleOf_retype (regs P i) S]
        rw [Fintype.sum_prod_type]
        simp_rw [← (Fin.appendEquiv _ _).sum_comp, Fintype.sum_prod_type,
          ← (pcpBitsEquiv P hk).sum_comp]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
        have hq : ((regs P i).sampleOf S a w).question hm b
            = ((regs P i).sampleOf S b w).question hm b :=
          (LIDT.CL.Sample.question_retype hm _ b b b).symm
        simp only [f, e, copyFail]
        rw [show (Fin.appendEquiv _ _) (x, pcpBitsEquiv P hk w) = Fin.append x (pcpBits P hk w)
          from rfl, cl_eval_append, cl_eval_append, ← hq, LIDT.CL.Sample.question_retype,
          LIDT.CL.Sample.question_retype]
        rfl
    _ = ∑ uv ∈ Finset.univ.image e, ∑ z, f uv z := by
        rw [Finset.sum_image fun x _ y _ h => he h]
    _ ≤ ∑ uv, ∑ z, f uv z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun uv _ _ => Finset.sum_nonneg fun z _ => hf uv z

theorem card_arTy_sq : Fintype.card (ArTy × ArTy) = 2916 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  rfl

/-- **The per-seed failures average to at most `324` times the typed failure**, at a role pair
where copy `i` is tested: the copy's nine type pairs are `9 / 54^2 = 1 / 324` of the typed game's
edges, and on them the copy's registers of a uniform vector carry a uniform sample. -/
theorem sum_one_sub_value_copyStrategy_le
    (T : TensorProductStrategy (typedGame V n P hk S S' check B)) {r : Role} {i : Fin 5}
    (hr : LDStep r i) :
    ∑ x₀, (1 - (copyStrategy V n P hk S S' check B T r i x₀).value)
      ≤ Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) * (324 * (1 - T.value)) := by
  set K : ℝ := (Fintype.card (Fq P hk) : ℝ) ^ (Fintype.card (Coord P) - (2 * P.m + 1))
  set Sc : ℝ := (Fintype.card (LIDT.CL.Sample (Fq P hk) P.m) : ℝ)
  set Xc : ℝ := (Fintype.card (Fin (V.sampler.dim n) → 𝔽₂) : ℝ)
  set Wc : ℝ := (Fintype.card (Coord P → Fq P hk) : ℝ)
  have hK : 9 * Wc = K * Sc := by
    have h := LIDT.CL.Regs.sum_sampleOf_retype (regs P i) S (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
    have h9 : Fintype.card LIDT.CL.Ty = 3 := rfl
    rw [h9] at h
    simp only [Wc, K, Sc]
    exact_mod_cast (by rw [← h]; ring : 9 * Fintype.card (Coord P → Fq P hk) = _)
  have hZ : (Fintype.card (Fin (dim V n P) → 𝔽₂) : ℝ) = Xc * Wc := by
    rw [← Fintype.card_congr (Fin.appendEquiv _ _), Fintype.card_prod,
      Fintype.card_congr (pcpBitsEquiv P hk).symm]
    push_cast
    rfl
  have hKpos : 0 < K := by positivity
  have hSpos : 0 < Sc := by
    simp only [Sc]
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(⟨.point, .point, 0, 0, 0⟩ : LIDT.CL.Sample (Fq P hk) P.m)⟩
  have h2 := sum_copyFail_le V n P hk S S' check B T r i
  rw [card_arTy_sq, hZ] at h2
  calc ∑ x₀, (1 - (copyStrategy V n P hk S S' check B T r i x₀).value)
      ≤ ∑ x₀, (∑ sm, copyFail V n P hk S S' check B T r i x₀ sm) / Sc :=
        Finset.sum_le_sum fun x₀ _ => one_sub_value_copyStrategy_le V n P hk S S' check B T hr x₀
    _ = (∑ x₀, ∑ sm, copyFail V n P hk S S' check B T r i x₀ sm) / Sc := by
        rw [Finset.sum_div]
    _ ≤ Xc * (324 * (1 - T.value)) := by
        rw [div_le_iff₀ hSpos]
        refine le_of_mul_le_mul_left ?_ hKpos
        refine h2.trans (le_of_eq ?_)
        push_cast
        linear_combination (324 * Xc * (1 - T.value)) * hK

end MIPRE.AnswerReduction

end
