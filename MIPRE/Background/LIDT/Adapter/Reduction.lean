/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Adapter.Weights
import MIPRE.Background.LIDT.Soundness

/-!
# The seeded-CL adapter, part 6: the reduction

This is the payoff. `MIPRE.LIDT.lowIndividualDegree_soundness` is soundness of the
*canonical-line* test `lidtGame`, proved through the vendored MIPStarRE development; the seeded
CL test `clGame` of `def:lidt-cl` is a different test, and `rem:lidt-cl-adapter` says that
transferring soundness from one to the other needs an explicit strategy adapter. The previous
five parts built it; this one runs it.

The shape of the argument:

* a strategy `S` for `clGame` with `ldc = 1` is turned into one for `lidtGame` by reindexing the
  questions along `qmapS` (a canonical line becomes a seeded description of its reversal) and
  coarse-graining the answers along `amap` (the diagonal answer is affinely reparametrized);
* `hD_qmap` says the adapted strategy is accepted wherever `S` is, and `hμ_qmapS` says the
  push-forward of the question distribution costs a factor `3m`, so
  `exists_one_sub_value_adapt_le` produces one member of the averaging family whose adapted
  strategy has `1 - value ≤ 3m ε`;
* `lowIndividualDegree_soundness` applies to it and returns two low-degree measurements;
* the three consistency conclusions are carried back through the coordinate reversal
  (`inconsistency_congr`), which acts on the questions by `revPoint` --- measure-preserving,
  `uniform` being uniform --- and on the outcomes by `revPoly`, the same reversal of a
  polynomial's exponent vectors.

What is *not* here: the `ldc > 1` case (`lem:lidt-ldc`, the paper's Steps 1--5), and the
translation of `lidtError m d q k (3m ε)` into the `δ_CL` of `thm:lidt-cl-soundness`, which is a
separate arithmetic obligation and gets its own statement.
-/

namespace MIPRE.LIDT.Adapter

open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## Reversing a polynomial

The adapter plays a canonical-line question at the *reversed* point, so the low-degree
polynomial the soundness theorem produces is a polynomial in the reversed variables. Reversing
the exponent vectors turns it back, and does so bijectively and degree-preservingly --- the
individual degree bound `d` is symmetric in the variables. -/

/-- Coordinate reversal on exponent vectors. -/
def revExp : (Fin m → Fin (d + 1)) ≃ (Fin m → Fin (d + 1)) where
  toFun e := fun i => e (Fin.rev i)
  invFun e := fun i => e (Fin.rev i)
  left_inv e := by funext i; simp [Fin.rev_rev]
  right_inv e := by funext i; simp [Fin.rev_rev]

/-- Coordinate reversal on polynomials of individual degree at most `d`. -/
def revPoly (p : LowIndDegPoly (F := F) (m := m) (d := d)) :
    LowIndDegPoly (F := F) (m := m) (d := d) := fun e => p (revExp e)

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- **Reversing a polynomial is reversing its argument.** -/
theorem eval_revPoly (p : LowIndDegPoly (F := F) (m := m) (d := d)) (u : Point F m) :
    (revPoly p).eval u = p.eval (revPoint u) := by
  classical
  show (∑ e, (revPoly p) e * ∏ i, u i ^ ((e i : ℕ)))
    = ∑ e, p e * ∏ i, (revPoint u : Point F m) i ^ ((e i : ℕ))
  refine Finset.sum_equiv revExp (fun e => by simp) (fun e _ => ?_)
  show p (revExp e) * (∏ i, u i ^ ((e i : ℕ)))
    = p (revExp e) * ∏ i, (revPoint u : Point F m) i ^ (((revExp e) i : ℕ))
  refine congrArg (fun z : F => p (revExp e) * z) ?_
  exact (Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)).symm

/-- Polynomial reversal as an equivalence. -/
def revPolyEquiv :
    LowIndDegPoly (F := F) (m := m) (d := d) ≃ LowIndDegPoly (F := F) (m := m) (d := d) where
  toFun := revPoly
  invFun := revPoly
  left_inv p := by funext e; simp [revPoly, revExp, Fin.rev_rev]
  right_inv p := by funext e; simp [revPoly, revExp, Fin.rev_rev]

/-! ## Two computations of measurement operators -/

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
/-- The operators of a coarse-grained POVM, as a sum over the fibre. -/
theorem val_mats_map {A B n : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Fintype n]
    [DecidableEq n] (f : A → B) (M : POVM A n) (b : B) :
    ((M.map f).mats b).val = ∑ a ∈ Finset.univ.filter (fun a => f a = b), (M.mats a).val :=
  AddSubmonoidClass.coe_finsetSum _ _

/-- Composing two coarse-grainings of a sum over fibres. -/
theorem sum_filter_comp {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq ρ]
    {M : Type*} [AddCommMonoid M] (r : ι → κ) (g : κ → ρ) (h : ι → M) (f : ρ) :
    (∑ a' ∈ Finset.univ.filter (fun a' => g a' = f),
        ∑ a ∈ Finset.univ.filter (fun a => r a = a'), h a)
      = ∑ a ∈ Finset.univ.filter (fun a => g (r a) = f), h a := by
  classical
  have hmaps : ∀ a ∈ Finset.univ.filter (fun a => g (r a) = f),
      r a ∈ Finset.univ.filter (fun a' => g a' = f) := fun a ha =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps h]
  refine Finset.sum_congr rfl fun a' ha' => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h1 => ⟨by rw [h1]; exact (Finset.mem_filter.mp ha').2, h1⟩, fun h1 => h1.2⟩

omit [Fintype F] [NeZero m] in
/-- **The adapter reads a point answer exactly as the seeded test does.** -/
theorem toValue_amap_point (c : F) (u : Point F m) (a : CL.Answer F m d 1) :
    (amap c (Question.point u) a).toValue = a.toValue := by
  cases a <;> rfl

/-! ## The adapted strategy's point measurements -/

variable {hm : m ∣ Fintype.card F}

/-- The strategy the adapter builds, for one member of the averaging family. -/
noncomputable def adapted (σc : Seed F m)
    (S : TensorProductStrategy (clGame (d := d) (ldc := 1) hm)) :
    TensorProductStrategy (lidtGame F m d) :=
  S.adapt (lidtGame F m d) (qmapS hm σc) (qmapS hm σc)
    (fun x' => amap (σc.2 : F) x') (fun y' => amap (σc.2 : F) y')

/-- **A's point measurement of the adapted strategy is A's point measurement of the seeded
strategy at the reversed point.** -/
theorem val_mats_pointPOVMA_adapted (σc : Seed F m)
    (S : TensorProductStrategy (clGame (d := d) (ldc := 1) hm)) (u : Point F m) (f : F) :
    ((CL.pointPOVMA S u).mats f).val
      = ((pointPOVMA (adapted σc S) (revPoint u)).mats f).val := by
  classical
  rw [CL.pointPOVMA, pointPOVMA, val_mats_map, val_mats_map]
  have hR : ∀ a : Answer F m d,
      (((adapted σc S).PA.toPOVM (Question.point (revPoint u))).mats a).val
        = ∑ b ∈ Finset.univ.filter (fun b : CL.Answer F m d 1 =>
            amap (σc.2 : F) (Question.point (revPoint u)) b = a),
              ((S.PA.toPOVM (CL.Question.point u)).mats b).val := by
    intro a
    have h1 : (adapted σc S).PA.M (Question.point (revPoint u)) a
        = ∑ b ∈ Finset.univ.filter (fun b : CL.Answer F m d 1 =>
            amap (σc.2 : F) (Question.point (revPoint u)) b = a),
              S.PA.M (qmapS hm σc (Question.point (revPoint u))) b := rfl
    rw [qmapS_point, revPoint_revPoint] at h1
    exact h1
  refine Eq.symm ?_
  refine (Finset.sum_congr rfl fun a _ => hR a).trans ?_
  refine (sum_filter_comp (fun b : CL.Answer F m d 1 =>
      amap (σc.2 : F) (Question.point (revPoint u)) b) (Answer.toValue : Answer F m d → F)
      (fun b : CL.Answer F m d 1 => ((S.PA.toPOVM (CL.Question.point u)).mats b).val) f).trans ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, toValue_amap_point]

/-- **B's point measurement, likewise.** -/
theorem val_mats_pointPOVMB_adapted (σc : Seed F m)
    (S : TensorProductStrategy (clGame (d := d) (ldc := 1) hm)) (u : Point F m) (f : F) :
    ((CL.pointPOVMB S u).mats f).val
      = ((pointPOVMB (adapted σc S) (revPoint u)).mats f).val := by
  classical
  rw [CL.pointPOVMB, pointPOVMB, val_mats_map, val_mats_map]
  have hR : ∀ a : Answer F m d,
      (((adapted σc S).PB.toPOVM (Question.point (revPoint u))).mats a).val
        = ∑ b ∈ Finset.univ.filter (fun b : CL.Answer F m d 1 =>
            amap (σc.2 : F) (Question.point (revPoint u)) b = a),
              ((S.PB.toPOVM (CL.Question.point u)).mats b).val := by
    intro a
    have h1 : (adapted σc S).PB.M (Question.point (revPoint u)) a
        = ∑ b ∈ Finset.univ.filter (fun b : CL.Answer F m d 1 =>
            amap (σc.2 : F) (Question.point (revPoint u)) b = a),
              S.PB.M (qmapS hm σc (Question.point (revPoint u))) b := rfl
    rw [qmapS_point, revPoint_revPoint] at h1
    exact h1
  refine Eq.symm ?_
  refine (Finset.sum_congr rfl fun a _ => hR a).trans ?_
  refine (sum_filter_comp (fun b : CL.Answer F m d 1 =>
      amap (σc.2 : F) (Question.point (revPoint u)) b) (Answer.toValue : Answer F m d → F)
      (fun b : CL.Answer F m d 1 => ((S.PB.toPOVM (CL.Question.point u)).mats b).val) f).trans ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, toValue_amap_point]

/-! ## Reversing the low-degree measurements -/

/-- The reversal of a measurement with polynomial outcomes. -/
def revMeas {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
      (Matrix n n ℂ)) :
    ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d)) (Matrix n n ℂ) :=
  G.reindex (fun _ : Unit => ()) revPolyEquiv

omit [NeZero m] in
/-- **Evaluating the reversal is evaluating at the reversed point.** -/
theorem val_mats_evalPOVM_revMeas {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
      (Matrix n n ℂ)) (u : Point F m) (a : F) :
    ((evalPOVM (revMeas G) u).mats a).val = ((evalPOVM G (revPoint u)).mats a).val := by
  classical
  rw [evalPOVM, evalPOVM, val_mats_map, val_mats_map]
  refine Finset.sum_equiv revPolyEquiv (fun p => ?_) (fun p _ => rfl)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, revPolyEquiv, Equiv.coe_fn_mk,
    eval_revPoly, revPoint_revPoint]

/-! ## The reduction -/

/-- **Soundness of the seeded CL test at `ldc = 1`, by reduction to the canonical-line test.**

A strategy for `clGame` passing with probability at least `1 - ε` has point measurements
consistent, up to `lidtError m d q k (3m·ε)`, with the evaluations of a single measurement with
low-individual-degree outcomes --- one per player, the two consistent with each other. The
factor `3m` is the push-forward cost of the adapter (`hμ_qmapS`); the `k` is free subject to
`k ≥ 400md`, exactly as in the canonical-line theorem.

This is the `ldc = 1` case of `thm:lidt-cl-soundness` *with the error in the canonical-line
form*. Turning `lidtError m d q k (3m ε)` into the `δ_CL` the blueprint asks for is a separate
arithmetic obligation, and `ldc > 1` is `lem:lidt-ldc`, a separate piece of work on top. -/
theorem clSoundness_ldc_one
    (S : TensorProductStrategy (clGame (d := d) (ldc := 1) hm)) (ε : ℝ) (hS : 1 - ε ≤ S.value)
    (k : ℕ) (hk : 400 * m * d ≤ k) (hk0 : 0 < k) :
    ∃ GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dA) (Fin S.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dB) (Fin S.dB) ℂ),
      inconsistency (uniform (Point F m)) S.ψ (CL.pointPOVMA S) (evalPOVM GB)
          ≤ lidtError m d (Fintype.card F) k (3 * m * ε) ∧
        inconsistency (uniform (Point F m)) S.ψ (evalPOVM GA) (CL.pointPOVMB S)
          ≤ lidtError m d (Fintype.card F) k (3 * m * ε) ∧
        inconsistency (uniform Unit) S.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ lidtError m d (Fintype.card F) k (3 * m * ε) := by
  classical
  have : Nonempty (Seed F m) := nonempty_seed hm
  -- choose the family member the derandomization provides
  obtain ⟨σc, hval⟩ := TensorProductStrategy.exists_one_sub_value_adapt_le
    (S := S) (G' := lidtGame F m d)
    (qA := fun σc : Seed F m => qmapS hm σc) (qB := fun σc : Seed F m => qmapS hm σc)
    (rA := fun (σc : Seed F m) (x' : Question F m) => amap (σc.2 : F) x')
    (rB := fun (σc : Seed F m) (y' : Question F m) => amap (σc.2 : F) y')
    (C := 3 * m)
    (fun σc x' y' a b hμ0 hacc => hD_qmap hm σc.1 σc.2.2 x' y' hμ0 a b hacc)
    (fun x y => hμ_qmapS (d := d) (ldc := 1) hm x y)
  -- the adapted strategy is good
  have hval' : 1 - (adapted σc S).value ≤ 3 * (m : ℝ) * (1 - S.value) := hval
  have hS'val : 1 - 3 * (m : ℝ) * ε ≤ (adapted σc S).value := by
    have hmnn : (0 : ℝ) ≤ 3 * m := by positivity
    nlinarith [hval', hS]
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    lowIndividualDegree_soundness (adapted σc S) (3 * (m : ℝ) * ε) hS'val k hk hk0
  refine ⟨revMeas GA, revMeas GB, ?_, ?_, ?_⟩
  · have heq : inconsistency (uniform (Point F m)) S.ψ (CL.pointPOVMA S) (evalPOVM (revMeas GB))
        = inconsistency (uniform (Point F m)) S.ψ (pointPOVMA (adapted σc S)) (evalPOVM GB) :=
      inconsistency_congr (uniform (Point F m)) (uniform (Point F m)) S.ψ
        (pointPOVMA (adapted σc S)) (evalPOVM GB) (CL.pointPOVMA S) (evalPOVM (revMeas GB))
        revPoint (Equiv.refl F) (fun _ => rfl)
        (fun u a => val_mats_pointPOVMA_adapted σc S u a)
        (fun u a => val_mats_evalPOVM_revMeas GB u a)
    exact le_of_eq_of_le heq h1
  · have heq : inconsistency (uniform (Point F m)) S.ψ (evalPOVM (revMeas GA)) (CL.pointPOVMB S)
        = inconsistency (uniform (Point F m)) S.ψ (evalPOVM GA) (pointPOVMB (adapted σc S)) :=
      inconsistency_congr (uniform (Point F m)) (uniform (Point F m)) S.ψ
        (evalPOVM GA) (pointPOVMB (adapted σc S)) (evalPOVM (revMeas GA)) (CL.pointPOVMB S)
        revPoint (Equiv.refl F) (fun _ => rfl)
        (fun u a => val_mats_evalPOVM_revMeas GA u a)
        (fun u a => val_mats_pointPOVMB_adapted σc S u a)
    exact le_of_eq_of_le heq h2
  · have heq : inconsistency (uniform Unit) S.ψ (fun _ => (revMeas GA).toPOVM ())
          (fun _ => (revMeas GB).toPOVM ())
        = inconsistency (uniform Unit) S.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) :=
      inconsistency_congr (uniform Unit) (uniform Unit) S.ψ
        (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
        (fun _ => (revMeas GA).toPOVM ()) (fun _ => (revMeas GB).toPOVM ())
        (Equiv.refl Unit) revPolyEquiv (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    exact le_of_eq_of_le heq h3

end MIPRE.LIDT.Adapter
