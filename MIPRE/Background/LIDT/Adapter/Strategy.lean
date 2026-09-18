/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Adapter.Geometry
import MIPRE.Background.LIDT.Adapter.Reparam
import MIPRE.Background.LIDT.Adapter.Seeds
import MIPRE.Foundations.GameAdapt

/-!
# The seeded-CL adapter, part 4: the question and answer maps

The reduction plays a strategy for the seeded CL test as a strategy for the canonical-line
test, through `MIPRE.TensorProductStrategy.adapt`. That needs two maps, and this file defines
them and the bookkeeping that identifies them.

`qmap hm σ` sends a question of the canonical-line test to the seeded question it is played
through:

* a point `u` to the point `ρ u`, reversal exchanging the two diagonal conventions;
* an axis-parallel line to `(ρ ℓ.1, s)` — no `rep` is needed, the two tests' base points agree
  exactly there (`rep_single_eq_through`) — with `s` the chosen seed of the fibre over
  `rev (axisIdx ℓ)`;
* a diagonal line to `(rep (ρ ℓ.2) (ρ ℓ.1), s, ρ ℓ.2)`, carrying the direction *unrescaled*.
  That is legitimate because the seeded test's `DLine` questions carry the raw direction, and it
  is what makes the answer conversion a pure shift rather than a shift and a scaling.

`amap` sends a seeded answer to a canonical-line answer, and depends on the question — the
shift does. Its unreachable branches are unreachable because `clGame` *rejects* an answer
whose format does not match its question's type; before that was repaired the branches would
have been live.

`shiftOf ℓ` is the shift, read off `rep_eq`: the two base points differ by `shiftOf ℓ` times the
direction (`rep_rev_eq`), so the two parameters of a point of the line differ by `shiftOf ℓ`.
-/

namespace MIPRE.LIDT.Adapter

open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## Reading the direction off a line -/

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem single_inj {i j : Fin m} (h : (Pi.single i 1 : Point F m) = Pi.single j 1) : i = j := by
  by_contra hne
  have hi := congrFun h i
  rw [Pi.single_eq_same, Pi.single_apply, if_neg hne] at hi
  exact one_ne_zero hi

/-- A default index, for the branches of the maps below that the support never reaches. -/
def idx0 : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

/-- The direction index of an axis-parallel line. -/
noncomputable def axisIdx (ℓ : Line F m) : Fin m :=
  if h : ∃ i : Fin m, ℓ.2 = Pi.single i 1 then h.choose else idx0

omit [Fintype F] in
@[simp] theorem axisIdx_eq (b : Point F m) (i : Fin m) :
    axisIdx ((b, Pi.single i 1) : Line F m) = i := by
  have h : ∃ j : Fin m, ((b, Pi.single i 1) : Line F m).2 = Pi.single j 1 := ⟨i, rfl⟩
  rw [axisIdx, dif_pos h]
  exact (single_inj h.choose_spec).symm

/-- The `χ`-index the adapter uses for a diagonal line: the first nonzero coordinate of the
reversed direction, which is the pivot of its span and so the coordinate `rep` zeroes.

The fallback for a *singleton* line (direction zero) is `rev idx0 = m - 1`, not `idx0`, and the
choice is forced by the weight bookkeeping rather than free. The seeded test's `DLine` samples
with `zeroBelow (χ s) V = 0` number `q^{χ s}`, so its mass on `(u₀, s, 0)` grows with `χ s`;
the canonical-line test puts mass `≈ 1/(6 m q^m q)` on a singleton line, which only the largest
`χ` can dominate. Sending singleton lines to `χ = 0` costs a factor `q^{m-1}`, which the error
term of `thm:lidt-cl-soundness` does not allow. See `planning/lidt-cl-adapter.md`. -/
noncomputable def diagIdx (ℓ : Line F m) : Fin m :=
  if h : ∃ j, (revPoint ℓ.2) j ≠ 0 then Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h
  else Fin.rev idx0

omit [Fintype F] in
/-- The fallback, named. -/
theorem diagIdx_of_dir_eq_zero {ℓ : Line F m} (h : (revPoint ℓ.2 : Point F m) = 0) :
    diagIdx ℓ = Fin.rev idx0 := by
  refine dif_neg fun hc => ?_
  obtain ⟨j, hj⟩ := hc
  exact hj (by rw [h]; rfl)

omit [Fintype F] in
/-- On a nondegenerate line `diagIdx` is the pivot. -/
theorem diagIdx_eq_find {ℓ : Line F m} (h : ∃ j, (revPoint ℓ.2) j ≠ 0) :
    diagIdx ℓ = Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h := dif_pos h

/-- The shift between the two presentations of a line. -/
noncomputable def shiftOf (ℓ : Line F m) : F :=
  if h : ∃ j, (revPoint ℓ.2) j ≠ 0 then
    (revPoint ℓ.1) (Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h)
      / (revPoint ℓ.2) (Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h)
  else 0

/-! ## The seeded test's base point, in terms of the shift -/

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- `canonLin` of the zero subspace is the identity: there are no pivots. -/
theorem canonLin_bot (x : Fin m → F) : canonLin (⊥ : Submodule F (Fin m → F)) x = x := by
  classical
  have hpiv : pivots (⊥ : Submodule F (Fin m → F)) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj => ?_
    have h1 : dimTail (⊥ : Submodule F (Fin m → F)) ((j : ℕ) + 1) = 0 := by simp [dimTail]
    have h2 : dimTail (⊥ : Submodule F (Fin m → F)) (j : ℕ) = 0 := by simp [dimTail]
    rw [mem_pivots, h1, h2] at hj
    exact absurd hj (lt_irrefl 0)
  refine projection_eq_of (isCompl_canonCompl _).symm ?_ ?_
  · rw [canonCompl, hpiv, mem_coordSub]
    intro i hi
    exact absurd hi (Finset.notMem_empty i)
  · rw [sub_self]
    exact Submodule.zero_mem _

omit [Fintype F] [NeZero m] in
/-- **The two base points differ by the shift times the direction.** -/
theorem rep_rev_eq (ℓ : Line F m) :
    canonLin (span F {revPoint ℓ.2}) (revPoint ℓ.1)
      = revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2 := by
  by_cases h : ∃ j, (revPoint ℓ.2) j ≠ 0
  · rw [rep_eq h, shiftOf, dif_pos h]
  · have h0 : (revPoint ℓ.2 : Fin m → F) = 0 := by
      funext j
      exact not_not.mp (fun hc => h ⟨j, hc⟩)
    rw [h0, Set.singleton_zero, Submodule.span_zero, canonLin_bot, shiftOf, dif_neg h,
      zero_smul, sub_zero]

/-! ## The two maps -/

/-- The seeded question a canonical-line question is played through, for the seed choice `σ` and
the direction scale `c`.

The scale is averaged over along with the seed, and it has to be: the seeded test's `DLine`
questions carry the raw direction, so one geometric line has `q - 1` of them, and an adapter
using only one would concentrate its push-forward on a `1/(q-1)` fraction of them and need a
`q`-dependent constant. See the second correction in `planning/lidt-cl-adapter.md`.

Scaling the direction does not move the base point, `rep` depending only on the span. -/
noncomputable def qmap (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m))
    (c : F) : Question F m → CL.Question F m
  | .point u => .point (revPoint u)
  | .axisLine ℓ =>
      .aline (revPoint ℓ.1) (seedOf hm (Fin.rev (axisIdx ℓ)) (σ (Fin.rev (axisIdx ℓ))))
  | .diagLine ℓ =>
      .dline (revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2)
        (seedOf hm (diagIdx ℓ) (σ (diagIdx ℓ))) (c • revPoint ℓ.2)

/-- The canonical-line answer a seeded answer becomes. It depends on the question because the
shift does, and on the scale `c`; the branches not listed are the ones `clGame` rejects on
format.

A point of the line at the target's parameter `t` sits at the source's parameter
`(t + shiftOf ℓ) / c`, so the substitution to undo is `t ↦ c⁻¹ t + c⁻¹ · shiftOf ℓ`. -/
noncomputable def amap (c : F) : Question F m → CL.Answer F m d 1 → Answer F m d
  | .point _, .values a => .value (a 0)
  | .axisLine _, .apolys f => .axisPoly (f 0)
  | .diagLine ℓ, .dpolys f => .diagPoly (reparam c⁻¹ (c⁻¹ * shiftOf ℓ) (f 0))
  | _, _ => .value 0

/-! ## The support of the canonical-line test's distribution -/

/-- A question pair of positive weight comes from a sample. -/
theorem exists_sample_of_μ_ne_zero {x y : Question F m}
    (h : (lidtGame F m d).μ x y ≠ 0) : ∃ s : Sample F m, s.questions = (x, y) := by
  classical
  by_contra hc
  refine h ?_
  show ∑ s : Sample F m, s.weight * (if s.questions = (x, y) then 1 else 0) = 0
  exact Finset.sum_eq_zero fun s _ => by
    rw [if_neg (fun he => hc ⟨s, he⟩), mul_zero]

/-! ## Transporting membership through the reversal -/

omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- A point on the reversed line is on the line, with the same parameter. -/
theorem eq_add_smul_of_rev {u₀ w x : Point F m} {t : F}
    (h : revPoint x = revPoint u₀ + t • revPoint w) : x = u₀ + t • w := by
  have h' := congrArg revPoint h
  rwa [revPoint_revPoint, revPoint_add, revPoint_smul, revPoint_revPoint,
    revPoint_revPoint] at h'

/-! ## Reading the answer format off the acceptance -/

theorem fmtOk_of_accepts_left {hm : m ∣ Fintype.card F} {x y : CL.Question F m}
    {a b : CL.Answer F m d 1} (h : CL.accepts hm x y a b = true) : x.fmtOk a = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  rw [CL.accepts_eq_false_left hm hc] at h
  exact absurd h (by simp)

theorem fmtOk_of_accepts_right {hm : m ∣ Fintype.card F} {x y : CL.Question F m}
    {a b : CL.Answer F m d 1} (h : CL.accepts hm x y a b = true) : y.fmtOk b = true := by
  by_contra hc
  rw [Bool.not_eq_true] at hc
  rw [CL.accepts_eq_false_right hm hc] at h
  exact absurd h (by simp)

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem eq_values_of_fmtOk {u : Point F m} {a : CL.Answer F m d 1}
    (h : (CL.Question.point u).fmtOk a = true) : ∃ α, a = .values α := by
  cases a with
  | values α => exact ⟨α, rfl⟩
  | apolys f => exact absurd h (by simp [CL.Question.fmtOk])
  | dpolys f => exact absurd h (by simp [CL.Question.fmtOk])

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem eq_apolys_of_fmtOk {u₀ : Point F m} {s : F} {a : CL.Answer F m d 1}
    (h : (CL.Question.aline u₀ s).fmtOk a = true) : ∃ f, a = .apolys f := by
  cases a with
  | values α => exact absurd h (by simp [CL.Question.fmtOk])
  | apolys f => exact ⟨f, rfl⟩
  | dpolys f => exact absurd h (by simp [CL.Question.fmtOk])

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
theorem eq_dpolys_of_fmtOk {u₀ : Point F m} {s : F} {v : Point F m} {a : CL.Answer F m d 1}
    (h : (CL.Question.dline u₀ s v).fmtOk a = true) : ∃ f, a = .dpolys f := by
  cases a with
  | values α => exact absurd h (by simp [CL.Question.fmtOk])
  | apolys f => exact absurd h (by simp [CL.Question.fmtOk])
  | dpolys f => exact ⟨f, rfl⟩

/-! ## `hD`: acceptance survives the two maps

One lemma per case of `Sample`, since the source's acceptance says something different in each.
-/

variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}

/-- The self-consistency case: both players are asked the same point, and both tests check that
the two answers agree. -/
theorem hD_selfCons (u : Point F m) (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.point u)) (qmap hm σ c (.point u)) a b = true) :
    (lidtGame F m d).D (.point u) (.point u) (amap c (.point u) a) (amap c (.point u) b) = true := by
  have hq : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hq] at hacc
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨β, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_right hacc)
  have hab : α = β := by
    have h : CL.subtests (d := d) hm (CL.Question.point (revPoint u))
        (CL.Question.point (revPoint u)) (.values α : CL.Answer F m d 1)
        (.values β : CL.Answer F m d 1) = true := by
      have := hacc
      rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at this
      simpa [CL.Question.fmtOk] using this
    exact of_decide_eq_true (by simpa [CL.subtests] using h)
  show LIDT.accepts F m d (.point u) (.point u) (.value (α 0)) (.value (β 0)) = true
  simp [LIDT.accepts, hab]

/-- The axis-parallel case: the source checks the point is on the seeded line and the answer
evaluates correctly there, and after reversal that is the same equation the target checks. -/
theorem hD_axis (u : Point F m) (i : Fin m) (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.axisLine (Line.through u (Pi.single i 1))))
      (qmap hm σ c (.point u)) a b = true) :
    (lidtGame F m d).D (.axisLine (Line.through u (Pi.single i 1))) (.point u)
      (amap c (.axisLine (Line.through u (Pi.single i 1))) a) (amap c (.point u) b) = true := by
  classical
  set ℓ : Line F m := Line.through u (Pi.single i 1) with hℓdef
  have hthr : ℓ = (u - u i • (Pi.single i 1 : Point F m), (Pi.single i 1 : Point F m)) :=
    through_single i u
  have hd2 : ℓ.2 = (Pi.single i 1 : Point F m) := by rw [hthr]
  have hidx : axisIdx ℓ = i := by rw [hthr]; exact axisIdx_eq _ i
  set s : F := seedOf hm (Fin.rev i) (σ (Fin.rev i)) with hs
  have hchi : chi hm s = Fin.rev i := chi_seedOf hm _ _
  have hqA : qmap hm σ c (Question.axisLine ℓ) = CL.Question.aline (revPoint ℓ.1) s := by
    rw [qmap, hidx]
  have hqB : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hqA, hqB] at hacc
  obtain ⟨f, rfl⟩ := eq_apolys_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_right hacc)
  -- the source's subtest, with the direction rewritten as the reversal of the target's
  have hdir : (Pi.single (chi hm s) 1 : Point F m) = revPoint ℓ.2 := by
    rw [hchi, hd2, revPoint_single]
  have hsub : CL.lineVsPoint (revPoint ℓ.1) (revPoint ℓ.2) (revPoint u) f α = true := by
    have h : CL.subtests (d := d) hm (CL.Question.aline (revPoint ℓ.1) s)
        (CL.Question.point (revPoint u)) (.apolys f : CL.Answer F m d 1)
        (.values α : CL.Answer F m d 1) = true := by
      have := hacc
      rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at this
      simpa [CL.Question.fmtOk] using this
    rw [show CL.subtests (d := d) hm (CL.Question.aline (revPoint ℓ.1) s)
      (CL.Question.point (revPoint u)) (.apolys f : CL.Answer F m d 1)
      (.values α : CL.Answer F m d 1)
      = CL.lineVsPoint (revPoint ℓ.1) (Pi.single (chi hm s) 1) (revPoint u) f α from rfl,
      hdir] at h
    exact h
  obtain ⟨⟨t, ht⟩, heval⟩ := of_decide_eq_true (by simpa [CL.lineVsPoint] using hsub)
  -- transport membership and the parameter
  have hmem : u = ℓ.1 + t • ℓ.2 := eq_add_smul_of_rev ht
  have hex : ∃ j, (revPoint ℓ.2) j ≠ 0 := by
    refine ⟨Fin.rev i, ?_⟩
    rw [hd2, revPoint_single]
    simp
  have hparam : CL.lineParam (revPoint ℓ.1) (revPoint ℓ.2) (revPoint u) = t := by
    rw [ht]
    exact lineParam_eq_of_mem hex _ t
  have hpt : Line.param ℓ u = t := by
    have hv : ∃ j, (Pi.single i 1 : Point F m) j ≠ 0 := ⟨i, by simp⟩
    have := param_through_eq_of_mem hv u t
    rw [← hℓdef] at this
    rw [hmem]
    exact this
  show LIDT.accepts F m d (.axisLine ℓ) (.point u) (.axisPoly (f 0)) (.value (α 0)) = true
  rw [show LIDT.accepts F m d (.axisLine ℓ) (.point u) (.axisPoly (f 0)) (.value (α 0))
    = decide (ℓ.Mem u ∧ (f 0).eval (Line.param ℓ u) = α 0) from rfl]
  refine decide_eq_true ⟨⟨t, hmem⟩, ?_⟩
  rw [hpt, ← hparam]
  exact heval

/-- The diagonal case, and the one the affine rebasing exists for. The two tests' base points
differ by `shiftOf ℓ` times the direction and the directions by the scale `c`, so the point at
the target's parameter `t` sits at the source's `(t + shiftOf ℓ) / c`; `reparam c⁻¹ (c⁻¹ · shiftOf ℓ)`
undoes exactly that. This is where `lineParam_smul` and the general two-parameter `reparam` are
used. -/
theorem hD_diag (hc : c ≠ 0) (u : Point F m) (j : Fin m) (v : Fin ((j : ℕ) + 1) → F)
    (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D
      (qmap hm σ c (.diagLine (Line.through u (Sample.extend v)))) (qmap hm σ c (.point u)) a b
      = true) :
    (lidtGame F m d).D (.diagLine (Line.through u (Sample.extend v))) (.point u)
      (amap c (.diagLine (Line.through u (Sample.extend v))) a) (amap c (.point u) b) = true := by
  classical
  set ℓ : Line F m := Line.through u (Sample.extend v) with hℓdef
  set sh : F := shiftOf ℓ with hsh
  set u₀ : Point F m := revPoint ℓ.1 - sh • revPoint ℓ.2 with hu₀
  have hqL : qmap hm σ c (Question.diagLine ℓ)
      = CL.Question.dline u₀ (seedOf hm (diagIdx ℓ) (σ (diagIdx ℓ))) (c • revPoint ℓ.2) := rfl
  have hqP : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hqL, hqP] at hacc
  obtain ⟨f, rfl⟩ := eq_dpolys_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_right hacc)
  have hsub : CL.lineVsPoint u₀ (c • revPoint ℓ.2) (revPoint u) f α = true := by
    have h := hacc
    rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at h
    simpa [CL.Question.fmtOk, CL.subtests] using h
  obtain ⟨⟨t', ht'⟩, heval⟩ := of_decide_eq_true (by simpa [CL.lineVsPoint] using hsub)
  have hrev : revPoint u = revPoint ℓ.1 + (t' * c - sh) • revPoint ℓ.2 := by
    rw [ht', hu₀]
    module
  have hmem : u = ℓ.1 + (t' * c - sh) • ℓ.2 := eq_add_smul_of_rev hrev
  show LIDT.accepts F m d (.diagLine ℓ) (.point u)
    (.diagPoly (reparam c⁻¹ (c⁻¹ * sh) (f 0))) (.value (α 0)) = true
  rw [show LIDT.accepts F m d (.diagLine ℓ) (.point u)
    (.diagPoly (reparam c⁻¹ (c⁻¹ * sh) (f 0))) (.value (α 0))
    = decide (ℓ.Mem u ∧ (reparam c⁻¹ (c⁻¹ * sh) (f 0)).eval (Line.param ℓ u) = α 0) from rfl]
  refine decide_eq_true ⟨⟨t' * c - sh, hmem⟩, ?_⟩
  by_cases hz : ∃ k, ℓ.2 k ≠ 0
  · have hzr : ∃ k, (c • revPoint ℓ.2) k ≠ 0 := by
      obtain ⟨k, hk⟩ := hz
      refine ⟨Fin.rev k, ?_⟩
      rw [Pi.smul_apply, revPoint_apply, Fin.rev_rev, smul_eq_mul]
      exact mul_ne_zero hc hk
    have hv : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
      by_contra hcon
      have h0 : (Sample.extend v : Point F m) = 0 :=
        funext fun k => not_not.mp fun hk => hcon ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hz
      rw [hℓdef, h0, Line.through, dif_neg (by simp)] at hk
      exact hk rfl
    have hparam : CL.lineParam u₀ (c • revPoint ℓ.2) (revPoint u) = t' := by
      rw [ht']
      exact lineParam_eq_of_mem hzr _ t'
    have hpt : Line.param ℓ u = t' * c - sh := by
      have := param_through_eq_of_mem hv u (t' * c - sh)
      rw [← hℓdef] at this
      rw [hmem]
      exact this
    have hkey : c⁻¹ * (t' * c - sh) + c⁻¹ * sh = t' := by
      have hc1 : c⁻¹ * (t' * c) = t' := by
        rw [mul_comm t' c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [mul_sub, hc1]
      ring
    rw [hpt, eval_reparam, hkey, ← hparam]
    exact heval
  · have h0 : (ℓ.2 : Point F m) = 0 := funext fun k => not_not.mp fun hcon => hz ⟨k, hcon⟩
    have hsh0 : sh = 0 := by
      rw [hsh, shiftOf, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk (by simp)
    have hpt : Line.param ℓ u = 0 := by
      rw [Line.param, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk rfl
    have hcl : CL.lineParam u₀ (c • revPoint ℓ.2) (revPoint u) = 0 := by
      rw [CL.lineParam, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk (by simp)
    rw [hpt, eval_reparam, hsh0, mul_zero, add_zero, ← hcl]
    exact heval

/-! ### The swapped cases

Each test hands the line to either player, so the two mirrored cases have to be done too. The
proofs are the previous two with the roles exchanged; both games' predicates carry the mirrored
clause explicitly. -/

/-- `hD_axis` with the players exchanged. -/
theorem hD_axis' (u : Point F m) (i : Fin m) (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.point u))
      (qmap hm σ c (.axisLine (Line.through u (Pi.single i 1)))) a b = true) :
    (lidtGame F m d).D (.point u) (.axisLine (Line.through u (Pi.single i 1)))
      (amap c (.point u) a) (amap c (.axisLine (Line.through u (Pi.single i 1))) b) = true := by
  classical
  set ℓ : Line F m := Line.through u (Pi.single i 1) with hℓdef
  have hthr : ℓ = (u - u i • (Pi.single i 1 : Point F m), (Pi.single i 1 : Point F m)) :=
    through_single i u
  have hd2 : ℓ.2 = (Pi.single i 1 : Point F m) := by rw [hthr]
  have hidx : axisIdx ℓ = i := by rw [hthr]; exact axisIdx_eq _ i
  set s : F := seedOf hm (Fin.rev i) (σ (Fin.rev i)) with hs
  have hchi : chi hm s = Fin.rev i := chi_seedOf hm _ _
  have hqB : qmap hm σ c (Question.axisLine ℓ) = CL.Question.aline (revPoint ℓ.1) s := by
    rw [qmap, hidx]
  have hqA : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hqA, hqB] at hacc
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨f, rfl⟩ := eq_apolys_of_fmtOk (fmtOk_of_accepts_right hacc)
  have hdir : (Pi.single (chi hm s) 1 : Point F m) = revPoint ℓ.2 := by
    rw [hchi, hd2, revPoint_single]
  have hsub : CL.lineVsPoint (revPoint ℓ.1) (revPoint ℓ.2) (revPoint u) f α = true := by
    have h := hacc
    rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at h
    rw [← hdir]
    simpa [CL.Question.fmtOk, CL.subtests] using h
  obtain ⟨⟨t, ht⟩, heval⟩ := of_decide_eq_true (by simpa [CL.lineVsPoint] using hsub)
  have hmem : u = ℓ.1 + t • ℓ.2 := eq_add_smul_of_rev ht
  have hex : ∃ k, (revPoint ℓ.2) k ≠ 0 := by
    refine ⟨Fin.rev i, ?_⟩
    rw [hd2, revPoint_single]
    simp
  have hparam : CL.lineParam (revPoint ℓ.1) (revPoint ℓ.2) (revPoint u) = t := by
    rw [ht]
    exact lineParam_eq_of_mem hex _ t
  have hpt : Line.param ℓ u = t := by
    have hv : ∃ k, (Pi.single i 1 : Point F m) k ≠ 0 := ⟨i, by simp⟩
    have := param_through_eq_of_mem hv u t
    rw [← hℓdef] at this
    rw [hmem]
    exact this
  show LIDT.accepts F m d (.point u) (.axisLine ℓ) (.value (α 0)) (.axisPoly (f 0)) = true
  rw [show LIDT.accepts F m d (.point u) (.axisLine ℓ) (.value (α 0)) (.axisPoly (f 0))
    = decide (ℓ.Mem u ∧ (f 0).eval (Line.param ℓ u) = α 0) from rfl]
  refine decide_eq_true ⟨⟨t, hmem⟩, ?_⟩
  rw [hpt, ← hparam]
  exact heval

/-- `hD_diag` with the players exchanged. -/
theorem hD_diag' (hc : c ≠ 0) (u : Point F m) (j : Fin m) (v : Fin ((j : ℕ) + 1) → F)
    (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.point u))
      (qmap hm σ c (.diagLine (Line.through u (Sample.extend v)))) a b = true) :
    (lidtGame F m d).D (.point u) (.diagLine (Line.through u (Sample.extend v)))
      (amap c (.point u) a) (amap c (.diagLine (Line.through u (Sample.extend v))) b) = true := by
  classical
  set ℓ : Line F m := Line.through u (Sample.extend v) with hℓdef
  set sh : F := shiftOf ℓ with hsh
  set u₀ : Point F m := revPoint ℓ.1 - sh • revPoint ℓ.2 with hu₀
  have hqL : qmap hm σ c (Question.diagLine ℓ)
      = CL.Question.dline u₀ (seedOf hm (diagIdx ℓ) (σ (diagIdx ℓ))) (c • revPoint ℓ.2) := rfl
  have hqP : qmap hm σ c (Question.point u) = CL.Question.point (revPoint u) := rfl
  rw [hqL, hqP] at hacc
  obtain ⟨α, rfl⟩ := eq_values_of_fmtOk (fmtOk_of_accepts_left hacc)
  obtain ⟨f, rfl⟩ := eq_dpolys_of_fmtOk (fmtOk_of_accepts_right hacc)
  have hsub : CL.lineVsPoint u₀ (c • revPoint ℓ.2) (revPoint u) f α = true := by
    have h := hacc
    rw [show (clGame (d := d) (ldc := 1) hm).D = CL.accepts hm from rfl, CL.accepts] at h
    simpa [CL.Question.fmtOk, CL.subtests] using h
  obtain ⟨⟨t', ht'⟩, heval⟩ := of_decide_eq_true (by simpa [CL.lineVsPoint] using hsub)
  have hrev : revPoint u = revPoint ℓ.1 + (t' * c - sh) • revPoint ℓ.2 := by
    rw [ht', hu₀]
    module
  have hmem : u = ℓ.1 + (t' * c - sh) • ℓ.2 := eq_add_smul_of_rev hrev
  show LIDT.accepts F m d (.point u) (.diagLine ℓ)
    (.value (α 0)) (.diagPoly (reparam c⁻¹ (c⁻¹ * sh) (f 0))) = true
  rw [show LIDT.accepts F m d (.point u) (.diagLine ℓ)
    (.value (α 0)) (.diagPoly (reparam c⁻¹ (c⁻¹ * sh) (f 0)))
    = decide (ℓ.Mem u ∧ (reparam c⁻¹ (c⁻¹ * sh) (f 0)).eval (Line.param ℓ u) = α 0) from rfl]
  refine decide_eq_true ⟨⟨t' * c - sh, hmem⟩, ?_⟩
  by_cases hz : ∃ k, ℓ.2 k ≠ 0
  · have hzr : ∃ k, (c • revPoint ℓ.2) k ≠ 0 := by
      obtain ⟨k, hk⟩ := hz
      refine ⟨Fin.rev k, ?_⟩
      rw [Pi.smul_apply, revPoint_apply, Fin.rev_rev, smul_eq_mul]
      exact mul_ne_zero hc hk
    have hv : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
      by_contra hcon
      have h0 : (Sample.extend v : Point F m) = 0 :=
        funext fun k => not_not.mp fun hk => hcon ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hz
      rw [hℓdef, h0, Line.through, dif_neg (by simp)] at hk
      exact hk rfl
    have hparam : CL.lineParam u₀ (c • revPoint ℓ.2) (revPoint u) = t' := by
      rw [ht']
      exact lineParam_eq_of_mem hzr _ t'
    have hpt : Line.param ℓ u = t' * c - sh := by
      have := param_through_eq_of_mem hv u (t' * c - sh)
      rw [← hℓdef] at this
      rw [hmem]
      exact this
    have hkey : c⁻¹ * (t' * c - sh) + c⁻¹ * sh = t' := by
      have hc1 : c⁻¹ * (t' * c) = t' := by
        rw [mul_comm t' c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [mul_sub, hc1]
      ring
    rw [hpt, eval_reparam, hkey, ← hparam]
    exact heval
  · have h0 : (ℓ.2 : Point F m) = 0 := funext fun k => not_not.mp fun hcon => hz ⟨k, hcon⟩
    have hsh0 : sh = 0 := by
      rw [hsh, shiftOf, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk (by simp)
    have hpt : Line.param ℓ u = 0 := by
      rw [Line.param, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk rfl
    have hcl : CL.lineParam u₀ (c • revPoint ℓ.2) (revPoint u) = 0 := by
      rw [CL.lineParam, dif_neg]
      intro hcon
      obtain ⟨k, hk⟩ := hcon
      rw [h0] at hk
      exact hk (by simp)
    rw [hpt, eval_reparam, hsh0, mul_zero, add_zero, ← hcl]
    exact heval

/-! ### `hD`, assembled

The five cases above are exactly the five shapes a question pair of positive weight can have, so
this is the hypothesis `MIPRE.TensorProductStrategy.one_sub_value_adapt_le` asks for. Note it is
asked *only* on the support: off it the claim is false, since a pair of two line questions is a
real question pair of the seeded test and the canonical-line test has no subtest for it. -/

theorem hD_qmap (hc : c ≠ 0) (x' y' : Question F m) (hμ : (lidtGame F m d).μ x' y' ≠ 0)
    (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c x') (qmap hm σ c y') a b = true) :
    (lidtGame F m d).D x' y' (amap c x' a) (amap c y' b) = true := by
  obtain ⟨sm, hsm⟩ := exists_sample_of_μ_ne_zero hμ
  match sm, hsm with
  | Sample.selfConsistency u, hsm =>
      have hq : Sample.questions (Sample.selfConsistency u)
          = (Question.point u, Question.point (F := F) u) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_selfCons hm σ u a b hacc
  | Sample.axis false u i, hsm =>
      have hq : Sample.questions (Sample.axis false u i)
          = (Question.axisLine (Line.through u (Pi.single i 1)), Question.point u) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_axis hm σ u i a b hacc
  | Sample.axis true u i, hsm =>
      have hq : Sample.questions (Sample.axis true u i)
          = (Question.point u, Question.axisLine (Line.through u (Pi.single i 1))) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_axis' hm σ u i a b hacc
  | Sample.diag false u j v, hsm =>
      have hq : Sample.questions (Sample.diag false u j v)
          = (Question.diagLine (Line.through u (Sample.extend v)), Question.point u) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_diag hm σ hc u j v a b hacc
  | Sample.diag true u j v, hsm =>
      have hq : Sample.questions (Sample.diag true u j v)
          = (Question.point u, Question.diagLine (Line.through u (Sample.extend v))) := rfl
      rw [hq] at hsm
      injection hsm with h1 h2
      subst h1
      subst h2
      exact hD_diag' hm σ hc u j v a b hacc

end MIPRE.LIDT.Adapter
