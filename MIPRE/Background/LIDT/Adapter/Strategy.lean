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
reversed direction, which is the pivot of its span and so the coordinate `rep` zeroes. -/
noncomputable def diagIdx (ℓ : Line F m) : Fin m :=
  if h : ∃ j, (revPoint ℓ.2) j ≠ 0 then Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h else idx0

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

/-- The seeded question a canonical-line question is played through, for the seed choice `σ`. -/
noncomputable def qmap (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) :
    Question F m → CL.Question F m
  | .point u => .point (revPoint u)
  | .axisLine ℓ =>
      .aline (revPoint ℓ.1) (seedOf hm (Fin.rev (axisIdx ℓ)) (σ (Fin.rev (axisIdx ℓ))))
  | .diagLine ℓ =>
      .dline (revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2)
        (seedOf hm (diagIdx ℓ) (σ (diagIdx ℓ))) (revPoint ℓ.2)

/-- The canonical-line answer a seeded answer becomes. It depends on the question because the
shift does; the branches not listed are the ones `clGame` rejects on format. -/
noncomputable def amap : Question F m → CL.Answer F m d 1 → Answer F m d
  | .point _, .values a => .value (a 0)
  | .axisLine _, .apolys f => .axisPoly (f 0)
  | .diagLine ℓ, .dpolys f => .diagPoly (reparam 1 (shiftOf ℓ) (f 0))
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

end MIPRE.LIDT.Adapter
