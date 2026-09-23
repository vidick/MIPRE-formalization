/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryQuotientProgram
import MIPRE.Foundations.Introspection.AuxiliaryQuotientChecks
import MIPRE.Foundations.Introspection.AuxiliaryScanCorrect
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram

/-! # Executable boundary edges of the hiding chain

The first edge compares the initial dual quotient and untouched tail. The
last edge scans both reported prefixes, then compares those prefixes and the
full dual answers. Query functions are parameters so the same programs use
the proved padded-source interface.
-/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryBoundary
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear AuxiliaryProgram CLChecks

abbrev FirstInput := AuxiliarySource.Context × BitStr × (BitStr × BitStr × BitStr)

def firstContext : PolyTimeFun FirstInput AuxiliarySource.Context :=
  let ctx := fst
  let zero := AuxiliaryScan.zeros.comp (fst.comp snd)
  (AuxiliarySource.budget.comp ctx).pair ((AuxiliarySource.source.comp ctx).pair
    ((AuxiliarySource.index.comp ctx).pair ((AuxiliarySource.player.comp ctx).pair
      ((const 1).pair zero))))

theorem firstContext_apply (ctx : AuxiliarySource.Context) (x a b c : BitStr) :
    firstContext (ctx, x, a, b, c) =
      AuxiliaryScan.contextAt ctx 1 (AuxiliaryScan.zeros x) := rfl

def first (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) : PolyTimeFun FirstInput Bool :=
  let mask := f.comp firstContext
  let mat := m.comp firstContext
  let x := fst.comp snd
  let dual := fst.comp (snd.comp (snd.comp snd))
  let tail := snd.comp (snd.comp (snd.comp snd))
  let comparison := AuxiliaryBits.quotient.comp (mask.pair (mat.pair (dual.pair x)))
  let keep := AuxiliaryBits.complement.comp mask
  andCheck comparison (equal (AuxiliaryBits.mask.comp (keep.pair x))
    (AuxiliaryBits.mask.comp (keep.pair tail)))

theorem first_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin n) ℓ)
    (x a b c : Fin n → CL.𝔽₂)
    (hf : f (AuxiliaryScan.contextAt ctx 1 (CL.toBits (0 : Fin n → CL.𝔽₂))) =
      CL.indicatorBits (P.factorOfPrefix 0 0))
    (hm : m (AuxiliaryScan.contextAt ctx 1 (CL.toBits (0 : Fin n → CL.𝔽₂))) =
      matrixBits (LinearMap.toMatrix' (P.mapOfPrefix 0 0))) :
    first f m (ctx, CL.toBits x, CL.toBits a, CL.toBits b, CL.toBits c) = true ↔
      AuxiliaryQuotient.hidingPauli P x (a, b, c) := by
  simp only [first, andCheck_iff, equal_iff, comp_apply, pair_apply, fst_apply, snd_apply,
    firstContext_apply, AuxiliaryScan.zeros_toBits, hf, hm,
    AuxiliaryBits.complement_correct, AuxiliaryBits.mask_correct,
    toBits_injective.eq_iff]
  rw [← stageLinear_toLinearMap P 0 0, AuxiliaryBits.quotient_correct]
  rfl

theorem first_correct_of_queries (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin n) ℓ)
    (x a b c : Fin n → CL.𝔽₂) (hq : AuxiliaryScan.QueriesCorrectAt f m ctx P 0) :
    first f m (ctx, CL.toBits x, CL.toBits a, CL.toBits b, CL.toBits c) = true ↔
      AuxiliaryQuotient.hidingPauli P x (a, b, c) := by
  obtain ⟨hf, hm⟩ := hq 0 ⟨0, by simp⟩
  exact first_correct f m ctx P x a b c hf hm

abbrev LastInput := AuxiliarySource.Context × (BitStr × BitStr × BitStr) × (BitStr × BitStr)

def leftScan (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ℓ : ℕ) :
    PolyTimeFun LastInput AuxiliaryScan.State :=
  (AuxiliaryScan.program f m (ℓ - 1)).comp (fst.pair (fst.comp (fst.comp snd)))

def rightScan (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ℓ : ℕ) :
    PolyTimeFun LastInput AuxiliaryScan.State :=
  (AuxiliaryScan.program f m (ℓ - 1)).comp (fst.pair (fst.comp (snd.comp snd)))

def last (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ℓ : ℕ) :
    PolyTimeFun LastInput Bool :=
  let a := leftScan f m ℓ
  let b := rightScan f m ℓ
  andCheck (fst.comp a) (andCheck (fst.comp b)
    (andCheck (equal (fst.comp (snd.comp a)) (fst.comp (snd.comp b)))
      (equal (fst.comp (snd.comp (fst.comp snd))) (snd.comp (snd.comp snd)))))

theorem last_apply_iff (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ℓ : ℕ)
    (ctx : AuxiliarySource.Context) (a b c v d : BitStr) :
    last f m ℓ (ctx, (a, b, c), (v, d)) = true ↔
      (AuxiliaryScan.program f m (ℓ - 1) (ctx, a)).1 = true ∧
      (AuxiliaryScan.program f m (ℓ - 1) (ctx, v)).1 = true ∧
      (AuxiliaryScan.program f m (ℓ - 1) (ctx, a)).2.1 =
        (AuxiliaryScan.program f m (ℓ - 1) (ctx, v)).2.1 ∧ b = d := by
  simp only [last, andCheck_iff, equal_iff, comp_apply, leftScan, rightScan,
    pair_apply, fst_apply, snd_apply]

theorem last_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (a b c v d : Fin n → CL.𝔽₂)
    (hq : ∀ j < ℓ - 1, AuxiliaryScan.QueriesCorrectAt f m ctx P j) :
    last f m ℓ (ctx, (CL.toBits a, CL.toBits b, CL.toBits c), (CL.toBits v, CL.toBits d)) = true ↔
      (∃ x, (P.truncate (ℓ - 1)).eval x = P.outputPrefix (ℓ - 1) a) ∧
      (∃ x, (P.truncate (ℓ - 1)).eval x = P.outputPrefix (ℓ - 1) v) ∧
      CLChecks.hidingRead P (a, b, c) (v, d, ()) := by
  rw [last_apply_iff]
  constructor
  · rintro ⟨ha, hv, he, hd⟩
    obtain ⟨x, hx, hxa⟩ := AuxiliaryScan.program_sound f m ctx hP a (ℓ - 1) hq ha
    obtain ⟨y, hy, hyv⟩ := AuxiliaryScan.program_sound f m ctx hP v (ℓ - 1) hq hv
    rw [hx, hy] at he
    exact ⟨⟨x, hxa⟩, ⟨y, hyv⟩, toBits_injective he, toBits_injective hd⟩
  · rintro ⟨hxa, hyv, he, hd⟩
    have ha := AuxiliaryScan.program_complete f m ctx hP a (ℓ - 1) hq hxa
    have hv := AuxiliaryScan.program_complete f m ctx hP v (ℓ - 1) hq hyv
    obtain ⟨x, hx, _⟩ := AuxiliaryScan.program_sound f m ctx hP a (ℓ - 1) hq ha
    obtain ⟨y, hy, _⟩ := AuxiliaryScan.program_sound f m ctx hP v (ℓ - 1) hq hv
    refine ⟨ha, hv, ?_, congrArg CL.toBits hd⟩
    rw [hx, hy]
    exact congrArg CL.toBits he

end MIPRE.Introspection.AuxiliaryBoundary
end
