/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryScanCorrect

/-! # Executable adaptive register masks from legal source queries -/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryScan
open Cost Cost.PolyTimeFun CLChecks

def unionMask : PolyTimeFun (BitStr × BitStr) BitStr :=
  (map (ite fst (const true) snd)).comp zip

theorem unionMask_correct {n : ℕ} (S T : Finset (Fin n)) :
    unionMask (CL.indicatorBits S, CL.indicatorBits T) = CL.indicatorBits (S ∪ T) := by
  change ((CL.indicatorBits S).zip (CL.indicatorBits T)).map
    (fun p => if p.1 then true else p.2) = _
  apply List.ext_getElem
  · simp [CL.indicatorBits]
  · intro i hi hj
    simp only [CL.indicatorBits, List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    simp only [Finset.mem_union]
    by_cases h : (⟨i, by simpa [CL.indicatorBits] using hj⟩ : Fin n) ∈ S <;> simp [h]

def factorAt (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ) : PolyTimeFun Input BitStr :=
  ite (fst.comp (program f m k))
    (f.comp ((nextContext k).comp ((PolyTimeFun.id _).pair (program f m k))))
    (zeros.comp snd)

def registers (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) : ℕ → PolyTimeFun Input BitStr
  | 0 => zeros.comp snd
  | k + 1 => unionMask.comp ((registers f m k).pair (factorAt f m k))

theorem factorAt_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (y : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j ≤ k, QueriesCorrectAt f m ctx P j)
    (ha : ∃ x, (P.truncate k).eval x = P.outputPrefix k y) :
    factorAt f m k (ctx, CL.toBits y) = CL.indicatorBits (P.factorOfPrefix k y) := by
  have hp := program_complete f m ctx hP y k (fun j hj => hq j (by omega)) ha
  obtain ⟨x, he, hx⟩ := program_sound f m ctx hP y k (fun j hj => hq j (by omega)) hp
  have hf := (hq k le_rfl _ ⟨x, hx⟩).1
  rw [factorOfPrefix_outputPrefix hP] at hf
  simp only [factorAt, PolyTimeFun.ite_apply, comp_apply, pair_apply, id_apply, he, fst_apply, if_true]
  exact hf

theorem registers_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (y : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j < k, QueriesCorrectAt f m ctx P j)
    (ha : ∃ x, (P.truncate (k - 1)).eval x = P.outputPrefix (k - 1) y) :
    registers f m k (ctx, CL.toBits y) = CL.indicatorBits (prefixRegister P k y) := by
  induction k with
  | zero =>
    change zeros (CL.toBits y) = CL.indicatorBits (prefixRegister P 0 y)
    rw [zeros_toBits]
    cases P <;> simp [CL.toBits, CL.indicatorBits, prefixRegister]
  | succ k ih =>
    have ha' : ∃ x, (P.truncate k).eval x = P.outputPrefix k y := by simpa using ha
    have he : ∃ x, (P.truncate (k - 1)).eval x = P.outputPrefix (k - 1) y := by
      obtain ⟨x, hx⟩ := ha'
      exact ⟨x, earlier_attained hP (by omega) y x hx⟩
    change unionMask (registers f m k (ctx, CL.toBits y), factorAt f m k (ctx, CL.toBits y)) = _
    rw [ih (fun j hj => hq j (by omega)) he,
      factorAt_correct f m ctx hP y k (fun j hj => hq j (by omega)) ha',
      unionMask_correct, prefixRegister_step]

end MIPRE.Introspection.AuxiliaryScan
end
