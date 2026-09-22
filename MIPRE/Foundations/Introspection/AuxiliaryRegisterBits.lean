/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram
import MIPRE.Foundations.Introspection.SourcePadding

/-! # Exact binary projection for the full-register auxiliary checks -/

noncomputable section
namespace MIPRE.Introspection.AuxiliaryProgram
open Cost

def firstEmbedding {s Q : ℕ} (h : s ≤ Q) : Fin s ↪ Fin Q :=
  ⟨Fin.castLE h, fun _ _ he => Fin.ext (congrArg (fun i : Fin Q => i.val) he)⟩

theorem ofBits_take_first {s Q : ℕ} (h : s ≤ Q) (z : Fin Q → CL.𝔽₂) :
    CL.ofBits s ((CL.toBits z).take s) = CL.pull (firstEmbedding h) z := by
  funext i
  rw [CL.Detyping.ofBits_take_eq]
  have hi : (i : ℕ) < Q := lt_of_lt_of_le i.isLt h
  change (if (CL.toBits z).getD i false then (1 : CL.𝔽₂) else 0) = z (firstEmbedding h i)
  have he : (CL.toBits z).getD i false = decide (z (firstEmbedding h i) = 1) := by
    simp only [CL.toBits,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_true,Option.getD_some]
    rfl
  rw [he]
  generalize z (firstEmbedding h i) = a
  revert a
  decide

theorem toBits_push_first {s Q : ℕ} (h : s ≤ Q) (x : Fin s → CL.𝔽₂) :
    CL.toBits (CL.push (firstEmbedding h) x) = CL.toBits x ++ List.replicate (Q-s) false := by
  classical
  apply List.ext_getElem
  · simp only [CL.length_toBits,List.length_append,List.length_replicate]
    omega
  · intro i hi hi'
    by_cases hs : i < s
    · have he : (⟨i,by simpa using hi⟩ : Fin Q) = firstEmbedding h ⟨i,hs⟩ := rfl
      simp only [CL.toBits,List.getElem_ofFn,he,CL.push_apply]
      rw [List.getElem_append_left (by simpa using hs)]
      simp only [List.getElem_ofFn]
    · have hq : i < Q := by simpa using hi
      have hn : ¬ ∃ j, firstEmbedding h j = (⟨i,hq⟩ : Fin Q) := by
        rintro ⟨j,hj⟩
        have hjv := congrArg Fin.val hj
        change j.val = i at hjv
        exact hs (hjv ▸ j.isLt)
      simp only [CL.toBits,List.getElem_ofFn,CL.push,dif_neg hn]
      rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hs)]
      simp

/-- A full-register output equals a zero-extended source output exactly when
its suffix is zero and its retained prefix agrees. -/
theorem source_bits_iff {s Q : ℕ} (h : s ≤ Q) (y : Fin Q → CL.𝔽₂) (x : Fin s → CL.𝔽₂) :
    SourceCompiler.InSource s (CL.toBits y) ∧ (CL.toBits y).take s = CL.toBits x ↔
      y = CL.push (firstEmbedding h) x := by
  constructor
  · rintro ⟨hs,he⟩
    apply toBits_injective
    rw [toBits_push_first,SourceCompiler.InSource_padding (CL.length_toBits y) hs,he]
  · intro he
    subst y
    rw [toBits_push_first]
    simp [SourceCompiler.InSource,CL.length_toBits]

end MIPRE.Introspection.AuxiliaryProgram
end
