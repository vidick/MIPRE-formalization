/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.QLD.PauliBooleanCorrect
public import MIPRE.Background.QLD.PauliBooleanSymmetry

@[expose] public section

/-! # Exact decision equality for every pair of Pauli types

The arithmetic branches are proved individually. The fixed finite type router
then selects a forward branch, its proved reversal, exact consistency, or the
legacy off-graph default. Question contents remain arbitrary throughout.
-/

noncomputable section
namespace MIPRE.QLD.PauliBooleanProgram
open Cost SAT PauliCL LowDegree LIDT LCS.MagicSquare

set_option maxHeartbeats 60000 in
theorem pairTest_unhandled {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m] (hm : m ∣ Fintype.card F)
    (x y : Question F m) (a b : Answer F m d) (h : handled x.ty y.ty = false) :
    pairTest hm x y a b = true := by
  fun_cases pairTest hm x y a b <;> simp_all [Question.ty, handled]

set_option maxHeartbeats 60000 in
set_option backward.isDefEq.respectTransparency false in
theorem program_correct_forward (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (T U : Ty)
    (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier)
    (a b : Answer (shoupBinField k hk).carrier (2 ^ j) 1)
    (ha : (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y).fmtOk b = true)
    (hf : Forward T U) (reverse : Bool) :
    program (encodedInput (shoupBinField k hk) j T U x y a b) =
      (if reverse then
        accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y)
          (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x) b a
      else accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x)
        (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y) a b) := by
  rcases hf with ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ |
    ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨i, v, rfl, rfl⟩ | ⟨W, v, rfl, rfl⟩
  · obtain ⟨a, rfl⟩ := eq_val_of_fmtOk ha
    obtain ⟨f, rfl⟩ := eq_apoly_of_fmtOk hb
    rw [program_axis k hk j hj hm W x y a f]
    cases reverse <;> cases W <;> simp [accepts, subtests, ExplicitSeed.decode, Question.ty, Question.fmtOk,
      pairTest, ExplicitSeed.contentPermutation, vectorContent, Content.pt]
  · obtain ⟨a, rfl⟩ := eq_val_of_fmtOk ha
    obtain ⟨f, rfl⟩ := eq_dpoly_of_fmtOk hb
    rw [program_diagonal k hk j (2 ^ j) W x y a f]
    cases reverse <;> cases W <;> simp [accepts, subtests, ExplicitSeed.decode, Question.ty, Question.fmtOk,
      pairTest, ExplicitSeed.contentPermutation, vectorContent, Content.pt]
  · obtain ⟨a, rfl⟩ := eq_val_of_fmtOk ha
    obtain ⟨h, rfl⟩ := eq_pauliAns_of_fmtOk hb
    rw [program_table k hk j (2 ^ j) W x y a h]
    cases reverse <;> cases W <;> simp [accepts, subtests, ExplicitSeed.decode, Question.ty, Question.fmtOk,
      pairTest, ExplicitSeed.contentPermutation, vectorContent, Content.pt]
  · obtain ⟨a, rfl⟩ := eq_bit_of_fmtOk_pairB ha
    obtain ⟨b, rfl⟩ := eq_bitPair_of_fmtOk hb
    rw [program_pair k hk j (2 ^ j) W x y a b]
    cases reverse <;> simp [accepts, subtests, ExplicitSeed.decode, Question.ty, Question.fmtOk,
      pairTest, ExplicitSeed.contentPermutation, vectorContent, Content.omega, decide_not]
  · obtain ⟨a, rfl⟩ := eq_val_of_fmtOk ha
    obtain ⟨b, rfl⟩ := eq_bit_of_fmtOk_pairB hb
    rw [program_probe k hk j (2 ^ j) W x y a b]
    cases reverse <;> cases W <;> simp [accepts, subtests, ExplicitSeed.decode, Question.ty, Question.fmtOk,
      pairTest, ExplicitSeed.contentPermutation, vectorContent, Content.pt, Content.omega, Omega.r,
      decide_not]
  · obtain ⟨a, rfl⟩ := eq_bitTriple_of_fmtOk ha
    obtain ⟨b, rfl⟩ := eq_bit_of_fmtOk_var hb
    rw [program_magic k hk j (2 ^ j) i v x y a b]
    cases reverse <;> simp [accepts, subtests, ExplicitSeed.decode, Question.ty, Question.fmtOk,
      pairTest, ExplicitSeed.contentPermutation, vectorContent, Content.omega]
  · obtain ⟨a, rfl⟩ := eq_val_of_fmtOk ha
    obtain ⟨b, rfl⟩ := eq_bit_of_fmtOk_var hb
    rw [program_magicProbe k hk j (2 ^ j) W v x y a b]
    cases reverse <;> cases W <;> simp [accepts, subtests, ExplicitSeed.decode, Question.ty, Question.fmtOk,
      pairTest, ExplicitSeed.contentPermutation, vectorContent, Content.pt, Content.omega,
      probeEligible]

/-- The executable Pauli predicate agrees with the transported QLD interface
on all raw question contents and all canonically encoded formatted answers. -/
theorem program_correct_formatted (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (T U : Ty)
    (x y : Coord (2 ^ j) → (shoupBinField k hk).carrier)
    (a b : Answer (shoupBinField k hk).carrier (2 ^ j) 1)
    (ha : (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x).fmtOk a = true)
    (hb : (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y).fmtOk b = true) :
    program (encodedInput (shoupBinField k hk) j T U x y a b) =
      accepts hm (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) T x)
        (ExplicitSeed.decode (ExplicitSeed.seedPermutation (shoupBinField k hk)) U y) a b := by
  by_cases hTU : T = U
  · subst U
    rw [program_same_type (shoupBinField k hk) hk j _ T x y a b ha hb]
    simp only [accepts, ha, hb, Bool.true_and, subtests, explicitDecode_ty, ↓reduceIte]
  have h0 : 0 < (PauliBranchProgram.route T U).1 := by
    have hn := (PauliBranchProgram.consistency_iff T U).not.mpr hTU
    omega
  by_cases h8 : (PauliBranchProgram.route T U).1 = 8
  · rw [program_of_formatted (shoupBinField k hk) hk j _ T U x y a b ha hb, h8]
    simp only [List.getD_cons_succ, List.getD_nil, accepts, ha, hb, Bool.true_and,
      subtests, explicitDecode_ty, if_neg hTU]
    symm
    apply pairTest_unhandled
    simpa only [explicitDecode_ty] using route_default_unhandled T U h8
  have hlt : (PauliBranchProgram.route T U).1 < 8 := by
    have hbnd := PauliBranchProgram.route_lt_nine T U
    omega
  rcases forward_or_reverse T U h0 hlt with hf | hf
  · exact program_correct_forward k hk j hj hm T U x y a b ha hb hf false
  · have hs := program_swap_handled
      (encodedInput (shoupBinField k hk) j T U x y a b) h0 hlt
    rw [← hs]
    exact program_correct_forward k hk j hj hm U T y x b a hb ha hf true

end MIPRE.QLD.PauliBooleanProgram
end

end
