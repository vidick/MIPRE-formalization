/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.TypedPresentation
import MIPRE.Foundations.Introspection.TypedPredicate
import MIPRE.Foundations.Introspection.HidingTests

/-! # Auxiliary estimates for the concrete typed introspection game

The uniform ordered-edge law supplies the selection probability. The parsed
sampling predicate supplies the accepted-answer relation, including malformed
constructors, so its estimate has no abstract subtest or probability premise.
The Pauli predicate is passed the actual question contents; constructing that
predicate, and compiling the byte parser, remain separate obligations.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical

variable {PauliType PauliAnswer F ι κ A B C H K : Type*}
  [Fintype PauliType] [DecidableEq PauliType]
  [Fintype κ] [DecidableEq κ] [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] {ℓ : ℕ}

/-- On any auxiliary edge, the coarsened cross-party distance costs exactly twice
the ordered-edge count times the game's failure. -/
theorem aux_agreement_estimate (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      CL.Detyping.Question (QuestionType PauliType ℓ) κ → A → B → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM A H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ → POVM B K)
    {ε : ℝ} (hfail : 1 - povmValue (TypedPresentation.game E X Z ℓ P D) ψ MA MB ≤ ε)
    (t u : AuxType ℓ) (w w' : Bool)
    (hedge : TypeGraph.Adj E X Z (.inr (t, w)) (.inr (u, w')))
    (f : A → C) (g : B → C)
    (hcheck : ∀ a b, D (.inr (t, w), 0) (.inr (u, w'), 0) a b = true → f a = g b) :
    (∑ z, xSqNorm ψ ((((MA (.inr (t, w), 0)).map f).mats z).val)
      ((((MB (.inr (u, w'), 0)).map g).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  let G := TypedPresentation.game E X Z ℓ P D
  let x : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (.inr (t, w), 0)
  let y : CL.Detyping.Question (QuestionType PauliType ℓ) κ := (.inr (u, w'), 0)
  have hterm := sum_mul_condFail_le (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    hψ hfail {(x, y)}
  simp only [sum_singleton] at hterm
  change (TypedPresentation.game E X Z ℓ P D).μ (.inr (t, w), 0) (.inr (u, w'), 0) *
    condFail G ψ MA MB x y ≤ ε at hterm
  rw [TypedPresentation.mu_aux E X Z P D t u w w' hedge, inv_mul_eq_div] at hterm
  have hc : (0 : ℝ) < (TypeGraph.edges E X Z ℓ).card := by
    exact_mod_cast (TypeGraph.edges_nonempty E X Z ℓ).card_pos
  have hcond := (div_le_iff₀ hc).mp hterm
  have hdist := xSqNorm_sum_le_condFail (G := G) (ψ := ψ) (MA := MA) (MB := MB)
    (x := x) (y := y) hψ f g hcheck
  change _ ≤ 2 * (TypeGraph.edges E X Z ℓ).card * ε
  calc _ ≤ 2 * condFail G ψ MA MB x y := hdist
    _ ≤ 2 * (ε * (TypeGraph.edges E X Z ℓ).card) :=
      mul_le_mul_of_nonneg_left hcond (by norm_num)
    _ = _ := by ring

section Parsed

variable [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
  [Fintype PauliAnswer]

/-- Lift the parsed checks to actual typed questions. Only the Pauli test reads
their contents; the auxiliary tests depend on the type labels and answers. -/
def questionCheck (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (q r : CL.Detyping.Question (QuestionType PauliType ℓ) κ) :
    ParsedAnswer (ι → F) A PauliAnswer → ParsedAnswer (ι → F) A PauliAnswer → Bool :=
  TypedPredicate.check L X Z projectPauli D (fun p s => DP p s q.2 r.2) q.1 r.1

/-- The concrete typed game with the parsed introspection decision predicate. -/
def parsedGame (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool) :=
  TypedPresentation.game E X Z ℓ P (questionCheck L X Z projectPauli D DP)

/-- Coarsen an introspection answer, retaining a distinct outcome for malformed answers. -/
def introspectPrefix (L : CL.CLFun F ι ℓ) (k : ℕ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .pair y a => some (L.outputPrefix k y, a)
  | _ => none

/-- Coarsen a sampling answer by evaluating the original CL prefix on its sampled seed. -/
def samplePrefix (L : CL.CLFun F ι ℓ) (k : ℕ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × A)
  | .pair z a => some ((L.truncate k).eval z, a)
  | _ => none

/-- Every prefix of the actual parsed sampling test has cross-party error at most
`2 |E| ε`, summed over the complete alphabet, including the malformed-answer outcome. -/
theorem sampling_prefix_estimate (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
    {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)
    (w : Bool) (hL : (L w).SupportedOn univ) (k : ℕ) :
    (∑ z, xSqNorm ψ
      ((((MA (QuestionType.introspect w, 0)).map (introspectPrefix (L w) k)).mats z).val)
      ((((MB (QuestionType.sample w, 0)).map (samplePrefix (L w) k)).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  apply aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP) ψ hψ MA MB
    hfail .introspect .sample w w
    (TypeGraph.symmetric E X Z _ _ (TypeGraph.adj_sample_introspect E X Z w))
  intro a b h
  have hf := TypedPredicate.check_formats L X Z projectPauli D
    (fun p s => DP p s 0 0) h
  cases a with
  | pauli a => simp [TypedPredicate.fits] at hf
  | read y yp a => simp [TypedPredicate.fits] at hf
  | hide y yp x => simp [TypedPredicate.fits] at hf
  | pair y a =>
    cases b with
    | pauli b => simp [TypedPredicate.fits] at hf
    | read z zp b => simp [TypedPredicate.fits] at hf
    | hide z zp x => simp [TypedPredicate.fits] at hf
    | pair z b =>
      exact congrArg some (TypedPredicate.check_sampling_prefix L X Z projectPauli D
        (fun p s => DP p s 0 0) w hL h k)

/-- The last hiding answer, retaining exactly the data tested against Read. -/
def hidingReadout (L : CL.CLFun F ι ℓ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × (ι → F))
  | .hide y yp _ => some (L.outputPrefix (ℓ - 1) y, yp)
  | _ => none

/-- The same tested data from a Read answer. -/
def readingReadout (L : CL.CLFun F ι ℓ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × (ι → F))
  | .read y yp _ => some (L.outputPrefix (ℓ - 1) y, yp)
  | _ => none

variable (E : PauliType → PauliType → Bool) (X Z : PauliType)
  (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
  (projectPauli : PauliAnswer → ι → F)
  (D : (ι → F) → (ι → F) → A → A → Bool)
  (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
    PauliAnswer → PauliAnswer → Bool)
  (ψ : H × K → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
  (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) H)
  (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
    POVM (ParsedAnswer (ι → F) A PauliAnswer) K)
  {ε : ℝ} (hfail : 1 - povmValue (parsedGame E X Z P L projectPauli D DP) ψ MA MB ≤ ε)

include hψ hfail

/-- The concrete last-hiding/Read test bounds the tested coarse measurements,
without a separate accepted-answer or selection-probability assumption. -/
theorem hiding_read_estimate (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ) :
    (∑ z, xSqNorm ψ
      ((((MA (QuestionType.hide w k, 0)).map (hidingReadout (L w))).mats z).val)
      ((((MB (QuestionType.read w, 0)).map (readingReadout (L w))).mats z).val)) ≤
        2 * (TypeGraph.edges E X Z ℓ).card * ε := by
  apply aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP) ψ hψ MA MB
    hfail (.hide k) .read w w (TypeGraph.adj_hide_read E X Z w k hk)
  intro a b h
  have hf := TypedPredicate.check_formats L X Z projectPauli D
    (fun p s => DP p s 0 0) h
  cases a with
  | pauli a => simp [TypedPredicate.fits] at hf
  | pair y a => simp [TypedPredicate.fits] at hf
  | read y yp a => simp [TypedPredicate.fits] at hf
  | hide y yp x =>
    cases b with
    | pauli b => simp [TypedPredicate.fits] at hf
    | pair z b => simp [TypedPredicate.fits] at hf
    | hide z zp t => simp [TypedPredicate.fits] at hf
    | read z zp b =>
      have hc := TypedPredicate.check_hiding_read L X Z projectPauli D
        (fun p s => DP p s 0 0) w k hk h
      exact congrArg some (Prod.ext hc.1 hc.2)

/-- The terminal hiding test and Read consistency loop give a same-party estimate
with loss `8 |E| ε`, after coarse-graining the actual accepted-answer relations. -/
theorem hiding_read_same_side_estimate (w : Bool) (k : Fin ℓ) (hk : k.val + 1 = ℓ) :
    (∑ z, stateSqNorm ψ
      (((((MA (QuestionType.hide w k, 0)).map (hidingReadout (L w))).mats z).val) -
        ((((MA (QuestionType.read w, 0)).map (readingReadout (L w))).mats z).val))) ≤
          8 * (TypeGraph.edges E X Z ℓ).card * ε := by
  have h₁ := hiding_read_estimate E X Z P L projectPauli D DP ψ hψ MA MB hfail w k hk
  have h₂ := aux_agreement_estimate E X Z P (questionCheck L X Z projectPauli D DP)
    ψ hψ MA MB hfail .read .read w w (TypeGraph.adj_self E X Z (.inr (.read, w)))
    (readingReadout (L w)) (readingReadout (L w)) (fun a b hab =>
      congrArg (readingReadout (L w))
        (TypedPredicate.check_consistency L X Z projectPauli D (fun p s => DP p s 0 0) hab))
  have htriangle := same_side_via_common_other ψ
    (fun z => ((((MA (QuestionType.hide w k, 0)).map (hidingReadout (L w))).mats z).val))
    (fun z => ((((MA (QuestionType.read w, 0)).map (readingReadout (L w))).mats z).val))
    (fun z => ((((MB (QuestionType.read w, 0)).map (readingReadout (L w))).mats z).val))
  linarith only [htriangle, h₁, h₂]

end Parsed
end MIPRE.Introspection.TypedEstimates

end
