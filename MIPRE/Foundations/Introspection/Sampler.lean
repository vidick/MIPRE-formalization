/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SamplerProgram

/-! # The actual typed introspection sampler

An executable three-level Pauli sampler extends to the complete introspection
type set. Pauli presentations are retained, and every auxiliary type uses the
zero presentation with a full first factor. The program satisfies every query
clause and halts on arbitrary encoded inputs.
-/

noncomputable section

namespace MIPRE.Introspection

open Cost CL CL.Detyping CL.Detyping.Program SamplerProgram

private theorem pad_length (b : Bool) {l : BitStr} {s : ℕ} (h : l.length = s) :
    pad b l = List.replicate s b := by simp [pad, List.map_const', h]

private theorem indicatorBits_univ (s : ℕ) :
    indicatorBits (Finset.univ : Finset (Fin s)) = List.replicate s true := by
  simp [indicatorBits]

private theorem indicatorBits_empty (s : ℕ) :
    indicatorBits (∅ : Finset (Fin s)) = List.replicate s false := by
  simp [indicatorBits]

variable {P : Type*} [SizedEncoding P]

/-- The typed introspection sampler, constructed from the executable Pauli sampler. -/
def typedSampler (ℓ : ℕ) (S : TypedSampler 3 P) : TypedSampler 3 (QuestionType P ℓ) where
  prog := SamplerProgram.prog S
  closed := prog_closed S
  dim := S.dim
  cl n w := TypedPresentation.family (S.cl n w)
  cl_exactlyOn n w := TypedPresentation.family_exactlyOn _ (S.cl_exactlyOn n w)
  runs_dimension n := by
    obtain ⟨time, hr⟩ := S.runs_dimension n
    exact prog_run_call S _ _ _ time (route_dimension (P := QuestionType P ℓ) n) hr
  runs_marginal n w t j z hj hj' hz := by
    cases t with
    | inl p =>
      obtain ⟨time, hr⟩ := S.runs_marginal n w p j z hj hj' hz
      exact prog_run_call S _ _ _ time (route_pauli ℓ n p (.marginal w j z)) hr
    | inr t =>
      rcases t with ⟨t, role⟩
      rw [TypedPresentation.marginal_aux, toBits_zero]
      apply prog_run_direct S
      rw [route_aux]
      simp only [auxResult, Sampler.Query.toTuple, show ¬(1 : ℕ) = 2 by omega,
        show ¬(1 : ℕ) = 3 by omega, ↓reduceIte, pad_length false hz]
  runs_linear n w t j u y hj hj' hu hy := by
    cases t with
    | inl p =>
      obtain ⟨time, hr⟩ := S.runs_linear n w p j u y hj hj' hu hy
      exact prog_run_call S _ _ _ time (route_pauli ℓ n p (.linear w j u y)) hr
    | inr t =>
      rcases t with ⟨t, role⟩
      rw [TypedPresentation.linear_aux]
      simp only [LinearMap.zero_apply, toBits_zero]
      apply prog_run_direct S
      rw [route_aux]
      simp only [auxResult, Sampler.Query.toTuple, ↓reduceIte, pad_length false hy]
  runs_factor n w t j u hj hj' hu := by
    have huLen : u.length = S.dim n := by
      obtain ⟨x, rfl⟩ := hu
      exact length_toBits _
    cases t with
    | inl p =>
      obtain ⟨time, hr⟩ := S.runs_factor n w p j u hj hj' hu
      exact prog_run_call S _ _ _ time (route_pauli ℓ n p (.factor w j u)) hr
    | inr t =>
      rcases t with ⟨t, role⟩
      rw [TypedPresentation.factor_aux]
      by_cases hj1 : j = 1
      · have hz : j - 1 = 0 := by omega
        simp only [hz, ↓reduceIte, indicatorBits_univ]
        apply prog_run_direct S
        rw [route_aux]
        simp only [auxResult, Sampler.Query.toTuple, show ¬(3 : ℕ) = 2 by omega,
          ↓reduceIte, hj1, decide_true, pad_length true huLen]
      · have hz : j - 1 ≠ 0 := by omega
        simp only [hz, ↓reduceIte, indicatorBits_empty]
        apply prog_run_direct S
        rw [route_aux]
        simp only [auxResult, Sampler.Query.toTuple, show ¬(3 : ℕ) = 2 by omega,
          ↓reduceIte, hj1, decide_false, pad_length false huLen]
  halts := prog_halts S

theorem typedSampler_dim (ℓ : ℕ) (S : TypedSampler 3 P) (n : ℕ) :
    (typedSampler ℓ S).dim n = S.dim n := rfl

theorem typedSampler_cl (ℓ : ℕ) (S : TypedSampler 3 P) (n : ℕ) (w : Player) :
    (typedSampler ℓ S).cl n w = TypedPresentation.family (S.cl n w) := rfl

/-- The executable extension does not depend on the number of hiding types. -/
theorem typedSampler_prog_independent (ℓ ℓ' : ℕ) (S : TypedSampler 3 P) :
    (typedSampler ℓ S).prog = (typedSampler ℓ' S).prog := rfl

section Detyped

variable [Fintype P] [DecidableEq P]

/-- The executable five-level introspection sampler after graph detyping. -/
def detypedSampler (E : P → P → Bool) (X Z : P) (ℓ : ℕ) (S : TypedSampler 3 P) : CL.Sampler 5 :=
  Detyping.sampler (TypeGraph.Adj E X Z) (typedSampler ℓ S) (by decide)

theorem detypedSampler_dim (E : P → P → Bool) (X Z : P) (ℓ : ℕ) (S : TypedSampler 3 P) (n : ℕ) :
    (detypedSampler E X Z ℓ S).dim n = 4 * (Fintype.card P + 2 * ℓ + 6) + S.dim n := by
  rw [detypedSampler, Detyping.sampler_dim, QuestionType.card, typedSampler_dim]

/-- The final sampler's presentations are exactly the detyped typed family. -/
theorem detypedSampler_cl (E : P → P → Bool) (X Z : P) (ℓ : ℕ) (S : TypedSampler 3 P)
    (n : ℕ) (w : Player) :
    (detypedSampler E X Z ℓ S).cl n w =
      Detyping.numbered (TypeGraph.Adj E X Z) w
        (TypedPresentation.family (ℓ := ℓ) (S.cl n w)) := rfl

end Detyped

end MIPRE.Introspection
