/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.Sampler

/-! # Runtime transfer for the actual introspection sampler

The auxiliary extension makes at most one Pauli-sampler call. Its explicit
polynomial majorant has a degree independent of the input index and the number
of hiding types. Composing this bound with the actual detyping compiler gives
a polynomial query bound for the final five-level sampler.
-/

noncomputable section

namespace MIPRE.Introspection

open Cost CL Polynomial

def typedSamplerCost (n B k : ℕ) : Polynomial ℕ :=
  (Prog.routeCost SamplerProgram.route SamplerProgram.post B k).comp
    (X + C (esize n + 1))

def typedSamplerDegree (k : ℕ) : ℕ :=
  Prog.routeDegree SamplerProgram.route SamplerProgram.post k

theorem typedSamplerCost_natDegree_le (n B k : ℕ) :
    (typedSamplerCost n B k).natDegree ≤ typedSamplerDegree k := by
  have hi : (X + C (esize n + 1) : Polynomial ℕ).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp only [natDegree_X]; omega)
      (by simp only [natDegree_C]; omega)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul
    (Prog.routeCost_natDegree_le _ _ B k) hi).trans (by simp [typedSamplerDegree]))

def typedSamplerCoefficient (n B k : ℕ) : ℕ :=
  let Q := typedSamplerCost n B k
  ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i

variable {P : Type*} [SizedEncoding P]

theorem typedSampler_haltsWithin (ℓ : ℕ) (S : TypedSampler 3 P) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) (q : Data) :
    HaltsWithin (typedSampler ℓ S).prog (.cons (encode n) q)
      ((typedSamplerCost n B k).eval q.size) := by
  have hr := Prog.routeOneCall_haltsWithin SamplerProgram.route S.closed
    SamplerProgram.post n B k q h (SamplerProgram.route_preserves n q)
  simpa only [typedSampler, SamplerProgram.prog, typedSamplerCost,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Data.size_cons, esize, encode_data, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr

/-- Typed introspection preserves polynomial query time with a common exponent. -/
theorem typedSampler_timeBoundAt (ℓ : ℕ) (S : TypedSampler 3 P) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) :
    (typedSampler ℓ S).TimeBoundAt n (typedSamplerCoefficient n B k) (typedSamplerDegree k) := by
  let Q := typedSamplerCost n B k
  have hQ : (typedSampler ℓ S).TimeBoundAt n (typedSamplerCoefficient n B k) Q.natDegree := by
    intro q
    obtain ⟨r, time, ht, hr⟩ := typedSampler_haltsWithin ℓ S n B k h q
    exact ⟨r, time, ht.trans ((polynomial_eval_mono Q (Nat.le_succ q.size)).trans
      (polynomial_eval_le_sum_coeff_mul_pow Q (by omega))), hr⟩
  exact hQ.mono le_rfl (typedSamplerCost_natDegree_le n B k)

theorem typedSampler_timeBound (ℓ : ℕ) (S : TypedSampler 3 P) (B : ℕ → ℕ) (k : ℕ)
    (h : ∀ n, S.TimeBoundAt n (B n) k) :
    ∀ n, (typedSampler ℓ S).TimeBoundAt n (typedSamplerCoefficient n (B n) k)
      (typedSamplerDegree k) := fun n => typedSampler_timeBoundAt ℓ S n (B n) k (h n)

section Detyped

variable [Fintype P] [DecidableEq P]

/-- The executable five-level sampler inherits a global polynomial query bound. -/
theorem detypedSampler_timeBound (E : P → P → Bool) (X Z : P) (ℓ : ℕ)
    (S : TypedSampler 3 P) (B : ℕ → ℕ) (k : ℕ)
    (h : ∀ n, S.TimeBoundAt n (B n) k) :
    ∃ B' k', (detypedSampler E X Z ℓ S).TimeBound B' k' := by
  let G := TypeGraph.Adj (ℓ := ℓ) E X Z
  refine ⟨fun n => Detyping.samplerCoefficient G n (typedSamplerCoefficient n (B n) k)
      (typedSamplerDegree k), Detyping.samplerDegree G (typedSamplerDegree k), ?_⟩
  exact Detyping.sampler_timeBound G (typedSampler ℓ S) (by decide)
    (fun n => typedSamplerCoefficient n (B n) k) (typedSamplerDegree k)
    (typedSampler_timeBound ℓ S B k h)

end Detyped
end MIPRE.Introspection
