/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.PauliSamplerCost
import MIPRE.Foundations.Introspection.SamplerCost

/-! # The executable five-level introspection sampler

The canonical Pauli sampler extends to all introspection types and is then
detyped along the actual type graph. The program is uniformly compiled from
the binary boundedness parameter. Its positive-index budget includes both
routers and the graph register; the final verifier handles zero separately.
-/

noncomputable section
namespace MIPRE.Introspection.PauliSampler
open Cost Cost.Prog Cost.PolyTimeFun CL Polynomial
open PauliSamplerParameters

abbrev graph (ℓ : ℕ) :=
  TypeGraph.Adj (ℓ := ℓ) QLD.adj (.pauli .X) (.pauli .Z)

def fullSampler (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam : ℕ) : CL.Sampler 5 :=
  Introspection.detypedSampler QLD.adj (.pauli .X) (.pauli .Z) ℓ (sampler c hc he lam)

theorem fullSampler_dim (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam n : ℕ) :
    (fullSampler c hc he ℓ lam).dim n =
      4 * (Fintype.card QLD.Ty + 2 * ℓ + 6) + dimension c lam n :=
  Introspection.detypedSampler_dim _ _ _ _ _ _

def fullCompiler (c ℓ : ℕ) : PolyTimeFun ℕ Prog :=
  (ClockSimulation.codeRoute (CL.Detyping.Program.route (graph ℓ))
    (CL.Detyping.Program.post (CL.Detyping.graphDim (QuestionType QLD.Ty ℓ)))).comp
      ((ClockSimulation.codeRoute Introspection.SamplerProgram.route
        Introspection.SamplerProgram.post).comp (compiler c))

theorem fullCompiler_apply (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam : ℕ) :
    fullCompiler c ℓ lam = (fullSampler c hc he ℓ lam).prog := rfl

def fullDegree (ℓ : ℕ) : ℕ :=
  CL.Detyping.samplerDegree (graph ℓ) (Introspection.typedSamplerDegree degree)

def fullCoefficient (c ℓ lam n : ℕ) : ℕ :=
  CL.Detyping.samplerCoefficient (graph ℓ) n
    (Introspection.typedSamplerCoefficient n (coefficient c lam n) degree)
    (Introspection.typedSamplerDegree degree)

theorem fullSampler_timeBoundAt (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ lam n : ℕ) :
    (fullSampler c hc he ℓ lam).TimeBoundAt n (fullCoefficient c ℓ lam n) (fullDegree ℓ) :=
  CL.Detyping.sampler_timeBoundAt_uniform_degree (graph ℓ)
    (Introspection.typedSampler ℓ (sampler c hc he lam)) (by decide) n
    (Introspection.typedSamplerCoefficient n (coefficient c lam n) degree)
    (Introspection.typedSamplerDegree degree)
    (Introspection.typedSampler_timeBoundAt ℓ (sampler c hc he lam) n
      (coefficient c lam n) degree (sampler_timeBoundAt c hc he lam n))

private theorem routeCost_eval_mono (r : PolyTimeFun Data (Bool × Data))
    (p : PolyTimeFun (Data × Data) Data) (k : ℕ) {B B' x x' : ℕ}
    (hB : B ≤ B') (hx : x ≤ x') :
    (routeCost r p B k).eval x ≤ (routeCost r p B' k).eval x' := by
  have hR := polynomial_eval_mono r.timeBound hx
  have hF : B * (r.timeBound.eval x + 1) ^ k ≤
      B' * (r.timeBound.eval x' + 1) ^ k := by gcongr
  have hP := polynomial_eval_mono p.timeBound (show
    r.timeBound.eval x + B * (r.timeBound.eval x + 1) ^ k + 1 ≤
      r.timeBound.eval x' + B' * (r.timeBound.eval x' + 1) ^ k + 1 by omega)
  simp only [routeCost, eval_mul, eval_add, eval_C, eval_pow, eval_one, eval_comp]
  omega

private theorem routeCost_polyBounded (r : PolyTimeFun Data (Bool × Data))
    (p : PolyTimeFun (Data × Data) Data) (k : ℕ) {B : ℕ → ℕ} (hB : PolyBounded B) :
    PolyBounded (fun v => (routeCost r p (B v) k).eval (4 * v + 3)) := by
  simp only [routeCost, eval_mul, eval_add, eval_C, eval_pow, eval_one, eval_comp]
  repeat' first
    | exact hB
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.pow
    | apply PolyBounded.eval
    | apply PolyBounded.const
    | exact PolyBounded.id

def typedMajorant (c v : ℕ) : ℕ :=
  (routeCost Introspection.SamplerProgram.route Introspection.SamplerProgram.post
    (coefficientMajorant c v) degree).eval (4 * v + 3)

def fullMajorant (c ℓ v : ℕ) : ℕ :=
  (routeCost (CL.Detyping.Program.route (graph ℓ))
    (CL.Detyping.Program.post (CL.Detyping.graphDim (QuestionType QLD.Ty ℓ)))
    (typedMajorant c v) (Introspection.typedSamplerDegree degree)).eval (4 * v + 3)

theorem fullMajorant_polyBounded (c ℓ : ℕ) : PolyBounded (fullMajorant c ℓ) :=
  routeCost_polyBounded _ _ _
    (routeCost_polyBounded _ _ _ (coefficientMajorant_polyBounded c))

private theorem sum_coeff_eq_eval_one (P : Polynomial ℕ) :
    (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i) = P.eval 1 := by
  simp only [eval_eq_sum_range, one_pow, mul_one]

theorem fullCoefficient_le_majorant {c ℓ lam n v : ℕ} (hc : 1 ≤ c)
    (hl : lam ≤ v) (hn : n ≤ v) (hu : lam * n ≤ v) :
    fullCoefficient c ℓ lam n ≤ fullMajorant c ℓ v := by
  have hnsize : esize n + 2 ≤ 4 * v + 3 := by
    have he := esize_nat_le n
    have hs := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n)
    omega
  have hc' := coefficient_le_majorant hc hl hn hu
  have ht : Introspection.typedSamplerCoefficient n (coefficient c lam n) degree ≤
      typedMajorant c v := by
    have he : Introspection.typedSamplerCoefficient n (coefficient c lam n) degree =
        (routeCost Introspection.SamplerProgram.route Introspection.SamplerProgram.post
          (coefficient c lam n) degree).eval (esize n + 2) := by
      simp only [Introspection.typedSamplerCoefficient, Introspection.typedSamplerCost]
      rw [sum_coeff_eq_eval_one]
      simp only [eval_comp, eval_add, eval_X, eval_C]
      congr 1
      omega
    rw [he]
    exact routeCost_eval_mono _ _ _ hc' hnsize
  have he : fullCoefficient c ℓ lam n =
      (routeCost (CL.Detyping.Program.route (graph ℓ))
        (CL.Detyping.Program.post (CL.Detyping.graphDim (QuestionType QLD.Ty ℓ)))
        (Introspection.typedSamplerCoefficient n (coefficient c lam n) degree)
        (Introspection.typedSamplerDegree degree)).eval (esize n + 2) := by
    simp only [fullCoefficient, CL.Detyping.samplerCoefficient, CL.Detyping.samplerCost]
    rw [sum_coeff_eq_eval_one]
    simp only [eval_comp, eval_add, eval_X, eval_C]
    congr 1
    omega
  rw [he]
  exact routeCost_eval_mono _ _ _ ht hnsize

/-- Both routers preserve the single uniform positive-index budget. -/
theorem fullSampler_uniform_bound (c : ℕ) (hc : 1 ≤ c) (he : Even c) (ℓ : ℕ) :
    ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      (fullSampler c hc he ℓ lam).TimeBoundAt n ((lam * n + 1) ^ C) C ∧
      (fullSampler c hc he ℓ lam).dim n ≤ (lam * n + 1) ^ C := by
  obtain ⟨D, hD⟩ := ((fullMajorant_polyBounded c ℓ).add
    ((PolyBounded.const (4 * (Fintype.card QLD.Ty + 2 * ℓ + 6))).add
      (dimensionMajorant_polyBounded c))).exists_le_pow
  refine ⟨max D (fullDegree ℓ), fun lam n hl hn => ?_⟩
  have hlv : lam ≤ lam * n + 1 := by nlinarith
  have hnv : n ≤ lam * n + 1 := by nlinarith
  have hv : 2 ≤ lam * n + 1 := by nlinarith
  have hb := hD (lam * n + 1) hv
  have hp : (lam * n + 1) ^ D ≤ (lam * n + 1) ^ max D (fullDegree ℓ) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hcoef := fullCoefficient_le_majorant (ℓ := ℓ) hc hlv hnv (Nat.le_succ (lam * n))
  have hdim := dimension_le_majorant hc (show lam * n ≤ lam * n + 1 by omega)
  constructor
  · exact (fullSampler_timeBoundAt c hc he ℓ lam n).mono (by omega) (le_max_right _ _)
  · rw [fullSampler_dim]
    omega

end MIPRE.Introspection.PauliSampler
end
