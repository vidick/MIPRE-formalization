/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.PauliSampler
import MIPRE.Foundations.Introspection.PauliSamplerParamsCost

/-! # Polynomial query time of the canonical Pauli sampler

The query degree is independent of the index and of the boundedness
parameter. The coefficient includes the explicit canonical-parameter cost;
no halting or complexity assumption on a supplied program is used.
-/

noncomputable section
namespace MIPRE.Introspection.PauliSampler
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program Polynomial
open PauliSamplerParameters

def costPolynomial (c lam n : ℕ) : Polynomial ℕ :=
  let s := esize (parameters c lam n)
  let p := PauliSamplerParameters.cost c lam n + esize lam + esize n + 3
  route.timeBound.comp (X + Polynomial.C (esize n + 1)) +
    Polynomial.C (3 * esize n + s + p + 19) +
    Polynomial.C 3 * X + post.timeBound.comp (X + Polynomial.C (s + 1)) +
    QLD.PauliCL.SamplerProgram.query.timeBound.comp (X + Polynomial.C (s + 1))

def degree : ℕ := max route.timeBound.natDegree
  (max post.timeBound.natDegree (max QLD.PauliCL.SamplerProgram.query.timeBound.natDegree 1))

private theorem shifted_degree (P : Polynomial ℕ) (a : ℕ) :
    (P.comp (X + Polynomial.C a)).natDegree ≤ P.natDegree := by
  have h : (X + Polynomial.C a : Polynomial ℕ).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp) (by simp)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ h).trans (by simp))

theorem costPolynomial_degree (c lam n : ℕ) :
    (costPolynomial c lam n).natDegree ≤ degree := by
  have hR : route.timeBound.natDegree ≤ degree := le_max_left _ _
  have hP : post.timeBound.natDegree ≤ degree :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hQ : QLD.PauliCL.SamplerProgram.query.timeBound.natDegree ≤ degree :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h1 : 1 ≤ degree :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold costPolynomial
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_add_le_of_degree_le ((shifted_degree _ _).trans hR)
          (by simp only [natDegree_C]; exact Nat.zero_le _)
      · exact (natDegree_C_mul_le _ _).trans (by simpa using h1)
    · exact (shifted_degree _ _).trans hP
  · exact (shifted_degree _ _).trans hQ

theorem prog_runs_cost (c lam n : ℕ) (d : Data) :
    ∃ time ≤ (costPolynomial c lam n).eval d.size,
      (prog c lam).Runs (.cons (encode n) d)
        (QLD.PauliCL.SamplerProgram.query (parameters c lam n, d)) time := by
  obtain ⟨t₁, ht₁, h₁⟩ := PauliSamplerParameters.prog_runs_cost c lam n
  have h₂ := hardcode_time (PauliSamplerParameters.prog_closed c) h₁
  obtain ⟨t₃, ht₃, h₃⟩ := routeOneCall_indirect_cost route
    (hardcode_wellScoped (PauliSamplerParameters.prog_closed c) _) post
    (.cons (encode n) d) (encode n) d (encode (parameters c lam n)) _
    (by simp [route, readNat_encode]) h₂
  have hout : post (d, encode (parameters c lam n)) =
      encode (parameters c lam n, d) := rfl
  rw [hout] at h₃
  obtain ⟨t₄, ht₄, h₄⟩ := QLD.PauliCL.SamplerProgram.query.computes (parameters c lam n, d)
  refine ⟨_, ?_, Eval.let_ h₃
    (Eval.append_of_wellScoped h₄ QLD.PauliCL.SamplerProgram.query.closed _)⟩
  simp only [costPolynomial, eval_add, eval_mul, eval_C, eval_X, eval_comp]
  simp only [Data.size_cons] at ht₃
  simp only [esize_prod, esize_data] at ht₄
  change t₃ ≤ route.timeBound.eval (esize n + d.size + 1) + 3 * esize n +
    3 * d.size + esize (parameters c lam n) + (t₁ + esize lam + esize n + 3) +
    post.timeBound.eval (d.size + esize (parameters c lam n) + 1) + 18 at ht₃
  have hR : esize n + d.size + 1 = d.size + (esize n + 1) := by omega
  have hP : d.size + esize (parameters c lam n) + 1 =
      d.size + (esize (parameters c lam n) + 1) := by omega
  have hQ : esize (parameters c lam n) + d.size + 1 =
      d.size + (esize (parameters c lam n) + 1) := by omega
  rw [hR, hP] at ht₃
  rw [hQ] at ht₄
  omega

def coefficient (c lam n : ℕ) : ℕ :=
  let P := costPolynomial c lam n
  ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i

theorem sampler_timeBoundAt (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ) :
    (sampler c hc he lam).TimeBoundAt n (coefficient c lam n) degree := by
  intro d
  obtain ⟨t, ht, hr⟩ := prog_runs_cost c lam n d
  refine ⟨_, t, ht.trans ?_, hr⟩
  apply (polynomial_eval_mono _ (Nat.le_succ d.size)).trans
  apply (polynomial_eval_le_sum_coeff_mul_pow _ (by omega)).trans
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (costPolynomial_degree c lam n))

theorem coefficient_eq_eval_one (c lam n : ℕ) :
    coefficient c lam n = (costPolynomial c lam n).eval 1 := by
  simp only [coefficient, eval_eq_sum_range, one_pow, mul_one]

/-- A polynomial majorant uniform in both the boundedness parameter and index. -/
def coefficientMajorant (c v : ℕ) : ℕ :=
  let s := 6 * widthBound c v + 5
  let e := 4 * v + 1
  route.timeBound.eval (1 + (e + 1)) +
    (3 * e + s + (costMajorant c v + e + e + 3) + 19) + 3 +
    post.timeBound.eval (1 + (s + 1)) +
    QLD.PauliCL.SamplerProgram.query.timeBound.eval (1 + (s + 1))

theorem coefficient_le_majorant {c lam n v : ℕ} (hc : 1 ≤ c)
    (hl : lam ≤ v) (hn : n ≤ v) (hu : lam * n ≤ v) :
    coefficient c lam n ≤ coefficientMajorant c v := by
  have hs := parameters_size_le hc hu
  have ht := cost_le_majorant hc hl hn hu
  have hel : esize lam ≤ 4 * v + 1 := (esize_nat_le lam).trans (by
    have h := (Nat.size_le.mpr Nat.lt_two_pow_self : lam.size ≤ lam)
    omega)
  have hen : esize n ≤ 4 * v + 1 := (esize_nat_le n).trans (by
    have h := (Nat.size_le.mpr Nat.lt_two_pow_self : n.size ≤ n)
    omega)
  have hR := polynomial_eval_mono route.timeBound
    (show 1 + (esize n + 1) ≤ 1 + ((4 * v + 1) + 1) by omega)
  have hP := polynomial_eval_mono post.timeBound
    (show 1 + (esize (parameters c lam n) + 1) ≤
      1 + ((6 * widthBound c v + 5) + 1) by omega)
  have hQ := polynomial_eval_mono QLD.PauliCL.SamplerProgram.query.timeBound
    (show 1 + (esize (parameters c lam n) + 1) ≤
      1 + ((6 * widthBound c v + 5) + 1) by omega)
  rw [coefficient_eq_eval_one]
  simp only [costPolynomial, eval_add, eval_mul, eval_C, eval_X, eval_comp, mul_one]
  dsimp only [coefficientMajorant]
  omega

theorem coefficientMajorant_polyBounded (c : ℕ) : PolyBounded (coefficientMajorant c) := by
  unfold coefficientMajorant widthBound
  repeat' first
    | exact costMajorant_polyBounded c
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.eval
    | apply PolyBounded.const
    | exact PolyBounded.id

def dimensionMajorant (c v : ℕ) : ℕ :=
  (3 * widthBound c v + 3) * widthBound c v

theorem dimension_le_majorant {c lam n v : ℕ} (hc : 1 ≤ c) (hu : lam * n ≤ v) :
    dimension c lam n ≤ dimensionMajorant c v := by
  obtain ⟨hk, _, hm⟩ := parameters_le_widthBound hc hu
  unfold dimension dimensionMajorant
  gcongr

theorem dimensionMajorant_polyBounded (c : ℕ) : PolyBounded (dimensionMajorant c) := by
  unfold dimensionMajorant widthBound
  repeat' first
    | apply PolyBounded.add
    | apply PolyBounded.mul
    | apply PolyBounded.const
    | exact PolyBounded.id

/-- One exponent bounds the canonical sampler's query time and question
dimension at every positive index and positive boundedness parameter. -/
theorem sampler_uniform_bound (c : ℕ) (hc : 1 ≤ c) (he : Even c) :
    ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      (sampler c hc he lam).TimeBoundAt n ((lam * n + 1) ^ C) C ∧
      (sampler c hc he lam).dim n ≤ (lam * n + 1) ^ C := by
  obtain ⟨D, hD⟩ := ((coefficientMajorant_polyBounded c).add
    (dimensionMajorant_polyBounded c)).exists_le_pow
  refine ⟨max D degree, fun lam n hl hn => ?_⟩
  have hlv : lam ≤ lam * n + 1 := by nlinarith
  have hnv : n ≤ lam * n + 1 := by nlinarith
  have hv : 2 ≤ lam * n + 1 := by nlinarith
  have hb := hD (lam * n + 1) hv
  have hp : (lam * n + 1) ^ D ≤ (lam * n + 1) ^ max D degree :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hcoef := coefficient_le_majorant hc hlv hnv (Nat.le_succ (lam * n))
  have hdim := dimension_le_majorant hc (show lam * n ≤ lam * n + 1 by omega)
  constructor
  · exact (sampler_timeBoundAt c hc he lam n).mono (by omega) (le_max_right _ _)
  · exact hdim.trans (by omega)

end MIPRE.Introspection.PauliSampler
end
