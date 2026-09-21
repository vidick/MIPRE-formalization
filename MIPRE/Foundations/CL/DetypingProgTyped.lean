/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.TypedSampler
import MIPRE.Foundations.CL.DetypingProgFinite
import MIPRE.Foundations.Cost.Growth

/-! # Executable specialization of a typed sampler

Fixing a type yields an ordinary sampler, through an actual query adapter.
The adapter recognizes the dimension query and otherwise adds the type tag.
All malformed queries still halt because they become raw queries to the
original typed sampler at the same index.
-/

namespace MIPRE.CL.TypedSampler

open Cost Cost.PolyTimeFun

variable {T : Type*} [SizedEncoding T] {ℓ : ℕ}

def tagQuery (t : T) (q : Data) : Data :=
  if q = encode Sampler.Query.dimension then .nil else .cons (encode t) q

/-- The complete raw-data query adapter, including malformed input trees. -/
noncomputable def adapter (t : T) : PolyTimeFun Data Data :=
  ap₂ treePair treeHead (ite
    (ap₂ treeEq treeTail (const (encode Sampler.Query.dimension)))
    (const Data.nil) (ap₂ treePair (const (encode t)) treeTail))

theorem adapter_cons (t : T) (n q : Data) :
    adapter t (.cons n q) = .cons n (tagQuery t q) := by
  simp [adapter, tagQuery]

@[simp] theorem tagQuery_dimension (t : T) :
    tagQuery t (encode Sampler.Query.dimension) = encode (Query.dimension : Query T) := by
  simp [tagQuery]
  rfl

theorem tagQuery_atType (t : T) (q : Sampler.Query) (hq : q ≠ .dimension) :
    tagQuery t (encode q) = encode (Query.atType t q) := by
  have h : encode q ≠ encode Sampler.Query.dimension := fun h => hq (encode_injective h)
  simp only [tagQuery, h, ↓reduceIte]
  rfl

/-- The ordinary program specializing one type of the typed sampler. -/
noncomputable def specializeProg (S : TypedSampler ℓ T) (t : T) : Prog :=
  .let_ (adapter t).code S.prog

theorem specializeProg_closed (S : TypedSampler ℓ T) (t : T) :
    (specializeProg S t).WellScoped 1 :=
  ⟨(adapter t).closed, S.closed.mono (by omega) _⟩

theorem specializeProg_runs (S : TypedSampler ℓ T) (t : T)
    (n : ℕ) (q r : Data) (time : ℕ)
    (hr : S.prog.Runs (.cons (encode n) (tagQuery t q)) r time) :
    ∃ time', (specializeProg S t).Runs (.cons (encode n) q) r time' := by
  obtain ⟨t₀, _, h₀⟩ := (adapter t).computes (.cons (encode n) q)
  rw [adapter_cons] at h₀
  exact ⟨_, Eval.let_ h₀ (Eval.append_of_wellScoped hr S.closed _)⟩

/-- Fixing any type produces a genuine sampler with the same dimension and CL
functions. In particular this is available to detyping's selected-type calls. -/
noncomputable def specialize (S : TypedSampler ℓ T) (t : T) : Sampler ℓ where
  prog := specializeProg S t
  closed := specializeProg_closed S t
  dim := S.dim
  cl n w := S.cl n w t
  cl_exactlyOn n w := S.cl_exactlyOn n w t
  runs_dimension n := by
    obtain ⟨time, hr⟩ := S.runs_dimension n
    refine specializeProg_runs S t n (encode Sampler.Query.dimension) _ time ?_
    rw [tagQuery_dimension]
    exact hr
  runs_marginal n w j z hj hℓ hz := by
    obtain ⟨time, hr⟩ := S.runs_marginal n w t j z hj hℓ hz
    refine specializeProg_runs S t n (encode (Sampler.Query.marginal w j z)) _ time ?_
    rw [tagQuery_atType t (.marginal w j z) (by simp)]
    exact hr
  runs_linear n w j u y hj hℓ hu hy := by
    obtain ⟨time, hr⟩ := S.runs_linear n w t j u y hj hℓ hu hy
    refine specializeProg_runs S t n (encode (Sampler.Query.linear w j u y)) _ time ?_
    rw [tagQuery_atType t (.linear w j u y) (by simp)]
    exact hr
  runs_factor n w j u hj hℓ hu := by
    obtain ⟨time, hr⟩ := S.runs_factor n w t j u hj hℓ hu
    refine specializeProg_runs S t n (encode (Sampler.Query.factor w j u)) _ time ?_
    rw [tagQuery_atType t (.factor w j u) (by simp)]
    exact hr
  halts n q := by
    obtain ⟨r, time, hr⟩ := S.halts n (tagQuery t q)
    obtain ⟨time', hr'⟩ := specializeProg_runs S t n q r time hr
    exact ⟨r, time', hr'⟩

@[simp] theorem specialize_dim (S : TypedSampler ℓ T) (t : T) (n : ℕ) :
    (specialize S t).dim n = S.dim n := rfl

@[simp] theorem specialize_cl (S : TypedSampler ℓ T) (t : T) (n : ℕ) (w : Player) :
    (specialize S t).cl n w = S.cl n w t := rfl

/-- An explicit polynomial for the wrapper's overhead at one index. -/
noncomputable def specializeCost (t : T) (n B k : ℕ) : Polynomial ℕ :=
  (adapter t).timeBound.comp (Polynomial.X + Polynomial.C (esize n + 1)) +
    Polynomial.C B * (Polynomial.X + Polynomial.C (esize t + 2)) ^ k + 1

theorem tagQuery_size (t : T) (q : Data) :
    (tagQuery t q).size + 1 ≤ q.size + (esize t + 2) := by
  unfold tagQuery
  split_ifs <;> simp only [Data.size_nil, Data.size_cons, esize] <;> omega

/-- A typed running-time bound transfers through the actual adapter, including
all malformed query trees, with the displayed polynomial overhead. -/
theorem specialize_haltsWithin (S : TypedSampler ℓ T) (t : T) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) (q : Data) :
    HaltsWithin (specialize S t).prog (.cons (encode n) q)
      ((specializeCost t n B k).eval q.size) := by
  obtain ⟨r, time, ht, hr⟩ := h (tagQuery t q)
  obtain ⟨t₀, ht₀, h₀⟩ := (adapter t).computes (.cons (encode n) q)
  rw [adapter_cons] at h₀
  refine ⟨r, t₀ + time + 1, ?_,
    Eval.let_ h₀ (Eval.append_of_wellScoped hr S.closed _)⟩
  have htag := Nat.mul_le_mul_left B (Nat.pow_le_pow_left (tagQuery_size t q) k)
  have hsz : esize (Data.cons (encode n) q) = q.size + (esize n + 1) := by
    simp only [esize, encode_data, Data.size_cons]
    omega
  rw [hsz] at ht₀
  simp only [specializeCost, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one]
  omega

/-- Specializing a type preserves polynomial boundedness at every index. -/
theorem specialize_timeBoundAt (S : TypedSampler ℓ T) (t : T) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) :
    ∃ B' k', (specialize S t).TimeBoundAt n B' k' := by
  let Q := specializeCost t n B k
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i, Q.natDegree, ?_⟩
  intro q
  obtain ⟨r, time, ht, hr⟩ := specialize_haltsWithin S t n B k h q
  refine ⟨r, time, ht.trans ?_, hr⟩
  exact (polynomial_eval_mono Q (Nat.le_succ q.size)).trans
    (polynomial_eval_le_sum_coeff_mul_pow Q (by omega))

end MIPRE.CL.TypedSampler
