/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgFinite
import MIPRE.Foundations.CL.Sampler
import MIPRE.Foundations.CL.Graph
import MIPRE.Foundations.CL.Embedding
import MIPRE.Foundations.Cost.Growth

/-! # An executable fixed graph sampler

Every fixed finite CL presentation has a total ambient sampler program: a
finite table covers its valid queries, with a fixed output on other inputs.
We instantiate this construction with the two-level graph presentation used
by detyping. Its dimension, all query answers and halting on malformed inputs
are proved. This finite-table construction is polynomial in query size for
each fixed graph; it does not claim polynomial compilation in graph size.
-/

noncomputable section

namespace MIPRE.CL

open Cost Classical Finset

namespace FixedSampler

abbrev QueryIndex (d ℓ : ℕ) :=
  Fin 3 × Bool × Fin (ℓ + 1) × (Fin d → 𝔽₂) × (Fin d → 𝔽₂)

def queryOfIndex {d ℓ : ℕ} (i : QueryIndex d ℓ) : Sampler.Query :=
  match i.1.val with
  | 0 => .marginal (Player.ofBool i.2.1) i.2.2.1 (toBits i.2.2.2.1)
  | 1 => .linear (Player.ofBool i.2.1) i.2.2.1 (toBits i.2.2.2.1) (toBits i.2.2.2.2)
  | _ => .factor (Player.ofBool i.2.1) i.2.2.1 (toBits i.2.2.2.1)

def queries (d ℓ : ℕ) : Finset Data :=
  insert (encode Sampler.Query.dimension)
    (univ.image (fun i : QueryIndex d ℓ => encode (queryOfIndex i)))

theorem dimension_mem (d ℓ : ℕ) : encode Sampler.Query.dimension ∈ queries d ℓ := by
  simp [queries]

theorem marginal_mem {d ℓ : ℕ} (w : Player) (j : ℕ) (z : BitStr)
    (hj : j ≤ ℓ) (hz : z.length = d) :
    encode (Sampler.Query.marginal w j z) ∈ queries d ℓ := by
  apply mem_insert_of_mem
  apply mem_image.mpr
  refine ⟨(0, w.toBool, ⟨j, by omega⟩, ofBits d z, 0), mem_univ _, ?_⟩
  simp only [queryOfIndex, Fin.val_zero, Player.ofBool_toBool, toBits_ofBits hz]

theorem linear_mem {d ℓ : ℕ} (w : Player) (j : ℕ) (u y : BitStr)
    (hj : j ≤ ℓ) (hu : u.length = d) (hy : y.length = d) :
    encode (Sampler.Query.linear w j u y) ∈ queries d ℓ := by
  apply mem_insert_of_mem
  apply mem_image.mpr
  refine ⟨(1, w.toBool, ⟨j, by omega⟩, ofBits d u, ofBits d y), mem_univ _, ?_⟩
  simp only [queryOfIndex, Fin.val_one, Player.ofBool_toBool, toBits_ofBits hu,
    toBits_ofBits hy]

theorem factor_mem {d ℓ : ℕ} (w : Player) (j : ℕ) (u : BitStr)
    (hj : j ≤ ℓ) (hu : u.length = d) :
    encode (Sampler.Query.factor w j u) ∈ queries d ℓ := by
  apply mem_insert_of_mem
  apply mem_image.mpr
  refine ⟨(2, w.toBool, ⟨j, by omega⟩, ofBits d u, 0), mem_univ _, ?_⟩
  simp only [queryOfIndex, Player.ofBool_toBool, toBits_ofBits hu]

def answer {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ) : Sampler.Query → Data
  | .dimension => encode d
  | .marginal w j z => encode (toBits (((P w).truncate j).eval (ofBits d z)))
  | .linear w j u y =>
      encode (toBits ((P w).mapOfPrefix (j - 1) (ofBits d u) (ofBits d y)))
  | .factor w j u => encode (indicatorBits ((P w).factorOfPrefix (j - 1) (ofBits d u)))

def table {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ) : PolyTimeFun Data Data :=
  PolyTimeFun.finiteTable (fun data =>
    ((decode data : Option Sampler.Query).map (answer P)).getD .nil) (queries d ℓ).toList

theorem table_correct {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ)
    (q : Sampler.Query) (hq : encode q ∈ queries d ℓ) : table P (encode q) = answer P q := by
  rw [table, PolyTimeFun.finiteTable_apply_of_mem _ _ _ (mem_toList.mpr hq)]
  simp [SizedEncoding.decode_encode]

/-- Drop the index without traversing it and run the finite query table. -/
def prog {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ) : Prog :=
  .let_ Prog.sndProg (table P).code

theorem prog_closed {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ) :
    (prog P).WellScoped 1 :=
  ⟨Prog.sndProg_wellScoped, (table P).closed.mono (by omega) _⟩

theorem prog_runs {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ)
    (n : ℕ) (q : Sampler.Query) (hq : encode q ∈ queries d ℓ) :
    ∃ time, (prog P).Runs (encode (n, q)) (answer P q) time := by
  obtain ⟨t, _, hr⟩ := (table P).computes (encode q)
  rw [table_correct P q hq] at hr
  exact ⟨_, Eval.let_ (Prog.sndProg_runs (encode n) (encode q))
    (Eval.append_of_wellScoped hr (table P).closed _)⟩

def sampler {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ)
    (hP : ∀ w, (P w).ExactlyOn univ) : Sampler ℓ where
  prog := prog P
  closed := prog_closed P
  dim _ := d
  cl _ := P
  cl_exactlyOn _ := hP
  runs_dimension n := prog_runs P n _ (dimension_mem d ℓ)
  runs_marginal n w j z _ hj hz := prog_runs P n _ (marginal_mem w j z hj hz)
  runs_linear n w j u y _ hj hu hy := by
    obtain ⟨x, rfl⟩ := hu
    exact prog_runs P n _ (linear_mem w j _ y hj (length_toBits _) hy)
  runs_factor n w j u _ hj hu := by
    obtain ⟨x, rfl⟩ := hu
    exact prog_runs P n _ (factor_mem w j _ hj (length_toBits _))
  halts n data := by
    obtain ⟨t, _, hr⟩ := (table P).computes data
    exact ⟨_, _, Eval.let_ (Prog.sndProg_runs (encode n) data)
      (Eval.append_of_wellScoped hr (table P).closed _)⟩

/-- A single polynomial bounds every index, because the program never traverses
the index. Its coefficients depend on the fixed finite presentation. -/
theorem sampler_timeBound {d ℓ : ℕ} (P : Player → CLFun 𝔽₂ (Fin d) ℓ)
    (hP : ∀ w, (P w).ExactlyOn univ) :
    ∃ B k, (sampler P hP).TimeBound (fun _ => B) k := by
  let Q := (table P).timeBound + Polynomial.X + Polynomial.C 3
  refine ⟨∑ i ∈ range (Q.natDegree + 1), Q.coeff i, Q.natDegree, ?_⟩
  intro n data
  obtain ⟨t, ht, hr⟩ := (table P).computes data
  refine ⟨_, data.size + 2 + t + 1, ?_,
    Eval.let_ (Prog.sndProg_runs (encode n) data)
      (Eval.append_of_wellScoped hr (table P).closed _)⟩
  calc data.size + 2 + t + 1 ≤ Q.eval (data.size + 1) := by
        have hm := polynomial_eval_mono (table P).timeBound
          (Nat.le_succ data.size)
        simp only [Q, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
          esize_data, Nat.succ_eq_add_one] at *
        omega
    _ ≤ _ := polynomial_eval_le_sum_coeff_mul_pow Q (by omega)

end FixedSampler

namespace Graph

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Numbering the four finite graph blocks in the standard sampler interface. -/
def numberedPresentation (E : T → T → Prop) [DecidableRel E] (w : Player) :
    CLFun 𝔽₂ (Fin (Fintype.card (Coord T))) 2 :=
  (presentation E w.toBool).embed (Fintype.equivFin (Coord T)).toEmbedding

theorem numberedPresentation_exactlyOn (E : T → T → Prop) [DecidableRel E] (w : Player) :
    (numberedPresentation E w).ExactlyOn univ := by
  have h := (presentation_exactlyOn E w.toBool).embed (Fintype.equivFin (Coord T)).toEmbedding
  simpa [numberedPresentation] using h

/-- The fixed graph sampler is an actual total program with all four query clauses. -/
def sampler (E : T → T → Prop) [DecidableRel E] : Sampler 2 :=
  FixedSampler.sampler (numberedPresentation E) (numberedPresentation_exactlyOn E)

theorem sampler_dim (E : T → T → Prop) [DecidableRel E] (n : ℕ) :
    (sampler E).dim n = 4 * Fintype.card T := by
  change Fintype.card (Coord T) = _
  simp [Coord]
  omega

theorem sampler_timeBound (E : T → T → Prop) [DecidableRel E] :
    ∃ B k, (sampler E).TimeBound (fun _ => B) k :=
  FixedSampler.sampler_timeBound _ _

end Graph
end MIPRE.CL
