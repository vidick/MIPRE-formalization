/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Chain.Defs
public import MIPRE.Background.LIDT.ModelSoundness

@[expose] public section

/-!
# The model chain, part 2: extracting exactly linear combined codewords

The model counterpart of the operator half of the repository's
`MIPRE/Background/LIDT/Extraction.lean` (blueprint `lem:lidt-ldc-extraction`; not a vendored file:
its matrix statements serve the tensor instance `soundIn_tensor` and stay), in the port of
`planning/c6b-plan.md` (milestone M14, unit M14-3). It is the paper's Step 4 of the proof of
`lem:ld-soundness` for general `ldc` (`ldt.tex`, Claims 4 and 5), read in any bipartite model
`M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` whose two algebras are star-ordered `⋆`-rings (the instance set of
`MIPRE.LIDT.Simul.SoundIn`), at a unit state `‖M.ψ‖ = 1`.

The simultaneous test with `r` codewords is reduced to the single-codeword test in `K + m`
variables by *combining*: a point `(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where
`b ∈ F^r` is the original point answer at `y` (`combPOVM`). The single-codeword theorem returns a
measurement `R` of polynomials in the `K + m` variables, consistent with the combined answers;
`extractPM` turns it back into a measurement of `r`-tuples of polynomials in the `m` original
variables, read at a point by `MIPRE.LIDT.Simul.evalTuplePOVMIn` (`ModelSoundness.lean`), and
`extracted_conclusions` transfers the three conclusions, at the price `(K + m) d / q` on the two
point conclusions. Every statement is in the vocabulary of `M.inconsistency` and `M.bornProb`; the
original point measurements `A`, `B` are any families (in the chain, the tuple readings
`MIPRE.LIDT.Simul.tuplePOVMAIn`, `tuplePOVMBIn` of a strategy for the seeded test).

The proofs are those of the matrix file, with the matrix Born rule replaced by the model's: the
estimate is the classical `MIPRE.LIDT.Simul.sum_agreeX_le`, applied to the weights
`β y b g = M.bornProb (A_y)_b R_g`, which are nonnegative because the two players' positive
operators commute (`BipartiteModel.bornProb_nonneg`), and whose sum over `b` is the weight of `g`
alone (`BipartiteModel.bornProb_one_left`). Nothing is dimension-dependent.

**Reused by import.** The classical half of `Extraction.lean` (the partial evaluation, the linear
forms, the extraction itself, Schwartz--Zippel at a fixed `y` and the weighted bound) is imported
and named through an explicit `open MIPRE.LIDT.Simul (…)` list: `extract`, `extEval`, `linPoly`,
`padB`, `agreeX`, `sum_agreeX_le`, `xOf`, `yOf`, `sum_uniform_pad`, `sum_uniform_agree`,
`sum_uniform_one`, and `evalTuplePOVMIn` of `ModelSoundness.lean`.

## Not ported

The declarations of the operator section of `Extraction.lean` are redeclared here, under their
names, for POVMs in the algebras of `M`: `inconsistency_eq_one_sub`, `sum_bornProb_map_right`,
`sum_bornProb_map_left`, `inconsistency_extract_right_le`, `inconsistency_extract_left_le`,
`inconsistency_map_le`, `extractPM`, `combPOVM` and `extracted_conclusions`. Of the rest:

- `isPVM_pm`: the matrix projective measurement as an `IsPVM` family; the model's measurements are
  `POVMIn`s with `IsPVMIn` carried beside them, so there is nothing to convert.
- `extractPM_toPOVM`: `extractPM` is the coarse-graining `R.map (extract hd hr)` by definition here.
- `evalTuplePOVM`: replaced by `MIPRE.LIDT.Simul.evalTuplePOVMIn`, its existing model form; its
  lemma `evalTuplePOVM_extractPM` is `evalTuplePOVMIn_extractPM` here.
- the classical declarations, above: classical, imported.

`inconsistency_map_le` drops the hypothesis `∑ x, μ x = 1` of the matrix statement, which its
model proof (through `BipartiteModel.dis_map_le`) does not use, and `extracted_conclusions` takes
`RA`, `RB` as POVMs, projectivity being the separate `extractPM_isPVMIn`.

## New here

- `extractPM_isPVMIn`: the extraction of a projective measurement is projective
  (`POVMIn.isPVMIn_map`).
- `evalTuplePOVMIn_extractPM`: above.
-/

open MIPRE.LIDT (Point LowIndDegPoly LowIndDegPoly.eval)
open MIPRE.LIDT.Simul (extract extEval linPoly padB agreeX sum_agreeX_le xOf yOf sum_uniform_pad
  sum_uniform_agree sum_uniform_one evalTuplePOVMIn)

noncomputable section

namespace MIPRE.LIDT.Co.Chain

open Finset

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-! ## The operator form -/

section Operators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **`inconsistency` is one minus the average agreement**, for POVMs at a unit state and a
probability distribution on the questions. -/
theorem inconsistency_eq_one_sub {M : BipartiteModel 𝒞 𝒜 ℬ} {X Λ : Type*} [Fintype X]
    [Fintype Λ] [DecidableEq Λ] {μ : X → ℝ} (hμ1 : ∑ x, μ x = 1) (hψ : ‖M.ψ‖ = 1)
    (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M.inconsistency μ P Q = 1 - ∑ x, μ x * ∑ a, M.bornProb ((P x).op a) ((Q x).op a) := by
  rw [M.inconsistency_eq_sum_dis hψ]
  simp only [BipartiteModel.dis, mul_sub, mul_one, Finset.sum_sub_distrib, hμ1]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Relabelling the second family: `∑_c ⟨P_c, (N.map f)_c⟩ = ∑_a ⟨P_{f a}, N_a⟩`. -/
theorem sum_bornProb_map_right (M : BipartiteModel 𝒞 𝒜 ℬ) {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq C] (P : C → 𝒜) (N : POVMIn A ℬ) (f : A → C) :
    ∑ c, M.bornProb (P c) ((N.map f).op c) = ∑ a, M.bornProb (P (f a)) (N.op a) := by
  simp only [POVMIn.map_op, M.bornProb_sum_right]
  rw [← Finset.sum_fiberwise (univ : Finset A) f fun a => M.bornProb (P (f a)) (N.op a)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- Relabelling the first family. -/
theorem sum_bornProb_map_left (M : BipartiteModel 𝒞 𝒜 ℬ) {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq C] (N : POVMIn A 𝒜) (Q : C → ℬ) (f : A → C) :
    ∑ c, M.bornProb ((N.map f).op c) (Q c) = ∑ a, M.bornProb (N.op a) (Q (f a)) := by
  simp only [POVMIn.map_op, M.bornProb_sum_left]
  rw [← Finset.sum_fiberwise (univ : Finset A) f fun a => M.bornProb (N.op a) (Q (f a))]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.mp ha).2]

omit [Field F] [Fintype F] [DecidableEq F] in
/-- A padded point is the concatenation of its combining and original coordinates. -/
private theorem append_xOf_yOf (u : Point F (K + m)) : Fin.append (xOf u) (yOf u) = u := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- The average over a uniform `x` of the combined agreement indicators, weighted by `β`, is the
weighted `agreeX`. -/
private theorem sum_uniform_weighted_agree (hd : 1 ≤ d) (y : Point F m)
    (β : (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ) :
    ∑ x : Point F K, uniform (Point F K) x * ∑ b, ∑ g, β b g *
        (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0)
      = ∑ b, ∑ g, β b g * agreeX hd g y b := by
  simp only [Finset.mul_sum, ← sum_uniform_agree hd]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun x _ => by ring

/-- The agreement of an original answer with the extracted tuple, as a weighted indicator. -/
private theorem sum_ite_extEval (hd : 1 ≤ d) (hr : r ≤ K) (y : Point F m)
    (β : (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ) :
    ∑ g, β (extEval hd hr g y) g = ∑ b, ∑ g, β b g * (if extEval hd hr g y = b then 1 else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single (extEval hd hr g y) (fun b _ hb => by
    rw [ite_eq_right (Ne.symm hb), mul_zero]) (fun h => absurd (Finset.mem_univ _) h),
    ite_eq_left rfl, mul_one]

/-- **The extraction bound, the extracted measurement on the second party.** -/
theorem inconsistency_extract_right_le {M : BipartiteModel 𝒞 𝒜 ℬ} (hd : 1 ≤ d) (hr : r ≤ K)
    (hψ : ‖M.ψ‖ = 1) (A : Point F m → POVMIn (Fin r → F) 𝒜)
    (R : POVMIn (LowIndDegPoly (F := F) (m := K + m) (d := d)) ℬ) :
    M.inconsistency (uniform (Point F m)) A (fun y => R.map fun g => extEval hd hr g y)
      ≤ M.inconsistency (uniform (Point F (K + m)))
          (fun u => (A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u))
          (fun u => R.map fun g => g.eval u)
        + (K + m) * d / Fintype.card F := by
  set β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ :=
    fun y b g => M.bornProb ((A y).op b) (R.op g) with hβ
  have hβ0 : ∀ y b g, 0 ≤ β y b g := fun y b g =>
    M.bornProb_nonneg ((A y).op_nonneg b) (R.op_nonneg g)
  have hw : ∀ y g, ∑ b, β y b g = M.bornProb 1 (R.op g) := fun y g =>
    (M.bornProb_one_left (A y) _).symm
  have hw1 : ∑ g, M.bornProb 1 (R.op g) = 1 := by
    simp_rw [M.bornProb_one_left (A 0)]
    rw [Finset.sum_comm]
    exact M.sum_bornProb hψ _ _
  have hmain := sum_agreeX_le hd hr β hβ0 _ hw hw1
  rw [inconsistency_eq_one_sub (sum_uniform_one _) hψ,
    inconsistency_eq_one_sub (sum_uniform_one _) hψ]
  have hL : ∀ y, ∑ c, M.bornProb ((A y).op c) ((R.map fun g => extEval hd hr g y).op c)
      = ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0) := fun y => by
    rw [sum_bornProb_map_right M (fun c => (A y).op c) R]
    exact sum_ite_extEval hd hr y (β y)
  have hR : ∀ u : Point F (K + m), ∑ c,
      M.bornProb (((A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)).op c)
        ((R.map fun g => g.eval u).op c)
      = ∑ b, ∑ g, β (yOf u) b g *
          (if (linPoly hd (padB b)).eval (xOf u) = g.eval (Fin.append (xOf u) (yOf u))
            then 1 else 0) := fun u => by
    rw [append_xOf_yOf, M.sum_bornProb_map]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g _ => by ring
  simp only [hL, hR]
  rw [sum_uniform_pad (fun x y => ∑ b, ∑ g, β y b g *
      (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0))]
  simp only [sum_uniform_weighted_agree hd]
  linarith

/-- **The extraction bound, the extracted measurement on the first party.** -/
theorem inconsistency_extract_left_le {M : BipartiteModel 𝒞 𝒜 ℬ} (hd : 1 ≤ d) (hr : r ≤ K)
    (hψ : ‖M.ψ‖ = 1) (R : POVMIn (LowIndDegPoly (F := F) (m := K + m) (d := d)) 𝒜)
    (B : Point F m → POVMIn (Fin r → F) ℬ) :
    M.inconsistency (uniform (Point F m)) (fun y => R.map fun g => extEval hd hr g y) B
      ≤ M.inconsistency (uniform (Point F (K + m)))
          (fun u => R.map fun g => g.eval u)
          (fun u => (B (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u))
        + (K + m) * d / Fintype.card F := by
  set β : Point F m → (Fin r → F) → LowIndDegPoly (F := F) (m := K + m) (d := d) → ℝ :=
    fun y b g => M.bornProb (R.op g) ((B y).op b) with hβ
  have hβ0 : ∀ y b g, 0 ≤ β y b g := fun y b g =>
    M.bornProb_nonneg (R.op_nonneg g) ((B y).op_nonneg b)
  have hw : ∀ y g, ∑ b, β y b g = M.bornProb (R.op g) 1 := fun y g =>
    (M.bornProb_one_right _ (B y)).symm
  have hw1 : ∑ g, M.bornProb (R.op g) 1 = 1 := by
    simp_rw [M.bornProb_one_right _ (B 0)]
    exact M.sum_bornProb hψ _ _
  have hmain := sum_agreeX_le hd hr β hβ0 _ hw hw1
  rw [inconsistency_eq_one_sub (sum_uniform_one _) hψ,
    inconsistency_eq_one_sub (sum_uniform_one _) hψ]
  have hL : ∀ y, ∑ c, M.bornProb ((R.map fun g => extEval hd hr g y).op c) ((B y).op c)
      = ∑ b, ∑ g, β y b g * (if extEval hd hr g y = b then 1 else 0) := fun y => by
    rw [sum_bornProb_map_left M R (fun c => (B y).op c)]
    exact sum_ite_extEval hd hr y (β y)
  have hR : ∀ u : Point F (K + m), ∑ c,
      M.bornProb ((R.map fun g => g.eval u).op c)
        (((B (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)).op c)
      = ∑ b, ∑ g, β (yOf u) b g *
          (if (linPoly hd (padB b)).eval (xOf u) = g.eval (Fin.append (xOf u) (yOf u))
            then 1 else 0) := fun u => by
    rw [append_xOf_yOf, M.sum_bornProb_map, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g _ => by
      simp only [hβ, eq_comm]; ring
  simp only [hL, hR]
  rw [sum_uniform_pad (fun x y => ∑ b, ∑ g, β y b g *
      (if (linPoly hd (padB b)).eval x = g.eval (Fin.append x y) then 1 else 0))]
  simp only [sum_uniform_weighted_agree hd]
  linarith

end Operators

/-! ## The extracted measurements, and the three conclusions -/

section Assembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}

/-- **Data processing for `inconsistency`**: relabelling both families' outcomes the same way can
only decrease the disagreement. -/
theorem inconsistency_map_le {M : BipartiteModel 𝒞 𝒜 ℬ} {X Λ C : Type*} [Fintype X] [Fintype Λ]
    [DecidableEq Λ] [Fintype C] [DecidableEq C] {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x)
    (hψ : ‖M.ψ‖ = 1) (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) (f : Λ → C) :
    M.inconsistency μ (fun x => (P x).map f) (fun x => (Q x).map f) ≤ M.inconsistency μ P Q := by
  rw [M.inconsistency_eq_sum_dis hψ, M.inconsistency_eq_sum_dis hψ]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (M.dis_map_le _ _ f) (hμ0 x)

/-- **The extracted measurement**: `R` coarse-grained by `extract`, a measurement of `r`-tuples
of polynomials in the `m` original variables. -/
def extractPM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hd : 1 ≤ d) (hr : r ≤ K) (G : POVMIn (LowIndDegPoly (F := F) (m := K + m) (d := d)) R) :
    POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) R :=
  G.map (extract hd hr)

/-- **The extracted measurement of a projective measurement is projective.** -/
theorem extractPM_isPVMIn {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hd : 1 ≤ d) (hr : r ≤ K) {G : POVMIn (LowIndDegPoly (F := F) (m := K + m) (d := d)) R}
    (hG : IsPVMIn G.op) : IsPVMIn (extractPM hd hr G).op :=
  POVMIn.isPVMIn_map hG _

/-- The extracted measurement read at `y` is `R` relabelled by the extracted tuple at `y`. -/
theorem evalTuplePOVMIn_extractPM {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (hd : 1 ≤ d) (hr : r ≤ K)
    (G : POVMIn (LowIndDegPoly (F := F) (m := K + m) (d := d)) R) (y : Point F m) :
    evalTuplePOVMIn (extractPM hd hr G) y = G.map fun g => extEval hd hr g y :=
  POVMIn.map_map _ _ _

/-- The combined point measurement: at the padded point `(x, y)`, measure the original point
measurement at `y` and answer `∑_{j < r} x_j b_j`. -/
def combPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hd : 1 ≤ d) (A : Point F m → POVMIn (Fin r → F) R) (u : Point F (K + m)) : POVMIn F R :=
  (A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)

/-- **From the single-codeword conclusions to the simultaneous ones** (the paper's Step 4), in
the model `M` at a unit state. If the two players' measurements `RA`, `RB` of polynomials in the
`K + m` variables satisfy the three conclusions of the single-codeword theorem against the
combined point measurements, with error `δ`, then their extractions satisfy the three conclusions
of the simultaneous theorem against the original point measurements `A`, `B`, with error
`δ + (K + m) d / q` for the two point conclusions and `δ` for the full-tuple one. -/
theorem extracted_conclusions {M : BipartiteModel 𝒞 𝒜 ℬ} (hd : 1 ≤ d) (hr : r ≤ K)
    (hψ : ‖M.ψ‖ = 1) (A : Point F m → POVMIn (Fin r → F) 𝒜)
    (B : Point F m → POVMIn (Fin r → F) ℬ)
    (RA : POVMIn (LowIndDegPoly (F := F) (m := K + m) (d := d)) 𝒜)
    (RB : POVMIn (LowIndDegPoly (F := F) (m := K + m) (d := d)) ℬ) {δ : ℝ}
    (h1 : M.inconsistency (uniform (Point F (K + m))) (combPOVM hd A) (evalPOVMIn RB) ≤ δ)
    (h2 : M.inconsistency (uniform (Point F (K + m))) (evalPOVMIn RA) (combPOVM hd B) ≤ δ)
    (h3 : M.inconsistency (uniform Unit) (fun _ => RA) (fun _ => RB) ≤ δ) :
    M.inconsistency (uniform (Point F m)) A (evalTuplePOVMIn (extractPM hd hr RB))
        ≤ δ + (K + m) * d / Fintype.card F ∧
      M.inconsistency (uniform (Point F m)) (evalTuplePOVMIn (extractPM hd hr RA)) B
        ≤ δ + (K + m) * d / Fintype.card F ∧
      M.inconsistency (uniform Unit) (fun _ => extractPM hd hr RA)
        (fun _ => extractPM hd hr RB) ≤ δ := by
  refine ⟨?_, ?_, ?_⟩
  · have h := inconsistency_extract_right_le hd hr hψ A RB
    rw [show evalTuplePOVMIn (extractPM hd hr RB) = fun y => RB.map fun g => extEval hd hr g y
      from funext (evalTuplePOVMIn_extractPM hd hr RB)]
    exact h.trans (by unfold combPOVM evalPOVMIn at h1; linarith)
  · have h := inconsistency_extract_left_le hd hr hψ RA B
    rw [show evalTuplePOVMIn (extractPM hd hr RA) = fun y => RA.map fun g => extEval hd hr g y
      from funext (evalTuplePOVMIn_extractPM hd hr RA)]
    exact h.trans (by unfold combPOVM evalPOVMIn at h2; linarith)
  · exact (inconsistency_map_le (fun _ => by simp only [uniform]; positivity) hψ
      (fun _ => RA) (fun _ => RB) (extract hd hr)).trans h3

end Assembly

end MIPRE.LIDT.Co.Chain

end

end
