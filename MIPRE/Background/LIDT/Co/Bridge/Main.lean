/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Bridge.Value
public import MIPRE.Background.LIDT.Co.Bridge.Consistency
public import MIPRE.Background.LIDT.Co.Test.MainTheorem.MainFormal
public import MIPRE.Background.LIDT.Co.Chain.Defs

@[expose] public section

/-!
# Bridge, part 8, over models: the soundness theorem in our vocabulary

The model counterpart of the repository's matrix bridge `MIPRE/Background/LIDT/Bridge/Main.lean`
(not a vendored file; it serves the tensor instance and stays), in the port of
`planning/c6b-plan.md` (milestone M14, unit M14-2).

The port's main theorem `MIPRE.LIDT.Co.Test.mainFormal_isPVMIn` (`Co/Test/MainTheorem/MainFormal`),
applied to the induced strategy `toCoProjStrat S` of a projective strategy
`S : M.ProjStrat (lidtGame F m d)` in a bipartite model `M` that is a dyadic pair, produces two
projective measurements of the port with outcomes the polynomials of individual degree at most
`d`, one in each player's algebra, which are projective measurements of the repository
(`MIPRE.IsPVMIn`). `ofProjMeas` reads them as POVMs with outcomes in `LowIndDegPoly` along
`lowIndDegEquiv`, projective by `ofProjMeas_isPVMIn`, and the three consistency conclusions are
transferred with `inconsistency_eq_bipartiteConsError` (`Co/Bridge/Consistency.lean`), the
hypothesis on the value through `failure_le` (`Co/Bridge/Value.lean`). The result is `soundness`,
and its packaging as the canonical-line theorem of `M`, `soundLidtIn_of_isDyadicPair :
SoundLidtIn M` (`Co/Chain/Defs.lean`).

**Departures from the matrix statements.** `soundness` takes `hM : M.IsDyadicPair` and
`hd : 1 ≤ d`, which the port's main theorem needs (`Co/Test/MainTheorem/MainFormal`); its
measurements are single POVMs of the players' algebras with `IsPVMIn` of their operators, as in
`SoundLidtIn`, where the matrix one returns matrix projective measurements over the one-point
question set `Unit`; its error is `M.inconsistency`. `ofProjMeas` is accordingly a `POVMIn`, and
its projectivity is the separate `ofProjMeas_isPVMIn`. The point and evaluation readings are
`pointPOVMAIn`, `pointPOVMBIn` and `evalPOVMIn` of `Co/Chain/Defs.lean`.

**Reused by import.** The classical declarations of the matrix bridge (`lidtParams`, `enc`,
`encP`, `decP_encP`, `pointEquiv`, `scalarEquiv`, `lowIndDegEquiv`, `lowIndDegEquiv_apply_encP`,
`enc_injective`) are named through an explicit `open MIPRE.LIDT.Bridge (…)` list, which names none
of the declarations redeclared here. `mainFormalError_eq` is classical too, but is restated here
under its name rather than imported from the matrix `Bridge/Main.lean`.

## Not ported

Every declaration of the matrix bridge is redeclared here under its name, for a bipartite model:
`ofProjMeas` (a `POVMIn`, with the departure above), `ofProjMeas_M` (as `ofProjMeas_op`, the
operators of a `POVMIn` being `op`), `mainFormalError_eq`, `pointPOVMA_val`, `pointPOVMB_val`,
`evalPOVM_val` and `soundness`.

## New here

- `ofProjMeas_isPVMIn`: the projectivity of `ofProjMeas G`, from that of `G`.
- `soundLidtIn_of_isDyadicPair`: `soundness` as `SoundLidtIn M`.
-/

universe u

open MIPStarRE.LDT (uniformDistribution)
open MIPRE.LIDT.Bridge (lidtParams enc encP decP_encP pointEquiv scalarEquiv lowIndDegEquiv
  lowIndDegEquiv_apply_encP enc_injective)
open MIPRE.LIDT.Co.Chain (pointPOVMAIn pointPOVMBIn evalPOVMIn SoundLidtIn)

noncomputable section

namespace MIPRE.LIDT.Co.Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## Polynomial measurements as POVMs -/

section OfProjMeas

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- A projective measurement of the port with polynomial outcomes, as a POVM with outcomes in
`LowIndDegPoly` (the outcomes relabelled along `lowIndDegEquiv`). Its projectivity is
`ofProjMeas_isPVMIn`. -/
def ofProjMeas (G : ProjMeas (MIPStarRE.LDT.Polynomial (lidtParams F m d)) R) :
    POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) R where
  mats c := ⟨G.outcome (lowIndDegEquiv c), G.outcome_hermitian _⟩
  nonneg c := G.outcome_pos _
  normalized := Subtype.ext <| by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (lowIndDegEquiv.sum_comp fun g => G.outcome g).trans G.sum_eq

/-- The operators of `ofProjMeas G` are the outcome operators of `G`. -/
@[simp] theorem ofProjMeas_op (G : ProjMeas (MIPStarRE.LDT.Polynomial (lidtParams F m d)) R)
    (c : LowIndDegPoly) : (ofProjMeas G).op c = G.outcome (lowIndDegEquiv c) := rfl

/-- `ofProjMeas G` is projective when the outcome operators of `G` form a projective
measurement of the repository. -/
theorem ofProjMeas_isPVMIn {G : ProjMeas (MIPStarRE.LDT.Polynomial (lidtParams F m d)) R}
    (h : IsPVMIn G.outcome) : IsPVMIn (ofProjMeas G).op where
  star_eq _ := h.star_eq _
  idem _ := h.idem _
  sum_eq_one := (lowIndDegEquiv.sum_comp G.outcome).trans h.sum_eq_one
  orthogonal hab := h.orthogonal (lowIndDegEquiv.injective.ne hab)

end OfProjMeas

omit [DecidableEq F] in
/-- The error bounds of the two developments agree. -/
theorem mainFormalError_eq (k : ℕ) (ε : ℝ) :
    MIPStarRE.LDT.Test.mainFormalError (lidtParams F m d) k ε =
      lidtError m d (Fintype.card F) k ε := by
  unfold MIPStarRE.LDT.Test.mainFormalError lidtError
  rw [neg_div]
  try rfl

/-! ## The readings of the conclusions -/

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder ℬ]
  [StarOrderedRing ℬ] {M : MIPRE.BipartiteModel.{u} 𝒞 𝒜 ℬ}

/-- The point POVMs of player A, as outcomes of the induced strategy's point measurements. -/
theorem pointPOVMA_val (S : M.ProjStrat (lidtGame F m d)) (u : Point F m) (a : F) :
    (pointPOVMAIn S u).op a =
      ((toCoProjStrat S).pointMeasurementA (encP u)).toSubMeas.outcome (enc a) := by
  classical
  rw [pointMeasA_eq, SubMeas.postprocess_outcome]
  simp only [pointPOVMAIn, POVMIn.map_op, decP_encP, toProjMeas_outcome]
  refine Finset.sum_congr (Finset.filter_congr fun ans _ => ?_) fun _ _ => rfl
  exact enc_injective.eq_iff.symm

/-- The point POVMs of player B, as outcomes of the induced strategy's point measurements. -/
theorem pointPOVMB_val (S : M.ProjStrat (lidtGame F m d)) (u : Point F m) (a : F) :
    (pointPOVMBIn S u).op a =
      ((toCoProjStrat S).pointMeasurementB (encP u)).toSubMeas.outcome (enc a) := by
  classical
  rw [pointMeasB_eq, SubMeas.postprocess_outcome]
  simp only [pointPOVMBIn, POVMIn.map_op, decP_encP, toProjMeas_outcome]
  refine Finset.sum_congr (Finset.filter_congr fun ans _ => ?_) fun _ _ => rfl
  exact enc_injective.eq_iff.symm

/-- Evaluation of a converted global measurement, as the port's evaluation family. -/
theorem evalPOVM_val {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (G : ProjMeas (MIPStarRE.LDT.Polynomial (lidtParams F m d)) R) (u : Point F m) (a : F) :
    (evalPOVMIn (ofProjMeas G) u).op a =
      (polynomialEvaluationFamily (lidtParams F m d) G.toSubMeas (encP u)).outcome (enc a) := by
  classical
  change _ = (postprocess G.toSubMeas fun g => g (encP u)).outcome (enc a)
  rw [SubMeas.postprocess_outcome]
  simp only [evalPOVMIn, POVMIn.map_op, ofProjMeas_op]
  refine Finset.sum_equiv lowIndDegEquiv (fun c => ?_) fun c _ => rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, lowIndDegEquiv_apply_encP]
  exact enc_injective.eq_iff.symm

/-! ## The soundness theorem -/

/-- **The soundness theorem in a dyadic pair**, assembled from the port's main theorem: a
projective strategy for the `(m, q, d)`-low individual degree test with value at least `1 - ε`
has projective measurements `GA` in `𝒜` and `GB` in `ℬ`, with outcomes the polynomials of
individual degree `d`, consistent with the other player's point measurements and with each other,
up to `lidtError m d q k ε`.

Departure from the matrix statement: `hM` and `hd` are new (the port's main theorem needs them),
and the measurements are POVMs of the players' algebras with `IsPVMIn` operators. -/
theorem soundness (hM : M.IsDyadicPair) (S : M.ProjStrat (lidtGame F m d)) (hd : 1 ≤ d) (ε : ℝ)
    (hS : 1 - ε ≤ S.value) (k : ℕ) (hk : 400 * m * d ≤ k) (hk0 : 0 < k) :
    ∃ GA : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) 𝒜,
    ∃ GB : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) ℬ,
      IsPVMIn GA.op ∧ IsPVMIn GB.op ∧
      M.inconsistency (uniform (Point F m)) (pointPOVMAIn S) (evalPOVMIn GB)
          ≤ lidtError m d (Fintype.card F) k ε ∧
        M.inconsistency (uniform (Point F m)) (evalPOVMIn GA) (pointPOVMBIn S)
          ≤ lidtError m d (Fintype.card F) k ε ∧
        M.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
          ≤ lidtError m d (Fintype.card F) k ε := by
  obtain ⟨GA, GB, hA, hB, h1, h2, h3⟩ := MIPRE.LIDT.Co.Test.mainFormal_isPVMIn (lidtParams F m d)
    (toCoProjStrat S) hM hd ε ((failure_le S).trans (by linarith)) k hk hk0
  rw [mainFormalError_eq] at h1 h2 h3
  refine ⟨ofProjMeas GA, ofProjMeas GB, ofProjMeas_isPVMIn hA, ofProjMeas_isPVMIn hB, ?_, ?_, ?_⟩
  · rw [inconsistency_eq_bipartiteConsError S.ψ_unit pointEquiv scalarEquiv (pointPOVMAIn S)
      (evalPOVMIn (ofProjMeas GB))
      (IdxProjMeas.toIdxSubMeas (toCoProjStrat S).pointMeasurementA)
      (polynomialEvaluationFamily (lidtParams F m d) GB.toSubMeas)
      (fun x => ((toCoProjStrat S).pointMeasurementA x).total_eq_one) (fun _ => GB.total_eq_one)
      (pointPOVMA_val S) (evalPOVM_val GB)]
    exact h1
  · rw [inconsistency_eq_bipartiteConsError S.ψ_unit pointEquiv scalarEquiv
      (evalPOVMIn (ofProjMeas GA)) (pointPOVMBIn S)
      (polynomialEvaluationFamily (lidtParams F m d) GA.toSubMeas)
      (IdxProjMeas.toIdxSubMeas (toCoProjStrat S).pointMeasurementB)
      (fun _ => GA.total_eq_one) (fun x => ((toCoProjStrat S).pointMeasurementB x).total_eq_one)
      (evalPOVM_val GA) (pointPOVMB_val S)]
    exact h2
  · rw [inconsistency_eq_bipartiteConsError S.ψ_unit (Equiv.refl Unit) lowIndDegEquiv
      (fun _ => ofProjMeas GA) (fun _ => ofProjMeas GB)
      (constSubMeasFamily GA.toSubMeas) (constSubMeasFamily GB.toSubMeas)
      (fun _ => GA.total_eq_one) (fun _ => GB.total_eq_one) (fun _ _ => rfl) (fun _ _ => rfl)]
    exact h3

/-- **The canonical-line theorem holds in every dyadic pair**: `soundness`, read as
`SoundLidtIn M` (`Co/Chain/Defs.lean`). -/
theorem soundLidtIn_of_isDyadicPair (hM : M.IsDyadicPair) : SoundLidtIn M :=
  fun hd S ε hS k hk hk0 => soundness hM S hd ε hS k hk hk0

end MIPRE.LIDT.Co.Bridge

end

end
