/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Chain.Defs
public import MIPRE.Background.LIDT.Adapter.Reduction
public import MIPRE.Foundations.ModelEmbedding

@[expose] public section

/-!
# The model chain, part 3: the seeded test at one codeword, by reduction

The model counterpart of the repository's `MIPRE/Background/LIDT/Adapter/Reduction.lean` (not a
vendored file: its matrix statements serve the tensor instance and stay), in the port of
`planning/c6b-plan.md` (milestone M14, unit M14-4). It is the `ldc = 1` case of
`thm:lidt-cl-soundness` in any bipartite model `M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with the instance
set of `MIPRE.LIDT.Simul.SoundIn`, from the canonical-line theorem in `M`,
`MIPRE.LIDT.Co.Chain.SoundLidtIn M` (`Co/Chain/Defs.lean`), taken as a hypothesis.

The argument is the matrix one:

* a projective strategy `S` for `clGame` with `ldc = 1` is played as one for `lidtGame`
  (`adapted`), through `MIPRE.BipartiteModel.ProjStrat.adapt`, reindexing the questions along
  the classical `qmapS` and coarse-graining the answers along `amap`;
* the classical `hD_qmap` and `pushforward_le` make the averaging lemma
  `MIPRE.BipartiteModel.exists_one_sub_povmValue_adapt_le` produce a seed whose adapted strategy
  fails at most `3m` times as often;
* `SoundLidtIn M` applies to it, at `hd : 1 ≤ d`, and returns two projective measurements of
  polynomials;
* the three conclusions are carried back through the coordinate reversal: on the questions by
  `revPoint`, which preserves the uniform distribution (`inconsistency_uniform_comp`), on the
  polynomials by `revPolyEquiv` (`revMeas`, `MIPRE.BipartiteModel.inconsistency_map_equiv`).

`clSoundness_ldc_one` states the conclusion with the canonical-line error, and
`clSoundness_ldc_one_deltaCL` with the blueprint's `δ_CL`, through the classical
`lidtError_le_deltaCL` and the choice `k = clK m d`.

The conclusions are read with `CL.pointPOVMAIn S` and `CL.pointPOVMBIn S`, the model forms of
`MIPRE.LIDT.CL.pointPOVMA`, `pointPOVMB`: the point measurements with outcomes in `F` (the tuple
readings `MIPRE.LIDT.Simul.tuplePOVMAIn` at `r = 1` have outcomes in `Fin 1 → F`, and do not
serve).

**Reused by import.** The classical content of `Adapter/*` is named through explicit `open` lists:
`revPoint`, `revPolyEquiv`, `eval_revPoly`, `Seed`, `qmapS`, `qmapS_point`, `amap`,
`toValue_amap_point`, `hD_qmap`, `pushforward_le`, `nonempty_seed` (namespace
`MIPRE.LIDT.Adapter`); `lidtError_le_deltaCL`, `deltaCL`, `clK`, `le_clK` and `clK_pos` are in
`MIPRE.LIDT` and need no `open`.

## Not ported

The model forms of `adapted`, `revMeas`, `clSoundness_ldc_one` and `clSoundness_ldc_one_deltaCL`
are declared here under their names. `clSoundness_ldc_one` takes `SoundLidtIn M` and `1 ≤ d` (the
hypothesis of `SoundLidtIn`) in addition to the matrix hypotheses, and its measurements are
`POVMIn`s with `IsPVMIn` carried beside them. Of the rest:

- `revExp`, `revPoly`, `eval_revPoly`, `revPolyEquiv`, `toValue_amap_point`: classical, imported.
- `val_mats_map`: the operators of a matrix coarse-graining; for `POVMIn` it is
  `MIPRE.POVMIn.map_op`.
- `sum_filter_comp`: composing two matrix coarse-grainings; for `POVMIn` it is
  `MIPRE.POVMIn.map_map`.
- `val_mats_pointPOVMA_adapted`, `val_mats_pointPOVMB_adapted`: replaced by `pointPOVMAIn_adapted`,
  `pointPOVMBIn_adapted`, equalities of POVMs rather than of their operators.
- `val_mats_evalPOVM_revMeas`: replaced by `evalPOVMIn_revMeas`, likewise.

## New here

- `CL.pointPOVMAIn`, `CL.pointPOVMBIn`: above.
- `pointPOVMAIn_adapted`, `pointPOVMBIn_adapted`, `evalPOVMIn_revMeas`: above.
- `revMeas_isPVMIn`: the reversal of a projective measurement is projective.
- `inconsistency_uniform_comp`: relabelling the questions along a bijection keeps the
  inconsistency on the uniform distribution (the question half of the matrix
  `MIPRE.inconsistency_congr`).
-/

open MIPRE.LIDT.Adapter (revPoint revPoint_revPoint revPolyEquiv eval_revPoly Seed qmapS
  qmapS_point amap toValue_amap_point hD_qmap pushforward_le nonempty_seed)
open MIPRE.LIDT.CL (clGame)

noncomputable section

namespace MIPRE.LIDT.Co.Chain

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-! ## The readings of the conclusions -/

namespace CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {hm : m ∣ Fintype.card F}

/-- The first player's point measurements of a projective strategy for the seeded test with one
codeword, as POVMs with outcomes in `F` (the model form of `MIPRE.LIDT.CL.pointPOVMA`). -/
def pointPOVMAIn (S : M.ProjStrat (clGame (d := d) (ldc := 1) hm)) (u : Point F m) :
    POVMIn F 𝒜 :=
  (S.PA (.point u)).map MIPRE.LIDT.CL.Answer.toValue

/-- The second player's point measurements, as for `pointPOVMAIn` (the model form of
`MIPRE.LIDT.CL.pointPOVMB`). -/
def pointPOVMBIn (S : M.ProjStrat (clGame (d := d) (ldc := 1) hm)) (u : Point F m) :
    POVMIn F ℬ :=
  (S.PB (.point u)).map MIPRE.LIDT.CL.Answer.toValue

end CL

/-! ## The adapted strategy and its point measurements -/

section Adapted

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {hm : m ∣ Fintype.card F}

/-- The strategy the adapter builds, for one member `σc` of the averaging family: `S` played on
the canonical-line test through `qmapS` and `amap`. -/
def adapted (σc : Seed F m) (S : M.ProjStrat (clGame (d := d) (ldc := 1) hm)) :
    M.ProjStrat (lidtGame F m d) :=
  S.adapt (lidtGame F m d) (qmapS hm σc) (qmapS hm σc)
    (fun x' => amap (σc.2 : F) x') (fun y' => amap (σc.2 : F) y')

/-- **A's point measurement of the adapted strategy is A's point measurement of the seeded
strategy at the reversed point.** -/
theorem pointPOVMAIn_adapted (σc : Seed F m) (S : M.ProjStrat (clGame (d := d) (ldc := 1) hm))
    (u : Point F m) : CL.pointPOVMAIn S u = pointPOVMAIn (adapted σc S) (revPoint u) := by
  show _ = ((S.PA (qmapS hm σc (.point (revPoint u)))).map _).map _
  rw [POVMIn.map_map, qmapS_point, revPoint_revPoint, CL.pointPOVMAIn]
  congr 1
  funext a
  exact (toValue_amap_point _ _ a).symm

/-- **B's point measurement, likewise.** -/
theorem pointPOVMBIn_adapted (σc : Seed F m) (S : M.ProjStrat (clGame (d := d) (ldc := 1) hm))
    (u : Point F m) : CL.pointPOVMBIn S u = pointPOVMBIn (adapted σc S) (revPoint u) := by
  show _ = ((S.PB (qmapS hm σc (.point (revPoint u)))).map _).map _
  rw [POVMIn.map_map, qmapS_point, revPoint_revPoint, CL.pointPOVMBIn]
  congr 1
  funext a
  exact (toValue_amap_point _ _ a).symm

end Adapted

/-! ## Reversing the low-degree measurements -/

section Reversal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
  {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- The reversal of a measurement with polynomial outcomes: its outcomes relabelled along
`revPolyEquiv`. -/
def revMeas (G : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) R) :
    POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) R :=
  G.map revPolyEquiv

omit [Field F] in
/-- The reversal of a projective measurement is projective. -/
theorem revMeas_isPVMIn {G : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) R}
    (hG : IsPVMIn G.op) : IsPVMIn (revMeas G).op :=
  POVMIn.isPVMIn_map hG _

/-- **Evaluating the reversal is evaluating at the reversed point.** -/
theorem evalPOVMIn_revMeas (G : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) R)
    (u : Point F m) : evalPOVMIn (revMeas G) u = evalPOVMIn G (revPoint u) := by
  rw [evalPOVMIn, evalPOVMIn, revMeas, POVMIn.map_map]
  congr 1
  funext g
  exact eval_revPoly g u

end Reversal

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **Relabelling the questions along a bijection keeps the inconsistency** on the uniform
distribution. -/
theorem inconsistency_uniform_comp {X Λ : Type*} [Fintype X] [Fintype Λ] [DecidableEq Λ]
    (e : X ≃ X) (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M.inconsistency (uniform X) (fun x => P (e x)) (fun x => Q (e x))
      = M.inconsistency (uniform X) P Q :=
  e.sum_comp fun x => uniform X x * ∑ a, ∑ b,
    if a = b then 0 else M.bornProb ((P x).op a) ((Q x).op b)

/-! ## The reduction -/

section Reduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {hm : m ∣ Fintype.card F}

/-- **Soundness of the seeded CL test at `ldc = 1` in the model `M`, by reduction to the
canonical-line test** (the model form of `MIPRE.LIDT.Adapter.clSoundness_ldc_one`). If the
canonical-line theorem holds in `M`, a projective strategy for `clGame` passing with probability
at least `1 - ε` has point measurements consistent, up to `lidtError m d q k (3m ε)`, with the
evaluations of a projective measurement of polynomials of individual degree `d` held by the other
player, the two measurements consistent with each other; `k ≥ 400 m d` is free. -/
theorem clSoundness_ldc_one (h : SoundLidtIn M) (S : M.ProjStrat (clGame (d := d) (ldc := 1) hm))
    (ε : ℝ) (hS : 1 - ε ≤ S.value) (hd : 1 ≤ d) (k : ℕ) (hk : 400 * m * d ≤ k) (hk0 : 0 < k) :
    ∃ GA : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) 𝒜,
    ∃ GB : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) ℬ,
      IsPVMIn GA.op ∧ IsPVMIn GB.op ∧
      M.inconsistency (uniform (Point F m)) (CL.pointPOVMAIn S) (evalPOVMIn GB)
          ≤ lidtError m d (Fintype.card F) k (3 * m * ε) ∧
        M.inconsistency (uniform (Point F m)) (evalPOVMIn GA) (CL.pointPOVMBIn S)
          ≤ lidtError m d (Fintype.card F) k (3 * m * ε) ∧
        M.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
          ≤ lidtError m d (Fintype.card F) k (3 * m * ε) := by
  classical
  have : Nonempty (Seed F m) := nonempty_seed hm
  -- choose the family member the derandomization provides
  obtain ⟨σc, hval⟩ := M.exists_one_sub_povmValue_adapt_le S.PA S.PB S.ψ_unit (lidtGame F m d)
    (fun σc : Seed F m => qmapS hm σc) (fun σc : Seed F m => qmapS hm σc)
    (fun (σc : Seed F m) (x' : Question F m) => amap (σc.2 : F) x')
    (fun (σc : Seed F m) (y' : Question F m) => amap (σc.2 : F) y') (3 * m)
    (fun σc x' y' a b hμ0 hacc => hD_qmap hm σc.1 σc.2.2 x' y' hμ0 a b hacc)
    (fun x y => pushforward_le (d := d) (ldc := 1) hm x y)
  -- the adapted strategy is good
  have hval' : 1 - (adapted σc S).value ≤ 3 * (m : ℝ) * (1 - S.value) := hval
  have hS' : 1 - 3 * (m : ℝ) * ε ≤ (adapted σc S).value := by
    have hm0 : (0 : ℝ) ≤ 3 * m := by positivity
    nlinarith [hval', hS]
  obtain ⟨GA, GB, hA, hB, h1, h2, h3⟩ := h hd (adapted σc S) (3 * (m : ℝ) * ε) hS' k hk hk0
  refine ⟨revMeas GA, revMeas GB, revMeas_isPVMIn hA, revMeas_isPVMIn hB, ?_, ?_, ?_⟩
  · rw [funext (pointPOVMAIn_adapted σc S), funext (evalPOVMIn_revMeas GB),
      inconsistency_uniform_comp revPoint (pointPOVMAIn (adapted σc S)) (evalPOVMIn GB)]
    exact h1
  · rw [funext (pointPOVMBIn_adapted σc S), funext (evalPOVMIn_revMeas GA),
      inconsistency_uniform_comp revPoint (evalPOVMIn GA) (pointPOVMBIn (adapted σc S))]
    exact h2
  · exact (M.inconsistency_map_equiv revPolyEquiv (uniform Unit) (fun _ => GA)
      (fun _ => GB)).trans_le h3

/-- **The `ldc = 1` case of `thm:lidt-cl-soundness` in the model `M`** (the model form of
`MIPRE.LIDT.Adapter.clSoundness_ldc_one_deltaCL`): the conclusion of `clSoundness_ldc_one` with
the blueprint's error `δ_CL` in place of the canonical-line one, at the sampling parameter
`clK m d` (`lidtError_le_deltaCL`). -/
theorem clSoundness_ldc_one_deltaCL (h : SoundLidtIn M)
    (S : M.ProjStrat (clGame (d := d) (ldc := 1) hm)) (ε : ℝ) (hε : 0 ≤ ε)
    (hS : 1 - ε ≤ S.value) (hm1 : 1 ≤ m) (hd : 1 ≤ d) :
    ∃ GA : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) 𝒜,
    ∃ GB : POVMIn (LowIndDegPoly (F := F) (m := m) (d := d)) ℬ,
      IsPVMIn GA.op ∧ IsPVMIn GB.op ∧
      M.inconsistency (uniform (Point F m)) (CL.pointPOVMAIn S) (evalPOVMIn GB)
          ≤ deltaCL (Fintype.card F) m d ε ∧
        M.inconsistency (uniform (Point F m)) (evalPOVMIn GA) (CL.pointPOVMBIn S)
          ≤ deltaCL (Fintype.card F) m d ε ∧
        M.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
          ≤ deltaCL (Fintype.card F) m d ε := by
  obtain ⟨GA, GB, hA, hB, h1, h2, h3⟩ :=
    clSoundness_ldc_one h S ε hS hd (clK m d) (le_clK m d hm1) (clK_pos m d hm1)
  have hle := lidtError_le_deltaCL m d (Fintype.card F) hm1 hd ε hε
  exact ⟨GA, GB, hA, hB, h1.trans hle, h2.trans hle, h3.trans hle⟩

end Reduction

end MIPRE.LIDT.Co.Chain

end

end
