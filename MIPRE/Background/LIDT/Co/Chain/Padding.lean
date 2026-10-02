/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Chain.Extraction
public import MIPRE.Background.LIDT.Co.Chain.Reduction
public import MIPRE.Background.LIDT.Padding

@[expose] public section

/-!
# The model chain, part 4: the padded strategy

The model counterpart of the strategy section of the repository's
`MIPRE/Background/LIDT/Padding.lean` (blueprint `lem:lidt-ldc-adapter`; not a vendored file: its
matrix statements serve the tensor instance and stay), in the port of `planning/c6b-plan.md`
(milestone M14, unit M14-4). A projective strategy `S`, in any bipartite model
`M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with the instance set of `MIPRE.LIDT.Simul.SoundIn`, for the
seeded test with `r` codewords in `m` variables is played as one for the seeded test with one
codeword in `K + m` variables (`padded`), through `MIPRE.BipartiteModel.ProjStrat.adapt` along the
classical question map `qmap` and answer map `rmap`, for a seed offset `σ`.

* `exists_padded_value`: some offset makes the padded strategy fail at most `9 (K + 1)` times as
  often as `S`, by the averaging lemma `MIPRE.BipartiteModel.exists_one_sub_povmValue_adapt_le`
  with the classical acceptance transfer `clGame_D_rmap` and push-forward bound `sum_mu_qmap_le`.
* `pointPOVMA_padded`, `pointPOVMB_padded`: the padded strategy's point measurements
  (`CL.pointPOVMAIn`, `CL.pointPOVMBIn` of `Co/Chain/Reduction.lean`) are the combined ones,
  `combPOVM` of `Co/Chain/Extraction.lean` applied to the tuple readings
  `MIPRE.LIDT.Simul.tuplePOVMAIn`, `tuplePOVMBIn` of `S`.

The parameter `hd : 1 ≤ d` is passed straight through: `d` is the same on both sides of the
padding.

**Reused by import.** Everything before the strategy section of `Padding.lean` is classical: the
decider on a sample, the geometry of lines and blocks, the question and answer maps, the
acceptance transfer and the count. It is named through an explicit
`open MIPRE.LIDT.Simul (…)` list: `qmap`, `rmap`, `clGame_D_rmap`, `sum_mu_qmap_le`,
`eval_linPoly_padB`, and the model readings `tuplePOVMAIn`, `tuplePOVMBIn` of
`ModelSoundness.lean`.

## Not ported

`padded`, `exists_padded_value`, `pointPOVMA_padded` and `pointPOVMB_padded` are declared here
under their names. Of the rest of `Padding.lean`:

- `tuplePOVMA`, `tuplePOVMB`: replaced by the existing model readings
  `MIPRE.LIDT.Simul.tuplePOVMAIn`, `tuplePOVMBIn` (`ModelSoundness.lean`).
- `toPOVM_mergeAt`: the matrix adapted strategy is built with `ProjectiveMeasurement.mergeAt`;
  the model's `ProjStrat.adapt` is the coarse-graining `POVMIn.map` by definition, so there is
  nothing to convert.
- the declarations of the sections `Interface`, `Lines`, `Blocks`, `Maps`, `Answers`, `Transfer`,
  `Accept` and `Count`: classical, imported.

## New here

Nothing: every declaration here is the model form of a matrix one.
-/

open MIPRE.LIDT.Simul (qmap rmap clGame_D_rmap sum_mu_qmap_le eval_linPoly_padB tuplePOVMAIn
  tuplePOVMBIn)
open MIPRE.LIDT.CL (clGame card_div_pos)

noncomputable section

namespace MIPRE.LIDT.Co.Chain

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

/-- The padded strategy for the seeded test with one codeword in `K + m` variables: `S` played
through the question map `qmap` at the seed offset `σ` and the answer map `rmap`. -/
def padded (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) (σ : Fin (Fintype.card F / m)) :
    M.ProjStrat (clGame (d := d) (ldc := 1) hM) :=
  S.adapt (clGame (d := d) (ldc := 1) hM) (qmap hm hM σ) (qmap hm hM σ) (rmap hM hr) (rmap hM hr)

/-- **The padded adapter loses a factor `9 (K + 1)`** (blueprint `lem:lidt-ldc-adapter`): some
seed offset makes the padded strategy fail at most `9 (K + 1)` times as often as `S`. -/
theorem exists_padded_value (hd : 1 ≤ d) (hK : 1 ≤ K)
    (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) :
    ∃ σ : Fin (Fintype.card F / m),
      1 - (padded hm hM hr S σ).value ≤ 9 * (K + 1) * (1 - S.value) := by
  have : Nonempty (Fin (Fintype.card F / m)) := ⟨⟨0, card_div_pos hm⟩⟩
  exact M.exists_one_sub_povmValue_adapt_le S.PA S.PB S.ψ_unit (clGame (d := d) (ldc := 1) hM)
    (fun σ => qmap hm hM σ) (fun σ => qmap hm hM σ) (fun _ => rmap hM hr) (fun _ => rmap hM hr)
    (9 * (K + 1)) (fun σ x y a b hμ h => clGame_D_rmap hm hM hr hd hK σ x y a b hμ h)
    (fun x y => sum_mu_qmap_le hm hM x y)

/-- **The padded strategy's point measurements are the combined ones**: at the padded point
`(x, y)`, measure the original point measurement at `y` and answer `∑_{k<r} x_k b_k`. -/
theorem pointPOVMA_padded (hd : 1 ≤ d) (S : M.ProjStrat (clGame (d := d) (ldc := r) hm))
    (σ : Fin (Fintype.card F / m)) (u : Point F (K + m)) :
    CL.pointPOVMAIn (padded hm hM hr S σ) u = combPOVM hd (tuplePOVMAIn hm S) u := by
  rw [CL.pointPOVMAIn, combPOVM, tuplePOVMAIn, POVMIn.map_map]
  show ((S.PA (qmap hm hM σ (.point u))).map (rmap hM hr (.point u))).map _ = _
  rw [POVMIn.map_map]
  congr 1
  funext a
  rw [eval_linPoly_padB hd hr]
  rfl

/-- The same for player B. -/
theorem pointPOVMB_padded (hd : 1 ≤ d) (S : M.ProjStrat (clGame (d := d) (ldc := r) hm))
    (σ : Fin (Fintype.card F / m)) (u : Point F (K + m)) :
    CL.pointPOVMBIn (padded hm hM hr S σ) u = combPOVM hd (tuplePOVMBIn hm S) u := by
  rw [CL.pointPOVMBIn, combPOVM, tuplePOVMBIn, POVMIn.map_map]
  show ((S.PB (qmap hm hM σ (.point u))).map (rmap hM hr (.point u))).map _ = _
  rw [POVMIn.map_map]
  congr 1
  funext a
  rw [eval_linPoly_padB hd hr]
  rfl

end MIPRE.LIDT.Co.Chain

end

end
