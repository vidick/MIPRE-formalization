/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Chain.Padding
public import MIPRE.Background.LIDT.ModelSoundness

@[expose] public section

/-!
# The model chain, part 5: the simultaneous contract in a model

The model counterpart of the repository's `MIPRE/Background/LIDT/Simultaneous.lean` (blueprint
`thm:lidt-cl-soundness`, through `lem:lidt-ldc` and `lem:lidt-ldc-error`; not a vendored file: its
matrix statement `MIPRE.LIDT.Simul.clSoundness` serves the tensor instance `soundIn_tensor` and
stays), in the port of `planning/c6b-plan.md` (milestone M14, unit M14-5). It closes the model
chain: in any bipartite model `M : MIPRE.BipartiteModel 𝒞 𝒜 ℬ` with the instance set of
`MIPRE.LIDT.Simul.SoundIn`, **the canonical-line theorem in `M` implies the simultaneous
contract in `M`** (`soundIn_of_soundLidtIn : SoundLidtIn M → SoundIn M`).

The proof is that of `clSoundness`, step for step. A strategy for the seeded test with `r`
codewords in `m` variables is played as one with a single codeword in `K + m` variables
(`padded`, `Co/Chain/Padding.lean`), failing at most `9 (K + 1)` times as often; the
single-codeword theorem `clSoundness_ldc_one_deltaCL` (`Co/Chain/Reduction.lean`) applies to it,
from `SoundLidtIn M`; and `extracted_conclusions` (`Co/Chain/Extraction.lean`) reads `r`-tuples of
polynomials in the original variables off its measurements (`clSoundness_padded`). With
`K + m = padM m r` the error is absorbed into `δ_sim` by the classical `deltaCL_padded_le`; when
`m + r > q` there is no room to pad, `δ_sim ≥ 1` (`one_le_deltaSim`), and the one-outcome
measurements `constPM` do, since every inconsistency at a unit state is at most one
(`inconsistency_le_one`).

**Reused by import.** The classical part of `Simultaneous.lean` (the choice of `M`, the error
`δ_sim` and its bounds) is named through an explicit `open MIPRE.LIDT.Simul (…)` list: `padM`,
`le_padM`, `padM_le_mul`, `padM_dvd`, `deltaSim`, `deltaCL_padded_le`, `one_le_deltaSim`,
`sum_uniform_one`, and `SoundIn`, `tuplePOVMAIn`, `tuplePOVMBIn`, `evalTuplePOVMIn` of
`ModelSoundness.lean`.

## Not ported

`clSoundness_padded`, `constPM` and `inconsistency_le_one` are declared here under their names,
for POVMs in the algebras of `M`; `clSoundness_padded` takes `SoundLidtIn M`, and its
measurements are `POVMIn`s with `IsPVMIn` carried beside them. Of the rest of `Simultaneous.lean`:

- `clSoundness`: replaced by `soundIn_of_soundLidtIn`, whose conclusion is `SoundIn M`, the
  statement of `clSoundness` read in `M`.
- `padM`, `le_padM`, `padM_le`, `padM_le_mul`, `padM_dvd`, `simA`, `deltaSim`, `forty_le_simA`,
  `clA_add_one_le_simA`, `rpow_le_rpow_simA`, `deltaCL_padded_le`, `one_le_deltaSim`: classical,
  imported.

## New here

- `constPM_isPVMIn`: the one-outcome measurement is projective (the matrix `constPM` is a
  `ProjectiveMeasurement`, so its projectivity is a field there).
- `soundIn_of_soundLidtIn`: above.
-/

open MIPRE.LIDT.Simul (padM le_padM padM_le_mul padM_dvd deltaSim deltaCL_padded_le
  one_le_deltaSim sum_uniform_one SoundIn tuplePOVMAIn tuplePOVMBIn evalTuplePOVMIn)
open MIPRE.LIDT.CL (clGame)

noncomputable section

namespace MIPRE.LIDT.Co.Chain

open Finset

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-! ## The padded chain -/

section Padded

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]

/-- **The simultaneous contract in the model `M`, at a padding `K ≥ r`** (the model form of
`MIPRE.LIDT.Simul.clSoundness_padded`): if the canonical-line theorem holds in `M`, a projective
strategy for the seeded test with `r` codewords passing with probability at least `1 - ε` admits
projective measurements of `r`-tuples of polynomials, with error
`δ_CL(9 (K + 1) ε, q, K + m, d)` plus `(K + m) d / q` on the two point conclusions. -/
theorem clSoundness_padded (h : SoundLidtIn M) [NeZero (K + m)] (hm : m ∣ Fintype.card F)
    (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) (ε : ℝ) (hε : 0 ≤ ε)
    (hS : 1 - ε ≤ S.value) :
    ∃ GA : POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) 𝒜,
    ∃ GB : POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) ℬ,
      IsPVMIn GA.op ∧ IsPVMIn GB.op ∧
      M.inconsistency (uniform (Point F m)) (tuplePOVMAIn hm S) (evalTuplePOVMIn GB)
          ≤ deltaCL (Fintype.card F) (K + m) d (9 * (K + 1) * ε)
            + (K + m) * d / Fintype.card F ∧
        M.inconsistency (uniform (Point F m)) (evalTuplePOVMIn GA) (tuplePOVMBIn hm S)
          ≤ deltaCL (Fintype.card F) (K + m) d (9 * (K + 1) * ε)
            + (K + m) * d / Fintype.card F ∧
        M.inconsistency (uniform Unit) (fun _ => GA) (fun _ => GB)
          ≤ deltaCL (Fintype.card F) (K + m) d (9 * (K + 1) * ε) := by
  obtain ⟨σ, hσ⟩ := exists_padded_value hm hM hr hd hK S
  have hS' : 1 - 9 * (K + 1) * ε ≤ (padded hm hM hr S σ).value := by
    have : (0 : ℝ) ≤ 9 * (K + 1) := by positivity
    nlinarith
  obtain ⟨GA', GB', hA, hB, h1, h2, h3⟩ := clSoundness_ldc_one_deltaCL h
    (padded hm hM hr S σ) (9 * (K + 1) * ε) (by positivity) hS' (by omega) hd
  rw [funext (pointPOVMA_padded hm hM hr hd S σ)] at h1
  rw [funext (pointPOVMB_padded hm hM hr hd S σ)] at h2
  obtain ⟨e1, e2, e3⟩ := extracted_conclusions hd hr S.ψ_unit (tuplePOVMAIn hm S)
    (tuplePOVMBIn hm S) GA' GB' h1 h2 h3
  exact ⟨extractPM hd hr GA', extractPM hd hr GB', extractPM_isPVMIn hd hr hA,
    extractPM_isPVMIn hd hr hB, e1, e2, e3⟩

end Padded

/-! ## The trivial regime -/

section Trivial

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
  {A : Type*} [Fintype A] [DecidableEq A]

/-- A measurement with a single outcome `a₀`: the identity at `a₀`, zero elsewhere. -/
def constPM (a₀ : A) : POVMIn A R where
  mats a := ⟨if a = a₀ then 1 else 0, by split_ifs <;> simp [selfAdjoint.mem_iff]⟩
  nonneg a := by
    change (0 : R) ≤ if a = a₀ then 1 else 0
    split_ifs
    · simp
    · exact le_rfl
  normalized := by
    ext
    simp

/-- The one-outcome measurement is projective. -/
theorem constPM_isPVMIn (a₀ : A) : IsPVMIn (constPM (R := R) a₀).op where
  star_eq a := (constPM a₀).star_op a
  idem a := by
    change (if a = a₀ then (1 : R) else 0) * (if a = a₀ then 1 else 0) = if a = a₀ then 1 else 0
    split_ifs <;> simp
  sum_eq_one := (constPM a₀).sum_op
  orthogonal {a b} hab := by
    change (if a = a₀ then (1 : R) else 0) * (if b = a₀ then 1 else 0) = 0
    split_ifs with ha hb
    · exact absurd (ha.trans hb.symm) hab
    all_goals simp

/-- At a unit state, the inconsistency of two families of POVMs on a uniform index is at most
one (the model form of `MIPRE.LIDT.Simul.inconsistency_le_one`). -/
theorem inconsistency_le_one {X Λ : Type*} [Fintype X] [Nonempty X] [Fintype Λ] [DecidableEq Λ]
    (hψ : ‖M.ψ‖ = 1) (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ) :
    M.inconsistency (uniform X) P Q ≤ 1 := by
  rw [inconsistency_eq_one_sub (sum_uniform_one X) hψ]
  have : 0 ≤ ∑ x, uniform X x * ∑ a, M.bornProb ((P x).op a) ((Q x).op a) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (by simp only [uniform]; positivity)
      (Finset.sum_nonneg fun a _ => M.bornProb_nonneg ((P x).op_nonneg a) ((Q x).op_nonneg a))
  linarith

end Trivial

/-! ## The theorem -/

/-- **The canonical-line theorem in a model implies the simultaneous contract in it** (the model
form of `MIPRE.LIDT.Simul.clSoundness`, blueprint `thm:lidt-cl-soundness` through `lem:lidt-ldc`):
if `SoundLidtIn M`, then `SoundIn M`. For `m + r ≤ q` the strategy is padded to
`K + m = padM m r` variables and the error of `clSoundness_padded` absorbed into `δ_sim` by
`deltaCL_padded_le`; otherwise `δ_sim ≥ 1` and the one-outcome measurements `constPM` do. -/
theorem soundIn_of_soundLidtIn (h : SoundLidtIn M) : SoundIn M := by
  intro F _ _ _ m d r k _ hq hm hd hr S ε hε hS
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  by_cases hmr : m + r ≤ Fintype.card F
  · -- pad to `K + m = padM m r`
    have hmM : m + r ≤ padM m r := le_padM m r
    set K := padM m r - m with hK
    have hKm : K + m = padM m r := by omega
    have hM : (K + m) ∣ Fintype.card F := by
      rw [hKm, hq]; exact padM_dvd (hq ▸ hmr)
    have : NeZero (K + m) := ⟨by omega⟩
    obtain ⟨GA, GB, hA, hB, h1, h2, h3⟩ := clSoundness_padded (K := K) h hm hM (by omega)
      (by omega) hd S ε hε hS
    have hle := deltaCL_padded_le (K := K) hm1 hd hr hq1 (M := K + m) (by omega)
      (by rw [hKm]; exact padM_le_mul hm1 hr) (by omega) hε
    have hext : (0 : ℝ) ≤ ((K + m : ℕ) : ℝ) * d / Fintype.card F := by positivity
    push_cast at hle hext
    exact ⟨GA, GB, hA, hB, h1.trans hle, h2.trans hle, h3.trans (by linarith)⟩
  · -- no room to pad: the bound is at least one
    push Not at hmr
    have h1 := one_le_deltaSim hm1 hd hr hq1 hmr hε
    refine ⟨constPM 0, constPM 0, constPM_isPVMIn 0, constPM_isPVMIn 0, ?_, ?_, ?_⟩ <;>
      exact (inconsistency_le_one S.ψ_unit _ _).trans h1

end MIPRE.LIDT.Co.Chain

end

end
