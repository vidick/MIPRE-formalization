/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Adapter.Reduction
import MIPRE.Foundations.RegisterReindex
import MIPRE.Foundations.StrategyDilation

/-!
# The seeded-CL adapter, part 7: strategies on arbitrary registers

`clSoundness_ldc_one_deltaCL` takes a `TensorProductStrategy`, whose registers are `Fin dA` and
`Fin dB`. The strategy the Pauli basis test's analysis hands it (`lem:qld-global-pvm`) is built
on structured registers --- the players' own spaces tensored with the expansion's ancillas and the
combining coefficients' ancillas --- and its value is a `povmValue`. This file restates the
soundness theorem for that form: a unit vector on `dA × dB`, projective measurement families on
`Matrix dA dA ℂ` and `Matrix dB dB ℂ` indexed by the seeded test's questions, and the value
hypothesis as a `povmValue`. The conclusion's two low-degree measurements live on the original
registers, and the three inconsistency bounds are stated against the original state.

The proof is bookkeeping: package the strategy with `TensorProductStrategy.ofProjective`, apply the
theorem, and read each conclusion back along `Fintype.equivFin` with `inconsistency_reindex`,
`POVM.map_reindex` and `ProjectiveMeasurement.toPOVM_map_reindex`. Nothing about the test is used.

One Lean point is worth recording. The packaged strategy's dimension `S.dA` is `Fintype.card dA`
only up to unfolding, so a rewrite that has to match `Fin S.dA` against `Fin (Fintype.card dA)`
fails. `clSoundness_ldc_one_deltaCL_transport` therefore takes the strategy abstractly, with the
register equivalences `eA : dA ≃ Fin S.dA`, `eB : dB ≃ Fin S.dB` and the identifications of its
state and measurements as hypotheses; everything is then syntactic, and the packaged strategy
supplies the hypotheses by `rfl`.
-/

namespace MIPRE.LIDT.Adapter

open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {hm : m ∣ Fintype.card F}

/-- The point measurements of a strategy for the seeded test given on arbitrary registers, as
POVMs with outcomes in `F`: the same reading as `CL.pointPOVMA`. -/
noncomputable def pointPOVM {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement (CL.Question F m) (CL.Answer F m d 1) (Matrix n n ℂ))
    (u : Point F m) : POVM F n :=
  (P.toPOVM (.point u)).map CL.Answer.toValue

omit [NeZero m] in
/-- Evaluating a reindexed low-degree measurement is reindexing the evaluation. -/
theorem evalPOVM_map_reindex {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n')
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d)) (Matrix n n ℂ))
    (u : Point F m) :
    evalPOVM (G.map (reindexStarAlgEquiv e)) u = (evalPOVM G u).reindex e := by
  rw [evalPOVM, evalPOVM, ProjectiveMeasurement.toPOVM_map_reindex, POVM.map_reindex]

/-- **The conclusion of `clSoundness_ldc_one_deltaCL`, read back along equivalences of the two
registers.** The strategy `S` is abstract; `eA`, `eB` identify its registers with `dA`, `dB`, and
`hψ`, `hPA`, `hPB` identify its state and measurements with the reindexings of `ψ`, `PA`, `PB`. -/
theorem clSoundness_ldc_one_deltaCL_transport {dA dB : Type*} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] (S : TensorProductStrategy (clGame (d := d) (ldc := 1) hm))
    (eA : dA ≃ Fin S.dA) (eB : dB ≃ Fin S.dB) (ψ : dA × dB → ℂ)
    (PA : ProjectiveMeasurement (CL.Question F m) (CL.Answer F m d 1) (Matrix dA dA ℂ))
    (PB : ProjectiveMeasurement (CL.Question F m) (CL.Answer F m d 1) (Matrix dB dB ℂ))
    (hψ : S.ψ = reindexVec eA eB ψ) (hPA : S.PA = PA.map (reindexStarAlgEquiv eA))
    (hPB : S.PB = PB.map (reindexStarAlgEquiv eB))
    (ε : ℝ) (hε : 0 ≤ ε) (hS : 1 - ε ≤ S.value) (hm1 : 1 ≤ m) (hd : 1 ≤ d) :
    ∃ GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix dA dA ℂ),
    ∃ GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix dB dB ℂ),
      inconsistency (uniform (Point F m)) ψ (pointPOVM PA) (evalPOVM GB)
          ≤ deltaCL (Fintype.card F) m d ε ∧
        inconsistency (uniform (Point F m)) ψ (evalPOVM GA) (pointPOVM PB)
          ≤ deltaCL (Fintype.card F) m d ε ∧
        inconsistency (uniform Unit) ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ deltaCL (Fintype.card F) m d ε := by
  obtain ⟨GA', GB', h1, h2, h3⟩ := clSoundness_ldc_one_deltaCL S ε hε hS hm1 hd
  -- the point measurements of `S` are the reindexed point measurements of `PA`, `PB`
  have hptA : CL.pointPOVMA S = fun u => (pointPOVM PA u).reindex eA := funext fun u => by
    rw [CL.pointPOVMA, hPA, ProjectiveMeasurement.toPOVM_map_reindex, pointPOVM,
      POVM.map_reindex]
  have hptB : CL.pointPOVMB S = fun u => (pointPOVM PB u).reindex eB := funext fun u => by
    rw [CL.pointPOVMB, hPB, ProjectiveMeasurement.toPOVM_map_reindex, pointPOVM,
      POVM.map_reindex]
  -- the returned measurements are the reindexings of their pullbacks
  have hevA : evalPOVM GA'
      = fun u => (evalPOVM (GA'.map (reindexStarAlgEquiv eA.symm)) u).reindex eA :=
    funext fun u => by rw [evalPOVM_map_reindex, POVM.reindex_symm_reindex]
  have hevB : evalPOVM GB'
      = fun u => (evalPOVM (GB'.map (reindexStarAlgEquiv eB.symm)) u).reindex eB :=
    funext fun u => by rw [evalPOVM_map_reindex, POVM.reindex_symm_reindex]
  have hA : (fun _ : Unit => GA'.toPOVM ())
      = fun _ => ((GA'.map (reindexStarAlgEquiv eA.symm)).toPOVM ()).reindex eA :=
    funext fun _ => by rw [ProjectiveMeasurement.toPOVM_map_reindex, POVM.reindex_symm_reindex]
  have hB : (fun _ : Unit => GB'.toPOVM ())
      = fun _ => ((GB'.map (reindexStarAlgEquiv eB.symm)).toPOVM ()).reindex eB :=
    funext fun _ => by rw [ProjectiveMeasurement.toPOVM_map_reindex, POVM.reindex_symm_reindex]
  rw [hψ, hptA, hevB, inconsistency_reindex] at h1
  rw [hψ, hptB, hevA, inconsistency_reindex] at h2
  rw [hψ, hA, hB, inconsistency_reindex] at h3
  exact ⟨GA'.map (reindexStarAlgEquiv eA.symm), GB'.map (reindexStarAlgEquiv eB.symm),
    h1, h2, h3⟩

/-- **The `ldc = 1` case of `thm:lidt-cl-soundness`, for a strategy on arbitrary registers.** The
same conclusion as `clSoundness_ldc_one_deltaCL`, for a unit vector `ψ` on `dA × dB` and
projective measurement families on the two matrix algebras, with the value hypothesis as a
`povmValue`. -/
theorem clSoundness_ldc_one_deltaCL_of_projective {dA dB : Type*} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] (ψ : dA × dB → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (PA : ProjectiveMeasurement (CL.Question F m) (CL.Answer F m d 1) (Matrix dA dA ℂ))
    (PB : ProjectiveMeasurement (CL.Question F m) (CL.Answer F m d 1) (Matrix dB dB ℂ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hS : 1 - ε ≤ povmValue (clGame (d := d) (ldc := 1) hm) ψ
      (fun x => PA.toPOVM x) (fun y => PB.toPOVM y))
    (hm1 : 1 ≤ m) (hd : 1 ≤ d) :
    ∃ GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix dA dA ℂ),
    ∃ GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix dB dB ℂ),
      inconsistency (uniform (Point F m)) ψ (pointPOVM PA) (evalPOVM GB)
          ≤ deltaCL (Fintype.card F) m d ε ∧
        inconsistency (uniform (Point F m)) ψ (evalPOVM GA) (pointPOVM PB)
          ≤ deltaCL (Fintype.card F) m d ε ∧
        inconsistency (uniform Unit) ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ deltaCL (Fintype.card F) m d ε := by
  have hval : 1 - ε ≤
      (TensorProductStrategy.ofProjective (clGame (d := d) (ldc := 1) hm) ψ hψ PA PB).value := by
    rw [TensorProductStrategy.value_ofProjective]; exact hS
  exact clSoundness_ldc_one_deltaCL_transport
    (TensorProductStrategy.ofProjective (clGame (d := d) (ldc := 1) hm) ψ hψ PA PB)
    (Fintype.equivFin dA) (Fintype.equivFin dB) ψ PA PB rfl rfl rfl ε hε hval hm1 hd

/-- The same, for measurements given as POVM families with projective elements --- the form the
Pauli basis test's padded strategy arrives in. -/
theorem clSoundness_ldc_one_deltaCL_of_pvm {dA dB : Type*} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] (ψ : dA × dB → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Question F m → POVM (CL.Answer F m d 1) dA)
    (MB : CL.Question F m → POVM (CL.Answer F m d 1) dB)
    (hA : ∀ x, IsPVM fun a => ((MA x).mats a).val)
    (hB : ∀ y, IsPVM fun b => ((MB y).mats b).val)
    (ε : ℝ) (hε : 0 ≤ ε) (hS : 1 - ε ≤ povmValue (clGame (d := d) (ldc := 1) hm) ψ MA MB)
    (hm1 : 1 ≤ m) (hd : 1 ≤ d) :
    ∃ GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix dA dA ℂ),
    ∃ GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix dB dB ℂ),
      inconsistency (uniform (Point F m)) ψ (fun u => (MA (.point u)).map CL.Answer.toValue)
          (evalPOVM GB) ≤ deltaCL (Fintype.card F) m d ε ∧
        inconsistency (uniform (Point F m)) ψ (evalPOVM GA)
          (fun u => (MB (.point u)).map CL.Answer.toValue) ≤ deltaCL (Fintype.card F) m d ε ∧
        inconsistency (uniform Unit) ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ())
          ≤ deltaCL (Fintype.card F) m d ε := by
  have hS' : 1 - ε ≤ povmValue (clGame (d := d) (ldc := 1) hm) ψ
      (fun x => (ProjectiveMeasurement.ofIsPVM MA hA).toPOVM x)
      (fun y => (ProjectiveMeasurement.ofIsPVM MB hB).toPOVM y) := by
    simpa only [ProjectiveMeasurement.toPOVM_ofIsPVM] using hS
  obtain ⟨GA, GB, h1, h2, h3⟩ := clSoundness_ldc_one_deltaCL_of_projective ψ hψ
    (ProjectiveMeasurement.ofIsPVM MA hA) (ProjectiveMeasurement.ofIsPVM MB hB) ε hε hS' hm1 hd
  have hptA : pointPOVM (ProjectiveMeasurement.ofIsPVM MA hA)
      = fun u => (MA (.point u)).map CL.Answer.toValue :=
    funext fun u => by rw [pointPOVM, ProjectiveMeasurement.toPOVM_ofIsPVM]
  have hptB : pointPOVM (ProjectiveMeasurement.ofIsPVM MB hB)
      = fun u => (MB (.point u)).map CL.Answer.toValue :=
    funext fun u => by rw [pointPOVM, ProjectiveMeasurement.toPOVM_ofIsPVM]
  rw [hptA] at h1
  rw [hptB] at h2
  exact ⟨GA, GB, h1, h2, h3⟩


/-! ## Strategies given by POVMs

The padded strategy of the Pauli basis test's analysis is a family of *POVMs* --- averages of
sandwiches --- and `TensorProductStrategy` wants projective measurements. Naimark dilation
(`exists_projective_dilation_povm`) supplies projective families on the registers extended by the
answer type, whose compressions by the default answer are the given POVMs; on the twice-extended
state the dilated strategy has the value of the original (`povmValue_extVec2`), so the theorem
above applies to it. The conclusion is stated on the extended state, against the *dilated* point
measurements, and the two dilations are returned with their compression identities, which is what
a consumer needs to read the point clauses back on the original state
(`inconsistency_extVec2`). -/

/-- **The `ldc = 1` case of `thm:lidt-cl-soundness`, for a strategy given by POVMs.** The
strategy is dilated to a projective one on `dA × Answer`, `dB × Answer`, with the default answer
`values 0` as the ancilla state; the returned projective families `PA`, `PB` compress to `MA`, `MB`,
and the low-degree measurements and the three bounds live on the twice-extended state. -/
theorem clSoundness_ldc_one_deltaCL_of_povm {dA dB : Type*} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] (ψ : dA × dB → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : CL.Question F m → POVM (CL.Answer F m d 1) dA)
    (MB : CL.Question F m → POVM (CL.Answer F m d 1) dB)
    (ε : ℝ) (hε : 0 ≤ ε) (hS : 1 - ε ≤ povmValue (clGame (d := d) (ldc := 1) hm) ψ MA MB)
    (hm1 : 1 ≤ m) (hd : 1 ≤ d) :
    ∃ (PA : ProjectiveMeasurement (CL.Question F m) (CL.Answer F m d 1)
          (Matrix (dA × CL.Answer F m d 1) (dA × CL.Answer F m d 1) ℂ))
      (PB : ProjectiveMeasurement (CL.Question F m) (CL.Answer F m d 1)
          (Matrix (dB × CL.Answer F m d 1) (dB × CL.Answer F m d 1) ℂ))
      (GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
          (Matrix (dA × CL.Answer F m d 1) (dA × CL.Answer F m d 1) ℂ))
      (GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
          (Matrix (dB × CL.Answer F m d 1) (dB × CL.Answer F m d 1) ℂ)),
      (∀ x, (PA.toPOVM x).compress (CL.Answer.values fun _ => (0 : F)) = MA x)
      ∧ (∀ y, (PB.toPOVM y).compress (CL.Answer.values fun _ => (0 : F)) = MB y)
      ∧ inconsistency (uniform (Point F m))
          (extVec2 ψ (CL.Answer.values fun _ => (0 : F)) (CL.Answer.values fun _ => (0 : F)))
          (pointPOVM PA) (evalPOVM GB) ≤ deltaCL (Fintype.card F) m d ε
      ∧ inconsistency (uniform (Point F m))
          (extVec2 ψ (CL.Answer.values fun _ => (0 : F)) (CL.Answer.values fun _ => (0 : F)))
          (evalPOVM GA) (pointPOVM PB) ≤ deltaCL (Fintype.card F) m d ε
      ∧ inconsistency (uniform Unit)
          (extVec2 ψ (CL.Answer.values fun _ => (0 : F)) (CL.Answer.values fun _ => (0 : F)))
          (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) ≤ deltaCL (Fintype.card F) m d ε := by
  set a₀ : CL.Answer F m d 1 := CL.Answer.values fun _ => (0 : F) with ha₀
  obtain ⟨PA, hPA⟩ := exists_projective_dilation_povm MA a₀
  obtain ⟨PB, hPB⟩ := exists_projective_dilation_povm MB a₀
  have hval : 1 - ε ≤ povmValue (clGame (d := d) (ldc := 1) hm) (extVec2 ψ a₀ a₀)
      (fun x => PA.toPOVM x) (fun y => PB.toPOVM y) := by
    rw [povmValue_extVec2]
    simp only [hPA, hPB]
    exact hS
  obtain ⟨GA, GB, h1, h2, h3⟩ := clSoundness_ldc_one_deltaCL_of_projective
    (extVec2 ψ a₀ a₀) (extVec2_unit hψ a₀ a₀) PA PB ε hε hval hm1 hd
  exact ⟨PA, PB, GA, GB, hPA, hPB, h1, h2, h3⟩

end MIPRE.LIDT.Adapter
