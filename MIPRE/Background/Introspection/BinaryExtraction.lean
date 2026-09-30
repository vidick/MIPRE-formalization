/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.RestrictedProfileSoundness

@[expose] public section

/-! # Transporting field-register extraction into binary coordinates

This is an exact change of computational basis, using a self-dual field basis.
It neither assumes nor proves the existence of QLD extraction witnesses.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the change of basis is the
relabelling of the register of the ancilla model's register model along the binary basis
(`BipartiteModel.regRelabel`), composed after the extraction's local isometry.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical BinaryComplete BipartiteModel
set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t d : ℕ} [NeZero m]

theorem binaryX (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (x : Seed m t) :
    registerOp (Weyl.binEquiv b).symm
      (Weyl.proj Weyl.wX ((Weyl.binEquiv b).symm x)) = Honest.pauliXReadout (some x) := by
  have h := Weyl.proj_wX_binEquiv hb ((Weyl.binEquiv (n := Fin m → Bool) b).symm x)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h, Honest.pauliXReadout_some]
  exact registerOp_inv (Weyl.binEquiv b) _

theorem binaryZ (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (x : Seed m t) :
    registerOp (Weyl.binEquiv b).symm
      (Weyl.proj Weyl.wZ ((Weyl.binEquiv b).symm x)) =
      readout (some : Seed m t → Option (Seed m t)) (some x) := by
  have h := Weyl.proj_wZ_binEquiv hb ((Weyl.binEquiv (n := Fin m → Bool) b).symm x)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h]
  change registerOp (Weyl.binEquiv b).symm (registerOp (Weyl.binEquiv b) _) = _
  rw [registerOp_inv]
  ext i j
  by_cases hij : i = j <;> simp [hij, Weyl.proj_wZ, Weyl.zProj_apply, readout]

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **The conclusion of the Pauli basis test at the genuine full-register answers, in field
coordinates**: an ancilla model and a local isometry into it with the field register adjoined, the
state within `δ` of the register state, and the X and Z effects of the genuine answers within `δ`
of the honest generalized Pauli projectors in summed squared state norm. -/
structure FieldExtraction (M : BipartiteModel 𝒞 𝒜 ℬ) (hm : m ∣ Fintype.card F)
    (R : M.ProjStrat (QLD.qldGame (d := d) hm)) (δ : ℝ) where
  /-- The ancilla model. -/
  N : QLD.AncillaModel
  /-- The local isometry into the ancilla model with the field register adjoined. -/
  Φ : BipartiteModel.LocalIsometry M (N.N.reg (QLD.Honest.Register F m))
  state_error : ‖Φ.W M.ψ - (N.N.reg (QLD.Honest.Register F m)).ψ‖ ≤ δ
  X_error : ∑ x : QLD.Honest.Register F m, (N.N.reg (QLD.Honest.Register F m)).stateSqNorm
    (Φ.ΦA ((R.PA (.pauli .X)).op (.pauliAns x)) - smulKron 1 (Weyl.proj Weyl.wX x)) ≤ δ
  Z_error : ∑ z : QLD.Honest.Register F m, (N.N.reg (QLD.Honest.Register F m)).swap.stateSqNorm
    (Φ.ΦB ((R.PB (.pauli .Z)).op (.pauliAns z)) - smulKron 1 (Weyl.proj Weyl.wZ z)) ≤ δ

/-- Increasing the common error bound leaves the actual extraction data unchanged. -/
def FieldExtraction.mono {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {R : M.ProjStrat (QLD.qldGame (d := d) hm)} {δ δ' : ℝ}
    (w : FieldExtraction M hm R δ) (h : δ ≤ δ') : FieldExtraction M hm R δ' where
  N := w.N
  Φ := w.Φ
  state_error := w.state_error.trans h
  X_error := w.X_error.trans h
  Z_error := w.Z_error.trans h

/-- Exact field-to-binary conversion of the full extraction witness: the register is relabelled
along the binary basis (`BipartiteModel.regRelabel`). State distance and both valid-answer error
sums keep precisely the same bound. -/
def FieldExtraction.toBinary {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {R : M.ProjStrat (QLD.qldGame (d := d) hm)} {δ : ℝ}
    (w : FieldExtraction M hm R δ) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) : Extraction M hm b R δ where
  N := w.N
  Φ := (w.N.N.regRelabel (Weyl.binEquiv b).symm).comp w.Φ
  state_error := by
    rw [← w.N.N.regRelabel_W_ψ (Weyl.binEquiv b).symm]
    change ‖(w.N.N.regRelabel _).W (w.Φ.W M.ψ) - (w.N.N.regRelabel _).W _‖ ≤ δ
    rw [← map_sub, LinearIsometry.norm_map]
    exact w.state_error
  X_error := by
    have hx : ∀ x : Seed m t, (w.N.N.reg (Seed m t)).stateSqNorm
        (((w.N.N.regRelabel (Weyl.binEquiv (n := Fin m → Bool) b).symm).comp w.Φ).ΦA
            ((R.PA (.pauli .X)).op (validAnswer b x)) -
          smulKron 1 (Honest.pauliXReadout (some x))) =
        (w.N.N.reg (QLD.Honest.Register F m)).stateSqNorm
          (w.Φ.ΦA ((R.PA (.pauli .X)).op (.pauliAns ((Weyl.binEquiv b).symm x))) -
            smulKron 1 (Weyl.proj Weyl.wX ((Weyl.binEquiv b).symm x))) := by
      intro x
      have e1 : smulKron (1 : w.N.𝒜) (Honest.pauliXReadout (some x)) =
          (w.N.N.regRelabel (Weyl.binEquiv (n := Fin m → Bool) b).symm).ΦA
            (smulKron 1 (Weyl.proj Weyl.wX ((Weyl.binEquiv b).symm x))) := by
        rw [regRelabel_ΦA, ← binaryX b hb x]
        rfl
      rw [LocalIsometry.comp_ΦA, e1, ← map_sub,
        LocalIsometry.stateSqNorm_of_W_ψ (w.N.N.regRelabel_W_ψ _)]
      rfl
    rw [Finset.sum_congr rfl (fun x _ => hx x)]
    exact ((Equiv.sum_comp (Weyl.binEquiv (n := Fin m → Bool) b).symm (fun x =>
      (w.N.N.reg (QLD.Honest.Register F m)).stateSqNorm
        (w.Φ.ΦA ((R.PA (.pauli .X)).op (.pauliAns x)) -
          smulKron 1 (Weyl.proj Weyl.wX x))))).le.trans w.X_error
  Z_error := by
    have hz : ∀ z : Seed m t, (w.N.N.reg (Seed m t)).swap.stateSqNorm
        (((w.N.N.regRelabel (Weyl.binEquiv (n := Fin m → Bool) b).symm).comp w.Φ).ΦB
            ((R.PB (.pauli .Z)).op (validAnswer b z)) -
          smulKron 1 (readout (some : Seed m t → Option (Seed m t)) (some z))) =
        (w.N.N.reg (QLD.Honest.Register F m)).swap.stateSqNorm
          (w.Φ.ΦB ((R.PB (.pauli .Z)).op (.pauliAns ((Weyl.binEquiv b).symm z))) -
            smulKron 1 (Weyl.proj Weyl.wZ ((Weyl.binEquiv b).symm z))) := by
      intro z
      have e1 : smulKron (1 : w.N.ℬ) (readout (some : Seed m t → Option (Seed m t)) (some z)) =
          (w.N.N.regRelabel (Weyl.binEquiv (n := Fin m → Bool) b).symm).ΦB
            (smulKron 1 (Weyl.proj Weyl.wZ ((Weyl.binEquiv b).symm z))) := by
        rw [regRelabel_ΦB, ← binaryZ b hb z]
        rfl
      rw [LocalIsometry.comp_ΦB, e1, ← map_sub,
        LocalIsometry.swap_stateSqNorm_of_W_ψ (w.N.N.regRelabel_W_ψ _)]
      rfl
    rw [Finset.sum_congr rfl (fun z _ => hz z)]
    exact ((Equiv.sum_comp (Weyl.binEquiv (n := Fin m → Bool) b).symm (fun z =>
      (w.N.N.reg (QLD.Honest.Register F m)).swap.stateSqNorm
        (w.Φ.ΦB ((R.PB (.pauli .Z)).op (.pauliAns z)) -
          smulKron 1 (Weyl.proj Weyl.wZ z))))).le.trans w.Z_error

end MIPRE.Introspection.RestrictedSoundness
end

end
