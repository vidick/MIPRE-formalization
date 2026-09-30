/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveDilationTransport

@[expose] public section

/-! # Exact error transport through a registered auxiliary extension

Only an auxiliary register in a fixed pure state is added. The EPR register
and Bob's operators remain unchanged. All identities hold for arbitrary
operators and auxiliary states, without normalization or projectivity.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the auxiliary register in its
fixed state is the first player's one-sided ancilla `Ξ.expandA t₀`, and the registered extension
is the local isometry `registeredExtend Ξ t₀` from the register model `Ξ.reg I` into
`(Ξ.expandA t₀).reg I`: the inert embedding `BipartiteModel.inertA`, an old operator `M` becoming
`M ⊗ 1`, followed by the reassociation `regExchange`. It carries the state to the state, so every
error is transported exactly (`LocalIsometry.stateSqNorm_of_W_ψ`, `xSqNorm_of_W_ψ`,
`bornProb_of_W_ψ`). The extended operator `registeredExtendOp M` is its `ΦA`, the extended
measurement `registeredExtendPOVM M` the old one pushed forward along it, and Bob's operators are
unchanged. A relabelling of the local coordinates is `BipartiteModel.relabel`.
-/

noncomputable section
namespace MIPRE.Introspection

open Finset Matrix Classical
set_option linter.unusedSectionVars false

section Raw

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ψ : BipartiteModel 𝒞 𝒜 ℬ)
variable {T α β α' β' : Type*} [Fintype T] [DecidableEq T]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']

/-- Relabelling the registers of an extension, along a bijection for each player, preserves the
cross norm. -/
theorem xSqNorm_registerOp (e : α × β → ℂ) (e' : α' × β' → ℂ) (f : α' ≃ α) (g : β' ≃ β)
    (he : ∀ p, e' p = e (f p.1, g p.2)) (M : Matrix α α 𝒜) (N : Matrix β β ℬ) :
    (Ψ.expand e').xSqNorm (M.submatrix f f) (N.submatrix g g) = (Ψ.expand e).xSqNorm M N :=
  (Ψ.relabel e e' f g).xSqNorm_of_W_ψ (Ψ.relabel_W_ψ e e' f g he) M N

/-- The old deviation vector is extended by the same fixed isometry. -/
theorem deviation_extVecA (t₀ : T) (M : 𝒜) (N : ℬ) :
    (Ψ.expandA t₀).π ((Ψ.expandA t₀).πA (diagonal fun _ => M) - (Ψ.expandA t₀).πB N)
        (Ψ.expandA t₀).ψ =
      (Ψ.inertA t₀).W (Ψ.π (Ψ.πA M - Ψ.πB N) Ψ.ψ) := by
  have hA := (Ψ.inertA t₀).intertwineA M Ψ.ψ
  have hB := (Ψ.inertA t₀).intertwineB N Ψ.ψ
  rw [BipartiteModel.inertA_ΦA] at hA
  rw [BipartiteModel.inertA_ΦB] at hB
  rw [← Ψ.inertA_W_ψ t₀, map_sub, map_sub, _root_.sub_apply, _root_.sub_apply, hA, hB, map_sub]

theorem xSqNorm_extVecA (t₀ : T) (M : 𝒜) (N : ℬ) :
    (Ψ.expandA t₀).xSqNorm (diagonal fun _ => M) N = Ψ.xSqNorm M N := by
  show ‖(Ψ.expandA t₀).π ((Ψ.expandA t₀).πA (diagonal fun _ => M) - (Ψ.expandA t₀).πB N)
      (Ψ.expandA t₀).ψ‖ ^ 2 = ‖Ψ.π (Ψ.πA M - Ψ.πB N) Ψ.ψ‖ ^ 2
  rw [deviation_extVecA, LinearIsometry.norm_map]

end Raw

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] (Ξ : BipartiteModel 𝒞 𝒜 ℬ)
variable {I T A B : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype A] [Fintype B] [DecidableEq B]

/-- Extend an old operator by identity, then absorb the new register into
Alice's auxiliary factor. -/
def registeredExtendOp (M : Matrix I I 𝒜) : Matrix I I (Matrix T T 𝒜) :=
  BipartiteModel.layerSwap (diagonal fun _ : T => M)

/-- The extension is the `⋆`-homomorphism `M ↦ M ⊗ 1` followed by the exchange of the layers. -/
theorem registeredExtendOp_eq (M : Matrix I I 𝒜) :
    registeredExtendOp (T := T) M = (BipartiteModel.layerSwap.comp diagHom) M := rfl

theorem registeredExtendOp_apply (M : Matrix I I 𝒜) (i j : I) :
    registeredExtendOp (T := T) M i j = diagonal fun _ => M i j := by
  ext t t'
  by_cases h : t = t'
  · subst h
    simp only [registeredExtendOp, BipartiteModel.layerSwap_apply, diagonal_apply_eq]
  · simp only [registeredExtendOp, BipartiteModel.layerSwap_apply, diagonal_apply_ne _ h,
      Matrix.zero_apply]

@[simp] theorem registeredExtendOp_zero :
    registeredExtendOp (I := I) (T := T) (0 : Matrix I I 𝒜) = 0 := by
  rw [registeredExtendOp_eq, map_zero]

theorem registeredExtendOp_sub (M N : Matrix I I 𝒜) :
    registeredExtendOp (T := T) (M - N) = registeredExtendOp M - registeredExtendOp N := by
  simp only [registeredExtendOp_eq, map_sub]

/-- Every ideal acting on the original register is literally the same
ideal tensored with the enlarged auxiliary identity. -/
theorem registeredExtendOp_aOp (P : Matrix I I ℂ) :
    registeredExtendOp (T := T) (smulKron (1 : 𝒜) P) = smulKron 1 P := by
  ext i j t t'
  rw [registeredExtendOp_apply, smulKron_apply, smulKron_apply, Matrix.smul_apply]
  by_cases h : t = t'
  · subst h
    rw [diagonal_apply_eq, one_apply_eq]
  · rw [diagonal_apply_ne _ h, one_apply_ne h, smul_zero]

/-! ## The registered extension as a local isometry -/

/-- **The registered extension**: the register model into the register model of the one-sided
extension, the inert embedding of the fresh ancilla followed by its exchange with the register.
The first player's operator `M` becomes `registeredExtendOp M`, the second player's are
unchanged. -/
def registeredExtend (t₀ : T) : BipartiteModel.LocalIsometry (Ξ.reg I) ((Ξ.expandA t₀).reg I) :=
  (regExchange Ξ t₀).comp ((Ξ.reg I).inertA t₀)

@[simp]
theorem registeredExtend_ΦA (t₀ : T) (M : Matrix I I 𝒜) :
    (registeredExtend Ξ t₀).ΦA M = registeredExtendOp M := rfl

@[simp]
theorem registeredExtend_ΦB (t₀ : T) (N : Matrix I I ℬ) : (registeredExtend Ξ t₀).ΦB N = N :=
  rfl

/-- The registered extension carries the state to the state. -/
theorem registeredExtend_W_ψ (t₀ : T) :
    (registeredExtend (I := I) Ξ t₀).W (Ξ.reg I).ψ = ((Ξ.expandA t₀).reg I).ψ :=
  BipartiteModel.LocalIsometry.comp_W_ψ ((Ξ.reg I).inertA_W_ψ t₀)
    (Ξ.exchange_W_ψ t₀ (registerEPR I))

theorem stateSqNorm_registeredExtendOp (t₀ : T) (M : Matrix I I 𝒜) :
    ((Ξ.expandA t₀).reg I).stateSqNorm (registeredExtendOp M) = (Ξ.reg I).stateSqNorm M :=
  (registeredExtend Ξ t₀).stateSqNorm_of_W_ψ (registeredExtend_W_ψ Ξ t₀) M

theorem xSqNorm_registeredExtendOp (t₀ : T) (M : Matrix I I 𝒜) (N : Matrix I I ℬ) :
    ((Ξ.expandA t₀).reg I).xSqNorm (registeredExtendOp M) N = (Ξ.reg I).xSqNorm M N :=
  (registeredExtend Ξ t₀).xSqNorm_of_W_ψ (registeredExtend_W_ψ Ξ t₀) M N

/-- Bob's same-party error is unaffected by adding an auxiliary register
on Alice's side, including the exact registered state reassociation. -/
theorem snorm_bOp_registered_extVecA (t₀ : T) (N : Matrix I I ℬ) :
    ((Ξ.expandA t₀).reg I).snorm (((Ξ.expandA t₀).reg I).πB N) ^ 2 =
      (Ξ.reg I).snorm ((Ξ.reg I).πB N) ^ 2 :=
  (registeredExtend Ξ t₀).swap_stateSqNorm_of_W_ψ (registeredExtend_W_ψ Ξ t₀) N

theorem bornProb_registeredExtendOp (t₀ : T) (M : Matrix I I 𝒜) (N : Matrix I I ℬ) :
    ((Ξ.expandA t₀).reg I).bornProb (registeredExtendOp M) N = (Ξ.reg I).bornProb M N :=
  (registeredExtend Ξ t₀).bornProb_of_W_ψ (registeredExtend_W_ψ Ξ t₀) M N

/-! ## Measurements -/

section POVM

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]

/-- An old measurement on the register model, tensored with the identity of the fresh ancilla and
carried to the register model of the one-sided extension. -/
def registeredExtendPOVM (M : POVMIn A (Matrix I I 𝒜)) : POVMIn A (Matrix I I (Matrix T T 𝒜)) :=
  (POVMIn.ampA M).pushforward BipartiteModel.layerSwap BipartiteModel.layerSwap_one

@[simp] theorem registeredExtendPOVM_mats (M : POVMIn A (Matrix I I 𝒜)) (a : A) :
    (registeredExtendPOVM (T := T) M).op a = registeredExtendOp (M.op a) := rfl

theorem registeredExtendPOVM_map (M : POVMIn A (Matrix I I 𝒜)) (f : A → B) :
    registeredExtendPOVM (T := T) (M.map f) = (registeredExtendPOVM M).map f := by
  refine POVMIn.ext' fun b => ?_
  rw [registeredExtendPOVM_mats, POVMIn.map_op, POVMIn.map_op]
  simp only [registeredExtendPOVM_mats, registeredExtendOp_eq, map_sum]

theorem registeredExtendPOVM_isPVM (M : POVMIn A (Matrix I I 𝒜)) (hM : IsPVMIn M.op) :
    IsPVMIn (registeredExtendPOVM (T := T) M).op :=
  (hM.pushforward (diagHom_one (α := T))).pushforward BipartiteModel.layerSwap_one

end POVM

end MIPRE.Introspection
end

end
