/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.CrossConsistency
public import MIPRE.Foundations.POVMValue

@[expose] public section

/-!
# Local isometries of bipartite models

The conclusion of a rigidity theorem moves a strategy along a pair of local isometries: in the
tensor-product model, `V_A : ℂ^{d_A} → ℂ^{register} ⊗ ℂ^{H_A}` and its partner for the second
player, each player's operator `X` going to `V_A X V_Aᴴ`, and the state `ψ` to
`(V_A ⊗ V_B) ψ` (`MIPRE.Introspection.isometricImage`, `isometricState`). Phase 4 of
`planning/mipco-track.md` needs the same move in any bipartite model, where there is no
factorization of the space into the two players' parts. What survives is this
(`BipartiteModel.LocalIsometry`): a linear isometry `W` of the Hilbert spaces, and for each
player a non-unital `⋆`-homomorphism `Φ` of the player's algebra into the other model's, with
`W` intertwining the two representations,
`π' (πA' (Φ_A a)) ∘ W = W ∘ π (πA a)`, and likewise for the second player.

`X ↦ V_A X V_Aᴴ` is exactly such a `Φ_A`: it is multiplicative because `V_Aᴴ V_A = 1`, and not
unital, `Φ_A 1 = V_A V_Aᴴ` being the projection onto the image. In the commuting-operator model
the isometry built from a player's approximate Pauli operators has its entries in that player's
algebra, and conjugation by it is again multiplicative, for the same reason.

* **Born probabilities are carried over exactly** on the transported state `W ψ`
  (`LocalIsometry.bornProb_withState`), and so are the players' state norms
  (`LocalIsometry.stateSqNorm_withState`). The transported state is a state of the target's
  Hilbert space but not its state, so the statements are about the target with its state
  replaced (`BipartiteModel.withState`).
* **A projective measurement is carried over to a projective measurement**
  (`LocalIsometry.transportA`): `Φ_A` of each element, with the complement `1 - Φ_A 1` of the
  image added at one fixed outcome. It is intertwined with the original by `W`
  (`LocalIsometry.intertwine_transportA`), so a strategy and its transport have the same value
  on the transported state (`LocalIsometry.povmValue_transport`). This is
  `MIPRE.Introspection.isometricPOVM` in any model.
* Local isometries compose (`LocalIsometry.comp`), and exchange with the players
  (`LocalIsometry.swap`).
-/

noncomputable section

namespace MIPRE

open Finset
open scoped InnerProductSpace

universe u u' u''

/-! ## Replacing the state -/

namespace StateModel

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]

/-- The state model with its state replaced by the vector `φ` of its Hilbert space. -/
def withState (M : StateModel.{u} 𝒞) (φ : M.H) : StateModel.{u} 𝒞 where
  H := M.H
  ψ := φ
  π := M.π

variable (M : StateModel.{u} 𝒞) (φ : M.H)

@[simp]
theorem withState_ψ : (M.withState φ).ψ = φ := rfl

@[simp]
theorem withState_π (T : 𝒞) : (M.withState φ).π T = M.π T := rfl

theorem withState_snorm (T : 𝒞) : (M.withState φ).snorm T = ‖M.π T φ‖ := rfl

theorem withState_qform (T : 𝒞) : (M.withState φ).qform T = (⟪φ, M.π T φ⟫_ℂ).re := rfl

@[simp]
theorem withState_self : M.withState M.ψ = M := rfl

end StateModel

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- The bipartite model with its state replaced by the vector `φ` of its Hilbert space. -/
def withState (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) (φ : M.H) : BipartiteModel.{u} 𝒞 𝒜 ℬ where
  toStateModel := M.toStateModel.withState φ
  πA := M.πA
  πB := M.πB
  commute := M.commute

variable (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) (φ : M.H)

@[simp]
theorem withState_ψ : (M.withState φ).ψ = φ := rfl

@[simp]
theorem withState_πA (a : 𝒜) : (M.withState φ).πA a = M.πA a := rfl

@[simp]
theorem withState_πB (b : ℬ) : (M.withState φ).πB b = M.πB b := rfl

@[simp]
theorem withState_self : M.withState M.ψ = M := rfl

theorem withState_swap : (M.withState φ).swap = M.swap.withState φ := rfl

end BipartiteModel

/-! ## Pushing a measurement forward along a unital `⋆`-homomorphism -/

section Pushforward

variable {R S : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [Ring S] [StarRing S] [Algebra ℂ S]
  {X : Type*} [Fintype X]

/-- **The image of a projective measurement under a `⋆`-homomorphism preserving the unit.** -/
theorem IsPVMIn.pushforward {f : R →⋆ₙₐ[ℂ] S} (hf : f 1 = 1) {P : X → R} (hP : IsPVMIn P) :
    IsPVMIn fun x => f (P x) where
  star_eq x := by rw [← map_star, hP.star_eq]
  idem x := by rw [← map_mul, hP.idem]
  sum_eq_one := by rw [← map_sum, hP.sum_eq_one, hf]
  orthogonal hxy := by rw [← map_mul, hP.orthogonal hxy, map_zero]

variable [PartialOrder R] [StarOrderedRing R] [PartialOrder S] [StarOrderedRing S]

/-- **A POVM pushed forward along a `⋆`-homomorphism preserving the unit.** -/
def POVMIn.pushforward (f : R →⋆ₙₐ[ℂ] S) (hf : f 1 = 1) (P : POVMIn X R) : POVMIn X S where
  mats x := ⟨f (P.op x), by rw [selfAdjoint.mem_iff, ← map_star, P.star_op]⟩
  nonneg x := by
    change (0 : S) ≤ f (P.op x)
    simpa only [map_zero] using OrderHomClass.mono f (P.op_nonneg x)
  normalized := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum]
    change ∑ x, f (P.op x) = 1
    rw [← map_sum, P.sum_op, hf])

@[simp]
theorem POVMIn.pushforward_op (f : R →⋆ₙₐ[ℂ] S) (hf : f 1 = 1) (P : POVMIn X R) (x : X) :
    (P.pushforward f hf).op x = f (P.op x) := rfl

theorem POVMIn.isPVMIn_pushforward (f : R →⋆ₙₐ[ℂ] S) (hf : f 1 = 1) {P : POVMIn X R}
    (hP : IsPVMIn P.op) : IsPVMIn (P.pushforward f hf).op :=
  hP.pushforward hf

/-- **A projective measurement, as a POVM**: its elements are nonnegative, being star
projections. -/
def IsPVMIn.toPOVMIn {P : X → R} (hP : IsPVMIn P) : POVMIn X R where
  mats x := ⟨P x, hP.star_eq x⟩
  nonneg x := Subtype.coe_le_coe.mp (hP.nonneg x)
  normalized := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hP.sum_eq_one)

omit [Algebra ℂ R] in
@[simp]
theorem IsPVMIn.toPOVMIn_op {P : X → R} (hP : IsPVMIn P) (x : X) : hP.toPOVMIn.op x = P x := rfl

end Pushforward

/-! ## Local isometries -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ 𝒞' 𝒜' ℬ' 𝒞'' 𝒜'' ℬ'' : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞]
  [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
  [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜'] [Algebra ℂ 𝒜']
  [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']
  [Ring 𝒞''] [StarRing 𝒞''] [Algebra ℂ 𝒞''] [Ring 𝒜''] [StarRing 𝒜''] [Algebra ℂ 𝒜'']
  [Ring ℬ''] [StarRing ℬ''] [Algebra ℂ ℬ'']

/-- **A local isometry** from the bipartite model `M` into the bipartite model `M'`: a linear
isometry `W` of the Hilbert spaces, and for each player a non-unital `⋆`-homomorphism of the
player's algebra into the other model's, the two representations intertwined by `W`. The states
play no part: how far `W ψ` is from the state of `M'` is the error of whatever produced the
isometry. -/
structure LocalIsometry (M : BipartiteModel.{u} 𝒞 𝒜 ℬ) (M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ') where
  /-- The isometry of the Hilbert spaces. -/
  W : M.H →ₗᵢ[ℂ] M'.H
  /-- The first player's operators, moved along the isometry. -/
  ΦA : 𝒜 →⋆ₙₐ[ℂ] 𝒜'
  /-- The second player's operators, moved along the isometry. -/
  ΦB : ℬ →⋆ₙₐ[ℂ] ℬ'
  /-- The isometry intertwines the first player's operators with their images. -/
  intertwineA : ∀ (a : 𝒜) (v : M.H), M'.π (M'.πA (ΦA a)) (W v) = W (M.π (M.πA a) v)
  /-- The isometry intertwines the second player's operators with their images. -/
  intertwineB : ∀ (b : ℬ) (v : M.H), M'.π (M'.πB (ΦB b)) (W v) = W (M.π (M.πB b) v)

namespace LocalIsometry

variable {M : BipartiteModel.{u} 𝒞 𝒜 ℬ} {M' : BipartiteModel.{u'} 𝒞' 𝒜' ℬ'}
  {M'' : BipartiteModel.{u''} 𝒞'' 𝒜'' ℬ''}

/-- **The local isometry with the players exchanged.** -/
def swap (Φ : LocalIsometry M M') : LocalIsometry M.swap M'.swap where
  W := Φ.W
  ΦA := Φ.ΦB
  ΦB := Φ.ΦA
  intertwineA := Φ.intertwineB
  intertwineB := Φ.intertwineA

@[simp]
theorem swap_W (Φ : LocalIsometry M M') : Φ.swap.W = Φ.W := rfl

@[simp]
theorem swap_ΦA (Φ : LocalIsometry M M') : Φ.swap.ΦA = Φ.ΦB := rfl

@[simp]
theorem swap_ΦB (Φ : LocalIsometry M M') : Φ.swap.ΦB = Φ.ΦA := rfl

/-- **Local isometries compose.** -/
def comp (Φ' : LocalIsometry M' M'') (Φ : LocalIsometry M M') : LocalIsometry M M'' where
  W := Φ'.W.comp Φ.W
  ΦA := Φ'.ΦA.comp Φ.ΦA
  ΦB := Φ'.ΦB.comp Φ.ΦB
  intertwineA a v := by
    simp only [LinearIsometry.coe_comp, Function.comp_apply, NonUnitalStarAlgHom.comp_apply]
    rw [Φ'.intertwineA, Φ.intertwineA]
  intertwineB b v := by
    simp only [LinearIsometry.coe_comp, Function.comp_apply, NonUnitalStarAlgHom.comp_apply]
    rw [Φ'.intertwineB, Φ.intertwineB]

theorem comp_W_ψ {Φ' : LocalIsometry M' M''} {Φ : LocalIsometry M M'} (h : Φ.W M.ψ = M'.ψ)
    (h' : Φ'.W M'.ψ = M''.ψ) : (Φ'.comp Φ).W M.ψ = M''.ψ := by
  show Φ'.W (Φ.W M.ψ) = M''.ψ
  rw [h, h']

@[simp]
theorem comp_ΦA (Φ' : LocalIsometry M' M'') (Φ : LocalIsometry M M') (a : 𝒜) :
    (Φ'.comp Φ).ΦA a = Φ'.ΦA (Φ.ΦA a) := rfl

@[simp]
theorem comp_ΦB (Φ' : LocalIsometry M' M'') (Φ : LocalIsometry M M') (b : ℬ) :
    (Φ'.comp Φ).ΦB b = Φ'.ΦB (Φ.ΦB b) := rfl

/-- **The inverse of a local isometry** with an inverse isometry and inverse homomorphisms. -/
def symm (Φ : LocalIsometry M M') (W' : M'.H →ₗᵢ[ℂ] M.H) (hW : ∀ v, Φ.W (W' v) = v)
    (ΨA : 𝒜' →⋆ₙₐ[ℂ] 𝒜) (hA : ∀ a, Φ.ΦA (ΨA a) = a) (ΨB : ℬ' →⋆ₙₐ[ℂ] ℬ)
    (hB : ∀ b, Φ.ΦB (ΨB b) = b) : LocalIsometry M' M where
  W := W'
  ΦA := ΨA
  ΦB := ΨB
  intertwineA a v := Φ.W.injective (by rw [← Φ.intertwineA, hA, hW, hW])
  intertwineB b v := Φ.W.injective (by rw [← Φ.intertwineB, hB, hW, hW])

theorem symm_W_ψ (Φ : LocalIsometry M M') (W' : M'.H →ₗᵢ[ℂ] M.H) (hW : ∀ v, Φ.W (W' v) = v)
    (ΨA : 𝒜' →⋆ₙₐ[ℂ] 𝒜) (hA : ∀ a, Φ.ΦA (ΨA a) = a) (ΨB : ℬ' →⋆ₙₐ[ℂ] ℬ)
    (hB : ∀ b, Φ.ΦB (ΨB b) = b) (h : Φ.W M.ψ = M'.ψ) :
    (Φ.symm W' hW ΨA hA ΨB hB).W M'.ψ = M.ψ :=
  Φ.W.injective (by rw [← h]; exact hW _)

variable (Φ : LocalIsometry M M')

/-- The isometry intertwines a product of the two players' operators with the product of their
images. -/
theorem intertwine (a : 𝒜) (b : ℬ) (v : M.H) :
    M'.π (M'.πA (Φ.ΦA a) * M'.πB (Φ.ΦB b)) (Φ.W v) = Φ.W (M.π (M.πA a * M.πB b) v) := by
  rw [map_mul, map_mul, mul_apply_eq_comp, Φ.intertwineB,
    Φ.intertwineA, mul_apply_eq_comp]

/-- The image of the unit of the first player's algebra fixes the image of the isometry. -/
theorem π_πA_ΦA_one (v : M.H) : M'.π (M'.πA (Φ.ΦA 1)) (Φ.W v) = Φ.W v := by
  rw [Φ.intertwineA, map_one, map_one, one_apply_eq_self]

/-- The image of the unit of the second player's algebra fixes the image of the isometry. -/
theorem π_πB_ΦB_one (v : M.H) : M'.π (M'.πB (Φ.ΦB 1)) (Φ.W v) = Φ.W v :=
  Φ.swap.π_πA_ΦA_one v

/-- **Born probabilities are carried over exactly**, on the transported state. -/
theorem bornProb_withState (a : 𝒜) (b : ℬ) :
    (M'.withState (Φ.W M.ψ)).bornProb (Φ.ΦA a) (Φ.ΦB b) = M.bornProb a b := by
  show (⟪Φ.W M.ψ, M'.π (M'.πA (Φ.ΦA a) * M'.πB (Φ.ΦB b)) (Φ.W M.ψ)⟫_ℂ).re =
    (⟪M.ψ, M.π (M.πA a * M.πB b) M.ψ⟫_ℂ).re
  rw [Φ.intertwine, LinearIsometry.inner_map_map]

/-- **The first player's state norms are carried over exactly**, on the transported state. -/
theorem stateNorm_withState (a : 𝒜) :
    (M'.withState (Φ.W M.ψ)).stateNorm (Φ.ΦA a) = M.stateNorm a := by
  show ‖M'.π (M'.πA (Φ.ΦA a)) (Φ.W M.ψ)‖ = ‖M.π (M.πA a) M.ψ‖
  rw [Φ.intertwineA, LinearIsometry.norm_map]

theorem stateSqNorm_withState (a : 𝒜) :
    (M'.withState (Φ.W M.ψ)).stateSqNorm (Φ.ΦA a) = M.stateSqNorm a := by
  rw [stateSqNorm, stateSqNorm, Φ.stateNorm_withState]

/-- The transported state has the norm of the state. -/
theorem norm_W_ψ : ‖Φ.W M.ψ‖ = ‖M.ψ‖ := Φ.W.norm_map _

/-! ### An isometry carrying the state to the state

The local isometries between extensions of one model by registers carry the state exactly, and
then every quantity computed from the state is carried over. -/

section Exact

variable {Φ} (h : Φ.W M.ψ = M'.ψ)
include h

theorem bornProb_of_W_ψ (a : 𝒜) (b : ℬ) : M'.bornProb (Φ.ΦA a) (Φ.ΦB b) = M.bornProb a b := by
  have := Φ.bornProb_withState a b
  rwa [h, withState_self] at this

theorem stateNorm_of_W_ψ (a : 𝒜) : M'.stateNorm (Φ.ΦA a) = M.stateNorm a := by
  have := Φ.stateNorm_withState a
  rwa [h, withState_self] at this

theorem stateSqNorm_of_W_ψ (a : 𝒜) : M'.stateSqNorm (Φ.ΦA a) = M.stateSqNorm a := by
  rw [stateSqNorm, stateSqNorm, stateNorm_of_W_ψ h]

theorem swap_stateSqNorm_of_W_ψ (b : ℬ) :
    M'.swap.stateSqNorm (Φ.ΦB b) = M.swap.stateSqNorm b :=
  stateSqNorm_of_W_ψ (Φ := Φ.swap) h b

/-- The cross norm `‖(πA a - πB b) ψ‖` is carried over. -/
theorem xNorm_of_W_ψ (a : 𝒜) (b : ℬ) : M'.xNorm (Φ.ΦA a) (Φ.ΦB b) = M.xNorm a b := by
  show ‖M'.π (M'.πA (Φ.ΦA a) - M'.πB (Φ.ΦB b)) M'.ψ‖ = ‖M.π (M.πA a - M.πB b) M.ψ‖
  rw [← h, map_sub, map_sub, _root_.sub_apply, _root_.sub_apply, Φ.intertwineA, Φ.intertwineB,
    ← map_sub, LinearIsometry.norm_map]

theorem xSqNorm_of_W_ψ (a : 𝒜) (b : ℬ) : M'.xSqNorm (Φ.ΦA a) (Φ.ΦB b) = M.xSqNorm a b := by
  rw [xSqNorm, xSqNorm, xNorm_of_W_ψ h]

theorem norm_ψ_of_W_ψ : ‖M'.ψ‖ = ‖M.ψ‖ := by rw [← h, LinearIsometry.norm_map]

end Exact

/-! ### The image of the unit -/

theorem ΦA_one_mul_self : Φ.ΦA 1 * Φ.ΦA 1 = Φ.ΦA 1 := by rw [← map_mul, one_mul]

theorem star_ΦA_one : star (Φ.ΦA 1) = Φ.ΦA 1 := by rw [← map_star, star_one]

theorem ΦA_mul_ΦA_one (a : 𝒜) : Φ.ΦA a * Φ.ΦA 1 = Φ.ΦA a := by rw [← map_mul, mul_one]

theorem ΦA_one_mul_ΦA (a : 𝒜) : Φ.ΦA 1 * Φ.ΦA a = Φ.ΦA a := by rw [← map_mul, one_mul]

/-- The complement of the image of the first player's unit. -/
theorem compl_ΦA_one_mul_self : (1 - Φ.ΦA 1) * (1 - Φ.ΦA 1) = 1 - Φ.ΦA 1 := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, Φ.ΦA_one_mul_self, sub_self,
    sub_zero]

theorem star_compl_ΦA_one : star (1 - Φ.ΦA 1) = 1 - Φ.ΦA 1 := by
  rw [star_sub, star_one, Φ.star_ΦA_one]

theorem ΦA_mul_compl (a : 𝒜) : Φ.ΦA a * (1 - Φ.ΦA 1) = 0 := by
  rw [mul_sub, mul_one, Φ.ΦA_mul_ΦA_one, sub_self]

theorem compl_mul_ΦA (a : 𝒜) : (1 - Φ.ΦA 1) * Φ.ΦA a = 0 := by
  rw [sub_mul, one_mul, Φ.ΦA_one_mul_ΦA, sub_self]

/-- The complement of the image of the unit kills the image of the isometry. -/
theorem π_πA_compl (v : M.H) : M'.π (M'.πA (1 - Φ.ΦA 1)) (Φ.W v) = 0 := by
  rw [map_sub, map_sub, map_one, map_one, _root_.sub_apply,
    one_apply_eq_self, Φ.π_πA_ΦA_one, sub_self]

/-! ### Transporting a projective measurement -/

section Transport

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The transport of a family of the first player's operators**: the image of each, with the
complement of the image of the unit added at the outcome `x₀`. -/
def transportOpA (x₀ : X) (P : X → 𝒜) (x : X) : 𝒜' :=
  Φ.ΦA (P x) + if x = x₀ then 1 - Φ.ΦA 1 else 0

/-- **The transport of a projective measurement is a projective measurement.** -/
theorem isPVMIn_transportOpA (x₀ : X) {P : X → 𝒜} (hP : IsPVMIn P) :
    IsPVMIn (Φ.transportOpA x₀ P) where
  star_eq x := by
    unfold transportOpA
    rw [star_add, ← map_star, hP.star_eq]
    split_ifs
    · rw [Φ.star_compl_ΦA_one]
    · rw [star_zero]
  idem x := by
    unfold transportOpA
    split_ifs
    · rw [add_mul, mul_add, mul_add, ← map_mul, hP.idem, Φ.ΦA_mul_compl, Φ.compl_mul_ΦA,
        Φ.compl_ΦA_one_mul_self, add_zero, zero_add]
    · rw [add_zero, ← map_mul, hP.idem]
  sum_eq_one := by
    simp only [transportOpA, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    rw [← map_sum, hP.sum_eq_one]
    abel
  orthogonal {x y} hxy := by
    unfold transportOpA
    have hPxy : Φ.ΦA (P x) * Φ.ΦA (P y) = 0 := by rw [← map_mul, hP.orthogonal hxy, map_zero]
    by_cases hx : x = x₀
    · have hy : y ≠ x₀ := fun h => hxy (hx.trans h.symm)
      rw [ite_eq_left hx, ite_eq_right hy, add_zero, add_mul, hPxy, Φ.compl_mul_ΦA, add_zero]
    · rw [ite_eq_right hx, add_zero]
      split_ifs
      · rw [mul_add, hPxy, Φ.ΦA_mul_compl, add_zero]
      · rw [add_zero, hPxy]

omit [Fintype X] in
/-- **The transport is intertwined with the original by the isometry.** -/
theorem intertwine_transportOpA (x₀ : X) (P : X → 𝒜) (x : X) (v : M.H) :
    M'.π (M'.πA (Φ.transportOpA x₀ P x)) (Φ.W v) = Φ.W (M.π (M.πA (P x)) v) := by
  unfold transportOpA
  rw [map_add, map_add, _root_.add_apply, Φ.intertwineA]
  split_ifs
  · rw [Φ.π_πA_compl, add_zero]
  · rw [map_zero, map_zero, _root_.zero_apply, add_zero]

variable [PartialOrder 𝒜] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']

/-- **The transport of a projective measurement**, as a POVM of the target's first player. -/
def transportA (x₀ : X) (P : POVMIn X 𝒜) (hP : IsPVMIn P.op) : POVMIn X 𝒜' where
  mats x := ⟨Φ.transportOpA x₀ P.op x, (Φ.isPVMIn_transportOpA x₀ hP).star_eq x⟩
  nonneg x := (Φ.isPVMIn_transportOpA x₀ hP).nonneg x
  normalized := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (Φ.isPVMIn_transportOpA x₀ hP).sum_eq_one)

@[simp]
theorem transportA_op (x₀ : X) (P : POVMIn X 𝒜) (hP : IsPVMIn P.op) (x : X) :
    (Φ.transportA x₀ P hP).op x = Φ.transportOpA x₀ P.op x := rfl

theorem isPVMIn_transportA (x₀ : X) (P : POVMIn X 𝒜) (hP : IsPVMIn P.op) :
    IsPVMIn (Φ.transportA x₀ P hP).op :=
  Φ.isPVMIn_transportOpA x₀ hP

end Transport

section TransportB

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [PartialOrder ℬ] [PartialOrder ℬ']
  [StarOrderedRing ℬ']

/-- **The transport of a projective measurement of the second player.** -/
def transportB (y₀ : Y) (Q : POVMIn Y ℬ) (hQ : IsPVMIn Q.op) : POVMIn Y ℬ' :=
  Φ.swap.transportA y₀ Q hQ

@[simp]
theorem transportB_op (y₀ : Y) (Q : POVMIn Y ℬ) (hQ : IsPVMIn Q.op) (y : Y) :
    (Φ.transportB y₀ Q hQ).op y = Φ.swap.transportOpA y₀ Q.op y := rfl

theorem isPVMIn_transportB (y₀ : Y) (Q : POVMIn Y ℬ) (hQ : IsPVMIn Q.op) :
    IsPVMIn (Φ.transportB y₀ Q hQ).op :=
  Φ.swap.isPVMIn_transportOpA y₀ hQ

end TransportB

/-! ### The value of a transported strategy -/

section Value

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] [PartialOrder ℬ'] [StarOrderedRing ℬ']

omit [Fintype A] [Fintype B] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] [PartialOrder ℬ']
  [StarOrderedRing ℬ'] in
/-- The Born probabilities of a transported pair of measurements are the original ones, on the
transported state. -/
theorem bornProb_transport (a₀ : A) (b₀ : B) (P : A → 𝒜) (Q : B → ℬ) (a : A) (b : B) :
    (M'.withState (Φ.W M.ψ)).bornProb (Φ.transportOpA a₀ P a) (Φ.swap.transportOpA b₀ Q b) =
      M.bornProb (P a) (Q b) := by
  show (⟪Φ.W M.ψ, M'.π (M'.πA (Φ.transportOpA a₀ P a) * M'.πB (Φ.swap.transportOpA b₀ Q b))
      (Φ.W M.ψ)⟫_ℂ).re = (⟪M.ψ, M.π (M.πA (P a) * M.πB (Q b)) M.ψ⟫_ℂ).re
  rw [map_mul, mul_apply_eq_comp]
  have hB : M'.π (M'.πB (Φ.swap.transportOpA b₀ Q b)) (Φ.W M.ψ) =
      Φ.W (M.π (M.πB (Q b)) M.ψ) := Φ.swap.intertwine_transportOpA b₀ Q b M.ψ
  rw [hB, Φ.intertwine_transportOpA, LinearIsometry.inner_map_map, map_mul,
    mul_apply_eq_comp]

omit [StarOrderedRing 𝒜] [StarOrderedRing ℬ] in
/-- **A strategy and its transport have the same value**, on the transported state. -/
theorem povmValue_transport (G : Game X Y A B) (a₀ : A) (b₀ : B) (PA : X → POVMIn A 𝒜)
    (PB : Y → POVMIn B ℬ) (hPA : ∀ x, IsPVMIn (PA x).op) (hPB : ∀ y, IsPVMIn (PB y).op) :
    (M'.withState (Φ.W M.ψ)).povmValue G (fun x => Φ.transportA a₀ (PA x) (hPA x))
      (fun y => Φ.transportB b₀ (PB y) (hPB y)) = M.povmValue G PA PB := by
  unfold povmValue condWin
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [transportA_op, transportB_op, Φ.bornProb_transport]

end Value

/-! ### The value of a strategy moved along a unital local isometry -/

section UnitalValue

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] [PartialOrder ℬ'] [StarOrderedRing ℬ']

/-- **A strategy moved along a local isometry preserving the units has its value**, on the
transported state. -/
theorem povmValue_pushforward_withState (hA : Φ.ΦA 1 = 1) (hB : Φ.ΦB 1 = 1) (G : Game X Y A B)
    (PA : X → POVMIn A 𝒜) (PB : Y → POVMIn B ℬ) :
    (M'.withState (Φ.W M.ψ)).povmValue G (fun x => (PA x).pushforward Φ.ΦA hA)
      (fun y => (PB y).pushforward Φ.ΦB hB) = M.povmValue G PA PB := by
  unfold povmValue condWin
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [POVMIn.pushforward_op, POVMIn.pushforward_op, Φ.bornProb_withState]

/-- The same, for a local isometry carrying the state to the state. -/
theorem povmValue_pushforward {Φ : LocalIsometry M M'} (h : Φ.W M.ψ = M'.ψ)
    (hA : Φ.ΦA 1 = 1) (hB : Φ.ΦB 1 = 1) (G : Game X Y A B) (PA : X → POVMIn A 𝒜)
    (PB : Y → POVMIn B ℬ) :
    M'.povmValue G (fun x => (PA x).pushforward Φ.ΦA hA)
      (fun y => (PB y).pushforward Φ.ΦB hB) = M.povmValue G PA PB := by
  have := Φ.povmValue_pushforward_withState hA hB G PA PB
  rwa [h, withState_self] at this

end UnitalValue

end LocalIsometry

end BipartiteModel

end MIPRE

end
