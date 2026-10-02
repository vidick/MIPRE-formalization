/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.QuantumState
public import MIPRE.Foundations.Doubling
public import MIPRE.Foundations.FinitePairOrder

@[expose] public section

/-!
# The doubled model of a finite pair

The vendored low-individual-degree core assumes a state fixed by the swap of two identical tensor
factors. The port supplies that symmetry for any finite pair `M` by doubling it
(`reports/c6b-paper-proofs.md`, §4; `planning/c6b-plan.md`, M2): the doubled model `D(M)` acts on
`H ⊕ H`, its first player by `u ⊕ v` and its second by `v ⊕ u`, its state is `(ψ, ψ)/√2`, and the
flip `(ξ, η) ↦ (η, ξ)` fixes the state and exchanges the players. This file builds it as a
symmetric model of the port (`SymModel`, `Co/Basic/QuantumState.lean`) and proves the formulas
that later stages read through it; `Co/Doubling/FinitePair.lean` shows that it is again a finite
pair, and `Co/Doubling/Halving.lean` relates its quantities to those of `M`.

**The local algebra.** The report states `D(M)` over the abstract product `𝒜 × ℬ`; a symmetric model
needs a C⋆-algebra. So the local algebra is `Loc M = LocA M × LocB M`, where `LocA M` is the
commutant of the second player's operators of `M` and `LocB M` the commutant of the first player's:
closed `⋆`-subalgebras of `B(H)`, so C⋆-algebras, star-ordered with the operator order
(`MIPRE/Foundations/FinitePairOrder.lean`). In a finite pair they are the players' operators, and
`𝒜 ≃⋆ₐ LocA M`, `ℬ ≃⋆ₐ LocB M` preserve and reflect the order (`IsFinitePair.equivA`,
`IsFinitePair.equivB`); `Co/Doubling/FinitePair.lean` assembles them into `𝒜 × ℬ ≃⋆ₐ Loc M`.

**The model** (`Doubling.model M hM hψ`): `K = Ampl (Fin 2) M.H = H ⊕ H`, `Ψ = halfVec ψ`,
`L (a, b) = a ⊕ b` (`model_L`), `J = flip2`, so that `R (a, b) = b ⊕ a` (`model_R`). The two
placements commute because in a finite pair `LocA M` and `LocB M` are the two players' operators,
which commute (`commute_locA_locB`); this is the only place the finite-pair hypothesis enters the
definition.

**Formulas** (Lemmas 2 and 5 of the report, Theorem C):

* `ev_diag2`: the expectation of a block-diagonal operator is the average of its blocks'
  expectations at `ψ`; so `ev (L x) = ½ (⟨x₁⟩ + ⟨x₂⟩)` (`ev_L`) and the same for `R` (`ev_R`);
* `inner_L_mul_R`, `ev_L_mul_R` (**the role average**):
  `⟪Ψ, L x R y Ψ⟫ = ½ (⟪ψ, x₁ y₂ ψ⟫ + ⟪ψ, y₁ x₂ ψ⟫)`;
* `bornProb_model`: the Born probability of the doubled model is the average of the two
  operator Born probabilities.
-/

namespace MIPRE.LIDT.Co.Doubling

open scoped InnerProductSpace
open MIPRE.OperatorMatrix

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-! ## The local algebra and the placement -/

/-- The first player's block of the doubled local algebra: the commutant of the second player's
operators of `M` (in a finite pair, the first player's operators). -/
abbrev LocA (M : BipartiteModel 𝒞 𝒜 ℬ) : Type _ := StarSubalgebra.centralizer ℂ M.opsB

/-- The second player's block of the doubled local algebra: the commutant of the first player's
operators of `M` (in a finite pair, the second player's operators). -/
abbrev LocB (M : BipartiteModel 𝒞 𝒜 ℬ) : Type _ := StarSubalgebra.centralizer ℂ M.opsA

/-- **The local algebra of the doubled model**, `LocA M × LocB M`: a C⋆-algebra, star-ordered
componentwise with the operator order. -/
abbrev Loc (M : BipartiteModel 𝒞 𝒜 ℬ) : Type _ := LocA M × LocB M

variable (M : BipartiteModel 𝒞 𝒜 ℬ)

/-! The structure of `Loc M` is that of a C⋆-algebra; the shortcut instances below make every
synthesis of its ring, star and algebra structure go through `CStarAlgebra (Loc M)`, the path the
symmetric model `SymModel (Loc M) _` and its bipartite model are stated with, rather than through
the product, so that the two need no unfolding to be compared. -/

/-- The doubled local algebra is a C⋆-algebra (shortcut). -/
noncomputable instance (priority := high) instCStarAlgebraLoc : CStarAlgebra (Loc M) :=
  instCStarAlgebraProd

/-- The ring structure of the doubled local algebra, through its C⋆-algebra structure (shortcut). -/
noncomputable instance (priority := high) instRingLoc : Ring (Loc M) :=
  @NormedRing.toRing (Loc M) CStarAlgebra.toNormedRing

/-- The star structure of the doubled local algebra, through its C⋆-algebra structure
(shortcut). -/
noncomputable instance (priority := high) instStarRingLoc : StarRing (Loc M) :=
  CStarAlgebra.toStarRing (A := Loc M)

/-- The complex algebra structure of the doubled local algebra, through its C⋆-algebra structure
(shortcut). -/
noncomputable instance (priority := high) instAlgebraLoc : Algebra ℂ (Loc M) :=
  NormedAlgebra.toAlgebra (self := CStarAlgebra.toNormedAlgebra (A := Loc M))

/-- The order of the doubled local algebra: componentwise (shortcut). -/
noncomputable instance (priority := high) instPartialOrderLoc : PartialOrder (Loc M) :=
  Prod.instPartialOrder _ _

/-- The doubled local algebra is star-ordered (shortcut). -/
noncomputable instance (priority := high) instStarOrderedRingLoc : StarOrderedRing (Loc M) :=
  Prod.instStarOrderedRing

/-- The first block of an element of the doubled local algebra, as an operator. -/
noncomputable def fstOp : Loc M →⋆ₐ[ℂ] (M.H →L[ℂ] M.H) :=
  (StarSubalgebra.centralizer ℂ M.opsB).subtype.comp (StarAlgHom.fst ℂ (LocA M) (LocB M))

/-- The second block of an element of the doubled local algebra, as an operator. -/
noncomputable def sndOp : Loc M →⋆ₐ[ℂ] (M.H →L[ℂ] M.H) :=
  (StarSubalgebra.centralizer ℂ M.opsA).subtype.comp (StarAlgHom.snd ℂ (LocA M) (LocB M))

/-- **The first placement of the doubled model**, `(a, b) ↦ a ⊕ b`, a unital `⋆`-homomorphism. -/
noncomputable def locL : Loc M →⋆ₐ[ℂ] (Ampl (Fin 2) M.H →L[ℂ] Ampl (Fin 2) M.H) :=
  diag2.comp ((fstOp M).prod (sndOp M))

/-- The first placement of `(a, b)` is `a ⊕ b`. -/
theorem locL_apply (x : Loc M) :
    locL M x = diag2 (H := M.H) ((x.1 : M.H →L[ℂ] M.H), (x.2 : M.H →L[ℂ] M.H)) :=
  rfl

variable {M}

/-- **In a finite pair the two blocks commute**: `LocA M` is the first player's operators, and
`LocB M` commutes with them. -/
theorem commute_locA_locB (hM : M.IsFinitePair) (a : LocA M) (b : LocB M) :
    Commute (a : M.H →L[ℂ] M.H) (b : M.H →L[ℂ] M.H) :=
  (((StarSubalgebra.mem_centralizer_iff ℂ).1 b.2) _ (hM.mem_opsA a)).1

/-- **The doubled model** `D(M)` of a finite pair with a unit state (`reports/c6b-paper-proofs.md`,
§4.1): on `H ⊕ H`, with the state `(ψ, ψ)/√2`, the first placement `(a, b) ↦ a ⊕ b` of
`Loc M = LocA M × LocB M`, and the flip of the two copies. -/
noncomputable def model (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1) :
    SymModel (Loc M) (Ampl (Fin 2) M.H) where
  Ψ := halfVec M.ψ
  Ψ_norm := (norm_halfVec M.ψ).trans hψ
  L := locL M
  J := flip2
  J_J := flip2_flip2
  J_Ψ := flip2_halfVec M.ψ
  commute x y := by
    rw [locL_apply, locL_apply, conjStarAlgEquiv_flip2_diag2]
    refine Commute.map ?_ diag2
    exact Commute.prod (commute_locA_locB hM x.1 y.2) (commute_locA_locB hM y.1 x.2).symm

variable (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1)

/-- The state of the doubled model is the half vector `(ψ, ψ)/√2`. -/
@[simp]
theorem model_Ψ : (model hM hψ).Ψ = halfVec M.ψ :=
  rfl

/-- The first placement of the doubled model: `L (a, b) = a ⊕ b`. -/
theorem model_L (x : Loc M) :
    (model hM hψ).L x = diag2 (H := M.H) ((x.1 : M.H →L[ℂ] M.H), (x.2 : M.H →L[ℂ] M.H)) :=
  rfl

/-- The second placement of the doubled model: `R (a, b) = b ⊕ a`. -/
theorem model_R (x : Loc M) :
    (model hM hψ).R x = diag2 (H := M.H) ((x.2 : M.H →L[ℂ] M.H), (x.1 : M.H →L[ℂ] M.H)) :=
  conjStarAlgEquiv_flip2_diag2 ((x.1 : M.H →L[ℂ] M.H), (x.2 : M.H →L[ℂ] M.H))

/-! ## Expectations -/

/-- **The state formula** (Lemma 2 of `reports/c6b-paper-proofs.md`, §4.3): the expectation of a
block-diagonal operator is the average of its blocks' expectations at `ψ`. -/
theorem ev_diag2 (c : (M.H →L[ℂ] M.H) × (M.H →L[ℂ] M.H)) :
    (model hM hψ).ev (diag2 (H := M.H) c) = 2⁻¹ * (Op.qform M.ψ c.1 + Op.qform M.ψ c.2) := by
  rw [VecState.ev_eq_re_inner]
  change (⟪halfVec M.ψ, diag2 (H := M.H) c (halfVec M.ψ)⟫_ℂ).re = _
  rw [inner_halfVec_diag2]
  simp only [Op.qform, Complex.mul_re, Complex.add_re, Complex.add_im]
  norm_num

/-- The expectation of the first placement is the average of the blocks' expectations. -/
theorem ev_L (x : Loc M) :
    (model hM hψ).ev ((model hM hψ).L x) =
      2⁻¹ * (Op.qform M.ψ (x.1 : M.H →L[ℂ] M.H) + Op.qform M.ψ (x.2 : M.H →L[ℂ] M.H)) :=
  ev_diag2 hM hψ ((x.1 : M.H →L[ℂ] M.H), (x.2 : M.H →L[ℂ] M.H))

/-- The expectation of the second placement is the average of the blocks' expectations. -/
theorem ev_R (x : Loc M) :
    (model hM hψ).ev ((model hM hψ).R x) =
      2⁻¹ * (Op.qform M.ψ (x.1 : M.H →L[ℂ] M.H) + Op.qform M.ψ (x.2 : M.H →L[ℂ] M.H)) := by
  rw [model_R, ev_diag2, add_comm (Op.qform M.ψ _)]

/-- The product of the two placements is block diagonal:
`L x R y = (x₁ y₂) ⊕ (y₁ x₂)`. -/
theorem L_mul_R (x y : Loc M) :
    (model hM hψ).L x * (model hM hψ).R y =
      diag2 (H := M.H) ((x.1 : M.H →L[ℂ] M.H) * (y.2 : M.H →L[ℂ] M.H),
        (y.1 : M.H →L[ℂ] M.H) * (x.2 : M.H →L[ℂ] M.H)) := by
  rw [model_L, model_R, ← map_mul, Prod.mk_mul_mk, (commute_locA_locB hM y.1 x.2).eq]

/-- **The role average** (Theorem C, Lemma 5 of `reports/c6b-paper-proofs.md`, §4):
`⟪Ψ, L x R y Ψ⟫ = ½ (⟪ψ, x₁ y₂ ψ⟫ + ⟪ψ, y₁ x₂ ψ⟫)`. -/
theorem inner_L_mul_R (x y : Loc M) :
    ⟪(model hM hψ).Ψ, ((model hM hψ).L x * (model hM hψ).R y) (model hM hψ).Ψ⟫_ℂ =
      2⁻¹ * (⟪M.ψ, ((x.1 : M.H →L[ℂ] M.H) * (y.2 : M.H →L[ℂ] M.H)) M.ψ⟫_ℂ +
        ⟪M.ψ, ((y.1 : M.H →L[ℂ] M.H) * (x.2 : M.H →L[ℂ] M.H)) M.ψ⟫_ℂ) := by
  rw [L_mul_R, model_Ψ, inner_halfVec_diag2]

/-- **The role average**, for the expectation: `ev (L x R y) = ½ (⟨x₁ y₂⟩ + ⟨y₁ x₂⟩)`. -/
theorem ev_L_mul_R (x y : Loc M) :
    (model hM hψ).ev ((model hM hψ).L x * (model hM hψ).R y) =
      2⁻¹ * (Op.qform M.ψ ((x.1 : M.H →L[ℂ] M.H) * (y.2 : M.H →L[ℂ] M.H)) +
        Op.qform M.ψ ((y.1 : M.H →L[ℂ] M.H) * (x.2 : M.H →L[ℂ] M.H))) := by
  rw [L_mul_R, ev_diag2]

/-- **The Born probability of the doubled model** is the average of the operator Born
probabilities of the two role assignments. -/
theorem bornProb_model (x y : Loc M) :
    (model hM hψ).toBipartite.bornProb x y =
      2⁻¹ * (Op.qform M.ψ ((x.1 : M.H →L[ℂ] M.H) * (y.2 : M.H →L[ℂ] M.H)) +
        Op.qform M.ψ ((y.1 : M.H →L[ℂ] M.H) * (x.2 : M.H →L[ℂ] M.H))) :=
  ev_L_mul_R hM hψ x y

end MIPRE.LIDT.Co.Doubling

end
