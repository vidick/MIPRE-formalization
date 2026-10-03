/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.Group.Basic
public import MIPRE.Foundations.FinitePairExpand
public import MIPRE.Tactics

@[expose] public section

/-!
# The order of a finite pair's algebras is the operator order

In a finite pair (`MIPRE/Foundations/FinitePair.lean`) each player's algebra is ordered by its own
order, and represented injectively on the model's space onto the commutant of the other player's
operators. This file shows that the two orders agree (`reports/c6b-paper-proofs.md`, §4 Lemma 10
and §5 Lemma 13): for a star-ordered `𝒜`, `0 ≤ a` exactly when `0 ≤ π (πA a)` in `B(H)`
(`IsFinitePair.nonneg_iff_A`), and likewise for `ℬ`. So positive operator valued and projective
measurements of the represented operators pull back to the players' algebras, and push forward.

* **The commutants as C⋆-algebras.** The commutant `StarSubalgebra.centralizer ℂ s` of a set of
  operators is norm closed (`isClosed_centralizer`), hence a C⋆-algebra
  (`StarSubalgebra.cstarAlgebra`), and star-ordered with the order of `B(H)`
  (`starOrderedRing_centralizer`, registered here as an instance).
* **The players' algebras as commutants** (`IsFinitePair.equivA`, `IsFinitePair.equivB`): in a
  finite pair, `a ↦ π (πA a)` is a `⋆`-isomorphism of `𝒜` onto the commutant of the second
  player's operators: injective by `injA`, onto by `commutantA`.
* **Order agreement** (`IsFinitePair.nonneg_iff_A`, `IsFinitePair.nonneg_iff_B`): a `⋆`-ring
  homomorphism between star-ordered rings is monotone, and the inverse of the isomorphism is one.
  The forward direction is `π_πA_nonneg`; the backward one is where the commutant matters, through
  the square root of a positive operator of the commutant, which lies in it.
* **Transport of measurements** (`POVMIn.mapHom`, `isPVMIn_map_equiv_iff`): a unital `⋆`-ring
  homomorphism between star-ordered rings carries a POVM to a POVM, and a `⋆`-isomorphism carries
  projective measurements both ways; in particular a POVM of a product has POVMs as coordinates
  (`POVMIn.fst`, `POVMIn.snd`).
-/

namespace MIPRE

open scoped InnerProductSpace

/-! ## Commutants of operators -/

section Commutant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The commutant of a set of operators is norm closed.** -/
instance isClosed_centralizer (s : Set (H →L[ℂ] H)) :
    IsClosed (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) := by
  rw [StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

/-- **The commutant of a set of operators is star-ordered** with the order of `B(H)`
(`starOrderedRing_centralizer`). -/
instance instStarOrderedRingCentralizer (s : Set (H →L[ℂ] H)) :
    StarOrderedRing (StarSubalgebra.centralizer ℂ s) :=
  starOrderedRing_centralizer s

end Commutant

/-! ## Transport of measurements along `⋆`-homomorphisms -/

section Transport

variable {X R S : Type*} [Fintype X] [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
  [Ring S] [StarRing S] [PartialOrder S] [StarOrderedRing S]

/-- **The image of a POVM under a unital `⋆`-ring homomorphism** between star-ordered rings, which
is monotone: each operator is replaced by its image. (`POVMIn.map` coarse-grains the outcomes
instead.) -/
def POVMIn.mapHom {F : Type*} [FunLike F R S] [RingHomClass F R S]
    [NonUnitalStarRingHomClass F R S] (f : F) (P : POVMIn X R) : POVMIn X S where
  mats x := ⟨f (P.op x), by rw [selfAdjoint.mem_iff, ← map_star, P.star_op]⟩
  nonneg x := Subtype.coe_le_coe.mp (map_nonneg f (P.op_nonneg x))
  normalized := Subtype.ext <| by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (map_sum f P.op Finset.univ).symm.trans (by rw [P.sum_op, map_one]; rfl)

/-- The operators of a transported POVM are the images of the operators. -/
@[simp]
theorem POVMIn.mapHom_op {F : Type*} [FunLike F R S] [RingHomClass F R S]
    [NonUnitalStarRingHomClass F R S] (f : F) (P : POVMIn X R) (x : X) :
    (P.mapHom f).op x = f (P.op x) :=
  rfl

/-- Transport along a `⋆`-isomorphism and back is the identity. -/
@[simp]
theorem POVMIn.mapHom_symm_mapHom [Algebra ℂ R] [Algebra ℂ S] (e : R ≃⋆ₐ[ℂ] S)
    (P : POVMIn X R) : (P.mapHom e).mapHom e.symm = P :=
  POVMIn.ext' fun x => e.symm_apply_apply (P.op x)

/-- Transport along the inverse of a `⋆`-isomorphism and back is the identity. -/
@[simp]
theorem POVMIn.mapHom_mapHom_symm [Algebra ℂ R] [Algebra ℂ S] (e : R ≃⋆ₐ[ℂ] S)
    (P : POVMIn X S) : (P.mapHom e.symm).mapHom e = P :=
  POVMIn.ext' fun x => e.apply_symm_apply (P.op x)

/-- **The first coordinates of a POVM of a product** of star-ordered algebras, a POVM of the first
factor. -/
def POVMIn.fst [Algebra ℂ R] [Algebra ℂ S] (P : POVMIn X (R × S)) : POVMIn X R :=
  P.mapHom (StarAlgHom.fst ℂ R S)

/-- **The second coordinates of a POVM of a product** of star-ordered algebras, a POVM of the
second factor. -/
def POVMIn.snd [Algebra ℂ R] [Algebra ℂ S] (P : POVMIn X (R × S)) : POVMIn X S :=
  P.mapHom (StarAlgHom.snd ℂ R S)

/-- The operators of the first coordinates are the first coordinates of the operators. -/
@[simp]
theorem POVMIn.fst_op [Algebra ℂ R] [Algebra ℂ S] (P : POVMIn X (R × S)) (x : X) :
    P.fst.op x = (P.op x).1 :=
  rfl

/-- The operators of the second coordinates are the second coordinates of the operators. -/
@[simp]
theorem POVMIn.snd_op [Algebra ℂ R] [Algebra ℂ S] (P : POVMIn X (R × S)) (x : X) :
    P.snd.op x = (P.op x).2 :=
  rfl

omit [PartialOrder R] [StarOrderedRing R] [PartialOrder S] [StarOrderedRing S] in
/-- **A `⋆`-isomorphism carries projective measurements both ways.** -/
theorem isPVMIn_map_equiv_iff [Algebra ℂ R] [Algebra ℂ S] (e : R ≃⋆ₐ[ℂ] S) {P : X → R} :
    IsPVMIn (fun x => e (P x)) ↔ IsPVMIn P := by
  refine ⟨fun h => ?_, fun h => h.map e⟩
  have := h.map e.symm
  simpa only [StarAlgEquiv.symm_apply_apply] using this

end Transport

/-! ## The players' algebras of a finite pair -/

namespace BipartiteModel

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}

/-- The first player's operators commute with the second player's and their adjoints. -/
theorem opsA_subset_centralizer (M : BipartiteModel 𝒞 𝒜 ℬ) :
    M.opsA ⊆ StarSubalgebra.centralizer ℂ M.opsB := by
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, StarSubalgebra.mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  rw [← map_star, ← map_star]
  exact ⟨((M.commute a b).map M.π).eq.symm, ((M.commute a (star b)).map M.π).eq.symm⟩

/-- The second player's operators commute with the first player's and their adjoints. -/
theorem opsB_subset_centralizer (M : BipartiteModel 𝒞 𝒜 ℬ) :
    M.opsB ⊆ StarSubalgebra.centralizer ℂ M.opsA :=
  M.swap.opsA_subset_centralizer

/-- **In a finite pair, the commutant of the second player's operators is the first player's
operators.** -/
theorem IsFinitePair.coe_centralizer_opsB (hM : M.IsFinitePair) :
    (StarSubalgebra.centralizer ℂ M.opsB : Set (M.H →L[ℂ] M.H)) = M.opsA := by
  refine Set.Subset.antisymm (fun T hT => hM.commutantA T fun b => ?_)
    M.opsA_subset_centralizer
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).1 hT) _ ⟨b, rfl⟩).1.symm

/-- **In a finite pair, the commutant of the first player's operators is the second player's
operators.** -/
theorem IsFinitePair.coe_centralizer_opsA (hM : M.IsFinitePair) :
    (StarSubalgebra.centralizer ℂ M.opsA : Set (M.H →L[ℂ] M.H)) = M.opsB :=
  hM.swap.coe_centralizer_opsB

/-- An element of the commutant of the second player's operators is one of the first player's. -/
theorem IsFinitePair.mem_opsA (hM : M.IsFinitePair) (x : StarSubalgebra.centralizer ℂ M.opsB) :
    (x : M.H →L[ℂ] M.H) ∈ M.opsA :=
  hM.coe_centralizer_opsB ▸ x.2

/-- An element of the commutant of the first player's operators is one of the second player's. -/
theorem IsFinitePair.mem_opsB (hM : M.IsFinitePair) (x : StarSubalgebra.centralizer ℂ M.opsA) :
    (x : M.H →L[ℂ] M.H) ∈ M.opsB :=
  hM.coe_centralizer_opsA ▸ x.2

/-- **The first player's algebra of a finite pair is the commutant of the second player's
operators**, as a `⋆`-isomorphism `a ↦ π (πA a)`: injective by `injA`, onto by `commutantA`. -/
noncomputable def IsFinitePair.equivA (hM : M.IsFinitePair) :
    𝒜 ≃⋆ₐ[ℂ] StarSubalgebra.centralizer ℂ M.opsB :=
  StarAlgEquiv.ofBijective
    (StarAlgHom.codRestrict (M.π.comp M.πA) _ fun a => M.opsA_subset_centralizer ⟨a, rfl⟩)
    ⟨fun a a' h => hM.injA (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := hM.mem_opsA x
      exact ⟨a, Subtype.ext ha⟩⟩

/-- **The second player's algebra of a finite pair is the commutant of the first player's
operators**, as a `⋆`-isomorphism `b ↦ π (πB b)`. -/
noncomputable def IsFinitePair.equivB (hM : M.IsFinitePair) :
    ℬ ≃⋆ₐ[ℂ] StarSubalgebra.centralizer ℂ M.opsA :=
  hM.swap.equivA

/-- The operator of `equivA a` is `π (πA a)`. -/
@[simp]
theorem IsFinitePair.coe_equivA (hM : M.IsFinitePair) (a : 𝒜) :
    (hM.equivA a : M.H →L[ℂ] M.H) = M.π (M.πA a) :=
  rfl

/-- The operator of `equivB b` is `π (πB b)`. -/
@[simp]
theorem IsFinitePair.coe_equivB (hM : M.IsFinitePair) (b : ℬ) :
    (hM.equivB b : M.H →L[ℂ] M.H) = M.π (M.πB b) :=
  rfl

/-- The operator of the inverse of `equivA` is the element of the commutant. -/
theorem IsFinitePair.π_πA_equivA_symm (hM : M.IsFinitePair)
    (x : StarSubalgebra.centralizer ℂ M.opsB) :
    M.π (M.πA (hM.equivA.symm x)) = x :=
  congrArg Subtype.val (hM.equivA.apply_symm_apply x)

/-- The operator of the inverse of `equivB` is the element of the commutant. -/
theorem IsFinitePair.π_πB_equivB_symm (hM : M.IsFinitePair)
    (x : StarSubalgebra.centralizer ℂ M.opsA) :
    M.π (M.πB (hM.equivB.symm x)) = x :=
  congrArg Subtype.val (hM.equivB.apply_symm_apply x)

section Order

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- **Order agreement in a finite pair** (`reports/c6b-paper-proofs.md`, §4 Lemma 10, §5 Lemma 13):
an element of the first player's algebra is nonnegative exactly when its operator is positive.
This is also the statement that `equivA` preserves and reflects the order, `0 ≤ equivA a ↔ 0 ≤ a`,
since the commutant carries the operator order; it is the one order-agreement lemma of the
library, and every other form (`le_iff_A`, the doubled model's `Doubling.equiv_nonneg_iff`) is
derived from it. -/
theorem IsFinitePair.nonneg_iff_A (hM : M.IsFinitePair) {a : 𝒜} :
    0 ≤ M.π (M.πA a) ↔ 0 ≤ a :=
  ⟨fun h => hM.equivA.symm_apply_apply a ▸ map_nonneg hM.equivA.symm
      (show 0 ≤ hM.equivA a from h),
    fun h => map_nonneg hM.equivA h⟩

/-- Order agreement in a finite pair, for the order itself, first player. -/
theorem IsFinitePair.le_iff_A (hM : M.IsFinitePair) {a a' : 𝒜} :
    M.π (M.πA a) ≤ M.π (M.πA a') ↔ a ≤ a' := by
  rw [← sub_nonneg, ← map_sub, ← map_sub, hM.nonneg_iff_A, sub_nonneg]

variable [PartialOrder ℬ] [StarOrderedRing ℬ]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- **Order agreement in a finite pair**, for the second player's algebra (`nonneg_iff_A` for the
swapped pair). -/
theorem IsFinitePair.nonneg_iff_B (hM : M.IsFinitePair) {b : ℬ} :
    0 ≤ M.π (M.πB b) ↔ 0 ≤ b :=
  hM.swap.nonneg_iff_A

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- Order agreement in a finite pair, for the order itself, second player. -/
theorem IsFinitePair.le_iff_B (hM : M.IsFinitePair) {b b' : ℬ} :
    M.π (M.πB b) ≤ M.π (M.πB b') ↔ b ≤ b' :=
  hM.swap.le_iff_A

end Order

end BipartiteModel

end MIPRE

end
