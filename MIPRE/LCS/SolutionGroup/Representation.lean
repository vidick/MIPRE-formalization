/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
import MIPRE.LCS.EPR
import MIPRE.LCS.SolutionGroup
import Mathlib.Algebra.Star.Unitary

/-!
# Representations of Solution Groups

This module constructs matrix representations of an LCS solution group from
observable matrices satisfying the analytic identities extracted by the
EPR/local-loss pipeline.

The representation sends the solution-group generators to unitary matrices:
$$
  x_j \mapsto \operatorname{obs}_j,\qquad J \mapsto -I.
$$
The main point is to prove that this assignment respects every relator in the
solution-group presentation, so that it descends to a homomorphism
$$
  \operatorname{SolutionGroup}(\operatorname{game.toLinearSystem})
    \to \operatorname{U}(n) .
$$

The file is organized in three layers.

* Unitary packaging:
  `involutiveMatrixUnitary`, `observableMatrixUnitary`, and `negOneMatrixUnitary` turn
  observables and $-I$ into unitary matrices, so they can be used
  as group-valued generator images.
* Generic presented-group construction:
  `solutionGroupRepresentation` packages the observable generator image,
  same-equation commutation, and equation relators into a representation of the
  presented solution group.
* Game and EPR construction:
  `rowObservableProduct_eq_sign_of_local_loss` converts local-loss
  annihilation on the EPR vector into the row identity
  $$
    \prod_{j \in V_i}\operatorname{obs}_j = (-1)^{b_i}I,
  $$
  `solutionGroupRepresentationOfRows` turns row identities into a
  game-specialized representation, and `solutionGroupRepresentationOfEPRLoss`
  supplies those row identities from the EPR/local-loss argument.
-/

namespace MIPRE.LCS

open scoped BigOperators
open Matrix

namespace SolutionGroup

/-!
## Unitary Matrices

The target group of a representation is `unitary (Matrix n n ℂ)`, so observable
matrices must first be packaged as unitary elements.  Since an observable is
self-adjoint and involutive, it is unitary.  The distinguished solution-group
generator `J` is represented by the unitary matrix `-I`.
-/

section MatrixUnitaries

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A self-adjoint involution as a unitary matrix. -/
noncomputable def involutiveMatrixUnitary
    (M : Matrix n n ℂ) (hM : M * M = 1) (hMstar : star M = M) : unitary (Matrix n n ℂ) :=
  ⟨M, by
    rw [Unitary.mem_iff]
    constructor <;> rw [hMstar] <;> exact hM⟩

/-- An observable matrix as a unitary matrix. -/
noncomputable def observableMatrixUnitary
    (M : Matrix n n ℂ) (hM : IsObservable M) : unitary (Matrix n n ℂ) :=
  involutiveMatrixUnitary M hM.involutive hM.self_adjoint

/-- The scalar matrix `-I` as a unitary matrix. -/
noncomputable def negOneMatrixUnitary : unitary (Matrix n n ℂ) :=
  involutiveMatrixUnitary ((-1 : ℂ) • (1 : Matrix n n ℂ)) (by
    rw [smul_mul_smul]
    simp) (by simp)

/-- The underlying matrix of `involutiveMatrixUnitary M hM hMstar` is $M$:
$$
  \operatorname{val}(\operatorname{involutiveMatrixUnitary}(M)) = M.
$$
This simp lemma lets unit-valued generator images reduce back to their matrix
values during relator and row-product calculations.
-/
@[simp] lemma involutiveMatrixUnitary_val
    (M : Matrix n n ℂ) (hM : M * M = 1) (hMstar : star M = M) :
    (involutiveMatrixUnitary M hM hMstar : Matrix n n ℂ) = M :=
  rfl

/-- The underlying matrix of `observableMatrixUnitary M hM` is $M$:
$$
  \operatorname{val}(\operatorname{observableMatrixUnitary}(M)) = M.
$$
This simp lemma keeps generator-image computations at the matrix level after an
observable has been packaged as a unitary matrix.
-/
@[simp] lemma observableMatrixUnitary_val
    (M : Matrix n n ℂ) (hM : IsObservable M) :
    (observableMatrixUnitary M hM : Matrix n n ℂ) = M :=
  rfl

/-- A packaged observable squares to the identity in the unitary group:
$$
  \operatorname{involutiveMatrixUnitary}(M)^2 = 1.
$$
This discharges the $x_j^2 = 1$ and $J^2 = 1$ style relators after matrices are
turned into units.
-/
@[simp] lemma involutiveMatrixUnitary_sq
    (M : Matrix n n ℂ) (hM : M * M = 1) (hMstar : star M = M) :
    involutiveMatrixUnitary M hM hMstar ^ 2 = 1 := by
  apply Subtype.ext
  simpa [pow_two, involutiveMatrixUnitary] using hM

/-- An observable matrix unitary squares to $1$:
$$
  \operatorname{observableMatrixUnitary}(M)^2 = 1.
$$
This is the representation-side proof of the variable involution relators
$x_j^2 = 1$.
-/
@[simp] lemma observableMatrixUnitary_sq
    (M : Matrix n n ℂ) (hM : IsObservable M) :
    observableMatrixUnitary M hM ^ 2 = 1 := by
  simp [observableMatrixUnitary]

/-- The unit representing $J$ squares to $1$:
$$
  (-I)^2 = I.
$$
This is the representation-side proof of the distinguished involution relator
$J^2 = 1$.
-/
@[simp] lemma negOneMatrixUnitary_sq :
    negOneMatrixUnitary (n := n) ^ 2 = 1 := by
  simp [negOneMatrixUnitary]

@[simp] lemma negOneMatrixUnitary_pow_val
    (b : ZMod 2) :
    ((negOneMatrixUnitary (n := n) ^ b.val : unitary (Matrix n n ℂ)) : Matrix n n ℂ) =
      (-1 : ℂ) ^ b.val • (1 : Matrix n n ℂ) := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp [negOneMatrixUnitary]

/-- Alice lift commutes with finite noncommutative products:
$$
  \operatorname{AliceLift}\!\left(\prod_{x \in s} f_x\right)
    = \prod_{x \in s}\operatorname{AliceLift}(f_x).
$$
The product is written with `Finset.noncommProd`, so pairwise commutation fixes
the order ambiguity.  This is useful when the EPR/local-loss row product
`ProjectorStrategy.aliceRowProd` must be identified with the Alice lift of the concrete row
observable product.
-/
lemma bipartiteAliceLift_noncommProd
    {α : Type*} (s : Finset α) (f : α → Matrix n n ℂ)
    (comm : (s : Set α).Pairwise (fun x y => Commute (f x) (f y))) :
    bipartiteAliceLift (s.noncommProd f comm) =
      s.noncommProd (fun x => bipartiteAliceLift (f x))
        (fun _ hx _ hy hxy => bipartiteAliceLift_commute (comm hx hy hxy)) := by
  classical
  induction s using Finset.cons_induction_on with
  | empty =>
      simp [bipartiteAliceLift]
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons, Finset.noncommProd_cons]
      rw [← bipartiteAliceLift_mul, ih]

end MatrixUnitaries

/-!
## Generic presented-group construction

This section is independent of a concrete `Game`.  It starts with a
`LinearSystem S` and a proposed image of the solution-group generators.

The public constructor in this section is `solutionGroupRepresentation`.  It
handles the involution and centrality relators internally, so the caller only
needs to supply matrix commutation for variables in a common equation and the
equation-relator proofs themselves.
-/

section PresentedGroupConstruction

variable {S : LinearSystem}
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The intended image of the solution-group generators in unitary matrices.

This is the generator-level assignment that all later constructors try to
descend through the quotient defining `SolutionGroup S`:

```text
var j ↦ obs j
J     ↦ -I
```
-/
noncomputable def solutionGroupGeneratorImage
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j)) :
    SolutionGen S → unitary (Matrix n n ℂ)
  | .var j => observableMatrixUnitary (obs j) (obs_is_observable j)
  | .J => negOneMatrixUnitary

/-- Commuting matrices give commuting packaged unitary observables:
$$
  MN = NM \Longrightarrow \widehat M\,\widehat N = \widehat N\,\widehat M.
$$
This lifts same-equation commutation from matrices to units, which is the form
required by the relators in `SolutionGroup S`.
-/
lemma observableMatrixUnitary_commute_of_commute
    {M N : Matrix n n ℂ} {hM : IsObservable M} {hN : IsObservable N}
    (h : Commute M N) :
    Commute (observableMatrixUnitary M hM) (observableMatrixUnitary N hN) := by
  change observableMatrixUnitary M hM * observableMatrixUnitary N hN =
      observableMatrixUnitary N hN * observableMatrixUnitary M hM
  apply Subtype.ext
  exact h.eq

/-- The distinguished image of $J$, namely $-I$, commutes with every matrix unit:
$$
  U(-I) = (-I)U.
$$
This proves the centrality relators involving $J$ in the target unit group.
-/
lemma commute_negOneMatrixUnitary
    (U : unitary (Matrix n n ℂ)) :
    Commute U negOneMatrixUnitary := by
  change U * negOneMatrixUnitary = negOneMatrixUnitary * U
  apply Subtype.ext
  simp [negOneMatrixUnitary, involutiveMatrixUnitary]

/-- Construct a representation of `SolutionGroup S` from observable generator
images, same-equation commutation, and the equation-relator proofs. -/
noncomputable def solutionGroupRepresentation
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hsame : ∀ {j k}, SameEquation S j k → Commute (obs j) (obs k))
    (hequation : ∀ i, FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable)
      (equationRelator S i) = 1) :
    SolutionGroup S →* unitary (Matrix n n ℂ) :=
  have hrel :
      ∀ r ∈ solutionRelators S,
        FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable) r = 1 := by
    intro r hr
    rcases hr with hvar | hJ | hcentral | hcomm | heq
    · rcases hvar with ⟨j, rfl⟩
      simp [involutionRel, genVar, solutionGroupGeneratorImage]
    · subst r
      simp [involutionRel, genJ, solutionGroupGeneratorImage]
    · rcases hcentral with ⟨j, rfl⟩
      have h : Commute (solutionGroupGeneratorImage obs obs_is_observable (.var j))
                       (negOneMatrixUnitary (n := n)) :=
         commute_negOneMatrixUnitary _
      simpa [commuteRel, genVar, genJ, solutionGroupGeneratorImage, mul_assoc] using
        mul_inv_eq_one.mpr h.eq
    · rcases hcomm with ⟨j, k, _, hsameEq, rfl⟩
      have h : Commute (observableMatrixUnitary (obs j) (obs_is_observable j))
                       (observableMatrixUnitary (obs k) (obs_is_observable k)) :=
          observableMatrixUnitary_commute_of_commute (hsame hsameEq)
      simpa [commuteRel, genVar, solutionGroupGeneratorImage, mul_assoc] using
        mul_inv_eq_one.mpr h.eq
    · rcases heq with ⟨i, rfl⟩
      exact hequation i
  PresentedGroup.toGroup hrel

@[simp] lemma solutionGroupRepresentation_var
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hsame : ∀ {j k}, SameEquation S j k → Commute (obs j) (obs k))
    (hequation : ∀ i, FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable)
      (equationRelator S i) = 1)
    (j : Fin S.layout.s) :
    solutionGroupRepresentation obs obs_is_observable hsame hequation
        (SolutionGroup.var (S := S) j) =
      observableMatrixUnitary (obs j) (obs_is_observable j) := by
  simp [solutionGroupRepresentation, SolutionGroup.var,
    solutionGroupGeneratorImage]

@[simp] lemma solutionGroupRepresentation_J
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hsame : ∀ {j k}, SameEquation S j k → Commute (obs j) (obs k))
    (hequation : ∀ i, FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable)
      (equationRelator S i) = 1) :
    solutionGroupRepresentation obs obs_is_observable hsame hequation
        (SolutionGroup.J (S := S)) =
      negOneMatrixUnitary := by
  simp [solutionGroupRepresentation, SolutionGroup.J,
    solutionGroupGeneratorImage]

end PresentedGroupConstruction

/-!
## Game-level and EPR-level constructors

The previous section works for an arbitrary `LinearSystem`.  This section
specializes it to `game.toLinearSystem` and supplies equation-relator proofs
from the local identities produced by the EPR/local-loss pipeline.

The key bridge is:

```text
rowObservableProduct obs i = (-1) ^ (game.b i).val • I
  ↓ lift_equationRelator_of_rowIdentity
equationRelator game.toLinearSystem i maps to 1
```

The top-level constructor `solutionGroupRepresentationOfEPRLoss` obtains that
row identity from `local_matrix_identities_of_local_loss_annihilate_epr`.
-/

section RepresentationData

variable {G : Layout}
variable (game : Game G)
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (obs : Fin G.s → Matrix n n ℂ)

/-- The canonical ordered product over the support of row `i`.

The product is taken over the sorted support list.  This fixes an order that
matches `equationWord`, which is useful when translating between free-group
words and matrix products.
-/
noncomputable def orderedSupportProduct
    {M : Type*} [Monoid M]
    (f : Fin G.s → M) (i : Fin G.r) : M :=
  (((G.V i).sort (· ≤ ·)).map f).prod

/-- The local product of observables in equation `i`.

This is the matrix-side version of the equation word for row `i`, using the
same sorted support order as `equationWord`.
-/
noncomputable def rowObservableProduct
    (i : Fin G.r) :
    Matrix n n ℂ :=
  orderedSupportProduct (G := G) obs i

/-- Relate the sorted row product to `Finset.noncommProd`:
$$
  \prod_{j \in V_i}^{\mathrm{sorted}} f_j
    = \prod_{j \in V_i}^{\mathrm{noncomm}} f_j.
$$
This is the monoid-level support-product lemma.  The sorted list fixes the same
canonical order used by `equationWord`, while `noncommProd` is convenient for
strategy row products.  Pairwise commutation makes the two presentations agree.
-/
private lemma orderedSupportProduct_eq_noncommProd
    {M : Type*} [Monoid M]
    (f : Fin G.s → M)
    (i : Fin G.r)
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (f j.1) (f k.1))) :
    orderedSupportProduct (G := G) f i =
      (G.V i).attach.noncommProd (fun j => f j.1)
        (fun _ _ _ _ hjk => sameEquation_comm i hjk) := by
  let support : List (G.V i) :=
    ((G.V i).sort (· ≤ ·)).pmap
      (fun j hj =>
        ⟨j, by
          simpa using (Finset.mem_sort (s := G.V i) (r := (· ≤ ·))).mp hj⟩)
      (by intro _ hj; exact hj)
  have hsupport_toFinset : support.toFinset = (G.V i).attach := by
    ext j
    simp [support]
  have hsupport_prod :
      (support.map (fun j => f j.1)).prod =
        orderedSupportProduct (G := G) f i := by
    simp [support, orderedSupportProduct]
  have hsupport_nodup : support.Nodup := by
    dsimp [support]
    apply List.Nodup.pmap
    · intro _ _ _ _ h
      exact Subtype.ext_iff.mp h
    · exact Finset.sort_nodup (G.V i) (· ≤ ·)
  symm
  rw [← hsupport_toFinset]
  rw [Finset.noncommProd_toFinset]
  · exact hsupport_prod
  · exact hsupport_nodup

/-- Relate the sorted row observable product to the `noncommProd` used by
`ProjectorStrategy.aliceRowProd`:
$$
  \operatorname{rowObservableProduct}_i
    = \prod_{j \in V_i}^{\mathrm{noncomm}}\operatorname{obs}_j.
$$
`rowObservableProduct` uses a sorted list to match `equationWord`, while
`ProjectorStrategy.aliceRowProd` uses `Finset.noncommProd` over the attached row support.  This
bridge is useful when importing the row identity extracted from the EPR/SOS
pipeline.
-/
@[simp] lemma aliceRowProd_bipartite
    (strat : BipartiteObservableStrategy n G)
    (i : Fin G.r) :
    ProjectorStrategy.aliceRowProd strat.toProjectorStrategy i =
      bipartiteAliceLift (rowObservableProduct strat.obs i) := by
  unfold rowObservableProduct ProjectorStrategy.aliceRowProd
  rw [orderedSupportProduct_eq_noncommProd
    (f := strat.obs) (sameEquation_comm := strat.sameEquation_comm)]
  rw [bipartiteAliceLift_noncommProd]
  simp

/-- In `game.toLinearSystem`, `SameEquation` is exactly common row membership:
$$
  \operatorname{SameEquation}(j,k)
    \Longleftrightarrow \exists i,\; j \in V_i \land k \in V_i.
$$
This converts the generic presentation's commutation hypothesis into the
row-wise commutation data carried by an LCS observable strategy.
-/
private lemma sameEquation_toLinearSystem_iff
    (j k : Fin G.s) :
    SameEquation game.toLinearSystem j k ↔
      ∃ i : Fin G.r, j ∈ G.V i ∧ k ∈ G.V i := by
  simp [SameEquation, Game.toLinearSystem]

/-- The linear-system support of equation $i$ is the game row support $V_i$:
$$
  \operatorname{eqSupport}(\operatorname{game.toLinearSystem}, i) = V_i.
$$
This rewrite aligns the generic `equationWord` construction with the LCS row
support used in observable products.
-/
private lemma eqSupport_toLinearSystem
    (i : Fin G.r) :
    eqSupport game.toLinearSystem i = G.V i := by
  ext j
  simp [eqSupport, Game.toLinearSystem]

/-- Evaluate the free-group lift of a list of variable generators as matrices:
$$
  \operatorname{val}\!\left(\operatorname{lift}(\rho_0)
    \prod_\ell x_{\ell}\right)
    = \prod_\ell \operatorname{obs}_{\ell}.
$$
This list-level calculation is the basic evaluator for equation words before
the support list is specialized to a row.
-/
private lemma lift_genVar_list_prod_val {S : LinearSystem}
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (l : List (Fin S.layout.s)) :
    ((FreeGroup.lift
        (solutionGroupGeneratorImage (S := S)
          obs obs_is_observable)
        (l.map (genVar (S := S))).prod :
      unitary (Matrix n n ℂ)) : Matrix n n ℂ) =
        (l.map obs).prod := by
  induction l with
  | nil =>
      simp
  | cons j l ih =>
      simp [genVar, solutionGroupGeneratorImage, ih]

/-- Evaluating an equation word gives the corresponding row observable product:
$$
  \operatorname{val}\bigl(\operatorname{lift}(\rho_0)(w_i)\bigr)
    = \operatorname{rowObservableProduct}_i.
$$
This identifies the group word appearing in the equation relator with the
matrix product whose value is extracted from the EPR/local-loss argument.
-/
private lemma lift_equationWord_toLinearSystem_val
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (i : Fin G.r) :
    ((FreeGroup.lift
        (solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable)
      (equationWord game.toLinearSystem i) : unitary (Matrix n n ℂ)) :
      Matrix n n ℂ) =
        rowObservableProduct obs i := by
  classical
  simp only [equationWord, eqSupport_toLinearSystem, rowObservableProduct,
    orderedSupportProduct]
  exact lift_genVar_list_prod_val (S := game.toLinearSystem) obs obs_is_observable
    ((G.V i).sort (· ≤ ·))

/-- Turn a row matrix identity into the corresponding equation-relator proof:
if
$$
  \operatorname{rowObservableProduct}_i = (-1)^{b_i}I,
$$
then the equation relator maps to $1$:
$$
  \operatorname{lift}(\rho_0)(\operatorname{equationRelator}_i) = 1.
$$
This is the main algebraic bridge from row equations to the relator hypothesis
needed by the presented-group universal property.
-/
lemma lift_equationRelator_of_rowIdentity
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (i : Fin G.r)
    (hrow :
      rowObservableProduct obs i =
        (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ)) :
    FreeGroup.lift
        (solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable)
        (equationRelator game.toLinearSystem i) = 1 := by
  have hword := lift_equationWord_toLinearSystem_val game obs obs_is_observable i
  have hwordUnit :
      FreeGroup.lift
          (solutionGroupGeneratorImage (S := game.toLinearSystem) obs obs_is_observable)
          (equationWord game.toLinearSystem i) =
        solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable .J ^ (game.b i).val := by
    apply Subtype.ext
    rw [hword, hrow]
    simpa [solutionGroupGeneratorImage] using
      (negOneMatrixUnitary_pow_val (n := n) (b := game.b i)).symm
  have hbLinear : game.toLinearSystem.b i = game.b i := rfl
  simp [equationRelator, genJ, hwordUnit, hbLinear]

omit [DecidableEq n] in
/-- Convert row-wise commutation into `SameEquation` commutation for
`game.toLinearSystem`:
$$
  j,k \in V_i \Longrightarrow \operatorname{obs}_j\operatorname{obs}_k
    = \operatorname{obs}_k\operatorname{obs}_j.
$$
This supplies the generic constructor with the commutation hypothesis required
for every pair of variables that appears together in some equation.
-/
private lemma sameEquation_comm_of_row_comm
    (obs : Fin G.s → Matrix n n ℂ)
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    {j k : Fin G.s}
    (hjk : SameEquation game.toLinearSystem j k) :
    Commute (obs j) (obs k) := by
  rcases (sameEquation_toLinearSystem_iff game j k).mp hjk with
    ⟨i, hj, hk⟩
  by_cases h : (⟨j, hj⟩ : G.V i) = ⟨k, hk⟩
  · have hjk_eq : j = k := Subtype.ext_iff.mp h
    subst k
    exact Commute.refl _
  · exact sameEquation_comm i h

/-- Build the game-level representation from the row identities.
This is the natural intermediate constructor between the generic
presented-group layer and the EPR/local-loss extraction. -/
noncomputable def solutionGroupRepresentationOfRows
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    (hrow :
      ∀ i, rowObservableProduct obs i =
        (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ)) :
    SolutionGroup game.toLinearSystem →* unitary (Matrix n n ℂ) :=
  solutionGroupRepresentation
    (S := game.toLinearSystem) obs obs_is_observable
    (sameEquation_comm_of_row_comm game obs sameEquation_comm)
    (fun i => lift_equationRelator_of_rowIdentity game
      obs obs_is_observable i (hrow i))

/-- Extract the row equation from the EPR/local-loss hypothesis:
$$
  \operatorname{rowObservableProduct}_i = (-1)^{b_i}I.
$$
For each row $i$, the local loss for any support element contains the row SOS
term.  Since the row is assumed nonempty, one such support element is enough to
recover the row identity.  This isolates the analytic EPR/SOS step from the
presented-group construction.
-/
lemma rowObservableProduct_eq_sign_of_local_loss
    (strat : BipartiteObservableStrategy n G)
    (hNonempty : ∀ i, Nonempty (G.V i))
    (hLoss :
      ∀ i (j : G.V i),
        (localLossOperator game strat.toProjectorStrategy i j) *ᵥ (eprVec n) = 0)
    (i : Fin G.r) :
    rowObservableProduct strat.obs i =
      (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ) := by
  classical
  let row := rowObservableProduct strat.obs i
  change row = (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ)
  rcases hNonempty i with ⟨j⟩
  have hAlice :
      ProjectorStrategy.aliceObs strat.toProjectorStrategy i j = bipartiteAliceLift (strat.obs j.1) := by
    simp
  have hBob :
      ProjectorStrategy.bobObs strat.toProjectorStrategy j.1 = bipartiteBobLift (strat.obs j.1) := by
    simp
  have hRowLift :
      ProjectorStrategy.aliceRowProd strat.toProjectorStrategy i = bipartiteAliceLift row := by
    simp [row, aliceRowProd_bipartite (n := n) strat i]
  exact
    (local_matrix_identities_of_local_loss_annihilate_epr
      game n strat.toProjectorStrategy i j (strat.obs j.1) (strat.obs j.1) row
          (hLoss i j) hAlice hBob hRowLift (strat.isObservable j.1)).2.1

/-- End-to-end representation constructor from the EPR/local-loss hypothesis:
$$
  \operatorname{SolutionGroup}(\operatorname{game.toLinearSystem})
    \to \operatorname{U}(n),
  \qquad x_j \mapsto \operatorname{obs}_j,\quad J \mapsto -I.
$$
This is the main constructor in the file.  It extracts each row identity from
local-loss annihilation on $\Omega$, turns the row identity into an equation
relator proof, and then invokes the generic solution-group representation
constructor.
-/
noncomputable def solutionGroupRepresentationOfEPRLoss
    (strat : BipartiteObservableStrategy n G)
    (hNonempty : ∀ i, Nonempty (G.V i))
    (hLoss :
      ∀ i (j : G.V i),
        (localLossOperator game strat.toProjectorStrategy i j) *ᵥ (eprVec n) = 0) :
    SolutionGroup game.toLinearSystem →* unitary (Matrix n n ℂ) :=
  solutionGroupRepresentationOfRows game
    strat.obs strat.isObservable strat.sameEquation_comm
    (rowObservableProduct_eq_sign_of_local_loss game strat hNonempty hLoss)

end RepresentationData

end SolutionGroup

end MIPRE.LCS
