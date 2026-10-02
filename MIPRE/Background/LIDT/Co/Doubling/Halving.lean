/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Doubling.FinitePair
public import MIPRE.Background.LIDT.Co.Test.Defs

@[expose] public section

/-!
# The doubled model's quantities are role averages of the model's

Theorem C of `reports/c6b-paper-proofs.md`, §4 (Lemma 5), in the vocabulary of the port and of
`M`: every quantity of the doubled model `Doubling.model hM hψ` (`Co/Doubling/Model.lean`) built
from Born probabilities is the average of the same quantity of `M` over the two ways of assigning
the doubled players' blocks to the two players of `M`.

An element `x` of the doubled local algebra `Loc M = LocA M × LocB M` has the components
`compA hM x : 𝒜` and `compB hM x : ℬ`, its blocks pulled back along the `⋆`-isomorphisms of
`IsFinitePair.equivA` and `IsFinitePair.equivB`; on the report's local algebra `𝒜 × ℬ`, translated
by `Doubling.equiv`, they are the two coordinates (`compA_equiv`, `compB_equiv`).

* **Born probabilities** (`bornProb_model_eq`, `bornProb_model_equiv`):
  `bornProb_D(x, y) = ½ (bornProb_M(x¹, y²) + bornProb_M(y¹, x²))`.
* **The submeasurement consistency defect** (`qBipartiteConsDefect_model`): the port's
  `qBipartiteConsDefect` of two submeasurements of the doubled model is the average of the two
  defects `max 0 (total − match)` of `M`, exactly, since both are off-diagonal Born masses.
* **The disagreement** (`dis_model`, `dis_model_pair`) and **the inconsistency**
  (`inconsistency_model`, `inconsistency_model_pair`) of `MIPRE/Foundations/` halve in the same
  way. A POVM `G` of the doubled local algebra has the POVMs `povmA hM G` of `𝒜` and
  `povmB hM G` of `ℬ` as components (the report's `G¹`, `G²`), and a POVM of `𝒜 × ℬ` is translated
  by `povmPair`, with components its coordinates (`povmA_povmPair`, `povmB_povmPair`).

The players' algebras of `M` are star-ordered here, as in `MIPRE.LIDT.Simul.SoundIn`, so that the
components of a positive element are positive and POVMs transport.
-/

namespace MIPRE.LIDT.Co.Doubling

open scoped InnerProductSpace
open MIPRE.OperatorMatrix

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
  (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1)

/-! ## The components of the doubled local algebra -/

/-- **The first component** of an element of the doubled local algebra, in `𝒜`: its first block,
pulled back along `IsFinitePair.equivA`. -/
noncomputable def compA : Loc M →⋆ₐ[ℂ] 𝒜 :=
  hM.equivA.symm.toStarAlgHom.comp (StarAlgHom.fst ℂ (LocA M) (LocB M))

/-- **The second component** of an element of the doubled local algebra, in `ℬ`: its second block,
pulled back along `IsFinitePair.equivB`. -/
noncomputable def compB : Loc M →⋆ₐ[ℂ] ℬ :=
  hM.equivB.symm.toStarAlgHom.comp (StarAlgHom.snd ℂ (LocA M) (LocB M))

/-- The operator of the first component is the first block. -/
theorem π_πA_compA (x : Loc M) : M.π (M.πA (compA hM x)) = x.1 :=
  hM.π_πA_equivA_symm x.1

/-- The operator of the second component is the second block. -/
theorem π_πB_compB (x : Loc M) : M.π (M.πB (compB hM x)) = x.2 :=
  hM.π_πB_equivB_symm x.2

/-- The first component of a translated element of `𝒜 × ℬ` is its first coordinate. -/
@[simp]
theorem compA_equiv (n : 𝒜 × ℬ) : compA hM (equiv hM n) = n.1 :=
  hM.equivA.symm_apply_apply n.1

/-- The second component of a translated element of `𝒜 × ℬ` is its second coordinate. -/
@[simp]
theorem compB_equiv (n : 𝒜 × ℬ) : compB hM (equiv hM n) = n.2 :=
  hM.equivB.symm_apply_apply n.2

/-- The Born probability of `M` at two components is the operator Born probability of the
blocks. -/
theorem bornProb_compA_compB (x y : Loc M) :
    M.bornProb (compA hM x) (compB hM y) =
      Op.qform M.ψ ((x.1 : M.H →L[ℂ] M.H) * (y.2 : M.H →L[ℂ] M.H)) := by
  rw [BipartiteModel.bornProb, StateModel.qform, map_mul, π_πA_compA, π_πB_compB]

/-! ## Born probabilities -/

/-- **The role average for Born probabilities** (Theorem C of `reports/c6b-paper-proofs.md`, §4):
`bornProb_D(x, y) = ½ (bornProb_M(x¹, y²) + bornProb_M(y¹, x²))`. -/
theorem bornProb_model_eq (x y : Loc M) :
    (model hM hψ).toBipartite.bornProb x y =
      2⁻¹ * (M.bornProb (compA hM x) (compB hM y) + M.bornProb (compA hM y) (compB hM x)) := by
  rw [bornProb_model, bornProb_compA_compB, bornProb_compA_compB]

/-- **The role average for Born probabilities**, on the report's local algebra `𝒜 × ℬ`:
`bornProb_D((a, b), (a', b')) = ½ (bornProb_M(a, b') + bornProb_M(a', b))`. -/
theorem bornProb_model_equiv (n n' : 𝒜 × ℬ) :
    (model hM hψ).toBipartite.bornProb (equiv hM n) (equiv hM n') =
      2⁻¹ * (M.bornProb n.1 n'.2 + M.bornProb n'.1 n.2) := by
  rw [bornProb_model_eq, compA_equiv, compB_equiv, compA_equiv, compB_equiv]

/-! ## The halving of the consistency quantities -/

/-- The defect `max 0 (total − match)` of a nonnegative double sum is its off-diagonal part. -/
theorem max_sum_sub_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ι → ℝ}
    (hf : ∀ a b, 0 ≤ f a b) :
    max 0 (∑ a, ∑ b, f a b - ∑ a, f a a) = ∑ a, ∑ b, if a = b then 0 else f a b := by
  have hrow : ∀ a, ∑ b, f a b = f a a + ∑ b, if a = b then 0 else f a b := fun a => by
    rw [← Fintype.sum_ite_eq a (f a), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp_all
  have hoff : 0 ≤ ∑ a, ∑ b, if a = b then (0 : ℝ) else f a b :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
      split_ifs
      exacts [le_rfl, hf a b]
  rw [Finset.sum_congr rfl fun a _ => hrow a, Finset.sum_add_distrib, add_sub_cancel_left,
    max_eq_right hoff]

/-- The off-diagonal part of a role-averaged double sum is the average of the two off-diagonal
parts, the second with its indices exchanged. -/
theorem sum_ne_half {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ι → ℝ) :
    (∑ a, ∑ b, if a = b then 0 else 2⁻¹ * (f a b + g b a)) =
      2⁻¹ * ((∑ a, ∑ b, if a = b then 0 else f a b) +
        ∑ a, ∑ b, if a = b then 0 else g a b) := by
  have hg : (∑ a, ∑ b, if a = b then (0 : ℝ) else g b a) =
      ∑ a, ∑ b, if a = b then 0 else g a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      simp only [eq_comm]
  rw [← hg, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

variable [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The Born probabilities of `M` at the components of nonnegative elements are nonnegative. -/
theorem bornProb_comp_nonneg {x y : Loc M} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ M.bornProb (compA hM x) (compB hM y) :=
  M.bornProb_nonneg (map_nonneg (compA hM) hx) (map_nonneg (compB hM) hy)

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The total Born probability of two submeasurements of the doubled local algebra, at the
components, is the double sum of the outcome Born probabilities. -/
theorem bornProb_total_comp {Outcome : Type*} [Fintype Outcome] (X Y : SubMeas Outcome (Loc M)) :
    M.bornProb (compA hM X.total) (compB hM Y.total) =
      ∑ a, ∑ b, M.bornProb (compA hM (X.outcome a)) (compB hM (Y.outcome b)) := by
  rw [← X.sum_eq_total, ← Y.sum_eq_total, map_sum, map_sum, M.bornProb_sum_left]
  exact Finset.sum_congr rfl fun a _ => M.bornProb_sum_right _ _ _

/-- **The submeasurement consistency defect halves** (Theorem C, Lemma 5 of
`reports/c6b-paper-proofs.md`, §4): the port's bipartite defect of two submeasurements of the
doubled model is the average of the two defects `max 0 (total − match)` of `M`, at the components
`X¹, Y²` and `Y¹, X²`. -/
theorem qBipartiteConsDefect_model {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (X Y : SubMeas Outcome (Loc M)) :
    (model hM hψ).qBipartiteConsDefect X Y =
      2⁻¹ * (max 0 (M.bornProb (compA hM X.total) (compB hM Y.total) -
          ∑ a, M.bornProb (compA hM (X.outcome a)) (compB hM (Y.outcome a))) +
        max 0 (M.bornProb (compA hM Y.total) (compB hM X.total) -
          ∑ a, M.bornProb (compA hM (Y.outcome a)) (compB hM (X.outcome a)))) := by
  rw [SymModel.qBipartiteConsDefect_eq_sum_ne, bornProb_total_comp, bornProb_total_comp,
    max_sum_sub_diag fun a b => bornProb_comp_nonneg hM (X.outcome_pos a) (Y.outcome_pos b),
    max_sum_sub_diag fun a b => bornProb_comp_nonneg hM (Y.outcome_pos a) (X.outcome_pos b),
    ← sum_ne_half]
  simp only [bornProb_model_eq]

/-! ## POVMs -/

section POVM

variable {Λ : Type*} [Fintype Λ]

/-- **The first components of a POVM of the doubled local algebra**, a POVM of `𝒜` (the report's
`G¹`). -/
noncomputable def povmA (P : POVMIn Λ (Loc M)) : POVMIn Λ 𝒜 :=
  P.mapHom (compA hM)

/-- **The second components of a POVM of the doubled local algebra**, a POVM of `ℬ` (the report's
`G²`). -/
noncomputable def povmB (P : POVMIn Λ (Loc M)) : POVMIn Λ ℬ :=
  P.mapHom (compB hM)

/-- **The translation of a POVM of the report's local algebra `𝒜 × ℬ`**, a POVM of the doubled
local algebra. -/
noncomputable def povmPair (P : POVMIn Λ (𝒜 × ℬ)) : POVMIn Λ (Loc M) :=
  P.mapHom (equiv hM).toStarAlgHom

omit [PartialOrder ℬ] [StarOrderedRing ℬ] in
/-- The operators of `povmA hM P` are the first components of those of `P`. -/
@[simp]
theorem povmA_op (P : POVMIn Λ (Loc M)) (a : Λ) : (povmA hM P).op a = compA hM (P.op a) :=
  rfl

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] in
/-- The operators of `povmB hM P` are the second components of those of `P`. -/
@[simp]
theorem povmB_op (P : POVMIn Λ (Loc M)) (a : Λ) : (povmB hM P).op a = compB hM (P.op a) :=
  rfl

/-- The operators of `povmPair hM P` are the translations of those of `P`. -/
@[simp]
theorem povmPair_op (P : POVMIn Λ (𝒜 × ℬ)) (a : Λ) : (povmPair hM P).op a = equiv hM (P.op a) :=
  rfl

/-- The first components of a translated POVM of `𝒜 × ℬ` are its first coordinates. -/
@[simp]
theorem povmA_povmPair (P : POVMIn Λ (𝒜 × ℬ)) : povmA hM (povmPair hM P) = P.fst :=
  POVMIn.ext' fun a => compA_equiv hM (P.op a)

/-- The second components of a translated POVM of `𝒜 × ℬ` are its second coordinates. -/
@[simp]
theorem povmB_povmPair (P : POVMIn Λ (𝒜 × ℬ)) : povmB hM (povmPair hM P) = P.snd :=
  POVMIn.ext' fun a => compB_equiv hM (P.op a)

/-- **The disagreement halves**: the disagreement of two POVMs of the doubled model is the average
of the disagreements of `M` at their components. -/
theorem dis_model (P Q : POVMIn Λ (Loc M)) :
    (model hM hψ).toBipartite.dis P Q =
      2⁻¹ * (M.dis (povmA hM P) (povmB hM Q) + M.dis (povmA hM Q) (povmB hM P)) := by
  simp only [BipartiteModel.dis, povmA_op, povmB_op, bornProb_model_eq, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  ring

/-- **The disagreement halves**, for POVMs of the report's local algebra `𝒜 × ℬ`. -/
theorem dis_model_pair (P Q : POVMIn Λ (𝒜 × ℬ)) :
    (model hM hψ).toBipartite.dis (povmPair hM P) (povmPair hM Q) =
      2⁻¹ * (M.dis P.fst Q.snd + M.dis Q.fst P.snd) := by
  rw [dis_model, povmA_povmPair, povmB_povmPair, povmA_povmPair, povmB_povmPair]

variable [DecidableEq Λ] {X : Type*} [Fintype X]

/-- **The inconsistency halves**: the inconsistency of two families of POVMs of the doubled model
is the average of the inconsistencies of `M` at their components. -/
theorem inconsistency_model (μ : X → ℝ) (P Q : X → POVMIn Λ (Loc M)) :
    (model hM hψ).toBipartite.inconsistency μ P Q =
      2⁻¹ * (M.inconsistency μ (fun x => povmA hM (P x)) (fun x => povmB hM (Q x)) +
        M.inconsistency μ (fun x => povmA hM (Q x)) (fun x => povmB hM (P x))) := by
  simp only [BipartiteModel.inconsistency, povmA_op, povmB_op, bornProb_model_eq, sum_ne_half,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => by ring

/-- **The inconsistency halves**, for families of POVMs of the report's local algebra `𝒜 × ℬ`. -/
theorem inconsistency_model_pair (μ : X → ℝ) (P Q : X → POVMIn Λ (𝒜 × ℬ)) :
    (model hM hψ).toBipartite.inconsistency μ (fun x => povmPair hM (P x))
        (fun x => povmPair hM (Q x)) =
      2⁻¹ * (M.inconsistency μ (fun x => (P x).fst) (fun x => (Q x).snd) +
        M.inconsistency μ (fun x => (Q x).fst) (fun x => (P x).snd)) := by
  rw [inconsistency_model]
  simp only [povmA_povmPair, povmB_povmPair]

end POVM

end MIPRE.LIDT.Co.Doubling

end
