/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Tsirelson.Algebra
import MIPRE.Foundations.Tsirelson.Conditional

/-!
# `C_qc` is closed, and `C_qa ⊆ C_qc`

The compactness step of the Tsirelson route (`planning/tsirelson-campaign.md`, §3.3): the set
`C_qc` of commuting-operator correlations is compact, hence closed, in every finite scenario,
so `C_qa = closure C_q ⊆ C_qc`. With the conditional consumer of
`MIPRE.Foundations.Tsirelson.Conditional`, this reduces the negative answer to Tsirelson's
problem, `C_qa ⊊ C_qc` (blueprint `cor:tsirelson`), to the halting reduction and an upper
semidecider for the commuting-operator value (`tsirelson_of_upperRE`).

**The state space in coordinates.** A `ℂ`-linear functional on the game algebra
`NCPoly (Gen X Y A B)` is determined by its values on words, and every function
`φ : FreeMonoid (Gen X Y A B) → ℂ` extends linearly (`extend φ`, through the monomial basis;
`extend_single_one`, `extend_apply_single_one`). For a fixed polynomial `z`, `extend φ z` is a
finite combination of coordinates of `φ`, so it is continuous in `φ` for the product topology
(`continuous_extend_apply`). The state space `stateSpace X Y A B` is the set of `φ` whose
extension is a cone state (`MIPRE.Tsirelson.IsConeState`: `L 1 = 1` and `0 ≤ Re L m` for every
`m` in the cone `M`). Each of these conditions is closed, so the state space is closed
(`isClosed_stateSpace`).

**Boundedness.** A cone state is bounded by `1` on every word `w`
(`IsConeState.norm_map_single_one_le`): `1 - w⋆ w ∈ M` by telescoping, so for `|α| = 1`,
`2·1 + α w + (α w)⋆ = (1 + α w)⋆ (1 + α w) + (1 - w⋆ w) ∈ M`, and `L` of it is
`2 + 2 Re (α L w)`; the choice `α = -conj (L w) / |L w|` gives `|L w| ≤ 1`. So the state space
lies in the product of closed unit disks, and it is compact by Tychonoff
(`isCompact_stateSpace`).

**The image.** The map `φ ↦ (x, y, a, b) ↦ Re φ(e_xa f_yb)` (`correlationOf`) is continuous,
and it maps the state space onto `C_qc` (`image_correlationOf_stateSpace`): this is
`MIPRE.Tsirelson.mem_Cqc_iff`, whose two directions are the GNS strategy of a cone state and the
state of a strategy. Hence `C_qc` is compact (`MIPRE.isCompact_Cqc`) and closed
(`MIPRE.isClosed_Cqc`).

## Main declarations

* `Tsirelson.extend`, `Tsirelson.continuous_extend_apply`;
* `Tsirelson.IsConeState.norm_map_single_one_le`;
* `Tsirelson.stateSpace`, `Tsirelson.isClosed_stateSpace`, `Tsirelson.isCompact_stateSpace`;
* `Tsirelson.correlationOf`, `Tsirelson.image_correlationOf_stateSpace`;
* `isCompact_Cqc`, `isClosed_Cqc`, `Cqa_subset_Cqc`, `tsirelson_of_upperRE`.
-/

noncomputable section

open ComplexConjugate

namespace MIPRE

namespace Tsirelson

/-! ## Functionals from their values on words -/

section Extend

variable {G : Type*}

/-- The linear extension of word values `φ : FreeMonoid G → ℂ` to a `ℂ`-linear functional on
`NCPoly G`: `Σ_w c_w w ↦ Σ_w c_w φ w`. -/
def extend (φ : FreeMonoid G → ℂ) : NCPoly G →ₗ[ℂ] ℂ :=
  NCPoly.basis.constr ℂ φ

/-- The linear extension, as a finite sum over the support of the coefficients. -/
theorem extend_apply (φ : FreeMonoid G → ℂ) (z : NCPoly G) :
    extend φ z = ∑ w ∈ z.coeff.support, z.coeff w * φ w := by
  rw [extend, Module.Basis.constr_apply]
  rfl

/-- The linear extension takes the prescribed value on each word. -/
@[simp] theorem extend_single_one (φ : FreeMonoid G → ℂ) (w : FreeMonoid G) :
    extend φ (NCPoly.single w 1) = φ w :=
  NCPoly.basis.constr_basis ℂ φ w

/-- A linear functional is the linear extension of its values on words. -/
theorem extend_apply_single_one (L : NCPoly G →ₗ[ℂ] ℂ) :
    extend (fun w => L (NCPoly.single w 1)) = L :=
  NCPoly.basis.constr_self ℂ L

/-- For a fixed polynomial, the linear extension is continuous in the word values, for the
product topology on `FreeMonoid G → ℂ`. -/
theorem continuous_extend_apply (z : NCPoly G) :
    Continuous fun φ : FreeMonoid G → ℂ => extend φ z := by
  simp only [extend_apply]
  exact continuous_finsetSum _ fun w _ => continuous_const.mul (continuous_apply w)

end Extend

/-! ## Cone states are bounded on words -/

section Bound

variable {X Y A B : Type*} [Fintype A] [Fintype B]

/-- **A cone state is bounded by `1` on words.** With `c = L w` and `α = -conj c / |c|`, the
element `2·1 + α w + (α w)⋆` lies in the cone (`NCPoly.herm_add_const_mem`, from
`1 - w⋆ w ∈ M`), and its value under `L` is `2 + 2 Re (α c) = 2 - 2 |c|`. -/
theorem IsConeState.norm_map_single_one_le {L : NCPoly (Gen X Y A B) →ₗ[ℂ] ℂ}
    (hL : IsConeState L) (w : FreeMonoid (Gen X Y A B)) : ‖L (NCPoly.single w 1)‖ ≤ 1 := by
  set s : NCPoly (Gen X Y A B) := NCPoly.single w 1
  obtain ⟨c, hcs⟩ : ∃ c, L s = c := ⟨_, rfl⟩
  rw [hcs]
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, norm_zero]; exact zero_le_one
  have hn : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc)
  obtain ⟨α, hαdef⟩ : ∃ α : ℂ, α = -conj c / ‖c‖ := ⟨_, rfl⟩
  have hα : Complex.normSq α = 1 := by
    rw [hαdef, Complex.normSq_div, Complex.normSq_neg, Complex.normSq_conj,
      Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    field_simp [norm_ne_zero_iff.2 hc]
  have hαc : α * c = -‖c‖ := by
    rw [hαdef, div_mul_eq_mul_div, neg_mul, Complex.conj_mul', neg_div, sq, mul_div_assoc,
      div_self hn, mul_one]
  have h := hL.re_nonneg _ (NCPoly.herm_add_const_mem
    (NCPoly.one_sub_star_word_mem (R := rels X Y A B) one_sub_gen_mul_gen_mem w) α)
  rw [hα, map_add, map_add, ← Complex.coe_smul, map_smul, hL.map_one, hL.map_star, map_smul,
    hcs] at h
  simp only [smul_eq_mul, hαc] at h
  norm_num at h
  linarith

end Bound

/-! ## The state space in coordinates -/

section StateSpace

variable (X Y A B : Type*) [Fintype A] [Fintype B]

/-- **The state space of the game algebra**, in coordinates: the word values
`φ : FreeMonoid (Gen X Y A B) → ℂ` whose linear extension is a cone state. -/
def stateSpace : Set (FreeMonoid (Gen X Y A B) → ℂ) :=
  {φ | IsConeState (extend φ)}

variable {X Y A B}

/-- Membership in the state space, unfolded: normalisation and positivity on the cone. -/
theorem mem_stateSpace_iff {φ : FreeMonoid (Gen X Y A B) → ℂ} :
    φ ∈ stateSpace X Y A B ↔
      extend φ 1 = 1 ∧ ∀ m ∈ cone X Y A B, 0 ≤ (extend φ m).re :=
  ⟨fun h => ⟨h.map_one, h.re_nonneg⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **The state space is closed** in the product topology: each defining condition involves
finitely many coordinates, continuously. -/
theorem isClosed_stateSpace : IsClosed (stateSpace X Y A B) := by
  have h : stateSpace X Y A B = {φ | extend φ 1 = 1} ∩
      ⋂ m ∈ cone X Y A B, {φ | 0 ≤ (extend φ m).re} := by
    ext φ
    simp only [mem_stateSpace_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact (isClosed_eq (continuous_extend_apply 1) continuous_const).inter
    (isClosed_biInter fun m _ => isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_extend_apply m)))

/-- The state space lies in the product of closed unit disks. -/
theorem stateSpace_subset_pi :
    stateSpace X Y A B ⊆ Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1 := by
  intro φ hφ w _
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := IsConeState.norm_map_single_one_le hφ w
  rwa [extend_single_one] at h

/-- **The state space is compact**: a closed subset of a product of closed disks
(Tychonoff). -/
theorem isCompact_stateSpace : IsCompact (stateSpace X Y A B) :=
  (isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset
    isClosed_stateSpace stateSpace_subset_pi

end StateSpace

section CorrelationOf

variable {X Y A B : Type*}

/-- The correlation of word values `φ`: `Re φ(e_xa f_yb)`, read through the linear
extension. -/
def correlationOf (φ : FreeMonoid (Gen X Y A B) → ℂ) : X → Y → A → B → ℝ :=
  fun x y a b => (extend φ (eG x a * fG y b)).re

/-- The correlation of word values is continuous in them. -/
theorem continuous_correlationOf :
    Continuous (correlationOf : (FreeMonoid (Gen X Y A B) → ℂ) → X → Y → A → B → ℝ) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ =>
    Complex.continuous_re.comp (continuous_extend_apply _)

end CorrelationOf

section Image

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **`C_qc` is the image of the state space** under `φ ↦ Re φ(e_xa f_yb)`: a cone state gives
a commuting-operator strategy by GNS, and a strategy gives a cone state (`mem_Cqc_iff`). -/
theorem image_correlationOf_stateSpace : correlationOf '' stateSpace X Y A B = Cqc X Y A B := by
  ext p
  rw [mem_Cqc_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨extend φ, hφ, rfl⟩
  · rintro ⟨L, hL, rfl⟩
    refine ⟨fun w => L (NCPoly.single w 1), ?_, ?_⟩
    · change IsConeState (extend _)
      rwa [extend_apply_single_one]
    · unfold correlationOf
      rw [extend_apply_single_one]

end Image

end Tsirelson

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- **`C_qc` is compact**: it is the continuous image of the compact state space. -/
theorem isCompact_Cqc : IsCompact (Cqc X Y A B) := by
  rw [← Tsirelson.image_correlationOf_stateSpace]
  exact Tsirelson.isCompact_stateSpace.image Tsirelson.continuous_correlationOf

/-- **`C_qc` is closed.** -/
theorem isClosed_Cqc : IsClosed (Cqc X Y A B) :=
  isCompact_Cqc.isClosed

/-- **`C_qa ⊆ C_qc`**: `C_q ⊆ C_qc`, and `C_qc` is closed. -/
theorem Cqa_subset_Cqc : Cqa X Y A B ⊆ Cqc X Y A B :=
  Cqa_subset_Cqc_of_isClosed isClosed_Cqc

/-- **Tsirelson's problem, negative answer, given an upper semidecider** (blueprint
`cor:tsirelson`): `C_qa ⊊ C_qc` in some finite scenario, given the halting reduction and an
upper semidecider for the commuting-operator value. Closedness of `C_qc`, the other hypothesis
of `tsirelson_of_upperRE_of_isClosed`, is `isClosed_Cqc`. -/
theorem tsirelson_of_upperRE (hred : HaltingReductionQuantum) (hU : CommutingUpperRE) :
    ∃ nX nA : ℕ, Cqa (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) ⊂
      Cqc (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)) :=
  tsirelson_of_upperRE_of_isClosed hred hU fun _ _ => isClosed_Cqc

end MIPRE
