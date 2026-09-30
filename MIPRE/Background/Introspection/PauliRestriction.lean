/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.PauliRestriction
public import MIPRE.Background.QLD.CLTransport

@[expose] public section

/-! # Actual Pauli strategies extracted by restricting introspection

The strategy is built on exactly the original finite registers and state.
Outer malformed answers are completed at fixed answers; the binary CL
strategy then pulls back to the actual QLD game along canonical encodings.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the strategies are projective
strategies of one model `Ξ`, and the restricted QLD strategy is a strategy of the same model, so
the state is unchanged by construction.
-/

noncomputable section
namespace MIPRE.Introspection.PauliRestriction
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]

def pauliCheck (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QLD.Ty) (x y : Fin ((3*m+3)*t) → ZMod 2) :
    QLD.Answer F m d → QLD.Answer F m d → Bool :=
  QLD.accepts hm (QLD.PauliCL.binaryQuestion b p x) (QLD.PauliCL.binaryQuestion b q y)

def fullGame (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
    (D : (ι → F₀) → (ι → F₀) → A → A → Bool) :=
  TypedEstimates.parsedGame QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm b) L project D (pauliCheck hm b)

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {Ξ : BipartiteModel 𝒞 𝒜 ℬ}

variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : Ξ.ProjStrat (fullGame hm b L project D))

def alice (a₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    POVMIn (QLD.Answer F m d) 𝒜 :=
  completePauliPOVM a₀ (S.PA (.inl q.1,q.2))

def bob (b₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    POVMIn (QLD.Answer F m d) ℬ :=
  completePauliPOVM b₀ (S.PB (.inl q.1,q.2))

theorem alice_isPVM (a₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    IsPVMIn (alice hm b L project D S a₀ q).op :=
  completePauliPOVM_isPVM _ _ (S.projA _)

theorem bob_isPVM (b₀ : QLD.Answer F m d) (q : QLD.PauliCL.BinaryQuestion m t) :
    IsPVMIn (bob hm b L project D S b₀ q).op :=
  completePauliPOVM_isPVM _ _ (S.projB _)

/-- Restriction and answer completion preserve the actual original state. -/
def binaryStrategy (a₀ b₀ : QLD.Answer F m d) :
    Ξ.ProjStrat (QLD.PauliCL.binaryGame (d := d) hm b) where
  PA := alice hm b L project D S a₀
  PB := bob hm b L project D S b₀
  projA := alice_isPVM hm b L project D S a₀
  projB := bob_isPVM hm b L project D S b₀
  ψ_unit := S.ψ_unit

theorem binaryStrategy_failAt_le (a₀ b₀ : QLD.Answer F m d)
    (x y : QLD.PauliCL.BinaryQuestion m t) :
    Ξ.condFail (QLD.PauliCL.binaryGame (d := d) hm b)
        (binaryStrategy hm b L project D S a₀ b₀).PA
        (binaryStrategy hm b L project D S a₀ b₀).PB x y ≤
      Ξ.condFail (fullGame hm b L project D) S.PA S.PB (.inl x.1,x.2) (.inl y.1,y.2) :=
  TypedEstimates.completed_pauli_condFail_le QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm b) L project D (pauliCheck hm b)
    (QLD.PauliCL.binaryGame hm b) (fun _ _ _ _ => rfl) Ξ
    (fun q => S.PA q) (fun q => S.PB q) a₀ b₀ x y

/-- The full ordered-edge count is a uniform soundness factor for restriction. -/
theorem binaryStrategy_failure_le (a₀ b₀ : QLD.Answer F m d) {ε : ℝ}
    (hS : 1 - S.value ≤ ε) :
    1 - (binaryStrategy hm b L project D S a₀ b₀).value ≤
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε := by
  let R := binaryStrategy hm b L project D S a₀ b₀
  let G := QLD.PauliCL.binaryGame (d := d) hm b
  let n : ℝ := Fintype.card (Fin ((3*m+3)*t) → ZMod 2)
  let c : ℝ := (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  let : Nonempty QLD.TyEdge := ⟨⟨(.pair,.pair), by decide⟩⟩
  have he : (0 : ℝ) < Fintype.card QLD.TyEdge := by exact_mod_cast Fintype.card_pos
  have havg (e : QLD.TyEdge) :
      (∑ z : Fin ((3*m+3)*t) → ZMod 2,
        Ξ.condFail G R.PA R.PB
          (e.val.1, (QLD.PauliCL.binaryPresentation hm b e.val.1).eval z)
          (e.val.2, (QLD.PauliCL.binaryPresentation hm b e.val.2).eval z)) / n ≤ c := by
    have hedge : TypeGraph.Adj (ℓ := ℓ) QLD.adj (.pauli .X) (.pauli .Z)
        (.inl e.val.1) (.inl e.val.2) := by
      change TypeGraph.adj _ _ _ _ _ = true
      rw [TypeGraph.adj_pauli QLD.adj _ _ QLD.adj_symm QLD.adj_self]
      exact e.property
    have hf := TypedEstimates.typed_edge_mean_failure_le QLD.adj (.pauli .X) (.pauli .Z)
      (QLD.PauliCL.binaryPresentation hm b)
      (TypedEstimates.questionCheck L (.pauli .X) (.pauli .Z) project D (pauliCheck hm b))
      Ξ S.ψ_unit (fun q => S.PA q) (fun q => S.PB q)
      (by simpa only [BipartiteModel.ProjStrat.value, fullGame,
        TypedEstimates.parsedGame] using hS)
      (.inl e.val.1) (.inl e.val.2) hedge
    apply le_trans (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun z _ =>
      binaryStrategy_failAt_le hm b L project D S a₀ b₀ _ _)) hn.le)
    exact hf
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ (univ : Finset QLD.TyEdge)) => havg e)
  have hform : 1 - R.value =
      (∑ e : QLD.TyEdge, (∑ z : Fin ((3*m+3)*t) → ZMod 2,
        Ξ.condFail G R.PA R.PB
          (e.val.1, (QLD.PauliCL.binaryPresentation hm b e.val.1).eval z)
          (e.val.2, (QLD.PauliCL.binaryPresentation hm b e.val.2).eval z)) / n) /
        Fintype.card QLD.TyEdge := by
    rw [BipartiteModel.ProjStrat.value, Ξ.one_sub_povmValue_eq]
    change (∑ x, ∑ y, SampledGame.dist (QLD.PauliCL.binaryQuery hm b false)
      (QLD.PauliCL.binaryQuery hm b true) x y * Ξ.condFail G R.PA R.PB x y) = _
    rw [SampledGame.sum_dist_mul]
    simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
      QLD.PauliCL.binaryQuery, Bool.false_eq_true, ↓reduceIte, ← Finset.sum_div, div_div, n]
    congr 1
    ring
  rw [hform]
  calc _ ≤ (∑ _ : QLD.TyEdge, c) / Fintype.card QLD.TyEdge :=
      div_le_div_of_nonneg_right hs he.le
    _ = c := by simp [he.ne']

/-- The actual QLD strategy obtained by canonical question pullback. -/
def strategy (a₀ b₀ : QLD.Answer F m d) : Ξ.ProjStrat (QLD.qldGame (d := d) hm) :=
  QLD.PauliCL.pullbackStrategy hm b (binaryStrategy hm b L project D S a₀ b₀)

theorem strategy_failure_le (a₀ b₀ : QLD.Answer F m d) {ε : ℝ} (hS : 1 - S.value ≤ ε) :
    1 - (strategy hm b L project D S a₀ b₀).value ≤
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε := by
  rw [strategy, QLD.PauliCL.pullbackStrategy_value]
  exact binaryStrategy_failure_le hm b L project D S a₀ b₀ hS

theorem strategy_pauli_A (a₀ b₀ : QLD.Answer F m d) (W : QLD.Bas) :
    (strategy hm b L project D S a₀ b₀).PA (.pauli W) =
      completePauliPOVM a₀ (S.PA (QuestionType.pauli (.pauli W),0)) :=
  QLD.PauliCL.pullbackStrategy_pauli_A hm b (binaryStrategy hm b L project D S a₀ b₀) W

theorem strategy_pauli_B (a₀ b₀ : QLD.Answer F m d) (W : QLD.Bas) :
    (strategy hm b L project D S a₀ b₀).PB (.pauli W) =
      completePauliPOVM b₀ (S.PB (QuestionType.pauli (.pauli W),0)) :=
  QLD.PauliCL.pullbackStrategy_pauli_B hm b (binaryStrategy hm b L project D S a₀ b₀) W

/-- Choosing a scalar completion answer leaves every genuine Pauli answer
operator exactly unchanged, even when malformed outer answers have mass. -/
theorem strategy_pauliAns_A (W : QLD.Bas) (a : (Fin m → Bool) → F) :
    ((strategy hm b L project D S (.val 0) (.val 0)).PA (.pauli W)).op (.pauliAns a) =
      (S.PA (QuestionType.pauli (.pauli W),0)).op (.pauli (.pauliAns a)) := by
  rw [strategy_pauli_A, completePauliPOVM_mats_of_ne _ _ (by intro h; cases h)]

theorem strategy_pauliAns_B (W : QLD.Bas) (a : (Fin m → Bool) → F) :
    ((strategy hm b L project D S (.val 0) (.val 0)).PB (.pauli W)).op (.pauliAns a) =
      (S.PB (QuestionType.pauli (.pauli W),0)).op (.pauli (.pauliAns a)) := by
  rw [strategy_pauli_B, completePauliPOVM_mats_of_ne _ _ (by intro h; cases h)]

end MIPRE.Introspection.PauliRestriction
end

end
