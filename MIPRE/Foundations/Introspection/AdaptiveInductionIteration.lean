/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.Introspection.AdaptiveInductionStep
public import MIPRE.Foundations.Introspection.AdaptiveIterationBudget
public import MIPRE.Foundations.ModelOver

@[expose] public section

/-! # Finite iteration of the actual Alice Introspect replacement

Starting with the original projective family, each successor is constructed from the current
game's tests. The numerical inverse threshold discharges every smallness premise. All other
questions retain their extensions, and all fixed hiding errors and both primitive Z errors are
preserved exactly.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`). Each stage adjoins to the
first player an ancilla register whose size the Kraus–Halmos dilation chooses
(`exists_intro_successor`), so the model changes type from one stage to the next: the iterated
model is a model over the second player's algebra, packed with its algebras (`ModelOver`). Every
POVM strategy of it reduces to one of the original model (`BipartiteModel.POVMReduces`), which is
how a value model dominating the original model dominates it. The matrix version's explicit
carrier `introIterationAux`, state `introIterationState` and repeated extension
`introIterationExtend` have no counterpart: the iterated model carries them.
-/

noncomputable section
namespace MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
set_option linter.unusedSectionVars false

universe u v

variable {PauliType PauliAnswer κ : Type*} {F ι A : Type}
  [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
  [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype A] {ℓ : ℕ}
variable {𝒞 𝒜 ℬ : Type u} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
  [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [StarModule ℂ ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarProper ℬ]

-- The dilation ancilla's instances exceed the default synthesis size (`AdaptiveGameStage`).
set_option synthInstance.maxSize 512 in
/-- A concrete projective strategy family exists after every finite Alice
stage, in a model reducing to the original one. The original primitive bounds and explicit
positive threshold suffice; no future structural invariant, future error bound, or
stage-smallness conclusion is assumed. The full option-valued invariant includes malformed
answers and the support of all valid answers. -/
theorem exists_intro_iteration
    (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) κ 3) (L : Bool → CL.CLFun F ι ℓ)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → (κ → ZMod 2) → (κ → ZMod 2) →
      PauliAnswer → PauliAnswer → Bool)
    (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) (hΞ : ‖Ξ.ψ‖ = 1)
    (MA : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) 𝒜))
    (MB : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
      POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) ℬ))
    (hMA : ∀ q, IsPVMIn (MA q).op) (hMB : ∀ q, IsPVMIn (MB q).op)
    (q : κ → ZMod 2) (hq : ∀ z, (P Z).eval z = q)
    (w : Bool) (hL : (L w).SupportedOn univ)
    {initial η δ : ℝ} (hi0 : 0 ≤ initial) (hη0 : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hfail : 1 - (Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MA MB ≤
      initial)
    (hZ : introBobZError projectPauli Z q Ξ MB ≤ η)
    (hhide : ∀ j : Fin ℓ, hidingAliceError L w hL Ξ MA j ≤ δ)
    (hi : initial ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hη : η ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (hδ : δ ≤ adaptiveSmallThreshold ℓ (TypeGraph.edges E X Z ℓ).card ℓ)
    (n : ℕ) (hn : n ≤ ℓ) :
    ∃ (N : ModelOver.{u, v} ℬ)
      (MN : CL.Detyping.Question (QuestionType PauliType ℓ) κ →
        POVMIn (ParsedAnswer (ι → F) A PauliAnswer) (Matrix (ι → F) (ι → F) N.𝒜))
      (_ : IntroPrefixInvariant (L w) n
        ((MN (QuestionType.introspect w, 0)).map introspectPair)),
      ‖N.Ξ.ψ‖ = 1 ∧ (∀ t, IsPVMIn (MN t).op) ∧
      1 - (N.Ξ.reg (ι → F)).povmValue (parsedGame E X Z P L projectPauli D DP) MN MB ≤
        adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n ∧
      introAliceZError projectPauli Z q N.Ξ MN = introAliceZError projectPauli Z q Ξ MA ∧
      introBobZError projectPauli Z q N.Ξ MB = introBobZError projectPauli Z q Ξ MB ∧
      (∀ j : Fin ℓ, hidingAliceError L w hL N.Ξ MN j = hidingAliceError L w hL Ξ MA j) ∧
      (∀ j : Fin ℓ, hidingBobError L w hL N.Ξ MB j = hidingBobError L w hL Ξ MB j) ∧
      N.Ξ.POVMReduces Ξ := by
  induction n with
  | zero =>
      exact ⟨ModelOver.of Ξ, MA, initialIntroPrefixInvariant (L w)
        ((MA (QuestionType.introspect w, 0)).map introspectPair)
        (POVMIn.isPVMIn_map (hMA _) _), hΞ, hMA, hfail, rfl, rfl, fun _ => rfl,
        fun _ => rfl, BipartiteModel.POVMReduces.refl Ξ⟩
  | succ n ih =>
      have hn' : n ≤ ℓ := (Nat.le_succ n).trans hn
      obtain ⟨N, MN, IN, hNψ, hMN, hfailN, hzAN, hzBN, hhideN, hhideBN, hredN⟩ := ih hn'
      let j : Fin ℓ := ⟨n, by omega⟩
      have he : (0 : ℝ) ≤ (TypeGraph.edges E X Z ℓ).card := Nat.cast_nonneg _
      have hb : 0 ≤ adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card
          η δ initial n :=
        adaptiveFailureBudget_nonneg ℓ n _ η δ hi0
      have hdepth : adaptiveStageBudget (ℓ - j.val)
          ((TypeGraph.edges E X Z ℓ).card *
            adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n) η δ ≤
          adaptiveStageBudget ℓ
            ((TypeGraph.edges E X Z ℓ).card *
              adaptiveFailureBudget ℓ (TypeGraph.edges E X Z ℓ).card η δ initial n) η δ :=
        adaptiveStageBudget_mono_depth (Nat.sub_le ℓ j.val) (mul_nonneg he hb)
      have hsmall := hdepth.trans
        (adaptiveStageBudget_le_one_of_threshold ℓ ℓ he hi hη hδ n hn')
      obtain ⟨K, MS, IS, hMS, hfailS, _, hhideS, hzAS, hzBS, hhideBS⟩ := exists_intro_successor
        E X Z P L projectPauli D DP N.Ξ hNψ MN MB hMN hMB q hq w hL j IN
        hb hη0 hδ0 hfailN (hzBN.trans_le hZ) ((hhideN j).trans_le (hhide j)) hsmall
      let t₀ : DilationAncilla (Option ((ι → F) × A)) K := Sum.inl (none, 0)
      refine ⟨N.expandA t₀, MS, IS, (N.norm_expandA_ψ t₀).trans hNψ, hMS, ?_,
        hzAS.trans hzAN, hzBS.trans hzBN, fun i => (hhideS i).trans (hhideN i),
        fun i => (hhideBS i).trans (hhideBN i), BipartiteModel.POVMReduces.trans (N.povmReduces_expandA t₀) hredN⟩
      exact hfailS.trans (by
        rw [adaptiveFailureBudget_step]
        exact add_le_add le_rfl (adaptiveStepLoss_mono hdepth))

end MIPRE.Introspection.TypedEstimates
end

end
