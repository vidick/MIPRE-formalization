/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingDeciderGame
import MIPRE.Foundations.CL.DetypingSoundness
import MIPRE.Foundations.CL.DetypingComplete

/-! # Same-state soundness for the actual detyped verifier

The actual sampler's numbered CL presentations have precisely the finite
detyping distribution after the coordinate permutation. Together with the
proved executable predicate law, this transports the existing finite-game
restriction to strategies for the compiled ambient verifier.
-/

noncomputable section

namespace MIPRE.CL.Detyping.DeciderProgram

open Cost Finset
set_option linter.unusedSectionVars false

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

/-- The coordinate numbering is an equivalence of the complete question spaces. -/
def vectorEquiv (s : ℕ) : (Coord T (Fin s) → 𝔽₂) ≃ (Fin (graphDim T + s) → 𝔽₂) where
  toFun := push (registerEquiv s).toEmbedding
  invFun := pull (registerEquiv s).toEmbedding
  left_inv := pull_push _
  right_inv z := by
    funext i
    obtain ⟨q, rfl⟩ := (registerEquiv (T := T) s).surjective i
    exact push_apply _ _ q

def sourceFamily (n : ℕ) (w : Bool) := S.cl n (Player.ofBool w)

/-- The exact finite distribution obtained by numbering the detyped registers. -/
theorem numbered_clDist (n : ℕ) (x y : Coord T (Fin (S.dim n)) → 𝔽₂) :
    clDist (numbered E .alice (S.cl n .alice)).eval
      (numbered E .bob (S.cl n .bob)).eval (vectorEquiv (S.dim n) x) (vectorEquiv (S.dim n) y) =
    clDist (presentation E false (sourceFamily S n false)).eval
      (presentation E true (sourceFamily S n true)).eval x y := by
  classical
  unfold clDist
  rw [Fintype.card_congr (vectorEquiv (T := T) (S.dim n)).symm]
  congr 2
  rw [← Finset.map_univ_equiv (vectorEquiv (T := T) (S.dim n)),
    Finset.filter_map, Finset.card_map]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    numbered, CLFun.eval_embed, Function.comp_apply, Equiv.toEmbedding_apply,
    vectorEquiv, Equiv.coe_fn_mk, pull_push]
  change (vectorEquiv (S.dim n) ((presentation E false (S.cl n .alice)).eval z) =
      vectorEquiv (S.dim n) x ∧
    vectorEquiv (S.dim n) ((presentation E true (S.cl n .bob)).eval z) =
      vectorEquiv (S.dim n) y) ↔ _
  simp only [(vectorEquiv (T := T) (S.dim n)).injective.eq_iff]
  rfl

/-- The actual ambient game and the finite game have identical question weights. -/
theorem verifier_game_mu (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (x y : Coord T (Fin (S.dim n)) → 𝔽₂) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).μ
      (vectorEquiv (S.dim n) x) (vectorEquiv (S.dim n) y) =
    (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).μ x y := by
  rw [game_mu_eq_clDist]
  exact numbered_clDist E S n x y

/-- Read the actual compiled-verifier strategy in the unnumbered finite game. -/
def toFinite (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    TensorProductStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)) :=
  R.relabel _ (vectorEquiv (S.dim n)) (vectorEquiv (S.dim n)) (.refl _) (.refl _)

theorem toFinite_state (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    (toFinite E S D C hℓ hD n R).ψ = R.ψ := rfl

theorem toFinite_value (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    (toFinite E S D C hℓ hD n R).value = R.value := by
  apply R.value_relabel _ (vectorEquiv (S.dim n)) (vectorEquiv (S.dim n)) (.refl _) (.refl _)
  · intro x y
    exact (verifier_game_mu E S D C hℓ hD n x y).symm
  · intro x y a b
    exact (verifier_game_D E S D C hℓ hD n x y a b).symm

/-- Restrict an actual compiled-verifier strategy to valid typed graph views. -/
def restrictAmbient (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    TensorProductStrategy (typedGame E hne (sourceFamily S n) (typedPredicate S D C n)) :=
  Detyping.restrict E hne _ _ (toFinite E S D C hℓ hD n R)

/-- Ambient restriction changes neither Hilbert spaces nor the shared state. -/
theorem restrictAmbient_state (hne : (Graph.edges E).Nonempty)
    (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    (restrictAmbient E S D C hne hℓ hD n R).ψ = R.ψ := rfl

/-- The source detyping soundness factor now applies to the actual program-defined game. -/
theorem restrictAmbient_failure_le (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n))) :
    1 - (restrictAmbient E S D C hne hℓ hD n R).value ≤
      (16 : ℝ) ^ Fintype.card T * (1 - R.value) := by
  have h := Detyping.restrict_failure_le E hE hne (sourceFamily S n)
    (fun w t => S.cl_exactlyOn n (Player.ofBool w) t) hℓ (typedPredicate S D C n)
    (toFinite E S D C hℓ hD n R)
  rw [toFinite_value] at h
  exact h

theorem restrictAmbient_value_ge (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : TensorProductStrategy ((verifier E S D C hℓ hD).game n (C.outer n)))
    {ε : ℝ} (hR : 1 - ε ≤ R.value) :
    1 - (16 : ℝ) ^ Fintype.card T * ε ≤
      (restrictAmbient E S D C hne hℓ hD n R).value := by
  have h := restrictAmbient_failure_le E S D C hE hne hℓ hD n R
  have hp : 0 ≤ (16 : ℝ) ^ Fintype.card T := pow_nonneg (by norm_num) _
  nlinarith

/-- Undo coordinate numbering while preserving the doubling tag. -/
def doubledVectorEquiv (s : ℕ) :
    (Bool × (Fin (graphDim T + s) → 𝔽₂)) ≃ (Bool × (Coord T (Fin s) → 𝔽₂)) :=
  Equiv.prodCongr (.refl Bool) (vectorEquiv s).symm

theorem doubled_game_mu (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (p q : Bool × (Fin (graphDim T + S.dim n) → 𝔽₂)) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).doubled.μ p q =
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled.μ
        (doubledVectorEquiv (S.dim n) p) (doubledVectorEquiv (S.dim n) q) := by
  change (if p.1 = false ∧ q.1 = true then
    ((verifier E S D C hℓ hD).game n (C.outer n)).μ p.2 q.2 else 0) =
    if p.1 = false ∧ q.1 = true then
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).μ
        ((vectorEquiv (S.dim n)).symm p.2) ((vectorEquiv (S.dim n)).symm q.2) else 0
  by_cases h : p.1 = false ∧ q.1 = true
  · rw [if_pos h, if_pos h]
    simpa only [Equiv.apply_symm_apply] using
      verifier_game_mu E S D C hℓ hD n ((vectorEquiv (S.dim n)).symm p.2)
        ((vectorEquiv (S.dim n)).symm q.2)
  · rw [if_neg h, if_neg h]

theorem doubled_game_D (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (p q : Bool × (Fin (graphDim T + S.dim n) → 𝔽₂))
    (a b : MIPRE.Verifier.Answers (C.outer n)) :
    ((verifier E S D C hℓ hD).game n (C.outer n)).doubled.D p q a b =
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled.D
        (doubledVectorEquiv (S.dim n) p) (doubledVectorEquiv (S.dim n) q) a b := by
  change (if p.1 = false ∧ q.1 = true then
    ((verifier E S D C hℓ hD).game n (C.outer n)).D p.2 q.2 a b else false) =
    if p.1 = false ∧ q.1 = true then
      (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).D
        ((vectorEquiv (S.dim n)).symm p.2) ((vectorEquiv (S.dim n)).symm q.2) a b else false
  by_cases h : p.1 = false ∧ q.1 = true
  · rw [if_pos h, if_pos h]
    have hd : ((verifier E S D C hℓ hD).game n (C.outer n)).D
        (vectorEquiv (S.dim n) ((vectorEquiv (S.dim n)).symm p.2))
        (vectorEquiv (S.dim n) ((vectorEquiv (S.dim n)).symm q.2)) a b =
        (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).D
          ((vectorEquiv (S.dim n)).symm p.2) ((vectorEquiv (S.dim n)).symm q.2) a b :=
      verifier_game_D E S D C hℓ hD n ((vectorEquiv (S.dim n)).symm p.2)
        ((vectorEquiv (S.dim n)).symm q.2) a b
    simpa only [Equiv.apply_symm_apply] using hd
  · rw [if_neg h, if_neg h]

/-- Transport a synchronous finite-game strategy to the actual compiled verifier. -/
def fromFiniteSync (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled) :
    SyncStrategy ((verifier E S D C hℓ hD).game n (C.outer n)).doubled :=
  R.relabel _ (doubledVectorEquiv (S.dim n)) (.refl _)

theorem fromFiniteSync_d (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled) :
    (fromFiniteSync E S D C hℓ hD n R).d = R.d := rfl

theorem fromFiniteSync_value (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled) :
    (fromFiniteSync E S D C hℓ hD n R).value = R.value :=
  R.value_relabel _ (doubledVectorEquiv (S.dim n)) (.refl _)
    (doubled_game_mu E S D C hℓ hD n) (doubled_game_D E S D C hℓ hD n)

theorem fromFiniteSync_isPCC (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (Detyping.game E (sourceFamily S n) (typedPredicate S D C n)).doubled)
    (hR : R.IsPCC) : (fromFiniteSync E S D C hℓ hD n R).IsPCC :=
  SyncStrategy.isPCC_relabel hR _ (doubledVectorEquiv (S.dim n)) (.refl _)
    (doubled_game_mu E S D C hℓ hD n)

/-- Perfect PCC completeness for the actual program-defined game, on the same
outer answer alphabet with the source typed cutoff included in the premise. -/
theorem exists_ambientPerfectPCC (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (typedGame E hne (sourceFamily S n) (typedPredicate S D C n)).doubled)
    (hR : R.IsPCC) (hval : R.value = 1) :
    ∃ Q : SyncStrategy ((verifier E S D C hℓ hD).game n (C.outer n)).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = R.d := by
  obtain ⟨Q, hQ, hv, hd⟩ := Detyping.exists_perfectPCC E hE hne (sourceFamily S n)
    (fun w t => S.cl_exactlyOn n (Player.ofBool w) t) hℓ (typedPredicate S D C n)
    R hR hval ⟨[], by simp⟩
  exact ⟨fromFiniteSync E S D C hℓ hD n Q,
    fromFiniteSync_isPCC E S D C hℓ hD n Q hQ,
    (fromFiniteSync_value E S D C hℓ hD n Q).trans hv, hd⟩

/-- Completeness in the ambient verifier API, with the source typed cutoff
already present in the finite typed game on the same outer alphabet. -/
theorem verifier_hasPerfectPCC (hE : ∀ u v, E u v → E v u)
    (hne : (Graph.edges E).Nonempty) (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ)
    (R : SyncStrategy (typedGame E hne (sourceFamily S n) (typedPredicate S D C n)).doubled)
    (hR : R.IsPCC) (hval : R.value = 1) :
    (verifier E S D C hℓ hD).HasPerfectPCC n (C.outer n) := by
  obtain ⟨Q, hQ, hv, _⟩ := exists_ambientPerfectPCC E S D C hE hne hℓ hD n R hR hval
  exact ⟨Q, hQ, hv⟩

end MIPRE.CL.Detyping.DeciderProgram
