/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.VerifierValue

/-! # Verifier transport at a single index

Wrappers may change a sampler at exceptional indices. Equality of its dimension
and CL presentations at the index in question suffices to preserve both quantum
value and perfect PCC strategies; the programs need not agree elsewhere.
-/

noncomputable section
namespace MIPRE.Verifier
open CL

/-- Numbered vectors transported along an equality of their dimensions. -/
def dimensionEquiv {s t : ℕ} (h : s = t) : (Fin s → 𝔽₂) ≃ (Fin t → 𝔽₂) :=
  h ▸ Equiv.refl _

theorem toBits_dimensionEquiv {s t : ℕ} (h : s = t) (x : Fin s → 𝔽₂) :
    toBits (dimensionEquiv h x) = toBits x := by
  subst t
  rfl

theorem clDist_dimensionEquiv {s t ℓ : ℕ} (h : s = t)
    (L R : CLFun 𝔽₂ (Fin s) ℓ) (L' R' : CLFun 𝔽₂ (Fin t) ℓ)
    (hL : HEq L L') (hR : HEq R R') (x y : Fin s → 𝔽₂) :
    clDist L'.eval R'.eval (dimensionEquiv h x) (dimensionEquiv h y) =
      clDist L.eval R.eval x y := by
  subst t
  cases eq_of_heq hL
  cases eq_of_heq hR
  rfl

variable {ℓ : ℕ} {V W : Verifier ℓ} {n T : ℕ}

/-- Only the sampler data used at this index are compared. -/
structure SamplerAgreement (V W : Verifier ℓ) (n : ℕ) : Prop where
  dimension : V.sampler.dim n = W.sampler.dim n
  presentation : ∀ w, HEq (V.sampler.cl n w) (W.sampler.cl n w)

theorem SamplerAgreement.symm (h : SamplerAgreement V W n) : SamplerAgreement W V n :=
  ⟨h.dimension.symm, fun w => (h.presentation w).symm⟩

theorem game_mu_dimensionEquiv (h : SamplerAgreement V W n) (x y : V.Questions n) :
    (W.game n T).μ (dimensionEquiv h.dimension x) (dimensionEquiv h.dimension y) =
      (V.game n T).μ x y :=
  clDist_dimensionEquiv h.dimension _ _ _ _ (h.presentation .alice) (h.presentation .bob) x y

theorem game_D_dimensionEquiv (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (x y : V.Questions n) (a b : Answers T) :
    (W.game n T).D (dimensionEquiv h.dimension x) (dimensionEquiv h.dimension y) a b =
      (V.game n T).D x y a b := by
  classical
  change decide (W.decider.Accepts n _ _ _ _) = decide (V.decider.Accepts n _ _ _ _)
  simp only [toBits_dimensionEquiv]
  exact decide_eq_decide.mpr (hD _ _ _ _).symm

/-- Changing programs away from the current index preserves quantum value. -/
theorem valStar_congr_at (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valStar n T = W.valStar n T :=
  quantumValue_eq_of_equiv (W.game n T) (V.game n T)
    (dimensionEquiv h.dimension) (dimensionEquiv h.dimension) (.refl _) (.refl _)
    (fun x y => (game_mu_dimensionEquiv h x y).symm)
    (fun x y a b => (game_D_dimensionEquiv h hD x y a b).symm)

/-- Perfect PCC strategies also depend only on the game at the current index. -/
theorem hasPerfectPCC_of_congr_at (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T := by
  let e := dimensionEquiv h.dimension
  let e' := Equiv.prodCongr (Equiv.refl Bool) e.symm
  have hμ (p q : Bool × W.Questions n) :
      (W.doubledGame n T).μ p q = (V.doubledGame n T).μ (e' p) (e' q) := by
    change (if p.1 = false ∧ q.1 = true then (W.game n T).μ p.2 q.2 else 0) =
      if p.1 = false ∧ q.1 = true then (V.game n T).μ (e.symm p.2) (e.symm q.2) else 0
    have hh := game_mu_dimensionEquiv (T := T) h (e.symm p.2) (e.symm q.2)
    change (W.game n T).μ (e (e.symm p.2)) (e (e.symm q.2)) = _ at hh
    simpa only [Equiv.apply_symm_apply] using congrArg (fun r => if p.1 = false ∧ q.1 = true then r else 0) hh
  have hd (p q : Bool × W.Questions n) (a b : Answers T) :
      (W.doubledGame n T).D p q a b = (V.doubledGame n T).D (e' p) (e' q) a b := by
    change (if p.1 = false ∧ q.1 = true then (W.game n T).D p.2 q.2 a b else false) =
      if p.1 = false ∧ q.1 = true then (V.game n T).D (e.symm p.2) (e.symm q.2) a b else false
    have hh := game_D_dimensionEquiv h hD (e.symm p.2) (e.symm q.2) a b
    change (W.game n T).D (e (e.symm p.2)) (e (e.symm q.2)) a b = _ at hh
    simpa only [Equiv.apply_symm_apply] using congrArg (fun r => if p.1 = false ∧ q.1 = true then r else false) hh
  obtain ⟨R,hR,hv⟩ := hV
  exact ⟨R.relabel _ e' (.refl _), R.isPCC_relabel hR _ e' (.refl _) hμ,
    (R.value_relabel _ e' (.refl _) hμ hd).trans hv⟩

theorem hasPerfectPCC_congr_at (h : SamplerAgreement V W n)
    (hD : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.HasPerfectPCC n T ↔ W.HasPerfectPCC n T :=
  ⟨hasPerfectPCC_of_congr_at h hD,
    hasPerfectPCC_of_congr_at h.symm fun x y a b => (hD x y a b).symm⟩

end MIPRE.Verifier
