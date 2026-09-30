/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.POVMReduction

@[expose] public section

/-! # A bipartite model over a given second player's algebra

Each Alice stage of introspection adjoins to the first player an ancilla register whose size is
chosen along the way, by the Kraus–Halmos dilation (`exists_pvm_dilation_ge`). This changes the
first player's algebra, and the algebra the model represents, from one stage to the next, and
leaves the second player's algebra alone; a stage therefore returns a model together with its
algebras. `ModelOver ℬ` packs a bipartite model whose second player's algebra is `ℬ` with its
represented algebra and its first player's algebra, and the instances register measurements need
(`StarModule ℂ`, and an ordered, proper `⋆`-ring). Its ancilla extension `ModelOver.expandA`
reduces to it (`BipartiteModel.povmReduces_expandA`), so a value model dominating the model at one
stage dominates it at every later one.

Phase 4 of `planning/mipco-track.md`.
-/

noncomputable section

namespace MIPRE

universe u v

/-- **A bipartite model over the second player's algebra `ℬ`**, packed with its represented
algebra and its first player's algebra, the latter ordered and proper. -/
structure ModelOver (ℬ : Type u) [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] where
  /-- The algebra represented on the Hilbert space. -/
  𝒞 : Type u
  /-- The first player's algebra. -/
  𝒜 : Type u
  [ring𝒞 : Ring 𝒞]
  [starRing𝒞 : StarRing 𝒞]
  [algebra𝒞 : Algebra ℂ 𝒞]
  [ring𝒜 : Ring 𝒜]
  [starRing𝒜 : StarRing 𝒜]
  [algebra𝒜 : Algebra ℂ 𝒜]
  [starModule𝒜 : StarModule ℂ 𝒜]
  [partialOrder𝒜 : PartialOrder 𝒜]
  [starOrderedRing𝒜 : StarOrderedRing 𝒜]
  [starProper𝒜 : StarProper 𝒜]
  /-- The model. -/
  Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ

attribute [instance] ModelOver.ring𝒞 ModelOver.starRing𝒞 ModelOver.algebra𝒞 ModelOver.ring𝒜
  ModelOver.starRing𝒜 ModelOver.algebra𝒜 ModelOver.starModule𝒜 ModelOver.partialOrder𝒜
  ModelOver.starOrderedRing𝒜 ModelOver.starProper𝒜

namespace ModelOver

variable {ℬ : Type u} [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- A bipartite model, packed. -/
def of {𝒞 𝒜 : Type u} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜]
    [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) : ModelOver.{u, v} ℬ :=
  ⟨𝒞, 𝒜, Ξ⟩

@[simp]
theorem of_Ξ {𝒞 𝒜 : Type u} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
    [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarProper 𝒜]
    (Ξ : BipartiteModel.{v} 𝒞 𝒜 ℬ) : (of Ξ).Ξ = Ξ := rfl

variable {T : Type} [Fintype T] [DecidableEq T]

/-- **The first player's ancilla extension**: the register `T` adjoined to the first player, in
its reference state `t₀`. -/
def expandA (N : ModelOver.{u, v} ℬ) (t₀ : T) : ModelOver.{u, v} ℬ :=
  of (N.Ξ.expandA t₀)

@[simp]
theorem expandA_Ξ (N : ModelOver.{u, v} ℬ) (t₀ : T) : (N.expandA t₀).Ξ = N.Ξ.expandA t₀ := rfl

theorem norm_expandA_ψ (N : ModelOver.{u, v} ℬ) (t₀ : T) :
    ‖(N.expandA t₀).Ξ.ψ‖ = ‖N.Ξ.ψ‖ :=
  N.Ξ.norm_expandA_ψ t₀

/-- **The extension reduces to the model**, whatever the second player's order. -/
theorem povmReduces_expandA [PartialOrder ℬ] [StarOrderedRing ℬ] (N : ModelOver.{u, v} ℬ)
    (t₀ : T) : (N.expandA t₀).Ξ.POVMReduces N.Ξ :=
  N.Ξ.povmReduces_expandA t₀

end ModelOver

end MIPRE

end
