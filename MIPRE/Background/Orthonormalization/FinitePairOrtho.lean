/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Orthonormalization.NoAbelian
public import MIPRE.Foundations.FinitePair
public import MIPRE.Foundations.Measurement

@[expose] public section

/-!
# Orthonormalization in a finite pair without abelian projections

The form of de la Salle's Theorem 1.2 that the C6b port consumes, stated in this repository's model
vocabulary so that it can be used outside `MIPRE/Background/Orthonormalization/`: a POVM in the
first algebra of a finite pair (`MIPRE/Foundations/FinitePair.lean`) whose operators contain no
nonzero abelian projection, nearly projective at the model's state, is close to a projective
measurement of that algebra (`povm_orthogonalization_finitePair`). The second player's version is
the same theorem for the model with the players exchanged.

The first player's operators of a finite pair are the commutant of the second player's, so they form
a Mathlib `VonNeumannAlgebra` with no bicommutant theorem (`vnA`: its `M″ = M` field is `S‴ = S′`;
`mem_vnA_iff`); the vector trace of the finite pair is a faithful tracial vector functional on it;
and the model's state is a vector state. `povm_orthogonalization_vecTrace` then applies, and its
projective measurement lies in the operators of the algebra, from which injectivity pulls it back.
-/

namespace MIPRE.Orthonormalization

open scoped ComplexOrder InnerProductSpace

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- **The first player's von Neumann algebra** of a bipartite model: the commutant of the second
player's operators, as a Mathlib `VonNeumannAlgebra` on the model's space. Its `M″ = M` field is
`S‴ = S′`, as for the vendored `matrixAlgebra`, so no bicommutant theorem is needed. -/
noncomputable def vnA (M : BipartiteModel 𝒞 𝒜 ℬ) : VonNeumannAlgebra M.H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ M.opsB
  centralizer_centralizer' := by
    show Set.centralizer (Set.centralizer (SetLike.coe (StarSubalgebra.centralizer ℂ M.opsB))) =
      SetLike.coe (StarSubalgebra.centralizer ℂ M.opsB)
    rw [StarSubalgebra.coe_centralizer, Set.centralizer_centralizer_centralizer]

/-- **In a finite pair, the first player's von Neumann algebra is the first player's operators**:
an operator commuting with the second player's is one of the first player's (`commutantA`), and
the first player's operators commute with the second player's and their adjoints. -/
theorem mem_vnA_iff {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : M.IsFinitePair) {T : M.H →L[ℂ] M.H} :
    T ∈ vnA M ↔ T ∈ M.opsA := by
  change T ∈ StarSubalgebra.centralizer ℂ M.opsB ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · exact fun hT => hM.commutantA T fun b => (hT _ ⟨b, rfl⟩).1.symm
  · rintro ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_star, ← map_star]
    exact ⟨((M.commute a b).map M.π).eq.symm, ((M.commute a (star b)).map M.π).eq.symm⟩

/-- **Orthonormalization in a finite pair without abelian projections**: if the first player's
operators of a finite pair contain no nonzero abelian projection, a POVM `P` of the first
player's algebra with `∑ₐ ‖π(πA(Pₐ)) ψ‖² > 1 - ε` at the model's unit state is within
`∑ₐ ‖π(πA(Pₐ - Qₐ)) ψ‖² < 9ε` of a projective measurement `Q` of that algebra. -/
theorem povm_orthogonalization_finitePair [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (M : BipartiteModel 𝒞 𝒜 ℬ) (hM : M.IsFinitePair) (hψ : ‖M.ψ‖ = 1)
    (hII : ∀ r ∈ M.opsA, IsStarProjection r →
      (∀ x ∈ M.opsA, ∀ y ∈ M.opsA, r * x * r * (r * y * r) = r * y * r * (r * x * r)) → r = 0)
    {Λ : Type*} [Fintype Λ] (P : POVMIn Λ 𝒜) (ε : ℝ)
    (hε : 1 - ε < ∑ a, ‖M.π (M.πA (P.op a)) M.ψ‖ ^ 2) :
    ∃ Q : Λ → 𝒜, IsPVMIn Q ∧ ∑ a, ‖M.π (M.πA (P.op a - Q a)) M.ψ‖ ^ 2 < 9 * ε := by
  obtain ⟨t⟩ := hM.traceA
  have hmem : ∀ T, T ∈ vnA M ↔ T ∈ M.opsA := fun T => mem_vnA_iff hM
  -- the POVM, represented on the model's space
  have hPOVM : Orthogonalization.IsPOVM (vnA M) fun a => M.π (M.πA (P.op a)) :=
    ⟨fun a => (hmem _).2 ⟨_, rfl⟩,
      fun a => ContinuousLinearMap.nonneg_iff_isPositive.1 (M.π_πA_nonneg (P.op_nonneg a)),
      by rw [← map_sum, ← map_sum, P.sum_op, map_one, map_one]⟩
  obtain ⟨p, hp, hlt⟩ := povm_orthogonalization_vecTrace (vnA M)
    (fun r hr => hII r ((hmem r).1 hr.2.1) hr.1 fun x hx y hy =>
      hr.2.2 x ((hmem x).2 hx) y ((hmem y).2 hy))
    t.g (fun x hx y hy => t.trace_mul_comm x ((hmem x).1 hx) y ((hmem y).1 hy))
    (fun x hx => t.separating x ((hmem x).1 hx)) M.ψ hψ _ hPOVM ε hε
  -- the projections are the first player's operators, and injectivity pulls them back
  have hex : ∀ a, ∃ q : 𝒜, M.π (M.πA q) = p a := fun a => (hmem (p a)).1 (hp.1 a)
  choose Q hQ using hex
  refine ⟨Q, IsPVMIn.of_map (f := M.π.comp M.πA) hM.injA ?_, ?_⟩
  · simp only [StarAlgHom.comp_apply, hQ]
    exact IsPVMIn.of_isStarProjection (fun x => (CStarRing.star_mul_self_eq_zero_iff x).1) hp.2.1
      hp.2.2
  · simpa only [map_sub, hQ] using hlt

end MIPRE.Orthonormalization

end
