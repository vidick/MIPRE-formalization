/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Simul
public import MIPRE.Background.QLD.Expanded
public import MIPRE.Background.QLD.Uniform

@[expose] public section

/-!
# The marginals track the point measurements (`lem:qld-helper`)

Stage 5 uses the simultaneous pair measurement of `lem:qld-simultaneous` through two statements,
the paper's `lem:qld-constructing-the-paulis-helper`. For `W ∈ {X, Z}`, on average over a uniform
point `u ∈ F_q^m`, with `S^W_a` the evaluated `W` marginal of Alice's pair measurement and
`M̂^{W,u}_a` the expanded point measurement:

* **cross-party**: `∑_a ⟨S^W_a ⊗ M̂^{B,W,u}_a⟩ ≥ 1 - δ_S`, the consistency read as an agreement;
* **same-party**: `∑_a ‖(S^W_a (1 - M̂^{A,W,u}_a) ⊗ 1) Φ‖² ≤ 4 δ_S + 2 κ`, in which *both*
  factors sit on Alice --- the form the Pauli construction needs, since it multiplies the
  marginal by the point measurement on one side.

`κ` is the self-consistency of the expanded point measurements (`lem:qld-expanded-points`,
`172 ε`), which is what lets the second statement cross from one party to the other.

## The identity behind the same-party statement

With `T = S^W_a` and `A = M̂^{A,W,u}_a` projectors on Alice, `B = M̂^{B,W,u}_a` a projector on
Bob, and `Φ` the state,

`T ⊗ 1 · (1 - A ⊗ 1) = (1 - 1 ⊗ B)(T ⊗ 1 - 1 ⊗ B) - (T ⊗ 1)(A ⊗ 1 - 1 ⊗ B)`,

because the cross terms `(T ⊗ 1)(1 ⊗ B)` cancel and `(1 - 1 ⊗ B)(1 ⊗ B) = 0` by projectivity of
`B`. Both factors in front are contractions, so the deviation of the same-party product is at most
the sum of the two cross-party deviations: the first is the consistency of the marginal with Bob's
point measurement, the second the self-consistency of the point measurements. No positivity of the
state is used beyond its being a unit vector.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The pair measurement is a
`SimulPair M S K ι δ` of a projective strategy `S` of a bipartite model `M`: its measurements live
in the model `K`, and the expanded point measurements, POVMs of the register model
`M.reg (Anc F m)`, are read in `K` through the embedding `ι`. The identity above is an identity in
`K`'s algebra, `T ⊗ 1` being `K.πA T` and `1 ⊗ B` being `K.πB B`; the expanded self-consistency
of `lem:qld-expanded-points` is carried to `K` exactly along `ι` (`SimulPair.xSqNorm_aOp`). The
projectivity of the strategy, a hypothesis of the matrix statements, is a field of `S`.
-/

noncomputable section

namespace MIPRE

open Finset

/-! ## The same-party deviation -/

section SameParty

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]

/-- **The key identity**: the same-party product `T (1 - A)` is a combination of the two
cross-party deviations, `T ⊗ 1 - 1 ⊗ B` and `A ⊗ 1 - 1 ⊗ B`. -/
theorem aOp_mul_one_sub_eq (M : BipartiteModel 𝒞 𝒜 ℬ) {T A : 𝒜} {B : ℬ} (hBi : B * B = B) :
    M.πA (T * (1 - A))
      = (1 - M.πB B) * (M.πA T - M.πB B) - M.πA T * (M.πA A - M.πB B) := by
  have hBB : M.πB B * M.πB B = M.πB B := by rw [← map_mul, hBi]
  have hcomm : M.πA T * M.πB B = M.πB B * M.πA T := (M.commute T B).eq
  rw [map_mul, map_sub, map_one]
  simp only [mul_sub, sub_mul, mul_one, one_mul, hBB, hcomm]
  abel

/-- **The same-party deviation is at most the two cross-party ones.** -/
theorem snorm_aOp_mul_one_sub_le (M : BipartiteModel 𝒞 𝒜 ℬ) {T A : 𝒜} {B : ℬ}
    (hT : star T = T) (hTi : T * T = T) (hB : star B = B) (hBi : B * B = B) :
    M.snorm (M.πA (T * (1 - A))) ≤ M.xNorm T B + M.xNorm A B := by
  have hbT : M.Bnd (M.πA T) 1 := M.bnd_πA_of_isStarProjection ⟨hTi, hT⟩
  have hbB : M.Bnd (1 - M.πB B) 1 := by
    have h := M.bnd_πB_of_isStarProjection (IsStarProjection.one_sub ⟨hBi, hB⟩)
    rwa [map_sub, map_one] at h
  rw [aOp_mul_one_sub_eq M hBi, BipartiteModel.xNorm, BipartiteModel.xNorm]
  refine le_trans (M.snorm_sub_le _ _) (add_le_add ?_ ?_)
  · have := M.snorm_mul_le hbB (M.πA T - M.πB B)
    rwa [one_mul] at this
  · have := M.snorm_mul_le hbT (M.πA A - M.πB B)
    rwa [one_mul] at this

/-- The squared form, at the usual cost of a factor two. -/
theorem snorm_sq_aOp_mul_one_sub_le (M : BipartiteModel 𝒞 𝒜 ℬ) {T A : 𝒜} {B : ℬ}
    (hT : star T = T) (hTi : T * T = T) (hB : star B = B) (hBi : B * B = B) :
    M.snorm (M.πA (T * (1 - A))) ^ 2 ≤ 2 * M.xSqNorm T B + 2 * M.xSqNorm A B := by
  have h := snorm_aOp_mul_one_sub_le M (A := A) hT hTi hB hBi
  have h0 := M.snorm_nonneg (M.πA (T * (1 - A)))
  rw [M.xSqNorm_eq_sq, M.xSqNorm_eq_sq]
  nlinarith [sq_nonneg (M.xNorm T B - M.xNorm A B), M.xNorm_nonneg T B, M.xNorm_nonneg A B]

end SameParty

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## One minus the inconsistency is the agreement -/

section Agreement

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

/-- **The inconsistency is one minus the agreement.** -/
theorem sum_bornProb_diag_eq {μ : X → ℝ} (hμ : ∑ x, μ x = 1) {M : BipartiteModel 𝒞 𝒜 ℬ}
    (hM : ‖M.ψ‖ = 1) (P : X → POVMIn A 𝒜) (Q : X → POVMIn A ℬ) :
    ∑ x, μ x * ∑ a, M.bornProb ((P x).op a) ((Q x).op a) = 1 - M.inconsistency μ P Q := by
  have hx : ∀ x, ∑ a, M.bornProb ((P x).op a) ((Q x).op a)
      = 1 - pairInconsistency M (P x) (Q x) := fun x => sum_diag_eq_one_sub hM (P x) (Q x)
  rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => by rw [hx x],
    show M.inconsistency μ P Q = ∑ x, μ x * pairInconsistency M (P x) (Q x) from rfl,
    Finset.sum_congr rfl fun x (_ : x ∈ univ) => mul_sub (μ x) 1 (pairInconsistency M (P x) (Q x)),
    Finset.sum_sub_distrib]
  simp only [mul_one]
  rw [hμ]

end Agreement

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]

/-! ## The self-consistency of the expanded point measurements, at a uniform point -/

section SelfCons

omit [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
/-- **The verifier's `W` block is uniform**: an average over contents of a function of the
content's `W` point is the average over a uniform point. -/
theorem sum_content_pt (W : Bas) (f : Point F m → ℝ) :
    ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * f (c.pt W)
      = ∑ u, uniform (Point F m) u * f u := by
  cases W with
  | X =>
      have h := sum_content_blocks (F := F) (m := m) (fun x _z => f x)
      rw [show (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * f (c.pt .X))
          = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * (fun x (_z : Point F m) =>
            f x) c.uX c.uZ from rfl, h]
      refine Finset.sum_congr rfl fun x _ => ?_
      show (∑ _z : Point F m, uniform (Point F m) x * uniform (Point F m) _z * f x) = _
      rw [Finset.sum_congr rfl fun z (_ : z ∈ univ) =>
        show uniform (Point F m) x * uniform (Point F m) z * f x
          = uniform (Point F m) x * f x * uniform (Point F m) z from by ring,
        ← Finset.mul_sum, sum_uniform_eq_one, mul_one]
  | Z =>
      have h := sum_content_blocks (F := F) (m := m) (fun (_x : Point F m) z => f z)
      rw [show (∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * f (c.pt .Z))
          = ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ * (fun (_x : Point F m) z =>
            f z) c.uX c.uZ from rfl, h, Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      show (∑ _x : Point F m, uniform (Point F m) _x * uniform (Point F m) z * f z) = _
      rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) =>
        show uniform (Point F m) x * uniform (Point F m) z * f z
          = uniform (Point F m) z * f z * uniform (Point F m) x from by ring,
        ← Finset.mul_sum, sum_uniform_eq_one, mul_one]

/-- `lem:qld-expanded-points`, read at a uniform point rather than at the verifier's content: the
content's `W` block is uniform, and the hatted measurement at a content is the one at its point. -/
theorem sum_uniform_xSqNorm_hatMats_le {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    {ε : ℝ} (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        (M.reg (Anc F m)).xSqNorm (hatMats PA W u a) (hatMats PB W u a)
      ≤ 172 * ε := by
  have h := sum_content_hatMats_consistency (PB := PB) hM hfail W
  rwa [sum_content_pt W (fun u => ∑ a : F,
    (M.reg (Anc F m)).xSqNorm (hatMats PA W u a) (hatMats PB W u a))] at h

end SelfCons

/-! ## The two items of `lem:qld-helper` -/

namespace SimulPair

variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]
  [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
/-- The elements of a hatted point measurement are self-adjoint. -/
theorem hatMats_conjTranspose {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R]
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) (a : F) :
    star (hatMats P W u a) = hatMats P W u a :=
  (hatPtPOVM P W u).star_op a

variable (P : SimulPair M S K ι δ)

/-- **`lem:qld-helper`, item 1**: the evaluated marginal agrees with the opposite party's expanded
point measurement with probability at least `1 - δ_S`, on average over a uniform point. -/
theorem sum_bornProb_evalMarg_ge (W : Bas) :
    1 - δ ≤ ∑ u, uniform (Point F m) u * ∑ a : F,
      K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a)) := by
  have h := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) P.ψ_unit
    (fun u => evalMarg P.SA W u) (fun u => (hatPtPOVM S.PB W u).pushforward ι.ΦB ι.ΦB_one)
  have hc := P.consA W
  rw [show (∑ u, uniform (Point F m) u * ∑ a : F,
      K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a)))
      = ∑ u, uniform (Point F m) u * ∑ a : F,
        K.bornProb ((evalMarg P.SA W u).op a)
          (((hatPtPOVM S.PB W u).pushforward ι.ΦB ι.ΦB_one).op a) from rfl, h]
  linarith

/-- The cross-party deviation of the marginal from the point measurement, from item 1. -/
theorem sum_xSqNorm_evalMarg_le (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        K.xSqNorm ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a))
      ≤ 2 * δ := by
  have hterm : ∀ u : Point F m, ∑ a : F,
      K.xSqNorm ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a))
      ≤ 2 * (1 - ∑ a : F, K.bornProb ((evalMarg P.SA W u).op a)
        (ι.ΦB (hatMats S.PB W u a))) := fun u =>
    K.xSqNorm_sum_le_two_mul P.ψ_unit (evalMarg P.SA W u)
      ((hatPtPOVM S.PB W u).pushforward ι.ΦB ι.ΦB_one)
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hterm u) (uniform_nonneg (Point F m) u)
  have hsplit : ∑ u, uniform (Point F m) u * (2 * (1 - ∑ a : F,
      K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a))))
      = 2 * (∑ u, uniform (Point F m) u)
        - 2 * ∑ u, uniform (Point F m) u * ∑ a : F,
          K.bornProb ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit, sum_uniform_eq_one] at hsum
  linarith [P.sum_bornProb_evalMarg_ge W]

include P in
/-- The cross-party deviation of the two parties' expanded point measurements, read in `K`:
`lem:qld-expanded-points`, carried along the embedding. -/
theorem sum_xSqNorm_hat_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        K.xSqNorm (ι.ΦA (hatMats S.PA W u a)) (ι.ΦB (hatMats S.PB W u a))
      ≤ 172 * ε := by
  simp only [P.xSqNorm_aOp]
  exact sum_uniform_xSqNorm_hatMats_le (hm := hm) S.ψ_unit hfail W

/-- **`lem:qld-helper`, item 2**: the same-party product of the marginal with the complement of
*Alice's own* point measurement is small. -/
theorem sum_snorm_sq_evalMarg_one_sub_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        K.snorm (K.πA ((evalMarg P.SA W u).op a * (1 - ι.ΦA (hatMats S.PA W u a)))) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  have hT : ∀ u : Point F m, IsPVMIn (evalMarg P.SA W u).op := fun u =>
    isPVM_evalMarg P.SA_proj W u
  have hB : ∀ u : Point F m, IsPVMIn fun a => ι.ΦB (hatMats S.PB W u a) := fun u =>
    (isPVM_hatMats S.projB W u).pushforward ι.ΦB_one
  have hterm : ∀ (u : Point F m) (a : F),
      K.snorm (K.πA ((evalMarg P.SA W u).op a * (1 - ι.ΦA (hatMats S.PA W u a)))) ^ 2
      ≤ 2 * K.xSqNorm ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a))
        + 2 * K.xSqNorm (ι.ΦA (hatMats S.PA W u a)) (ι.ΦB (hatMats S.PB W u a)) := fun u a =>
    snorm_sq_aOp_mul_one_sub_le K ((hT u).star_eq a) ((hT u).idem a) ((hB u).star_eq a)
      ((hB u).idem a)
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a (_ : a ∈ univ) => hterm u a)
      (uniform_nonneg (Point F m) u)
  have hsplit : ∑ u, uniform (Point F m) u * ∑ a : F,
      (2 * K.xSqNorm ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a))
        + 2 * K.xSqNorm (ι.ΦA (hatMats S.PA W u a)) (ι.ΦB (hatMats S.PB W u a)))
      = 2 * (∑ u, uniform (Point F m) u * ∑ a : F,
          K.xSqNorm ((evalMarg P.SA W u).op a) (ι.ΦB (hatMats S.PB W u a)))
        + 2 * ∑ u, uniform (Point F m) u * ∑ a : F,
          K.xSqNorm (ι.ΦA (hatMats S.PA W u a)) (ι.ΦB (hatMats S.PB W u a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hsplit] at hsum
  linarith [P.sum_xSqNorm_evalMarg_le W, P.sum_xSqNorm_hat_le hfail W]

end SimulPair

end MIPRE.QLD

end

end
