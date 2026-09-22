/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Complete

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
`B` (`snorm_proj_one_sub_le`). Both factors in front are contractions, so the deviation of the
same-party product is at most the sum of the two cross-party deviations: the first is the
consistency of the marginal with Bob's point measurement, the second the self-consistency of the
point measurements. No positivity of the state is used beyond its being a unit vector.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## The same-party deviation -/

section SameParty

variable {RA RB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]

/-- **The key identity**: the same-party product `T (1 - A)` is a combination of the two
cross-party deviations, `T ⊗ 1 - 1 ⊗ B` and `A ⊗ 1 - 1 ⊗ B`. -/
theorem aOp_mul_one_sub_eq {T A : Matrix RA RA ℂ} {B : Matrix RB RB ℂ} (hBi : B * B = B) :
    (aOp (T * (1 - A)) : Matrix (RA × RB) _ ℂ)
      = ((1 : Matrix (RA × RB) _ ℂ) - bOp B) * ((aOp T : Matrix (RA × RB) _ ℂ) - bOp B)
        - (aOp T : Matrix (RA × RB) _ ℂ) * ((aOp A : Matrix (RA × RB) _ ℂ) - bOp B) := by
  have hBB : (bOp B : Matrix (RA × RB) _ ℂ) * bOp B = bOp B := by rw [← bOp_mul, hBi]
  have hcomm : (aOp T : Matrix (RA × RB) _ ℂ) * bOp B = bOp B * aOp T := aOp_mul_bOp T B
  simp only [aOp_mul, aOp_sub, aOp_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, hBB, hcomm]
  abel

/-- **The same-party deviation is at most the two cross-party ones.** -/
theorem snorm_aOp_mul_one_sub_le (Φ : RA × RB → ℂ) {T A : Matrix RA RA ℂ} {B : Matrix RB RB ℂ}
    (hT : Tᴴ = T) (hTi : T * T = T) (hB : Bᴴ = B) (hBi : B * B = B) :
    snorm Φ ((aOp (T * (1 - A)) : Matrix (RA × RB) _ ℂ)) ≤ xNorm Φ T B + xNorm Φ A B := by
  have hbT : Bnd (aOp T : Matrix (RA × RB) _ ℂ) 1 :=
    bnd_aOp (by rw [hT, hTi]; exact proj_le_one hT hTi)
  have hbB : Bnd ((1 : Matrix (RA × RB) _ ℂ) - bOp B) 1 := by
    have h1 : ((1 : Matrix RB RB ℂ) - B)ᴴ * ((1 : Matrix RB RB ℂ) - B) ≤ 1 := by
      have hsa : ((1 : Matrix RB RB ℂ) - B)ᴴ = 1 - B := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hB]
      have hid : ((1 : Matrix RB RB ℂ) - B) * ((1 : Matrix RB RB ℂ) - B) = 1 - B := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul, hBi]
        abel
      rw [hsa, hid]
      exact proj_le_one hsa hid
    have := bnd_bOp (HA := RA) h1
    rwa [bOp_sub, bOp_one] at this
  rw [aOp_mul_one_sub_eq hBi, xNorm_eq_snorm, xNorm_eq_snorm]
  refine le_trans (snorm_sub_le Φ _ _) (add_le_add ?_ ?_)
  · have := snorm_mul_le (v := Φ) hbB ((aOp T : Matrix (RA × RB) _ ℂ) - bOp B)
    rwa [one_mul] at this
  · have := snorm_mul_le (v := Φ) hbT ((aOp A : Matrix (RA × RB) _ ℂ) - bOp B)
    rwa [one_mul] at this

/-- The squared form, at the usual cost of a factor two. -/
theorem snorm_sq_aOp_mul_one_sub_le (Φ : RA × RB → ℂ) {T A : Matrix RA RA ℂ} {B : Matrix RB RB ℂ}
    (hT : Tᴴ = T) (hTi : T * T = T) (hB : Bᴴ = B) (hBi : B * B = B) :
    snorm Φ ((aOp (T * (1 - A)) : Matrix (RA × RB) _ ℂ)) ^ 2
      ≤ 2 * xSqNorm Φ T B + 2 * xSqNorm Φ A B := by
  have h := snorm_aOp_mul_one_sub_le (A := A) Φ hT hTi hB hBi
  have h0 := snorm_nonneg Φ ((aOp (T * (1 - A)) : Matrix (RA × RB) _ ℂ))
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq]
  nlinarith [sq_nonneg (xNorm Φ T B - xNorm Φ A B), xNorm_nonneg Φ T B, xNorm_nonneg Φ A B]

end SameParty

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## One minus the inconsistency is the agreement -/

section Agreement

variable {X A dA dB : Type*} [Fintype X] [Fintype A] [DecidableEq A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

/-- **The inconsistency is one minus the agreement.** -/
theorem sum_bornProb_diag_eq {μ : X → ℝ} (hμ : ∑ x, μ x = 1) {Φ : dA × dB → ℂ}
    (hΦ : star Φ ⬝ᵥ Φ = 1) (M : X → POVM A dA) (N : X → POVM A dB) :
    ∑ x, μ x * ∑ a, bornProb Φ (((M x).mats a).val) (((N x).mats a).val)
      = 1 - inconsistency μ Φ M N := by
  have hx : ∀ x, ∑ a, bornProb Φ (((M x).mats a).val) (((N x).mats a).val)
      = 1 - pairInconsistency Φ (M x) (N x) := fun x => sum_diag_eq_one_sub hΦ (M x) (N x)
  rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) => by rw [hx x],
    inconsistency_eq_sum_pairInconsistency,
    Finset.sum_congr rfl fun x (_ : x ∈ univ) => mul_sub (μ x) 1 (pairInconsistency Φ (M x) (N x)),
    Finset.sum_sub_distrib]
  simp only [mul_one]
  rw [hμ]

end Agreement

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/-! ## The self-consistency of the expanded point measurements, at a uniform point -/

section SelfCons

variable {hm : m ∣ Fintype.card F} {ε : ℝ}

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
theorem sum_uniform_xSqNorm_hatMats_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W u a) (hatMats MB W u a)
      ≤ 172 * ε := by
  have h := hatPOVM_consistency (MB := MB) hψ hfail W
  have hmats : ∀ c : Content F m,
      (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (((hatPOVM hm MA W c).mats a).val)
          (((hatPOVM hm MB W c).mats a).val)
      = (Fintype.card (Content F m) : ℝ)⁻¹ * ∑ a : F,
        xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W (c.pt W) a)
          (hatMats MB W (c.pt W) a) := by
    intro c
    congr 1
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hmats c,
    sum_content_pt W (fun u => ∑ a : F,
      xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W u a) (hatMats MB W u a))] at h
  exact h

end SelfCons

/-! ## The two items of `lem:qld-helper` -/

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

theorem hatMats_conjTranspose {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (a : F) :
    (hatMats M W u a)ᴴ = hatMats M W u a := by
  rw [hatMats, ← Matrix.star_eq_conjTranspose]
  exact ((hatPtPOVM M W u).mats a).2

/-- **`lem:qld-helper`, item 1**: the evaluated marginal agrees with the opposite party's expanded
point measurement with probability at least `1 - δ_S`, on average over a uniform point. -/
theorem sum_bornProb_evalMarg_ge (W : Bas) :
    1 - δ ≤ ∑ u, uniform (Point F m) u * ∑ a : F,
      bornProb P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a)) := by
  have h := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) P.Φ_unit
    (fun u => evalMarg P.SA W u) (fun u => (hatPtPOVM MB W u).aOp (E := P.EB))
  have hc := P.consA W
  rw [show (∑ u, uniform (Point F m) u * ∑ a : F,
      bornProb P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a)))
      = ∑ u, uniform (Point F m) u * ∑ a : F,
        bornProb P.Φ (((evalMarg P.SA W u).mats a).val)
          ((((hatPtPOVM MB W u).aOp (E := P.EB)).mats a).val) from rfl, h]
  linarith

/-- The cross-party deviation of the marginal from the point measurement, from item 1. -/
theorem sum_xSqNorm_evalMarg_le (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        xSqNorm P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a))
      ≤ 2 * δ := by
  have hterm : ∀ u : Point F m, ∑ a : F,
      xSqNorm P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a))
      ≤ 2 * (1 - ∑ a : F, bornProb P.Φ (((evalMarg P.SA W u).mats a).val)
        (aOp (hatMats MB W u a))) := fun u =>
    xSqNorm_sum_le_two_mul P.Φ_unit (evalMarg P.SA W u) ((hatPtPOVM MB W u).aOp (E := P.EB))
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hterm u) (uniform_nonneg (Point F m) u)
  have hsplit : ∑ u, uniform (Point F m) u * (2 * (1 - ∑ a : F,
      bornProb P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a))))
      = 2 * (∑ u, uniform (Point F m) u)
        - 2 * ∑ u, uniform (Point F m) u * ∑ a : F,
          bornProb P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hsplit, sum_uniform_eq_one] at hsum
  linarith [P.sum_bornProb_evalMarg_ge W]

/-- The cross-party deviation of the two parties' expanded point measurements, read on the padded
state: `lem:qld-expanded-points`, transferred by the structure's reduced-state property. -/
theorem sum_xSqNorm_hat_le {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        xSqNorm P.Φ (aOp (hatMats MA W u a)) (aOp (hatMats MB W u a))
      ≤ 172 * ε := by
  have htr : ∀ (u : Point F m) (a : F),
      xSqNorm P.Φ (aOp (hatMats MA W u a)) (aOp (hatMats MB W u a))
      = xSqNorm (hatVec (F := F) (m := m) ψ) (hatMats MA W u a) (hatMats MB W u a) := fun u a =>
    P.xSqNorm_aOp (hatMats_conjTranspose MA W u a) _
  simp only [htr]
  exact sum_uniform_xSqNorm_hatMats_le (hm := hm) hψ hfail W

/-- **`lem:qld-helper`, item 2**: the same-party product of the marginal with the complement of
*Alice's own* point measurement is small. -/
theorem sum_snorm_sq_evalMarg_one_sub_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ a : F, snorm P.Φ
        (aOp ((((evalMarg P.SA W u).mats a).val)
          * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  have hT : ∀ (u : Point F m), IsPVM fun a => (((evalMarg P.SA W u).mats a).val) := fun u =>
    isPVM_evalMarg P.SA_proj W u
  have hB : ∀ (u : Point F m) (a : F),
      IsPVM fun a => (aOp (hatMats MB W u a) : Matrix ((dB × Anc F m) × P.EB) _ ℂ) := fun u _ =>
    (isPVM_hatMats hprojB W u).aOp
  have hterm : ∀ (u : Point F m) (a : F), snorm P.Φ
      (aOp ((((evalMarg P.SA W u).mats a).val)
        * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2
      ≤ 2 * xSqNorm P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a))
        + 2 * xSqNorm P.Φ (aOp (hatMats MA W u a)) (aOp (hatMats MB W u a)) := by
    intro u a
    exact snorm_sq_aOp_mul_one_sub_le P.Φ ((hT u).isSelfAdjoint a) ((hT u).idem a)
      ((hB u a).isSelfAdjoint a) ((hB u a).idem a)
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a (_ : a ∈ univ) => hterm u a)
      (uniform_nonneg (Point F m) u)
  have hsplit : ∑ u, uniform (Point F m) u * ∑ a : F,
      (2 * xSqNorm P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a))
        + 2 * xSqNorm P.Φ (aOp (hatMats MA W u a)) (aOp (hatMats MB W u a)))
      = 2 * (∑ u, uniform (Point F m) u * ∑ a : F,
          xSqNorm P.Φ (((evalMarg P.SA W u).mats a).val) (aOp (hatMats MB W u a)))
        + 2 * ∑ u, uniform (Point F m) u * ∑ a : F,
          xSqNorm P.Φ (aOp (hatMats MA W u a)) (aOp (hatMats MB W u a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hsplit] at hsum
  linarith [P.sum_xSqNorm_evalMarg_le W, P.sum_xSqNorm_hat_le (hm := hm) hψ hfail W]

end SimulPair

end MIPRE.QLD

end
