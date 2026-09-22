/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.MTilde
import MIPRE.Background.QLD.AncTransport

/-!
# The estimates of `lem:qld-pauli-selfcons`, by polynomial outcome

`MIPRE/Background/QLD/AncTransport.lean` closes the identities of the paper's pulling chain. Its
estimates --- displays `eq:qld-pulling-7` and `eq:qld-pulling-11` --- consume the second item of
`lem:qld-helper`, but not in the form that lemma is stated in. The helper is stated at an outcome
`a` in `F_q`, which is what the expansion stage produces; the chain sums over the *polynomial*
outcomes `g` of the simultaneous measurement, because the label `coded(g) . u-tilde` it carries is
a function of `g` and not of `g(u)`.

The two sums are equal, not merely comparable. Within a fibre of the evaluation the pair
measurement's outcomes are orthogonal projectors, so every cross term of the squared norm
vanishes, and the fibres partition the outcomes. That is `snorm_sq_sum_orthogonal` below, and the
helper in the chain's own indexing is its corollary.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## A squared norm over orthogonal outcomes -/

section Orthogonal

variable {N : Type*} [Fintype N] [DecidableEq N] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **A sum of orthogonal blocks has no cross terms.** If `S` is a projective family then, for any
`R`, the squared state norm of `(∑ g ∈ s, S g) R` is the sum of those of the `S g · R`. -/
theorem snorm_sq_sum_orthogonal (v : N → ℂ) {S : Λ → Matrix N N ℂ} (hS : IsPVM S)
    (R : Matrix N N ℂ) (s : Finset Λ) :
    snorm v ((∑ g ∈ s, S g) * R) ^ 2 = ∑ g ∈ s, snorm v (S g * R) ^ 2 := by
  classical
  rw [snorm_sq_eq_qform, Finset.sum_mul, Matrix.conjTranspose_sum, Finset.sum_mul]
  have hterm : ∀ g ∈ s, ((S g * R)ᴴ * ∑ g' ∈ s, S g' * R) = (S g * R)ᴴ * (S g * R) := by
    intro g hg
    rw [Finset.mul_sum, Finset.sum_eq_single_of_mem g hg fun g' _ hg' => ?_]
    rw [Matrix.conjTranspose_mul, hS.isSelfAdjoint, Matrix.mul_assoc,
      ← Matrix.mul_assoc (S g) (S g') R, hS.orthogonal (Ne.symm hg'), Matrix.zero_mul,
      Matrix.mul_zero]
  rw [Finset.sum_congr rfl hterm, qform_sum]
  exact Finset.sum_congr rfl fun g _ => (snorm_sq_eq_qform v (S g * R)).symm

end Orthogonal

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

section Helper

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- The pair space is a four-fold product whose `DecidableEq` runs past the default instance-size
bound; raised as in `MIPRE/Background/QLD/MTilde.lean`. -/
set_option synthInstance.maxSize 1000

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **The evaluated marginal's same-party product, split by polynomial outcome.** The evaluated
marginal at `a` is the sum of the polynomial-indexed outcomes over the fibre `g(u) = a`, and those
are orthogonal projectors, so the squared norms add. -/
theorem snorm_sq_evalMarg_eq_sum_polyMarg (W : Bas) (u : Point F m) (a : F) :
    snorm P.Φ (aOp ((((evalMarg P.SA W u).mats a).val)
          * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2
      = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          snorm P.Φ (aOp (((polyMarg P.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2 := by
  classical
  have hsplit : (((evalMarg P.SA W u).mats a).val)
      = ∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          ((polyMarg P.SA W).mats g).val := by
    rw [evalMarg_eq_map_polyMarg]
    exact POVM.map_mats _ _ _
  rw [hsplit, Finset.sum_mul, aOp_sum]
  rw [show (∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
      (aOp (((polyMarg P.SA W).mats g).val
        * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))
        : Matrix (((dA × Anc F m) × P.EA) × ((dB × Anc F m) × P.EB)) _ ℂ))
      = (∑ g ∈ univ.filter fun g : LowIndDegPoly (F := F) (m := m) (d := d) => g.eval u = a,
          (aOp (((polyMarg P.SA W).mats g).val)
            : Matrix (((dA × Anc F m) × P.EA) × ((dB × Anc F m) × P.EB)) _ ℂ))
        * aOp (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)) from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun g _ => aOp_mul _ _]
  rw [snorm_sq_sum_orthogonal P.Φ (isPVM_polyMarg P.SA_proj W).aOp _ _]
  exact Finset.sum_congr rfl fun g _ => by rw [aOp_mul]

/-- **Item 2 of `lem:qld-helper`, in the chain's own indexing**: the same-party product of the
*polynomial-indexed* marginal with the complement of Alice's point measurement at that outcome's
own value. This is the form displays `eq:qld-pulling-7` and `eq:qld-pulling-11` consume. -/
theorem sum_snorm_sq_polyMarg_one_sub_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) :
    ∑ u, uniform (Point F m) u
        * ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), snorm P.Φ
          (aOp (((polyMarg P.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  classical
  have h := P.sum_snorm_sq_evalMarg_one_sub_le (hm := hm) hψ hfail hprojB W
  have hu : ∀ u : Point F m,
      (∑ a : F, snorm P.Φ (aOp ((((evalMarg P.SA W u).mats a).val)
          * (1 - (aOp (hatMats MA W u a) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2)
        = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), snorm P.Φ
          (aOp (((polyMarg P.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2 :=
    fun u => by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        P.snorm_sq_evalMarg_eq_sum_polyMarg W u a]
      rw [← Finset.sum_fiberwise (univ : Finset (LowIndDegPoly (F := F) (m := m) (d := d)))
        (fun g => g.eval u) fun g => snorm P.Φ (aOp (((polyMarg P.SA W).mats g).val
          * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × P.EA) _ ℂ)))) ^ 2]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g hg => by
        rw [(Finset.mem_filter.mp hg).2]
  rwa [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hu u]] at h

end SimulPair

end Helper

/-! ## Passing from pointwise agreement to equality of polynomials -/

section Agree

open MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

omit [NeZero m] in
/-- **Schwartz--Zippel for two low-individual-degree outcomes.** Distinct polynomials of individual
degree at most `d` agree at a uniform point with probability at most `md/q`. No lower bound on `d`
is needed: both polynomials carry the same degree bound, so the hypothesis
`prob_agree_le_individualDegree` wants is already met. -/
theorem sum_uniform_agree_le
    {p q : LowIndDegPoly (F := F) (m := m) (d := d)} (hne : p.toMv ≠ q.toMv) :
    ∑ u, uniform (Point F m) u * (if p.eval u = q.eval u then (1 : ℝ) else 0)
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  have hsz := prob_agree_le_individualDegree hne (LowIndDegPoly.degreeOf_toMv_le p)
    (LowIndDegPoly.degreeOf_toMv_le q)
  have hset : (univ.filter fun u : Point F m => p.eval u = q.eval u) = agree p.toMv q.toMv := by
    ext u
    rw [mem_filter, mem_agree, LowIndDegPoly.eval_toMv, LowIndDegPoly.eval_toMv]
    simp only [mem_univ, true_and]
  simp only [uniform]
  rw [← Finset.mul_sum, Finset.sum_boole, hset, Fintype.card_fun, Fintype.card_fin]
  push_cast at hsz ⊢
  rw [inv_mul_eq_div]
  exact hsz

omit [NeZero m] in
/-- **Restricting a weighted sum to pointwise agreement costs `md/q`** when the polynomials
compared are distinct. This is display `eq:qld-pulling-12`: the chain's sum is constrained by an
equality of polynomial *values* at the sampled point, and passing to equality of the polynomials
themselves discards only the tuples where distinct polynomials happen to agree there. The weights
are the Born probabilities of a projective family, hence nonnegative and summing to at most one. -/
theorem sum_uniform_agree_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ι → LowIndDegPoly (F := F) (m := m) (d := d)} (hne : ∀ i, (p i).toMv ≠ (q i).toMv)
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i ≤ 1) :
    ∑ u, uniform (Point F m) u
        * ∑ i ∈ univ.filter fun i => (p i).eval u = (q i).eval u, w i
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  have hmd : (0 : ℝ) ≤ (m : ℝ) * d / Fintype.card F := by positivity
  have hswap : (∑ u, uniform (Point F m) u
        * ∑ i ∈ univ.filter fun i => (p i).eval u = (q i).eval u, w i)
      = ∑ i, w i * ∑ u, uniform (Point F m) u
          * (if (p i).eval u = (q i).eval u then (1 : ℝ) else 0) := by
    simp only [Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
  rw [hswap]
  calc ∑ i, w i * ∑ u, uniform (Point F m) u
          * (if (p i).eval u = (q i).eval u then (1 : ℝ) else 0)
      ≤ ∑ i, w i * ((m : ℝ) * d / Fintype.card F) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (sum_uniform_agree_le (hne i)) (hw0 i)
    _ = (∑ i, w i) * ((m : ℝ) * d / Fintype.card F) := by rw [Finset.sum_mul]
    _ ≤ 1 * ((m : ℝ) * d / Fintype.card F) := mul_le_mul_of_nonneg_right hw hmd
    _ = (m : ℝ) * d / Fintype.card F := one_mul _

end Agree

end MIPRE.QLD

end
