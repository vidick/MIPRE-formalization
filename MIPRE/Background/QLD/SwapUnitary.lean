/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.ExactPauli
import MIPRE.Foundations.WeylEPR
import MIPRE.Foundations.Sandwich

/-!
# The swap unitary, and why two twirls force an EPR pair

Blueprint `lem:qld-swap`, the part of it that is **exact**, together with the elementary estimate
that turns the exact part into the closeness statement.

The appendix builds, out of the simultaneous pair measurement `S`, a *local unitary*

`V = sum_{(g_X, g_Z)} S_{g_X,g_Z}  (x)  tau^X(cd g_Z) tau^Z(cd g_X)`

and shows that conjugation by it carries each exact Pauli observable `wTilde` of
`MIPRE/Background/QLD/ExactPauli.lean` to a *bare* Weyl operator on the ancilla,
`V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. Both statements are identities, and both are here
(`swapU_mul_conjTranspose`, `swapU_conj`).

## The algebra of `sTensor`

Every operator in sight has the shape `sum_p S_p (x) T_p` for a family `T` on the ancilla. Because
`S` is projective, these compose factorwise (`sTensor_mul`), so the whole calculation is arithmetic
in `T` and the projectivity of `S` is used once, in that one lemma. Unitarity of `V` and the
conjugation identity are then two lines each.

## The two twirls

The estimate rests on an identity about the Weyl system alone, with no measurement in it:

`twirl_mul_twirl`:  `(E_u tau^X(u) (x) tau^X(u)) * (E_v tau^Z(v) (x) tau^Z(v)) = |EPR_q><EPR_q|` .

The paper reaches it through an iterated tensor product over the `M` qudits. In this
repository `(C^q)^{(x) M}` is *one* matrix algebra indexed by `F_q^M`
(`MIPRE/Foundations/Weyl.lean` explains why), so the identity is a single entry computation: the
`v`-average kills every off-diagonal pair of column indices by the cancellation lemma, and the
`u`-average then leaves exactly the diagonal pair of row indices.

## The repaired arithmetic

`re_inner_ge_of_two_close` is the last step, and it is where the pinned paper carried an error that
the verification campaign repaired: the earlier text bounded `||(H_W - Id) v||` by `delta_S` where
the display above it gives `delta_S` for the *square*, and compared a squared triangle inequality
with `2 sqrt(delta_S)` where the bound on the square is `4 delta_S`. The conclusion
`O(sqrt(delta_S))` is unchanged; only the constants move, and the chain below is the corrected one:
from `Re<theta, H_W theta> >= 1 - delta/2` for both `W` one gets
`Re<H_X theta, H_Z theta> >= 1 - 2 sqrt(delta) - 2 delta`.

The case split in its proof is not in the paper and is not a repair --- it is what a statement
with no implicit "for small enough `delta`" needs: for `delta > 1` the first chain's
`1 - sqrt(delta)` is negative and squaring it reverses, so that range is handled by the trivial
bound `Re<x,y> >= -2 delta`, which is already stronger there.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

set_option linter.unusedSectionVars false

/-! ## Operators block-diagonal along a pair measurement -/

/-- `sum_p S_p (x) T_p`: an ancilla-side family `T` read along the outcomes of `S`. The swap
unitary, the exact Pauli observables and the identity are all of this shape. -/
def sTensor (S : G × G → Matrix dA dA ℂ) (T : G × G → Matrix (n → F) (n → F) ℂ) :
    Matrix (dA × (n → F)) (dA × (n → F)) ℂ :=
  ∑ p, S p ⊗ₖ T p

/-- **The composition law.** Projectivity of `S` makes these operators multiply factorwise: the
cross terms `S_p S_q` with `p != q` vanish. This is the only place projectivity is used. -/
theorem sTensor_mul {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S)
    (T T' : G × G → Matrix (n → F) (n → F) ℂ) :
    sTensor S T * sTensor S T' = sTensor S fun p => T p * T' p := by
  classical
  rw [sTensor, sTensor, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single p (fun q _ hq => ?_) fun hmem =>
    absurd (Finset.mem_univ p) hmem]
  · rw [← Matrix.mul_kronecker_mul, hS.idem]
  · rw [← Matrix.mul_kronecker_mul, hS.orthogonal hq.symm, Matrix.zero_kronecker]

/-- The constant family at the identity gives the identity. -/
theorem sTensor_one {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S) :
    sTensor S (fun _ => (1 : Matrix (n → F) (n → F) ℂ)) = 1 := by
  show (∑ p, S p ⊗ₖ (1 : Matrix (n → F) (n → F) ℂ)) = 1
  rw [← sum_kron, hS.sum_eq_one, Matrix.one_kronecker_one]

/-- Adjoints are taken factorwise. -/
theorem sTensor_conjTranspose {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S)
    (T : G × G → Matrix (n → F) (n → F) ℂ) :
    (sTensor S T)ᴴ = sTensor S fun p => (T p)ᴴ := by
  rw [sTensor, sTensor, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun p _ => by
    rw [Matrix.conjTranspose_kronecker, hS.isSelfAdjoint]

/-- **The exact Pauli observable is of this shape**, with the signed constant family: this is
`wTilde_eq` rewritten so that `sTensor_mul` applies to it. -/
theorem wTilde_eq_sTensor (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
    (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : F) (u : n → F) :
    wTilde S pi cd w e u = sTensor S fun p => sgn (cdPhase pi cd e u p) • w (e • u) := by
  rw [wTilde_eq, sTensor, pvmObs, sum_kron]
  exact Finset.sum_congr rfl fun p _ => by rw [Matrix.smul_kronecker, Matrix.kronecker_smul]

/-! ## The swap unitary -/

/-- The ancilla-side factor of the swap unitary at one outcome: `tau^X(cd g_Z) tau^Z(cd g_X)`.
Note the crossing --- the argument of the `X`-type operator is the `Z`-side polynomial. -/
def uOf (cd : G → (n → F)) (p : G × G) : Matrix (n → F) (n → F) ℂ :=
  wX (cd p.2) * wZ (cd p.1)

/-- **The swap unitary** of the appendix's isometry construction. -/
def swapU (S : G × G → Matrix dA dA ℂ) (cd : G → (n → F)) :
    Matrix (dA × (n → F)) (dA × (n → F)) ℂ :=
  sTensor S (uOf cd)

theorem uOf_conjTranspose (cd : G → (n → F)) (p : G × G) :
    (uOf cd p)ᴴ = wZ (cd p.1) * wX (cd p.2) := by
  rw [uOf, Matrix.conjTranspose_mul, wX_conjTranspose, wZ_conjTranspose]

theorem uOf_mul_conjTranspose (cd : G → (n → F)) (p : G × G) :
    uOf cd p * (uOf cd p)ᴴ = 1 := by
  rw [uOf_conjTranspose, uOf]
  calc wX (cd p.2) * wZ (cd p.1) * (wZ (cd p.1) * wX (cd p.2))
      = wX (cd p.2) * (wZ (cd p.1) * wZ (cd p.1)) * wX (cd p.2) := by noncomm_ring
    _ = 1 := by
        rw [wZ_mul_wZ, add_self_vec, wZ_zero, Matrix.mul_one, wX_mul_wX, add_self_vec, wX_zero]

theorem uOf_conjTranspose_mul (cd : G → (n → F)) (p : G × G) :
    (uOf cd p)ᴴ * uOf cd p = 1 := by
  rw [uOf_conjTranspose, uOf]
  calc wZ (cd p.1) * wX (cd p.2) * (wX (cd p.2) * wZ (cd p.1))
      = wZ (cd p.1) * (wX (cd p.2) * wX (cd p.2)) * wZ (cd p.1) := by noncomm_ring
    _ = 1 := by
        rw [wX_mul_wX, add_self_vec, wX_zero, Matrix.mul_one, wZ_mul_wZ, add_self_vec, wZ_zero]

variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}

/-- **The swap map is unitary.** -/
theorem swapU_mul_conjTranspose (hS : IsPVM S) : swapU S cd * (swapU S cd)ᴴ = 1 := by
  rw [swapU, sTensor_conjTranspose hS, sTensor_mul hS,
    show (fun p => uOf cd p * (uOf cd p)ᴴ) = fun _ => (1 : Matrix (n → F) (n → F) ℂ) from
      funext fun p => uOf_mul_conjTranspose cd p,
    sTensor_one hS]

theorem swapU_conjTranspose_mul (hS : IsPVM S) : (swapU S cd)ᴴ * swapU S cd = 1 := by
  rw [swapU, sTensor_conjTranspose hS, sTensor_mul hS,
    show (fun p => (uOf cd p)ᴴ * uOf cd p) = fun _ => (1 : Matrix (n → F) (n → F) ℂ) from
      funext fun p => uOf_conjTranspose_mul cd p,
    sTensor_one hS]

/-! ### Conjugating a Weyl operator by the ancilla factor

Two instances of the twisted commutation relation, in the only form the conjugation needs. -/

/-- `(tau^X(x) tau^Z(z)) tau^X(a) (tau^X(x) tau^Z(z))^dagger = (-1)^{tr(a . z)} tau^X(a)`. -/
theorem uOf_conj_wX (cd : G → (n → F)) (p : G × G) (a : n → F) :
    uOf cd p * wX a * (uOf cd p)ᴴ = sgn (trDot a (cd p.1)) • wX a := by
  have hzx : wZ (cd p.1) * wX a = sgn (trDot a (cd p.1)) • (wX a * wZ (cd p.1)) := by
    rw [wX_mul_wZ, smul_smul, sgn_mul_self, one_smul]
  rw [uOf_conjTranspose, uOf]
  calc wX (cd p.2) * wZ (cd p.1) * wX a * (wZ (cd p.1) * wX (cd p.2))
      = wX (cd p.2) * ((wZ (cd p.1) * wX a) * wZ (cd p.1)) * wX (cd p.2) := by noncomm_ring
    _ = sgn (trDot a (cd p.1)) • wX a := by
        rw [hzx, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
          show wX a * wZ (cd p.1) * wZ (cd p.1) = wX a from by
            rw [mul_assoc, wZ_mul_wZ, add_self_vec, wZ_zero, Matrix.mul_one],
          wX_mul_wX, wX_mul_wX]
        congr 1
        rw [add_comm (cd p.2) a, add_assoc, add_self_vec, add_zero]

/-- `(tau^X(x) tau^Z(z)) tau^Z(b) (tau^X(x) tau^Z(z))^dagger = (-1)^{tr(x . b)} tau^Z(b)`. -/
theorem uOf_conj_wZ (cd : G → (n → F)) (p : G × G) (b : n → F) :
    uOf cd p * wZ b * (uOf cd p)ᴴ = sgn (trDot (cd p.2) b) • wZ b := by
  rw [uOf_conjTranspose, uOf]
  calc wX (cd p.2) * wZ (cd p.1) * wZ b * (wZ (cd p.1) * wX (cd p.2))
      = wX (cd p.2) * (wZ (cd p.1) * wZ b * wZ (cd p.1)) * wX (cd p.2) := by noncomm_ring
    _ = wX (cd p.2) * wZ b * wX (cd p.2) := by
        rw [wZ_mul_wZ, wZ_mul_wZ, show cd p.1 + b + cd p.1 = b from by
          rw [add_comm (cd p.1) b, add_assoc, add_self_vec, add_zero]]
    _ = sgn (trDot (cd p.2) b) • wZ b := by
        rw [wX_mul_wZ, Matrix.smul_mul, show wZ b * wX (cd p.2) * wX (cd p.2) = wZ b from by
          rw [mul_assoc, wX_mul_wX, add_self_vec, wX_zero, Matrix.mul_one]]

/-! ### The conjugation identity -/

/-- **Conjugation by the swap unitary strips the measurement off the observable.** For a family
whose ancilla factor conjugates to itself up to the very sign the first factor carries, the two
signs cancel and only the bare ancilla operator survives:
`V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. -/
theorem swapU_conj_of_sign (hS : IsPVM S) {phi : G × G → ZMod 2}
    {B : Matrix (n → F) (n → F) ℂ} (hB : ∀ p, uOf cd p * B * (uOf cd p)ᴴ = sgn (phi p) • B) :
    swapU S cd * sTensor S (fun p => sgn (phi p) • B) * (swapU S cd)ᴴ = 1 ⊗ₖ B := by
  rw [swapU, sTensor_mul hS, sTensor_conjTranspose hS, sTensor_mul hS]
  rw [show (fun p => uOf cd p * (sgn (phi p) • B) * (uOf cd p)ᴴ) = fun _ => B from
    funext fun p => by
      rw [Matrix.mul_smul, Matrix.smul_mul, hB p, smul_smul, sgn_mul_self, one_smul]]
  show (∑ p, S p ⊗ₖ B) = 1 ⊗ₖ B
  rw [← sum_kron, hS.sum_eq_one]

/-- **The `X`-side conjugation identity.** -/
theorem swapU_conj_wTilde_X (hS : IsPVM S) (e : F) (u : n → F) :
    swapU S cd * wTilde S Prod.fst cd wX e u * (swapU S cd)ᴴ = 1 ⊗ₖ wX (e • u) := by
  rw [wTilde_eq_sTensor]
  refine swapU_conj_of_sign hS fun p => ?_
  rw [uOf_conj_wX, cdPhase, trDot_smul, dotF_comm]

/-- **The `Z`-side conjugation identity.** -/
theorem swapU_conj_wTilde_Z (hS : IsPVM S) (e : F) (u : n → F) :
    swapU S cd * wTilde S Prod.snd cd wZ e u * (swapU S cd)ᴴ = 1 ⊗ₖ wZ (e • u) := by
  rw [wTilde_eq_sTensor]
  refine swapU_conj_of_sign hS fun p => ?_
  rw [uOf_conj_wZ, cdPhase, trDot_smul_right]

/-! ## The two twirls, and the maximally entangled state -/

/-- The rank-one projector onto the maximally entangled state of the two ancilla halves. The
generalized Paulis in characteristic two are real, so no conjugation appears. -/
def eprProj : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ :=
  Matrix.vecMulVec (epr (F := F) (n := n)) (epr (F := F) (n := n))

theorem eprProj_apply (j i : (n → F) × (n → F)) :
    eprProj (F := F) (n := n) j i
      = if j.1 = j.2 then (if i.1 = i.2 then (Fintype.card (n → F) : ℂ)⁻¹ else 0) else 0 := by
  rw [eprProj, Matrix.vecMulVec_apply, epr, epr]
  by_cases hj : j.1 = j.2
  · rw [if_pos hj, if_pos hj]
    by_cases hi : i.1 = i.2
    · rw [if_pos hi, if_pos hi, ← Complex.ofReal_mul, ← sq, eprScale_sq]
      push_cast
      rfl
    · rw [if_neg hi, if_neg hi, mul_zero]
  · rw [if_neg hj, if_neg hj, zero_mul]

/-- **The Weyl twirl** `E_u tau^W(u) (x) tau^W(u)` on two copies of the ancilla. -/
def twirl (w : (n → F) → Matrix (n → F) (n → F) ℂ) :
    Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ u : n → F, w u ⊗ₖ w u

/-- One entry of a product of an `X`-type and a `Z`-type Weyl operator: the `Z` factor is diagonal,
so the matrix product is a single term. -/
theorem wX_mul_wZ_apply (u v j i : n → F) :
    (wX u * wZ v) j i = (if j = i + u then (1 : ℂ) else 0) * sgn (trDot v i) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [wZ_apply, if_neg hk, mul_zero]) fun hmem => absurd (Finset.mem_univ i) hmem,
    wZ_apply, if_pos rfl, wX_apply]

/-- The product of the two twirls, as one double average of products. -/
theorem twirl_mul_twirl_eq_sum :
    twirl (wX (F := F) (n := n)) * twirl wZ
      = ((Fintype.card (n → F) : ℂ)⁻¹ * (Fintype.card (n → F) : ℂ)⁻¹) •
        ∑ u : n → F, ∑ v : n → F, (wX u * wZ v) ⊗ₖ (wX u * wZ v) := by
  rw [twirl, twirl, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => (Matrix.mul_kronecker_mul _ _ _ _).symm

/-- **The product of the two Weyl twirls is the maximally entangled projector.**

This is the one identity behind the swap isometry, and it involves no measurement: averaging
`tau^Z(v) (x) tau^Z(v)` over `v` kills every pair of column indices off the diagonal
(`sum_sgn_trDot`), and averaging `tau^X(u) (x) tau^X(u)` over `u` then leaves exactly the diagonal
pairs of row indices, with weight `1/q^n`.

The paper proves it by an induction over the `n` qudits, having presented the ancilla as an
iterated tensor product. Here the ancilla is a single matrix algebra indexed by `F_q^n`, so the
proof is one entry computation and the induction disappears. -/
theorem twirl_mul_twirl :
    twirl (wX (F := F) (n := n)) * twirl wZ = eprProj := by
  classical
  have hN : (Fintype.card (n → F) : ℂ) ≠ 0 := card_ne_zero
  rw [twirl_mul_twirl_eq_sum]
  ext j i
  obtain ⟨j1, j2⟩ := j
  obtain ⟨i1, i2⟩ := i
  rw [Matrix.smul_apply, eprProj_apply]
  -- the entry of the double sum factors into a row part and a column part
  have hterm : ∀ u v : n → F,
      ((wX u * wZ v) ⊗ₖ (wX u * wZ v)) (j1, j2) (i1, i2)
        = ((if j1 = i1 + u then (1 : ℂ) else 0) * (if j2 = i2 + u then (1 : ℂ) else 0))
          * sgn (trDot v (i1 + i2)) := by
    intro u v
    rw [Matrix.kronecker_apply, wX_mul_wZ_apply, wX_mul_wZ_apply, trDot_add_right, sgn_add]
    ring
  have hentry : (∑ u : n → F, ∑ v : n → F, (wX u * wZ v) ⊗ₖ (wX u * wZ v)) (j1, j2) (i1, i2)
      = (∑ u : n → F, (if j1 = i1 + u then (1 : ℂ) else 0)
            * (if j2 = i2 + u then (1 : ℂ) else 0))
        * ∑ v : n → F, sgn (trDot v (i1 + i2)) := by
    rw [Matrix.sum_apply, Finset.sum_congr rfl fun u (_ : u ∈ univ) => by
        rw [Matrix.sum_apply, Finset.sum_congr rfl fun v (_ : v ∈ univ) => hterm u v,
          ← Finset.mul_sum],
      ← Finset.sum_mul]
  rw [hentry]
  by_cases hi : i1 = i2
  · -- the column indices agree, so the `v`-average is the whole dimension
    rw [if_pos hi, show i1 + i2 = 0 from by rw [hi, add_self_vec], sum_sgn_trDot_zero]
    by_cases hj : j1 = j2
    · -- and the `u`-average picks out the single shift carrying the rows onto the columns
      have hsum : (∑ u : n → F, (if j1 = i1 + u then (1 : ℂ) else 0)
            * (if j2 = i2 + u then (1 : ℂ) else 0)) = 1 := by
        rw [Finset.sum_eq_single (j1 + i1) (fun u _ hu => ?_)
          fun hmem => absurd (Finset.mem_univ (j1 + i1)) hmem]
        · rw [show i1 + (j1 + i1) = j1 from by
              rw [add_comm j1 i1, ← add_assoc, add_self_vec, zero_add], if_pos rfl,
            show i2 + (j1 + i1) = j2 from by
              rw [← hi, add_comm j1 i1, ← add_assoc, add_self_vec, zero_add]; exact hj,
            if_pos rfl, mul_one]
        · by_cases hh : j1 = i1 + u
          · exact absurd (show u = j1 + i1 from by
              rw [hh, add_comm i1 u, add_add_cancel_vec]) hu
          · rw [if_neg hh, zero_mul]
      rw [if_pos hj, hsum, one_mul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hN, mul_one]
    · -- the rows disagree, so no shift can carry both onto the columns
      rw [if_neg hj, Finset.sum_congr rfl fun u (_ : u ∈ univ) => show
          (if j1 = i1 + u then (1 : ℂ) else 0) * (if j2 = i2 + u then (1 : ℂ) else 0) = 0 from by
        by_cases h1 : j1 = i1 + u
        · rw [if_neg fun h2 : j2 = i2 + u => hj (by rw [h1, hi, h2]), mul_zero]
        · rw [if_neg h1, zero_mul], Finset.sum_const_zero, zero_mul, smul_zero]
  · -- the column indices disagree, so the character in the `v`-average is nontrivial
    rw [if_neg hi, sum_sgn_trDot (c := i1 + i2) fun hh => hi ((add_eq_zero_iff_vec i1 i2).mp hh),
      mul_zero, smul_zero, ite_self]

/-! ## From two near-invariances to the overlap

The last step of `lem:qld-swap`, in the state-independent form: two vectors each close to a unit
vector have a large inner product with one another. Both lemmas are elementary, and both are
stated for a bound rather than for the quantity itself, so that no "for small enough" is hidden. -/

section TwoClose

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **A contraction with a large overlap moves a unit vector little.** `||theta - x||^2 =
||theta||^2 - 2 Re<theta, x> + ||x||^2`, and both squared norms are at most one. -/
theorem norm_sub_sq_le_of_re_inner_ge {θ x : E} {δ : ℝ} (hθ : ‖θ‖ = 1) (hx : ‖x‖ ≤ 1)
    (h : 1 - δ / 2 ≤ (inner ℂ θ x : ℂ).re) : ‖θ - x‖ ^ 2 ≤ δ := by
  have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hxs : ‖x‖ ^ 2 ≤ 1 := by nlinarith
  rw [norm_sub_sq (𝕜 := ℂ), hθ]
  simp only [RCLike.re_to_complex]
  nlinarith

/-- **The repaired arithmetic chain of the swap isometry.** If `x` and `y` are each within
`sqrt(delta)` of the same unit vector then `Re<x, y> >= 1 - 2 sqrt(delta) - 2 delta`.

The two ranges are handled separately because the statement carries no smallness assumption. For
`delta <= 1` the bound `||x|| >= 1 - sqrt(delta)` may be squared, and the triangle inequality
`||x - y|| <= 2 sqrt(delta)` gives the claim. For `delta > 1` the same squaring is invalid ---
`1 - sqrt(delta)` is negative --- but there the claim is weaker than the trivial
`Re<x, y> >= -2 delta`, which follows from the triangle inequality and the nonnegativity of the two
squared norms alone. -/
theorem re_inner_ge_of_two_close {θ x y : E} {δ : ℝ} (hδ : 0 ≤ δ) (hθ : ‖θ‖ = 1)
    (hx : ‖θ - x‖ ^ 2 ≤ δ) (hy : ‖θ - y‖ ^ 2 ≤ δ) :
    1 - 2 * Real.sqrt δ - 2 * δ ≤ (inner ℂ x y : ℂ).re := by
  have hs : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ
  have hs0 : (0 : ℝ) ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hxd : ‖θ - x‖ ≤ Real.sqrt δ := by
    rw [show ‖θ - x‖ = Real.sqrt (‖θ - x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hx
  have hyd : ‖θ - y‖ ≤ Real.sqrt δ := by
    rw [show ‖θ - y‖ = Real.sqrt (‖θ - y‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hy
  -- the triangle inequality on the difference of the two vectors
  have hxy : ‖x - y‖ ≤ 2 * Real.sqrt δ := by
    calc ‖x - y‖ = ‖(θ - y) - (θ - x)‖ := by rw [show (θ - y) - (θ - x) = x - y from by abel]
      _ ≤ ‖θ - y‖ + ‖θ - x‖ := norm_sub_le _ _
      _ ≤ 2 * Real.sqrt δ := by linarith
  have hexp : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x y : ℂ).re + ‖y‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp only [RCLike.re_to_complex]
  have hxy2 : ‖x‖ ^ 2 - 2 * (inner ℂ x y : ℂ).re + ‖y‖ ^ 2 ≤ 4 * δ := by
    rw [← hexp]
    nlinarith [norm_nonneg (x - y)]
  rcases le_or_gt δ 1 with hle | hgt
  · -- the squaring is valid, and gives the stated bound
    have hsle : Real.sqrt δ ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hle
    have hxn : 1 - Real.sqrt δ ≤ ‖x‖ := by
      have := norm_sub_norm_le θ x
      rw [hθ] at this
      linarith
    have hyn : 1 - Real.sqrt δ ≤ ‖y‖ := by
      have := norm_sub_norm_le θ y
      rw [hθ] at this
      linarith
    nlinarith
  · -- outside that range the trivial bound is already stronger
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]


/-- **A state with large weight on a projector is close to its normalized projection.** The
appendix's extraction of the auxiliary state: with `x = P theta` for a projector `P`, the
hypothesis `hx` is `<theta, P theta> = ||P theta||^2`, and the conclusion bounds the squared
distance from `theta` to the unit vector along `x`.

This is where the paper's `sqrt` enters, and the reason `lem:qld-swap`'s error is `delta_S^{1/4}`
and not `delta_S^{1/2}`: the overlap is the square root of the weight, and the squared distance is
twice its deficit. -/
theorem norm_sub_normalize_sq_le {θ x : E} {η : ℝ} (hθ : ‖θ‖ = 1)
    (hx : ‖x‖ ^ 2 = (inner ℂ θ x : ℂ).re) (hlt : η < 1)
    (hlow : 1 - η ≤ (inner ℂ θ x : ℂ).re) :
    ‖θ - ((‖x‖⁻¹ : ℝ) : ℂ) • x‖ ^ 2 ≤ 2 - 2 * Real.sqrt (1 - η) := by
  have h0 : (0 : ℝ) < 1 - η := by linarith
  have hxpos : 0 < ‖x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg x) with h | h
    · exfalso
      rw [← h] at hx
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hx
      linarith [hx ▸ hlow]
    · exact h
  -- the norm of the projection is the square root of the weight
  have hnormx : Real.sqrt (1 - η) ≤ ‖x‖ := by
    rw [show ‖x‖ = Real.sqrt (‖x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, hx]
    exact Real.sqrt_le_sqrt hlow
  -- the normalized vector is a unit vector whose overlap with `theta` is that norm
  have hunit : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
  have hov : (inner ℂ θ (((‖x‖⁻¹ : ℝ) : ℂ) • x) : ℂ).re = ‖x‖ := by
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, ← hx]
    field_simp
  rw [norm_sub_sq (𝕜 := ℂ), hθ, hunit]
  simp only [RCLike.re_to_complex]
  rw [hov]
  linarith

end TwoClose

end MIPRE.QLD

end
