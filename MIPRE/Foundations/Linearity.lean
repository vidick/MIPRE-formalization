/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Dilation
import MIPRE.Foundations.Parseval
import MIPRE.Foundations.PVM
import MIPRE.Foundations.StateDistance
import MIPRE.Foundations.Weyl

/-!
# Approximate linearity gives exact linearity

Blueprint `thm:linearity`, the quantum linearity test. A family of observables
`{O^u}_{u in F_q^n}` that is *approximately* linear --- `O^u O^{u'}` close to `O^{u + u'}` on
average, in the state-dependent distance --- is close on average to a family that is *exactly*
linear, after adjoining an ancilla register to one player.

The paper imports this from Natarajan--Vidick; it is proved here. The route is the one the
blueprint's proof text names, and every step of it is already in this repository:

* **Parseval.** The Fourier transform `A_e = |V|^{-1} sum_a (-1)^{<a,e>} O^a` of the family
  against the characters of the trace form has `sum_e A_e^2 = |V|^{-1} sum_a (O^a)^2 = Id`
  whenever each `O^a` is an involution. So `{A_e^2}` is a POVM --- **exactly**, with no
  appeal to the approximate linearity, which is the one surprise of the argument.
* **Naimark.** `exists_projective_dilation` dilates that POVM to a projective measurement
  `{P_e}` on `d x V`, compressed back by the isometry that pads with the ancilla state `|0>`.
* **Inversion.** `L^u = sum_e (-1)^{<u,e>} P_e` is then exactly linear --- `L^u L^{u'} =
  L^{u+u'}` and `L^0 = Id` --- because the `P_e` are mutually orthogonal projections, and its
  compression is `sum_e (-1)^{<u,e>} A_e^2`, which the same character sum identifies with
  `|V|^{-1} sum_a O^a O^{a+u}`.
* **The estimate.** That average is where the hypothesis enters, and it enters once:
  `|V|^{-2} sum_{a,b} <psi| O^a O^b O^{a+b} |psi>` is the hypothesis written out, so the
  closeness of `L^u` to `O^u` on the extended state carries the *same* `delta`, with no square
  root and no loss in the exponent.

The one thing to watch is which distance the hypothesis is in. It is the state-dependent one of
`def:state-distance` --- not the Hilbert--Schmidt distance of `thm:gowers-hatami` --- so this is
not Gowers--Hatami with a different normalization; the exact-POVM step above replaces the
approximate-representation machinery entirely.
-/

noncomputable section

namespace MIPRE

open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## The Fourier transform of a family of operators -/

/-- **The Fourier transform** of a family of operators indexed by `V = F_q^n`, against the
characters of the trace form. This is `MIPRE.Weyl.proj` with the index group decoupled from the
space the operators act on, and with no group law assumed. -/
def fourierOf (O : (n → F) → Matrix d d ℂ) (e : n → F) : Matrix d d ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • O a

theorem fourierOf_conjTranspose {O : (n → F) → Matrix d d ℂ} (hsa : ∀ a, (O a)ᴴ = O a)
    (e : n → F) : (fourierOf O e)ᴴ = fourierOf O e := by
  rw [fourierOf, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, star_sgn, hsa a]]
  congr 1
  simp

theorem fourierOf_posSemidef {O : (n → F) → Matrix d d ℂ} (hsa : ∀ a, (O a)ᴴ = O a)
    (e : n → F) : (fourierOf O e * fourierOf O e).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (fourierOf O e)
  rwa [fourierOf_conjTranspose hsa e] at h

/-- **The character sum that carries the whole argument.** Summing the squares of the Fourier
coefficients against a character collapses the double sum to a single one: only the pairs with
`b = a + u` survive. -/
theorem sum_sgn_smul_fourierOf_sq (O : (n → F) → Matrix d d ℂ) (u : n → F) :
    ∑ e : n → F, sgn (trDot u e) • (fourierOf O e * fourierOf O e)
      = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, O a * O (a + u) := by
  classical
  have hN : (Fintype.card (n → F) : ℂ) ≠ 0 := card_ne_zero
  -- one term, with the three characters merged
  have hterm : ∀ e : n → F, sgn (trDot u e) • (fourierOf O e * fourierOf O e)
      = ((Fintype.card (n → F) : ℂ)⁻¹ * (Fintype.card (n → F) : ℂ)⁻¹) •
          ∑ a : n → F, ∑ b : n → F, sgn (trDot (u + a + b) e) • (O a * O b) := by
    intro e
    have hexp : fourierOf O e * fourierOf O e
        = ((Fintype.card (n → F) : ℂ)⁻¹ * (Fintype.card (n → F) : ℂ)⁻¹) •
            ∑ a : n → F, ∑ b : n → F, (sgn (trDot a e) * sgn (trDot b e)) • (O a * O b) := by
      rw [fourierOf, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.smul_mul, Finset.mul_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [Matrix.mul_smul, smul_smul]
    rw [hexp, smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, trDot_add_left, trDot_add_left, sgn_add, sgn_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => hterm e, ← Finset.smul_sum]
  -- exchange the sums, so that the character sum can be evaluated
  rw [show (∑ e : n → F, ∑ a : n → F, ∑ b : n → F, sgn (trDot (u + a + b) e) • (O a * O b))
      = ∑ a : n → F, ∑ b : n → F, (∑ e : n → F, sgn (trDot (u + a + b) e)) • (O a * O b) from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_smul]]
  -- only `b = a + u` contributes
  have hinner : ∀ a : n → F,
      (∑ b : n → F, (∑ e : n → F, sgn (trDot (u + a + b) e)) • (O a * O b))
        = (Fintype.card (n → F) : ℂ) • (O a * O (a + u)) := by
    intro a
    refine (Finset.sum_eq_single_of_mem (a + u) (mem_univ _) fun b _ hb => ?_).trans ?_
    · have hne : u + a + b ≠ 0 := fun h => hb (by
        rw [← (add_eq_zero_iff_vec (u + a) b).mp h]
        exact add_comm u a)
      rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [trDot_comm],
        sum_sgn_trDot hne, zero_smul]
    · congr 1
      rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
          rw [show u + a + (a + u) = 0 from by rw [add_comm a u, add_self_vec],
            trDot_zero_left],
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sgn_zero, mul_one]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hinner a, ← Finset.smul_sum, smul_smul]
  congr 1
  field_simp

/-- **Parseval.** The squares of the Fourier coefficients of a family of *involutions* form a
POVM --- exactly, with no appeal to any approximate linearity. -/
theorem sum_fourierOf_sq (O : (n → F) → Matrix d d ℂ) (hinv : ∀ a, O a * O a = 1) :
    ∑ e : n → F, (fourierOf O e * fourierOf O e) = 1 := by
  classical
  have h := sum_sgn_smul_fourierOf_sq O 0
  simp only [trDot_zero_left, sgn_zero, one_smul, add_zero] at h
  rw [h, Finset.sum_congr rfl fun a (_ : a ∈ univ) => hinv a, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ card_ne_zero, one_smul]

omit [DecidableEq F] [DecidableEq d] in
theorem fourierOf_sub (A B : (n → F) → Matrix d d ℂ) (e : n → F) :
    fourierOf (fun v => A v - B v) e = fourierOf A e - fourierOf B e := by
  rw [fourierOf, fourierOf, fourierOf, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by rw [smul_sub]

/-- **The two-field transform of a product family factorizes.** The combined measurement of a
pair of parameters is the product of the two one-parameter measurements --- with no hypothesis, the
double average simply splitting. -/
theorem fourierOf_pair_mul (A B : F → Matrix d d ℂ) (a b : F) :
    fourierOf (fun v : Fin 2 → F => A (v 0) * B (v 1)) (pairVec a b)
      = trFourier A a * trFourier B b := by
  classical
  have hcard : (Fintype.card (Fin 2 → F) : ℂ) = (Fintype.card F : ℂ) * (Fintype.card F : ℂ) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [fourierOf, sum_pairVec, hcard, trFourier, trFourier, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Finset.sum_mul]
  rw [mul_inv]
  refine congrArg _ ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.smul_mul, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_smul, smul_smul, trDot_pairVec, sgn_add, pairVec_zero, pairVec_one]

/-- The same with the two factors in the other order. -/
theorem fourierOf_pair_mul' (A B : F → Matrix d d ℂ) (a b : F) :
    fourierOf (fun v : Fin 2 → F => B (v 1) * A (v 0)) (pairVec a b)
      = trFourier B b * trFourier A a := by
  classical
  have hcard : (Fintype.card (Fin 2 → F) : ℂ) = (Fintype.card F : ℂ) * (Fintype.card F : ℂ) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [fourierOf, sum_pairVec, hcard, trFourier, trFourier, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_inv, mul_comm ((Fintype.card F : ℂ))⁻¹ ((Fintype.card F : ℂ))⁻¹,
    Finset.sum_mul]
  refine congrArg _ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.smul_mul, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mul_smul, smul_smul, trDot_pairVec, sgn_add, pairVec_zero, pairVec_one, mul_comm]

/-- **Parseval for a family of operators against a state.** The transform is an isometry up to
the normalization, so an average bound on the family is a summed bound on the transform and
conversely. This is the dictionary between an `F_q`-valued measurement and its binary
observables. -/
theorem sum_stateSqNorm_fourierOf {dB : Type*} [Fintype dB] [DecidableEq dB]
    (ψ : d × dB → ℂ) (M : (n → F) → Matrix d d ℂ) :
    ∑ e : n → F, stateSqNorm ψ (fourierOf M e)
      = (Fintype.card (n → F) : ℝ)⁻¹ * ∑ a : n → F, stateSqNorm ψ (M a) := by
  classical
  have hvec : ∀ e : n → F, (aOp (fourierOf M e) : Matrix (d × dB) _ ℂ) *ᵥ ψ
      = fourierVec (fun a => (aOp (M a) : Matrix (d × dB) _ ℂ) *ᵥ ψ) e := by
    intro e
    rw [fourierOf, aOp_smul, aOp_sum, Matrix.smul_mulVec, fourierVec]
    congr 1
    rw [Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun a _ => by rw [aOp_smul, Matrix.smul_mulVec]
  have hnorm : ∀ (v : Matrix d d ℂ), stateSqNorm ψ v
      = ‖evec ((aOp v : Matrix (d × dB) _ ℂ) *ᵥ ψ)‖ ^ 2 := fun v => rfl
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by rw [hnorm, hvec e],
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => hnorm (M a)]
  exact sum_norm_fourierVec_sq (fun a => (aOp (M a) : Matrix (d × dB) _ ℂ) *ᵥ ψ)

/-! ## The exactly linear family -/

/-- **The exactly linear family, on the extended space.** The Fourier transform of the family is
dilated to a projective measurement on `d x V` (`exists_projective_dilation`), and inverting the
transform on the dilation gives a family that is *exactly* linear: `L^u L^{u'} = L^{u + u'}`, with
the identity at `0`. Its compression to the `|0>`-slice is the average
`|V|^{-1} sum_a O^a O^{a+u}`, which is what the closeness estimate compares with `O^u`.

The whole family is dilated by **one** isometry, question-independent, which is what lets the
estimate be taken against a single state. -/
theorem exists_exactly_linear {X : Type*} [Fintype X] (O : X → (n → F) → Matrix d d ℂ)
    (hsa : ∀ x a, (O x a)ᴴ = O x a) (hinv : ∀ x a, O x a * O x a = 1) :
    ∃ L : X → (n → F) → Matrix (d × (n → F)) (d × (n → F)) ℂ,
      (∀ x u, (L x u)ᴴ = L x u) ∧
      (∀ x u u', L x u * L x u' = L x (u + u')) ∧
      (∀ x, L x 0 = 1) ∧
      (∀ x u, (ancillaEmbed d (0 : n → F))ᴴ * (L x u * ancillaEmbed d (0 : n → F))
        = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, O x a * O x (a + u)) := by
  classical
  obtain ⟨P, hPsa, hPidem, hPsum, hPcomp⟩ :=
    exists_projective_dilation (d := d) (A := n → F) (X := X) (0 : n → F)
      (E := fun x e => fourierOf (O x) e * fourierOf (O x) e)
      (fun x e => fourierOf_posSemidef (hsa x) e)
      (fun x => sum_fourierOf_sq (O x) (hinv x))
  have hPVM : ∀ x, IsPVM (P x) := fun x =>
    { isSelfAdjoint := fun e => by rw [← Matrix.star_eq_conjTranspose, hPsa x e]
      idem := hPidem x
      sum_eq_one := hPsum x }
  refine ⟨fun x u => ∑ e : n → F, sgn (trDot u e) • P x e, ?_, ?_, ?_, ?_⟩
  · intro x u
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun e _ => by
      rw [Matrix.conjTranspose_smul, star_sgn, (hPVM x).isSelfAdjoint e]
  · intro x u u'
    have hstep : ∀ e : n → F,
        (sgn (trDot u e) • P x e) * ∑ e' : n → F, sgn (trDot u' e') • P x e'
          = sgn (trDot (u + u') e) • P x e := by
      intro e
      rw [Matrix.mul_sum]
      refine (Finset.sum_eq_single_of_mem e (mem_univ e) fun e' _ he' => ?_).trans ?_
      · rw [Matrix.smul_mul, Matrix.mul_smul, (hPVM x).orthogonal (Ne.symm he'), smul_zero,
          smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, (hPVM x).idem e, trDot_add_left, sgn_add]
    rw [Finset.sum_mul, Finset.sum_congr rfl fun e (_ : e ∈ univ) => hstep e]
  · intro x
    show ∑ e : n → F, sgn (trDot (0 : n → F) e) • P x e = 1
    rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
      rw [trDot_zero_left, sgn_zero, one_smul]]
    exact hPsum x
  · intro x u
    show (ancillaEmbed d (0 : n → F))ᴴ * ((∑ e : n → F, sgn (trDot u e) • P x e)
        * ancillaEmbed d (0 : n → F)) = _
    rw [Matrix.sum_mul, Matrix.mul_sum,
      Finset.sum_congr rfl fun e (_ : e ∈ univ) => by
        rw [Matrix.smul_mul, Matrix.mul_smul, hPcomp x e],
      sum_sgn_smul_fourierOf_sq]

/-! ## Adjoining an ancilla to one party -/

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The one-sided extension of a state**: an ancilla register in the fixed state `|a₀⟩`,
adjoined to the **first** party only. `expVec` splits an ancilla *pair* between the two parties;
this is the asymmetric extension `thm:linearity` needs, the exactly linear observables living on
the first party's enlarged space and the second party untouched. -/
def extVecA {A : Type*} [Fintype A] [DecidableEq A] (ψ : dA × dB → ℂ) (a₀ : A) :
    (dA × A) × dB → ℂ :=
  ((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ

section Ext

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem ancillaEmbed_kron_isometry (a₀ : A) :
    (((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ *
        ((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ)))
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    ancillaEmbed_isometry, Matrix.one_mul, Matrix.one_kronecker_one]

/-- The extension does not change the norm: the padding is an isometry. -/
theorem norm_evec_extVecA (ψ : dA × dB → ℂ) (a₀ : A) :
    ‖evec (extVecA ψ a₀)‖ = ‖evec ψ‖ :=
  norm_evec_mulVec_eq (ancillaEmbed_kron_isometry a₀) ψ

/-- **An operator with an inert ancilla commutes with the padding isometry.** -/
theorem kron_one_mul_ancillaEmbed (a₀ : A) (M : Matrix dA dA ℂ) :
    (M ⊗ₖ (1 : Matrix A A ℂ)) * ancillaEmbed dA a₀ = ancillaEmbed dA a₀ * M := by
  ext p j
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single_of_mem (j, a₀) (mem_univ _) fun q _ hq => by
      simp [ancillaEmbed, hq],
    Finset.sum_eq_single_of_mem p.1 (mem_univ _) fun k _ hk => by
      have hz : ancillaEmbed dA a₀ p k = 0 :=
        show (if p = (k, a₀) then (1 : ℂ) else 0) = 0 from
          if_neg fun h => hk (congrArg Prod.fst h).symm
      rw [hz, zero_mul]]
  by_cases h : p.2 = a₀
  · simp [ancillaEmbed, Matrix.one_apply, h, Prod.ext_iff]
  · simp [ancillaEmbed, h, Prod.ext_iff]

/-- The same, on the other side of the isometry. -/
theorem ancillaEmbed_conjTranspose_mul_kron_one (a₀ : A) (M : Matrix dA dA ℂ) :
    (ancillaEmbed dA a₀)ᴴ * (M ⊗ₖ (1 : Matrix A A ℂ)) = M * (ancillaEmbed dA a₀)ᴴ := by
  have h := congrArg Matrix.conjTranspose (kron_one_mul_ancillaEmbed a₀ (Mᴴ))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact h

/-- **Compressing a product whose right factor has an inert ancilla.** -/
theorem compress_mul_kron_one (a₀ : A) (M : Matrix dA dA ℂ) (Y : Matrix (dA × A) (dA × A) ℂ) :
    (ancillaEmbed dA a₀)ᴴ * (Y * (M ⊗ₖ (1 : Matrix A A ℂ)) * ancillaEmbed dA a₀)
      = (ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀) * M := by
  calc (ancillaEmbed dA a₀)ᴴ * (Y * (M ⊗ₖ (1 : Matrix A A ℂ)) * ancillaEmbed dA a₀)
      = (ancillaEmbed dA a₀)ᴴ * (Y * ((M ⊗ₖ (1 : Matrix A A ℂ)) * ancillaEmbed dA a₀)) := by
        rw [Matrix.mul_assoc Y]
    _ = (ancillaEmbed dA a₀)ᴴ * (Y * (ancillaEmbed dA a₀ * M)) := by
        rw [kron_one_mul_ancillaEmbed]
    _ = (ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀ * M) := by
        rw [Matrix.mul_assoc Y]
    _ = (ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀) * M := by
        rw [Matrix.mul_assoc ((ancillaEmbed dA a₀)ᴴ) (Y * ancillaEmbed dA a₀) M]

/-- **Compressing a product whose left factor has an inert ancilla.** -/
theorem compress_kron_one_mul (a₀ : A) (M : Matrix dA dA ℂ) (Y : Matrix (dA × A) (dA × A) ℂ) :
    (ancillaEmbed dA a₀)ᴴ * ((M ⊗ₖ (1 : Matrix A A ℂ)) * Y * ancillaEmbed dA a₀)
      = M * ((ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀)) := by
  calc (ancillaEmbed dA a₀)ᴴ * ((M ⊗ₖ (1 : Matrix A A ℂ)) * Y * ancillaEmbed dA a₀)
      = (ancillaEmbed dA a₀)ᴴ * ((M ⊗ₖ (1 : Matrix A A ℂ)) * (Y * ancillaEmbed dA a₀)) := by
        rw [Matrix.mul_assoc (M ⊗ₖ (1 : Matrix A A ℂ))]
    _ = (ancillaEmbed dA a₀)ᴴ * (M ⊗ₖ (1 : Matrix A A ℂ)) * (Y * ancillaEmbed dA a₀) := by
        rw [Matrix.mul_assoc ((ancillaEmbed dA a₀)ᴴ) (M ⊗ₖ (1 : Matrix A A ℂ))
          (Y * ancillaEmbed dA a₀)]
    _ = M * (ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀) := by
        rw [ancillaEmbed_conjTranspose_mul_kron_one]
    _ = M * ((ancillaEmbed dA a₀)ᴴ * (Y * ancillaEmbed dA a₀)) := by
        rw [Matrix.mul_assoc M ((ancillaEmbed dA a₀)ᴴ) (Y * ancillaEmbed dA a₀)]

/-- The conjugation identity: a quadratic form on the extended state is the quadratic form of the
**compressed** operator on the original one. -/
theorem qform_extVecA (ψ : dA × dB → ℂ) (a₀ : A) (M : Matrix (dA × A) (dA × A) ℂ) :
    qform (extVecA ψ a₀) (aOp M : Matrix ((dA × A) × dB) _ ℂ)
      = qform ψ (aOp ((ancillaEmbed dA a₀)ᴴ * (M * ancillaEmbed dA a₀))) := by
  rw [qform, qform, extVecA, dotProduct_mulVec_conj]
  congr 2
  rw [aOp, aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]

end Ext

/-! ## The distance between two unitaries, as a quadratic form -/

/-- **Expanding a squared distance.** For `A` and `B` with `AᴴA = BᴴB = 1` --- observables, or
products of them --- the state-dependent squared distance is `2` minus the two orders of the
overlap. Keeping both orders rather than combining them into a real part is what lets the
linearity estimate be matched term by term against its hypothesis. -/
theorem stateSqNorm_sub_of_isometry {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A B : Matrix dA dA ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    stateSqNorm ψ (A - B)
      = 2 - qform ψ (aOp (Aᴴ * B)) - qform ψ (aOp (Bᴴ * A)) := by
  have hexp : (A - B)ᴴ * (A - B) = (1 - Aᴴ * B) + (1 - Bᴴ * A) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hA, hB]
    abel
  rw [stateSqNorm, stateNorm]
  show snorm ψ (aOp (A - B) : Matrix (dA × dB) _ ℂ) ^ 2 = _
  have hone : qform ψ (aOp (1 : Matrix dA dA ℂ) : Matrix (dA × dB) _ ℂ) = 1 := by
    rw [aOp_one]
    exact qform_one _ hψ
  rw [snorm_sq_eq_qform, aOp_conjTranspose, ← aOp_mul, hexp, aOp_add, qform_add, aOp_sub,
    aOp_sub, qform_sub, qform_sub, hone]
  ring


/-! ## The theorem -/

section Main

variable {X : Type*} [Fintype X]

omit [DecidableEq F] in
/-- A product of two involutions is unitary, which is all the expansion of the hypothesis's
squared distance needs. -/
theorem conjTranspose_mul_self_of_involution {O : X → (n → F) → Matrix dA dA ℂ}
    (hsa : ∀ x a, (O x a)ᴴ = O x a) (hinv : ∀ x a, O x a * O x a = 1) (x : X) (a b : n → F) :
    (O x a * O x b)ᴴ * (O x a * O x b) = 1 := by
  rw [Matrix.conjTranspose_mul, hsa, hsa, Matrix.mul_assoc, ← Matrix.mul_assoc (O x a),
    hinv, Matrix.one_mul, hinv]

/-- **`thm:linearity`.** A family of observables that is approximately linear on average is, after
adjoining an ancilla register to the first party, *exactly* linear --- a representation of `F_q^n`
by commuting involutions, with the identity at `0` --- and close to the original family, with the
**same** average error: the linearity defect is transported, not merely bounded. -/
theorem exists_exactly_linear_close {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    (O : X → (n → F) → Matrix dA dA ℂ)
    (hsa : ∀ x a, (O x a)ᴴ = O x a) (hinv : ∀ x a, O x a * O x a = 1) :
    ∃ L : X → (n → F) → Matrix (dA × (n → F)) (dA × (n → F)) ℂ,
      (∀ x u, (L x u)ᴴ = L x u) ∧
      (∀ x u u', L x u * L x u' = L x (u + u')) ∧
      (∀ x, L x 0 = 1) ∧
      (∀ x, ∑ u : n → F, (Fintype.card (n → F) : ℝ)⁻¹ *
              stateSqNorm (extVecA ψ (0 : n → F)) (L x u - aOp (O x u))
            = ∑ a : n → F, ∑ b : n → F,
                ((Fintype.card (n → F) : ℝ)⁻¹ * (Fintype.card (n → F) : ℝ)⁻¹) *
                  stateSqNorm ψ (O x a * O x b - O x (a + b))) := by
  classical
  obtain ⟨L, hLsa, hLmul, hL0, hLcomp⟩ := exists_exactly_linear O hsa hinv
  refine ⟨L, hLsa, hLmul, hL0, fun x => ?_⟩
  set N : ℕ := Fintype.card (n → F) with hNdef
  have hNpos : 0 < N := Fintype.card_pos
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have hNC : ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  have hinvo : ∀ a b : n → F, a + b + b = a := fun a b => by
    rw [add_assoc, add_self_vec, add_zero]
  -- **the left-hand side, one term.** The compression of the exactly linear observable is the
  -- average `|V|^{-1} sum_a O^a O^{a+u}`, and the distance expands into the two orders of the
  -- overlap of that average with `O^u`.
  have hleft : ∀ u : n → F, stateSqNorm (extVecA ψ (0 : n → F)) (L x u - aOp (O x u))
      = 2 - (N : ℝ)⁻¹ * (∑ a : n → F, qform ψ (aOp (O x a * O x (a + u) * O x u)))
        - (N : ℝ)⁻¹ * ∑ a : n → F, qform ψ (aOp (O x u * O x a * O x (a + u))) := by
    intro u
    have hLu : (L x u)ᴴ * L x u = 1 := by rw [hLsa x u, hLmul, add_self_vec, hL0]
    have hOu : (aOp (O x u) : Matrix (dA × (n → F)) _ ℂ)ᴴ * aOp (O x u) = 1 := by
      rw [aOp_conjTranspose, ← aOp_mul, hsa x u, hinv x u, aOp_one]
    have hc1 : (ancillaEmbed dA (0 : n → F))ᴴ *
          (L x u * aOp (O x u) * ancillaEmbed dA (0 : n → F))
        = ((N : ℂ)⁻¹ • ∑ a : n → F, O x a * O x (a + u)) * O x u := by
      rw [aOp, compress_mul_kron_one, hLcomp x u]
    have hc2 : (ancillaEmbed dA (0 : n → F))ᴴ *
          (aOp (O x u) * L x u * ancillaEmbed dA (0 : n → F))
        = O x u * ((N : ℂ)⁻¹ • ∑ a : n → F, O x a * O x (a + u)) := by
      rw [aOp, compress_kron_one_mul, hLcomp x u]
    have hq1 : qform (extVecA ψ (0 : n → F))
          (aOp (L x u * aOp (O x u)) : Matrix ((dA × (n → F)) × dB) _ ℂ)
        = (N : ℝ)⁻¹ * ∑ a : n → F, qform ψ (aOp (O x a * O x (a + u) * O x u)) := by
      rw [qform_extVecA, hc1, Matrix.smul_mul, Finset.sum_mul, hNC, aOp_smul, qform_smul_real,
        aOp_sum, qform_sum]
    have hq2 : qform (extVecA ψ (0 : n → F))
          (aOp (aOp (O x u) * L x u) : Matrix ((dA × (n → F)) × dB) _ ℂ)
        = (N : ℝ)⁻¹ * ∑ a : n → F, qform ψ (aOp (O x u * O x a * O x (a + u))) := by
      rw [qform_extVecA, hc2, Matrix.mul_smul, Finset.mul_sum, hNC, aOp_smul, qform_smul_real,
        aOp_sum, qform_sum]
      exact congrArg _ (Finset.sum_congr rfl fun a _ => by rw [← Matrix.mul_assoc])
    rw [stateSqNorm_sub_of_isometry (by rw [norm_evec_extVecA]; exact hψ) hLu hOu, hLsa x u,
      aOp_conjTranspose, hsa x u, hq1, hq2]
  -- **the right-hand side, one term.**
  have hright : ∀ u a : n → F, stateSqNorm ψ (O x a * O x (a + u) - O x u)
      = 2 - qform ψ (aOp (O x (a + u) * O x a * O x u))
        - qform ψ (aOp (O x u * O x a * O x (a + u))) := by
    intro u a
    rw [stateSqNorm_sub_of_isometry hψ (conjTranspose_mul_self_of_involution hsa hinv x a (a + u))
        (by rw [hsa x u, hinv x u]),
      Matrix.conjTranspose_mul, hsa, hsa, hsa x u]
    congr 2
    rw [← Matrix.mul_assoc]
  -- splitting a constant off an average
  have hsplit : ∀ f g : (n → F) → ℝ,
      ∑ a : n → F, (N : ℝ)⁻¹ * (2 - f a - g a)
        = 2 - (N : ℝ)⁻¹ * (∑ a : n → F, f a) - (N : ℝ)⁻¹ * ∑ a : n → F, g a := by
    intro f g
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        show (N : ℝ)⁻¹ * (2 - f a - g a)
          = (N : ℝ)⁻¹ * 2 - (N : ℝ)⁻¹ * f a - (N : ℝ)⁻¹ * g a from by ring,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← hNdef, nsmul_eq_mul]
    simp only [← Finset.mul_sum]
    field_simp
  -- **the two sides agree one `u` at a time**, after reindexing the average by `a ↦ a + u`.
  have hkey : ∀ u : n → F, stateSqNorm (extVecA ψ (0 : n → F)) (L x u - aOp (O x u))
      = ∑ a : n → F, (N : ℝ)⁻¹ * stateSqNorm ψ (O x a * O x (a + u) - O x u) := by
    intro u
    have hre : ∑ a : n → F, qform ψ (aOp (O x (a + u) * O x a * O x u))
        = ∑ a : n → F, qform ψ (aOp (O x a * O x (a + u) * O x u)) :=
      Fintype.sum_equiv (Equiv.addRight u) _ _ fun a => by
        rw [Equiv.coe_addRight, hinvo a u]
    have hRHS : ∑ a : n → F, (N : ℝ)⁻¹ * stateSqNorm ψ (O x a * O x (a + u) - O x u)
        = 2 - (N : ℝ)⁻¹ * (∑ a : n → F, qform ψ (aOp (O x (a + u) * O x a * O x u)))
          - (N : ℝ)⁻¹ * ∑ a : n → F, qform ψ (aOp (O x u * O x a * O x (a + u))) := by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by rw [hright u a]]
      exact hsplit _ _
    rw [hleft u, hRHS, hre]
  -- and then one reindexing of the double average
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hkey u]]
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => Finset.mul_sum univ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Fintype.sum_equiv (Equiv.addLeft a) _ _ fun u => ?_
  rw [Equiv.coe_addLeft]
  show (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * stateSqNorm ψ (O x a * O x (a + u) - O x u))
    = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * stateSqNorm ψ (O x a * O x (a + u) - O x (a + (a + u)))
  rw [show a + (a + u) = u from by rw [← add_assoc, add_self_vec, zero_add], mul_assoc]

end Main

end MIPRE

end
