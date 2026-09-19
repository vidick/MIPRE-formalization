/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Commutation
import MIPRE.Foundations.Expanded
import MIPRE.Foundations.WeylEPR
import MIPRE.Foundations.Expanded

/-!
# The expansion stage: the hatted point observables

Blueprint `lem:qld-expanded-points`, the commutation half. The expansion adjoins
`|EPR_q>^{(x) M}` to each player and replaces the point observable by

```
  W-hat^r(u) = W^r(u) (x) tau^W(r . ind_m(u)) ,
```

the strategy's own observable tensored with a generalized Pauli on the ancilla. The point of
doing so is a **single exact cancellation**:

* the strategy's two observables commute up to the sign `(-1)^{gamma(omega)}`
  (`signed_commutation`), at `O(eps)`;
* the two ancilla Pauli observables commute up to the *same* sign, **exactly** --- that is the
  twisted commutation relation of `def:generalized-pauli`, and the sign is the same because
  `gamma(omega)` *is* the form `tr(r_X ind(u_X) . r_Z ind(u_Z))` (`gam_eq_trDot`).

So the hatted observables commute up to nothing at all: the two signs multiply to one, and what
is left is the strategy's error with no sign in it. Without the ancillas the two bases would only
commute up to an error carrying `(-1)^gamma`, which does not improve with `eps`.

## What makes it cheap

Three facts, none of them about the Pauli test. The ancilla operator that survives the
cancellation is *unitary*, so it is invisible to the state-norm
(`norm_stateVec_kron_unitary`); what is left has an **inert** ancilla, so it has the same norm on
the expanded state as on the original one (`norm_stateVec_expVec_kron_one`); and the ancilla state
is a unit vector (`epr_unit`). The expansion therefore costs exactly the constant of
`lem:qld-obs-commutation` and nothing more.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

set_option linter.unusedSectionVars false

section Expansion

/-! ## The ancilla -/

/-- The ancilla register: `(C^q)^{(x) M}` with `M = 2^m`, indexed by `F_q^M` --- that is, by the
functions the low-degree encoding of `def:ld-encoding` already uses. -/
abbrev Anc (F : Type*) (m : ℕ) := (Fin m → Bool) → F

/-- The Weyl family of a basis. -/
def weylOf : Bas → Anc F m → Matrix (Anc F m) (Anc F m) ℂ
  | .X => wX
  | .Z => wZ

/-- The ancilla vector the expansion attaches to a point question: `r_W . ind_m(u_W)`. -/
def ancVec (ω : Omega F m) (W : Bas) : Anc F m := ω.r W • indVec (ω.pt W)

/-- **The test's sign is the Weyl form of the two ancilla vectors.** This is the identity the
cancellation runs on, and it is why the two signs are the same sign. -/
theorem gam_eq_trDot (ω : Omega F m) : gam ω = trDot (ancVec ω .X) (ancVec ω .Z) := by
  rw [gam, acGamma, trDot, ancVec, ancVec]
  congr 1
  rw [indPair, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by
    show ω.rX * ω.rZ * (indVec ω.uX y * indVec ω.uZ y)
      = (ω.rX • indVec ω.uX) y * (ω.rZ • indVec ω.uZ) y
    show ω.rX * ω.rZ * (indVec ω.uX y * indVec ω.uZ y)
      = (ω.rX * indVec ω.uX y) * (ω.rZ * indVec ω.uZ y)
    ring

theorem weylOf_isUnitary (W : Bas) (a : Anc F m) :
    (weylOf W a)ᴴ * weylOf W a = (1 : Matrix (Anc F m) (Anc F m) ℂ) := by
  cases W
  · exact wX_isUnitary a
  · exact wZ_isUnitary a

/-- The product that survives the cancellation is unitary. -/
theorem weylOf_prod_isUnitary (a b : Anc F m) :
    ((weylOf (F := F) (m := m) .X a * weylOf .Z b))ᴴ * (weylOf (F := F) (m := m) .X a
        * weylOf .Z b) = (1 : Matrix (Anc F m) (Anc F m) ℂ) := by
  calc ((weylOf (F := F) (m := m) .X a * weylOf .Z b))ᴴ
        * (weylOf (F := F) (m := m) .X a * weylOf .Z b)
      = (weylOf (F := F) (m := m) .Z b)ᴴ
        * (((weylOf (F := F) (m := m) .X a)ᴴ * weylOf .X a) * weylOf .Z b) := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
    _ = 1 := by rw [weylOf_isUnitary, Matrix.one_mul, weylOf_isUnitary]

/-! ## The hatted observables and the expanded state -/

/-- **The hatted point observable** `W-hat^r(u) = W^r(u) (x) tau^W(r . ind_m(u))`. -/
def hatObs (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA) (W : Bas)
    (c : Content F m) : Matrix (dA × Anc F m) (dA × Anc F m) ℂ :=
  ptObs hm MA W c ⊗ₖ weylOf W (ancVec c.omega W)

/-- **The expanded state** on the registers `A A' | B A''`: the strategy's state with a
maximally entangled pair adjoined, one half to each party. -/
def hatVec (ψ : dA × dB → ℂ) : (dA × Anc F m) × (dB × Anc F m) → ℂ :=
  expVec ψ (epr (F := F) (n := Fin m → Bool))

theorem norm_evec_epr : ‖evec (epr (F := F) (n := Fin m → Bool))‖ = 1 := by
  have h : ‖evec (epr (F := F) (n := Fin m → Bool))‖ ^ 2 = 1 := by
    rw [norm_evec_sq, epr_unit]
    norm_num
  nlinarith [norm_nonneg (evec (epr (F := F) (n := Fin m → Bool))), h]

/-! ## The cancellation -/

/-- **The two signs cancel.** The commutator of the hatted observables is the *signed* commutator
of the strategy's, tensored with a unitary: the ancilla's twisted commutation contributes exactly
the sign `(-1)^{gamma(omega)}` that the strategy's carries. -/
theorem hatObs_comm_eq (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA)
    (c : Content F m) :
    hatObs hm MA .X c * hatObs hm MA .Z c - hatObs hm MA .Z c * hatObs hm MA .X c
      = (ptObs hm MA .X c * ptObs hm MA .Z c
          - sgn (gam c.omega) • (ptObs hm MA .Z c * ptObs hm MA .X c))
        ⊗ₖ (weylOf .X (ancVec c.omega .X) * weylOf .Z (ancVec c.omega .Z)) := by
  have htw : weylOf (F := F) (m := m) .Z (ancVec c.omega .Z) * weylOf .X (ancVec c.omega .X)
      = sgn (gam c.omega)
        • (weylOf (F := F) (m := m) .X (ancVec c.omega .X) * weylOf .Z (ancVec c.omega .Z)) := by
    have h := wX_mul_wZ (ancVec c.omega .X) (ancVec c.omega .Z)
    rw [gam_eq_trDot]
    show wZ (ancVec c.omega .Z) * wX (ancVec c.omega .X)
      = sgn (trDot (ancVec c.omega .X) (ancVec c.omega .Z))
        • (wX (ancVec c.omega .X) * wZ (ancVec c.omega .Z))
    rw [h, smul_smul, sgn_mul_self, one_smul]
  rw [hatObs, hatObs, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, htw,
    Matrix.kronecker_smul, ← Matrix.smul_kronecker, ← sub_kronecker_right]

/-- **The hatted observables commute on the expanded state, with no sign**, at exactly the
constant of `lem:qld-obs-commutation`. -/
theorem norm_hatVec_hatObs_comm (hm : m ∣ Fintype.card F)
    (MA : Question F m → POVM (Answer F m d) dA) (ψ : dA × dB → ℂ) (c : Content F m) :
    ‖stateVec (hatVec (F := F) (m := m) ψ) (hatObs hm MA .X c * hatObs hm MA .Z c
        - hatObs hm MA .Z c * hatObs hm MA .X c)‖
      = ‖stateVec ψ (ptObs hm MA .X c * ptObs hm MA .Z c
          - sgn (gam c.omega) • (ptObs hm MA .Z c * ptObs hm MA .X c))‖ := by
  rw [hatObs_comm_eq, hatVec,
    norm_stateVec_kron_unitary _ _ (weylOf_prod_isUnitary (ancVec c.omega .X) (ancVec c.omega .Z)),
    norm_stateVec_expVec_kron_one _ norm_evec_epr]

theorem hatVec_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (hatVec (F := F) (m := m) ψ) ⬝ᵥ hatVec ψ = 1 := by
  rw [hatVec, expVec_unit hψ epr_unit]

/-- **The commutation half of `lem:qld-expanded-points`.** On the expanded state the `X`-side and
`Z`-side hatted point observables commute --- with *no* sign, on average over the verifier's
content, at the constant of `lem:qld-obs-commutation`. The sign the strategy carries is cancelled
identically by the one the ancilla carries. -/
theorem hatObs_commutation {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVec (hatVec (F := F) (m := m) ψ) (hatObs hm MA .X c * hatObs hm MA .Z c
          - hatObs hm MA .Z c * hatObs hm MA .X c)‖ ^ 2
      ≤ 57676416 * ε := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
    (signed_commutation (MB := MB) hψ hfail)
  rw [norm_hatVec_hatObs_comm]

/-! ## The hatted measurements, and their self-consistency

The other item of `lem:qld-expanded-points`. The hatted measurement is the **convolution** of the
strategy's point measurement with the ancilla's syndrome measurement: the product measurement,
coarse-grained by addition of the two field elements. Its self-consistency across the
re-bipartitioned parties comes from three things, and nothing else:

* item 1 of `lem:qld-win` for the strategy's factor;
* **perfect** self-consistency of the syndrome projectors across the two ancilla halves, which is
  the EPR stabilizer relation of `def:weyl-epr`;
* data processing for the convolution --- taken at the **Born level**, because the
  state-dependent distance has no data-processing inequality (NW19's own remark gives a
  counterexample; the paper's `fact:data-processing` is the consistency form).

So the whole estimate runs through Born probabilities and is converted to the distance exactly
once, at the end, by `xSqNorm_sum_le_two_mul`.
-/

/-- The syndrome measurement of the ancilla at a point question, as a POVM. -/
def synPOVM (W : Bas) (u : Point F m) : POVM F (Anc F m) :=
  (isPVM_syn (w := weylOf W) (by cases W; exacts [isWeylFamily_wX, isWeylFamily_wZ])
    (indVec u)).toPOVM

theorem synPOVM_mats (W : Bas) (u : Point F m) (a : F) :
    (((synPOVM W u).mats a).val) = syn (weylOf W) (indVec u) a := rfl

theorem weylOf_transpose (W : Bas) (a : Anc F m) : (weylOf W a)ᵀ = weylOf W a := by
  cases W
  · exact wX_transpose a
  · exact wZ_transpose a

/-- **The syndrome measurement is perfectly self-consistent on the maximally entangled state.**
This is the EPR stabilizer relation at the Born level, and it is the `1` that the expansion
contributes to the agreement probability. -/
theorem sum_bornProb_epr_synPOVM (W : Bas) (u : Point F m) :
    ∑ a : F, bornProb (epr (F := F) (n := Fin m → Bool)) (((synPOVM W u).mats a).val)
      (((synPOVM W u).mats a).val) = 1 := by
  classical
  have hsa : ∀ a : F, ((((synPOVM W u).mats a).val))ᴴ = (((synPOVM W u).mats a).val) := fun a => by
    rw [← Matrix.star_eq_conjTranspose, ((synPOVM W u).mats a).2]
  have hterm : ∀ a : F, bornProb (epr (F := F) (n := Fin m → Bool))
      (((synPOVM W u).mats a).val) (((synPOVM W u).mats a).val)
      = qform (epr (F := F) (n := Fin m → Bool))
          (aOp (((synPOVM W u).mats a).val) : Matrix ((Anc F m) × (Anc F m)) _ ℂ) := by
    intro a
    have htr : stateVec (epr (F := F) (n := Fin m → Bool)) (((synPOVM W u).mats a).val)
        = stateVecB epr (((synPOVM W u).mats a).val) := by
      rw [synPOVM_mats]
      exact stateVec_epr_syn (weylOf_transpose W) (indVec u) a
    have hinner := inner_stateVec_stateVecB (epr (F := F) (n := Fin m → Bool)) (hsa a)
      (((synPOVM W u).mats a).val)
    rw [← htr] at hinner
    rw [bornProb, ← hinner,
      show (inner ℂ (stateVec (epr (F := F) (n := Fin m → Bool)) (((synPOVM W u).mats a).val))
            (stateVec epr (((synPOVM W u).mats a).val)) : ℂ).re
          = ‖stateVec (epr (F := F) (n := Fin m → Bool)) (((synPOVM W u).mats a).val)‖ ^ 2 from by
        rw [← RCLike.re_to_complex]
        exact inner_self_eq_norm_sq _,
      norm_stateVec_eq_snorm, snorm_sq_eq_qform]
    congr 1
    rw [aOp_conjTranspose, ← aOp_mul, hsa a, synPOVM_mats,
      (isPVM_syn (w := weylOf W) (by cases W; exacts [isWeylFamily_wX, isWeylFamily_wZ])
        (indVec u)).idem a]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hterm a, ← qform_sum]
  rw [show (∑ a : F, (aOp (((synPOVM W u).mats a).val)
      : Matrix ((Anc F m) × (Anc F m)) ((Anc F m) × (Anc F m)) ℂ)) = 1 from by
    rw [← aOp_sum, show (∑ a : F, (((synPOVM W u).mats a).val)) = 1 from by
      rw [← AddSubmonoidClass.coe_finsetSum, (synPOVM W u).normalized]
      rfl]
    exact aOp_one]
  exact qform_one _ norm_evec_epr

/-! ### The hatted measurement -/

/-- The point measurement read as a field element --- the same definition for either player. -/
def ptValPOVM {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) : POVM F d' :=
  (M (c.question hm (.point W))).map rdVal

/-- **The hatted point measurement**: the product of the strategy's point measurement with the
ancilla's syndrome measurement, coarse-grained by adding the two field elements. That convolution
is the paper's `M-hat^{(Point,W),u}_a = sum_{a' + a'' = a} M_{a'} (x) tau^{W,u}_{a''}`. -/
def hatPOVM {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) :
    POVM F (d' × Anc F m) :=
  ((ptValPOVM hm M W c).kron (synPOVM W (c.omega.pt W))).map fun p => p.1 + p.2

/-- **The hatted measurements are cross-party consistent**, at one content: twice the conditional
failure of the `(Point, W)` subtest, and nothing for the ancilla. The three inputs meet here --- the
strategy's consistency, the ancilla's *perfect* consistency, and Born-level data processing for the
convolution. -/
theorem sum_xSqNorm_hatPOVM_le {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    (hψ : star ψ ⬝ᵥ ψ = 1) (W : Bas) (c : Content F m) :
    ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (((hatPOVM hm MA W c).mats a).val)
        (((hatPOVM hm MB W c).mats a).val)
      ≤ 2 * condFail (qldGame hm) ψ MA MB (c.question hm (.point W))
          (c.question hm (.point W)) := by
  classical
  -- the agreement of the product measurement factorizes, and the ancilla factor is one
  have hfac : ∀ p : F × F, bornProb (hatVec (F := F) (m := m) ψ)
      ((((ptValPOVM hm MA W c).kron (synPOVM W (c.omega.pt W))).mats p).val)
      ((((ptValPOVM hm MB W c).kron (synPOVM W (c.omega.pt W))).mats p).val)
      = bornProb ψ (((ptValPOVM hm MA W c).mats p.1).val)
          (((ptValPOVM hm MB W c).mats p.1).val)
        * bornProb (epr (F := F) (n := Fin m → Bool))
          (((synPOVM W (c.omega.pt W)).mats p.2).val)
          (((synPOVM W (c.omega.pt W)).mats p.2).val) := by
    intro p
    rw [POVM.kron_mats, POVM.kron_mats, hatVec]
    exact bornProb_expVec_kron _ _ ((synPOVM W (c.omega.pt W)).posSemidef p.2)
      ((synPOVM W (c.omega.pt W)).posSemidef p.2)
  have hprod : ∑ p : F × F, bornProb (hatVec (F := F) (m := m) ψ)
      ((((ptValPOVM hm MA W c).kron (synPOVM W (c.omega.pt W))).mats p).val)
      ((((ptValPOVM hm MB W c).kron (synPOVM W (c.omega.pt W))).mats p).val)
      = ∑ a : F, bornProb ψ (((ptValPOVM hm MA W c).mats a).val)
          (((ptValPOVM hm MB W c).mats a).val) := by
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hfac p,
      sum_prod_mul
        (fun a : F => bornProb ψ (((ptValPOVM hm MA W c).mats a).val)
          (((ptValPOVM hm MB W c).mats a).val))
        (fun a : F => bornProb (epr (F := F) (n := Fin m → Bool))
          (((synPOVM W (c.omega.pt W)).mats a).val)
          (((synPOVM W (c.omega.pt W)).mats a).val)),
      sum_bornProb_epr_synPOVM, mul_one]
  -- data processing for the convolution
  have hdp := sum_bornProb_le_map (hatVec (F := F) (m := m) ψ)
    ((ptValPOVM hm MA W c).kron (synPOVM W (c.omega.pt W)))
    ((ptValPOVM hm MB W c).kron (synPOVM W (c.omega.pt W))) (fun p : F × F => p.1 + p.2)
  rw [hprod] at hdp
  -- the strategy's own consistency, at the Born level
  have hcons : 1 - ∑ a : F, bornProb ψ (((ptValPOVM hm MA W c).mats a).val)
      (((ptValPOVM hm MB W c).mats a).val)
      ≤ condFail (qldGame hm) ψ MA MB (c.question hm (.point W))
          (c.question hm (.point W)) := by
    refine one_sub_sum_bornProb_le_condFail (G := qldGame hm) (ψ := ψ) (MA := MA) (MB := MB)
      rdVal rdVal fun a b h => ?_
    have hs := (of_accepts h).2.2
    rw [subtests, if_pos rfl] at hs
    exact congrArg rdVal (of_decide_eq_true hs)
  refine le_trans (xSqNorm_sum_le_two_mul (hatVec_unit hψ) _ _) ?_
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [hatPOVM, hatPOVM]
  linarith

/-- **The self-consistency half of `lem:qld-expanded-points`.** On average over the verifier's
content, the two players' hatted point measurements agree across the re-bipartitioned parties at
`172 eps` --- the constant of item 1 of `lem:qld-win`, with the expansion contributing nothing. -/
theorem hatPOVM_consistency {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (W : Bas) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (((hatPOVM hm MA W c).mats a).val)
          (((hatPOVM hm MB W c).mats a).val)
      ≤ 172 * ε := by
  classical
  refine le_trans (Finset.sum_le_sum fun c (_ : c ∈ univ) =>
    mul_le_mul_of_nonneg_left (sum_xSqNorm_hatPOVM_le (MB := MB) hψ W c) (by positivity)) ?_
  have heq : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        (2 * condFail (qldGame hm) ψ MA MB
          (c.question hm (.point W)) (c.question hm (.point W)))
      = 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          condFail (qldGame hm) ψ MA MB
            (c.question hm (.point W)) (c.question hm (.point W)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [heq, show (172 : ℝ) * ε = 2 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (subtest_le hψ hfail (adj_self' (.point W)) univ) (by norm_num)

/-- **`lem:qld-expanded-points`**: both items, on the expanded state. The measurements are the
hatted ones; they are cross-party consistent at `172 eps`, and their `X`-side and `Z`-side
observables commute at `57676416 eps` with no sign. -/
theorem expanded_points {ψ : dA × dB → ℂ} {hm : m ∣ Fintype.card F}
    {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
    {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    (∀ W : Bas, ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ a : F, xSqNorm (hatVec (F := F) (m := m) ψ) (((hatPOVM hm MA W c).mats a).val)
          (((hatPOVM hm MB W c).mats a).val) ≤ 172 * ε)
      ∧ ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ‖stateVec (hatVec (F := F) (m := m) ψ) (hatObs hm MA .X c * hatObs hm MA .Z c
            - hatObs hm MA .Z c * hatObs hm MA .X c)‖ ^ 2 ≤ 57676416 * ε :=
  ⟨fun W => hatPOVM_consistency (MB := MB) hψ hfail W, hatObs_commutation (MB := MB) hψ hfail⟩

end Expansion

end MIPRE.QLD

end
