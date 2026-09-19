/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Commutation
import MIPRE.Foundations.Expanded
import MIPRE.Foundations.WeylEPR

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

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

set_option linter.unusedSectionVars false

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

end MIPRE.QLD

end
