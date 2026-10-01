/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Commutation
public import MIPRE.Background.LIDT.Adapter.Geometry
public import MIPRE.Foundations.Expanded
public import MIPRE.Foundations.Introspection.RegisterModel
public import MIPRE.Foundations.LowDegree.LineRestrict
public import MIPRE.Foundations.ModelStrategy
public import MIPRE.Foundations.WeylEPR

@[expose] public section

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
(`BipartiteModel.stateNorm_mul_of_isometry`); what is left has an **inert** ancilla, so it has the
same norm on the expanded state as on the original one
(`BipartiteModel.stateSqNorm_expand_smulKron_one`); and the ancilla state is a unit vector
(`Introspection.registerEPR_norm`). The expansion therefore costs exactly the constant of
`lem:qld-obs-commutation` and nothing more.

## In a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The strategy is a model
`M : BipartiteModel 𝒞 𝒜 ℬ` with `‖M.ψ‖ = 1` and two families of POVMs in the players' ordered
algebras, and the expanded state `ψ ⊗ |EPR>` of the matrix route is the **register model**
`M.reg (Anc F m)` (`MIPRE/Foundations/Introspection/RegisterModel.lean`): the EPR register on
`Anc F m`, one half (`A'`) held by the first player, whose operators become the matrices
`Matrix (Anc F m) (Anc F m) 𝒜`, and the other (`A''`) by the second, `Matrix (Anc F m) (Anc F m) ℬ`.
A strategy's operator `X` tensored with an ancilla matrix `P` is `smulKron X P` (register outer),
so the hatted observable is `smulKron (ptObs …) (weylOf …)` and the hatted measurements are
convolutions of the strategy's POVM with the ancilla's syndrome measurement, POVMs in the
register's matrices (`kronIn`, then `POVMIn.map`). The Born probability of a product measurement
factorizes (`BipartiteModel.bornProb_expand_smulKron`), and the ancilla's factor is the matrix
computation on the EPR vector it was before (`sum_bornProb_epr_synOfPOVM`), so every constant is
kept. On a unit vector `ψ : dA × dB → ℂ` the statements are read at the tensor-product model
`BipartiteModel.tensor ψ` with the families `POVM.toIn`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

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

/-- **The hatted point observable** `W-hat^r(u) = W^r(u) (x) tau^W(r . ind_m(u))`: the strategy's
observable, an element of the player's algebra `R`, tensored with the ancilla's generalized Pauli,
as a matrix over `R` on the ancilla register (register outer). -/
def hatObs {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (c : Content F m) : Matrix (Anc F m) (Anc F m) R :=
  smulKron (ptObs hm P W c) (weylOf W (ancVec c.omega W))

theorem norm_evec_epr : ‖evec (epr (F := F) (n := Fin m → Bool))‖ = 1 := by
  have h : ‖evec (epr (F := F) (n := Fin m → Bool))‖ ^ 2 = 1 := by
    rw [norm_evec_sq, epr_unit]
    norm_num
  nlinarith [norm_nonneg (evec (epr (F := F) (n := Fin m → Bool))), h]

/-- **The expanded state is a unit vector** when the strategy's is: the state of the register
model `M.reg (Anc F m)` is `ψ ⊗ |EPR>`, the model form of the matrix route's `hatVec ψ`. -/
theorem hatVec_unit {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1) :
    ‖(M.reg (Anc F m)).ψ‖ = 1 := by
  rw [BipartiteModel.norm_reg_ψ, hM]

/-! ## The cancellation -/

private theorem smulKron_smul_left_hat {R α : Type*} [Ring R] [Algebra ℂ R] (c : ℂ) (X : R)
    (P : Matrix α α ℂ) : smulKron (c • X) P = c • smulKron X P := by
  ext a b
  simp only [smulKron_apply, Matrix.smul_apply]
  exact smul_comm (P a b) c X

/-- **The two signs cancel.** The commutator of the hatted observables is the *signed* commutator
of the strategy's, tensored with a unitary: the ancilla's twisted commutation contributes exactly
the sign `(-1)^{gamma(omega)}` that the strategy's carries. -/
theorem hatObs_comm_eq {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R]
    [StarOrderedRing R] (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R)
    (c : Content F m) :
    hatObs hm P .X c * hatObs hm P .Z c - hatObs hm P .Z c * hatObs hm P .X c
      = smulKron (ptObs hm P .X c * ptObs hm P .Z c
          - sgn (gam c.omega) • (ptObs hm P .Z c * ptObs hm P .X c))
        (weylOf .X (ancVec c.omega .X) * weylOf .Z (ancVec c.omega .Z)) := by
  have htw : weylOf (F := F) (m := m) .Z (ancVec c.omega .Z) * weylOf .X (ancVec c.omega .X)
      = sgn (gam c.omega)
        • (weylOf (F := F) (m := m) .X (ancVec c.omega .X) * weylOf .Z (ancVec c.omega .Z)) := by
    have h := wX_mul_wZ (ancVec c.omega .X) (ancVec c.omega .Z)
    rw [gam_eq_trDot]
    show wZ (ancVec c.omega .Z) * wX (ancVec c.omega .X)
      = sgn (trDot (ancVec c.omega .X) (ancVec c.omega .Z))
        • (wX (ancVec c.omega .X) * wZ (ancVec c.omega .Z))
    rw [h, smul_smul, sgn_mul_self, one_smul]
  rw [hatObs, hatObs, smulKron_mul, smulKron_mul, htw, smulKron_smul_right,
    ← smulKron_smul_left_hat, smulKron_sub_left]

/-- **The hatted observables commute on the expanded state, with no sign**, at exactly the
constant of `lem:qld-obs-commutation`: the state norm of their commutator on the register model is
the state norm of the strategy's signed commutator on the model. -/
theorem norm_hatVec_hatObs_comm [StarModule ℂ 𝒜] (hm : m ∣ Fintype.card F)
    (PA : Question F m → POVMIn (Answer F m d) 𝒜) (M : BipartiteModel 𝒞 𝒜 ℬ) (c : Content F m) :
    (M.reg (Anc F m)).stateSqNorm (hatObs hm PA .X c * hatObs hm PA .Z c
        - hatObs hm PA .Z c * hatObs hm PA .X c)
      = M.stateSqNorm (ptObs hm PA .X c * ptObs hm PA .Z c
          - sgn (gam c.omega) • (ptObs hm PA .Z c * ptObs hm PA .X c)) := by
  set D := ptObs hm PA .X c * ptObs hm PA .Z c
    - sgn (gam c.omega) • (ptObs hm PA .Z c * ptObs hm PA .X c) with hD
  set U := weylOf (F := F) (m := m) .X (ancVec c.omega .X) * weylOf .Z (ancVec c.omega .Z)
    with hU
  have hfac : smulKron D U = smulKron (1 : 𝒜) U * smulKron D 1 := by
    rw [smulKron_mul, one_mul, Matrix.mul_one]
  have hiso : star (smulKron (1 : 𝒜) U) * smulKron (1 : 𝒜) U = 1 := by
    rw [star_smulKron, star_one, smulKron_mul, one_mul, hU,
      weylOf_prod_isUnitary (ancVec c.omega .X) (ancVec c.omega .Z), smulKron_one_one]
  rw [hatObs_comm_eq, ← hD, ← hU, hfac, BipartiteModel.stateSqNorm,
    (M.reg (Anc F m)).stateNorm_mul_of_isometry hiso, ← BipartiteModel.stateSqNorm,
    BipartiteModel.stateSqNorm_expand_smulKron_one, Introspection.registerEPR_norm, one_pow,
    one_mul]

/-- **The commutation half of `lem:qld-expanded-points`.** On the expanded state the `X`-side and
`Z`-side hatted point observables commute --- with *no* sign, on average over the verifier's
content, at the constant of `lem:qld-obs-commutation`. The sign the strategy carries is cancelled
identically by the one the ancilla carries. The first player's measurements are projective, as
`signed_commutation` needs. -/
theorem hatObs_commutation [StarModule ℂ 𝒜] {hm : m ∣ Fintype.card F}
    {M : BipartiteModel 𝒞 𝒜 ℬ} {PA : Question F m → POVMIn (Answer F m d) 𝒜}
    {PB : Question F m → POVMIn (Answer F m d) ℬ} {ε : ℝ} (hM : ‖M.ψ‖ = 1)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        (M.reg (Anc F m)).stateSqNorm (hatObs hm PA .X c * hatObs hm PA .Z c
          - hatObs hm PA .Z c * hatObs hm PA .X c)
      ≤ 57676416 * ε := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
    (signed_commutation hM hPA hfail)
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
once, at the end, by `BipartiteModel.xSqNorm_sum_le_two_mul`.
-/

theorem isWeylFamily_weylOf (W : Bas) : IsWeylFamily (weylOf (F := F) (m := m) W) := by
  cases W
  exacts [isWeylFamily_wX, isWeylFamily_wZ]

/-- **The ancilla's basis measurement, coarse-grained by an arbitrary label.** Measuring all `M`
qudits in the basis `W` gives an outcome `h`; this measurement reports `φ h` instead. At
`φ h = ⟨h, ind_m(u)⟩` it is the syndrome measurement of a point question, and at ``the restriction
of `g_h` to a line'' it is the line measurement of the expansion stage. -/
def synOfPOVM {C : Type*} [Fintype C] [DecidableEq C] (W : Bas) (φ : Anc F m → C) :
    POVM C (Anc F m) :=
  (isPVM_synOf (w := weylOf W) (isWeylFamily_weylOf W) φ).toPOVM

theorem synOfPOVM_mats {C : Type*} [Fintype C] [DecidableEq C] (W : Bas) (φ : Anc F m → C)
    (o : C) : (((synOfPOVM W φ).mats o).val) = synOf (weylOf W) φ o := rfl

/-- The coarse-grained basis measurement is projective. -/
theorem isPVM_synOfPOVM {C : Type*} [Fintype C] [DecidableEq C] (W : Bas) (φ : Anc F m → C) :
    IsPVM fun o => (((synOfPOVM W φ).mats o).val) :=
  isPVM_synOf (isWeylFamily_weylOf W) φ

/-- The syndrome measurement of the ancilla at a point question, as a POVM. -/
def synPOVM (W : Bas) (u : Point F m) : POVM F (Anc F m) :=
  synOfPOVM W fun h => dotF h (indVec u)

theorem synPOVM_mats (W : Bas) (u : Point F m) (a : F) :
    (((synPOVM W u).mats a).val) = syn (weylOf W) (indVec u) a := rfl

/-- The syndrome measurement is projective. -/
theorem isPVM_synPOVM (W : Bas) (u : Point F m) :
    IsPVM fun a : F => (((synPOVM (F := F) (m := m) W u).mats a).val) :=
  isPVM_synOfPOVM W _

theorem weylOf_transpose (W : Bas) (a : Anc F m) : (weylOf W a)ᵀ = weylOf W a := by
  cases W
  · exact wX_transpose a
  · exact wZ_transpose a

/-- **The coarse-grained basis measurement is perfectly self-consistent on the maximally entangled
state.** This is the EPR stabilizer relation at the Born level, and it is the `1` that the
expansion contributes to every agreement probability --- exactly `1`, not `1 - O(eps)`. -/
theorem sum_bornProb_epr_synOfPOVM {C : Type*} [Fintype C] [DecidableEq C] (W : Bas)
    (φ : Anc F m → C) :
    ∑ o : C, bornProb (epr (F := F) (n := Fin m → Bool)) (((synOfPOVM W φ).mats o).val)
      (((synOfPOVM W φ).mats o).val) = 1 := by
  classical
  have hsa : ∀ o : C, ((((synOfPOVM W φ).mats o).val))ᴴ = (((synOfPOVM W φ).mats o).val) :=
    fun o => by rw [← Matrix.star_eq_conjTranspose, ((synOfPOVM W φ).mats o).2]
  have hterm : ∀ o : C, bornProb (epr (F := F) (n := Fin m → Bool))
      (((synOfPOVM W φ).mats o).val) (((synOfPOVM W φ).mats o).val)
      = qform (epr (F := F) (n := Fin m → Bool))
          (aOp (((synOfPOVM W φ).mats o).val) : Matrix ((Anc F m) × (Anc F m)) _ ℂ) := by
    intro o
    have htr : stateVec (epr (F := F) (n := Fin m → Bool)) (((synOfPOVM W φ).mats o).val)
        = stateVecB epr (((synOfPOVM W φ).mats o).val) := by
      rw [synOfPOVM_mats]
      exact stateVec_epr_synOf (weylOf_transpose W) φ o
    have hinner := inner_stateVec_stateVecB (epr (F := F) (n := Fin m → Bool)) (hsa o)
      (((synOfPOVM W φ).mats o).val)
    rw [← htr] at hinner
    rw [bornProb, ← hinner,
      show (inner ℂ (stateVec (epr (F := F) (n := Fin m → Bool)) (((synOfPOVM W φ).mats o).val))
            (stateVec epr (((synOfPOVM W φ).mats o).val)) : ℂ).re
          = ‖stateVec (epr (F := F) (n := Fin m → Bool)) (((synOfPOVM W φ).mats o).val)‖ ^ 2 from by
        rw [← RCLike.re_to_complex]
        exact inner_self_eq_norm_sq _,
      norm_stateVec_eq_snorm, snorm_sq_eq_qform]
    congr 1
    rw [aOp_conjTranspose, ← aOp_mul, hsa o, (isPVM_synOfPOVM W φ).idem o]
  rw [Finset.sum_congr rfl fun o (_ : o ∈ univ) => hterm o, ← qform_sum]
  rw [show (∑ o : C, (aOp (((synOfPOVM W φ).mats o).val)
      : Matrix ((Anc F m) × (Anc F m)) ((Anc F m) × (Anc F m)) ℂ)) = 1 from by
    rw [← aOp_sum, show (∑ o : C, (((synOfPOVM W φ).mats o).val)) = 1 from by
      rw [← AddSubmonoidClass.coe_finsetSum, (synOfPOVM W φ).normalized]
      rfl]
    exact aOp_one]
  exact qform_one _ norm_evec_epr

/-- **The syndrome measurement is perfectly self-consistent on the maximally entangled state.** -/
theorem sum_bornProb_epr_synPOVM (W : Bas) (u : Point F m) :
    ∑ a : F, bornProb (epr (F := F) (n := Fin m → Bool)) (((synPOVM W u).mats a).val)
      (((synPOVM W u).mats a).val) = 1 :=
  sum_bornProb_epr_synOfPOVM W _

/-! ### A POVM of the player times a projective measurement of the register -/

section KronIn

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
  [StarOrderedRing R] [StarProper R] {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
  [DecidableEq α]

/-- **A POVM in a player's algebra times a projective measurement of a register**, as a POVM in
the register's matrices over the algebra (register outer): the element at `(i, k)` is
`smulKron (P.op i) Q_k`. The model form of `POVM.kron` when the second factor is a projective
measurement of a finite register; its elements are then projections, which is what makes the
products nonnegative in the order of the matrices over `R` (`smulKron_nonneg_of_proj`). -/
def kronIn (P : POVMIn ι R) (Q : POVM κ α) (hQ : IsPVM fun k => ((Q.mats k).val)) :
    POVMIn (ι × κ) (Matrix α α R) where
  mats p := ⟨smulKron (P.op p.1) ((Q.mats p.2).val), by
    rw [selfAdjoint.mem_iff, star_smulKron, P.star_op, ← Matrix.star_eq_conjTranspose,
      (Q.mats p.2).2]⟩
  nonneg p := Subtype.coe_le_coe.mp (smulKron_nonneg_of_proj (P.op_nonneg p.1)
    (by rw [← Matrix.star_eq_conjTranspose, (Q.mats p.2).2]; exact hQ.idem p.2))
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    change (∑ p : ι × κ, smulKron (P.op p.1) ((Q.mats p.2).val)) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← smulKron_sum_right, POVM.sum_val, ← smulKron_sum_left, P.sum_op,
      smulKron_one_one]

theorem kronIn_op (P : POVMIn ι R) (Q : POVM κ α) (hQ : IsPVM fun k => ((Q.mats k).val))
    (p : ι × κ) : (kronIn P Q hQ).op p = smulKron (P.op p.1) ((Q.mats p.2).val) := rfl

/-- **A product of projective measurements is projective.** -/
theorem isPVMIn_kronIn {P : POVMIn ι R} (hP : IsPVMIn P.op) (Q : POVM κ α)
    (hQ : IsPVM fun k => ((Q.mats k).val)) : IsPVMIn (kronIn P Q hQ).op := by
  classical
  exact hP.smulKron hQ.toIn

/-- The product depends on the register's measurement only through its elements. -/
theorem kronIn_congr (P : POVMIn ι R) {Q Q' : POVM κ α} (h : Q = Q')
    (hQ : IsPVM fun k => ((Q.mats k).val)) (hQ' : IsPVM fun k => ((Q'.mats k).val)) :
    kronIn P Q hQ = kronIn P Q' hQ' := by
  subst h
  rfl

/-- **Relabelling the two factors is relabelling the product.** -/
theorem kronIn_map {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    (P : POVMIn ι R) (Q : POVM κ α) (hQ : IsPVM fun k => ((Q.mats k).val)) (f : ι → ι')
    (g : κ → κ') (hQ' : IsPVM fun k => (((Q.map g).mats k).val)) :
    kronIn (P.map f) (Q.map g) hQ' = (kronIn P Q hQ).map fun p => (f p.1, g p.2) := by
  classical
  refine POVMIn.ext' fun b => ?_
  have hfil : (Finset.univ.filter fun p : ι × κ => (f p.1, g p.2) = b)
      = (Finset.univ.filter fun i => f i = b.1) ×ˢ (Finset.univ.filter fun j => g j = b.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Prod.ext_iff]
  rw [kronIn_op, POVMIn.map_op, POVMIn.map_op, POVM.map_mats, hfil, Finset.sum_product,
    smulKron_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smulKron_sum_right]
  rfl

end KronIn

/-! ### The hatted measurement -/

/-- The point measurement read as a field element --- the same definition for either player. -/
def ptValPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (c : Content F m) : POVMIn F R :=
  (P (c.question hm (.point W))).map rdVal

/-- **The hatted point measurement**: the product of the strategy's point measurement with the
ancilla's syndrome measurement, coarse-grained by adding the two field elements. That convolution
is the paper's `M-hat^{(Point,W),u}_a = sum_{a' + a'' = a} M_{a'} (x) tau^{W,u}_{a''}`, a POVM in
the register's matrices over the player's algebra. -/
def hatPOVM {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [PartialOrder R]
    [StarOrderedRing R] [StarProper R] (hm : m ∣ Fintype.card F)
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (c : Content F m) :
    POVMIn F (Matrix (Anc F m) (Anc F m) R) :=
  (kronIn (ptValPOVM hm P W c) (synPOVM W (c.omega.pt W)) (isPVM_synPOVM W _)).map
    fun p => p.1 + p.2

/-- **The hatted measurements are cross-party consistent**, at one content: twice the conditional
failure of the `(Point, W)` subtest, and nothing for the ancilla. The three inputs meet here --- the
strategy's consistency, the ancilla's *perfect* consistency, and Born-level data processing for the
convolution. -/
theorem sum_xSqNorm_hatPOVM_le [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    (hM : ‖M.ψ‖ = 1) (W : Bas) (c : Content F m) :
    ∑ a : F, (M.reg (Anc F m)).xSqNorm ((hatPOVM hm PA W c).op a) ((hatPOVM hm PB W c).op a)
      ≤ 2 * M.condFail (qldGame hm) PA PB (c.question hm (.point W))
          (c.question hm (.point W)) := by
  classical
  -- the agreement of the product measurement factorizes, and the ancilla factor is one
  have hfac : ∀ p : F × F, (M.reg (Anc F m)).bornProb
      ((kronIn (ptValPOVM hm PA W c) (synPOVM W (c.omega.pt W)) (isPVM_synPOVM W _)).op p)
      ((kronIn (ptValPOVM hm PB W c) (synPOVM W (c.omega.pt W)) (isPVM_synPOVM W _)).op p)
      = M.bornProb ((ptValPOVM hm PA W c).op p.1) ((ptValPOVM hm PB W c).op p.1)
        * bornProb (epr (F := F) (n := Fin m → Bool))
          (((synPOVM W (c.omega.pt W)).mats p.2).val)
          (((synPOVM W (c.omega.pt W)).mats p.2).val) := by
    intro p
    rw [kronIn_op, kronIn_op, BipartiteModel.bornProb_expand_smulKron _ _ _ _
      ((synPOVM W (c.omega.pt W)).posSemidef p.2) ((synPOVM W (c.omega.pt W)).posSemidef p.2),
      mul_comm]
    rfl
  have hprod : ∑ p : F × F, (M.reg (Anc F m)).bornProb
      ((kronIn (ptValPOVM hm PA W c) (synPOVM W (c.omega.pt W)) (isPVM_synPOVM W _)).op p)
      ((kronIn (ptValPOVM hm PB W c) (synPOVM W (c.omega.pt W)) (isPVM_synPOVM W _)).op p)
      = ∑ a : F, M.bornProb ((ptValPOVM hm PA W c).op a) ((ptValPOVM hm PB W c).op a) := by
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hfac p,
      sum_prod_mul
        (fun a : F => M.bornProb ((ptValPOVM hm PA W c).op a) ((ptValPOVM hm PB W c).op a))
        (fun a : F => bornProb (epr (F := F) (n := Fin m → Bool))
          (((synPOVM W (c.omega.pt W)).mats a).val)
          (((synPOVM W (c.omega.pt W)).mats a).val)),
      sum_bornProb_epr_synPOVM, mul_one]
  -- data processing for the convolution
  have hdp := (M.reg (Anc F m)).sum_bornProb_le_map
    (kronIn (ptValPOVM hm PA W c) (synPOVM W (c.omega.pt W)) (isPVM_synPOVM W _))
    (kronIn (ptValPOVM hm PB W c) (synPOVM W (c.omega.pt W)) (isPVM_synPOVM W _))
    (fun p : F × F => p.1 + p.2)
  rw [hprod] at hdp
  -- the strategy's own consistency, at the Born level
  have hcons : 1 - ∑ a : F, M.bornProb ((ptValPOVM hm PA W c).op a)
      ((ptValPOVM hm PB W c).op a)
      ≤ M.condFail (qldGame hm) PA PB (c.question hm (.point W))
          (c.question hm (.point W)) := by
    refine M.one_sub_sum_bornProb_le_condFail (G := qldGame hm) (MA := PA) (MB := PB)
      rdVal rdVal fun a b h => ?_
    have hs := (of_accepts h).2.2
    rw [subtests, if_pos rfl] at hs
    exact congrArg rdVal (of_decide_eq_true hs)
  refine le_trans ((M.reg (Anc F m)).xSqNorm_sum_le_two_mul (hatVec_unit hM) _ _) ?_
  rw [hatPOVM, hatPOVM]
  linarith

/-- **The self-consistency half of `lem:qld-expanded-points`.** On average over the verifier's
content, the two players' hatted point measurements agree across the re-bipartitioned parties at
`172 eps` --- the constant of item 1 of `lem:qld-win`, with the expansion contributing nothing. -/
theorem hatPOVM_consistency [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    {ε : ℝ} (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ a : F, (M.reg (Anc F m)).xSqNorm ((hatPOVM hm PA W c).op a)
          ((hatPOVM hm PB W c).op a)
      ≤ 172 * ε := by
  classical
  refine le_trans (Finset.sum_le_sum fun c (_ : c ∈ univ) =>
    mul_le_mul_of_nonneg_left (sum_xSqNorm_hatPOVM_le (PB := PB) hM W c) (by positivity)) ?_
  have heq : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        (2 * M.condFail (qldGame hm) PA PB
          (c.question hm (.point W)) (c.question hm (.point W)))
      = 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          M.condFail (qldGame hm) PA PB
            (c.question hm (.point W)) (c.question hm (.point W)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [heq, show (172 : ℝ) * ε = 2 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (subtest_le hM hfail (adj_self' (.point W)) univ) (by norm_num)

/-- **`lem:qld-expanded-points`**: both items, on the expanded state. The measurements are the
hatted ones; they are cross-party consistent at `172 eps`, and their `X`-side and `Z`-side
observables commute at `57676416 eps` with no sign. -/
theorem expanded_points [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    {ε : ℝ} (hM : ‖M.ψ‖ = 1) (hPA : ∀ q, IsPVMIn (PA q).op)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) :
    (∀ W : Bas, ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ a : F, (M.reg (Anc F m)).xSqNorm ((hatPOVM hm PA W c).op a)
          ((hatPOVM hm PB W c).op a) ≤ 172 * ε)
      ∧ ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
          (M.reg (Anc F m)).stateSqNorm (hatObs hm PA .X c * hatObs hm PA .Z c
            - hatObs hm PA .Z c * hatObs hm PA .X c) ≤ 57676416 * ε :=
  ⟨fun W => hatPOVM_consistency (PB := PB) hM hfail W, hatObs_commutation (PB := PB) hM hPA hfail⟩

/-! ## The line measurements

`lem:qld-expanded-lines`, the paper's `lem:qld-comm-line-cons`. The construction is the line
analogue of the hatted point measurement: the strategy's line measurement, convolved with an
ancilla measurement that reports **the restriction of the encoding to the line** rather than its
value at a point.

Three things make it work, and all three are exact.

* `synLinePOVM_map_eval`: relabelling a line outcome of the ancilla by its value at a point of
  the line *is* the ancilla's point measurement there. Both are coarse-grainings of the same
  eigenbasis measurement (`synOf`), and the labels agree because evaluating the restriction of
  `g_h` along the line is evaluating `g_h` at the point (`eval_lineCoeffs`). The paper gets the
  same effect from "the exact consistency between the `tau^{W,line}` and `tau^{W,u}`
  measurements"; here the two families are literally the same family, relabelled.
* `isPVM_hatLinePOVM`: the convolution is **projective**, from two closure properties of
  projective measurements --- products and coarse-grainings (`isPVMIn_kronIn`,
  `POVMIn.isPVMIn_map`). The paper checks the same thing by hand.
* The ancilla's agreement probability is again exactly `1`
  (`sum_bornProb_epr_synOfPOVM`), so the expansion costs nothing here either.

As in the point case the whole estimate runs on Born probabilities and is converted to the
state-dependent distance once, at the end. That is what lets the paper's two forms of
line-against-point consistency --- comparing outcomes, and comparing the evaluation --- come out
of a *single* inequality: the coarse-graining that relates them is free at the Born level, and
`fact:data-processing` is never needed for `~=`.
-/

section Lines

/-! ### Restriction to a line, in coefficients -/

/-- **The restriction of a multivariate polynomial to the line** `t ↦ u₀ + t w`, as a polynomial
of degree at most `n` given by its coefficients. -/
def lineCoeffs (n : ℕ) (u₀ w : Point F m) (p : MvPolynomial (Fin m) F) : LinePoly F n :=
  fun i => (MIPRE.LowDegree.lineRestrict u₀ w p).coeff (i : ℕ)

/-- **Evaluating the restriction is evaluating along the line.** -/
theorem eval_lineCoeffs {n : ℕ} {p : MvPolynomial (Fin m) F} (hp : p.totalDegree ≤ n)
    (u₀ w : Point F m) (t : F) :
    (lineCoeffs n u₀ w p).eval t = MvPolynomial.eval (u₀ + t • w) p :=
  MIPRE.LowDegree.sum_coeff_lineRestrict hp u₀ w t

/-- **The pairing with `ind_m(u)` is the encoding evaluated at `u`**, which is what identifies the
ancilla's point measurement as a coarse-graining of its basis measurement along `g_h(u)`. -/
theorem dotF_indVec (h : Anc F m) (u : Point F m) :
    dotF h (indVec u) = MvPolynomial.eval u (ldEnc h) := by
  rw [ldEnc, map_sum, dotF]
  exact Finset.sum_congr rfl fun y _ => by rw [map_mul, MvPolynomial.eval_C]; rfl

/-- A polynomial of degree at most `k`, read as one of degree at most `n`: pad the coefficient
vector with zeros. An axis-parallel line answer has degree at most `d` and has to be added to an
ancilla restriction of degree at most `m`, so the two live in `LinePoly F (m d)` together. -/
def padLine {k : ℕ} (n : ℕ) (f : LinePoly F k) : LinePoly F n :=
  fun i => if h : (i : ℕ) < k + 1 then f ⟨i, h⟩ else 0

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The coefficient form of an evaluation, as a sum over `range (k+1)`. -/
theorem linePoly_eval_eq_range {k : ℕ} (f : LinePoly F k) (t : F) :
    f.eval t = ∑ j ∈ Finset.range (k + 1), (if h : j < k + 1 then f ⟨j, h⟩ else 0) * t ^ j := by
  rw [LinePoly.eval, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Padding does not change the polynomial.** -/
theorem eval_padLine {k n : ℕ} (hkn : k ≤ n) (f : LinePoly F k) (t : F) :
    (padLine n f).eval t = f.eval t := by
  rw [linePoly_eval_eq_range, linePoly_eval_eq_range]
  have hAB : ∀ j : ℕ, (if h : j < n + 1 then (padLine n f) ⟨j, h⟩ else 0) * t ^ j
      = (if h : j < k + 1 then f ⟨j, h⟩ else 0) * t ^ j := by
    intro j
    by_cases hj : j < n + 1
    · rw [dif_pos hj]; rfl
    · rw [dif_neg hj, dif_neg (by omega)]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range (n + 1)) => hAB j]
  refine (Finset.sum_subset (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega))
    fun j _ hj => ?_).symm
  rw [dif_neg (by simpa using hj), zero_mul]

/-- A line answer read as a polynomial of degree at most `n`, whichever of the two line formats it
has; anything else reads as zero, which the format check makes unreachable. -/
def rdLine (n : ℕ) : Answer F m d → LinePoly F n
  | .apoly f => padLine n f
  | .dpoly f => padLine n f
  | _ => 0

/-! ### The ancilla's line measurement -/

/-- **The ancilla's line measurement** `τ^{W,ℓ}`: measure all `M` qudits in the basis `W`, and
report the restriction to the line of the low-degree encoding of the outcome. -/
def synLinePOVM (n : ℕ) (W : Bas) (u₀ w : Point F m) : POVM (LinePoly F n) (Anc F m) :=
  synOfPOVM W fun h => lineCoeffs n u₀ w (ldEnc h)

/-- The ancilla's line measurement is projective. -/
theorem isPVM_synLinePOVM (n : ℕ) (W : Bas) (u₀ w : Point F m) :
    IsPVM fun f : LinePoly F n => (((synLinePOVM (F := F) (m := m) n W u₀ w).mats f).val) :=
  isPVM_synOfPOVM W _

/-- **The ancilla's line and point measurements are exactly compatible.** Relabelling a line
outcome by its value at the point of parameter `t` gives precisely the point measurement at that
point --- not approximately: the two families are the same coarse-graining of the same
eigenbasis measurement. -/
theorem synLinePOVM_map_eval {n : ℕ} (hmn : m ≤ n) (W : Bas) (u₀ w : Point F m) (t : F) :
    (synLinePOVM n W u₀ w).map (fun f => LinePoly.eval f t) = synPOVM W (u₀ + t • w) := by
  classical
  have hlabel : (fun h : Anc F m => LinePoly.eval (lineCoeffs n u₀ w (ldEnc h)) t)
      = fun h : Anc F m => dotF h (indVec (u₀ + t • w)) := by
    funext h
    rw [eval_lineCoeffs ((MIPRE.LowDegree.totalDegree_ldEnc_le h).trans hmn), dotF_indVec]
  refine POVM.ext' fun a => ?_
  rw [POVM.map_mats]
  calc ∑ f ∈ univ.filter fun f => LinePoly.eval f t = a, (((synLinePOVM n W u₀ w).mats f).val)
      = synOf (weylOf W) (fun h => LinePoly.eval (lineCoeffs n u₀ w (ldEnc h)) t) a :=
        sum_synOf _ _ _ _
    _ = synOf (weylOf W) (fun h => dotF h (indVec (u₀ + t • w))) a := by rw [hlabel]
    _ = (((synPOVM W (u₀ + t • w)).mats a).val) := rfl

/-! ### The hatted line measurement -/

/-- The strategy's line measurement at a content, read as a polynomial of degree at most `n` ---
the same definition for either player. -/
def lineAnsPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R] (n : ℕ)
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (ty : Ty)
    (c : Content F m) : POVMIn (LinePoly F n) R :=
  (P (c.question hm ty)).map (rdLine n)

/-- **The hatted line measurement** `M̂^{(Line,W),ℓ}_f = ∑_{f' + f'' = f} M^{(Line,W),ℓ}_{f'} ⊗
τ^{W,ℓ}_{f''}`: the product of the strategy's line measurement with the ancilla's, coarse-grained
by adding the two polynomials. -/
def hatLinePOVM {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R] (n : ℕ) (hm : m ∣ Fintype.card F)
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (ty : Ty)
    (base dir : Content F m → Point F m) (c : Content F m) :
    POVMIn (LinePoly F n) (Matrix (Anc F m) (Anc F m) R) :=
  (kronIn (lineAnsPOVM n hm P ty c) (synLinePOVM n W (base c) (dir c))
    (isPVM_synLinePOVM n W _ _)).map fun p => p.1 + p.2

/-- **The hatted line measurement is projective** whenever the strategy's own line measurement is.
Projectivity is closed under products and under coarse-graining, and that is all the convolution
is; the paper checks the same thing by hand. -/
theorem isPVM_hatLinePOVM {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R] {n : ℕ}
    {hm : m ∣ Fintype.card F} {P : Question F m → POVMIn (Answer F m d) R} {W : Bas} {ty : Ty}
    {base dir : Content F m → Point F m} {c : Content F m}
    (hP : IsPVMIn (P (c.question hm ty)).op) :
    IsPVMIn (hatLinePOVM n hm P W ty base dir c).op :=
  POVMIn.isPVMIn_map (isPVMIn_kronIn (POVMIn.isPVMIn_map hP _) _ _) _

/-! ### Self-consistency of the hatted line measurement -/

/-- **The hatted line measurements are cross-party consistent**, at one content: twice the
conditional failure of the line type's own consistency subtest, and nothing for the ancilla. The
three inputs are the same three as in the point case --- the strategy's consistency, the ancilla's
*perfect* consistency, and Born-level data processing for the convolution. -/
theorem sum_xSqNorm_hatLinePOVM_le [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
    [StarProper ℬ] {n : ℕ} {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    (hM : ‖M.ψ‖ = 1) (W : Bas) (ty : Ty) (base dir : Content F m → Point F m)
    (c : Content F m) :
    ∑ f : LinePoly F n, (M.reg (Anc F m)).xSqNorm
        ((hatLinePOVM n hm PA W ty base dir c).op f)
        ((hatLinePOVM n hm PB W ty base dir c).op f)
      ≤ 2 * M.condFail (qldGame hm) PA PB (c.question hm ty) (c.question hm ty) := by
  classical
  -- the agreement of the product measurement factorizes, and the ancilla factor is one
  have hfac : ∀ p : LinePoly F n × LinePoly F n, (M.reg (Anc F m)).bornProb
      ((kronIn (lineAnsPOVM n hm PA ty c) (synLinePOVM n W (base c) (dir c))
        (isPVM_synLinePOVM n W _ _)).op p)
      ((kronIn (lineAnsPOVM n hm PB ty c) (synLinePOVM n W (base c) (dir c))
        (isPVM_synLinePOVM n W _ _)).op p)
      = M.bornProb ((lineAnsPOVM n hm PA ty c).op p.1) ((lineAnsPOVM n hm PB ty c).op p.1)
        * bornProb (epr (F := F) (n := Fin m → Bool))
          (((synLinePOVM n W (base c) (dir c)).mats p.2).val)
          (((synLinePOVM n W (base c) (dir c)).mats p.2).val) := by
    intro p
    rw [kronIn_op, kronIn_op, BipartiteModel.bornProb_expand_smulKron _ _ _ _
      ((synLinePOVM n W (base c) (dir c)).posSemidef p.2)
      ((synLinePOVM n W (base c) (dir c)).posSemidef p.2), mul_comm]
    rfl
  have hanc : ∑ f : LinePoly F n, bornProb (epr (F := F) (n := Fin m → Bool))
      (((synLinePOVM n W (base c) (dir c)).mats f).val)
      (((synLinePOVM n W (base c) (dir c)).mats f).val) = 1 := by
    rw [synLinePOVM]
    exact sum_bornProb_epr_synOfPOVM W _
  have hprod : ∑ p : LinePoly F n × LinePoly F n, (M.reg (Anc F m)).bornProb
      ((kronIn (lineAnsPOVM n hm PA ty c) (synLinePOVM n W (base c) (dir c))
        (isPVM_synLinePOVM n W _ _)).op p)
      ((kronIn (lineAnsPOVM n hm PB ty c) (synLinePOVM n W (base c) (dir c))
        (isPVM_synLinePOVM n W _ _)).op p)
      = ∑ f : LinePoly F n, M.bornProb ((lineAnsPOVM n hm PA ty c).op f)
          ((lineAnsPOVM n hm PB ty c).op f) := by
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hfac p,
      sum_prod_mul
        (fun f : LinePoly F n => M.bornProb ((lineAnsPOVM n hm PA ty c).op f)
          ((lineAnsPOVM n hm PB ty c).op f))
        (fun f : LinePoly F n => bornProb (epr (F := F) (n := Fin m → Bool))
          (((synLinePOVM n W (base c) (dir c)).mats f).val)
          (((synLinePOVM n W (base c) (dir c)).mats f).val)),
      hanc, mul_one]
  -- data processing for the convolution
  have hdp := (M.reg (Anc F m)).sum_bornProb_le_map
    (kronIn (lineAnsPOVM n hm PA ty c) (synLinePOVM n W (base c) (dir c))
      (isPVM_synLinePOVM n W _ _))
    (kronIn (lineAnsPOVM n hm PB ty c) (synLinePOVM n W (base c) (dir c))
      (isPVM_synLinePOVM n W _ _))
    (fun p : LinePoly F n × LinePoly F n => p.1 + p.2)
  rw [hprod] at hdp
  -- the strategy's own consistency, at the Born level
  have hcons : 1 - ∑ f : LinePoly F n, M.bornProb ((lineAnsPOVM n hm PA ty c).op f)
      ((lineAnsPOVM n hm PB ty c).op f)
      ≤ M.condFail (qldGame hm) PA PB (c.question hm ty) (c.question hm ty) := by
    refine M.one_sub_sum_bornProb_le_condFail (G := qldGame hm) (MA := PA) (MB := PB)
      (rdLine n) (rdLine n) fun a b h => ?_
    have hs := (of_accepts h).2.2
    rw [subtests, if_pos rfl] at hs
    exact congrArg (rdLine n) (of_decide_eq_true hs)
  refine le_trans ((M.reg (Anc F m)).xSqNorm_sum_le_two_mul (hatVec_unit hM) _ _) ?_
  rw [hatLinePOVM, hatLinePOVM]
  linarith

/-- **The self-consistency item of `lem:qld-expanded-lines`.** On average over the verifier's
content --- which is the line--point distribution, the line and the point being read off the same
sample --- the two players' hatted line measurements agree at `172 eps`. -/
theorem hatLinePOVM_consistency [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
    [StarProper ℬ] {n : ℕ} {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    {ε : ℝ} (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) (ty : Ty)
    (base dir : Content F m → Point F m) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ f : LinePoly F n, (M.reg (Anc F m)).xSqNorm
          ((hatLinePOVM n hm PA W ty base dir c).op f)
          ((hatLinePOVM n hm PB W ty base dir c).op f)
      ≤ 172 * ε := by
  classical
  refine le_trans (Finset.sum_le_sum fun c (_ : c ∈ univ) =>
    mul_le_mul_of_nonneg_left (sum_xSqNorm_hatLinePOVM_le (PB := PB) hM W ty base dir c)
      (by positivity)) ?_
  have heq : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        (2 * M.condFail (qldGame hm) PA PB (c.question hm ty) (c.question hm ty))
      = 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          M.condFail (qldGame hm) PA PB (c.question hm ty) (c.question hm ty) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [heq, show (172 : ℝ) * ε = 2 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (subtest_le hM hfail (adj_self' ty) univ) (by norm_num)

/-! ### Consistency with the expanded point measurements -/

omit [Algebra (ZMod 2) F] in
theorem Content.omega_pt (c : Content F m) (W : Bas) : c.omega.pt W = c.pt W := by
  cases W <;> rfl

/-- **The hatted line measurement, relabelled by its value at a point of the line, is the product
of the two relabelled factors.** Evaluation is additive, so it passes through the convolution. -/
theorem hatLinePOVM_map_eval {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    [PartialOrder R] [StarOrderedRing R] [StarProper R] {n : ℕ}
    (hm : m ∣ Fintype.card F) (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (ty : Ty)
    (base dir : Content F m → Point F m) (c : Content F m) (t : F) :
    (hatLinePOVM n hm P W ty base dir c).map (fun f => LinePoly.eval f t)
      = (kronIn ((lineAnsPOVM n hm P ty c).map fun f => LinePoly.eval f t)
          ((synLinePOVM n W (base c) (dir c)).map fun f => LinePoly.eval f t)
          (isPVM_povm_map _ (isPVM_synLinePOVM n W _ _) _)).map
        fun p => p.1 + p.2 := by
  rw [hatLinePOVM, POVMIn.map_map, kronIn_map _ _ (isPVM_synLinePOVM n W _ _), POVMIn.map_map]
  congr 1
  funext p
  exact LinePoly.eval_add p.1 p.2 t

/-- **The line-against-point item of `lem:qld-expanded-lines`.** At one content: twice the
conditional failure of the line subtest, and nothing for the ancilla, whose line and point
measurements are *exactly* compatible (`synLinePOVM_map_eval`). This single inequality carries both
of the paper's two forms --- comparing a line outcome with a point outcome, and comparing the
evaluation of the line polynomial at the point --- because at the Born level the coarse-graining
that relates them is free. -/
theorem sum_xSqNorm_hatLine_point_le [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
    [StarProper ℬ] {n : ℕ} (hmn : m ≤ n) {M : BipartiteModel 𝒞 𝒜 ℬ}
    {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    (hM : ‖M.ψ‖ = 1) (W : Bas) (ty : Ty) (base dir : Content F m → Point F m)
    (hon : ∀ c : Content F m,
      base c + (MIPRE.LIDT.CL.lineParam (base c) (dir c) (c.pt W)) • dir c = c.pt W)
    (hsub : ∀ (c : Content F m) (a b : Answer F m d),
      accepts hm (c.question hm (.point W)) (c.question hm ty) a b = true →
        rdVal a = (rdLine n b).eval (MIPRE.LIDT.CL.lineParam (base c) (dir c) (c.pt W)))
    (c : Content F m) :
    ∑ a : F, (M.reg (Anc F m)).xSqNorm ((hatPOVM hm PA W c).op a)
        (((hatLinePOVM n hm PB W ty base dir c).map
            (fun f => LinePoly.eval f
              (MIPRE.LIDT.CL.lineParam (base c) (dir c) (c.pt W)))).op a)
      ≤ 2 * M.condFail (qldGame hm) PA PB (c.question hm (.point W)) (c.question hm ty) := by
  classical
  set t := MIPRE.LIDT.CL.lineParam (base c) (dir c) (c.pt W) with ht
  -- the ancilla's two measurements are the same measurement
  have hancEq : (synLinePOVM n W (base c) (dir c)).map (fun f => LinePoly.eval f t)
      = synPOVM W (c.pt W) := by
    rw [synLinePOVM_map_eval hmn W (base c) (dir c) t, hon c]
  -- both players' measurements are convolutions of a strategy factor with that one
  have hB : (hatLinePOVM n hm PB W ty base dir c).map (fun f => LinePoly.eval f t)
      = (kronIn ((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t)
          (synPOVM W (c.pt W)) (isPVM_synPOVM W _)).map fun p => p.1 + p.2 := by
    rw [hatLinePOVM_map_eval, kronIn_congr _ hancEq _ (isPVM_synPOVM W (c.pt W))]
  have hsyn : synPOVM W (c.omega.pt W) = synPOVM W (c.pt W) := by rw [Content.omega_pt]
  have hA : hatPOVM hm PA W c
      = (kronIn (ptValPOVM hm PA W c) (synPOVM W (c.pt W)) (isPVM_synPOVM W _)).map
          fun p => p.1 + p.2 := by
    rw [hatPOVM, kronIn_congr _ hsyn _ (isPVM_synPOVM W (c.pt W))]
  -- the agreement of the product measurement factorizes, and the ancilla factor is one
  have hfac : ∀ p : F × F, (M.reg (Anc F m)).bornProb
      ((kronIn (ptValPOVM hm PA W c) (synPOVM W (c.pt W)) (isPVM_synPOVM W _)).op p)
      ((kronIn ((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t)
          (synPOVM W (c.pt W)) (isPVM_synPOVM W _)).op p)
      = M.bornProb ((ptValPOVM hm PA W c).op p.1)
          (((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t).op p.1)
        * bornProb (epr (F := F) (n := Fin m → Bool))
          (((synPOVM W (c.pt W)).mats p.2).val) (((synPOVM W (c.pt W)).mats p.2).val) := by
    intro p
    rw [kronIn_op, kronIn_op, BipartiteModel.bornProb_expand_smulKron _ _ _ _
      ((synPOVM W (c.pt W)).posSemidef p.2) ((synPOVM W (c.pt W)).posSemidef p.2), mul_comm]
    rfl
  have hprod : ∑ p : F × F, (M.reg (Anc F m)).bornProb
      ((kronIn (ptValPOVM hm PA W c) (synPOVM W (c.pt W)) (isPVM_synPOVM W _)).op p)
      ((kronIn ((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t)
          (synPOVM W (c.pt W)) (isPVM_synPOVM W _)).op p)
      = ∑ a : F, M.bornProb ((ptValPOVM hm PA W c).op a)
          (((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t).op a) := by
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hfac p,
      sum_prod_mul
        (fun a : F => M.bornProb ((ptValPOVM hm PA W c).op a)
          (((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t).op a))
        (fun a : F => bornProb (epr (F := F) (n := Fin m → Bool))
          (((synPOVM W (c.pt W)).mats a).val) (((synPOVM W (c.pt W)).mats a).val)),
      sum_bornProb_epr_synPOVM, mul_one]
  -- data processing for the convolution
  have hdp := (M.reg (Anc F m)).sum_bornProb_le_map
    (kronIn (ptValPOVM hm PA W c) (synPOVM W (c.pt W)) (isPVM_synPOVM W _))
    (kronIn ((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t)
      (synPOVM W (c.pt W)) (isPVM_synPOVM W _))
    (fun p : F × F => p.1 + p.2)
  rw [hprod] at hdp
  -- the strategy's own line-against-point agreement, at the Born level
  have hcons : 1 - ∑ a : F, M.bornProb ((ptValPOVM hm PA W c).op a)
      (((lineAnsPOVM n hm PB ty c).map fun f => LinePoly.eval f t).op a)
      ≤ M.condFail (qldGame hm) PA PB (c.question hm (.point W)) (c.question hm ty) := by
    rw [ptValPOVM, lineAnsPOVM, POVMIn.map_map]
    exact M.one_sub_sum_bornProb_le_condFail (G := qldGame hm) (MA := PA) (MB := PB)
      rdVal (fun b => LinePoly.eval (rdLine n b) t) fun a b h => hsub c a b h
  refine le_trans ((M.reg (Anc F m)).xSqNorm_sum_le_two_mul (hatVec_unit hM) _ _) ?_
  rw [hA, hB]
  linarith

/-! ### The two line types of the Pauli basis test -/

/-- **The sampled point lies on the line the seeded test reports**, at the parameter `lineParam`
computes. The base point is the canonical representative, which differs from the point by an
element of the direction's span (`MIPRE.CL.sub_canonLin_mem`). -/
theorem rep_add_lineParam_smul (v x : Point F m) :
    MIPRE.LIDT.CL.rep v x
        + (MIPRE.LIDT.CL.lineParam (MIPRE.LIDT.CL.rep v x) v x) • v = x := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (MIPRE.CL.sub_canonLin_mem (Submodule.span F {v}) x)
  have hx : x = MIPRE.LIDT.CL.rep v x + t • v := by
    rw [MIPRE.LIDT.CL.rep, ht]
    abel
  by_cases hv : ∃ j, v j ≠ 0
  · set u₀ := MIPRE.LIDT.CL.rep v x with hu
    rw [hx, MIPRE.LIDT.Adapter.lineParam_eq_of_mem hv u₀ t]
  · have hv0 : v = 0 := funext fun j => not_not.mp fun hj => hv ⟨j, hj⟩
    subst hv0
    rw [smul_zero, add_zero]
    rw [smul_zero, add_zero] at hx
    exact hx.symm

/-- The base point of the axis-parallel line a content presents on the `W` side. -/
def abaseOf (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) : Point F m :=
  MIPRE.LIDT.CL.rep (dirOf hm c) (c.pt W)

/-- The direction of the diagonal line a content presents. -/
def ddirOf (hm : m ∣ Fintype.card F) (c : Content F m) : Point F m :=
  MIPRE.LIDT.CL.zeroBelow (MIPRE.LIDT.CL.chi hm c.s) c.v

/-- The base point of the diagonal line a content presents on the `W` side. -/
def dbaseOf (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) : Point F m :=
  MIPRE.LIDT.CL.rep (ddirOf hm c) (c.pt W)

omit [Algebra (ZMod 2) F] in
theorem d_le_mul : d ≤ m * d :=
  Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero (NeZero.ne m))

omit [Algebra (ZMod 2) F] in
theorem m_le_mul (hd : 1 ≤ d) : m ≤ m * d :=
  Nat.le_mul_of_pos_right m hd

/-- **The axis-parallel line subtest, as the hypothesis the general estimate needs**: the line
answer, padded to degree `m d` and evaluated at the parameter of the sampled point, is the point
answer. This is item 2a of `lem:qld-win` with the padding added. -/
theorem hsub_aline {hm : m ∣ Fintype.card F} (W : Bas) (c : Content F m) (a b : Answer F m d)
    (h : accepts hm (c.question hm (.point W)) (c.question hm (.aline W)) a b = true) :
    rdVal a = (rdLine (m * d) b).eval
      (MIPRE.LIDT.CL.lineParam (abaseOf hm W c) (dirOf hm c) (c.pt W)) := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨p, rfl⟩ := eq_apoly_of_fmtOk hfb
  have hs' : lowDeg (MIPRE.LIDT.CL.rep (dirOf hm c) (c.pt W)) (dirOf hm c) (c.pt W) p a'
      = true := by
    simpa [subtests, Question.ty, Content.question, pairTest, dirOf] using hs
  rw [rdVal, rdLine, eval_padLine d_le_mul, abaseOf]
  exact (eval_eq_of_lowDeg hs').symm

/-- **The diagonal line subtest**, the same way: item 2b of `lem:qld-win`. -/
theorem hsub_dline {hm : m ∣ Fintype.card F} (W : Bas) (c : Content F m) (a b : Answer F m d)
    (h : accepts hm (c.question hm (.point W)) (c.question hm (.dline W)) a b = true) :
    rdVal a = (rdLine (m * d) b).eval
      (MIPRE.LIDT.CL.lineParam (dbaseOf hm W c) (ddirOf hm c) (c.pt W)) := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨a', rfl⟩ := eq_val_of_fmtOk hfa
  obtain ⟨p, rfl⟩ := eq_dpoly_of_fmtOk hfb
  have hs' : lowDeg (MIPRE.LIDT.CL.rep (ddirOf hm c) (c.pt W)) (ddirOf hm c) (c.pt W) p a'
      = true := by
    simpa [subtests, Question.ty, Content.question, pairTest, ddirOf] using hs
  rw [rdVal, rdLine, eval_padLine le_rfl, dbaseOf]
  exact (eval_eq_of_lowDeg hs').symm

/-- **The line-against-point item of `lem:qld-expanded-lines`, on average over the content.** -/
theorem hatLinePOVM_point_consistency [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
    [StarProper ℬ] {n : ℕ} (hmn : m ≤ n) {M : BipartiteModel 𝒞 𝒜 ℬ}
    {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    {ε : ℝ} (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) (ty : Ty)
    (hadj : adj (.point W) ty = true) (base dir : Content F m → Point F m)
    (hon : ∀ c : Content F m,
      base c + (MIPRE.LIDT.CL.lineParam (base c) (dir c) (c.pt W)) • dir c = c.pt W)
    (hsub : ∀ (c : Content F m) (a b : Answer F m d),
      accepts hm (c.question hm (.point W)) (c.question hm ty) a b = true →
        rdVal a = (rdLine n b).eval (MIPRE.LIDT.CL.lineParam (base c) (dir c) (c.pt W))) :
    ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ a : F, (M.reg (Anc F m)).xSqNorm ((hatPOVM hm PA W c).op a)
          (((hatLinePOVM n hm PB W ty base dir c).map
              (fun f => LinePoly.eval f
                (MIPRE.LIDT.CL.lineParam (base c) (dir c) (c.pt W)))).op a)
      ≤ 172 * ε := by
  classical
  refine le_trans (Finset.sum_le_sum fun c (_ : c ∈ univ) =>
    mul_le_mul_of_nonneg_left
      (sum_xSqNorm_hatLine_point_le (PB := PB) hmn hM W ty base dir hon hsub c)
      (by positivity)) ?_
  have heq : ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
        (2 * M.condFail (qldGame hm) PA PB (c.question hm (.point W)) (c.question hm ty))
      = 2 * ∑ c : Content F m, (Fintype.card (Content F m) : ℝ)⁻¹ *
          M.condFail (qldGame hm) PA PB (c.question hm (.point W)) (c.question hm ty) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [heq, show (172 : ℝ) * ε = 2 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (subtest_le hM hfail hadj univ) (by norm_num)

/-! ### `lem:qld-expanded-lines` -/

/-- **`lem:qld-expanded-lines` for the axis-parallel line type.** The hatted line measurement has
outcomes the polynomials of degree at most `m d` on the line; it is self-consistent over the
line--point distribution at `172 eps`, and consistent with the expanded point measurements of
`lem:qld-expanded-points` at `172 eps` --- in the form that compares the *evaluation* of the line
polynomial at the sampled point, which at the Born level is also the form that compares the
outcomes. Projectivity is `isPVM_hatLinePOVM`, given a projective strategy. -/
theorem expanded_lines_aline [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (hd : 1 ≤ d) {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    {ε : ℝ} (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    (∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ f : LinePoly F (m * d), (M.reg (Anc F m)).xSqNorm
          ((hatLinePOVM (m * d) hm PA W (.aline W) (abaseOf hm W) (dirOf hm) c).op f)
          ((hatLinePOVM (m * d) hm PB W (.aline W) (abaseOf hm W) (dirOf hm) c).op f)
        ≤ 172 * ε)
      ∧ ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ a : F, (M.reg (Anc F m)).xSqNorm ((hatPOVM hm PA W c).op a)
            (((hatLinePOVM (m * d) hm PB W (.aline W) (abaseOf hm W) (dirOf hm) c).map
                (fun f => LinePoly.eval f
                  (MIPRE.LIDT.CL.lineParam (abaseOf hm W c) (dirOf hm c) (c.pt W)))).op a)
          ≤ 172 * ε :=
  ⟨hatLinePOVM_consistency (PB := PB) hM hfail W (.aline W) (abaseOf hm W) (dirOf hm),
    hatLinePOVM_point_consistency (PB := PB) (m_le_mul hd) hM hfail W (.aline W)
      (adj_point_aline W) (abaseOf hm W) (dirOf hm)
      (fun c => rep_add_lineParam_smul (dirOf hm c) (c.pt W)) (hsub_aline W)⟩

/-- **`lem:qld-expanded-lines` for the diagonal line type**, the same two items. -/
theorem expanded_lines_dline [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]
    (hd : 1 ≤ d) {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    {ε : ℝ} (hM : ‖M.ψ‖ = 1)
    (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε) (W : Bas) :
    (∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ∑ f : LinePoly F (m * d), (M.reg (Anc F m)).xSqNorm
          ((hatLinePOVM (m * d) hm PA W (.dline W) (dbaseOf hm W) (ddirOf hm) c).op f)
          ((hatLinePOVM (m * d) hm PB W (.dline W) (dbaseOf hm W) (ddirOf hm) c).op f)
        ≤ 172 * ε)
      ∧ ∑ c, (Fintype.card (Content F m) : ℝ)⁻¹ *
          ∑ a : F, (M.reg (Anc F m)).xSqNorm ((hatPOVM hm PA W c).op a)
            (((hatLinePOVM (m * d) hm PB W (.dline W) (dbaseOf hm W) (ddirOf hm) c).map
                (fun f => LinePoly.eval f
                  (MIPRE.LIDT.CL.lineParam (dbaseOf hm W c) (ddirOf hm c) (c.pt W)))).op a)
          ≤ 172 * ε :=
  ⟨hatLinePOVM_consistency (PB := PB) hM hfail W (.dline W) (dbaseOf hm W) (ddirOf hm),
    hatLinePOVM_point_consistency (PB := PB) (m_le_mul hd) hM hfail W (.dline W)
      (adj_point_dline W) (dbaseOf hm W) (ddirOf hm)
      (fun c => rep_add_lineParam_smul (ddirOf hm c) (c.pt W)) (hsub_dline W)⟩

end Lines

end Expansion

end MIPRE.QLD

end

end
