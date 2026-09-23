/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Descent
import MIPRE.Background.QLD.PhysEmbed
import MIPRE.Background.QLD.QLDError
import MIPRE.Background.QLD.RegisterForm
import MIPRE.Background.QLD.Regime
import MIPRE.Background.QLD.Legalize
import MIPRE.Foundations.StrategyDilation

/-!
# `thm:qld`: soundness of the Pauli basis test

This file assembles `thm:qld` (the paper's `thm:pauli-appendix`, proved at the end of
`qld-isometry.tex`) from the swap isometry lemma and four pieces written for this step:
`Descent.lean`, `PhysEmbed.lean`, `QLDError.lean` and `RegisterForm.lean`. The headline is
`qld_soundness`: universal constants `a ≥ 1`, `0 < b < 1`, fixed before anything else, such that
every **POVM** strategy of the Pauli basis test that fails with probability at most `ε` has local
isometries `V_A`, `V_B` and **one** unit state `|aux>` with

1. `‖(V_A ⊗ V_B) |ψ> - |EPR_q>^M ⊗ |aux>‖ ≤ δ`, the distance itself and not its square;
2. for each basis `W`, and for each party, the summed squared state-dependent distance, relative
   to `|EPR_q>^M ⊗ |aux>`, between the party's **original** coarse `(Pauli, W)` measurement
   conjugated by its isometry and the honest projectors `tau^W_h` on its register is at most `δ`;

where `δ = a (md)^a (ε^b + q^{-b} + 2^{-bmd})` (`errShape`). The isometries are register-first,
`Matrix (Anc F m × H) d ℂ`, in the vocabulary of the consumer
(`TypedEstimates.quantumValue_ge_of_valid_isometric_images`): `isometricState`, `registerState`,
`isometricImage`.

## The route

`MirrorSimul.swap_isometry` is a statement about a *legal projective* strategy, about the swapped
physical state `V_A ⊗ V_B |psi-hat>`, and about `V`-conjugation of the dilated measurement.
`thm:qld` is about an arbitrary POVM strategy, its own state and its own measurement. Three
passages close the gap, and only the last is more than bookkeeping.

* **Dilate and legalize** (`exists_legal_dilation`). Naimark makes the strategy projective on
  `d × Answer`, compressed back by the ancilla `|a₀>`; legalizing makes it legally supported,
  which the chain needs, at no cost in value. Neither changes what the coarse Pauli measurement
  compresses to (`rdPauliVec_legalize_pauli`).
* **The state is a product image** (`exists_phys_of_regime`). `mirrorOfGlobalPairs` --- and not
  `exists_mirrorSimul`, which forgets it --- has an explicit physical state:
  `physEmb ⊗ physEmb` applied to the doubly padded state (`physVec_mirrorOfGlobalPairs`), which is
  itself `N ⊗ N` applied to `ψ` (`kronecker_mulVec_extVec2`). So with
  `phi_A = V_A ∘ physEmb ∘ N`, the paper's `phi_A` composed with the dilation, the swapped physical
  state is `(phi_A ⊗ phi_B) ψ` on the nose, and item 1 of the swap lemma is item 1 here.
* **The descent through agreement** (`MirrorSimul.exists_phys_descent`). Compression by an
  isometry does not preserve a *closeness* statement, which is what item 2 of the swap lemma is;
  it preserves an *agreement* with a family on the other party, which is bilinear. On the product
  state `tau^W_h` on Alice's half of the pair acts as `tau^W_h` on Bob's, so closeness to `tau^W`
  is agreement with `tau^W` across the cut, and that agreement is carried to the pushed-forward
  state (at `2 sqrt η`), compressed, and carried back (`sum_snorm_sq_descent_isometry_aOp`). Its one
  hypothesis is the compression identity `phi_A^† (V_A M'_h V_A^†) phi_A = M_h`, which is
  `conj_mul_conj_unitary`, then `physEmb_mul_ancillaEmbed_conj`, then the dilation's own
  compression. So the paper's two passages --- `V`-conjugation to `phi`-conjugation through the
  projection `P = V (Id ⊗ P_EPR) V^†`, and the dilation back to the POVM --- are one step here.

## The error

`exists_qldErr_le` fixes the constants: `qldErr` at the failure bound `min ε 1` is of the shape.
`min ε 1` is still a failure bound, because a value is nonnegative (`povmValue_nonneg`).
`exists_le_qldErr` then bounds both items by `qldErr`: inside the regime (`48 m d ≤ q`, where the
chain runs, and `qldHlt < 1`, where `swap_isometry` applies) item 1 costs `sqrt qldEta` and item 2
costs `deltaItemTwo + 8 sqrt qldEta`, both at most `qldBound`; every item is also at most `2`
whatever the isometries (`norm_isometricState_sub_registerState_le_two`,
`sum_snorm_sq_registerState_alice_le_two`), so at most `min qldBound 4`. Outside the regime
`qldErr = 4`, and the inert ancilla `ψ ↦ |0> ⊗ ψ` with `aux = ψ` does. The paper budgets a
square root for converting agreement back to closeness, and halves `b` for it; neither conversion
takes a root here (closeness and agreement of two projective families determine each other
exactly, and a sub-POVM's closeness to a projective family is linear in its disagreement), so the
only root is the one inside `sqrt qldEta`, the cost of moving between the two states. The paper's
other halving, for item 1's norm against the swap lemma's squared norm, is
`sqrt_qldEta_le_qldBound`.

## What differs from the paper's statement

* The regime is `48 m d ≤ q`, not `16 m d ≤ q`: `48` is where `lem:qld-global-separate` is
  formalized. The constant `a` absorbs the difference, as the paper's own `a ≥ 64` does.
* `m ≥ 1` is the instance `[NeZero m]`, which `qldGame` needs to be stated at all.
* The `(Pauli, W)` measurement is read as cube data through `rdPauliVec`, which reads an answer of
  the wrong format as `h = 0`. The paper assumes well-formatted answers; this is a relabelling of
  outcomes, not a restriction.

## A note on spelling

`MirrorSimul.exists_phys_descent` is stated for any `MirrorSimul` and any embeddings `E_A`, `E_B`
of original spaces, typed with `M.Ea`. Only `exists_phys_of_regime` meets the concrete
`mirrorOfGlobalPairs`, whose `Ea` is definitionally, not reducibly, the padding type: the facts
about `physEmb` are proved at the explicit type and handed over as arguments, where the
elaborator checks them up to definitional equality.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.Weyl MIPRE.Introspection
open scoped Kronecker ComplexOrder MatrixOrder

/- The same four-fold physical register as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-! ## Generic facts -/

section Generic

/-- **The value of a POVM strategy is nonnegative.** -/
theorem povmValue_nonneg {X Y A B dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB] (G : Game X Y A B)
    (ψ : dA × dB → ℂ) (MA : X → POVM A dA) (MB : Y → POVM B dB) :
    0 ≤ povmValue G ψ MA MB :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (G.μ_nonneg x y) (condWin_nonneg x y)

/-- **A rectangular isometry after a rectangular isometry is an isometry.** -/
theorem isometry_mul_isometry {R S D : Type*} [Fintype R] [Fintype S] [DecidableEq S]
    [DecidableEq D] {U : Matrix R S ℂ} {E : Matrix S D ℂ} (hU : Uᴴ * U = 1) (hE : Eᴴ * E = 1) :
    (U * E)ᴴ * (U * E) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul, hE]

/-- **Compressing a unitary conjugate by the unitary followed by an embedding** is compressing by
the embedding alone: `(U E)^† (U X U^†) (U E) = E^† X E`. -/
theorem conj_mul_conj_unitary {R D : Type*} [Fintype R] [DecidableEq R] [Fintype D]
    {U : Matrix R R ℂ} (hU : Uᴴ * U = 1) (E : Matrix R D ℂ) (X : Matrix R R ℂ) :
    (U * E)ᴴ * (U * X * Uᴴ) * (U * E) = Eᴴ * X * E := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

/-- **Two unit vectors are at distance at most `2`.** -/
theorem norm_evec_sub_le_two {N : Type*} [Fintype N] {v w : N → ℂ} (hv : ‖evec v‖ = 1)
    (hw : ‖evec w‖ = 1) : ‖evec (v - w)‖ ≤ 2 := by
  rw [evec_sub]
  calc ‖evec v - evec w‖ ≤ ‖evec v‖ + ‖evec w‖ := norm_sub_le _ _
    _ = 2 := by rw [hv, hw]; norm_num

end Generic

/-! ## From a POVM strategy to a legal projective one -/

section Dilate

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- **Legalizing a `(Pauli, W)` answer does not change the cube data it reports**: an answer of
the wrong format reads as `0`, and so does the default. -/
theorem rdPauliVec_legalize_pauli (W : Bas) (a : Answer F m d) :
    rdPauliVec (legalize (.pauli W) a) = rdPauliVec a := by
  cases a <;> simp [legalize, Question.fmtOk, Question.defaultAns, rdPauliVec]

omit [DecidableEq F] in
/-- A finite field has at least two elements. -/
theorem two_le_card_field : 2 ≤ Fintype.card F := Fintype.one_lt_card

variable [Algebra (ZMod 2) F] [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]

/-- **Every POVM strategy is the compression of a legal projective one, on the doubly padded
state.** Naimark dilation (`exists_projective_dilation_povm`) makes each party's measurements
projective on `d × Answer`, compressed back by the ancilla state `|a₀>`; legalizing
(`legalizeStrat`) makes them legally supported, keeps them projective, and does not raise the
failure probability. The coarse `(Pauli, W)` measurement --- the one the theorem is about --- is
unchanged by legalization (`rdPauliVec_legalize_pauli`), so it still compresses to the original
strategy's. -/
theorem exists_legal_dilation (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    {ε : ℝ} (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (a₀ : Answer F m d) :
    ∃ (MA' : Question F m → POVM (Answer F m d) (dA × Answer F m d))
      (MB' : Question F m → POVM (Answer F m d) (dB × Answer F m d)),
      (∀ q, IsPVM fun a => ((MA' q).mats a).val) ∧ (∀ q, IsPVM fun a => ((MB' q).mats a).val) ∧
      LegalSupport MA' ∧ LegalSupport MB' ∧
      1 - povmValue (qldGame hm) (extVec2 ψ a₀ a₀) MA' MB' ≤ ε ∧
      (∀ (W : Bas) (h : Anc F m), ancCompress a₀ ((((MA' (.pauli W)).map rdPauliVec).mats h).val)
        = (((MA (.pauli W)).map rdPauliVec).mats h).val) ∧
      (∀ (W : Bas) (h : Anc F m), ancCompress a₀ ((((MB' (.pauli W)).map rdPauliVec).mats h).val)
        = (((MB (.pauli W)).map rdPauliVec).mats h).val) := by
  obtain ⟨PA, hPA⟩ := exists_projective_dilation_povm MA a₀
  obtain ⟨PB, hPB⟩ := exists_projective_dilation_povm MB a₀
  have hpvm : ∀ {D : Type} [Fintype D] [DecidableEq D]
      (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix D D ℂ)) (q : Question F m),
      IsPVM fun a => ((P.toPOVM q).mats a).val :=
    fun P q => ⟨P.selfAdjoint q, P.projective q, P.normalized q⟩
  refine ⟨legalizeStrat PA.toPOVM, legalizeStrat PB.toPOVM, isPVM_legalizeStrat (hpvm PA),
    isPVM_legalizeStrat (hpvm PB), legalSupport_legalizeStrat _, legalSupport_legalizeStrat _,
    ?_, ?_, ?_⟩
  · refine one_sub_povmValue_legalizeStrat_le hm _ _ _ ?_
    rw [povmValue_extVec2]
    simpa only [hPA, hPB] using hfail
  · intro W h
    rw [legalizeStrat_map _ _ _ (rdPauliVec_legalize_pauli W), ← POVM.compress_mats,
      POVM.map_compress, hPA]
  · intro W h
    rw [legalizeStrat_map _ _ _ (rdPauliVec_legalize_pauli W), ← POVM.compress_mats,
      POVM.map_compress, hPB]

end Dilate

/-! ## The embedding of the original space -/

section Embed

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  {D A : Type*} [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]

/-- **The embedding of the original space**, `phi_0 ∘ N`: the Naimark ancilla at `|a₀>`, then
the pair and the padding (`physEmb`). It is an isometry. -/
theorem physEmb_mul_ancillaEmbed_isometry (a₀ : A) :
    (physEmb (F := F) (m := m) (d := d) (D × A) * ancillaEmbed D a₀)ᴴ
        * (physEmb (F := F) (m := m) (d := d) (D × A) * ancillaEmbed D a₀) = 1 :=
  isometry_mul_isometry physEmb_isometry (ancillaEmbed_isometry a₀)

/-- **It compresses an operator extended by the identity to the operator's compression by the
ancilla**: `(phi_0 N)^† (X ⊗ Id) (phi_0 N) = N^† X N`. -/
theorem physEmb_mul_ancillaEmbed_conj (a₀ : A) (X : Matrix (D × A) (D × A) ℂ) :
    (physEmb (F := F) (m := m) (d := d) (D × A) * ancillaEmbed D a₀)ᴴ
        * (aOp (aOp (aOp X)) : Matrix ((((D × A) × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1))
          × Anc F m) ((((D × A) × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) × Anc F m) ℂ)
        * (physEmb (F := F) (m := m) (d := d) (D × A) * ancillaEmbed D a₀)
      = ancCompress a₀ X := by
  conv_rhs => rw [ancCompress, ← physEmb_conj_aOp (F := F) (m := m) (d := d) X]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Embed

/-- **A state pushed through a pair of embeddings after the doubly padded state** is the original
state pushed through the composites. -/
theorem kronecker_mulVec_extVec2 {dA dB A B R S : Type*} [Fintype dA] [DecidableEq dA]
    [Fintype dB] [DecidableEq dB] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (EA : Matrix R (dA × A) ℂ) (EB : Matrix S (dB × B) ℂ) (ψ : dA × dB → ℂ) (a₀ : A) (b₀ : B) :
    (EA ⊗ₖ EB) *ᵥ extVec2 ψ a₀ b₀
      = ((EA * ancillaEmbed dA a₀) ⊗ₖ (EB * ancillaEmbed dB b₀)) *ᵥ ψ := by
  rw [extVec2, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul]

/-! ## The descent, at a `MirrorSimul` -/

section Mirror

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **Bob's conjugated Pauli measurement is projective**: a projective coarse-graining,
conjugated by the unitary `V_B`. Alice's is `isPVM_aliceConjPauli`. -/
theorem isPVM_bobConjPauli (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) :
    IsPVM (M.bobConjPauli W) :=
  isPVM_conj_unitary ((((isPVM_povm_map _ (hprojB _) rdPauliVec).aOp).aOp).aOp)
    M.bobSwap_conjTranspose_mul M.bobSwap_mul_conjTranspose

/-- **`thm:qld` at a `MirrorSimul`, for any pair of embeddings of an original space whose image
the physical state is.** Let `E_A`, `E_B` be isometries from spaces `K_A`, `K_B` into the two
physical registers with `M.physVec = (E_A ⊗ E_B) θ`, and let `P^A_{W,h}`, `P^B_{W,h}` be POVMs on
`K_A`, `K_B` that the strategy's total Pauli measurements compress to under `E_A`, `E_B`. Then with
`phi_A = V_A E_A`, `phi_B = V_B E_B` and the auxiliary state of the swap isometry lemma:

1. `phi_A ⊗ phi_B θ` is within `sqrt η` of `|aux> ⊗ |EPR_q>^M`;
2. `phi_A P^A_{W,h} phi_A^†` is within `deltaItemTwo + 8 sqrt η` of `Id ⊗ tau^W_h` on `A''` in the
   summed squared state-dependent distance relative to that product state, and likewise for Bob.

Item 1 is item 1 of `swap_isometry`, since `phi_A ⊗ phi_B θ` *is* the swapped physical state.
Item 2 is item 2 of `swap_isometry` carried down by the descent through agreement
(`sum_snorm_sq_descent_isometry_aOp`, `..._bOp`): conjugated by `phi_A`, the swap-conjugated
Pauli measurement compresses to `P^A_{W,h}` (`conj_mul_conj_unitary`), and that one identity makes
both the passage from `V`-conjugation to `phi`-conjugation and the one from the dilation to the
original measurement. -/
theorem exists_phys_descent {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hlt : 2 * Real.sqrt (deltaSelfCons δ ε m d (Fintype.card F))
      + 2 * deltaSelfCons δ ε m d (Fintype.card F) < 1)
    {KA KB : Type*} [Fintype KA] [DecidableEq KA] [Fintype KB] [DecidableEq KB]
    {θ : KA × KB → ℂ} (hθ : ‖evec θ‖ = 1)
    {EA : Matrix (((dA × Anc F m) × M.Ea) × Anc F m) KA ℂ}
    {EB : Matrix (((dB × Anc F m) × M.Eb) × Anc F m) KB ℂ}
    (hEA : EAᴴ * EA = 1) (hEB : EBᴴ * EB = 1) (hphys : M.physVec = (EA ⊗ₖ EB) *ᵥ θ)
    {PA : Bas → Anc F m → Matrix KA KA ℂ} {PB : Bas → Anc F m → Matrix KB KB ℂ}
    (hPA0 : ∀ W h, 0 ≤ PA W h) (hPA1 : ∀ W, ∑ h, PA W h = 1)
    (hPB0 : ∀ W h, 0 ≤ PB W h) (hPB1 : ∀ W, ∑ h, PB W h = 1)
    (hcompA : ∀ W h, EAᴴ * M.alicePauli W h * EA = PA W h)
    (hcompB : ∀ W h, EBᴴ * M.bobPauli W h * EB = PB W h) :
    ∃ aux : ((dA × Anc F m) × M.Ea) × ((dB × Anc F m) × M.Eb) → ℂ,
      (M.aliceSwap * EA)ᴴ * (M.aliceSwap * EA) = 1 ∧
      (M.bobSwap * EB)ᴴ * (M.bobSwap * EB) = 1 ∧ ‖evec aux‖ = 1 ∧
      ‖evec (((M.aliceSwap * EA) ⊗ₖ (M.bobSwap * EB)) *ᵥ θ
          - outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux))‖
        ≤ Real.sqrt (etaItemOne δ ε m d (Fintype.card F)) ∧
      ∀ W : Bas,
        ∑ h : Anc F m, snorm (outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux))
            (aOp (M.aliceSwap * EA * PA W h * (M.aliceSwap * EA)ᴴ - bOp (proj (weylOf W) h))) ^ 2
          ≤ deltaItemTwo δ ε m d (Fintype.card F) (etaItemOne δ ε m d (Fintype.card F))
            + 8 * Real.sqrt (etaItemOne δ ε m d (Fintype.card F)) ∧
        ∑ h : Anc F m, snorm (outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux))
            (bOp (M.bobSwap * EB * PB W h * (M.bobSwap * EB)ᴴ - bOp (proj (weylOf W) h))) ^ 2
          ≤ deltaItemTwo δ ε m d (Fintype.card F) (etaItemOne δ ε m d (Fintype.card F))
            + 8 * Real.sqrt (etaItemOne δ ε m d (Fintype.card F)) := by
  obtain ⟨aux, haux, hη, hW⟩ := M.swap_isometry (hm := hm) hψ hfail hprojA hprojB hd hδ hε hlt
  have hΔ : ‖evec (M.physAux aux)‖ = 1 := by rw [M.norm_evec_physAux, haux]
  have hΓ : ((M.aliceSwap * EA) ⊗ₖ (M.bobSwap * EB)) *ᵥ θ = M.physSwap *ᵥ M.physVec := by
    rw [hphys, MirrorSimul.physSwap, aOp_mul_bOp_mulVec_kronecker]
  have hr : ‖evec (((M.aliceSwap * EA) ⊗ₖ (M.bobSwap * EB)) *ᵥ θ - M.physAux aux)‖
      ≤ Real.sqrt (etaItemOne δ ε m d (Fintype.card F)) := by
    rw [hΓ, M.norm_evec_physSwap_sub_physAux]
    exact Real.le_sqrt_of_sq_le hη
  have hUA := isometry_mul_isometry M.aliceSwap_conjTranspose_mul hEA
  have hUB := isometry_mul_isometry M.bobSwap_conjTranspose_mul hEB
  refine ⟨aux, hUA, hUB, (norm_evec_auxVec aux).symm.trans haux, hr, fun W => ⟨?_, ?_⟩⟩
  · have h := sum_snorm_sq_descent_isometry_aOp hUA hUB hθ hΔ hr
      (M.isPVM_aliceConjPauli hprojA W) (hPA0 W) (hPA1 W)
      (fun h => by rw [aliceConjPauli, conj_mul_conj_unitary M.aliceSwap_conjTranspose_mul,
        hcompA]) (M.isPVM_bobTau W) (M.aliceTau_mulVec_physAux aux W) (hW W).1
    simp only [aOp_sub]
    exact h
  · have h := sum_snorm_sq_descent_isometry_bOp hUA hUB hθ hΔ hr
      (M.isPVM_bobConjPauli hprojB W) (hPB0 W) (hPB1 W)
      (fun h => by rw [bobConjPauli, conj_mul_conj_unitary M.bobSwap_conjTranspose_mul,
        hcompB]) (M.isPVM_aliceTau W) (fun h => (M.aliceTau_mulVec_physAux aux W h).symm) (hW W).2
    simp only [bOp_sub]
    exact h

end MirrorSimul

end Mirror

/-! ## Inside the regime -/

section Regime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **`thm:qld` inside the regime, in physical form.** For a POVM strategy of failure probability
at most `ε`, when `48 m d ≤ q` and `qldHlt < 1`, there are isometries `phi_A`, `phi_B` from the
original spaces into `H_A ⊗ (C^q)^M`, `H_B ⊗ (C^q)^M` (the half of the pair **last**) and a unit
`|aux>` on `H_A ⊗ H_B` such that

1. `phi_A ⊗ phi_B |psi>` is within `sqrt qldEta` of `|aux> ⊗ |EPR_q>^M`, and
2. for each basis `W`, `phi_A M^{(Pauli,W)}_h phi_A^†` is within `deltaItemTwo + 8 sqrt qldEta` of
   `Id ⊗ tau^W_h`, in the summed squared state-dependent distance relative to that product state,
   and likewise for Bob, where `M^{(Pauli,W)}_h` is the **original** strategy's coarse Pauli
   measurement.

The strategy is dilated and legalized (`exists_legal_dilation`); the dilation has both cuts'
simultaneous pair measurements on one state (`exists_globalPair` twice, `mirrorOfGlobalPairs`);
its physical state is the original state pushed through `phi_0 ∘ N`
(`physVec_mirrorOfGlobalPairs`, `kronecker_mulVec_extVec2`); and `phi_A = V_A ∘ phi_0 ∘ N`
compresses the swap-conjugated Pauli measurement to the original one
(`physEmb_mul_ancillaEmbed_conj`, then the dilation's compression). The rest is
`MirrorSimul.exists_phys_descent`. -/
theorem exists_phys_of_regime (hm : m ∣ Fintype.card F) (hd : 1 ≤ d) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : Question F m → POVM (Answer F m d) dA)
    (MB : Question F m → POVM (Answer F m d) dB) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F)
    (hlt : qldHlt ε m d (Fintype.card F) < 1) :
    ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB) (_ : DecidableEq HB)
      (φA : Matrix (HA × Anc F m) dA ℂ) (φB : Matrix (HB × Anc F m) dB ℂ) (aux : HA × HB → ℂ),
      φAᴴ * φA = 1 ∧ φBᴴ * φB = 1 ∧ ‖evec aux‖ = 1 ∧
      ‖evec ((φA ⊗ₖ φB) *ᵥ ψ - outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux))‖
        ≤ Real.sqrt (qldEta ε m d (Fintype.card F)) ∧
      ∀ W : Bas,
        ∑ h : Anc F m, snorm (outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux))
            (aOp (φA * (((MA (.pauli W)).map rdPauliVec).mats h).val * φAᴴ
              - bOp (proj (weylOf W) h))) ^ 2
          ≤ deltaItemTwo (qldDelta ε m d (Fintype.card F)) ε m d (Fintype.card F)
              (qldEta ε m d (Fintype.card F))
            + 8 * Real.sqrt (qldEta ε m d (Fintype.card F)) ∧
        ∑ h : Anc F m, snorm (outerUnVec (auxVec (F := F) (n := Fin m → Bool) aux))
            (bOp (φB * (((MB (.pauli W)).map rdPauliVec).mats h).val * φBᴴ
              - bOp (proj (weylOf W) h))) ^ 2
          ≤ deltaItemTwo (qldDelta ε m d (Fintype.card F)) ε m d (Fintype.card F)
              (qldEta ε m d (Fintype.card F))
            + 8 * Real.sqrt (qldEta ε m d (Fintype.card F)) := by
  obtain ⟨MA', MB', hpA, hpB, hlA, hlB, hfail', hcA, hcB⟩ :=
    exists_legal_dilation hm ψ MA MB hfail (.pauliAns 0 : Answer F m d)
  have hψ' := extVec2_unit hψ (.pauliAns 0 : Answer F m d) (.pauliAns 0 : Answer F m d)
  have hm4 := four_mul_dvd_card_of_regime hm hd hq
  obtain ⟨P⟩ := exists_globalPair hm hm4 hψ' hfail' hpA hpB hε hlA hlB hd
  obtain ⟨P'⟩ := exists_globalPair hm hm4 (swapVec_unit hψ') (povmValue_swapped_le hfail')
    hpB hpA hε hlB hlA hd
  have hphys := physVec_mirrorOfGlobalPairs hm P P' hd hψ' hfail' hq
  rw [kronecker_mulVec_extVec2] at hphys
  obtain ⟨aux, hUA, hUB, haux, hr, hW⟩ :=
    (mirrorOfGlobalPairs hm P P' hd hψ' hfail' hq).exists_phys_descent (hm := hm) hψ' hfail'
      hpA hpB hd (qldDelta_nonneg hε m d _) hε hlt (norm_evec_eq_one_of_unit hψ)
      (physEmb_mul_ancillaEmbed_isometry _) (physEmb_mul_ancillaEmbed_isometry _) hphys
      (PA := fun W h => (((MA (.pauli W)).map rdPauliVec).mats h).val)
      (PB := fun W h => (((MB (.pauli W)).map rdPauliVec).mats h).val)
      (fun W h => ((MA (.pauli W)).map rdPauliVec).nonneg h)
      (fun W => ((MA (.pauli W)).map rdPauliVec).sum_val)
      (fun W h => ((MB (.pauli W)).map rdPauliVec).nonneg h)
      (fun W => ((MB (.pauli W)).map rdPauliVec).sum_val)
      (fun W h => (physEmb_mul_ancillaEmbed_conj _ _).trans (hcA W h))
      (fun W h => (physEmb_mul_ancillaEmbed_conj _ _).trans (hcB W h))
  exact ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _, aux, hUA, hUB,
    haux, hr, hW⟩

end Regime

/-! ## The trivial bounds, in the register-first form -/

section Trivial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m] {HA HB dA dB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
  [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **Item 1's trivial bound**: for any pair of isometries and any unit `aux`, the distance is at
most `2`, both states being unit vectors. -/
theorem norm_isometricState_sub_registerState_le_two {VA : Matrix (Anc F m × HA) dA ℂ}
    {VB : Matrix (Anc F m × HB) dB ℂ} (hVA : VAᴴ * VA = 1) (hVB : VBᴴ * VB = 1)
    {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {aux : HA × HB → ℂ} (haux : ‖evec aux‖ = 1) :
    ‖evec (isometricState VA VB ψ - registerState (Anc F m) aux)‖ ≤ 2 :=
  norm_evec_sub_le_two ((isometricState_norm VA VB hVA hVB ψ).trans hψ)
    (registerState_norm aux haux)

/-- **Item 2's trivial bound, Alice's half**: for any isometry and any POVM, the summed squared
distance of the conjugated POVM from the honest projectors on the register is at most `2`. On
`registerState` the honest projector on Alice's register acts as the same projector on Bob's
(`registerState_move`), so this is the descent's trivial bound
(`sum_snorm_sq_aOp_sub_aOp_le_two`): twice the disagreement of a sub-POVM with a projective
measurement. -/
theorem sum_snorm_sq_registerState_alice_le_two {VA : Matrix (Anc F m × HA) dA ℂ}
    (hVA : VAᴴ * VA = 1) {aux : HA × HB → ℂ} (haux : ‖evec aux‖ = 1)
    {P : Anc F m → Matrix dA dA ℂ} (hP0 : ∀ h, 0 ≤ P h) (hP1 : ∑ h, P h = 1) (W : Bas) :
    ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
        (aOp (isometricImage VA (P h) - aOp (proj (weylOf W) h))) ^ 2 ≤ 2 := by
  obtain ⟨hX0, hX1⟩ := conj_isometry_subPOVM hVA hP0 hP1
  simp only [aOp_sub]
  exact sum_snorm_sq_aOp_sub_aOp_le_two (registerState_norm aux haux) hX0 hX1
    (isPVM_proj (isWeylFamily_weylOf W)).aOp
    fun h => registerState_move aux (weylOf_transpose W) h

/-- **Item 2's trivial bound, Bob's half.** -/
theorem sum_snorm_sq_registerState_bob_le_two {VB : Matrix (Anc F m × HB) dB ℂ}
    (hVB : VBᴴ * VB = 1) {aux : HA × HB → ℂ} (haux : ‖evec aux‖ = 1)
    {Q : Anc F m → Matrix dB dB ℂ} (hQ0 : ∀ h, 0 ≤ Q h) (hQ1 : ∑ h, Q h = 1) (W : Bas) :
    ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
        (bOp (isometricImage VB (Q h) - aOp (proj (weylOf W) h))) ^ 2 ≤ 2 := by
  obtain ⟨hX0, hX1⟩ := conj_isometry_subPOVM hVB hQ0 hQ1
  simp only [bOp_sub]
  exact sum_snorm_sq_bOp_sub_bOp_le_two (registerState_norm aux haux) hX0 hX1
    (isPVM_proj (isWeylFamily_weylOf W)).aOp
    fun h => (registerState_move aux (weylOf_transpose W) h).symm

end Trivial

/-! ## The assembly -/

section Assembly

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **`thm:qld` with its error named**: both items at most `qldErr ε m d q`, for a POVM strategy
of failure probability at most `ε`. Inside the regime (`48 m d ≤ q` and `qldHlt < 1`) the
isometries are `exists_phys_of_regime`'s with the register moved to the front (`regFirst`), and
`RegisterForm` reads the consumer's quantities as the physical ones; each item is also at most the
trivial bound `2`, so at most `min qldBound 4`. Outside it `qldErr = 4` and the isometries are the
inert ancilla `ψ ↦ |0> ⊗ ψ`, with `aux = ψ`: the trivial bounds suffice. -/
theorem exists_le_qldErr (hm : m ∣ Fintype.card F) (hd : 1 ≤ d) {ψ : dA × dB → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (MA : Question F m → POVM (Answer F m d) dA)
    (MB : Question F m → POVM (Answer F m d) dB) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB) (_ : DecidableEq HB)
      (VA : Matrix (Anc F m × HA) dA ℂ) (VB : Matrix (Anc F m × HB) dB ℂ) (aux : HA × HB → ℂ),
      VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ ‖evec aux‖ = 1 ∧
      ‖evec (isometricState VA VB ψ - registerState (Anc F m) aux)‖
        ≤ qldErr ε m d (Fintype.card F) ∧
      ∀ W : Bas,
        ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
            (aOp (isometricImage VA (((MA (.pauli W)).map rdPauliVec).mats h).val
              - aOp (proj (weylOf W) h))) ^ 2
          ≤ qldErr ε m d (Fintype.card F) ∧
        ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
            (bOp (isometricImage VB (((MB (.pauli W)).map rdPauliVec).mats h).val
              - aOp (proj (weylOf W) h))) ^ 2
          ≤ qldErr ε m d (Fintype.card F) := by
  have hψn := norm_evec_eq_one_of_unit hψ
  by_cases hreg : 48 * m * d ≤ Fintype.card F ∧ qldHlt ε m d (Fintype.card F) < 1
  · obtain ⟨HA, HB, i1, i2, i3, i4, φA, φB, aux, hA, hB, haux, h1, h2⟩ :=
      exists_phys_of_regime hm hd hψ MA MB hε hfail hreg.1 hreg.2
    have hA' := regFirst_isometry hA
    have hB' := regFirst_isometry hB
    refine ⟨HA, HB, i1, i2, i3, i4, regFirst φA, regFirst φB, aux, hA', hB', haux, ?_,
      fun W => ⟨?_, ?_⟩⟩
    · refine le_qldErr ((norm_isometricState_sub_registerState_le_two hA' hB' hψn haux).trans
        (by norm_num)) fun _ _ => ?_
      rw [norm_isometricState_sub_registerState]
      exact h1.trans (sqrt_qldEta_le_qldBound hε _ _ _)
    · refine le_qldErr ((sum_snorm_sq_registerState_alice_le_two hA' haux
        (fun h => ((MA (.pauli W)).map rdPauliVec).nonneg h)
        ((MA (.pauli W)).map rdPauliVec).sum_val W).trans (by norm_num)) fun _ _ => ?_
      simp only [snorm_registerState_alice]
      exact (h2 W).1.trans (itemTwo_le_qldBound _ _ _ _)
    · refine le_qldErr ((sum_snorm_sq_registerState_bob_le_two hB' haux
        (fun h => ((MB (.pauli W)).map rdPauliVec).nonneg h)
        ((MB (.pauli W)).map rdPauliVec).sum_val W).trans (by norm_num)) fun _ _ => ?_
      simp only [snorm_registerState_bob]
      exact (h2 W).2.trans (itemTwo_le_qldBound _ _ _ _)
  · rw [qldErr_of_not hreg]
    have hA' := regFirst_isometry (ancillaEmbed_isometry (d := dA) (0 : Anc F m))
    have hB' := regFirst_isometry (ancillaEmbed_isometry (d := dB) (0 : Anc F m))
    refine ⟨dA, dB, inferInstance, inferInstance, inferInstance, inferInstance, _, _, ψ, hA', hB',
      hψn, (norm_isometricState_sub_registerState_le_two hA' hB' hψn hψn).trans (by norm_num),
      fun W => ⟨?_, ?_⟩⟩
    · exact (sum_snorm_sq_registerState_alice_le_two hA' hψn
        (fun h => ((MA (.pauli W)).map rdPauliVec).nonneg h)
        ((MA (.pauli W)).map rdPauliVec).sum_val W).trans (by norm_num)
    · exact (sum_snorm_sq_registerState_bob_le_two hB' hψn
        (fun h => ((MB (.pauli W)).map rdPauliVec).nonneg h)
        ((MB (.pauli W)).map rdPauliVec).sum_val W).trans (by norm_num)

end Assembly

/-- **`thm:qld`: soundness of the Pauli basis test** (the paper's `thm:pauli-appendix`). There are
universal constants `a ≥ 1` and `0 < b < 1` such that for every admissible `(q, m, d)` (a field of
characteristic two with `m | q`, and `d ≥ 1`) and **every** POVM strategy `(ψ, M_A, M_B)` of the
Pauli basis test that fails with probability at most `ε`, there are local isometries
`V_A : C^{d_A} → (C^q)^M ⊗ H_A`, `V_B : C^{d_B} → (C^q)^M ⊗ H_B` (the register first) and a unit
state `|aux>` on `H_A ⊗ H_B` such that, with `δ = a (md)^a (ε^b + q^{-b} + 2^{-bmd})`,

1. `‖(V_A ⊗ V_B) |ψ> - |EPR_q>^M ⊗ |aux>‖ ≤ δ`, and
2. for each basis `W ∈ {X, Z}`, the strategy's own `(Pauli, W)` measurement, read as cube data
   and conjugated by the party's isometry, is `δ`-close to the honest Pauli basis measurement
   `tau^W_h` on that party's register, in the summed squared state-dependent distance relative
   to `|EPR_q>^M ⊗ |aux>` --- for Alice and for Bob, with the one `|aux>`.

The constants are those of `exists_qldErr_le`, fixed before anything else. The failure bound is
taken at `min ε 1`, which is still a failure bound because a value is nonnegative
(`povmValue_nonneg`), and the rest is `exists_le_qldErr`. -/
theorem qld_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
        [NeZero m] (hm : m ∣ Fintype.card F), 1 ≤ d →
      ∀ {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
        (ψ : dA × dB → ℂ), star ψ ⬝ᵥ ψ = 1 →
      ∀ (MA : Question F m → POVM (Answer F m d) dA)
        (MB : Question F m → POVM (Answer F m d) dB) {ε : ℝ}, 0 ≤ ε →
        1 - povmValue (qldGame hm) ψ MA MB ≤ ε →
      ∃ (HA HB : Type) (_ : Fintype HA) (_ : DecidableEq HA) (_ : Fintype HB)
        (_ : DecidableEq HB) (VA : Matrix (Anc F m × HA) dA ℂ) (VB : Matrix (Anc F m × HB) dB ℂ)
        (aux : HA × HB → ℂ),
        VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ ‖evec aux‖ = 1 ∧
        ‖evec (isometricState VA VB ψ - registerState (Anc F m) aux)‖
          ≤ errShape a b ε m d (Fintype.card F) ∧
        ∀ W : Bas,
          ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
              (aOp (isometricImage VA (((MA (.pauli W)).map rdPauliVec).mats h).val
                - aOp (proj (weylOf W) h))) ^ 2
            ≤ errShape a b ε m d (Fintype.card F) ∧
          ∑ h : Anc F m, snorm (registerState (Anc F m) aux)
              (bOp (isometricImage VB (((MB (.pauli W)).map rdPauliVec).mats h).val
                - aOp (proj (weylOf W) h))) ^ 2
            ≤ errShape a b ε m d (Fintype.card F) := by
  obtain ⟨a, b, ha, hb0, hb1, hab⟩ := exists_qldErr_le
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro F _ _ _ _ m d _ hm hd dA dB _ _ _ _ ψ hψ MA MB ε hε hfail
  have hle := hab ε m d (Fintype.card F) hε NeZero.one_le hd two_le_card_field
  have hfail' : 1 - povmValue (qldGame hm) ψ MA MB ≤ min ε 1 :=
    le_min hfail (by linarith [povmValue_nonneg (qldGame hm) ψ MA MB])
  obtain ⟨HA, HB, i1, i2, i3, i4, VA, VB, aux, hA, hB, haux, h1, h2⟩ :=
    exists_le_qldErr hm hd hψ MA MB (le_min hε zero_le_one) hfail'
  exact ⟨HA, HB, i1, i2, i3, i4, VA, VB, aux, hA, hB, haux, h1.trans hle,
    fun W => ⟨(h2 W).1.trans hle, (h2 W).2.trans hle⟩⟩

end MIPRE.QLD

end
