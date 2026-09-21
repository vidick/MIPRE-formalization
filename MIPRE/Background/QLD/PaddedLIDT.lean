/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.PaddedValue
import MIPRE.Background.QLD.Simul
import MIPRE.Background.QLD.Dummy
import MIPRE.Background.QLD.Products
import MIPRE.Background.LIDT.Adapter.Registers

/-!
# The global polynomial measurements: applying the seeded soundness theorem

`lem:qld-global-pvm`. By `lem:qld-global-success` (`padStrat_value`), the padded strategy
`(extHat ψ, padStrat hprojA, padStrat hprojB)` wins the seeded low individual degree test at
`(q, 4m, d, 1)` with probability at least `1 - δ_GS`, where
`δ_GS = 5 m² δ_P(ε, md/q + 1/q) + 4 δ_Q(ε) + (md + 1)/q`. This file feeds it to
`clSoundness_ldc_one_deltaCL_of_povm`, the seeded soundness theorem for POVM strategies, and reads
the conclusion back in the form stages 4b and 4c consume. It is the one module of the Pauli basis
test's analysis that reaches the vendored MIPStarRE tree.

## What the theorem returns

The soundness theorem dilates the padded strategy projectively (`lem:naimark-dilation`), which
adjoins to each party one more ancilla, indexed by the test's answers and prepared in the zero
answer `ansZero`. The two low-degree measurements `GA`, `GB` it produces are projective on the
dilated registers `PadReg`, and its three consistency estimates hold on the twice-padded state
`padState ψ = extVec2 (extHat ψ) ansZero ansZero`, against the dilation's own point measurements.
Those compress to the padded strategy's (`padStrat_point_map_toValue`), whose operators are the
expanded sandwich combinations `ptComb (sand M̂^X M̂^Z) α β`, extended by the identity
(`padPt_mats`).

## Why no further dilation is needed

On a product state `extVec2 Ψ a₀ b₀` the Born probability of `X ⊗ E` depends on `E` only through
its compression by `|b₀⟩` (`bornProb_extVec2_ancCompress`). The dilation's point measurement and
the padded strategy's own point measurement extended by the identity on the answer ancilla have
the same compression, so every consistency estimate against the former is the same number against
the latter (`inconsistency_padState_aOp_right`). The final form, `exists_global_pvm_hat`,
therefore mentions no dilation: it is a pair of projective measurements `GA`, `GB` on the two
`PadReg` registers whose evaluated marginals are consistent, on `padState ψ`, with the *original*
strategy's expanded sandwich combinations, doubly extended; and every expectation of a doubly
extended operator on `padState ψ` is its expectation on `hatVec ψ`
(`bornProb_padState_aOp_aOp`), so the conclusions of stages 2 and 3 transfer.

## The error

`δ_ld = deltaLD q m d ε = deltaCL q (4m) d (deltaGS q m d ε)`: the soundness theorem's error at
`(q, 4m, d, 1)` for a strategy of value `1 - δ_GS`. It is of the blueprint's displayed form
`A (md)^A ((δ_GS)^b + q^{-b} + 2^{-bmd})`, since `(4md)^A = 4^A (md)^A` and
`2^{-4bmd} ≤ 2^{-bmd}`.

The recovered polynomials live on `F^{4m}`, while the point measurements read only the `2m + 2`
coordinates `xBlk`, `zBlk`, `alph`, `bet`. The Schwartz--Zippel argument that the polynomials
mostly do not read the remaining dummy coordinates is `MIPRE/Background/QLD/Dummy.lean`;
`exists_global_pvm_wIndep` is `lem:qld-global-dummy` for the measurements produced here.
-/

noncomputable section

namespace MIPRE

section CompressAOp

variable {A d E : Type*} [Fintype A] [Fintype d] [DecidableEq d] [Fintype E] [DecidableEq E]

/-- Compressing an extension by the identity recovers the POVM. -/
theorem POVM.compress_aOp (a₀ : E) (M : POVM A d) : (M.aOp (E := E)).compress a₀ = M :=
  POVM.ext' fun a => by rw [POVM.compress_mats, POVM.aOp_mats, ancCompress, MIPRE.compress_aOp]

end CompressAOp

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.Adapter
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The zero answer to the seeded test at `(q, 4m, d, 1)`: the ancilla vector of the projective
dilation. -/
def ansZero : CL.Answer F (4 * m) d 1 := CL.Answer.values fun _ => 0

/-- A party's register after the projective dilation of the padded strategy: the expanded
register, the combining ancilla `F × F`, and the answer ancilla. -/
abbrev PadReg (F : Type*) (m d : ℕ) (dA : Type) :=
  ((dA × Anc F m) × (F × F)) × CL.Answer F (4 * m) d 1

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- Decidable equality on the dilated register. The default synthesis size limit misses it on
the five-fold product, so the two halves are assembled by hand. -/
instance instDecidableEqPadReg : DecidableEq (PadReg F m d dA) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

instance instFintypePadReg : Fintype (PadReg F m d dA) := instFintypeProd _ _

/-- **The twice-padded state**: the expanded state with the combining ancillas in `|0, 0⟩` and the
answer ancillas in `|ansZero⟩`. -/
def padState (ψ : dA × dB → ℂ) : PadReg F m d dA × PadReg F m d dB → ℂ :=
  extVec2 (extHat (F := F) (m := m) ψ) ansZero ansZero

theorem padState_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (padState (F := F) (m := m) (d := d) ψ) ⬝ᵥ padState (F := F) (m := m) (d := d) ψ = 1 :=
  extVec2_unit (extVec2_unit (hatVec_unit hψ) _ _) _ _

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **Doubly extended operators have on the twice-padded state the expectation they have on the
expanded state**: the conclusions of stages 2 and 3 transfer to `padState ψ`. -/
theorem bornProb_padState_aOp_aOp (ψ : dA × dB → ℂ) (X : Matrix (dA × Anc F m) (dA × Anc F m) ℂ)
    (Y : Matrix (dB × Anc F m) (dB × Anc F m) ℂ) :
    bornProb (padState (F := F) (m := m) (d := d) ψ) (aOp (aOp X)) (aOp (aOp Y))
      = bornProb (hatVec (F := F) (m := m) ψ) X Y := by
  rw [padState, bornProb_extVec2_aOp_aOp, extHat, bornProb_extVec2_aOp_aOp]

/-- The padded point measurement, extended to the dilated register: the expanded sandwich
combination, doubly extended. -/
theorem padPt_aOp_mats {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) (a : F) :
    ((((padPt hM u).aOp (E := CL.Answer F (4 * m) d 1)).mats a).val)
      = aOp (aOp (ptComb (sand (hatMats M .X (xBlk u)) (hatMats M .Z (zBlk u))) (alph u) (bet u)
          a)) := by
  rw [POVM.aOp_mats, padPt_mats]

/-! ## Replacing the dilation's measurements by their compressions' extensions -/

section Replace

variable {X : Type*} [Fintype X]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- On the twice-padded state, a POVM on Bob's dilated register may be replaced by the identity
extension of any POVM with the same compression. -/
theorem inconsistency_padState_aOp_right (μ : X → ℝ) (ψ : dA × dB → ℂ)
    (M : X → POVM F (PadReg F m d dA)) (N : X → POVM F ((dB × Anc F m) × (F × F)))
    (P : X → POVM F (PadReg F m d dB)) (h : ∀ x, (P x).compress ansZero = N x) :
    inconsistency μ (padState (F := F) (m := m) (d := d) ψ) M
        (fun x => (N x).aOp (E := CL.Answer F (4 * m) d 1))
      = inconsistency μ (padState (F := F) (m := m) (d := d) ψ) M P := by
  rw [padState, inconsistency_extVec2, inconsistency_extVec2]
  simp only [POVM.compress_aOp, h]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- On the twice-padded state, a POVM on Alice's dilated register may be replaced by the identity
extension of any POVM with the same compression. -/
theorem inconsistency_padState_aOp_left (μ : X → ℝ) (ψ : dA × dB → ℂ)
    (N : X → POVM F ((dA × Anc F m) × (F × F))) (M : X → POVM F (PadReg F m d dB))
    (P : X → POVM F (PadReg F m d dA)) (h : ∀ x, (P x).compress ansZero = N x) :
    inconsistency μ (padState (F := F) (m := m) (d := d) ψ)
        (fun x => (N x).aOp (E := CL.Answer F (4 * m) d 1)) M
      = inconsistency μ (padState (F := F) (m := m) (d := d) ψ) P M := by
  rw [padState, inconsistency_extVec2, inconsistency_extVec2]
  simp only [POVM.compress_aOp, h]

end Replace

/-! ## The errors -/

/-- **`δ_GS`**, the error of `lem:qld-global-success`: the padded strategy's failure probability
in the seeded test at `(q, 4m, d, 1)`. -/
def deltaGS (q m d : ℕ) (ε : ℝ) : ℝ :=
  5 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / q + (q : ℝ)⁻¹)) + 4 * deltaQ ε
    + ((m : ℝ) * d + 1) / q

/-- **`δ_ld`**: the seeded soundness theorem's error at `(q, 4m, d, 1)` for a strategy of value
`1 - δ_GS`. -/
def deltaLD (q m d : ℕ) (ε : ℝ) : ℝ := deltaCL q (4 * m) d (deltaGS q m d ε)

theorem deltaGS_nonneg {q m d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ deltaGS q m d ε := by
  unfold deltaGS deltaPairs deltaPairsD kappaPairs deltaQ
  positivity

/-! ## The lemma -/

section Global

variable (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ψ : dA × dB → ℂ} {ε : ℝ}

include hm4 in
/-- **`lem:qld-global-pvm`, as the soundness theorem returns it.** For a legal projective strategy
of the Pauli basis test of value `1 - ε`: projective dilations `PA`, `PB` of the padded strategy,
whose point measurements compress to the padded point measurements, and projective low-degree
measurements `GA`, `GB` on the dilated registers, with the two point-consistency estimates and the
full-polynomial consistency on the twice-padded state, all with error `δ_ld`. -/
theorem exists_global_pvm (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hε : 0 ≤ ε)
    (hlegA : LegalSupport MA) (hlegB : LegalSupport MB) (hd : 1 ≤ d) :
    ∃ (PA : ProjectiveMeasurement (CL.Question F (4 * m)) (CL.Answer F (4 * m) d 1)
          (Matrix (PadReg F m d dA) (PadReg F m d dA) ℂ))
      (PB : ProjectiveMeasurement (CL.Question F (4 * m)) (CL.Answer F (4 * m) d 1)
          (Matrix (PadReg F m d dB) (PadReg F m d dB) ℂ))
      (GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadReg F m d dA) (PadReg F m d dA) ℂ))
      (GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadReg F m d dB) (PadReg F m d dB) ℂ)),
      (∀ u, (pointPOVM PA u).compress ansZero = padPt hprojA u)
      ∧ (∀ u, (pointPOVM PB u).compress ansZero = padPt hprojB u)
      ∧ inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
          (pointPOVM PA) (evalPOVM GB) ≤ deltaLD (Fintype.card F) m d ε
      ∧ inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
          (evalPOVM GA) (pointPOVM PB) ≤ deltaLD (Fintype.card F) m d ε
      ∧ inconsistency (uniform Unit) (padState (F := F) (m := m) (d := d) ψ)
          (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) ≤ deltaLD (Fintype.card F) m d ε := by
  have hval := padStrat_value hm hm4 hψ hfail hprojA hprojB hε hlegA hlegB hd
  have hΨ : star (extHat (F := F) (m := m) ψ) ⬝ᵥ extHat (F := F) (m := m) ψ = 1 :=
    extVec2_unit (hatVec_unit hψ) _ _
  have hS : 1 - deltaGS (Fintype.card F) m d ε
      ≤ povmValue (CL.clGame (d := d) (ldc := 1) hm4) (extHat (F := F) (m := m) ψ)
        (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB) := by
    unfold deltaGS
    linarith
  obtain ⟨PA, PB, GA, GB, hPA, hPB, h1, h2, h3⟩ :=
    clSoundness_ldc_one_deltaCL_of_povm (hm := hm4) (extHat (F := F) (m := m) ψ) hΨ
      (padStrat hm hm4 hprojA) (padStrat hm hm4 hprojB) _ (deltaGS_nonneg hε) hS
      (by have := NeZero.pos m; omega) hd
  refine ⟨PA, PB, GA, GB, fun u => ?_, fun u => ?_, h1, h2, h3⟩
  · rw [pointPOVM, POVM.map_compress, ansZero, hPA, padStrat_point_map_toValue]
  · rw [pointPOVM, POVM.map_compress, ansZero, hPB, padStrat_point_map_toValue]

include hm4 in
/-- **`lem:qld-global-pvm`.** For a legal projective strategy of the Pauli basis test of value
`1 - ε`: projective low-degree measurements `GA`, `GB` on the two dilated registers, whose evaluated
marginals are consistent, on the twice-padded state and on average over a uniform point of
`F^{4m}`, with the opposite party's expanded sandwich combinations extended by the identity, and
which are consistent with each other, all with error `δ_ld`. No dilation appears in the
statement. -/
theorem exists_global_pvm_hat (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hε : 0 ≤ ε)
    (hlegA : LegalSupport MA) (hlegB : LegalSupport MB) (hd : 1 ≤ d) :
    ∃ (GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadReg F m d dA) (PadReg F m d dA) ℂ))
      (GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
          (Matrix (PadReg F m d dB) (PadReg F m d dB) ℂ)),
      inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
          (fun u => (padPt hprojA u).aOp (E := CL.Answer F (4 * m) d 1)) (evalPOVM GB)
        ≤ deltaLD (Fintype.card F) m d ε
      ∧ inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
          (evalPOVM GA) (fun u => (padPt hprojB u).aOp (E := CL.Answer F (4 * m) d 1))
        ≤ deltaLD (Fintype.card F) m d ε
      ∧ inconsistency (uniform Unit) (padState (F := F) (m := m) (d := d) ψ)
          (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) ≤ deltaLD (Fintype.card F) m d ε := by
  obtain ⟨PA, PB, GA, GB, hPA, hPB, h1, h2, h3⟩ :=
    exists_global_pvm hm hm4 hψ hfail hprojA hprojB hε hlegA hlegB hd
  refine ⟨GA, GB, ?_, ?_, h3⟩
  · rw [inconsistency_padState_aOp_left _ ψ _ _ (pointPOVM PA) hPA]
    exact h1
  · rw [inconsistency_padState_aOp_right _ ψ _ _ (pointPOVM PB) hPB]
    exact h2

/-! ## The output of the lemma, as a structure -/

/-- **The output of `lem:qld-global-pvm`, as a structure**: the two projective low-degree
measurements on the dilated registers, the two point consistencies against the opposite party's
padded point measurements (extended by the identity), and their mutual consistency, all on the
twice-padded state and with error `δ`. Stages 4b and 4c are theorems about a `GlobalPair`. -/
structure GlobalPair (ψ : dA × dB → ℂ) (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (δ : ℝ) where
  /-- Alice's global measurement. -/
  GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
    (Matrix (PadReg F m d dA) (PadReg F m d dA) ℂ)
  /-- Bob's global measurement. -/
  GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
    (Matrix (PadReg F m d dB) (PadReg F m d dB) ℂ)
  /-- Alice's padded points against Bob's evaluated global measurement. -/
  consA : inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
    (fun u => (padPt hprojA u).aOp (E := CL.Answer F (4 * m) d 1)) (evalPOVM GB) ≤ δ
  /-- Alice's evaluated global measurement against Bob's padded points. -/
  consB : inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
    (evalPOVM GA) (fun u => (padPt hprojB u).aOp (E := CL.Answer F (4 * m) d 1)) ≤ δ
  /-- The two global measurements against each other. -/
  consAB : inconsistency (uniform Unit) (padState (F := F) (m := m) (d := d) ψ)
    (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) ≤ δ

include hm4 in
/-- **`lem:qld-global-pvm`**, packaged: a legal projective strategy of value `1 - ε` has a
`GlobalPair` with error `δ_ld`. -/
theorem exists_globalPair (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hε : 0 ≤ ε)
    (hlegA : LegalSupport MA) (hlegB : LegalSupport MB) (hd : 1 ≤ d) :
    Nonempty (GlobalPair ψ hprojA hprojB (deltaLD (Fintype.card F) m d ε)) := by
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    exists_global_pvm_hat hm hm4 hψ hfail hprojA hprojB hε hlegA hlegB hd
  exact ⟨⟨GA, GB, h1, h2, h3⟩⟩

end Global

/-! ## The expanded point measurements on the dilated registers -/

section Lift

variable {d' : Type} [Fintype d'] [DecidableEq d']

/-- A party's expanded point measurement, doubly extended to the dilated register. -/
def liftOp (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (a : F) :
    Matrix (PadReg F m d d') (PadReg F m d d') ℂ :=
  aOp (aOp (hatMats M W u a))

theorem isPVM_liftOp {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (W : Bas) (u : Point F m) :
    IsPVM (liftOp M W u) :=
  (isPVM_hatMats hM W u).aOp.aOp

/-- The sandwich combination of the lifted measurements is the lifted padded point measurement. -/
theorem sandComb_liftOp (M : Question F m → POVM (Answer F m d) d') (u : Point F (4 * m)) (c : F) :
    sandComb (liftOp M .X) (liftOp M .Z) u c
      = aOp (aOp (ptComb (sand (hatMats M .X (xBlk u)) (hatMats M .Z (zBlk u))) (alph u) (bet u)
          c)) := by
  simp only [sandComb, ptComb, sand, liftOp, ← aOp_mul, ← aOp_sum]

theorem comm_liftOp (M : Question F m → POVM (Answer F m d) d') (x z : Point F m) (p : F × F) :
    comm (liftOp M .X x) (liftOp M .Z z) p = aOp (aOp (hatComm M x z p.1 p.2)) := by
  simp only [comm, liftOp, hatComm, ← aOp_mul, ← aOp_sub]

end Lift

/-! ## Norms on the twice-padded state -/

section Norms

variable (ψ : dA × dB → ℂ)

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem normSq_stateVecB_padState_aOp_aOp (C : Matrix (dB × Anc F m) (dB × Anc F m) ℂ) :
    ‖stateVecB (padState (F := F) (m := m) (d := d) ψ) (aOp (aOp C))‖ ^ 2
      = ‖stateVecB (hatVec (F := F) (m := m) ψ) C‖ ^ 2 := by
  rw [padState, normSq_stateVecB_extVec2_aOp, extHat, normSq_stateVecB_extVec2_aOp]

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem stateSqNorm_padState_aOp_aOp (C : Matrix (dA × Anc F m) (dA × Anc F m) ℂ) :
    stateSqNorm (padState (F := F) (m := m) (d := d) ψ) (aOp (aOp C))
      = stateSqNorm (hatVec (F := F) (m := m) ψ) C := by
  rw [padState, stateSqNorm_extVec2_aOp, extHat, stateSqNorm_extVec2_aOp]

theorem swapVec_padState_unit (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (swapVec (padState (F := F) (m := m) (d := d) ψ))
      ⬝ᵥ swapVec (padState (F := F) (m := m) (d := d) ψ) = 1 := by
  rw [swapVec_dotProduct]
  exact padState_unit hψ

end Norms

/-! ## The commutator weights of the two strategies, on the twice-padded state -/

section Comm

variable (hm : m ∣ Fintype.card F) {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ψ : dA × dB → ℂ} {ε : ℝ}

/-- Bob's commutator weight, from `lem:qld-combined-points`. -/
theorem sum_comm_liftOp_B_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z) * ∑ p : F × F,
        ‖stateVecB (padState (F := F) (m := m) (d := d) ψ)
          (comm (liftOp MB .X x) (liftOp MB .Z z) p)‖ ^ 2
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le_B (MA := MA) hψ hfail
  rw [sum_content_blocks (fun x z => ∑ p : F × F,
    ‖stateVecB (hatVec (F := F) (m := m) ψ) (hatComm MB x z p.1 p.2)‖ ^ 2)] at h
  simpa only [comm_liftOp, normSq_stateVecB_padState_aOp_aOp] using h

/-- Alice's commutator weight, read on the swapped padded state. -/
theorem sum_comm_liftOp_A_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z) * ∑ p : F × F,
        ‖stateVecB (swapVec (padState (F := F) (m := m) (d := d) ψ))
          (comm (liftOp MA .X x) (liftOp MA .Z z) p)‖ ^ 2
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le (MB := MB) hψ hfail
  rw [sum_content_blocks (fun x z => ∑ p : F × F,
    stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm MA x z p.1 p.2))] at h
  have hn : ∀ (x z : Point F m) (p : F × F),
      ‖stateVecB (swapVec (padState (F := F) (m := m) (d := d) ψ))
        (comm (liftOp MA .X x) (liftOp MA .Z z) p)‖ ^ 2
      = stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm MA x z p.1 p.2) := by
    intro x z p
    rw [norm_stateVecB, swapVec_swapVec, comm_liftOp, ← stateSqNorm, stateSqNorm_padState_aOp_aOp]
  simpa only [hn] using h

end Comm

/-! ## Stage 4b, on a `GlobalPair` -/

namespace GlobalPair

variable {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ψ : dA × dB → ℂ} {hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)}
  {hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)} {δ : ℝ}
  (P : GlobalPair ψ hprojA hprojB δ)

/-- **`lem:qld-global-dummy` for Alice's global measurement**: under `16 m d ≤ q`, the outcomes
that read a dummy coordinate weigh at most `4δ`. -/
theorem sum_bad_mass_A_le (hψ : star ψ ⬝ᵥ ψ = 1) (hq : 16 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ WIndep g),
      bornProb (padState (F := F) (m := m) (d := d) ψ) (P.GA.M () g) 1 ≤ 4 * δ := by
  have hP : ∀ u u' : Point F (4 * m),
      (padPt hprojB (mix u u')).aOp (E := CL.Answer F (4 * m) d 1)
        = (padPt hprojB u).aOp (E := CL.Answer F (4 * m) d 1) := fun u u' => by
    rw [padPt_mix]
  exact sum_bad_mass_le_of_le (padState_unit hψ) P.GA
    (fun u => (padPt hprojB u).aOp (E := CL.Answer F (4 * m) d 1)) hP P.consB hq

/-- **`lem:qld-global-dummy` for Bob's global measurement.** -/
theorem sum_bad_mass_B_le (hψ : star ψ ⬝ᵥ ψ = 1) (hq : 16 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ WIndep g),
      bornProb (padState (F := F) (m := m) (d := d) ψ) 1 (P.GB.M () g) ≤ 4 * δ := by
  have hP : ∀ u u' : Point F (4 * m),
      (padPt hprojA (mix u u')).aOp (E := CL.Answer F (4 * m) d 1)
        = (padPt hprojA u).aOp (E := CL.Answer F (4 * m) d 1) := fun u u' => by
    rw [padPt_mix]
  have h1 := P.consA
  rw [← inconsistency_swapVec] at h1
  have := sum_bad_mass_le_of_le (swapVec_padState_unit ψ hψ) P.GB
    (fun u => (padPt hprojA u).aOp (E := CL.Answer F (4 * m) d 1)) hP h1 hq
  simpa only [bornProb_swapVec] using this

/-- Alice's global measurement is consistent with the sandwich combination of Bob's lifted
point measurements: the form `lem:qld-global-products` consumes. -/
theorem cons_sandComb_A (hψ : star ψ ⬝ᵥ ψ = 1) :
    1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, bornProb
      (padState (F := F) (m := m) (d := d) ψ) (P.GA.M () g)
      (sandComb (liftOp MB .X) (liftOp MB .Z) u (g.eval u)) := by
  have h := P.consB
  rw [inconsistency_evalPOVM_eq _ (sum_uniform_eq_one _) (padState_unit hψ)] at h
  have hmats : ∀ (u : Point F (4 * m)) (c : F),
      (((padPt hprojB u).aOp (E := CL.Answer F (4 * m) d 1)).mats c).val
        = sandComb (liftOp MB .X) (liftOp MB .Z) u c := fun u c => by
    rw [padPt_aOp_mats, sandComb_liftOp]
  simp only [hmats] at h
  linarith

/-- Bob's version, on the swapped padded state. -/
theorem cons_sandComb_B (hψ : star ψ ⬝ᵥ ψ = 1) :
    1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, bornProb
      (swapVec (padState (F := F) (m := m) (d := d) ψ)) (P.GB.M () g)
      (sandComb (liftOp MA .X) (liftOp MA .Z) u (g.eval u)) := by
  have h := P.consA
  rw [← inconsistency_swapVec,
    inconsistency_evalPOVM_eq _ (sum_uniform_eq_one _) (swapVec_padState_unit ψ hψ)] at h
  have hmats : ∀ (u : Point F (4 * m)) (c : F),
      (((padPt hprojA u).aOp (E := CL.Answer F (4 * m) d 1)).mats c).val
        = sandComb (liftOp MA .X) (liftOp MA .Z) u c := fun u c => by
    rw [padPt_aOp_mats, sandComb_liftOp]
  simp only [hmats] at h
  linarith

variable (hm : m ∣ Fintype.card F) {ε : ℝ}

/-- **`lem:qld-global-products`, Alice's measurement against Bob's `Z_b X_a`.** -/
theorem products_ZX_A (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (padState (F := F) (m := m) (d := d) ψ)
        ((aOp (P.GA.M () g) : Matrix (PadReg F m d dA × PadReg F m d dB) _ ℂ)
          * bOp (1 - ordComb ordZX (liftOp MB .X) (liftOp MB .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordZX_le (padState_unit hψ) P.GA (isPVM_liftOp hprojB .X) (isPVM_liftOp hprojB .Z)
    (P.cons_sandComb_A hψ) (sum_comm_liftOp_B_le hm hψ hfail)

/-- **`lem:qld-global-products`, Alice's measurement against Bob's `X_a Z_b`.** -/
theorem products_XZ_A (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (padState (F := F) (m := m) (d := d) ψ)
        ((aOp (P.GA.M () g) : Matrix (PadReg F m d dA × PadReg F m d dB) _ ℂ)
          * bOp (1 - ordComb ordXZ (liftOp MB .X) (liftOp MB .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordXZ_le (padState_unit hψ) P.GA (isPVM_liftOp hprojB .X) (isPVM_liftOp hprojB .Z)
    (P.cons_sandComb_A hψ) (sum_comm_liftOp_B_le hm hψ hfail)

/-- **`lem:qld-global-products`, Bob's measurement against Alice's `Z_b X_a`**, on the swapped
padded state. -/
theorem products_ZX_B (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (swapVec (padState (F := F) (m := m) (d := d) ψ))
        ((aOp (P.GB.M () g) : Matrix (PadReg F m d dB × PadReg F m d dA) _ ℂ)
          * bOp (1 - ordComb ordZX (liftOp MA .X) (liftOp MA .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordZX_le (swapVec_padState_unit ψ hψ) P.GB (isPVM_liftOp hprojA .X)
    (isPVM_liftOp hprojA .Z) (P.cons_sandComb_B hψ) (sum_comm_liftOp_A_le hm hψ hfail)

/-- **`lem:qld-global-products`, Bob's measurement against Alice's `X_a Z_b`.** -/
theorem products_XZ_B (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (swapVec (padState (F := F) (m := m) (d := d) ψ))
        ((aOp (P.GB.M () g) : Matrix (PadReg F m d dB × PadReg F m d dA) _ ℂ)
          * bOp (1 - ordComb ordXZ (liftOp MA .X) (liftOp MA .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordXZ_le (swapVec_padState_unit ψ hψ) P.GB (isPVM_liftOp hprojA .X)
    (isPVM_liftOp hprojA .Z) (P.cons_sandComb_B hψ) (sum_comm_liftOp_A_le hm hψ hfail)

end GlobalPair


end MIPRE.QLD

end
