/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Combined
import MIPRE.Foundations.POVMMix

/-!
# The simultaneous pair measurement: the interface between stages 4 and 5

Stage 5 of the Pauli basis test's analysis (`lem:qld-helper`, `lem:qld-exact-paulis`,
`lem:qld-swap`, and the assembly of `thm:qld`) consumes stage 4 through one statement, the
paper's `lem:qld-4-7` (blueprint `lem:qld-simultaneous`): a *projective* measurement
`S-hat_{g_X, g_Z}` on each party's padded local space, with outcomes pairs of polynomials in `m`
variables of individual degree at most `d`, whose evaluated `X` and `Z` marginals are consistent
with the opposite party's expanded point measurements, in both register versions. This file
fixes that statement as a structure, `SimulPair`, so that stage 5 can be proved against it while
stage 4 fills it in, with no `sorry` in the tree at any point.

## The registers

The Lean padded strategy does not live on the paper's registers `A A' | B A''`:
`lem:qld-padded-points` dilates its sandwich with an `F × F` ancilla per party, and the seeded
soundness theorem is applied to a projective dilation of the padded strategy, which adds one
more. So the measurement stage 4 produces acts on `(dA × Anc F m) × EA` for an ancilla type `EA`
that stage 5 has no reason to know, and the state it is consistent on is a product of the
expanded state `hatVec ψ` with fixed ancilla vectors. The structure carries the ancilla types
`EA`, `EB` and the state `Φ` abstractly, and records the one property of `Φ` every transfer from
stages 2 and 3 needs: an operator on the two hat registers, extended by the identity, has the
expectation it has on `hatVec ψ` (`Φ_reduced`). Every `extVec2 (hatVec ψ) a₀ b₀`, nested or
reindexed, satisfies it.

## The consistency

`consA` says that Alice's pair measurement, read through the `W`-component evaluated at a
uniformly random point `u`, agrees with Bob's expanded `(Point, W)` measurement at `u` up to
`δ` --- the paper's `eq:qld-s-point-con-alice`; `consB` is `eq:qld-s-point-con-bob`. Both are
required, and no symmetry of the strategy is assumed.
-/

noncomputable section

universe u

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- Pairs of polynomials in `m` variables of individual degree at most `d`: the outcomes of the
simultaneous measurement. -/
abbrev PolyPair (F : Type u) (m d : ℕ) :=
  LowIndDegPoly (F := F) (m := m) (d := d) × LowIndDegPoly (F := F) (m := m) (d := d)

/-- The component of a pair a basis reads: `g_X` for `X`, `g_Z` for `Z`. -/
def PolyPair.proj (W : Bas) (p : PolyPair F m d) : LowIndDegPoly (F := F) (m := m) (d := d) :=
  match W with
  | .X => p.1
  | .Z => p.2

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem PolyPair.proj_X (p : PolyPair F m d) : PolyPair.proj .X p = p.1 := rfl

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem PolyPair.proj_Z (p : PolyPair F m d) : PolyPair.proj .Z p = p.2 := rfl

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- **The evaluated `W`-marginal** of a pair measurement at the point `u`: the paper's
`S-hat_{[eval_u(·_W) = a]}`, the POVM with outcomes in `F` that sums the pair operators whose
`W`-component takes the value `a` at `u`. -/
def evalMarg (S : POVM (PolyPair F m d) R) (W : Bas) (u : Point F m) : POVM F R :=
  S.map fun p => (PolyPair.proj W p).eval u

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem evalMarg_mats (S : POVM (PolyPair F m d) R) (W : Bas) (u : Point F m) (a : F) :
    ((evalMarg S W u).mats a).val
      = ∑ p ∈ univ.filter fun p : PolyPair F m d => (PolyPair.proj W p).eval u = a,
          ((S.mats p).val) :=
  POVM.map_mats _ _ _

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The evaluated marginal of a projective pair measurement is projective. -/
theorem isPVM_evalMarg {S : POVM (PolyPair F m d) R} (hS : IsPVM fun p => ((S.mats p).val))
    (W : Bas) (u : Point F m) : IsPVM fun a => (((evalMarg S W u).mats a).val) := by
  have hfun : (fun a => (((evalMarg S W u).mats a).val))
      = fun c => ∑ p ∈ univ.filter fun p : PolyPair F m d => (PolyPair.proj W p).eval u = c,
          ((S.mats p).val) :=
    funext fun a => POVM.map_mats _ _ _
  rw [hfun]
  exact hS.coarse _

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The simultaneous pair measurement** (`lem:qld-simultaneous`, the paper's `lem:qld-4-7`),
for a strategy `(ψ, MA, MB)` of the Pauli basis test, with error `δ`: on each party's padded
local space `(dA × Anc F m) × EA` a projective measurement with outcomes pairs of polynomials,
whose evaluated marginals are consistent with the opposite party's expanded point measurements
on the padded state `Φ`, in both register versions. -/
structure SimulPair (ψ : dA × dB → ℂ) (MA : Question F m → POVM (Answer F m d) dA)
    (MB : Question F m → POVM (Answer F m d) dB) (δ : ℝ) where
  /-- Alice's ancilla beyond the expansion. -/
  EA : Type u
  [instFintypeEA : Fintype EA]
  [instDecEqEA : DecidableEq EA]
  /-- Bob's ancilla beyond the expansion. -/
  EB : Type u
  [instFintypeEB : Fintype EB]
  [instDecEqEB : DecidableEq EB]
  /-- The padded state. -/
  Φ : ((dA × Anc F m) × EA) × ((dB × Anc F m) × EB) → ℂ
  Φ_unit : star Φ ⬝ᵥ Φ = 1
  /-- The padded state reduces to the expanded state on the two hat registers. -/
  Φ_reduced : ∀ (X : Matrix (dA × Anc F m) (dA × Anc F m) ℂ)
    (Y : Matrix (dB × Anc F m) (dB × Anc F m) ℂ),
    bornProb Φ (aOp X) (aOp Y) = bornProb (hatVec (F := F) (m := m) ψ) X Y
  /-- Alice's pair measurement. -/
  SA : POVM (PolyPair F m d) ((dA × Anc F m) × EA)
  SA_proj : IsPVM fun p => ((SA.mats p).val)
  /-- Bob's pair measurement. -/
  SB : POVM (PolyPair F m d) ((dB × Anc F m) × EB)
  SB_proj : IsPVM fun p => ((SB.mats p).val)
  /-- Alice's evaluated marginals track Bob's expanded point measurements. -/
  consA : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ (fun u => evalMarg SA W u)
    (fun u => (hatPtPOVM MB W u).aOp) ≤ δ
  /-- Bob's evaluated marginals track Alice's expanded point measurements. -/
  consB : ∀ W : Bas, inconsistency (uniform (Point F m)) Φ (fun u => (hatPtPOVM MA W u).aOp)
    (fun u => evalMarg SB W u) ≤ δ

attribute [instance] SimulPair.instFintypeEA SimulPair.instDecEqEA SimulPair.instFintypeEB
  SimulPair.instDecEqEB

namespace SimulPair

variable {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/-- The error can only be weakened. -/
def mono (P : SimulPair ψ MA MB δ) {δ' : ℝ} (h : δ ≤ δ') : SimulPair ψ MA MB δ' :=
  { P with consA := fun W => le_trans (P.consA W) h, consB := fun W => le_trans (P.consB W) h }

/-- **The padded state reproduces every expectation of the expanded state**, so every
conclusion of stages 2 and 3 about `hatVec ψ` transfers to `Φ` for operators extended by the
identity. -/
theorem bornProb_aOp_aOp (P : SimulPair ψ MA MB δ) (X : Matrix (dA × Anc F m) (dA × Anc F m) ℂ)
    (Y : Matrix (dB × Anc F m) (dB × Anc F m) ℂ) :
    bornProb P.Φ (aOp X) (aOp Y) = bornProb (hatVec (F := F) (m := m) ψ) X Y :=
  P.Φ_reduced X Y

end SimulPair

/-! ## Products with fixed ancilla vectors reduce to the expanded state -/

section Reduced

variable {RA RB EA EB : Type*} [Fintype RA] [DecidableEq RA] [Fintype RB] [DecidableEq RB]
  [Fintype EA] [DecidableEq EA] [Fintype EB] [DecidableEq EB]

/-- **An extension by fixed ancilla vectors has the reduced-state property**, on any registers:
operators extended by the identity on the ancillas have on `extVec2 φ a₀ b₀` the expectation they
have on `φ`. Applied twice, it takes the twice-padded state of `lem:qld-global-pvm` back to the
expanded state. -/
theorem bornProb_extVec2_aOp_aOp (φ : RA × RB → ℂ) (a₀ : EA) (b₀ : EB) (X : Matrix RA RA ℂ)
    (Y : Matrix RB RB ℂ) : bornProb (extVec2 φ a₀ b₀) (aOp X) (aOp Y) = bornProb φ X Y := by
  rw [bornProb_extVec2, compress_aOp, compress_aOp]

end Reduced

end MIPRE.QLD

end
