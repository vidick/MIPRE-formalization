/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Mirror

/-!
# The pulling chain's index algebra

`lem:qld-pauli-selfcons` is proved by a chain of eleven displays that ends at

```
sum_{g,h,g',h' : g - g_h = g' - g_h', (cd(g) - h) . u-tilde = a}
  ((S-hat^W_g)_{A A'} (x) (tau^W_h)_{A''}) . ((S-hat^W_g')_{B B'} (x) (tau^W_h')_{B''})
```

and concludes by the observation that **this expression is symmetric between `(g, h)` and
`(g', h')`**, so that the analogous derivation starting from Bob's exact Pauli measurement reaches
the same place, and the two are therefore close to each other. That observation is the whole reason
the lemma holds, and the reason it is not obvious is that the two conditions cutting out the index
set look asymmetric: the second mentions both pairs, but the first mentions only `g` and `h`.

The paper's sentence is that the conditions `(cd(g) - h) . u-tilde = a` and `g - g_h = g' - g_h'`
are together equivalent to `(cd(g') - h') . u-tilde = a` and `g - g_h = g' - g_h'`. This file is
that sentence, together with the rewriting of the exact Pauli measurement over the same index set
(`eq:qld-pulling-2` and `eq:qld-pulling-2b`). It is pure index algebra: no state, no estimate.

Subtraction is written as addition throughout, the field having characteristic two.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-! ## The label a pair of outcomes carries -/

/-- **The chain's label.** `cd(g) - h` is the paper's difference of the pair outcome's cube data
and the Weyl outcome; the chain's index set asks its pairing with the probe to be the measurement
outcome. -/
def chainLabel (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h : Anc F m) : Anc F m :=
  cubeData g + h

/-- **The chain's coupling condition.** The paper's `g - g_h = g' - g_{h'}`, with `g_h` the
low-degree encoding of `h`. -/
def ChainCoupled (g g' : LowIndDegPoly (F := F) (m := m) (d := d)) (h h' : Anc F m) : Prop :=
  g.toMv + ldEnc h = g'.toMv + ldEnc h'

instance decidableChainCoupled (g g' : LowIndDegPoly (F := F) (m := m) (d := d))
    (h h' : Anc F m) : Decidable (ChainCoupled g g' h h') :=
  inferInstanceAs (Decidable (g.toMv + ldEnc h = g'.toMv + ldEnc h'))

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The coupling is symmetric on its face, which is half of the display's symmetry. -/
theorem chainCoupled_symm {g g' : LowIndDegPoly (F := F) (m := m) (d := d)} {h h' : Anc F m}
    (hc : ChainCoupled g g' h h') : ChainCoupled g' g h' h := Eq.symm hc

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **Coupled pairs carry the same label**, which is the other half. Evaluating the coupling at a
cube point reads off the two labels there, the encoding of a cube datum being that datum on the
cube. -/
theorem chainLabel_eq_of_coupled {g g' : LowIndDegPoly (F := F) (m := m) (d := d)}
    {h h' : Anc F m} (hc : ChainCoupled g g' h h') : chainLabel g h = chainLabel g' h' := by
  funext y
  have hy := congrArg (fun p => MvPolynomial.eval (pt (F := F) y) p) hc
  simpa [chainLabel, cubeData, LowIndDegPoly.eval_toMv] using hy

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- **So the chain's last display is symmetric between the two pairs.** Its index set is cut out by
the coupling, symmetric on its face, and by a pairing condition read off one pair --- and the two
readings agree, so it may be read off either. That is what lets the derivation starting from Bob's
exact Pauli measurement reach the same expression as Alice's, and hence what makes
`lem:qld-pauli-selfcons` conclude. -/
theorem dotF_chainLabel_eq_of_coupled {g g' : LowIndDegPoly (F := F) (m := m) (d := d)}
    {h h' : Anc F m} (hc : ChainCoupled g g' h h') (v : Anc F m) :
    dotF (chainLabel g h) v = dotF (chainLabel g' h') v := by
  rw [chainLabel_eq_of_coupled hc]

/-! ## The index set, and the exact Pauli measurement written over it -/

/-- **The chain's index set** at the probe `v` and the outcome `a`: the pairs whose label pairs
with the probe to give `a`. -/
def chainIdx (v : Anc F m) (a : F) :
    Finset (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :=
  univ.filter fun p => dotF (chainLabel p.1 p.2) v = a

omit [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mem_chainIdx {v : Anc F m} {a : F}
    {p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m} :
    p ∈ chainIdx v a ↔ dotF (chainLabel p.1 p.2) v = a := by
  rw [chainIdx, mem_filter]
  exact and_iff_right (mem_univ p)

omit [NeZero m] in
/-- In characteristic two the syndrome's condition and the label's are one condition. -/
theorem dotF_chainLabel_eq_iff (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h v : Anc F m)
    (a : F) : dotF (chainLabel g h) v = a ↔ dotF h v = dotF (cubeData g) v + a := by
  rw [chainLabel, dotF_add_left]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hx, ← add_assoc, add_self, zero_add]
  · rw [hx, ← add_assoc, add_self, zero_add]

section Probe

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-- **The chain's summand on one party**: the pair measurement's `W`-marginal at `g`, tensored with
the Weyl spectral projector at `h`, on that party's physical register. -/
def SimulPair.chainOp (P : SimulPair ψ MA MB δ) (W : Bas)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  ((polyMarg P.SA W).mats p.1).val ⊗ₖ proj (weylOf W) p.2

/-- **Displays `eq:qld-pulling-2` and `eq:qld-pulling-2b`: the exact Pauli measurement, indexed the
chain's way.** `eq:tilde_M` sums over the pair measurement's outcomes `g` with a syndrome projector
attached; the chain sums over pairs `(g, h)` cut out by the pairing condition. The two are the same
sum, because the syndrome projector is by definition the fibre of the spectral family over that
pairing, and in characteristic two the shift the definition carries is the sum the chain's label is
written with. -/
theorem mTildeAnc_eq_sum_chainIdx (P : SimulPair ψ MA MB δ) (W : Bas) (v : Anc F m) (a : F) :
    P.mTildeAnc W v a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a, P.chainOp W p := by
  rw [chainIdx, Finset.sum_filter, Fintype.sum_prod_type, SimulPair.mTildeAnc, mTilde]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [sCoarse_eq_polyMarg, syn, kron_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  exact if_congr (by rw [dotF_chainLabel_eq_iff]) rfl rfl

end Probe

/-! ## The chain's endpoint, and its symmetry

Display `eq:qld-pulling-12` is a sum over *pairs* of index pairs, one per party, coupled by
`g - g_h = g' - g_{h'}` and cut out by the pairing condition on the first. Both parties' derivations
end there, and that is only because the expression does not in fact depend on which party's pair
the condition is read off. -/

section Endpoint

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-- **The index set of `eq:qld-pulling-12`**: coupled pairs, with the label read off the first. -/
def coupledIdx (v : Anc F m) (a : F) :
    Finset ((LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :=
  univ.filter fun q => ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2 ∧ dotF (chainLabel q.1.1 q.1.2) v = a

omit [Algebra (ZMod 2) F] [NeZero m] in
@[simp] theorem mem_coupledIdx {v : Anc F m} {a : F}
    {q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)} :
    q ∈ coupledIdx v a
      ↔ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2 ∧ dotF (chainLabel q.1.1 q.1.2) v = a := by
  rw [coupledIdx, mem_filter]
  exact and_iff_right (mem_univ q)

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The index set does not care which pair the label is read off.** This is the paper's sentence:
the conditions `(cd(g) - h) . u-tilde = a` and `g - g_h = g' - g_{h'}` are together equivalent to
`(cd(g') - h') . u-tilde = a` and the same coupling. -/
theorem swap_mem_coupledIdx {v : Anc F m} {a : F}
    {q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)} :
    q.swap ∈ coupledIdx v a ↔ q ∈ coupledIdx v a := by
  simp only [mem_coupledIdx, Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨hc, hl⟩
    exact ⟨chainCoupled_symm hc, (dotF_chainLabel_eq_of_coupled (chainCoupled_symm hc) v).trans hl⟩
  · rintro ⟨hc, hl⟩
    exact ⟨chainCoupled_symm hc, (dotF_chainLabel_eq_of_coupled (chainCoupled_symm hc) v).trans hl⟩

/-- **The chain's endpoint**, an operator on the physical cut: Alice's pair against Bob's. -/
def MirrorSimul.endOp (M : MirrorSimul ψ MA MB δ) (W : Bas) (v : Anc F m) (a : F) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  ∑ q ∈ coupledIdx v a, (M.toFirst.chainOp W q.1) ⊗ₖ (M.toSecond.chainOp W q.2)

/-- **The same endpoint reached from Bob's side**, which writes the two parties in the other order
and reads the label off Bob's pair. -/
def MirrorSimul.endOpMirror (M : MirrorSimul ψ MA MB δ) (W : Bas) (v : Anc F m) (a : F) :
    Matrix ((((dB × Anc F m) × M.Eb) × Anc F m) × (((dA × Anc F m) × M.Ea) × Anc F m))
      ((((dB × Anc F m) × M.Eb) × Anc F m) × (((dA × Anc F m) × M.Ea) × Anc F m)) ℂ :=
  ∑ q ∈ coupledIdx v a, (M.toSecond.chainOp W q.1) ⊗ₖ (M.toFirst.chainOp W q.2)

omit [NeZero m] in
/-- Swapping the two parties of a product operator is a reindexing by the product's commutation. -/
theorem reindex_prodComm_kron {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    Matrix.reindex (Equiv.prodComm A B) (Equiv.prodComm A B) (X ⊗ₖ Y) = Y ⊗ₖ X := by
  ext p q
  obtain ⟨b1, a1⟩ := p
  obtain ⟨b2, a2⟩ := q
  exact mul_comm _ _

/-- **The endpoint is symmetric between the two parties**, which is the whole reason
`lem:qld-pauli-selfcons` concludes: Bob's derivation ends at the same operator as Alice's, written
with the parties in the other order, so the two exact Pauli measurements are close to each other
rather than merely each close to something. -/
theorem MirrorSimul.endOpMirror_apply (M : MirrorSimul ψ MA MB δ) (W : Bas) (v : Anc F m) (a : F)
    (i j : (((dB × Anc F m) × M.Eb) × Anc F m) × (((dA × Anc F m) × M.Ea) × Anc F m)) :
    M.endOpMirror W v a i j = M.endOp W v a i.swap j.swap := by
  rw [MirrorSimul.endOpMirror, MirrorSimul.endOp, Matrix.sum_apply, Matrix.sum_apply]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  refine Finset.sum_equiv (Equiv.prodComm _ _) (fun q => swap_mem_coupledIdx.symm)
    (fun q _ => ?_)
  exact mul_comm _ _

/-- The same, as an identity of matrices. -/
theorem MirrorSimul.endOpMirror_eq (M : MirrorSimul ψ MA MB δ) (W : Bas) (v : Anc F m) (a : F) :
    M.endOpMirror W v a
      = Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (M.endOp W v a) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, M.endOpMirror_apply]
  rfl

/-! ## Closing the chain

Both parties' derivations end at the endpoint, and what remains is arithmetic: the triangle
inequality for a family of deviations, which Foundations has as `sum_snorm_sq_triangle'`. The two
hypotheses below are exactly the two chains --- Alice's `eq:qld-pulling-0` through
`eq:qld-pulling-12`, and Bob's symmetric equivalent --- and nothing else stands between them and
`lem:qld-pauli-selfcons`. -/

omit [NeZero m] in
/-- **A deviation reads the same on either party's ordering of the physical cut.** Swapping the two
parties is a reindexing of the whole space, and a state-norm makes no reference to a cut. -/
theorem snorm_reindex_prodComm {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (φ : A × B → ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    snorm (φ ∘ Prod.swap) (Matrix.reindex (Equiv.prodComm A B) (Equiv.prodComm A B) X)
      = snorm φ X := by
  have hsq : snorm (φ ∘ Prod.swap)
      (Matrix.reindex (Equiv.prodComm A B) (Equiv.prodComm A B) X) ^ 2 = snorm φ X ^ 2 := by
    rw [snorm_sq_eq_qform, snorm_sq_eq_qform, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.reindex_apply,
      qform, qform, show (φ ∘ Prod.swap) = φ ∘ (Equiv.prodComm A B).symm from rfl,
      qform_comp_equiv]
  have h1 := snorm_nonneg (φ ∘ Prod.swap)
    (Matrix.reindex (Equiv.prodComm A B) (Equiv.prodComm A B) X)
  have h2 := snorm_nonneg φ X
  nlinarith

section Close

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-- **The chain's conclusion.** Given that each party's exact Pauli measurement is close to the
endpoint, the two are close to each other, which is `eq:qld-pulling-cons`. The factor two is the
triangle inequality's, and the paper absorbs it into `delta_S`. -/
theorem sum_xSqNorm_le_of_endOp (M : MirrorSimul ψ MA MB δ) (W : Bas) (v : Anc F m) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : F, snorm M.physVec
            ((aOp (M.aliceMTilde W v a) : Matrix _ _ ℂ) - M.endOp W v a) ^ 2 ≤ δ₁)
    (h2 : ∑ a : F, snorm M.physVec
            (M.endOp W v a - (bOp (M.bobMTilde W v a) : Matrix _ _ ℂ)) ^ 2 ≤ δ₂) :
    ∑ a : F, xSqNorm M.physVec (M.aliceMTilde W v a) (M.bobMTilde W v a) ≤ 2 * δ₁ + 2 * δ₂ := by
  have h := sum_snorm_sq_triangle' M.physVec
    (fun a : F => (aOp (M.aliceMTilde W v a) : Matrix _ _ ℂ))
    (fun a : F => M.endOp W v a)
    (fun a : F => (bOp (M.bobMTilde W v a) : Matrix _ _ ℂ))
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => xSqNorm_eq_snorm_sq M.physVec _ _]
  linarith

end Close

end Endpoint

end MIPRE.QLD

end
