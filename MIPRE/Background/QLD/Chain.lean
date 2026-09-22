/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Mirror
import MIPRE.Background.QLD.SwapState

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
/-- **A deviation is carried by any reindexing of the whole space.** `qform_comp_equiv` says the
quadratic form is, and a state-norm is the square root of one. This is what lets the chain be read
along whichever of the paper's three groupings each of its steps is local in. -/
theorem snorm_comp_equiv {N N' : Type*} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (e : N ≃ N') (φ : N → ℂ) (X : Matrix N N ℂ) :
    snorm (φ ∘ e.symm) (Matrix.reindex e e X) = snorm φ X := by
  have hsq : snorm (φ ∘ e.symm) (Matrix.reindex e e X) ^ 2 = snorm φ X ^ 2 := by
    rw [snorm_sq_eq_qform, snorm_sq_eq_qform, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.reindex_apply,
      qform, qform, qform_comp_equiv]
  have h1 := snorm_nonneg (φ ∘ e.symm) (Matrix.reindex e e X)
  have h2 := snorm_nonneg φ X
  nlinarith

omit [NeZero m] in
/-- **In particular it reads the same on either party's ordering of the physical cut**, which is
what lets Bob's chain, derived at `toSecond`, be compared with Alice's. -/
theorem snorm_reindex_prodComm {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (φ : A × B → ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    snorm (φ ∘ Prod.swap) (Matrix.reindex (Equiv.prodComm A B) (Equiv.prodComm A B) X)
      = snorm φ X :=
  snorm_comp_equiv (Equiv.prodComm A B) φ X

omit [NeZero m] in
/-- **Right-multiplying a projective measurement costs exactly the operator's deviation from the
identity.** Summed over the outcomes there is no cross term, so no factor of the outcome count
appears --- which is what makes display `eq:qld-pulling-1` free rather than lossy. -/
theorem sum_snorm_sq_sub_mul {N Λ : Type*} [Fintype N] [DecidableEq N] [Fintype Λ]
    [DecidableEq Λ] (v : N → ℂ) {P : Λ → Matrix N N ℂ} (hP : IsPVM P) (Y : Matrix N N ℂ) :
    ∑ a : Λ, snorm v (P a - P a * Y) ^ 2 = snorm v (1 - Y) ^ 2 := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
    rw [show P a - P a * Y = P a * (1 - Y) from by rw [Matrix.mul_sub, Matrix.mul_one]]]
  rw [← snorm_sq_sum_orthogonal v hP (1 - Y) univ, hP.sum_eq_one, Matrix.one_mul]

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

/-! ## The chain's first estimate

`eq:qld-pulling-0` to `eq:qld-pulling-1` right-multiplies the exact Pauli measurement by the
near-identity of `lem:qld-helper`. What makes the step cost the helper's bound and no more is
`sum_snorm_sq_sub_mul`: the measurement's outcomes are orthogonal, so summing over them leaves one
deviation rather than one per outcome. -/

/-- `A (x) (sum B) = sum (A (x) B)`, on any registers. -/
theorem kron_sum' {R S ι : Type*} [Fintype R] [Fintype S] (s : Finset ι)
    (A : Matrix R R ℂ) (B : ι → Matrix S S ℂ) :
    A ⊗ₖ (∑ x ∈ s, B x) = ∑ x ∈ s, A ⊗ₖ B x := by
  ext p q
  simp [Matrix.sum_apply, Finset.mul_sum]

/-- `(sum B) (x) A = sum (B (x) A)`, on any registers. -/
theorem sum_kron' {R S ι : Type*} [Fintype R] [Fintype S] (s : Finset ι)
    (B : ι → Matrix R R ℂ) (A : Matrix S S ℂ) :
    (∑ x ∈ s, B x) ⊗ₖ A = ∑ x ∈ s, B x ⊗ₖ A := by
  ext p q
  simp [Matrix.sum_apply, Finset.sum_mul]

/-- Reindexing is additive. -/
theorem reindex_sum {M N ι : Type*} (e : M ≃ N) (s : Finset ι) (f : ι → Matrix M M ℂ) :
    Matrix.reindex e e (∑ i ∈ s, f i) = ∑ i ∈ s, Matrix.reindex e e (f i) := by
  ext p q
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]

/-- **A sum of orthogonal blocks has no cross terms, even with a different tail on each.** The
common-tail version `snorm_sq_sum_orthogonal` does not cover the chain, whose tail carries the
outcome's own point measurement. -/
theorem snorm_sq_sum_orthogonal' {N Λ : Type*} [Fintype N] [DecidableEq N] [Fintype Λ]
    [DecidableEq Λ] (v : N → ℂ) {S : Λ → Matrix N N ℂ} (hS : IsPVM S)
    (R : Λ → Matrix N N ℂ) (s : Finset Λ) :
    snorm v (∑ g ∈ s, S g * R g) ^ 2 = ∑ g ∈ s, snorm v (S g * R g) ^ 2 := by
  classical
  rw [snorm_sq_eq_qform, Matrix.conjTranspose_sum, Finset.sum_mul]
  have hterm : ∀ g ∈ s, ((S g * R g)ᴴ * ∑ g' ∈ s, S g' * R g') = (S g * R g)ᴴ * (S g * R g) := by
    intro g hg
    rw [Finset.mul_sum, Finset.sum_eq_single_of_mem g hg fun g' _ hg' => ?_]
    rw [Matrix.conjTranspose_mul, hS.isSelfAdjoint, Matrix.mul_assoc,
      show S g * (S g' * R g') = (S g * S g') * R g' from (Matrix.mul_assoc _ _ _).symm,
      hS.orthogonal (Ne.symm hg'), Matrix.zero_mul, Matrix.mul_zero]
  rw [Finset.sum_congr rfl hterm, qform_sum]
  exact Finset.sum_congr rfl fun g _ => (snorm_sq_eq_qform v (S g * R g)).symm

/-- **A Weyl family's spectral projectors are a projective measurement.** The three facts are in
Foundations one by one; this is them bundled, which is the form `isPVM_kron` consumes. -/
theorem isPVM_proj {n : Type*} [Fintype n] [DecidableEq n]
    {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) : IsPVM (proj w) where
  isSelfAdjoint e := proj_conjTranspose hw e
  idem e := by simpa using proj_mul_proj hw e e
  sum_eq_one := sum_proj hw

/-- **The chain's summands are a projective measurement** in the pair `(g, h)`: a marginal of a
projective pair measurement, tensored with a Weyl spectral projector. -/
theorem isPVM_chainOp (P : SimulPair ψ MA MB δ) (W : Bas) :
    IsPVM fun p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m => P.chainOp W p := by
  exact isPVM_kron (isPVM_polyMarg P.SA_proj W) (isPVM_proj (isWeylFamily_weylOf W))

/-- **Summing the *pair* outcome out of the summand** leaves the Weyl projector alone, the pair
measurement's outcomes being complete. This is what `eq:qld-pulling-9a` inserts. -/
theorem SimulPair.sum_poly_chainOp (P : SimulPair ψ MA MB δ) (W : Bas) (h : Anc F m) :
    (∑ g : LowIndDegPoly (F := F) (m := m) (d := d), P.chainOp W (g, h))
      = bOp (proj (weylOf W) h) := by
  rw [show (∑ g : LowIndDegPoly (F := F) (m := m) (d := d), P.chainOp W (g, h))
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
        (((polyMarg P.SA W).mats g).val) ⊗ₖ proj (weylOf W) h from rfl,
    ← sum_kron' univ, (isPVM_polyMarg P.SA_proj W).sum_eq_one]
  rfl

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The point measurement read off a strategy is projective** when the strategy's own is: it is a
coarse-graining of it along the answer's value. -/
theorem isPVM_ptAtPOVM {d' : Type} [Fintype d'] [DecidableEq d']
    {M : Question F m → POVM (Answer F m d) d'}
    (hproj : ∀ q, IsPVM fun a => (((M q).mats a).val)) (W : Bas) (u : Point F m) :
    IsPVM fun k : F => (((ptAtPOVM M W u).mats k).val) := by
  have hfun : (fun k : F => (((ptAtPOVM M W u).mats k).val))
      = fun k => ∑ a ∈ univ.filter fun a => rdVal a = k, (((M (.point W u)).mats a).val) :=
    funext fun k => POVM.map_mats _ _ _
  rw [hfun]
  exact (hproj _).coarse _

/-- **A single Weyl spectral projector transports across the expanded state, exactly.** The
syndrome version is `stateVec_hatVec_syn`; the chain's display `eq:qld-pulling-3a` moves one
projector, not a fibre of them. -/
theorem stateVec_hatVec_proj (φ : dA × dB → ℂ) (W : Bas) (h : Anc F m) :
    stateVec (hatVec (F := F) (m := m) φ) ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h)
      = stateVecB (hatVec (F := F) (m := m) φ)
        ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h) := by
  rw [hatVec, stateVec_expVec_kron_one, stateVecB_expVec_kron_one]
  congr 2
  have hh := stateVec_epr_proj (w := weylOf W) (weylOf_transpose W) h
  rw [stateVec, stateVecB] at hh
  exact congrArg (WithLp.ofLp) hh

/-- The same, as the vanishing of a cross-party deviation --- the form that crosses to the padded
state, `SimulPair` saying only that `Phi` reproduces the expanded state's expectations. -/
theorem xSqNorm_hatVec_proj (φ : dA × dB → ℂ) (W : Bas) (h : Anc F m) :
    xSqNorm (hatVec (F := F) (m := m) φ) ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h)
        ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h) = 0 := by
  rw [xSqNorm, stateVec_hatVec_proj, sub_self, norm_zero]
  norm_num

/-- **A syndrome projector meets a single spectral projector in that projector or in nothing.**
The syndrome is the fibre of the spectral family over the pairing, so the product keeps the one
outcome exactly when it lies in the fibre. -/
theorem syn_mul_proj {n : Type*} [Fintype n] [DecidableEq n]
    {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) (v : n → F) (b : F)
    (h : n → F) :
    syn w v b * proj w h = if dotF h v = b then proj w h else 0 := by
  classical
  rw [syn, Finset.sum_mul,
    Finset.sum_congr rfl fun e (_ : e ∈ univ.filter fun e => dotF e v = b) => proj_mul_proj hw e h]
  by_cases hb : dotF h v = b
  · rw [if_pos hb, Finset.sum_ite_eq' (univ.filter fun e : n → F => dotF e v = b) h (proj w),
      if_pos (mem_filter.mpr ⟨mem_univ h, hb⟩)]
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun e he => if_neg fun hc => hb ?_
    rw [← hc]
    exact (mem_filter.mp he).2

variable {d' : Type} [Fintype d'] [DecidableEq d']

/-- **Display `eq:qld-pulling-3b`.** The chain's factor `(M^{Point}_r)_A (x) (tau_h)_{A'}` is the
hatted point measurement itself, cut down by the Weyl outcome: `M-hat^{u}_{c}` times the projector
at `h` keeps exactly the point outcome `c - g_h(u)`, the syndrome factor selecting the one term of
the convolution whose shift matches `h`. -/
theorem hatMats_mul_proj (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m)
    (c : F) (h : Anc F m) :
    hatMats M W u c * ((1 : Matrix d' d' ℂ) ⊗ₖ proj (weylOf W) h)
      = (((ptAtPOVM M W u).mats (c + dotF h (indVec u))).val) ⊗ₖ proj (weylOf W) h := by
  classical
  rw [← sum_kron_syn_eq_hatMats M W u c, Finset.sum_mul,
    Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, synPOVM_mats,
        syn_mul_proj (isWeylFamily_weylOf W) (indVec u) (c + a') h]]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) =>
    show (((ptAtPOVM M W u).mats a').val)
        ⊗ₖ (if dotF h (indVec u) = c + a' then proj (weylOf W) h else 0)
      = (if a' = c + dotF h (indVec u)
          then (((ptAtPOVM M W u).mats a').val) ⊗ₖ proj (weylOf W) h else 0) from by
      by_cases hx : a' = c + dotF h (indVec u)
      · rw [if_pos hx, if_pos (show dotF h (indVec u) = c + a' from by
          rw [hx, ← add_assoc, add_self, zero_add])]
      · rw [if_neg hx, if_neg (fun hc => hx (by rw [hc, ← add_assoc, add_self, zero_add])),
          Matrix.kronecker_zero]]
  rw [Finset.sum_ite_eq' univ (c + dotF h (indVec u))
    (fun a' => (((ptAtPOVM M W u).mats a').val) ⊗ₖ proj (weylOf W) h), if_pos (mem_univ _)]

/-! ## The last two displays' common machinery

`eq:qld-pulling-5` to `-7` and `eq:qld-pulling-10` to `-12` are the chain's remaining estimates,
and they are the first of its steps to live on all six registers: both compare operators on the
physical cut, Alice's `A A' A''` against Bob's `B B' B''`. They share an outer shape and a way of
discharging the far party, collected here. -/

section LastTwo

variable {dA' dB' anc ι κ : Type*} [Fintype dA'] [DecidableEq dA'] [Fintype dB'] [DecidableEq dB']
  [Fintype anc] [DecidableEq anc] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Field F] [Algebra (ZMod 2) F] in
/-- **The outer shape both remaining displays share.** Each is a bound on the summed squared norm
of the chain's terms, grouped by the measurement outcome. Projectivity turns each group into a sum
of sandwiches (`snorm_sq_sum_proj_sandwich`), the groups are the fibres of the outcome map, so the
double sum is the single one over the index --- and what is left to bound is a sum of sandwiches
with no outcome in it. The index may be a subset, which is what `eq:qld-pulling-10` needs: it sums
over the pairs whose outcomes *disagree*. -/
theorem sum_snorm_sq_fiber_sandwich_subset_le {N : Type*} [Fintype N] [DecidableEq N] (v : N → ℂ)
    {P : ι → Matrix N N ℂ} (hP : IsPVM P) (W : ι → Matrix N N ℂ)
    (c : ι → F) (D : Finset ι) {ε : ℝ}
    (hbound : ∑ i ∈ D, qform v ((W i)ᴴ * P i * W i) ≤ ε) :
    ∑ a : F, snorm v (∑ i ∈ D.filter fun i => c i = a, P i * W i) ^ 2 ≤ ε := by
  classical
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => snorm_sq_sum_proj_sandwich v hP W _,
    Finset.sum_fiberwise D c fun i => qform v ((W i)ᴴ * P i * W i)]
  exact hbound

omit [Field F] [Algebra (ZMod 2) F] in
/-- The case the first of the two displays uses, where the whole index is summed over. -/
theorem sum_snorm_sq_fiber_sandwich_le {N : Type*} [Fintype N] [DecidableEq N] (v : N → ℂ)
    {P : ι → Matrix N N ℂ} (hP : IsPVM P) (W : ι → Matrix N N ℂ)
    (c : ι → F) {ε : ℝ} (hbound : ∑ i, qform v ((W i)ᴴ * P i * W i) ≤ ε) :
    ∑ a : F, snorm v (∑ i ∈ univ.filter fun i => c i = a, P i * W i) ^ 2 ≤ ε :=
  sum_snorm_sq_fiber_sandwich_subset_le v hP W c univ hbound

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Dropping the far party's sub-identity factor.** Each of the chain's sandwiches carries, on
the far party, a projector times a Weyl outcome; summed over the outcome those are at most the
identity, so the whole sum is bounded by the near party's sandwiches alone. This is
`fact:add-a-proj` in the form `eq:qld-pulling-7` and `eq:qld-pulling-11` consume it. -/
theorem sum_bornProb_sandwich_drop_le (ψ : dA' × (dB' × anc) → ℂ)
    {S : ι → Matrix dA' dA' ℂ} (hS : IsPVM S) (X : ι → Matrix dA' dA' ℂ)
    {B : ι → Matrix dB' dB' ℂ} (hBsa : ∀ i, (B i)ᴴ = B i) (hBidem : ∀ i, B i * B i = B i)
    {T : κ → Matrix anc anc ℂ} (hT : IsPVM T) :
    ∑ i, ∑ _x : κ, bornProb ψ ((X i)ᴴ * S i * X i) (B i ⊗ₖ T _x)
      ≤ ∑ i, bornProb ψ ((X i)ᴴ * S i * X i) 1 := by
  refine Finset.sum_le_sum fun i _ => ?_
  exact sum_bornProb_kron_le ψ (Matrix.PosSemidef.conjTranspose_mul_mul_same (hS.posSemidef i) _)
    (fun _ => hBsa i) (fun _ => hBidem i) hT

end LastTwo

section First

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

variable (P : SimulPair ψ MA MB δ)

/-- **The helper's near-identity**, read along the cut `mTilde` lives on. On `Phi`'s own cut it is
`agreeOp` of Alice's pair-measurement marginals against Bob's expanded point measurements, which is
what `lem:qld-helper` bounds; `regroupEquiv` carries it to the cut that has `A''` on Alice's
side. -/
def SimulPair.nearId (W : Bas) (u : Point F m) :
    Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB))
      ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) ℂ :=
  Matrix.reindex regroupEquiv regroupEquiv
    (agreeOp (fun g : LowIndDegPoly (F := F) (m := m) (d := d) =>
        ((polyMarg P.SA W).mats g).val)
      (fun g => (aOp (hatMats MB W u (g.eval u)) : Matrix ((dB × Anc F m) × P.EB) _ ℂ)))

/-- **Display `eq:qld-pulling-1`, as an identity.** Inserting the near-identity costs exactly its
own deficit on the state, with no loss at all. -/
theorem SimulPair.sum_snorm_sq_nearId (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, snorm P.mVec ((aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ)
          - (aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ) * P.nearId W u) ^ 2
      = 1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          bornProb P.Φ (((polyMarg P.SA W).mats g).val)
            (aOp (hatMats MB W u (g.eval u))) := by
  have hone : (1 : Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) _ ℂ)
        - P.nearId W u
      = Matrix.reindex regroupEquiv regroupEquiv
        (1 - agreeOp (fun g : LowIndDegPoly (F := F) (m := m) (d := d) =>
            ((polyMarg P.SA W).mats g).val)
          (fun g => (aOp (hatMats MB W u (g.eval u)) : Matrix ((dB × Anc F m) × P.EB) _ ℂ))) := by
    ext i j
    simp [SimulPair.nearId, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  have hnorm : ‖evec P.Φ‖ = 1 := by
    have h : ‖evec P.Φ‖ ^ 2 = 1 := by rw [norm_evec_sq, P.Φ_unit]; norm_num
    nlinarith [norm_nonneg (evec P.Φ), h]
  rw [sum_snorm_sq_sub_mul _ (IsPVM.aOp (P.isPVM_mTildeAnc W v)), hone, SimulPair.mVec,
    regroupVec, snorm_comp_equiv, snorm_sq_one_sub_agreeOp hnorm
      (isPVM_polyMarg P.SA_proj W)
      (fun g => ((IsPVM.aOp (isPVM_hatMats hprojB W u)).isSelfAdjoint _))
      (fun g => ((IsPVM.aOp (isPVM_hatMats hprojB W u)).idem _))]

/-- **And its cost**, which is item 1 of `lem:qld-helper`. -/
theorem SimulPair.sum_uniform_snorm_sq_nearId_le
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    ∑ u, uniform (Point F m) u
        * ∑ a : F, snorm P.mVec ((aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ)
            - (aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ) * P.nearId W u) ^ 2
      ≤ δ := by
  have hsplit : ∀ u : Point F m,
      (∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          bornProb P.Φ (((polyMarg P.SA W).mats g).val)
            (1 - (aOp (hatMats MB W u (g.eval u)) : Matrix ((dB × Anc F m) × P.EB) _ ℂ)))
        = 1 - ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
            bornProb P.Φ (((polyMarg P.SA W).mats g).val)
              (aOp (hatMats MB W u (g.eval u))) := by
    intro u
    rw [Finset.sum_congr rfl fun g (_ : g ∈ univ) =>
        bornProb_sub_right P.Φ (((polyMarg P.SA W).mats g).val) 1
          (aOp (hatMats MB W u (g.eval u))),
      Finset.sum_sub_distrib, ← bornProb_sum_left,
      (isPVM_polyMarg P.SA_proj W).sum_eq_one, bornProb_one_one P.Φ_unit]
  have h := P.sum_bornProb_polyMarg_one_sub_le (MB := MB) W
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hsplit u]] at h
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [P.sum_snorm_sq_nearId hprojB W v u]]
  exact h

namespace SimulPair

/-- **The near-identity, expanded.** -/
theorem nearId_eq_sum (W : Bas) (u : Point F m) :
    P.nearId W u
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), ∑ a' : F,
          ((((polyMarg P.SA W).mats g).val
              ⊗ₖ syn (weylOf W) (indVec u) (g.eval u + a'))
            ⊗ₖ (aOp (((ptAtPOVM MB W u).mats a').val) : Matrix (dB × P.EB) _ ℂ)) := by
  rw [nearId, agreeOp, reindex_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [aOp_mul_bOp_eq, ← sum_kron_syn_eq_hatMats MB W u (g.eval u), aOp_sum, kron_sum',
    reindex_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  exact reindex_regroupEquiv _ _ _

/-- **The exact Pauli measurement, expanded over the pair outcomes.** -/
theorem mTildeAnc_eq_sum (W : Bas) (v : Anc F m) (a : F) :
    P.mTildeAnc W v a
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          ((polyMarg P.SA W).mats g).val ⊗ₖ syn (weylOf W) v (dotF (cubeData g) v + a) :=
  Finset.sum_congr rfl fun g _ => by rw [sCoarse_eq_polyMarg]

/-- **Multiplying it by one of the near-identity's terms.** The pair measurement's outcomes are
orthogonal, so only the matching one survives, and `syn_mul_syn` collapses the two syndrome
projectors onto the Weyl outcomes satisfying both conditions. -/
theorem mTildeAnc_mul_kron (W : Bas) (v : Anc F m) (u : Point F m) (a : F)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) (b : F) :
    P.mTildeAnc W v a
        * (((polyMarg P.SA W).mats g).val ⊗ₖ syn (weylOf W) (indVec u) b)
      = ∑ h ∈ univ.filter fun h : Anc F m =>
            dotF h v = dotF (cubeData g) v + a ∧ dotF h (indVec u) = b,
          ((polyMarg P.SA W).mats g).val ⊗ₖ proj (weylOf W) h := by
  classical
  rw [mTildeAnc_eq_sum, Finset.sum_mul,
    Finset.sum_eq_single g (fun g' _ hg' => by
      rw [← Matrix.mul_kronecker_mul, (isPVM_polyMarg P.SA_proj W).orthogonal hg',
        Matrix.zero_kronecker])
      fun hmem => absurd (Finset.mem_univ g) hmem,
    ← Matrix.mul_kronecker_mul, (isPVM_polyMarg P.SA_proj W).idem,
    syn_mul_syn (isWeylFamily_weylOf W), kron_sum']

/-- **Display `eq:qld-pulling-2b` at the interface.** Expanding both factors, the pair
measurement's orthogonality picks out one outcome, `syn_mul_syn` fuses the two syndrome projectors,
and the sum over Bob's point outcome collapses --- for each Weyl outcome `h` exactly one of them
survives, namely `(g - g_h)(u)`. What is left is a sum over the chain's own index set. -/
theorem aOp_mTildeAnc_mul_nearId (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    (aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ) * P.nearId W u
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
          (P.chainOp W p)
            ⊗ₖ (aOp (((ptAtPOVM MB W u).mats (p.1.eval u + dotF p.2 (indVec u))).val)
                : Matrix (dB × P.EB) _ ℂ) := by
  classical
  rw [nearId_eq_sum, Finset.mul_sum, chainIdx, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  have hterm : ∀ a' : F,
      (aOp (P.mTildeAnc W v a) : Matrix _ _ ℂ)
          * ((((polyMarg P.SA W).mats g).val ⊗ₖ syn (weylOf W) (indVec u) (g.eval u + a'))
            ⊗ₖ (aOp (((ptAtPOVM MB W u).mats a').val) : Matrix (dB × P.EB) _ ℂ))
        = ∑ h : Anc F m, (if dotF h v = dotF (cubeData g) v + a ∧ dotF h (indVec u)
              = g.eval u + a' then
            (((polyMarg P.SA W).mats g).val ⊗ₖ proj (weylOf W) h)
              ⊗ₖ (aOp (((ptAtPOVM MB W u).mats a').val) : Matrix (dB × P.EB) _ ℂ) else 0) := by
    intro a'
    rw [aOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul, P.mTildeAnc_mul_kron W v u a g,
      Finset.sum_filter, sum_kron']
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with h1
    · rfl
    · rw [Matrix.zero_kronecker]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => hterm a', Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hA : dotF h v = dotF (cubeData g) v + a
  · rw [if_pos ((dotF_chainLabel_eq_iff g h v a).mpr hA),
      Finset.sum_eq_single (g.eval u + dotF h (indVec u))
        (fun a' _ hne => if_neg fun hc => hne (by rw [hc.2, ← add_assoc, add_self, zero_add]))
        (fun hmem => absurd (mem_univ _) hmem)]
    exact if_pos ⟨hA, by rw [← add_assoc, add_self, zero_add]⟩
  · rw [if_neg fun hc => hA ((dotF_chainLabel_eq_iff g h v a).mp hc)]
    refine Finset.sum_eq_zero fun a' _ => if_neg fun hc => hA hc.1

/-- **The outcome the chain's index pair carries**, the paper's `(g - g_h)(u)`: the pair outcome's
value at the sampled point, shifted by the Weyl outcome's own encoding there. -/
def chainShift (u : Point F m) (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) : F :=
  p.1.eval u + dotF p.2 (indVec u)

/-- Alice's copy of the point measurement, on her whole register. -/
def ptA (W : Bas) (u : Point F m) (k : F) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  aOp (aOp (aOp (((ptAtPOVM MA W u).mats k).val)))

/-- Bob's, on his. -/
def ptB (W : Bas) (u : Point F m) (k : F) : Matrix (dB × P.EB) (dB × P.EB) ℂ :=
  aOp (((ptAtPOVM MB W u).mats k).val)

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-3`.** Inserting Alice's copy of the point measurement beside each
term of the chain costs the point measurements' own cross-consistency and nothing else. Two things
hold the bound down: the chain's terms are a projective family in the pair `(g, h)`, so the
outcomes do not interfere (`snorm_sq_sum_orthogonal'`) and the fibres of the outcome map are seen
only once (`sum_snorm_sq_proj_comp_le`, inside `sum_snorm_sq_insert_le`). -/
theorem sum_snorm_sq_insert_chain (W : Bas) (v : Anc F m) (u : Point F m) {ε : ℝ}
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (hcons : ∑ k : F, xSqNorm P.mVec (P.ptA W u k) (P.ptB W u k) ≤ ε) :
    ∑ a : F, snorm P.mVec (∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
        (aOp (P.chainOp W p) : Matrix _ _ ℂ)
          * (((1 : Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) _ ℂ)
              - aOp (P.ptA W u (chainShift u p))) * bOp (P.ptB W u (chainShift u p)))) ^ 2
      ≤ ε := by
  classical
  have hP : IsPVM fun p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m =>
      (aOp (P.chainOp W p) : Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) _ ℂ) :=
    IsPVM.aOp (isPVM_chainOp P W)
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => snorm_sq_sum_orthogonal' _ hP _ _]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => rfl]
  refine le_trans (le_of_eq ?_)
    (sum_snorm_sq_insert_le P.mVec hP (chainShift u) (P.ptA W u)
      (fun k => (IsPVM.aOp (isPVM_ptAtPOVM hprojB W u)).isSelfAdjoint k)
      (fun k => (IsPVM.aOp (isPVM_ptAtPOVM hprojB W u)).idem k) hcons)
  simp only [chainIdx]
  exact (Finset.sum_fiberwise
    (univ : Finset (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m))
    (fun p => dotF (chainLabel p.1 p.2) v)
    (fun p => snorm P.mVec ((aOp (P.chainOp W p) : Matrix _ _ ℂ)
      * (((1 : Matrix ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) _ ℂ)
          - aOp (P.ptA W u (chainShift u p)))
        * bOp (P.ptB W u (chainShift u p)))) ^ 2))

/-- **Display `eq:qld-pulling-3a`: the Weyl projector transports across the padded state.** The
two halves of the pair `hatVec` carries are maximally entangled and the projectors are symmetric,
so moving one from Alice's half to Bob's costs nothing. -/
theorem stateVec_ancProj (W : Bas) (h : Anc F m) :
    stateVec P.Φ (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))
      = stateVecB P.Φ (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h)) := by
  have hsa : (((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))ᴴ
      = (1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      proj_conjTranspose (isWeylFamily_weylOf W)]
  have hx : xSqNorm P.Φ (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))
      (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h)) = 0 := by
    rw [P.xSqNorm_aOp hsa, xSqNorm_hatVec_proj]
  rw [xSqNorm, pow_eq_zero_iff (by norm_num), norm_eq_zero, sub_eq_zero] at hx
  exact hx

/-- **Display `eq:qld-pulling-4`: the matched pairs of Weyl projectors leave the state alone.** By
the transport each matched pair acts as the projector on one side alone, and those sum to the
identity. -/
theorem sum_ancProj_mulVec (W : Bas) :
    (∑ h : Anc F m, (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))
        * MIPRE.bOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h)))) *ᵥ P.Φ = P.Φ := by
  have htr : ∀ h : Anc F m,
      (MIPRE.bOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h))) *ᵥ P.Φ
        = (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))) *ᵥ P.Φ := fun h =>
    congrArg WithLp.ofLp (P.stateVec_ancProj W h).symm
  have hidem : ∀ h : Anc F m,
      ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h) * ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h)
        = (1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h := fun h => by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      (isPVM_proj (isWeylFamily_weylOf W)).idem]
  have hone : (∑ h : Anc F m, ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))
      = (1 : Matrix (dA × Anc F m) (dA × Anc F m) ℂ) := by
    rw [← kronecker_sum_right, (isPVM_proj (isWeylFamily_weylOf W)).sum_eq_one,
      Matrix.one_kronecker_one]
  rw [Matrix.sum_mulVec]
  have hstep : ∀ h : Anc F m,
      (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))
          * MIPRE.bOp (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ proj (weylOf W) h))) *ᵥ P.Φ
        = (MIPRE.aOp (aOp ((1 : Matrix dA dA ℂ) ⊗ₖ proj (weylOf W) h))) *ᵥ P.Φ := fun h => by
    rw [← Matrix.mulVec_mulVec, htr h, Matrix.mulVec_mulVec, ← aOp_mul, ← aOp_mul, hidem h]
  rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) => hstep h, ← Matrix.sum_mulVec, ← aOp_sum,
    ← aOp_sum, hone, aOp_one, aOp_one, Matrix.one_mulVec]

end SimulPair

end First

end Endpoint

/-! ## The physical cut's operators

What the last two displays sum over. -/

section Physical

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-! ## Each party's chain summand, on its own register

Every object of `eq:qld-pulling-5` onward carries a party's whole triple, and each is named in
that party's own spelling rather than reached through `toFirst` or `toSecond`: `toFirst.EA` is
`M.Ea` by definition, but the two spellings do not unify inside an elaborated product type, and a
single occurrence of the wrong one makes the product's `HMul` instance fail to synthesize. -/

/-- **Alice's chain summand**, on `A A' Ea A''`: her pair measurement's `W`-marginal at `g`,
tensored with the Weyl spectral projector at `h`. -/
def aliceChainOp (W : Bas)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  M.toFirst.chainOp W p

/-- It is a projective family in the pair `(g, h)`, by the lemma that says the first cut's is. -/
theorem isPVM_aliceChainOp (W : Bas) : IsPVM (M.aliceChainOp W) := isPVM_chainOp M.toFirst W

/-- **Bob's**, on `B B' Eb B''` --- the mirror image, and the second cut's. -/
def bobChainOp (W : Bas)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  M.toSecond.chainOp W p

/-- It is a projective family too, by the lemma that says the second cut's is. -/
theorem isPVM_bobChainOp (W : Bas) : IsPVM (M.bobChainOp W) := isPVM_chainOp M.toSecond W

/-- **Bob's Weyl projector**, on the half `B''` of the appended pair that the physical grouping
gives him --- the outermost factor of his register. -/
def bobWeyl (W : Bas) (h : Anc F m) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  bOp (proj (weylOf W) h)

/-- **The chain's projective family on the physical cut**: Alice's pair outcome and Weyl outcome
together, against Bob's Weyl outcome. Displays `eq:qld-pulling-5` onward sum over this triple. -/
def chainP (W : Bas)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (M.aliceChainOp W t.1) * bOp (M.bobWeyl W t.2)

/-- It is projective: `aOp U * bOp V` is `U (x) V`, and each party's family is projective. -/
theorem isPVM_chainP (W : Bas) : IsPVM (M.chainP W) := by
  have hrw : M.chainP W = fun t => (M.aliceChainOp W t.1) ⊗ₖ (M.bobWeyl W t.2) :=
    funext fun t => aOp_mul_bOp_eq _ _
  rw [hrw]
  exact isPVM_kron (M.isPVM_aliceChainOp W)
    (IsPVM.bOp (isPVM_proj (isWeylFamily_weylOf W)))

/-- **Alice's hatted point measurement**, on her physical register `A A' Ea A''`. -/
def aliceHat (W : Bas) (u : Point F m) (c : F) :
    Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ :=
  aOp (aOp (hatMats MA W u c))

/-- **Bob's**, on his. -/
def bobHat (W : Bas) (u : Point F m) (c : F) :
    Matrix (((dB × Anc F m) × M.Eb) × Anc F m) (((dB × Anc F m) × M.Eb) × Anc F m) ℂ :=
  aOp (aOp (hatMats MB W u c))

/-- **The tail the chain carries at `eq:qld-pulling-5`**: Alice's gap from her own point
measurement, against Bob's point measurement at the shifted outcome `(g - g_h + g_h')(u)`. -/
def chainW (W : Bas) (u : Point F m)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (1 - M.aliceHat W u (t.1.1.eval u))
    * bOp (M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))

/-- **The sandwich splits across the parties**, each factor being local. -/
theorem chainW_sandwich (W : Bas) (u : Point F m)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    (M.chainW W u t)ᴴ * (aOp (M.aliceChainOp W t.1) * bOp (M.bobWeyl W t.2))
        * M.chainW W u t
      = aOp ((1 - M.aliceHat W u (t.1.1.eval u))ᴴ * M.aliceChainOp W t.1
            * (1 - M.aliceHat W u (t.1.1.eval u)))
        * bOp ((M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))ᴴ
            * M.bobWeyl W t.2
            * M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))) := by
  rw [chainW, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, aOp_bOp_mul_aOp_bOp]

/-- **Summing the Weyl outcome out of Alice's summand** leaves her pair measurement's marginal
alone, extended by the identity on `A''`. -/
theorem sum_aliceChainOp (W : Bas) (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (∑ h : Anc F m, M.aliceChainOp W (g, h))
      = aOp (((polyMarg M.SA W).mats g).val) := by
  rw [show (∑ h : Anc F m, M.aliceChainOp W (g, h))
      = ∑ h : Anc F m, (((polyMarg M.SA W).mats g).val) ⊗ₖ proj (weylOf W) h from rfl,
    ← kron_sum' univ, (isPVM_proj (isWeylFamily_weylOf W)).sum_eq_one]
  rfl

/-- **So the Weyl index collapses out of her sandwich**, the gap operator not depending on it. -/
theorem sum_aliceChainOp_sandwich (W : Bas) (u : Point F m)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (∑ h : Anc F m, (1 - M.aliceHat W u (g.eval u))ᴴ * M.aliceChainOp W (g, h)
        * (1 - M.aliceHat W u (g.eval u)))
      = (1 - M.aliceHat W u (g.eval u))ᴴ * aOp (((polyMarg M.SA W).mats g).val)
        * (1 - M.aliceHat W u (g.eval u)) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, M.sum_aliceChainOp W g]

/-- **The far party's factor of the chain's sandwich**: a projector on `B B'` times a Weyl
outcome on `B''`. -/
theorem bobHat_conj_bobWeyl (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (W : Bas) (u : Point F m) (c : F) (h : Anc F m) :
    (M.bobHat W u c)ᴴ * M.bobWeyl W h * M.bobHat W u c
      = (aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ)
        ⊗ₖ proj (weylOf W) h := by
  have hsa : ((aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ))ᴴ
      = aOp (hatMats MB W u c) := by
    rw [aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      SimulPair.hatMats_conjTranspose]
  have hid : (aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ)
      * aOp (hatMats MB W u c) = aOp (hatMats MB W u c) := by
    rw [← aOp_mul, (isPVM_hatMats hprojB W u).idem]
  show ((aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ) ⊗ₖ 1)ᴴ
      * (1 ⊗ₖ proj (weylOf W) h) * (aOp (hatMats MB W u c) ⊗ₖ 1) = _
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hsa,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, hid]

/-- **Alice's sandwich is positive semidefinite**, being a projector conjugated. -/
theorem posSemidef_aliceSand (W : Bas) (u : Point F m)
    (t : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    ((1 - M.aliceHat W u (t.1.eval u))ᴴ * M.aliceChainOp W t
      * (1 - M.aliceHat W u (t.1.eval u))).PosSemidef :=
  Matrix.PosSemidef.conjTranspose_mul_mul_same ((M.isPVM_aliceChainOp W).posSemidef t) _

/-- **Display `eq:qld-pulling-8`: dropping the far party.** Summed over Bob's Weyl outcome, his
factor is a projector times a projective measurement, so at most the identity. -/
theorem sum_bornProb_chainW_drop_le (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (W : Bas) (u : Point F m)
    (t : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    (∑ h' : Anc F m, bornProb M.physVec
        ((1 - M.aliceHat W u (t.1.eval u))ᴴ * M.aliceChainOp W t
          * (1 - M.aliceHat W u (t.1.eval u)))
        ((M.bobHat W u (t.1.eval u + dotF t.2 (indVec u) + dotF h' (indVec u)))ᴴ
          * M.bobWeyl W h'
          * M.bobHat W u (t.1.eval u + dotF t.2 (indVec u) + dotF h' (indVec u))))
      ≤ bornProb M.physVec ((1 - M.aliceHat W u (t.1.eval u))ᴴ * M.aliceChainOp W t
          * (1 - M.aliceHat W u (t.1.eval u))) 1 := by
  rw [Finset.sum_congr rfl fun h' (_ : h' ∈ univ) => by
    rw [M.bobHat_conj_bobWeyl hprojB W u _ h']]
  exact sum_bornProb_kron_le M.physVec (M.posSemidef_aliceSand W u t)
    (fun h' => by
      rw [aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        SimulPair.hatMats_conjTranspose])
    (fun h' => by rw [← aOp_mul, (isPVM_hatMats hprojB W u).idem])
    (isPVM_proj (isWeylFamily_weylOf W))

/-- **The bridge from the physical state back to `Phi`.** An operator that is Alice's alone, and
the identity on the half of the appended pair she holds, sees the state `lem:qld-simultaneous`
already describes. The identity is spelled out as a fourfold tensor product because the
intermediate `mVec` carries Bob's padding under `toFirst`'s name for it, and rewriting inside
that application is not type-correct. -/
theorem bornProb_physVec_aOp_kron
    (Z : Matrix ((dA × Anc F m) × M.Ea) ((dA × Anc F m) × M.Ea) ℂ) :
    bornProb M.physVec (aOp Z)
        ((((1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
          ⊗ₖ (1 : Matrix M.Eb M.Eb ℂ)) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      = bornProb M.Φ Z 1 := by
  have h1 := M.bornProb_physVec (aOp Z) (1 : Matrix dB dB ℂ) (1 : Matrix M.Eb M.Eb ℂ)
  have h2 := bornProb_regroupVec M.Φ Z (1 : Matrix dB dB ℂ) (1 : Matrix (Anc F m) (Anc F m) ℂ)
  rw [show (aOp ((1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      : Matrix ((dB × Anc F m) × M.Eb) _ ℂ) = 1 from by
    rw [Matrix.one_kronecker_one, aOp_one]] at h2
  exact h1.trans h2

/-- The same, with the identity collapsed. -/
theorem bornProb_physVec_aOp
    (Z : Matrix ((dA × Anc F m) × M.Ea) ((dA × Anc F m) × M.Ea) ℂ) :
    bornProb M.physVec (aOp Z) 1 = bornProb M.Φ Z 1 := by
  have e : ((((1 : Matrix dB dB ℂ) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
      ⊗ₖ (1 : Matrix M.Eb M.Eb ℂ)) ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ)) = 1 := by
    rw [Matrix.one_kronecker_one, Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  rw [← e]
  exact M.bornProb_physVec_aOp_kron Z

set_option maxHeartbeats 1000000 in
/-- **Displays `eq:qld-pulling-5` to `-8`.** The chain's terms on the physical cut, grouped by the
measurement outcome: projectivity turns each group into a sum of sandwiches, Bob's factor is a
projector times a Weyl outcome and so sums away, and Alice's Weyl outcome sums out of hers,
leaving the pair-measurement marginal against the complement of her own point measurement. -/
theorem sum_snorm_sq_chainP_le (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val))
    (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, snorm M.physVec
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          M.chainP W t * M.chainW W u t) ^ 2
      ≤ ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), snorm M.Φ
          (aOp (((polyMarg M.SA W).mats g).val
            * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × M.Ea) _ ℂ))))
          ^ 2 := by
  classical
  refine sum_snorm_sq_fiber_sandwich_le M.physVec (M.isPVM_chainP W) (M.chainW W u)
    (fun t => dotF (chainLabel t.1.1 t.1.2) v) ?_
  rw [Finset.sum_congr rfl fun t (_ : t ∈ univ) => by
    rw [show M.chainP W t = aOp (M.aliceChainOp W t.1) * bOp (M.bobWeyl W t.2) from rfl,
      M.chainW_sandwich W u t, ← bornProb_eq_qform], Fintype.sum_prod_type]
  refine le_trans (Finset.sum_le_sum fun t1 (_ : t1 ∈ univ) =>
    M.sum_bornProb_chainW_drop_le hprojB W u t1) ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun g _ => le_of_eq ?_
  have hexp : (1 - M.aliceHat W u (g.eval u))ᴴ * aOp (((polyMarg M.SA W).mats g).val)
        * (1 - M.aliceHat W u (g.eval u))
      = aOp ((1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × M.Ea) _ ℂ))ᴴ
          * ((polyMarg M.SA W).mats g).val
          * (1 - (aOp (hatMats MA W u (g.eval u)) : Matrix ((dA × Anc F m) × M.Ea) _ ℂ))) := by
    rw [aliceHat, ← aOp_one, ← aOp_sub, aOp_conjTranspose, ← aOp_mul, ← aOp_mul]
  rw [← bornProb_sum_left, M.sum_aliceChainOp_sandwich W u g, hexp, M.bornProb_physVec_aOp,
    snorm_sq_eq_qform, bornProb_eq_qform, bOp_one, Matrix.mul_one, aOp_conjTranspose, ← aOp_mul]
  congr 1
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (((polyMarg M.SA W).mats g).val)ᴴ,
    (isPVM_polyMarg M.SA_proj W).isSelfAdjoint g, (isPVM_polyMarg M.SA_proj W).idem g]

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-9`**: the chain's step from `eq:qld-pulling-5` to
`eq:qld-pulling-7` costs item 2 of `lem:qld-helper` and nothing more. -/
theorem sum_uniform_snorm_sq_chainP_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    ∑ u, uniform (Point F m) u * ∑ a : F, snorm M.physVec
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          M.chainP W t * M.chainW W u t) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (M.sum_snorm_sq_chainP_le hprojB W v u)
      (uniform_nonneg (Point F m) u)) ?_
  exact M.toFirst.sum_snorm_sq_polyMarg_one_sub_le (hm := hm) hψ hfail hprojB W

/-! ## The four-index family, and Bob's half of the chain for free

`eq:qld-pulling-9a` left-multiplies by Bob's own pair measurement, which is the identity, and from
there to `eq:qld-pulling-12` the chain runs over *both* parties' pairs. `chainQ` is that family,
and `endOp` --- the chain's endpoint, already in place --- is its restriction to the coupled index
set. What the mirror buys is the rest: Bob's derivation is Alice's, instantiated. -/

/-- **The chain's four-index family on the physical cut**: each party's pair outcome and Weyl
outcome together. -/
def chainQ (W : Bas)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (M.aliceChainOp W q.1) * bOp (M.bobChainOp W q.2)

set_option maxHeartbeats 1000000 in
/-- It is projective, each party's family being so. -/
theorem isPVM_chainQ (W : Bas) : IsPVM (M.chainQ W) := by
  have hrw : M.chainQ W = fun q => (M.aliceChainOp W q.1) ⊗ₖ (M.bobChainOp W q.2) :=
    funext fun q => aOp_mul_bOp_eq _ _
  rw [hrw]
  exact isPVM_kron (M.isPVM_aliceChainOp W) (M.isPVM_bobChainOp W)

/-- **`endOp` is that family, restricted to the coupled index set** --- so display
`eq:qld-pulling-12` and the displays leading to it speak about one and the same projective
measurement. -/
theorem endOp_eq_sum_chainQ (W : Bas) (v : Anc F m) (a : F) :
    M.endOp W v a = ∑ q ∈ coupledIdx v a, M.chainQ W q :=
  Finset.sum_congr rfl fun _ _ => (aOp_mul_bOp_eq _ _).symm

/-- **Display `eq:qld-pulling-9a`**: left-multiplying by Bob's own pair measurement, which is the
identity, refines the chain's three-index family into the four-index one. -/
theorem sum_poly_chainQ (W : Bas)
    (t1 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) (h' : Anc F m) :
    (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d), M.chainQ W (t1, (g', h')))
      = M.chainP W (t1, h') := by
  have hsum : (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d),
      M.bobChainOp W (g', h')) = M.bobWeyl W h' :=
    M.toSecond.sum_poly_chainOp W h'
  show (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d),
      aOp (M.aliceChainOp W t1) * bOp (M.bobChainOp W (g', h')))
    = aOp (M.aliceChainOp W t1) * bOp (M.bobWeyl W h')
  rw [← hsum, bOp_sum, Finset.mul_sum]

set_option maxHeartbeats 1000000 in
/-- **Bob's `eq:qld-pulling-5` to `-8`, for free.** The same lemma at the mirror: what it asks of
Bob there it asks of Alice here, and the state it is read on is the physical state with the two
parties written in the other order. The paper's ``an entirely analogous derivation'' for the
second party is discharged this way for the whole chain, not lemma by lemma. -/
theorem mirror_sum_snorm_sq_chainP_le (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, snorm (M.physVec ∘ Prod.swap)
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          M.mirror.chainP W t * M.mirror.chainW W u t) ^ 2
      ≤ ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), snorm M.Φ'
          (aOp (((polyMarg M.SA' W).mats g).val
            * (1 - (aOp (hatMats MB W u (g.eval u)) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ))))
          ^ 2 := by
  rw [← M.mirror_physVec]
  exact M.mirror.sum_snorm_sq_chainP_le hprojA W v u

/-! ## `eq:qld-pulling-10`, down to its Cauchy--Schwarz step

The second of the chain's two remaining estimates. It runs over the four-index family and over the
pairs whose outcomes *disagree* at the sampled point, and the reduction below is everything before
the swap: projectivity, one relaxation, and two completeness sums. -/

end MirrorSimul

/-- **The outcome the chain's four-index pair carries**, the paper's `(g - g_h + g_h')(u)`. -/
def chainQShift (u : Point F m)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) : F :=
  q.1.1.eval u + dotF q.1.2 (indVec u) + dotF q.2.2 (indVec u)

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)


/-- **Bob's tail at `eq:qld-pulling-9a`**, at an arbitrary outcome: his point measurement, and
nothing on Alice. -/
def bobTail (W : Bas) (u : Point F m) (c : F) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  aOp (1 : Matrix (((dA × Anc F m) × M.Ea) × Anc F m) (((dA × Anc F m) × M.Ea) × Anc F m) ℂ)
    * bOp (M.bobHat W u c)

set_option maxHeartbeats 1000000 in
/-- **The sandwich splits across the parties**, Alice's factor untouched. -/
theorem bobTail_sandwich (W : Bas) (u : Point F m) (c : F)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    (M.bobTail W u c)ᴴ * M.chainQ W q * M.bobTail W u c
      = aOp (M.aliceChainOp W q.1)
        * bOp ((M.bobHat W u c)ᴴ * M.bobChainOp W q.2 * M.bobHat W u c) := by
  rw [bobTail, chainQ, aOp_bOp_conjTranspose, aOp_bOp_mul_aOp_bOp, aOp_bOp_mul_aOp_bOp,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- Bob's sandwiched pair-measurement marginal, on `B B' Eb`. -/
def bobSand (W : Bas) (u : Point F m) (c : F)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    Matrix ((dB × Anc F m) × M.Eb) ((dB × Anc F m) × M.Eb) ℂ :=
  (aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ)ᴴ
    * ((polyMarg M.SA' W).mats g).val
    * (aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ)

/-- **Bob's factor of that sandwich**: his point measurement conjugating his pair measurement's
marginal, tensored with his Weyl outcome. -/
theorem bobHat_conj_bobChainOp (W : Bas) (u : Point F m) (c : F)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    (M.bobHat W u c)ᴴ * M.bobChainOp W p * M.bobHat W u c
      = M.bobSand W u c p.1 ⊗ₖ proj (weylOf W) p.2 := by
  show ((aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ) ⊗ₖ 1)ᴴ
      * ((((polyMarg M.SA' W).mats p.1).val) ⊗ₖ proj (weylOf W) p.2)
      * ((aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ) ⊗ₖ 1) = _
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rfl

/-- **The sandwich, fully split.** -/
theorem bobTail_sandwich_kron (W : Bas) (u : Point F m) (c : F)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    qform M.physVec ((M.bobTail W u c)ᴴ * M.chainQ W q * M.bobTail W u c)
      = bornProb M.physVec (M.aliceChainOp W q.1)
        (M.bobSand W u c q.2.1 ⊗ₖ proj (weylOf W) q.2.2) := by
  rw [M.bobTail_sandwich W u c q, M.bobHat_conj_bobChainOp W u c q.2, ← bornProb_eq_qform]

/-- **The tail at the chain's own outcome**, the paper's `(g - g_h + g_h')(u)`. -/
def chainV (W : Bas) (u : Point F m)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ :=
  M.bobTail W u (chainQShift u q)

set_option maxHeartbeats 1000000 in
/-- **The first two steps of `eq:qld-pulling-10`'s justification.** Projectivity turns the grouped
squared norm into a sum of sandwiches over the disagreeing pairs; each of those is one term of a
sum over *all* outcomes the pair's own value excludes, and the rest of that sum is nonnegative; and
then the constraint tying the outcome to the index may be dropped. -/
theorem sum_snorm_sq_chainQ_disagree_le (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, snorm M.physVec
        (∑ q ∈ (univ.filter fun q => chainQShift u q ≠ q.2.1.eval u).filter
              fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
          M.chainQ W q * M.chainV W u q) ^ 2
      ≤ ∑ q, ∑ c ∈ univ.filter fun c : F => c ≠ q.2.1.eval u,
          qform M.physVec ((M.bobTail W u c)ᴴ * M.chainQ W q * M.bobTail W u c) := by
  classical
  have hnn : ∀ (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) (c : F),
      0 ≤ qform M.physVec ((M.bobTail W u c)ᴴ * M.chainQ W q * M.bobTail W u c) :=
    fun q c => qform_sandwich_nonneg M.physVec ((M.isPVM_chainQ W).posSemidef q) _
  refine sum_snorm_sq_fiber_sandwich_subset_le M.physVec (M.isPVM_chainQ W)
    (fun q => M.chainV W u q) (fun q => dotF (chainLabel q.1.1 q.1.2) v)
    (univ.filter fun q => chainQShift u q ≠ q.2.1.eval u) ?_
  refine le_trans (Finset.sum_le_sum fun q hq => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun q _ _ => Finset.sum_nonneg fun c _ => hnn q c)
  exact Finset.single_le_sum (f := fun c : F =>
      qform M.physVec ((M.bobTail W u c)ᴴ * M.chainQ W q * M.bobTail W u c))
    (fun c _ => hnn q c)
    (Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hq).2⟩)

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-13a`**: Alice's family and Bob's Weyl outcome both sum to the
identity, so what is left of the bound carries neither. -/
theorem sum_qform_bobTail_eq (W : Bas) (u : Point F m) :
    (∑ q, ∑ c ∈ univ.filter fun c : F => c ≠ q.2.1.eval u,
        qform M.physVec ((M.bobTail W u c)ᴴ * M.chainQ W q * M.bobTail W u c))
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          ∑ c ∈ univ.filter fun c : F => c ≠ g.eval u,
            bornProb M.physVec 1 (aOp (M.bobSand W u c g)) := by
  classical
  have hq1 : ∀ (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h : Anc F m) (c : F),
      (∑ q1 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
          bornProb M.physVec (M.aliceChainOp W q1)
            (M.bobSand W u c g ⊗ₖ proj (weylOf W) h))
        = bornProb M.physVec 1 (M.bobSand W u c g ⊗ₖ proj (weylOf W) h) := by
    intro g h c
    rw [← bornProb_sum_left, (M.isPVM_aliceChainOp W).sum_eq_one]
  have hh : ∀ (g : LowIndDegPoly (F := F) (m := m) (d := d)) (c : F),
      (∑ h : Anc F m, bornProb M.physVec 1 (M.bobSand W u c g ⊗ₖ proj (weylOf W) h))
        = bornProb M.physVec 1 (aOp (M.bobSand W u c g)) := by
    intro g c
    rw [← bornProb_sum_right, ← kron_sum' univ,
      (isPVM_proj (isWeylFamily_weylOf W)).sum_eq_one]
    rfl
  have key : ∀ q2 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
      (∑ q1 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
          ∑ c ∈ univ.filter fun c : F => c ≠ q2.1.eval u,
            bornProb M.physVec (M.aliceChainOp W q1)
              (M.bobSand W u c q2.1 ⊗ₖ proj (weylOf W) q2.2))
        = ∑ c ∈ univ.filter fun c : F => c ≠ q2.1.eval u,
            bornProb M.physVec 1 (M.bobSand W u c q2.1 ⊗ₖ proj (weylOf W) q2.2) := by
    intro q2
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => hq1 q2.1 q2.2 c
  rw [Finset.sum_congr rfl fun q (_ : q ∈ univ) => Finset.sum_congr rfl fun c _ =>
      M.bobTail_sandwich_kron W u c q,
    Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_congr rfl fun q2 (_ : q2 ∈ univ) => key q2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  show (∑ h : Anc F m, ∑ c ∈ univ.filter fun c : F => c ≠ g.eval u,
      bornProb M.physVec 1 (M.bobSand W u c g ⊗ₖ proj (weylOf W) h))
    = ∑ c ∈ univ.filter fun c : F => c ≠ g.eval u,
      bornProb M.physVec 1 (aOp (M.bobSand W u c g))
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => hh g c

end MirrorSimul

end Physical

end MIPRE.QLD

end
