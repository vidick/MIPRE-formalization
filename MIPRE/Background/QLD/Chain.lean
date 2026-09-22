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

end SimulPair

end First

end Endpoint

end MIPRE.QLD

end
