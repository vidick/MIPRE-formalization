/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Multilinear
import MIPRE.Background.QLD.SwapUnitary

/-!
# Item 1 of `lem:qld-exact-paulis`, read as `M~` (the paper's `eq:tilde_M`)

`MIPRE/Background/QLD/Multilinear.lean` proves the agreement the appendix's chain establishes,

`E_u sum_g <S^W_g (x) M^(Point,W),u_{coded(g).ind_m(u)}> >= 1 - delta_S - 2 (mass off the good
set)`,

as a sum over the *outcomes* of the simultaneous measurement. The paper states the same thing as a
closeness between two **measurements**: `M~^{W,ind_m(u)}_a`, an operator on one party, and the
strategy's `(Point, W)` measurement on the other. This file is that reading.

## Why it is a reindexing and not a new estimate

The paper's expanded state is
`|psi-hat> = |psi>_{A B} (x) |EPR>_{A' A''} (x) |EPR>_{B' B''}`, with `A' A''` a maximally
entangled pair *local to Alice* and `B' B''` one local to Bob, and it is read along two cuts,
`A A' | B A''` and `B B' | A B''` --- one per orientation of `lem:qld-simultaneous`. Neither cut is
the physical one: each splits a local pair. `MIPRE.QLD.hatVec` is one such cut, and it is all
`lem:qld-simultaneous` and `lem:qld-helper` need, since each uses one orientation at a time.

`M~^{W,u-tilde}_a = sum_g S-hat^W_g (x) tau^W_{coded(g) . u-tilde - a}(u-tilde)` is different: it
wants the pair measurement and the generalized Pauli on *disjoint registers of one party*,
`A A'` and `A''`. In the `hatVec` cut the register `A''` sits with the opposite party. So writing
`M~` as a single matrix is a regrouping of the same six registers along a third cut,
`A A' A'' | B`, and every Born probability transports across it by `bornProb_regroupVec`, which is
one entry computation. No second entangled pair and no new estimate are involved.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## Regrouping the two parties' registers -/

section Regroup

variable {R S T E : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]

/-- **The regrouping** that moves the ancilla factor `T` from the second party to the first. -/
def regroupEquiv : R × ((S × T) × E) ≃ (R × T) × (S × E) where
  toFun p := ((p.1, p.2.1.2), (p.2.1.1, p.2.2))
  invFun p := (p.1.1, ((p.2.1, p.1.2), p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The state, read along the regrouped cut. -/
def regroupVec (ψ : R × ((S × T) × E) → ℂ) : (R × T) × (S × E) → ℂ :=
  ψ ∘ (regroupEquiv (R := R) (S := S) (T := T) (E := E)).symm

/-- **The quadratic form is carried by any reindexing of the whole space.** The bipartite version
`quadForm_reindex` reindexes the two parties separately and so cannot move a factor between them;
this one makes no reference to a cut. -/
theorem qform_comp_equiv {N N' : Type*} [Fintype N] [Fintype N'] (e : N ≃ N') (ψ : N → ℂ)
    (A : Matrix N N ℂ) :
    star (ψ ∘ e.symm) ⬝ᵥ ((Matrix.reindex e e A) *ᵥ (ψ ∘ e.symm)) = star ψ ⬝ᵥ (A *ᵥ ψ) := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  have hcomp : (ψ ∘ e.symm) ∘ e.symm.symm = ψ := by
    rw [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rw [hcomp]
  show ∑ p, star ψ (e.symm p) * (A *ᵥ ψ) (e.symm p) = ∑ p, star ψ p * (A *ᵥ ψ) p
  exact Equiv.sum_comp e.symm fun p => star ψ p * (A *ᵥ ψ) p

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
  [Fintype E] in
/-- The same operator, grouped the two ways. -/
theorem reindex_regroupEquiv (X : Matrix R R ℂ) (M : Matrix S S ℂ) (N : Matrix T T ℂ) :
    Matrix.reindex (regroupEquiv (R := R) (S := S) (T := T) (E := E))
        (regroupEquiv (R := R) (S := S) (T := T) (E := E))
        (X ⊗ₖ (aOp (M ⊗ₖ N) : Matrix ((S × T) × E) ((S × T) × E) ℂ))
      = (X ⊗ₖ N) ⊗ₖ (aOp M : Matrix (S × E) (S × E) ℂ) := by
  ext p q
  obtain ⟨⟨r, t⟩, s, e⟩ := p
  obtain ⟨⟨r', t'⟩, s', e'⟩ := q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, regroupEquiv, Equiv.coe_fn_symm_mk,
    kroneckerMap_apply, aOp]
  ring

omit [DecidableEq R] [DecidableEq S] [DecidableEq T] in
/-- **The Born probability across the regrouped cut.** -/
theorem bornProb_regroupVec (ψ : R × ((S × T) × E) → ℂ) (X : Matrix R R ℂ) (M : Matrix S S ℂ)
    (N : Matrix T T ℂ) :
    bornProb (regroupVec ψ) (X ⊗ₖ N) (aOp M) = bornProb ψ X (aOp (M ⊗ₖ N)) := by
  rw [bornProb, bornProb, regroupVec, ← reindex_regroupEquiv, qform_comp_equiv]

omit [DecidableEq R] [DecidableEq S] [DecidableEq T] [DecidableEq E] in
/-- A regrouped unit vector is a unit vector. -/
theorem regroupVec_unit {ψ : R × ((S × T) × E) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (regroupVec ψ) ⬝ᵥ regroupVec ψ = 1 := by
  rw [← hψ]
  exact Equiv.sum_comp (regroupEquiv (R := R) (S := S) (T := T) (E := E)).symm
    fun p => star ψ p * ψ p

end Regroup

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## `mTilde` is a projective measurement -/

section PVM

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Fintype G] [DecidableEq G]
  {dA : Type*} [Fintype dA] [DecidableEq dA]

/-- `mTilde` is block diagonal along the pair measurement, so `sTensor_mul` applies to it. -/
theorem mTilde_eq_sTensor (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
    (w : (n → F) → Matrix (n → F) (n → F) ℂ) (u : n → F) (a : F) :
    mTilde S pi cd w u a = sTensor S fun p => syn w u (dotF (cd (pi p)) u + a) :=
  mTilde_eq_sum S pi cd w u a

/-- **The measurement `M~^{W,u}` is projective.** Its elements multiply factorwise because the
pair measurement is projective, and factorwise they are the ancilla's syndrome projectors. -/
theorem isPVM_mTilde {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S) (pi : G × G → G)
    (cd : G → (n → F)) {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w)
    (u : n → F) : IsPVM (mTilde S pi cd w u) where
  isSelfAdjoint a := by
    rw [mTilde_eq_sTensor, sTensor_conjTranspose hS]
    exact congrArg (sTensor S) (funext fun _ => (isPVM_syn hw u).isSelfAdjoint _)
  idem a := by
    rw [mTilde_eq_sTensor, sTensor_mul hS]
    exact congrArg (sTensor S) (funext fun _ => (isPVM_syn hw u).idem _)
  sum_eq_one := by
    have hone : ∀ c : F, (∑ a : F, syn w u (c + a)) = 1 := fun c => by
      rw [← (isPVM_syn hw u).sum_eq_one]
      exact Equiv.sum_comp (Equiv.addLeft c) fun b => syn w u b
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => mTilde_eq_sTensor S pi cd w u a,
      show (∑ a : F, sTensor S fun p => syn w u (dotF (cd (pi p)) u + a))
          = sTensor S fun p => ∑ a : F, syn w u (dotF (cd (pi p)) u + a) from by
        show (∑ a : F, ∑ p, S p ⊗ₖ syn w u (dotF (cd (pi p)) u + a))
          = ∑ p, S p ⊗ₖ ∑ a : F, syn w u (dotF (cd (pi p)) u + a)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => (kron_sum univ _ _).symm,
      show (fun p => ∑ a : F, syn w u (dotF (cd (pi p)) u + a))
          = fun _ : G × G => (1 : Matrix (n → F) (n → F) ℂ) from
        funext fun p => hone _,
      sTensor_one hS]

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [DecidableEq n] in
/-- The pairing is additive in its right argument too. -/
theorem dotF_add_right (a u v : n → F) : dotF a (u + v) = dotF a u + dotF a v := by
  rw [dotF, dotF, dotF, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by
    show a l * (u l + v l) = a l * u l + a l * v l
    ring

omit [Fintype F] [DecidableEq F] [DecidableEq n] [Fintype G] [DecidableEq G] in
/-- So is the phase the first tensor factor carries. -/
theorem cdPhase_add (pi : G × G → G) (cd : G → (n → F)) (e : F) (u v : n → F) (p : G × G) :
    cdPhase pi cd e (u + v) p = cdPhase pi cd e u p + cdPhase pi cd e v p := by
  simp only [cdPhase]
  rw [dotF_add_right, mul_add, map_add]

/-- **Linearity in the argument**: `W~^e(u) W~^e(v) = W~^e(u + v)`, exactly. Both tensor factors
are additive --- the sign because the pairing is, the generalized Pauli by the Weyl family's own
group law --- so no error term and no hypothesis beyond projectivity appears. With
`wTilde_mul_wTilde` this is the second of the two Pauli group relations
`lem:qld-exact-paulis` asserts. -/
theorem wTilde_mul_add {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S) (pi : G × G → G)
    (cd : G → (n → F)) {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) (e : F)
    (u v : n → F) :
    wTilde S pi cd w e u * wTilde S pi cd w e v = wTilde S pi cd w e (u + v) := by
  rw [wTilde_eq, wTilde_eq, wTilde_eq, ← Matrix.mul_kronecker_mul, pvmObs_mul hS, smul_add,
    hw.map_add]
  congr 1
  refine congrArg (pvmObs S) (funext fun p => ?_)
  simp only [Pi.mul_apply]
  rw [cdPhase_add, sgn_add]

end PVM

/-! ## The point measurement at a point, and the shift -/

section Shift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

omit [Fintype F] [DecidableEq F] in
/-- In characteristic two a sum is its own difference. -/
theorem add_self_eq_zero' (a : F) : a + a = 0 := by
  rw [← two_mul, MIPRE.Weyl.two_eq_zero, zero_mul]

omit [Fintype F] [DecidableEq F] in
/-- The partner of `a` in a fibre of the sum, in characteristic two. -/
theorem add_eq_iff_eq_add (a b c : F) : a + b = c ↔ b = c + a := by
  constructor
  · rintro rfl
    rw [add_comm a b, add_assoc, add_self_eq_zero', add_zero]
  · rintro rfl
    rw [← add_assoc, add_comm a c, add_assoc, add_self_eq_zero', add_zero]

variable {d' : Type} [Fintype d'] [DecidableEq d']

/-- The strategy's `(Point, W)` measurement at `u`, read as a field element. -/
def ptAtPOVM (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) : POVM F d' :=
  (M (.point W u)).map rdVal

theorem hatPtPOVM_eq_kron (M : Question F m → POVM (Answer F m d) d') (W : Bas)
    (u : Point F m) :
    hatPtPOVM M W u = ((ptAtPOVM M W u).kron (synPOVM W u)).map fun p => p.1 + p.2 := rfl

/-- **The convolution, summed along the shift.** In characteristic two `c + a` is the partner of
`a` in the fibre of the sum over `c`, so summing the product family along `a` is summing it over
that fibre --- which is the hatted point measurement at `c`. This is the step that turns
`mTilde`'s defining sum into the hatted point measurement the helper's agreement names. -/
theorem sum_kron_syn_eq_hatMats (M : Question F m → POVM (Answer F m d) d') (W : Bas)
    (u : Point F m) (c : F) :
    ∑ a : F, (((ptAtPOVM M W u).mats a).val ⊗ₖ ((synPOVM W u).mats (c + a)).val)
      = hatMats M W u c := by
  classical
  rw [hatMats, hatPtPOVM_eq_kron, POVM.map_mats, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (c + a) (fun b _ hb => if_neg fun h => hb
      ((add_eq_iff_eq_add a b c).mp h)) fun hmem => absurd (mem_univ (c + a)) hmem,
    if_pos ((add_eq_iff_eq_add a (c + a) c).mpr rfl), POVM.kron_mats]

end Shift

/-! ## Item 1, as a closeness of two measurements -/

section Item

/- The index of `mTilde`'s matrices is a four-fold product, `((dA x Anc) x EA) x Anc`, whose
`DecidableEq` runs past the default instance-size bound --- each half alone is found, the product
is not. Raised here and nowhere else. -/
set_option synthInstance.maxSize 1000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The marginal `sCoarse` of `ExactPauli.lean` is `polyMarg`. -/
theorem sCoarse_eq_polyMarg {R : Type*} [Fintype R] [DecidableEq R]
    (S : POVM (PolyPair F m d) R) (W : Bas)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    sCoarse (fun p => ((S.mats p).val)) (PolyPair.proj W) g = ((polyMarg S W).mats g).val :=
  (POVM.map_mats _ _ _).symm

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **The state along the third cut.** `hatVec`'s cut puts the register the paper calls `A''`
with the opposite party; this one puts it with Alice, which is where `mTilde` needs it. -/
def mVec : ((((dA × Anc F m) × P.EA) × Anc F m) × (dB × P.EB)) → ℂ := regroupVec P.Φ

theorem mVec_unit : star P.mVec ⬝ᵥ P.mVec = 1 := regroupVec_unit P.Φ_unit

/-- **The paper's `M~^{W, ind_m(u)}_a`** (`eq:tilde_M`): the simultaneous pair measurement of
`lem:qld-simultaneous` tensored with the ancilla's generalized Pauli at the shifted syndrome. -/
def mTildeAt (W : Bas) (u : Point F m) (a : F) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  mTilde (fun p => ((P.SA.mats p).val)) (PolyPair.proj W) cubeData (weylOf W) (indVec u) a

/-- It is a projective measurement. -/
theorem isPVM_mTildeAt (W : Bas) (u : Point F m) : IsPVM (P.mTildeAt W u) :=
  isPVM_mTilde P.SA_proj (PolyPair.proj W) cubeData (isWeylFamily_weylOf W) (indVec u)

theorem mTildeAt_eq (W : Bas) (u : Point F m) (a : F) :
    P.mTildeAt W u a
      = ∑ g, ((polyMarg P.SA W).mats g).val
          ⊗ₖ ((synPOVM W u).mats (dotF (cubeData g) (indVec u) + a)).val :=
  Finset.sum_congr rfl fun g _ => by rw [sCoarse_eq_polyMarg, synPOVM_mats]

/-- **One term of the agreement, across the cut.** -/
theorem bornProb_mTildeAt (W : Bas) (u : Point F m) (a : F) :
    bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val))
      = ∑ g, bornProb P.Φ (((polyMarg P.SA W).mats g).val)
          (aOp ((((ptAtPOVM MB W u).mats a).val)
            ⊗ₖ ((synPOVM W u).mats (dotF (cubeData g) (indVec u) + a)).val)) := by
  rw [P.mTildeAt_eq W u a, bornProb_sum_left, mVec]
  exact Finset.sum_congr rfl fun g _ => bornProb_regroupVec _ _ _ _

/-- **The agreement of `M~^{W,ind_m(u)}` with the strategy's point measurement is the outcome sum
the helper's chain bounds.** -/
theorem sum_bornProb_mTildeAt (W : Bas) (u : Point F m) :
    ∑ a : F, bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val))
      = ∑ g, bornProb P.Φ (((polyMarg P.SA W).mats g).val)
          (aOp (hatMats MB W u (dotF (cubeData g) (indVec u)))) := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => P.bornProb_mTildeAt W u a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← sum_kron_syn_eq_hatMats MB W u (dotF (cubeData g) (indVec u)), aOp_sum,
    bornProb_sum_right]

/-- **Item 1 of `lem:qld-exact-paulis`**: the measurement `M~^{W,ind_m(u)}` agrees with the
strategy's `(Point, W)` measurement with probability at least `1 - delta_qld`, on average over a
uniform point, where
`delta_qld = delta_S + 2 (delta_S + sqrt(688 eps) + md/q)`. -/
theorem sum_bornProb_mTilde_ge {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (W : Bas) :
    1 - (δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F))
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F,
          bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val)) := by
  have h := P.sum_bornProb_cubeData_ge (hm := hm) hψ hfail hprojB hd W
  have hrw : ∀ u : Point F m,
      uniform (Point F m) u * ∑ g, bornProb P.Φ (((polyMarg P.SA W).mats g).val)
          (aOp (hatMats MB W u (dotF (cubeData g) (indVec u))))
        = uniform (Point F m) u * ∑ a : F,
          bornProb P.mVec (P.mTildeAt W u a) (aOp (((ptAtPOVM MB W u).mats a).val)) :=
    fun u => by rw [P.sum_bornProb_mTildeAt W u]
  rwa [Finset.sum_congr rfl fun u (_ : u ∈ univ) => hrw u] at h

/-- **Item 1 of `lem:qld-exact-paulis` as the paper states it**: on average over a uniform point,
the measurement `M~^{W, ind_m(u)}` and the strategy's `(Point, W)` measurement are consistent to
within `delta_S + 2 (delta_S + sqrt(688 eps) + md/q)`. -/
theorem inconsistency_mTilde_le {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d) (W : Bas) :
    inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (ptAtPOVM MB W u).aOp)
      ≤ δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F) := by
  have hd0 := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) P.mVec_unit
    (fun u => (P.isPVM_mTildeAt W u).toPOVM) fun u => (ptAtPOVM MB W u).aOp (E := P.EB)
  have hge := P.sum_bornProb_mTilde_ge (hm := hm) hψ hfail hprojB hd W
  simp only [IsPVM.toPOVM_mats, POVM.aOp_mats] at hd0
  linarith

/-! ### The exact half, at the same data

`wTilde` and its three relations are proved in `MIPRE/Background/QLD/ExactPauli.lean` for an
abstract projective pair measurement and Weyl family. Instantiating them at the simultaneous
measurement of a `SimulPair` puts the exact half and the approximate half of
`lem:qld-exact-paulis` on the *same* objects, which is what the lemma asserts. -/

/-- **The paper's `W~^e(u-tilde)`** (`eq:def-tildewj`) at the simultaneous pair measurement. -/
def wTildeAt (W : Bas) (e : F) (v : Anc F m) :
    Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  wTilde (fun p => ((P.SA.mats p).val)) (PolyPair.proj W) cubeData (weylOf W) e v

/-- It is self-adjoint. -/
theorem wTildeAt_conjTranspose (W : Bas) (e : F) (v : Anc F m) :
    (P.wTildeAt W e v)ᴴ = P.wTildeAt W e v :=
  wTilde_conjTranspose P.SA_proj (isWeylFamily_weylOf W) e v

/-- It squares to the identity, so it is a genuine `+-1`-valued observable. -/
theorem wTildeAt_mul_self (W : Bas) (e : F) (v : Anc F m) :
    P.wTildeAt W e v * P.wTildeAt W e v = 1 :=
  wTilde_mul_self P.SA_proj (isWeylFamily_weylOf W) e v

/-- **Linearity in the argument**, exactly. -/
theorem wTildeAt_mul_add (W : Bas) (e : F) (v v' : Anc F m) :
    P.wTildeAt W e v * P.wTildeAt W e v' = P.wTildeAt W e (v + v') :=
  wTilde_mul_add P.SA_proj _ _ (isWeylFamily_weylOf W) e v v'

/-- **The exact twisted commutation relation**, with the general phase and no case split. -/
theorem wTildeAt_mul_wTildeAt (e e' : F) (v v' : Anc F m) :
    P.wTildeAt .X e v * P.wTildeAt .Z e' v'
      = sgn (Algebra.trace (ZMod 2) F (e * e' * dotF v v'))
        • (P.wTildeAt .Z e' v' * P.wTildeAt .X e v) :=
  wTilde_mul_wTilde P.SA_proj e e' v v'

end SimulPair

end Item

end MIPRE.QLD


end
