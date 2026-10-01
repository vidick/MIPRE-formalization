/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Multilinear
public import MIPRE.Background.QLD.SwapUnitary

@[expose] public section

/-!
# Item 1 of `lem:qld-exact-paulis`, read as `M~` (the paper's `eq:tilde_M`)

`MIPRE/Background/QLD/Multilinear.lean` proves the agreement the appendix's chain establishes,

`E_u sum_g <S^W_g (x) M^(Point,W),u_{coded(g).ind_m(u)}> >= 1 - delta_S - 2 (mass off the good
set)`,

as a sum over the *outcomes* of the simultaneous measurement. The paper states the same thing as a
closeness between two **measurements**: `M~^{W,ind_m(u)}_a`, an operator on one party, and the
strategy's `(Point, W)` measurement on the other. This file is that reading.

## Why it is a change of cut and not a new estimate

The paper's expanded state is
`|psi-hat> = |psi>_{A B} (x) |EPR>_{A' A''} (x) |EPR>_{B' B''}`, with `A' A''` a maximally
entangled pair *local to Alice* and `B' B''` one local to Bob, and it is read along two cuts,
`A A' | B A''` and `B B' | A B''` --- one per orientation of `lem:qld-simultaneous`. Neither cut is
the physical one: each splits a local pair. The first cut of the physical model (`cut1`) is one
such cut, and it is all `lem:qld-simultaneous` and `lem:qld-helper` need, since each uses one
orientation at a time.

`M~^{W,u-tilde}_a = sum_g S-hat^W_g (x) tau^W_{coded(g) . u-tilde - a}(u-tilde)` is different: it
wants the pair measurement and the generalized Pauli on *disjoint registers of one party*,
`A A'` and `A''`. In the first cut the register `A''` sits with the opposite party. So writing
`M~` as a single operator of one player is reading the same registers along a third cut,
`A A' A'' | B`, which is the physical model `phys` itself; every Born probability transports
across it by the reading lemmas `cut1_πA` and `cut1_πB` of the first cut
(`phys_bornProb_compHom_smulKron`). No second entangled pair and no new estimate are involved.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The pair measurement is the
`SA` of a `SimulPair M S K ι δ`, a projective measurement in the first algebra `𝒜'` of the model
`K`; `mTilde` and `wTilde` of `ExactPauli.lean` are taken over that algebra, so `mTildeAt` and
`wTildeAt` are matrices over `𝒜'` on the register `Anc F m` (register outer, `smulKron`). For a
pair measurement on the first cut of the physical state (`CutSimul N S K δ`), `𝒜'` is the matrices
over `𝒜` on `(Ea, A')`, and `compHom` of `mTildeAt` is an operator of the physical model's first
player on `(A'', (Ea, A'))`: that is the matrix `mVec` reading, whose state is now the physical
state, and whose regrouping `regroupVec` is the reading lemma of the first cut. The strategy's
point measurement is read in the physical model with the registers inert (`physInert`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

/-! ## `mTilde` is a projective measurement -/

section PVM

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Fintype G] [DecidableEq G]
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

/-- `mTilde` is block diagonal along the pair measurement, so `sTensor_mul` applies to it. -/
theorem mTilde_eq_sTensor (S : G × G → R) (pi : G × G → G) (cd : G → (n → F))
    (w : (n → F) → Matrix (n → F) (n → F) ℂ) (u : n → F) (a : F) :
    mTilde S pi cd w u a = sTensor S fun p => syn w u (dotF (cd (pi p)) u + a) :=
  mTilde_eq_sum S pi cd w u a

/-- **The measurement `M~^{W,u}` is projective.** Its elements multiply factorwise because the
pair measurement is projective, and factorwise they are the ancilla's syndrome projectors. -/
theorem isPVM_mTilde [StarModule ℂ R] {S : G × G → R} (hS : IsPVMIn S) (pi : G × G → G)
    (cd : G → (n → F)) {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w)
    (u : n → F) : IsPVMIn (mTilde S pi cd w u) where
  star_eq a := by
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
        show (∑ a : F, ∑ p, smulKron (S p) (syn w u (dotF (cd (pi p)) u + a)))
          = ∑ p, smulKron (S p) (∑ a : F, syn w u (dotF (cd (pi p)) u + a))
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => (kron_sum univ _ _).symm,
      show (fun p => ∑ a : F, syn w u (dotF (cd (pi p)) u + a))
          = fun _ : G × G => (1 : Matrix (n → F) (n → F) ℂ) from
        funext fun p => hone _,
      sTensor_one hS]
  orthogonal {a b} hab := by
    rw [mTilde_eq_sTensor, mTilde_eq_sTensor, sTensor_mul hS,
      show (fun p => syn w u (dotF (cd (pi p)) u + a) * syn w u (dotF (cd (pi p)) u + b))
          = fun _ : G × G => (0 : Matrix (n → F) (n → F) ℂ) from
        funext fun p => (isPVM_syn hw u).orthogonal fun h => hab (add_left_cancel h)]
    show (∑ p, smulKron (S p) (0 : Matrix (n → F) (n → F) ℂ)) = 0
    simp only [smulKron_zero_right, Finset.sum_const_zero]

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
theorem wTilde_mul_add {S : G × G → R} (hS : IsPVMIn S) (pi : G × G → G)
    (cd : G → (n → F)) {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) (e : F)
    (u v : n → F) :
    wTilde S pi cd w e u * wTilde S pi cd w e v = wTilde S pi cd w e (u + v) := by
  rw [wTilde_eq, wTilde_eq, wTilde_eq, smulKron_mul, hS.pvmObs_mul, smul_add, hw.map_add]
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

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The strategy's `(Point, W)` measurement at `u`, read as a field element. -/
def ptAtPOVM (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) :
    POVMIn F R :=
  (P (.point W u)).map rdVal

variable [Algebra ℂ R] [StarModule ℂ R] [StarProper R]

theorem hatPtPOVM_eq_kron (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (u : Point F m) :
    hatPtPOVM P W u
      = (kronIn (ptAtPOVM P W u) (synPOVM W u) (isPVM_synPOVM W u)).map fun p => p.1 + p.2 :=
  rfl

/-- **The convolution, summed along the shift.** In characteristic two `c + a` is the partner of
`a` in the fibre of the sum over `c`, so summing the product family along `a` is summing it over
that fibre --- which is the hatted point measurement at `c`. This is the step that turns
`mTilde`'s defining sum into the hatted point measurement the helper's agreement names. -/
theorem sum_kron_syn_eq_hatMats (P : Question F m → POVMIn (Answer F m d) R) (W : Bas)
    (u : Point F m) (c : F) :
    ∑ a : F, smulKron ((ptAtPOVM P W u).op a) ((synPOVM W u).mats (c + a)).val
      = hatMats P W u c := by
  rw [hatMats, hatPtPOVM_eq_kron, POVMIn.map_op, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (c + a) (fun b _ hb => ite_eq_right fun h => hb
      ((add_eq_iff_eq_add a b c).mp h)) fun hmem => absurd (mem_univ (c + a)) hmem,
    ite_eq_left ((add_eq_iff_eq_add a (c + a) c).mpr rfl), kronIn_op]

end Shift

/-! ## The first cut, read on the physical model

The first cut `cut1` of the physical model hands the first player's far half `A''` to the second
player. An operator of the first player of the physical model that is a product on `A''` ---
`compHom (smulKron T Q)`, `T` on `(Ea, A')` and `Q` a matrix of scalars on `A''` --- against an
operator of the second player that does not see the registers is the first cut's `T` against the
register model's `Y ⊗ Q` carried along `ι₁`: the reading lemmas `cut1_πA`, `cut1_πB` of
`MIPRE/Background/QLD/PhysModel.lean`, both readings sharing one state model. This is the model form
of the matrix regrouping `bornProb_regroupVec`. -/

section Reading

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {F : Type*} [Field F] [Fintype F]
  [DecidableEq F] {m d : ℕ}

variable (I F m d) in
/-- **The physical model reads the model's own operators with the registers inert**: `N` embeds in
its physical model, `X ↦ X ⊗ 1` for each player (`BipartiteModel.inertEmb` at the physical state).
The strategy's measurements are read in the physical model along it. -/
abbrev physInert (N : BipartiteModel 𝒞 𝒜 ℬ) (K : ℕ) : N.Embedding (phys I F m d N K) :=
  N.inertEmb (physE I F m d K) norm_physE

variable {N : BipartiteModel 𝒞 𝒜 ℬ} {K : ℕ}

@[simp]
theorem physInert_ΦA (X : 𝒜) :
    (physInert I F m d N K).ΦA X = diagonal fun _ : PhysReg I F m d K => X := rfl

@[simp]
theorem physInert_ΦB (Y : ℬ) :
    (physInert I F m d N K).ΦB Y = diagonal fun _ : PhysReg I F m d K => Y := rfl

/-- The register operators of the second player of the register model, carried to the first cut:
`Y ⊗ Q` acts as `Q` on `A''` and `Y` with the second player's physical registers inert. -/
theorem ι₁_ΦB_smulKron (Y : ℬ) (Q : Matrix I I ℂ) :
    (ι₁ I F m d N K).ΦB (smulKron Y Q)
      = compHom (smulKron ((physInert I F m d N K).ΦB Y) Q) := by
  rw [ι₁_ΦB, physInert_ΦB]
  congr 1
  ext a b p q
  by_cases h : p = q
  · subst h
    simp
  · simp [diagonal_apply_ne _ h]

/-- **A Born probability of the physical model, read on the first cut.** The first player's
operator is a product on the moved half `A''`, the second player's does not see the registers:
the reading lemmas `cut1_πA`, `cut1_πB` and `smulKron X Q = (X ⊗ 1)(1 ⊗ Q)`. -/
theorem phys_bornProb_compHom_smulKron
    (T : Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) 𝒜) (Q : Matrix I I ℂ) (Y : ℬ) :
    (phys I F m d N K).bornProb (compHom (smulKron T Q)) ((physInert I F m d N K).ΦB Y)
      = (cut1 I F m d N K).bornProb T ((ι₁ I F m d N K).ΦB (smulKron Y Q)) := by
  rw [ι₁_ΦB_smulKron]
  show (phys I F m d N K).qform _ = (phys I F m d N K).qform _
  rw [cut1_πA, cut1_πB, ← mul_assoc, ← map_mul, ← map_mul, ← smulKron_eq_diagonal_mul]

end Reading

/-! ## Item 1, as a closeness of two measurements -/

section Item

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

omit [Field F] [Algebra (ZMod 2) F] [NeZero m] in
/-- The marginal `sCoarse` of `ExactPauli.lean` is `polyMarg`. -/
theorem sCoarse_eq_polyMarg {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R]
    [StarOrderedRing R] (S : POVMIn (PolyPair F m d) R) (W : Bas)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    sCoarse S.op (PolyPair.proj W) g = (polyMarg S W).op g :=
  (POVMIn.map_op _ _ _).symm

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]

namespace SimulPair

section Generic

variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

variable (P : SimulPair M S K ι δ)

/-- **The paper's `M~^{W, ind_m(u)}_a`** (`eq:tilde_M`): the simultaneous pair measurement of
`lem:qld-simultaneous` tensored with the ancilla's generalized Pauli at the shifted syndrome, a
matrix over `K`'s first algebra on the register `Anc F m`. -/
def mTildeAt (W : Bas) (u : Point F m) (a : F) : Matrix (Anc F m) (Anc F m) 𝒜' :=
  mTilde P.SA.op (PolyPair.proj W) cubeData (weylOf W) (indVec u) a

/-- It is a projective measurement. -/
theorem isPVM_mTildeAt [StarModule ℂ 𝒜'] (W : Bas) (u : Point F m) :
    IsPVMIn (P.mTildeAt W u) :=
  isPVM_mTilde P.SA_proj (PolyPair.proj W) cubeData (isWeylFamily_weylOf W) (indVec u)

theorem mTildeAt_eq (W : Bas) (u : Point F m) (a : F) :
    P.mTildeAt W u a
      = ∑ g, smulKron ((polyMarg P.SA W).op g)
          ((synPOVM W u).mats (dotF (cubeData g) (indVec u) + a)).val :=
  Finset.sum_congr rfl fun g _ => by rw [sCoarse_eq_polyMarg, synPOVM_mats]

/-! ### The exact half, at the same data

`wTilde` and its three relations are proved in `MIPRE/Background/QLD/ExactPauli.lean` for an
abstract projective pair measurement and Weyl family. Instantiating them at the simultaneous
measurement of a `SimulPair` puts the exact half and the approximate half of
`lem:qld-exact-paulis` on the *same* objects, which is what the lemma asserts. -/

/-- **The paper's `W~^e(u-tilde)`** (`eq:def-tildewj`) at the simultaneous pair measurement. -/
def wTildeAt (W : Bas) (e : F) (v : Anc F m) : Matrix (Anc F m) (Anc F m) 𝒜' :=
  wTilde P.SA.op (PolyPair.proj W) cubeData (weylOf W) e v

/-- It is self-adjoint. -/
theorem wTildeAt_conjTranspose [StarModule ℂ 𝒜'] (W : Bas) (e : F) (v : Anc F m) :
    star (P.wTildeAt W e v) = P.wTildeAt W e v :=
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

end Generic

/-! ### On the physical model

For a pair measurement on the first cut of the physical state, `compHom` of `mTildeAt` is an
operator of the physical model's first player, and the strategy's point measurement is read there
with the registers inert. -/

section Physical

variable {hm : m ∣ Fintype.card F} {N : BipartiteModel 𝒞 𝒜 ℬ}
  {S : N.ProjStrat (qldGame (d := d) hm)} {K : ℕ} {δ : ℝ}

/-- **The physical state is a unit vector**: it is the state of the first cut. The matrix
statement was about the regrouped state `mVec`, whose model is the physical model. -/
theorem mVec_unit (P : CutSimul N S K δ) : ‖(phys (Anc F m) F m d N K).ψ‖ = 1 :=
  P.ψ_unit

/-- **`M~^{W, ind_m(u)}` as a measurement of the physical model's first player**: the elements
`compHom (P.mTildeAt W u a)`, the pair measurement on `(Ea, A')` and the Pauli on `A''`. -/
def mTildePOVM (P : CutSimul N S K δ) (W : Bas) (u : Point F m) :
    POVMIn F (Matrix (PhysReg (Anc F m) F m d K) (PhysReg (Anc F m) F m d K) 𝒜) :=
  ((P.isPVM_mTildeAt W u).pushforward compHom_one).toPOVMIn

@[simp]
theorem mTildePOVM_op (P : CutSimul N S K δ) (W : Bas) (u : Point F m) (a : F) :
    (P.mTildePOVM W u).op a = compHom (P.mTildeAt W u a) := rfl

/-- It is projective. -/
theorem isPVM_mTildePOVM (P : CutSimul N S K δ) (W : Bas) (u : Point F m) :
    IsPVMIn (P.mTildePOVM W u).op :=
  (P.isPVM_mTildeAt W u).pushforward compHom_one

/-- **One term of the agreement, across the cut.** -/
theorem bornProb_mTildeAt (P : CutSimul N S K δ) (W : Bas) (u : Point F m) (a : F) :
    (phys (Anc F m) F m d N K).bornProb (compHom (P.mTildeAt W u a))
        ((physInert (Anc F m) F m d N K).ΦB ((ptAtPOVM S.PB W u).op a))
      = ∑ g, (cut1 (Anc F m) F m d N K).bornProb ((polyMarg P.SA W).op g)
          ((ι₁ (Anc F m) F m d N K).ΦB (smulKron ((ptAtPOVM S.PB W u).op a)
            ((synPOVM W u).mats (dotF (cubeData g) (indVec u) + a)).val)) := by
  rw [P.mTildeAt_eq W u a, map_sum, BipartiteModel.bornProb_sum_left]
  exact Finset.sum_congr rfl fun g _ => phys_bornProb_compHom_smulKron _ _ _

/-- **The agreement of `M~^{W,ind_m(u)}` with the strategy's point measurement is the outcome sum
the helper's chain bounds.** -/
theorem sum_bornProb_mTildeAt (P : CutSimul N S K δ) (W : Bas) (u : Point F m) :
    ∑ a : F, (phys (Anc F m) F m d N K).bornProb (compHom (P.mTildeAt W u a))
        ((physInert (Anc F m) F m d N K).ΦB ((ptAtPOVM S.PB W u).op a))
      = ∑ g, (cut1 (Anc F m) F m d N K).bornProb ((polyMarg P.SA W).op g)
          ((ι₁ (Anc F m) F m d N K).ΦB (hatMats S.PB W u (dotF (cubeData g) (indVec u)))) := by
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => P.bornProb_mTildeAt W u a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← sum_kron_syn_eq_hatMats S.PB W u (dotF (cubeData g) (indVec u)), map_sum,
    BipartiteModel.bornProb_sum_right]

/-- **Item 1 of `lem:qld-exact-paulis`**: the measurement `M~^{W,ind_m(u)}` agrees with the
strategy's `(Point, W)` measurement with probability at least `1 - delta_qld`, on average over a
uniform point, where
`delta_qld = delta_S + 2 (delta_S + sqrt(688 eps) + md/q)`. -/
theorem sum_bornProb_mTilde_ge (P : CutSimul N S K δ) {ε : ℝ} (hfail : 1 - S.value ≤ ε)
    (hd : 1 ≤ d) (W : Bas) :
    1 - (δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F))
      ≤ ∑ u, uniform (Point F m) u * ∑ a : F,
          (phys (Anc F m) F m d N K).bornProb (compHom (P.mTildeAt W u a))
            ((physInert (Anc F m) F m d N K).ΦB ((ptAtPOVM S.PB W u).op a)) := by
  have h := P.sum_bornProb_cubeData_ge hfail hd W
  have hrw : ∀ u : Point F m,
      uniform (Point F m) u * ∑ g, (cut1 (Anc F m) F m d N K).bornProb ((polyMarg P.SA W).op g)
          ((ι₁ (Anc F m) F m d N K).ΦB (hatMats S.PB W u (dotF (cubeData g) (indVec u))))
        = uniform (Point F m) u * ∑ a : F,
          (phys (Anc F m) F m d N K).bornProb (compHom (P.mTildeAt W u a))
            ((physInert (Anc F m) F m d N K).ΦB ((ptAtPOVM S.PB W u).op a)) :=
    fun u => by rw [P.sum_bornProb_mTildeAt W u]
  rwa [Finset.sum_congr rfl fun u (_ : u ∈ univ) => hrw u] at h

/-- **Item 1 of `lem:qld-exact-paulis` as the paper states it**: on average over a uniform point,
the measurement `M~^{W, ind_m(u)}` and the strategy's `(Point, W)` measurement are consistent to
within `delta_S + 2 (delta_S + sqrt(688 eps) + md/q)`, on the physical state. -/
theorem inconsistency_mTilde_le (P : CutSimul N S K δ) {ε : ℝ} (hfail : 1 - S.value ≤ ε)
    (hd : 1 ≤ d) (W : Bas) :
    (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m)) (fun u => P.mTildePOVM W u)
        (fun u => (ptAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one)
      ≤ δ + 2 * ((δ + Real.sqrt (688 * ε)) + (m : ℝ) * d / Fintype.card F) := by
  have hd0 := sum_bornProb_diag_eq (sum_uniform_eq_one (Point F m)) P.mVec_unit
    (fun u => P.mTildePOVM W u)
    (fun u => (ptAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
      (physInert (Anc F m) F m d N K).ΦB_one)
  have hge := P.sum_bornProb_mTilde_ge hfail hd W
  simp only [mTildePOVM_op, POVMIn.pushforward_op] at hd0
  linarith

end Physical

end SimulPair

end Item

end MIPRE.QLD


end

end
