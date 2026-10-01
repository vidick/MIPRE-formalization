/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Chain

@[expose] public section

/-!
# The pulling chain on the physical state

`MIPRE/Background/QLD/Chain.lean` proves the index algebra of `lem:qld-pauli-selfcons`'s chain and
its first displays, `eq:qld-pulling-0` to `eq:qld-pulling-3b`, each of which concerns one
simultaneous pair measurement. From `eq:qld-pulling-4` on the chain compares *both* players' pair
measurements, Alice's on `(A'', (Ea, A'))` and Bob's on `(B'', (Eb, B'))`, on the physical state,
and runs over the four-index family `chainQ`, whose restriction to the coupled index set is the
chain's endpoint `endOp`. This file is that part:

* `eq:qld-pulling-4` and `-5` (`chainS3b_mulVec`): resolving the identity on Bob's own pair brings
  its outcome into the chain, and each matched pair of Weyl projectors cuts Bob's point measurement
  down to the hatted one at the shifted outcome --- exactly;
* `eq:qld-pulling-5` to `-9` (`sum_snorm_sq_chainP_le`), costing item 2 of `lem:qld-helper`;
* `eq:qld-pulling-9a` (`sum_poly_chainQ`), free;
* `eq:qld-pulling-10` down to its Cauchy--Schwarz step (`sum_snorm_sq_chainQ_disagree_le`,
  `sum_qform_bobTail_eq`), finished by `SimulPair.sum_uniform_qform_ne_le` at the second cut;
* `eq:qld-pulling-11` (`sum_snorm_sq_chainQ_agree_le`), costing item 2 of `lem:qld-helper` at the
  second cut;
* `eq:qld-pulling-12` (`sum_uniform_snorm_sq_chainQ_notCoupled_le`), Schwartz--Zippel;
* the endpoint's symmetry between the two players (`endOpMirror_eq`, `snorm_sub_endOpMirror`) and
  the chain's conclusion (`sum_xSqNorm_le_of_endOp`).

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). Everything here lives in the
physical model `phys (Anc F m) F m d M Mi.K` of a `MirrorSimul`: Alice's operators are matrices over
`𝒜` on her physical registers, built from the first cut's pair measurement by `compHom`, and Bob's
are matrices over `ℬ` on his, built from the second cut's. The matrix route read the first cut's
estimates on the physical state through an explicit lift (`physLift`, `physLiftEquiv`) that
regrouped the registers and appended Bob's pair, and read Bob's on the second cut through
`mirrorVec`; here the first cut is a reading of the physical model's state model, so its estimates
need no lift (`bornProb_physVec_aOp`), and the second cut is the first cut of the physical model of
the exchanged players, so Bob's estimates are carried over by the exchange of the blocks of
registers (`blockSwapIso`, through `phys_swap_bornProb`; `bornProb_physVec_bOp`,
`endOpMirror_eq`). The EPR switching on Bob's own pair, which the matrix route did on the regrouped
vector, is the mirror identity of the physical state (`physE_mirror_B`), and many of Bob's objects
are Alice's objects of the second cut on the nose (`bobWeyl`, `bobAnc`, `bobPt`, `bobHat`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]
variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]

/- Same four-fold product index as `mTildeAt`, and the same reason. -/
set_option synthInstance.maxSize 1000

/-! ## A sandwich on the first cut, read physically -/

section Cut

variable {N : BipartiteModel 𝒞 𝒜 ℬ} {K : ℕ}

omit [Algebra (ZMod 2) F] [NeZero m] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ]
  [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
/-- **A sandwich of a projection by an operator, on the first cut**, is the squared state norm of
half of it. -/
theorem cut1_bornProb_sandwich
    (X T : Matrix (PadAnc F m d K × Anc F m) (PadAnc F m d K × Anc F m) 𝒜)
    (hX : star X = X) (hXX : X * X = X) :
    (cut1 (Anc F m) F m d N K).bornProb (star T * X * T) 1
      = (cut1 (Anc F m) F m d N K).snorm ((cut1 (Anc F m) F m d N K).πA (X * T)) ^ 2 := by
  rw [StateModel.snorm_sq_eq_qform, ← map_star, ← map_mul, star_mul, hX, BipartiteModel.bornProb,
    map_one, mul_one, mul_assoc (star T) X (X * T), ← mul_assoc X X T, hXX, ← mul_assoc]

end Cut

/-! ## Two facts about models, used by instantiation -/

section ModelFacts

variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ']

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜]
  [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
/-- **An isomorphism of bipartite models keeps the state norm of a difference** of two operators
that its unitary intertwines with two operators of the other model. -/
theorem snorm_sub_of_iso {M₁ : BipartiteModel 𝒞 𝒜 ℬ} {M₂ : BipartiteModel 𝒞' 𝒜' ℬ'}
    (Φ : BipartiteModel.Iso M₁ M₂) {T₁ T₂ : 𝒞} {T₁' T₂' : 𝒞'}
    (h₁ : ∀ w, Φ.W (M₁.π T₁ w) = M₂.π T₁' (Φ.W w))
    (h₂ : ∀ w, Φ.W (M₁.π T₂ w) = M₂.π T₂' (Φ.W w)) :
    M₁.snorm (T₁ - T₂) = M₂.snorm (T₁' - T₂') := by
  show ‖M₁.π (T₁ - T₂) M₁.ψ‖ = ‖M₂.π (T₁' - T₂') M₂.ψ‖
  rw [← Φ.W_ψ, map_sub M₁.π, map_sub M₂.π, _root_.sub_apply, _root_.sub_apply, ← h₁, ← h₂,
    ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜]
  [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ] in
/-- The representation of a product, applied to a vector, is the composite. Stated for a state
model, so that it is used by instantiation rather than by a rewrite that would compare large
operators by unfolding them. -/
theorem π_mul_apply (N : StateModel 𝒞) (T₁ T₂ : 𝒞) (w : N.H) :
    N.π (T₁ * T₂) w = N.π T₁ (N.π T₂ w) := by
  rw [map_mul N.π, mul_apply_eq_comp]

end ModelFacts

namespace MirrorSimul

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ}

variable (Mi : MirrorSimul M S δ)

/-! ## The chain's endpoint, and its symmetry

Display `eq:qld-pulling-12` is a sum over pairs of index pairs, one per party, coupled by
`g - g_h = g' - g_{h'}` and cut out by the pairing condition on the first. Both parties'
derivations end there, and that is only because the expression does not in fact depend on which
party's pair the condition is read off (`swap_mem_coupledIdx`). -/

/-- **The chain's endpoint**, an element of the physical model's algebra: Alice's pair against
Bob's, over the coupled index set. -/
def endOp (W : Bas) (v : Anc F m) (a : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  ∑ q ∈ coupledIdx (F := F) (m := m) (d := d) v a,
    (phys (Anc F m) F m d M Mi.K).πA (compHom (Mi.first.chainOp W q.1))
      * (phys (Anc F m) F m d M Mi.K).πB (compHom (Mi.second.chainOp W q.2))

/-- **The same endpoint reached from Bob's side**: the endpoint of the mirror, an element of the
algebra of the physical model of the exchanged players, which writes the two parties in the other
order and reads the label off Bob's pair. -/
def endOpMirror (W : Bas) (v : Anc F m) (a : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  Mi.mirror.endOp W v a

/-- Read with the parties' operators exchanged, the endpoint is the sum over the coupled index set
with the label read off Bob's pair. -/
theorem sum_coupledIdx_swap (W : Bas) (v : Anc F m) (a : F) :
    (∑ q ∈ coupledIdx (F := F) (m := m) (d := d) v a,
        (phys (Anc F m) F m d M Mi.K).πB (compHom (Mi.second.chainOp W q.1))
          * (phys (Anc F m) F m d M Mi.K).πA (compHom (Mi.first.chainOp W q.2)))
      = Mi.endOp W v a :=
  Finset.sum_equiv (Equiv.prodComm (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m))
    (fun _ => swap_mem_coupledIdx.symm) fun _ _ =>
      ((phys (Anc F m) F m d M Mi.K).commute _ _).eq.symm

/-- **The endpoint is symmetric between the two parties**, which is the whole reason
`lem:qld-pauli-selfcons` concludes: the exchange of the blocks of registers (`blockSwapIso`)
carries the endpoint reached from Bob's side to the endpoint reached from Alice's, so the two
exact Pauli measurements are close to each other rather than merely each close to something. -/
theorem endOpMirror_eq (W : Bas) (v : Anc F m) (a : F) (w : (phys (Anc F m) F m d M.swap Mi.K).H) :
    (blockSwapIso (Anc F m) F m d M Mi.K).W
        ((phys (Anc F m) F m d M.swap Mi.K).π (Mi.endOpMirror W v a) w)
      = (phys (Anc F m) F m d M Mi.K).π (Mi.endOp W v a)
        ((blockSwapIso (Anc F m) F m d M Mi.K).W w) := by
  have h := (blockSwapIso (Anc F m) F m d M Mi.K).toLocalIsometry.intertwine_sum
    (coupledIdx (F := F) (m := m) (d := d) v a)
    (fun q => compHom (Mi.second.chainOp W q.1)) (fun q => compHom (Mi.first.chainOp W q.2)) w
  rw [← Mi.sum_coupledIdx_swap W v a]
  exact h.symm

/-- **The same, on a state norm**: an operator of Bob's against the endpoint reached from his side,
on the physical model of the exchanged players, has the state norm it has against the endpoint on
the physical model. -/
theorem snorm_sub_endOpMirror (W : Bas) (v : Anc F m) (a : F)
    (X : Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ) :
    (phys (Anc F m) F m d M.swap Mi.K).snorm
        ((phys (Anc F m) F m d M.swap Mi.K).πA X - Mi.endOpMirror W v a)
      = (phys (Anc F m) F m d M Mi.K).snorm
        ((phys (Anc F m) F m d M Mi.K).πB X - Mi.endOp W v a) :=
  snorm_sub_of_iso (blockSwapIso (Anc F m) F m d M Mi.K)
    (T₁' := (phys (Anc F m) F m d M Mi.K).πB X) (T₂' := Mi.endOp W v a)
    (fun w => ((blockSwapIso (Anc F m) F m d M Mi.K).intertwineA X w).symm)
    (Mi.endOpMirror_eq W v a)

/-! ## Each party's chain summand, on its physical registers -/

/-- **Alice's chain summand**, on her physical registers `(A'', (Ea, A'))`: her pair measurement's
`W`-marginal at `g` on `(Ea, A')`, tensored with the Weyl spectral projector at `h` on `A''`. -/
def aliceChainOp (W : Bas) (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  compHom (Mi.first.chainOp W p)

/-- It is a projective family in the pair `(g, h)`. -/
theorem isPVM_aliceChainOp (W : Bas) : IsPVMIn (Mi.aliceChainOp W) :=
  (isPVM_chainOp Mi.first W).pushforward compHom_one

/-- **Bob's**, on `(B'', (Eb, B'))` --- the mirror image, and the second cut's. -/
def bobChainOp (W : Bas) (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  compHom (Mi.second.chainOp W p)

/-- It is a projective family too. -/
theorem isPVM_bobChainOp (W : Bas) : IsPVMIn (Mi.bobChainOp W) :=
  (isPVM_chainOp Mi.second W).pushforward compHom_one

/-- **Bob's Weyl projector**, on the far half `B''` of his own pair --- the outermost of his
physical registers. It is the second cut's `ancB`. -/
def bobWeyl (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  Mi.second.ancB W h

/-- Bob's Weyl projectors are a projective measurement. -/
theorem isPVM_bobWeyl (W : Bas) : IsPVMIn (Mi.bobWeyl W) :=
  (IsPVMIn.smulKron_one (R := Matrix (PadAnc F m d Mi.K × Anc F m)
    (PadAnc F m d Mi.K × Anc F m) ℬ) (isPVM_proj (isWeylFamily_weylOf W)).toIn).pushforward
    compHom_one

/-- **The chain's projective family on the physical cut**: Alice's pair outcome and Weyl outcome
together, against Bob's Weyl outcome. Displays `eq:qld-pulling-5` onward sum over this triple. -/
def chainP (W : Bas) (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W t.1)
    * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W t.2)

/-- It is projective, each party's family being so. -/
theorem isPVM_chainP (W : Bas) : IsPVMIn (Mi.chainP W) :=
  isPVMIn_πA_mul_πB (phys (Anc F m) F m d M Mi.K) (Mi.isPVM_aliceChainOp W) (Mi.isPVM_bobWeyl W)

/-- **Alice's hatted point measurement**, on her physical registers: on `(A, A')`, with `Ea` and
`A''` inert. -/
def aliceHat (W : Bas) (u : Point F m) (c : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) 𝒜 :=
  Mi.first.hatA W u c

/-- **Bob's**, on his: the second cut's. -/
def bobHat (W : Bas) (u : Point F m) (c : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  Mi.second.hatA W u c

/-- **The tail the chain carries at `eq:qld-pulling-5`**: Alice's gap from her own point
measurement, against Bob's point measurement at the shifted outcome `(g - g_h + g_h')(u)`. -/
def chainW (W : Bas) (u : Point F m)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  (phys (Anc F m) F m d M Mi.K).πA (1 - Mi.aliceHat W u (t.1.1.eval u))
    * (phys (Anc F m) F m d M Mi.K).πB
      (Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))

/-- **The sandwich splits across the parties**, each factor being local. -/
theorem chainW_sandwich (W : Bas) (u : Point F m)
    (t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m) :
    star (Mi.chainW W u t) * ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W t.1)
        * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W t.2)) * Mi.chainW W u t
      = (phys (Anc F m) F m d M Mi.K).πA (star (1 - Mi.aliceHat W u (t.1.1.eval u))
            * Mi.aliceChainOp W t.1 * (1 - Mi.aliceHat W u (t.1.1.eval u)))
        * (phys (Anc F m) F m d M Mi.K).πB
          (star (Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))
            * Mi.bobWeyl W t.2
            * Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))) := by
  rw [chainW, BipartiteModel.star_πA_mul_πB, BipartiteModel.πA_mul_πB_mul,
    BipartiteModel.πA_mul_πB_mul]

/-- **Summing the Weyl outcome out of Alice's summand** leaves her pair measurement's marginal
alone, extended by the identity on `A''`. -/
theorem sum_aliceChainOp (W : Bas) (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (∑ h : Anc F m, Mi.aliceChainOp W (g, h))
      = compHom (diagonal fun _ : Anc F m => (polyMarg Mi.first.SA W).op g) := by
  rw [show (∑ h : Anc F m, Mi.aliceChainOp W (g, h))
      = compHom (smulKron ((polyMarg Mi.first.SA W).op g) (∑ h : Anc F m, proj (weylOf W) h)) by
      rw [smulKron_sum_right, map_sum]
      rfl,
    (isPVM_proj (isWeylFamily_weylOf W)).sum_eq_one, smulKron_one_right]

/-- **So the Weyl index collapses out of her sandwich**, the gap operator not depending on it. -/
theorem sum_aliceChainOp_sandwich (W : Bas) (u : Point F m)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (∑ h : Anc F m, star (1 - Mi.aliceHat W u (g.eval u)) * Mi.aliceChainOp W (g, h)
        * (1 - Mi.aliceHat W u (g.eval u)))
      = star (1 - Mi.aliceHat W u (g.eval u))
        * compHom (diagonal fun _ : Anc F m => (polyMarg Mi.first.SA W).op g)
        * (1 - Mi.aliceHat W u (g.eval u)) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, Mi.sum_aliceChainOp W g]

/-- **The far party's factor of the chain's sandwich**: a projector on `(Eb, B')` times a Weyl
outcome on `B''`. -/
theorem bobHat_conj_bobWeyl (W : Bas) (u : Point F m) (c : F) (h : Anc F m) :
    star (Mi.bobHat W u c) * Mi.bobWeyl W h * Mi.bobHat W u c
      = compHom (smulKron ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c))
          (proj (weylOf W) h)) := by
  have hsa : star ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c))
      = (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c) := by
    rw [← map_star, SimulPair.hatMats_conjTranspose]
  have hid : (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c)
        * (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c)
      = (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c) := by
    rw [← map_mul, (isPVM_hatMats S.projB W u).idem]
  rw [bobHat, SimulPair.hatA, BipartiteModel.ProjStrat.swap_PA, bobWeyl, SimulPair.ancB,
    star_compHom_diagonal, hsa, ← map_mul, ← map_mul, diagonal_mul_smulKron, mul_one,
    smulKron_mul_diagonal, hid]

/-- **Alice's sandwich is nonnegative**, being a projection conjugated. -/
theorem posSemidef_aliceSand (W : Bas) (u : Point F m)
    (t : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    0 ≤ star (1 - Mi.aliceHat W u (t.1.eval u)) * Mi.aliceChainOp W t
      * (1 - Mi.aliceHat W u (t.1.eval u)) :=
  star_left_conjugate_nonneg ((Mi.isPVM_aliceChainOp W).nonneg t) _

/-- **Display `eq:qld-pulling-8`: dropping the far party.** Summed over Bob's Weyl outcome, his
factor is a projector times a projective measurement, so at most the identity. -/
theorem sum_bornProb_chainW_drop_le (W : Bas) (u : Point F m)
    (t : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    (∑ h' : Anc F m, (phys (Anc F m) F m d M Mi.K).bornProb
        (star (1 - Mi.aliceHat W u (t.1.eval u)) * Mi.aliceChainOp W t
          * (1 - Mi.aliceHat W u (t.1.eval u)))
        (star (Mi.bobHat W u (t.1.eval u + dotF t.2 (indVec u) + dotF h' (indVec u)))
          * Mi.bobWeyl W h'
          * Mi.bobHat W u (t.1.eval u + dotF t.2 (indVec u) + dotF h' (indVec u))))
      ≤ (phys (Anc F m) F m d M Mi.K).bornProb (star (1 - Mi.aliceHat W u (t.1.eval u))
          * Mi.aliceChainOp W t * (1 - Mi.aliceHat W u (t.1.eval u))) 1 := by
  rw [Finset.sum_congr rfl fun h' (_ : h' ∈ univ) => by
    rw [Mi.bobHat_conj_bobWeyl W u _ h']]
  exact sum_bornProb_compHom_kron_le (phys (Anc F m) F m d M Mi.K) (Mi.posSemidef_aliceSand W u t)
    (B := fun h' => (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA
      (hatMats S.PB W u (t.1.eval u + dotF t.2 (indVec u) + dotF h' (indVec u))))
    (fun h' => by rw [← map_star, SimulPair.hatMats_conjTranspose])
    (fun h' => by rw [← map_mul, (isPVM_hatMats S.projB W u).idem])
    (isPVM_proj (isWeylFamily_weylOf W))

/-- **The bridge from the physical state back to the first cut.** An operator that is Alice's
alone, and the identity on the far half of her pair, sees the state the first cut already
describes: the two share their state model. -/
theorem bornProb_physVec_aOp
    (Z : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) 𝒜) :
    (phys (Anc F m) F m d M Mi.K).bornProb (compHom (diagonal fun _ : Anc F m => Z)) 1
      = (cut1 (Anc F m) F m d M Mi.K).bornProb Z 1 := by
  rw [BipartiteModel.bornProb, BipartiteModel.bornProb, map_one, map_one, mul_one, mul_one,
    cut1_πA]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Displays `eq:qld-pulling-5` to `-8`.** The chain's terms on the physical cut, grouped by the
measurement outcome: projectivity turns each group into a sum of sandwiches, Bob's factor is a
projector times a Weyl outcome and so sums away, and Alice's Weyl outcome sums out of hers,
leaving the pair-measurement marginal against the complement of her own point measurement, on the
first cut. -/
theorem sum_snorm_sq_chainP_le (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          Mi.chainP W t * Mi.chainW W u t) ^ 2
      ≤ ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), (cut1 (Anc F m) F m d M Mi.K).snorm
          ((cut1 (Anc F m) F m d M Mi.K).πA ((polyMarg Mi.first.SA W).op g
            * (1 - (ι₁ (Anc F m) F m d M Mi.K).ΦA (hatMats S.PA W u (g.eval u))))) ^ 2 := by
  classical
  refine sum_snorm_sq_fiber_sandwich_le (phys (Anc F m) F m d M Mi.K).toStateModel
    (Mi.isPVM_chainP W) (Mi.chainW W u) (fun t => dotF (chainLabel t.1.1 t.1.2) v) ?_
  rw [Finset.sum_congr rfl fun t (_ : t ∈ univ) => by
    rw [show Mi.chainP W t = (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W t.1)
        * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W t.2) from rfl,
      Mi.chainW_sandwich W u t, ← BipartiteModel.bornProb], Fintype.sum_prod_type]
  refine le_trans (Finset.sum_le_sum fun t1 (_ : t1 ∈ univ) =>
    Mi.sum_bornProb_chainW_drop_le W u t1) ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun g _ => le_of_eq ?_
  rw [← BipartiteModel.bornProb_sum_left, Mi.sum_aliceChainOp_sandwich W u g, aliceHat,
    SimulPair.hatA, one_sub_compHom_diagonal, star_compHom_diagonal, compHom_diagonal_mul,
    compHom_diagonal_mul, Mi.bornProb_physVec_aOp]
  exact cut1_bornProb_sandwich _ _ ((isPVM_polyMarg Mi.first.SA_proj W).star_eq g)
    ((isPVM_polyMarg Mi.first.SA_proj W).idem g)

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-9`**: the chain's step from `eq:qld-pulling-5` to
`eq:qld-pulling-7` costs item 2 of `lem:qld-helper` and nothing more. -/
theorem sum_uniform_snorm_sq_chainP_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas)
    (v : Anc F m) :
    ∑ u, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          Mi.chainP W t * Mi.chainW W u t) ^ 2
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (Mi.sum_snorm_sq_chainP_le W v u)
      (uniform_nonneg (Point F m) u)) ?_
  exact Mi.first.sum_snorm_sq_polyMarg_one_sub_le hfail W

/-! ## The four-index family, and Bob's half of the chain for free

`eq:qld-pulling-9a` left-multiplies by Bob's own pair measurement, which is the identity, and from
there to `eq:qld-pulling-12` the chain runs over *both* parties' pairs. `chainQ` is that family,
and `endOp` --- the chain's endpoint --- is its restriction to the coupled index set. What the
mirror buys is the rest: Bob's derivation is Alice's, instantiated. -/

/-- **The chain's four-index family on the physical cut**: each party's pair outcome and Weyl
outcome together. -/
def chainQ (W : Bas)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W q.1)
    * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobChainOp W q.2)

/-- It is projective, each party's family being so. -/
theorem isPVM_chainQ (W : Bas) : IsPVMIn (Mi.chainQ W) :=
  isPVMIn_πA_mul_πB (phys (Anc F m) F m d M Mi.K) (Mi.isPVM_aliceChainOp W) (Mi.isPVM_bobChainOp W)

/-- **`endOp` is that family, restricted to the coupled index set** --- so display
`eq:qld-pulling-12` and the displays leading to it speak about one and the same projective
measurement. -/
theorem endOp_eq_sum_chainQ (W : Bas) (v : Anc F m) (a : F) :
    Mi.endOp W v a = ∑ q ∈ coupledIdx (F := F) (m := m) (d := d) v a, Mi.chainQ W q :=
  rfl

/-- **Display `eq:qld-pulling-9a`**: left-multiplying by Bob's own pair measurement, which is the
identity, refines the chain's three-index family into the four-index one. -/
theorem sum_poly_chainQ (W : Bas)
    (t1 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) (h' : Anc F m) :
    (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d), Mi.chainQ W (t1, (g', h')))
      = Mi.chainP W (t1, h') := by
  have hsum : (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d), Mi.bobChainOp W (g', h'))
      = Mi.bobWeyl W h' := by
    rw [show (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d), Mi.bobChainOp W (g', h'))
        = compHom (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d),
          Mi.second.chainOp W (g', h')) by
        rw [map_sum]
        rfl,
      Mi.second.sum_poly_chainOp W h']
    rfl
  show (∑ g' : LowIndDegPoly (F := F) (m := m) (d := d),
      (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W t1)
        * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobChainOp W (g', h')))
    = (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W t1)
      * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h')
  rw [← hsum, map_sum, Finset.mul_sum]

set_option maxHeartbeats 1000000 in
/-- **Bob's `eq:qld-pulling-5` to `-8`, for free.** The same lemma at the mirror: what it asks of
Bob there it asks of Alice here, and the physical model of the mirror has the physical model's
state model, with the two players' algebras exchanged. The paper's ``an entirely analogous
derivation'' for the second party is discharged this way, once for the whole chain. -/
theorem mirror_sum_snorm_sq_chainP_le (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, (phys (Anc F m) F m d M.swap Mi.K).snorm
        (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
            => dotF (chainLabel t.1.1 t.1.2) v = a,
          Mi.mirror.chainP W t * Mi.mirror.chainW W u t) ^ 2
      ≤ ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), (cut1 (Anc F m) F m d M.swap Mi.K).snorm
          ((cut1 (Anc F m) F m d M.swap Mi.K).πA ((polyMarg Mi.second.SA W).op g
            * (1 - (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u (g.eval u))))) ^ 2 :=
  Mi.mirror.sum_snorm_sq_chainP_le W v u

/-! ## `eq:qld-pulling-10`, down to its Cauchy--Schwarz step

The second of the chain's two remaining estimates. It runs over the four-index family and over the
pairs whose outcomes *disagree* at the sampled point, and the reduction below is everything before
the swap: projectivity, one relaxation, and two completeness sums. -/

/-- **Bob's tail at `eq:qld-pulling-9a`**, at an arbitrary outcome: his hatted point measurement,
and nothing on Alice. -/
def bobTail (W : Bas) (u : Point F m) (c : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  (phys (Anc F m) F m d M Mi.K).πB (Mi.bobHat W u c)

/-- **The sandwich splits across the parties**, Alice's factor untouched. -/
theorem bobTail_sandwich (W : Bas) (u : Point F m) (c : F)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    star (Mi.bobTail W u c) * Mi.chainQ W q * Mi.bobTail W u c
      = (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W q.1)
        * (phys (Anc F m) F m d M Mi.K).πB
          (star (Mi.bobHat W u c) * Mi.bobChainOp W q.2 * Mi.bobHat W u c) :=
  πB_sandwich (phys (Anc F m) F m d M Mi.K) _ _ _

/-- Bob's sandwiched pair-measurement marginal, on `(Eb, B')`: an operator of the second cut's
first player. -/
def bobSand (W : Bas) (u : Point F m) (c : F)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ :=
  star ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c))
    * (polyMarg Mi.second.SA W).op g
    * (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c)

/-- **Bob's factor of that sandwich**: his point measurement conjugating his pair measurement's
marginal, tensored with his Weyl outcome. -/
theorem bobHat_conj_bobChainOp (W : Bas) (u : Point F m) (c : F)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    star (Mi.bobHat W u c) * Mi.bobChainOp W p * Mi.bobHat W u c
      = compHom (smulKron (Mi.bobSand W u c p.1) (proj (weylOf W) p.2)) := by
  rw [bobHat, SimulPair.hatA, BipartiteModel.ProjStrat.swap_PA, star_compHom_diagonal, bobChainOp,
    ← map_mul, ← map_mul, SimulPair.chainOp, diagonal_mul_smulKron, smulKron_mul_diagonal]
  rfl

/-- **The sandwich, fully split.** -/
theorem bobTail_sandwich_kron (W : Bas) (u : Point F m) (c : F)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    (phys (Anc F m) F m d M Mi.K).qform (star (Mi.bobTail W u c) * Mi.chainQ W q * Mi.bobTail W u c)
      = (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceChainOp W q.1)
        (compHom (smulKron (Mi.bobSand W u c q.2.1) (proj (weylOf W) q.2.2))) := by
  rw [Mi.bobTail_sandwich W u c q, Mi.bobHat_conj_bobChainOp W u c q.2, ← BipartiteModel.bornProb]

/-- **The tail at the chain's own outcome**, the paper's `(g - g_h + g_h')(u)`. -/
def chainV (W : Bas) (u : Point F m)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  Mi.bobTail W u (chainQShift u q)

set_option maxHeartbeats 1000000 in
/-- **The first two steps of `eq:qld-pulling-10`'s justification.** Projectivity turns the grouped
squared norm into a sum of sandwiches over the disagreeing pairs; each of those is one term of a
sum over *all* outcomes the pair's own value excludes, and the rest of that sum is nonnegative; and
then the constraint tying the outcome to the index may be dropped. -/
theorem sum_snorm_sq_chainQ_disagree_le (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (∑ q ∈ (univ.filter fun q => chainQShift u q ≠ q.2.1.eval u).filter
              fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
          Mi.chainQ W q * Mi.chainV W u q) ^ 2
      ≤ ∑ q, ∑ c ∈ univ.filter fun c : F => c ≠ q.2.1.eval u,
          (phys (Anc F m) F m d M Mi.K).qform
            (star (Mi.bobTail W u c) * Mi.chainQ W q * Mi.bobTail W u c) := by
  classical
  have hnn : ∀ (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) (c : F),
      0 ≤ (phys (Anc F m) F m d M Mi.K).qform
        (star (Mi.bobTail W u c) * Mi.chainQ W q * Mi.bobTail W u c) :=
    fun q c => qform_sandwich_nonneg _ (π_nonneg_of_isStarProjection _
      ((Mi.isPVM_chainQ W).isStarProjection q)) _
  refine sum_snorm_sq_fiber_sandwich_subset_le (phys (Anc F m) F m d M Mi.K).toStateModel
    (Mi.isPVM_chainQ W) (fun q => Mi.chainV W u q) (fun q => dotF (chainLabel q.1.1 q.1.2) v)
    (univ.filter fun q => chainQShift u q ≠ q.2.1.eval u) ?_
  refine le_trans (Finset.sum_le_sum fun q hq => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun q _ _ => Finset.sum_nonneg fun c _ => hnn q c)
  exact Finset.single_le_sum (f := fun c : F => (phys (Anc F m) F m d M Mi.K).qform
      (star (Mi.bobTail W u c) * Mi.chainQ W q * Mi.bobTail W u c))
    (fun c _ => hnn q c)
    (Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hq).2⟩)

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-13a`**: Alice's family and Bob's Weyl outcome both sum to the
identity, so what is left of the bound carries neither. -/
theorem sum_qform_bobTail_eq (W : Bas) (u : Point F m) :
    (∑ q, ∑ c ∈ univ.filter fun c : F => c ≠ q.2.1.eval u,
        (phys (Anc F m) F m d M Mi.K).qform
          (star (Mi.bobTail W u c) * Mi.chainQ W q * Mi.bobTail W u c))
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          ∑ c ∈ univ.filter fun c : F => c ≠ g.eval u,
            (phys (Anc F m) F m d M Mi.K).bornProb 1
              (compHom (diagonal fun _ : Anc F m => Mi.bobSand W u c g)) := by
  classical
  have hq1 : ∀ (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h : Anc F m) (c : F),
      (∑ q1 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
          (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceChainOp W q1)
            (compHom (smulKron (Mi.bobSand W u c g) (proj (weylOf W) h))))
        = (phys (Anc F m) F m d M Mi.K).bornProb 1
            (compHom (smulKron (Mi.bobSand W u c g) (proj (weylOf W) h))) := by
    intro g h c
    rw [← BipartiteModel.bornProb_sum_left, (Mi.isPVM_aliceChainOp W).sum_eq_one]
  have hh : ∀ (g : LowIndDegPoly (F := F) (m := m) (d := d)) (c : F),
      (∑ h : Anc F m, (phys (Anc F m) F m d M Mi.K).bornProb 1
          (compHom (smulKron (Mi.bobSand W u c g) (proj (weylOf W) h))))
        = (phys (Anc F m) F m d M Mi.K).bornProb 1
            (compHom (diagonal fun _ : Anc F m => Mi.bobSand W u c g)) := by
    intro g c
    rw [← BipartiteModel.bornProb_sum_right, ← map_sum, ← smulKron_sum_right,
      (isPVM_proj (isWeylFamily_weylOf W)).sum_eq_one, smulKron_one_right]
  have key : ∀ q2 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
      (∑ q1 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
          ∑ c ∈ univ.filter fun c : F => c ≠ q2.1.eval u,
            (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceChainOp W q1)
              (compHom (smulKron (Mi.bobSand W u c q2.1) (proj (weylOf W) q2.2))))
        = ∑ c ∈ univ.filter fun c : F => c ≠ q2.1.eval u,
            (phys (Anc F m) F m d M Mi.K).bornProb 1
              (compHom (smulKron (Mi.bobSand W u c q2.1) (proj (weylOf W) q2.2))) := by
    intro q2
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => hq1 q2.1 q2.2 c
  rw [Finset.sum_congr rfl fun q (_ : q ∈ univ) => Finset.sum_congr rfl fun c _ =>
      Mi.bobTail_sandwich_kron W u c q,
    Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_congr rfl fun q2 (_ : q2 ∈ univ) => key q2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ => ?_
  -- Restated so that the filter's decidability instance no longer mentions the pair.
  show (∑ h : Anc F m, ∑ c ∈ univ.filter fun c : F => c ≠ g.eval u,
      (phys (Anc F m) F m d M Mi.K).bornProb 1
        (compHom (smulKron (Mi.bobSand W u c g) (proj (weylOf W) h)))) = _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => hh g c

/-! ## `eq:qld-pulling-11`, and the second cut's bridge

The last of the chain's estimates before Schwartz--Zippel. Everything here is Bob's, and
everything Bob's is Alice's at the mirror. -/

/-- **The bridge from the physical state to the second cut.** The mirror image of
`bornProb_physVec_aOp`: an operator that is Bob's alone, and the identity on the far half of his
pair, sees the state the second cut already describes, by the exchange of the blocks of
registers. -/
theorem bornProb_physVec_bOp
    (Z : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ) :
    (phys (Anc F m) F m d M Mi.K).bornProb 1 (compHom (diagonal fun _ : Anc F m => Z))
      = (cut1 (Anc F m) F m d M.swap Mi.K).bornProb Z 1 := by
  rw [← phys_swap_bornProb]
  exact Mi.mirror.bornProb_physVec_aOp Z

/-- **Bob's lift**: an operator of his on `(Eb, B')`, extended by the identity on `B''` and read on
the physical model. Both remaining displays sandwich the four-index family with one of these; only
which one differs. -/
def bobLift (T : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ) :
    Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞 :=
  (phys (Anc F m) F m d M Mi.K).πB (compHom (diagonal fun _ : Anc F m => T))

/-- **The sandwich splits across the parties**, Alice's factor untouched. -/
theorem bobLift_sandwich (W : Bas)
    (T : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    star (Mi.bobLift T) * Mi.chainQ W q * Mi.bobLift T
      = (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W q.1)
        * (phys (Anc F m) F m d M Mi.K).πB (star (compHom (diagonal fun _ : Anc F m => T))
            * Mi.bobChainOp W q.2 * compHom (diagonal fun _ : Anc F m => T)) :=
  πB_sandwich (phys (Anc F m) F m d M Mi.K) _ _ _

/-- **Bob's factor of it**: his operator conjugating his pair measurement's marginal, tensored
with his Weyl outcome. -/
theorem aOp_conj_bobChainOp (W : Bas)
    (T : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ)
    (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) :
    star (compHom (diagonal fun _ : Anc F m => T)) * Mi.bobChainOp W p
        * compHom (diagonal fun _ : Anc F m => T)
      = compHom (smulKron (star T * (polyMarg Mi.second.SA W).op p.1 * T) (proj (weylOf W) p.2)) := by
  rw [star_compHom_diagonal, bobChainOp, ← map_mul, ← map_mul, SimulPair.chainOp,
    diagonal_mul_smulKron, smulKron_mul_diagonal]

/-- **The sandwich, fully split.** -/
theorem bobLift_sandwich_kron (W : Bas)
    (T : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ)
    (q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)) :
    (phys (Anc F m) F m d M Mi.K).qform (star (Mi.bobLift T) * Mi.chainQ W q * Mi.bobLift T)
      = (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceChainOp W q.1)
        (compHom (smulKron (star T * (polyMarg Mi.second.SA W).op q.2.1 * T)
          (proj (weylOf W) q.2.2))) := by
  rw [Mi.bobLift_sandwich W T q, Mi.aOp_conj_bobChainOp W T q.2, ← BipartiteModel.bornProb]

set_option maxHeartbeats 1000000 in
/-- **Alice's family and Bob's Weyl outcome sum away**, leaving a statement about the second cut
alone. This is the shape both `eq:qld-pulling-10` and `eq:qld-pulling-11` end at. -/
theorem sum_qform_bobLift_eq (W : Bas)
    (T : LowIndDegPoly (F := F) (m := m) (d := d)
      → Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ) :
    (∑ q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
        × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m),
      (phys (Anc F m) F m d M Mi.K).qform
        (star (Mi.bobLift (T q.2.1)) * Mi.chainQ W q * Mi.bobLift (T q.2.1)))
      = ∑ g : LowIndDegPoly (F := F) (m := m) (d := d),
          (cut1 (Anc F m) F m d M.swap Mi.K).bornProb
            (star (T g) * (polyMarg Mi.second.SA W).op g * T g) 1 := by
  classical
  have hq1 : ∀ (g : LowIndDegPoly (F := F) (m := m) (d := d)) (h : Anc F m),
      (∑ q1 : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
          (phys (Anc F m) F m d M Mi.K).bornProb (Mi.aliceChainOp W q1)
            (compHom (smulKron (star (T g) * (polyMarg Mi.second.SA W).op g * T g)
              (proj (weylOf W) h))))
        = (phys (Anc F m) F m d M Mi.K).bornProb 1
            (compHom (smulKron (star (T g) * (polyMarg Mi.second.SA W).op g * T g)
              (proj (weylOf W) h))) := by
    intro g h
    rw [← BipartiteModel.bornProb_sum_left, (Mi.isPVM_aliceChainOp W).sum_eq_one]
  have hh : ∀ g : LowIndDegPoly (F := F) (m := m) (d := d),
      (∑ h : Anc F m, (phys (Anc F m) F m d M Mi.K).bornProb 1
          (compHom (smulKron (star (T g) * (polyMarg Mi.second.SA W).op g * T g)
            (proj (weylOf W) h))))
        = (cut1 (Anc F m) F m d M.swap Mi.K).bornProb
            (star (T g) * (polyMarg Mi.second.SA W).op g * T g) 1 := by
    intro g
    rw [← BipartiteModel.bornProb_sum_right, ← map_sum, ← smulKron_sum_right,
      (isPVM_proj (isWeylFamily_weylOf W)).sum_eq_one, smulKron_one_right]
    exact Mi.bornProb_physVec_bOp _
  rw [Finset.sum_congr rfl fun q (_ : q ∈ univ) => Mi.bobLift_sandwich_kron W (T q.2.1) q,
    Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_congr rfl fun q2 (_ : q2 ∈ univ) => hq1 q2.1 q2.2, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun g _ => hh g

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-11`**: dropping Bob's point measurement from his side of the
chain's endpoint costs item 2 of `lem:qld-helper`, read on the second cut. The index set carries
the agreement constraint, which the bound simply drops --- every sandwich is nonnegative. -/
theorem sum_snorm_sq_chainQ_agree_le (W : Bas) (v : Anc F m) (u : Point F m) :
    ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
              × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
              chainQShift u q = q.2.1.eval u).filter
            fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
          Mi.chainQ W q
            * Mi.bobLift (1 - (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA
              (hatMats S.PB W u (q.2.1.eval u)))) ^ 2
      ≤ ∑ g : LowIndDegPoly (F := F) (m := m) (d := d), (cut1 (Anc F m) F m d M.swap Mi.K).snorm
          ((cut1 (Anc F m) F m d M.swap Mi.K).πA ((polyMarg Mi.second.SA W).op g
            * (1 - (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u (g.eval u))))) ^ 2 := by
  classical
  refine sum_snorm_sq_fiber_sandwich_subset_le (phys (Anc F m) F m d M Mi.K).toStateModel
    (Mi.isPVM_chainQ W)
    (fun q => Mi.bobLift (1 - (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA
      (hatMats S.PB W u (q.2.1.eval u))))
    (fun q => dotF (chainLabel q.1.1 q.1.2) v) _ ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun q _ _ => qform_sandwich_nonneg _ (π_nonneg_of_isStarProjection _
      ((Mi.isPVM_chainQ W).isStarProjection q)) _) (le_of_eq ?_)
  rw [Mi.sum_qform_bobLift_eq W fun g => 1 - (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA
    (hatMats S.PB W u (g.eval u))]
  exact Finset.sum_congr rfl fun g _ => cut1_bornProb_sandwich _ _
    ((isPVM_polyMarg Mi.second.SA_proj W).star_eq g) ((isPVM_polyMarg Mi.second.SA_proj W).idem g)

set_option maxHeartbeats 1000000 in
/-- **And its cost**, which is item 2 of `lem:qld-helper` at the second cut --- available, with no
new proof, because the second cut is a simultaneous pair measurement in its own right. -/
theorem sum_uniform_snorm_sq_chainQ_agree_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas)
    (v : Anc F m) :
    (∑ u, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
              × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
              chainQShift u q = q.2.1.eval u).filter
            fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
          Mi.chainQ W q
            * Mi.bobLift (1 - (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA
              (hatMats S.PB W u (q.2.1.eval u)))) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (Mi.sum_snorm_sq_chainQ_agree_le W v u)
      (uniform_nonneg (Point F m) u)) ?_
  exact Mi.second.sum_snorm_sq_polyMarg_one_sub_le (povmValue_swapped_le hfail) W

/-! ## `eq:qld-pulling-12`, Schwartz--Zippel, on the physical state -/

/-- **The chain's four-index family has total weight one on the physical state.** -/
theorem sum_qform_chainQ (W : Bas) :
    (∑ q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
        × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m),
      (phys (Anc F m) F m d M Mi.K).qform (Mi.chainQ W q)) = 1 := by
  rw [← StateModel.qform_sum, (Mi.isPVM_chainQ W).sum_eq_one,
    StateModel.qform_one _ Mi.physVec_unit]

set_option maxHeartbeats 1000000 in
/-- **Display `eq:qld-pulling-12`**: the chain's constraint is an equality of polynomial *values*
at the sampled point; passing to equality of the polynomials themselves discards only the tuples
where distinct polynomials happen to agree there, and Schwartz--Zippel bounds that by `md/q`. -/
theorem sum_uniform_snorm_sq_chainQ_notCoupled_le (hd : 1 ≤ d) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
              × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
              MIPRE.QLD.chainQShift u q = q.2.1.eval u
                ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2).filter
            fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
          Mi.chainQ W q) ^ 2)
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  have hP := Mi.isPVM_chainQ W
  have hnn : ∀ q, 0 ≤ (phys (Anc F m) F m d M Mi.K).qform (Mi.chainQ W q) := fun q =>
    StateModel.qform_nonneg _ (π_nonneg_of_isStarProjection _ (hP.isStarProjection q))
  have hu : ∀ u : Point F m,
      (∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
          (∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
                × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
                MIPRE.QLD.chainQShift u q = q.2.1.eval u
                  ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2).filter
              fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
            Mi.chainQ W q) ^ 2)
        ≤ ∑ q ∈ univ.filter fun q => MIPRE.QLD.chainQShift u q = q.2.1.eval u
            ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2,
          (phys (Anc F m) F m d M Mi.K).qform (Mi.chainQ W q) := by
    intro u
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      congrArg (· ^ 2) (congrArg (phys (Anc F m) F m d M Mi.K).snorm
        (Finset.sum_congr rfl fun q _ => (mul_one (Mi.chainQ W q)).symm)))) ?_
    refine sum_snorm_sq_fiber_sandwich_subset_le (phys (Anc F m) F m d M Mi.K).toStateModel hP
      (fun _ => 1) (fun q => dotF (chainLabel q.1.1 q.1.2) v) _ (le_of_eq ?_)
    exact Finset.sum_congr rfl fun q _ => by rw [star_one, one_mul, mul_one]
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hu u) (uniform_nonneg (Point F m) u)) ?_
  exact sum_uniform_chainCoupled_mass_le hd
    (fun q => (phys (Anc F m) F m d M Mi.K).qform (Mi.chainQ W q)) hnn
    (le_of_eq (Mi.sum_qform_chainQ W))

/-! ## `eq:qld-pulling-4` and `-5` on the physical state

The step that brings Bob's pair's outcome into the chain. Both halves of Bob's own pair are his in
the physical grouping, so the matched Weyl projectors are one operator of his, and the pair being
maximally entangled they act on the state as the projector on the far half alone
(`physE_mirror_B`). -/

/-- **The half of Bob's pair beside his own space**, `B'`: the second cut's `ancA`. -/
def bobAnc (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  Mi.second.ancA W h

/-- **Bob's matched Weyl projectors**, on the two halves of his own pair. -/
def bobPairProj (W : Bas) (h : Anc F m) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  Mi.bobAnc W h * Mi.bobWeyl W h

/-- The matched pair of projectors is the one on `B'` and Bob's Weyl outcome. -/
theorem bobPairProj_eq_mul (W : Bas) (h : Anc F m) :
    Mi.bobPairProj W h = Mi.bobAnc W h * Mi.bobWeyl W h := rfl

/-- It is a single scalar matrix on Bob's registers, the projector on both halves of his pair. -/
theorem bobPairProj_eq (W : Bas) (h : Anc F m) :
    Mi.bobPairProj W h = smulKron (1 : ℬ) (proj (weylOf W) h
      ⊗ₖ ((1 : Matrix (PadAnc F m d Mi.K) (PadAnc F m d Mi.K) ℂ) ⊗ₖ proj (weylOf W) h)) := by
  rw [bobPairProj, bobAnc, bobWeyl, SimulPair.ancA, SimulPair.ancB, compHom_smulKron_one,
    smulKron_mul, one_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- Bob's two halves commute, living on different registers. -/
theorem bobAnc_mul_bobWeyl (W : Bas) (h : Anc F m) :
    Mi.bobAnc W h * Mi.bobWeyl W h = Mi.bobWeyl W h * Mi.bobAnc W h := by
  rw [bobAnc, bobWeyl, SimulPair.ancA, SimulPair.ancB, compHom_smulKron_one, smulKron_mul,
    smulKron_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

/-- Bob's Weyl projector, as a scalar matrix on his registers: the projector on `B''`, the
identity on `(Eb, B')`. -/
theorem bobWeyl_eq (W : Bas) (h : Anc F m) :
    Mi.bobWeyl W h = smulKron (1 : ℬ) (proj (weylOf W) h
      ⊗ₖ (1 : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℂ)) := by
  rw [bobWeyl, SimulPair.ancB, compHom_smulKron_one]

/-- **One matched pair of Weyl projectors acts as Bob's Weyl outcome alone.** The pair the
physical grouping gives him entirely is maximally entangled, so the projector on its near half is
redundant beside the one on its far half. -/
theorem bobPairProj_mulVec (W : Bas) (h : Anc F m) :
    (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πB (Mi.bobPairProj W h))
        (phys (Anc F m) F m d M Mi.K).ψ
      = (phys (Anc F m) F m d M Mi.K).π ((phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h))
        (phys (Anc F m) F m d M Mi.K).ψ := by
  -- The near half against the far half, by the mirror identity of Bob's pair.
  have hB := physE_mirror_B (N := M) (F := F) (m := m) (d := d) (K := Mi.K) (proj (weylOf W) h)
  rw [proj_weylOf_transpose, ← Mi.bobWeyl_eq W h] at hB
  have hmul : (phys (Anc F m) F m d M Mi.K).πB (Mi.bobPairProj W h)
      = (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h)
        * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobAnc W h) := by
    rw [bobPairProj, Mi.bobAnc_mul_bobWeyl W h]
    exact map_mul (phys (Anc F m) F m d M Mi.K).πB _ _
  have hidem : (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h)
        * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h)
      = (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h) := by
    rw [← map_mul (phys (Anc F m) F m d M Mi.K).πB, (Mi.isPVM_bobWeyl W).idem h]
  -- Chained by `Eq.trans`: a rewrite here would compare Bob's different matrices by unfolding.
  have s2 := congrArg (fun w => (phys (Anc F m) F m d M Mi.K).π
    ((phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h)) w) hB
  have s4 := congrArg (fun T => (phys (Anc F m) F m d M Mi.K).π T (phys (Anc F m) F m d M Mi.K).ψ)
    hidem
  exact (congrArg (fun T => (phys (Anc F m) F m d M Mi.K).π T (phys (Anc F m) F m d M Mi.K).ψ)
    hmul).trans ((π_mul_apply (phys (Anc F m) F m d M Mi.K).toStateModel _ _ _).trans
      (s2.trans ((π_mul_apply (phys (Anc F m) F m d M Mi.K).toStateModel _ _ _).symm.trans s4)))

/-- **Display `eq:qld-pulling-4`: Bob's matched Weyl projectors leave the physical state alone.**
Each acts as the projector on the far half alone, and those sum to the identity. -/
theorem sum_bobPairProj_mulVec (W : Bas) :
    (phys (Anc F m) F m d M Mi.K).π
        (∑ h : Anc F m, (phys (Anc F m) F m d M Mi.K).πB (Mi.bobPairProj W h))
        (phys (Anc F m) F m d M Mi.K).ψ
      = (phys (Anc F m) F m d M Mi.K).ψ := by
  have hone : (∑ h : Anc F m, Mi.bobWeyl W h) = 1 := (Mi.isPVM_bobWeyl W).sum_eq_one
  rw [map_sum, _root_.sum_apply,
    Finset.sum_congr rfl fun h (_ : h ∈ univ) => Mi.bobPairProj_mulVec W h, ← _root_.sum_apply,
    ← map_sum, ← map_sum, hone, map_one, map_one, one_apply_eq_self]

/-- **Bob's point measurement, on his physical registers**: the second cut's `ptA`, which is the
first cut's `ptB`. -/
def bobPt (W : Bas) (u : Point F m) (k : F) :
    Matrix (PhysReg (Anc F m) F m d Mi.K) (PhysReg (Anc F m) F m d Mi.K) ℬ :=
  Mi.second.ptA W u k

/-- **Display `eq:qld-pulling-5`'s algebra on Bob's register.** The projector on the pair's near
half cuts the point measurement down to the hatted point measurement: the second cut's
`ptA_mul_ancA`. -/
theorem bobPt_mul_bobAnc (W : Bas) (u : Point F m) (c : F) (h : Anc F m) :
    Mi.bobPt W u (c + dotF h (indVec u)) * Mi.bobAnc W h = Mi.bobHat W u c * Mi.bobAnc W h :=
  Mi.second.ptA_mul_ancA W u c h

/-- The same against the matched pair, which is the form `eq:qld-pulling-5` uses. -/
theorem bobPt_mul_bobPairProj (W : Bas) (u : Point F m) (k : F) (h : Anc F m) :
    Mi.bobPt W u k * Mi.bobPairProj W h
      = Mi.bobHat W u (k + dotF h (indVec u)) * Mi.bobPairProj W h := by
  have hk : (k + dotF h (indVec u)) + dotF h (indVec u) = k := by
    rw [add_assoc, add_self, add_zero]
  rw [bobPairProj_eq_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  conv_lhs => rw [← hk]
  exact Mi.bobPt_mul_bobAnc W u (k + dotF h (indVec u)) h

/-- Bob's Weyl outcome and his hatted point measurement commute, living on different registers. -/
theorem bobHat_mul_bobWeyl (W : Bas) (u : Point F m) (c : F) (h : Anc F m) :
    Mi.bobHat W u c * Mi.bobWeyl W h = Mi.bobWeyl W h * Mi.bobHat W u c := by
  rw [bobHat, SimulPair.hatA, bobWeyl, SimulPair.ancB, ← map_mul, ← map_mul,
    smulKron_one_mul_diagonal, ← smulKron_eq_diagonal_mul]

set_option maxHeartbeats 4000000 in
/-- **Displays `eq:qld-pulling-4` and `-5`.** Resolving the identity on Bob's pair brings its
outcome into the chain, and each matched pair cuts Bob's point measurement down to the hatted point
measurement at the shifted outcome. The step costs nothing: with the first cut's
`chainS_three_mulVec` it carries the chain's fourth term to its fifth on the physical state. -/
theorem chainS3b_mulVec (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    (phys (Anc F m) F m d M Mi.K).π (Mi.first.chainS3b W v u a) (phys (Anc F m) F m d M Mi.K).ψ
      = (phys (Anc F m) F m d M Mi.K).π
          (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
              × Anc F m => dotF (chainLabel t.1.1 t.1.2) v = a,
            Mi.chainP W t * ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceHat W u (t.1.1.eval u))
              * (phys (Anc F m) F m d M Mi.K).πB
                (Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))))
          (phys (Anc F m) F m d M Mi.K).ψ := by
  classical
  have hins : ∀ Z : Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞,
      (phys (Anc F m) F m d M Mi.K).π Z (phys (Anc F m) F m d M Mi.K).ψ
        = ∑ h : Anc F m, (phys (Anc F m) F m d M Mi.K).π
          (Z * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobPairProj W h))
          (phys (Anc F m) F m d M Mi.K).ψ := by
    intro Z
    conv_lhs => rw [← Mi.sum_bobPairProj_mulVec W]
    rw [← mul_apply_eq_comp, ← map_mul, Finset.mul_sum, map_sum, _root_.sum_apply]
  have hterm : ∀ (p : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) (h : Anc F m),
      (phys (Anc F m) F m d M Mi.K).π
          ((phys (Anc F m) F m d M Mi.K).πA (compHom (Mi.first.chainOp W p)
              * Mi.first.hatA W u (p.1.eval u))
            * (phys (Anc F m) F m d M Mi.K).πB (Mi.first.ptB W u (SimulPair.chainShift u p))
            * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobPairProj W h))
          (phys (Anc F m) F m d M Mi.K).ψ
        = (phys (Anc F m) F m d M Mi.K).π (Mi.chainP W (p, h)
            * ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceHat W u (p.1.eval u))
              * (phys (Anc F m) F m d M Mi.K).πB
                (Mi.bobHat W u (p.1.eval u + dotF p.2 (indVec u) + dotF h (indVec u)))))
          (phys (Anc F m) F m d M Mi.K).ψ := by
    intro p h
    have hc : SimulPair.chainShift u p + dotF h (indVec u)
        = p.1.eval u + dotF p.2 (indVec u) + dotF h (indVec u) := rfl
    have hpt : Mi.first.ptB W u (SimulPair.chainShift u p)
        = Mi.bobPt W u (SimulPair.chainShift u p) := rfl
    have e : (phys (Anc F m) F m d M Mi.K).πA (compHom (Mi.first.chainOp W p)
            * Mi.first.hatA W u (p.1.eval u))
          * (phys (Anc F m) F m d M Mi.K).πB
            (Mi.bobHat W u (p.1.eval u + dotF p.2 (indVec u) + dotF h (indVec u)))
          * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h)
        = Mi.chainP W (p, h) * ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceHat W u (p.1.eval u))
            * (phys (Anc F m) F m d M Mi.K).πB
              (Mi.bobHat W u (p.1.eval u + dotF p.2 (indVec u) + dotF h (indVec u)))) := by
      rw [show Mi.chainP W (p, h) = (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceChainOp W p)
          * (phys (Anc F m) F m d M Mi.K).πB (Mi.bobWeyl W h) from rfl,
        BipartiteModel.πA_mul_πB_mul, ← Mi.bobHat_mul_bobWeyl W u _ h,
        map_mul (phys (Anc F m) F m d M Mi.K).πB, ← mul_assoc]
      rfl
    rw [mul_assoc, ← map_mul (phys (Anc F m) F m d M Mi.K).πB, hpt,
      Mi.bobPt_mul_bobPairProj W u (SimulPair.chainShift u p) h, hc,
      map_mul (phys (Anc F m) F m d M Mi.K).πB, ← mul_assoc,
      map_mul (phys (Anc F m) F m d M Mi.K).π, mul_apply_eq_comp, Mi.bobPairProj_mulVec W h,
      ← mul_apply_eq_comp, ← map_mul (phys (Anc F m) F m d M Mi.K).π, e]
  rw [SimulPair.chainS3b, map_sum, _root_.sum_apply,
    Finset.sum_congr rfl fun p (_ : p ∈ chainIdx (F := F) (m := m) (d := d) v a) => hins _,
    sum_chainLabel_filter v a, map_sum, _root_.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, _root_.sum_apply]
  exact Finset.sum_congr rfl fun h _ => hterm p h

end MirrorSimul

/-! ## Closing the chain

Both parties' derivations end at the endpoint, and what remains is arithmetic: the triangle
inequality for a family of deviations (`StateModel.sum_snorm_sq_triangle`). The two hypotheses
below are exactly the two chains --- Alice's `eq:qld-pulling-0` through `eq:qld-pulling-12`, and
Bob's symmetric equivalent --- and nothing else stands between them and `lem:qld-pauli-selfcons`. -/

section Close

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ}

/-- **The chain's conclusion.** Given that each party's exact Pauli measurement is close to the
endpoint, the two are close to each other, which is `eq:qld-pulling-cons`. The factor two is the
triangle inequality's, and the paper absorbs it into `delta_S`. -/
theorem sum_xSqNorm_le_of_endOp (Mi : MirrorSimul M S δ) (W : Bas) (v : Anc F m) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceMTilde W v a) - Mi.endOp W v a) ^ 2 ≤ δ₁)
    (h2 : ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.endOp W v a - (phys (Anc F m) F m d M Mi.K).πB (Mi.bobMTilde W v a)) ^ 2 ≤ δ₂) :
    ∑ a : F, (phys (Anc F m) F m d M Mi.K).xSqNorm (Mi.aliceMTilde W v a) (Mi.bobMTilde W v a)
      ≤ 2 * δ₁ + 2 * δ₂ := by
  have h := (phys (Anc F m) F m d M Mi.K).sum_snorm_sq_triangle univ
    (fun a : F => (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceMTilde W v a))
    (fun a : F => Mi.endOp W v a)
    (fun a : F => (phys (Anc F m) F m d M Mi.K).πB (Mi.bobMTilde W v a))
  simp only [BipartiteModel.xSqNorm_eq_sq, BipartiteModel.xNorm]
  linarith

end Close

end MIPRE.QLD

end

end
