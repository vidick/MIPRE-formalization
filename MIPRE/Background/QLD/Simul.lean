/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Combined
public import MIPRE.Background.QLD.PhysModel

@[expose] public section

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

The padded strategy does not live on the paper's registers `A A' | B A''`: the seeded soundness
theorem is applied to a projective dilation of the padded strategy, which adjoins a padding
register to each party, and stage 5 reads the result on the first cut of a physical state that
holds more registers still. So the measurement stage 4 produces lives in a model `K` that stage 5
has no reason to know. What every transfer from stages 2 and 3 needs is that an operator of the
expanded model `M.reg (Anc F m)`, carried to `K`, has there the expectation it had: the structure
is parameterized by `K` and an embedding `ι : (M.reg (Anc F m)).Embedding K` --- a local isometry
carrying the state to the state and keeping both units (`BipartiteModel.Embedding`) --- along
which every such quantity transfers exactly (`SimulPair.bornProb_aOp_aOp`,
`SimulPair.stateSqNorm_aOp`, `SimulPair.normSq_stateVecB_aOp`, `SimulPair.xSqNorm_aOp`). A
`SimulPair` moves along any further embedding of `K` (`SimulPair.transport`); stage 5 uses it on
the first cut of the physical state, `CutSimul`.

## The consistency

`consA` says that Alice's pair measurement, read through the `W`-component evaluated at a
uniformly random point `u`, agrees with Bob's expanded `(Point, W)` measurement at `u`, carried to
`K` along `ι`, up to `δ` --- the paper's `eq:qld-s-point-con-alice`; `consB` is
`eq:qld-s-point-con-bob`. Both are required, and no symmetry of the strategy is assumed.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The strategy is a projective
strategy `S : M.ProjStrat (qldGame hm)` of a bipartite model `M`, and the expanded state is the
register model `M.reg (Anc F m)` (`MIPRE/Background/QLD/Expanded.lean`). The matrix structure
carried the padded registers `EA`, `EB` and the padded state `Φ` as fields, with the one property
`Φ_reduced` (an operator on the two hat registers, extended by the identity, has the expectation
it has on `hatVec ψ`); here the model `K` and the embedding `ι` are parameters, `Φ_reduced` is
`ι.W_ψ`, and the pair measurements are POVMs in `K`'s algebras. The matrix reduction of a product
with fixed ancilla vectors (`bornProb_extVec2_aOp_aOp`) is the embedding
`BipartiteModel.inertEmb`.
-/

noncomputable section

namespace MIPRE

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder

section Norms

variable {R S : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

/-- Alice's squared state norm as a Born probability against the identity: the tensor-product
instance of `BipartiteModel.stateSqNorm_eq_bornProb_one`. -/
theorem stateSqNorm_eq_bornProb_one (φ : R × S → ℂ) (M : Matrix R R ℂ) :
    stateSqNorm φ M = bornProb φ (Mᴴ * M) 1 := by
  rw [stateSqNorm_eq_tensor, bornProb_eq_tensor,
    BipartiteModel.stateSqNorm_eq_bornProb_one, Matrix.star_eq_conjTranspose]

/-- Bob's squared state norm as a Born probability against the identity: the tensor-product
instance of `BipartiteModel.stateSqNorm_eq_bornProb_one` for the exchanged players. -/
theorem normSq_stateVecB_eq_one_bornProb (φ : R × S → ℂ) (M : Matrix S S ℂ) :
    ‖stateVecB φ M‖ ^ 2 = bornProb φ 1 (Mᴴ * M) := by
  rw [normSq_stateVecB_eq_tensor, bornProb_eq_tensor,
    BipartiteModel.stateSqNorm_eq_bornProb_one, BipartiteModel.bornProb_swap,
    Matrix.star_eq_conjTranspose]

end Norms

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- Pairs of polynomials in `m` variables of individual degree at most `d`: the outcomes of the
simultaneous measurement. -/
abbrev PolyPair (F : Type*) (m d : ℕ) :=
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

section EvalMarg

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]

/-- **The evaluated `W`-marginal** of a pair measurement at the point `u`: the paper's
`S-hat_{[eval_u(·_W) = a]}`, the POVM with outcomes in `F` that sums the pair operators whose
`W`-component takes the value `a` at `u`. -/
def evalMarg (S : POVMIn (PolyPair F m d) R) (W : Bas) (u : Point F m) : POVMIn F R :=
  S.map fun p => (PolyPair.proj W p).eval u

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem evalMarg_mats (S : POVMIn (PolyPair F m d) R) (W : Bas) (u : Point F m) (a : F) :
    (evalMarg S W u).op a
      = ∑ p ∈ univ.filter fun p : PolyPair F m d => (PolyPair.proj W p).eval u = a, S.op p :=
  POVMIn.map_op _ _ _

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The evaluated marginal of a projective pair measurement is projective. -/
theorem isPVM_evalMarg {S : POVMIn (PolyPair F m d) R} (hS : IsPVMIn S.op) (W : Bas)
    (u : Point F m) : IsPVMIn (evalMarg S W u).op :=
  POVMIn.isPVMIn_map hS _

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- The evaluated marginal of a pushed-forward pair measurement is the pushed-forward evaluated
marginal. -/
theorem evalMarg_pushforward {R' : Type*} [Ring R'] [StarRing R'] [PartialOrder R']
    [StarOrderedRing R'] [Algebra ℂ R] [Algebra ℂ R'] (f : R →⋆ₙₐ[ℂ] R') (hf : f 1 = 1)
    (S : POVMIn (PolyPair F m d) R) (W : Bas) (u : Point F m) :
    evalMarg (S.pushforward f hf) W u = (evalMarg S W u).pushforward f hf :=
  POVMIn.ext' fun a => by
    rw [POVMIn.pushforward_op, evalMarg_mats, evalMarg_mats, map_sum]
    rfl

end EvalMarg

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ]
  [StarProper ℬ]
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']

/-- **The simultaneous pair measurement** (`lem:qld-simultaneous`, the paper's `lem:qld-4-7`),
for a projective strategy `S` of the Pauli basis test in a bipartite model `M`, with error `δ`: in
each player's algebra of a model `K` into which the expanded model `M.reg (Anc F m)` embeds along
`ι`, a projective measurement with outcomes pairs of polynomials, whose evaluated marginals are
consistent on `K`'s state with the opposite party's expanded point measurements carried along
`ι`. -/
structure SimulPair {hm : m ∣ Fintype.card F} (M : BipartiteModel 𝒞 𝒜 ℬ)
    (S : M.ProjStrat (qldGame (d := d) hm)) (K : BipartiteModel 𝒞' 𝒜' ℬ')
    (ι : (M.reg (Anc F m)).Embedding K) (δ : ℝ) where
  /-- Alice's pair measurement. -/
  SA : POVMIn (PolyPair F m d) 𝒜'
  SA_proj : IsPVMIn SA.op
  /-- Bob's pair measurement (unused by stage 5, kept for `lem:qld-simultaneous`). -/
  SB : POVMIn (PolyPair F m d) ℬ'
  SB_proj : IsPVMIn SB.op
  /-- Alice's evaluated marginals track Bob's expanded point measurements. -/
  consA : ∀ W : Bas, K.inconsistency (uniform (Point F m)) (fun u => evalMarg SA W u)
    (fun u => (hatPtPOVM S.PB W u).pushforward ι.ΦB ι.ΦB_one) ≤ δ
  /-- Bob's evaluated marginals track Alice's expanded point measurements. -/
  consB : ∀ W : Bas, K.inconsistency (uniform (Point F m))
    (fun u => (hatPtPOVM S.PA W u).pushforward ι.ΦA ι.ΦA_one) (fun u => evalMarg SB W u) ≤ δ

namespace SimulPair

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

/-- The error can only be weakened. -/
def mono (P : SimulPair M S K ι δ) {δ' : ℝ} (h : δ ≤ δ') : SimulPair M S K ι δ' :=
  { P with consA := fun W => le_trans (P.consA W) h, consB := fun W => le_trans (P.consB W) h }

/-- **The state of `K` is a unit vector**, the strategy's being one: the matrix structure's
`Φ_unit`. -/
theorem ψ_unit (_P : SimulPair M S K ι δ) : ‖K.ψ‖ = 1 := by
  rw [ι.norm_ψ]
  exact hatVec_unit S.ψ_unit

/-- **`K` reproduces every expectation of the expanded model**, so every conclusion of stages 2
and 3 about `M.reg (Anc F m)` transfers to `K` for operators carried along `ι`. -/
theorem bornProb_aOp_aOp (_P : SimulPair M S K ι δ) (X : Matrix (Anc F m) (Anc F m) 𝒜)
    (Y : Matrix (Anc F m) (Anc F m) ℬ) :
    K.bornProb (ι.ΦA X) (ι.ΦB Y) = (M.reg (Anc F m)).bornProb X Y :=
  ι.bornProb X Y

/-- Alice's squared state norm transfers too. -/
theorem stateSqNorm_aOp (_P : SimulPair M S K ι δ) (X : Matrix (Anc F m) (Anc F m) 𝒜) :
    K.stateSqNorm (ι.ΦA X) = (M.reg (Anc F m)).stateSqNorm X :=
  ι.stateSqNorm X

/-- Bob's squared state norm transfers. -/
theorem normSq_stateVecB_aOp (_P : SimulPair M S K ι δ) (Y : Matrix (Anc F m) (Anc F m) ℬ) :
    K.swap.stateSqNorm (ι.ΦB Y) = (M.reg (Anc F m)).swap.stateSqNorm Y :=
  ι.swap_stateSqNorm Y

/-- **The cross-party deviation of two carried operators** is the one they have on the expanded
model. -/
theorem xSqNorm_aOp (_P : SimulPair M S K ι δ) (X : Matrix (Anc F m) (Anc F m) 𝒜)
    (Y : Matrix (Anc F m) (Anc F m) ℬ) :
    K.xSqNorm (ι.ΦA X) (ι.ΦB Y) = (M.reg (Anc F m)).xSqNorm X Y :=
  ι.xSqNorm X Y

section Transport

variable {𝒞'' 𝒜'' ℬ'' : Type*} [Ring 𝒞''] [StarRing 𝒞''] [Algebra ℂ 𝒞''] [Ring 𝒜'']
  [StarRing 𝒜''] [Algebra ℂ 𝒜''] [Ring ℬ''] [StarRing ℬ''] [Algebra ℂ ℬ''] [PartialOrder 𝒜'']
  [StarOrderedRing 𝒜''] [PartialOrder ℬ''] [StarOrderedRing ℬ''] {K' : BipartiteModel 𝒞'' 𝒜'' ℬ''}

/-- **A simultaneous pair measurement moves along an embedding** of its model: the two pair
measurements are pushed forward, and the consistencies are carried unchanged. -/
def transport (P : SimulPair M S K ι δ) (j : K.Embedding K') : SimulPair M S K' (j.comp ι) δ where
  SA := P.SA.pushforward j.ΦA j.ΦA_one
  SA_proj := POVMIn.isPVMIn_pushforward _ _ P.SA_proj
  SB := P.SB.pushforward j.ΦB j.ΦB_one
  SB_proj := POVMIn.isPVMIn_pushforward _ _ P.SB_proj
  consA W := by
    have hA : (fun u => evalMarg (P.SA.pushforward j.ΦA j.ΦA_one) W u)
        = fun u => (evalMarg P.SA W u).pushforward j.ΦA j.ΦA_one :=
      funext fun u => evalMarg_pushforward _ _ _ W u
    have hB : (fun u => (hatPtPOVM S.PB W u).pushforward (j.comp ι).ΦB (j.comp ι).ΦB_one)
        = fun u => ((hatPtPOVM S.PB W u).pushforward ι.ΦB ι.ΦB_one).pushforward j.ΦB j.ΦB_one :=
      funext fun u => POVMIn.ext' fun _ => rfl
    rw [hA, hB, j.inconsistency_pushforward]
    exact P.consA W
  consB W := by
    have hA : (fun u => (hatPtPOVM S.PA W u).pushforward (j.comp ι).ΦA (j.comp ι).ΦA_one)
        = fun u => ((hatPtPOVM S.PA W u).pushforward ι.ΦA ι.ΦA_one).pushforward j.ΦA j.ΦA_one :=
      funext fun u => POVMIn.ext' fun _ => rfl
    have hB : (fun u => evalMarg (P.SB.pushforward j.ΦB j.ΦB_one) W u)
        = fun u => (evalMarg P.SB W u).pushforward j.ΦB j.ΦB_one :=
      funext fun u => evalMarg_pushforward _ _ _ W u
    rw [hA, hB, j.inconsistency_pushforward]
    exact P.consB W

@[simp]
theorem transport_SA (P : SimulPair M S K ι δ) (j : K.Embedding K') :
    (P.transport j).SA = P.SA.pushforward j.ΦA j.ΦA_one := rfl

@[simp]
theorem transport_SB (P : SimulPair M S K ι δ) (j : K.Embedding K') :
    (P.transport j).SB = P.SB.pushforward j.ΦB j.ΦB_one := rfl

end Transport

end SimulPair

/-! ## The simultaneous pair measurement on the first cut of the physical state -/

/-- **A simultaneous pair measurement on the first cut of the physical state** (padding size `K`):
the model is the first cut `cut1` of the physical model, `A A' Ea | B A'' Eb (B' B'')`, into which
the register model embeds along `ι₁` (`MIPRE/Background/QLD/PhysModel.lean`). Stage 5 runs on two
of them, one for each player (the second at the exchanged players, `N := M.swap`), reading one
physical state. -/
abbrev CutSimul {hm : m ∣ Fintype.card F} (N : BipartiteModel 𝒞 𝒜 ℬ)
    (S : N.ProjStrat (qldGame (d := d) hm)) (K : ℕ) (δ : ℝ) :=
  SimulPair N S (cut1 (Anc F m) F m d N K) (ι₁ (Anc F m) F m d N K) δ

end MIPRE.QLD

end

end
