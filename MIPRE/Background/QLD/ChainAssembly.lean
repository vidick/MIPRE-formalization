/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.ChainPhysical

@[expose] public section

/-!
# The pulling chain, assembled

`MIPRE/Background/QLD/Chain.lean` and `MIPRE/Background/QLD/ChainPhysical.lean` prove the eleven
displays of `lem:qld-pauli-selfcons`'s derivation one at a time. This file names the terms they run
through and reads the displays as bounds on *consecutive deviations*, which is the form the
chaining inequality consumes.

`chainT` is the chain, on the physical model: ten terms for nine steps. The four displays
`eq:qld-pulling-0` to `-3` are the first cut's (`SimulPair.chainS`), and everything from `-5` on is
the physical model's own. The three terms between `-3` and `-5` are left out, the chain paying
nothing for them (`SimulPair.chainS_three_mulVec`, `MirrorSimul.chainS3b_mulVec`).

Three of the nine steps are free --- `eq:qld-pulling-2` and `-2b`, then `-3a` to `-5`, then
`-9a` --- and the six that are not cost, in order: item 1 of `lem:qld-helper`, the game's
point--point consistency, item 2 of `lem:qld-helper`, `eq:qld-pulling-10` complete, item 2 of
`lem:qld-helper` again at the second cut, and Schwartz--Zippel. The chain's total is nine times
their sum, not two to the ninth power, because a chain's deviation telescopes and Cauchy--Schwarz
against the constant one turns the squared norm of a sum of nine terms into nine times the sum of
their squares (`StateModel.sum_snorm_sq_chain_le`).

The last thing this file needs that `Chain.lean` did not have is the cost of `eq:qld-pulling-3`:
`sum_uniform_xSqNorm_pt_le` reads the game's point--point consistency on the physical model, which
reproduces the strategy's expectations for operators that do not see the registers.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The chain runs in the physical
model `phys (Anc F m) F m d M Mi.K` of a `MirrorSimul`. The matrix route ran the first four terms on
a regrouping `mVec` of the first cut's state and carried them to the physical cut by an explicit
lift (`physLift`); the first cut is a reading of the physical model's state model, so here the
first four terms are the first cut's terms as they stand, and nothing is lifted. That the physical
model reproduces the strategy's expectations (`bornProb_mVec_ext`, `xSqNorm_mVec_ext`) is the
embedding of the model into its physical model with the registers inert (`physInert`); the steps
that read the second cut go through `MirrorSimul.bornProb_physVec_bOp`. The constants are the
matrix ones.
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

section Probe

variable {hm : m ∣ Fintype.card F} {N : BipartiteModel 𝒞 𝒜 ℬ}
  {S : N.ProjStrat (qldGame (d := d) hm)} {K : ℕ} {δ : ℝ}

set_option synthInstance.maxSize 1000

namespace SimulPair

variable (P : CutSimul N S K δ)

/-- **The cut the chain runs on reproduces the strategy's own expectations** for operators
extended by the identity on every register: the model embeds in its physical model with the
registers inert (`physInert`). -/
theorem bornProb_mVec_ext (_P : CutSimul N S K δ) (X : 𝒜) (Y : ℬ) :
    (phys (Anc F m) F m d N K).bornProb ((physInert (Anc F m) F m d N K).ΦA X)
        ((physInert (Anc F m) F m d N K).ΦB Y)
      = N.bornProb X Y :=
  (physInert (Anc F m) F m d N K).bornProb X Y

/-- **And so it reproduces the strategy's cross-party deviations.** -/
theorem xSqNorm_mVec_ext (_P : CutSimul N S K δ) (X : 𝒜) (Y : ℬ) :
    (phys (Anc F m) F m d N K).xSqNorm ((physInert (Anc F m) F m d N K).ΦA X)
        ((physInert (Anc F m) F m d N K).ΦB Y)
      = N.xSqNorm X Y :=
  (physInert (Anc F m) F m d N K).xSqNorm X Y

/-- **The cost of `eq:qld-pulling-3`**: the point measurements' own cross-party deviation, read
on the physical model, is the game's point--point consistency and nothing more. -/
theorem sum_uniform_xSqNorm_pt_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas) :
    ∑ u, uniform (Point F m) u
        * ∑ k : F, (phys (Anc F m) F m d N K).xSqNorm (P.ptA W u k) (P.ptB W u k)
      ≤ 2 * (86 * ε) := by
  classical
  have hP : ∀ u : Point F m, IsPVMIn (ptAtPOVM S.PA W u).op :=
    fun u => POVMIn.isPVMIn_map (S.projA _) _
  have hQ : ∀ u : Point F m, IsPVMIn (ptAtPOVM S.PB W u).op :=
    fun u => POVMIn.isPVMIn_map (S.projB _) _
  have hkey : (∑ u, uniform (Point F m) u
        * ∑ k : F, (phys (Anc F m) F m d N K).xSqNorm (P.ptA W u k) (P.ptB W u k))
      = N.xPovmDist (uniform (Point F m)) (fun u => ptAtPOVM S.PA W u)
        (fun u => ptAtPOVM S.PB W u) := by
    rw [BipartiteModel.xPovmDist]
    exact Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun k _ =>
      P.xSqNorm_mVec_ext _ _)
  rw [hkey]
  have h := inconsistency_pt_pt_le S.ψ_unit hfail S.projA S.projB W
  rw [inconsistency_eq_half_xPovmDist (uniform (Point F m)) S.ψ_unit _ _ hP hQ] at h
  linarith

end SimulPair

end Probe

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- A deviation that vanishes on the state has no state-norm. -/
theorem snorm_sub_eq_zero_of_mulVec (M : StateModel 𝒞) {X Y : 𝒞}
    (h : M.π X M.ψ = M.π Y M.ψ) : M.snorm (X - Y) = 0 := by
  show ‖M.π (X - Y) M.ψ‖ = 0
  rw [map_sub, _root_.sub_apply, h, sub_self, norm_zero]

section Physical

variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {δ : ℝ}

set_option synthInstance.maxSize 1000

namespace MirrorSimul

variable (Mi : MirrorSimul M S δ)

/-- **The chain, on the physical model.** Ten terms: the four displays `eq:qld-pulling-0` to `-3`
of the first cut, then `-5`, `-7`, `-9a`, `-10`, `-11` and `-12`. The three terms between `-3` and
`-5` are left out, the chain paying nothing for them. -/
def chainT (W : Bas) (v : Anc F m) (u : Point F m) :
    ℕ → F → Matrix (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K)
      (PhysReg (Anc F m) F m d Mi.K × PhysReg (Anc F m) F m d Mi.K) 𝒞
  | 0 => fun a => Mi.first.chainS W v u 0 a
  | 1 => fun a => Mi.first.chainS W v u 1 a
  | 2 => fun a => Mi.first.chainS W v u 2 a
  | 3 => fun a => Mi.first.chainS W v u 3 a
  | 4 => fun a => ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d)
          × Anc F m) × Anc F m => dotF (chainLabel t.1.1 t.1.2) v = a,
      Mi.chainP W t * ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceHat W u (t.1.1.eval u))
        * (phys (Anc F m) F m d M Mi.K).πB
          (Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))))
  | 5 => fun a => ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d)
          × Anc F m) × Anc F m => dotF (chainLabel t.1.1 t.1.2) v = a,
      Mi.chainP W t * (phys (Anc F m) F m d M Mi.K).πB
        (Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))
  | 6 => fun a => ∑ q ∈ univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          dotF (chainLabel q.1.1 q.1.2) v = a,
      Mi.chainQ W q * Mi.chainV W u q
  | 7 => fun a => ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
      Mi.chainQ W q * Mi.chainV W u q
  | 8 => fun a => ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
      Mi.chainQ W q
  | _ => fun a => Mi.endOp W v a

/-- **Step 0 to 1 is `eq:qld-pulling-1`**, at item 1 of `lem:qld-helper`'s own constant. -/
theorem sum_uniform_snorm_sq_chainT_zero_one (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 0 a - Mi.chainT W v u 1 a) ^ 2) ≤ δ :=
  Mi.first.sum_uniform_snorm_sq_chainS_zero_one W v

/-- **Step 1 to 2 is free**, being displays `eq:qld-pulling-2` and `-2b`. -/
theorem sum_snorm_sq_chainT_one_two (W : Bas) (v : Anc F m) (u : Point F m) :
    (∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        (Mi.chainT W v u 1 a - Mi.chainT W v u 2 a) ^ 2) = 0 :=
  Mi.first.sum_snorm_sq_chainS_one_two W v u

/-- **Step 2 to 3 is `eq:qld-pulling-3`**, the insertion, at the game's point--point
consistency. -/
theorem sum_uniform_snorm_sq_chainT_two_three {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas)
    (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 2 a - Mi.chainT W v u 3 a) ^ 2)
      ≤ 2 * (86 * ε) := by
  have hstep : ∀ u : Point F m,
      (∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
          (Mi.chainT W v u 2 a - Mi.chainT W v u 3 a) ^ 2)
        ≤ ∑ k : F, (phys (Anc F m) F m d M Mi.K).xSqNorm (Mi.first.ptA W u k)
            (Mi.first.ptB W u k) :=
    fun u => Mi.first.sum_snorm_sq_chainS_two_three W v u (le_refl _)
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hstep u) (uniform_nonneg (Point F m) u)) ?_
  exact Mi.first.sum_uniform_xSqNorm_pt_le hfail W

/-- **Step 3 to 4 is free**, being displays `eq:qld-pulling-3a`, `-3b`, `-4` and `-5`. -/
theorem snorm_chainT_three_four (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    (phys (Anc F m) F m d M Mi.K).snorm (Mi.chainT W v u 3 a - Mi.chainT W v u 4 a) = 0 :=
  snorm_sub_eq_zero_of_mulVec (phys (Anc F m) F m d M Mi.K).toStateModel
    ((Mi.first.chainS_three_mulVec W v u a).trans (Mi.chainS3b_mulVec W v u a))

/-- **Step 4 to 5 is what `eq:qld-pulling-5` to `-7` bounds**: the gap between Alice's pair
measurement with her own point measurement beside it and without. -/
theorem chainT_five_sub_four (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Mi.chainT W v u 5 a - Mi.chainT W v u 4 a
      = ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
          => dotF (chainLabel t.1.1 t.1.2) v = a,
        Mi.chainP W t * Mi.chainW W u t := by
  classical
  show (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
          => dotF (chainLabel t.1.1 t.1.2) v = a,
        Mi.chainP W t * (phys (Anc F m) F m d M Mi.K).πB
          (Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))))
      - (∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
          => dotF (chainLabel t.1.1 t.1.2) v = a,
        Mi.chainP W t * ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceHat W u (t.1.1.eval u))
          * (phys (Anc F m) F m d M Mi.K).πB
            (Mi.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))))) = _
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [chainW, map_sub, map_one, sub_mul, one_mul, mul_sub]

/-- **And its cost is display `eq:qld-pulling-9`**, item 2 of `lem:qld-helper`. -/
theorem sum_uniform_snorm_sq_chainT_four_five {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas)
    (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 4 a - Mi.chainT W v u 5 a) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (le_of_eq ?_) (Mi.sum_uniform_snorm_sq_chainP_le hfail W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [StateModel.snorm_sub_comm, Mi.chainT_five_sub_four W v u a]

/-- **Step 5 to 6 is free**, being display `eq:qld-pulling-9a`: left-multiplying by Bob's own
pair measurement, which is the identity. -/
theorem chainT_five_eq_six (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Mi.chainT W v u 5 a = Mi.chainT W v u 6 a := by
  classical
  have h5 : Mi.chainT W v u 5 a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a, ∑ h' : Anc F m,
        Mi.chainP W (p, h') * (phys (Anc F m) F m d M Mi.K).πB
          (Mi.bobHat W u (p.1.eval u + dotF p.2 (indVec u) + dotF h' (indVec u))) :=
    sum_chainLabel_filter v a _
  have h6 : Mi.chainT W v u 6 a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
        ∑ r : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
          Mi.chainQ W (p, r) * Mi.chainV W u (p, r) :=
    sum_chainLabel_filter v a _
  rw [h5, h6]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h' _ => ?_
  have hV : ∀ g' : LowIndDegPoly (F := F) (m := m) (d := d),
      Mi.chainV W u (p, (g', h'))
        = (phys (Anc F m) F m d M Mi.K).πB
          (Mi.bobHat W u (p.1.eval u + dotF p.2 (indVec u) + dotF h' (indVec u))) :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun g' (_ : g' ∈ univ) => by rw [hV g'], ← Finset.sum_mul,
    Mi.sum_poly_chainQ W p h']

/-- **Step 6 to 7 is `eq:qld-pulling-10`**: what the chain drops is the pairs whose outcomes
disagree at the sampled point. -/
theorem chainT_six_sub_seven (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Mi.chainT W v u 6 a - Mi.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q ≠ q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q * Mi.chainV W u q := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
      dotF (chainLabel q.1.1 q.1.2) v = a)
    (fun q => chainQShift u q = q.2.1.eval u)
    (fun q => Mi.chainQ W q * Mi.chainV W u q)
  have e1 : (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          dotF (chainLabel q.1.1 q.1.2) v = a).filter
        (fun q => chainQShift u q = q.2.1.eval u)
      = (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          chainQShift u q = q.2.1.eval u).filter
        (fun q => dotF (chainLabel q.1.1 q.1.2) v = a) := Finset.filter_comm _ _ _
  have e2 : (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          dotF (chainLabel q.1.1 q.1.2) v = a).filter
        (fun q => ¬ chainQShift u q = q.2.1.eval u)
      = (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          chainQShift u q ≠ q.2.1.eval u).filter
        (fun q => dotF (chainLabel q.1.1 q.1.2) v = a) := Finset.filter_comm _ _ _
  rw [e1, e2] at hsplit
  have h6 : Mi.chainT W v u 6 a
      = ∑ q ∈ univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q * Mi.chainV W u q := rfl
  have h7 : Mi.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q * Mi.chainV W u q := rfl
  rw [h6, h7, ← hsplit, add_sub_cancel_left]

/-- **Bob's sandwiched marginal, read on the second cut**: the sandwich of the second cut's pair
measurement by Bob's hatted point measurement, which is what `SimulPair.sum_uniform_qform_ne_le`
bounds at the second cut. -/
theorem bornProb_bobSand_eq (W : Bas) (u : Point F m) (c : F)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    (phys (Anc F m) F m d M Mi.K).bornProb 1
        (compHom (diagonal fun _ : Anc F m => Mi.bobSand W u c g))
      = (cut1 (Anc F m) F m d M.swap Mi.K).qform
          ((cut1 (Anc F m) F m d M.swap Mi.K).πA
              ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c))
            * (cut1 (Anc F m) F m d M.swap Mi.K).πA ((polyMarg Mi.second.SA W).op g)
            * (cut1 (Anc F m) F m d M.swap Mi.K).πA
              ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c))) := by
  have hsa : star ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c))
      = (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u c) := by
    rw [← map_star, SimulPair.hatMats_conjTranspose]
  rw [Mi.bornProb_physVec_bOp, BipartiteModel.bornProb, map_one, mul_one, bobSand, hsa,
    map_mul, map_mul]

set_option maxHeartbeats 1000000 in
/-- **And its cost**, which is display `eq:qld-pulling-10` complete, read on the second cut. -/
theorem sum_uniform_snorm_sq_chainT_six_seven {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas)
    (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 6 a - Mi.chainT W v u 7 a) ^ 2)
      ≤ δ + 2 * Real.sqrt (172 * ε) := by
  classical
  have hstep : ∀ u : Point F m,
      (∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
          (Mi.chainT W v u 6 a - Mi.chainT W v u 7 a) ^ 2)
        ≤ ∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
            q.2 ≠ q.1.eval u,
          (cut1 (Anc F m) F m d M.swap Mi.K).qform
            ((cut1 (Anc F m) F m d M.swap Mi.K).πA
                ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u q.2))
              * (cut1 (Anc F m) F m d M.swap Mi.K).πA ((polyMarg Mi.second.SA W).op q.1)
              * (cut1 (Anc F m) F m d M.swap Mi.K).πA
                ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u q.2))) := by
    intro u
    have h1 : (∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
          (Mi.chainT W v u 6 a - Mi.chainT W v u 7 a) ^ 2)
        ≤ ∑ q, ∑ c ∈ univ.filter fun c : F => c ≠ q.2.1.eval u,
            (phys (Anc F m) F m d M Mi.K).qform
              (star (Mi.bobTail W u c) * Mi.chainQ W q * Mi.bobTail W u c) := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        congrArg (· ^ 2) (congrArg (phys (Anc F m) F m d M Mi.K).snorm
          (Mi.chainT_six_sub_seven W v u a)))) ?_
      exact Mi.sum_snorm_sq_chainQ_disagree_le W v u
    rw [Mi.sum_qform_bobTail_eq W u] at h1
    refine le_trans h1 (le_of_eq (Eq.symm ?_))
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => (Mi.bornProb_bobSand_eq W u c g).symm
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hstep u) (uniform_nonneg (Point F m) u)) ?_
  exact Mi.second.sum_uniform_qform_ne_le (povmValue_swapped_le hfail) W

/-- Bob's lift is unital. -/
theorem bobLift_one :
    Mi.bobLift (1 : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ) = 1 := by
  rw [bobLift, diagonal_one, compHom_one, map_one]

/-- And additive. -/
theorem bobLift_sub
    (T T' : Matrix (PadAnc F m d Mi.K × Anc F m) (PadAnc F m d Mi.K × Anc F m) ℬ) :
    Mi.bobLift (T - T') = Mi.bobLift T - Mi.bobLift T' := by
  rw [bobLift, bobLift, bobLift, ← map_sub, ← map_sub, diagonal_sub]

/-- **Step 7 to 8 is `eq:qld-pulling-11`**: dropping Bob's point measurement from his side. -/
theorem chainT_eight_sub_seven (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Mi.chainT W v u 8 a - Mi.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q
          * Mi.bobLift (1 - (ι₁ (Anc F m) F m d M.swap Mi.K).ΦA
              (hatMats S.PB W u (q.2.1.eval u))) := by
  classical
  have h8 : Mi.chainT W v u 8 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q := rfl
  have h7 : Mi.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q * Mi.chainV W u q := rfl
  rw [h8, h7, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hag : chainQShift u q = q.2.1.eval u :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hV : Mi.chainV W u q
      = Mi.bobLift ((ι₁ (Anc F m) F m d M.swap Mi.K).ΦA (hatMats S.PB W u (q.2.1.eval u))) := by
    rw [chainV, hag]
    rfl
  rw [hV, Mi.bobLift_sub, Mi.bobLift_one, mul_sub, mul_one]

/-- **And its cost**, which is item 2 of `lem:qld-helper` at the second cut. -/
theorem sum_uniform_snorm_sq_chainT_seven_eight {ε : ℝ} (hfail : 1 - S.value ≤ ε) (W : Bas)
    (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 7 a - Mi.chainT W v u 8 a) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (le_of_eq ?_) (Mi.sum_uniform_snorm_sq_chainQ_agree_le hfail W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [StateModel.snorm_sub_comm, Mi.chainT_eight_sub_seven W v u a]

end MirrorSimul

/-- **Coupled pairs agree at every point.** The coupling is an identity of polynomials, so
evaluating it at the sampled point gives the chain's agreement condition. -/
theorem chainQShift_eq_of_coupled (u : Point F m)
    {q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)}
    (hc : ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2) :
    MIPRE.QLD.chainQShift u q = q.2.1.eval u := by
  rw [chainQShift_eq_iff, dotF_indVec, dotF_indVec, ← LowIndDegPoly.eval_toMv,
    ← LowIndDegPoly.eval_toMv, ← map_add, ← map_add]
  exact congrArg (MvPolynomial.eval u) hc

namespace MirrorSimul

variable (Mi : MirrorSimul M S δ)

/-- **Step 8 to 9 is `eq:qld-pulling-12`**: what the chain drops is the pairs that agree at the
sampled point without being coupled. -/
theorem chainT_eight_sub_nine (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Mi.chainT W v u 8 a - Mi.chainT W v u 9 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            MIPRE.QLD.chainQShift u q = q.2.1.eval u
              ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
        × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
        MIPRE.QLD.chainQShift u q = q.2.1.eval u).filter
      fun q => dotF (chainLabel q.1.1 q.1.2) v = a)
    (fun q => ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2) (fun q => Mi.chainQ W q)
  have e1 : ((univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          MIPRE.QLD.chainQShift u q = q.2.1.eval u).filter
        fun q => dotF (chainLabel q.1.1 q.1.2) v = a).filter
        (fun q => ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2)
      = coupledIdx (F := F) (m := m) (d := d) v a := by
    ext q
    simp only [Finset.mem_filter, mem_univ, true_and, mem_coupledIdx]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨chainQShift_eq_of_coupled u h.1, h.2⟩, h.1⟩⟩
  have e2 : ((univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          MIPRE.QLD.chainQShift u q = q.2.1.eval u).filter
        fun q => dotF (chainLabel q.1.1 q.1.2) v = a).filter
        (fun q => ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2)
      = (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            MIPRE.QLD.chainQShift u q = q.2.1.eval u
              ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a := by
    ext q
    simp only [Finset.mem_filter, mem_univ, true_and]
    tauto
  rw [e1, e2] at hsplit
  have h9 : Mi.chainT W v u 9 a
      = ∑ q ∈ coupledIdx (F := F) (m := m) (d := d) v a, Mi.chainQ W q :=
    Mi.endOp_eq_sum_chainQ W v a
  have h8 : Mi.chainT W v u 8 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            MIPRE.QLD.chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        Mi.chainQ W q := rfl
  rw [h8, h9, ← hsplit, add_sub_cancel_left]

/-- **And its cost is `md/q`**, by Schwartz--Zippel. -/
theorem sum_uniform_snorm_sq_chainT_eight_nine (hd : 1 ≤ d) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 8 a - Mi.chainT W v u 9 a) ^ 2)
      ≤ (m : ℝ) * d / Fintype.card F := by
  refine le_trans (le_of_eq ?_) (Mi.sum_uniform_snorm_sq_chainQ_notCoupled_le hd W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [Mi.chainT_eight_sub_nine W v u a]

/-! ## The three free steps, averaged -/

theorem sum_uniform_snorm_sq_chainT_one_two (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 1 a - Mi.chainT W v u 2 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by rw [Mi.sum_snorm_sq_chainT_one_two W v u, mul_zero]

theorem sum_uniform_snorm_sq_chainT_three_four (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 3 a - Mi.chainT W v u 4 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by
    rw [Finset.sum_eq_zero fun a (_ : a ∈ univ) => by
      rw [Mi.snorm_chainT_three_four W v u a]
      norm_num, mul_zero]

theorem sum_uniform_snorm_sq_chainT_five_six (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 5 a - Mi.chainT W v u 6 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by
    rw [Finset.sum_eq_zero fun a (_ : a ∈ univ) => by
      rw [Mi.chainT_five_eq_six W v u a, sub_self, StateModel.snorm_zero]
      norm_num, mul_zero]

end MirrorSimul

omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
/-- Averaging a constant multiple of a chain's steps: the average goes inside. -/
theorem sum_mul_const_mul_sum_range {X : Type*} [Fintype X] (μ : X → ℝ) (n : ℕ)
    (f : ℕ → X → ℝ) (c : ℝ) :
    (∑ x, μ x * (c * ∑ k ∈ Finset.range n, f k x))
      = c * ∑ k ∈ Finset.range n, ∑ x, μ x * f k x :=
  calc (∑ x, μ x * (c * ∑ k ∈ Finset.range n, f k x))
      = ∑ x, ∑ k ∈ Finset.range n, c * (μ x * f k x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k ∈ Finset.range n, ∑ x, c * (μ x * f k x) := Finset.sum_comm
    _ = c * ∑ k ∈ Finset.range n, ∑ x, μ x * f k x := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

namespace MirrorSimul

variable (Mi : MirrorSimul M S δ)

/-- The chain starts at Alice's exact Pauli measurement on her physical registers. -/
theorem chainT_zero_eq (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Mi.chainT W v u 0 a = (phys (Anc F m) F m d M Mi.K).πA (Mi.aliceMTilde W v a) :=
  rfl

/-- And ends at `eq:qld-pulling-12`. -/
theorem chainT_nine_eq (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    Mi.chainT W v u 9 a = Mi.endOp W v a := rfl

set_option maxHeartbeats 1000000 in
/-- **The pulling chain, assembled.** Nine steps, of which three are free; the chain's total
deviation is at most nine times the sum of the steps', by Cauchy--Schwarz against the constant
one. -/
theorem sum_uniform_snorm_sq_chainT_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
            (Mi.chainT W v u 0 a - Mi.chainT W v u 9 a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  classical
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left
      ((phys (Anc F m) F m d M Mi.K).sum_snorm_sq_chain_le univ 9 (Mi.chainT W v u))
      (uniform_nonneg (Point F m) u)) ?_
  rw [sum_mul_const_mul_sum_range (uniform (Point F m)) 9
    (fun k u => ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
      (Mi.chainT W v u k a - Mi.chainT W v u (k + 1) a) ^ 2)
    ((9 : ℕ) : ℝ)]
  have b0 := Mi.sum_uniform_snorm_sq_chainT_zero_one W v
  have b1 := Mi.sum_uniform_snorm_sq_chainT_one_two W v
  have b2 := Mi.sum_uniform_snorm_sq_chainT_two_three hfail W v
  have b3 := Mi.sum_uniform_snorm_sq_chainT_three_four W v
  have b4 := Mi.sum_uniform_snorm_sq_chainT_four_five hfail W v
  have b5 := Mi.sum_uniform_snorm_sq_chainT_five_six W v
  have b6 := Mi.sum_uniform_snorm_sq_chainT_six_seven hfail W v
  have b7 := Mi.sum_uniform_snorm_sq_chainT_seven_eight hfail W v
  have b8 := Mi.sum_uniform_snorm_sq_chainT_eight_nine hd W v
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  linarith

/-- **Display `eq:qld-pulling-cons` for Alice**: her exact Pauli measurement on her physical
registers is close, in summed squared state distance, to the chain's endpoint. -/
theorem sum_uniform_snorm_sq_mTildeAnc_endOp_le {ε : ℝ} (hfail : 1 - S.value ≤ ε) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u * ∑ a : F, (phys (Anc F m) F m d M Mi.K).snorm
        ((phys (Anc F m) F m d M Mi.K).πA (Mi.aliceMTilde W v a) - Mi.endOp W v a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  refine le_trans (le_of_eq ?_) (Mi.sum_uniform_snorm_sq_chainT_le hfail hd W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [Mi.chainT_zero_eq W v u a, Mi.chainT_nine_eq W v u a]

end MirrorSimul

end Physical

end MIPRE.QLD

end
