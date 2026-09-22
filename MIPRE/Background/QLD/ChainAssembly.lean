/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Chain

/-!
# The pulling chain, assembled

`MIPRE/Background/QLD/Chain.lean` proves the eleven displays of `lem:qld-pauli-selfcons`'s
derivation one at a time. This file names the terms they run through and reads the displays as
bounds on *consecutive deviations*, which is the form the chaining inequality consumes.

`chainT` is the chain, on the physical cut: ten terms for nine steps. The four displays
`eq:qld-pulling-0` to `-3` are local in the grouping the state `Phi` lives on and enter lifted;
everything from `-5` on is local in the physical grouping and enters directly. The three terms
between `-3` and `-5` are left out, the chain paying nothing for them
(`physLift_chainU3b_mulVec`).

Three of the nine steps are free --- `eq:qld-pulling-2` and `-2b`, then `-3a` to `-5`, then
`-9a` --- and the six that are not cost, in order: item 1 of `lem:qld-helper`, the game's
point--point consistency, item 2 of `lem:qld-helper`, `eq:qld-pulling-10` complete, item 2 of
`lem:qld-helper` again at the second cut, and Schwartz--Zippel. The chain's total is nine times
their sum, not two to the ninth power, because a chain's deviation telescopes and Cauchy--Schwarz
against the constant one turns the squared norm of a sum of nine terms into nine times the sum of
their squares (`sum_snorm_sq_chain_le`).

The last thing this file needs that `Chain.lean` did not have is the cost of `eq:qld-pulling-3`:
`sum_uniform_xSqNorm_pt_le` reads the game's point--point consistency on the cut the chain runs
on, which the padded state reproduces because it reproduces the expanded state's expectations and
the expanded state's pair contributes only its norm.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LowDegree MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

section Probe

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

set_option synthInstance.maxSize 1000

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **The cut the chain runs on reproduces the strategy's own expectations** for operators
extended by the identity on every ancilla: the padding by `Phi_reduced`, the entangled pair by
its own norm. -/
theorem bornProb_mVec_ext (X : Matrix dA dA ℂ) (Y : Matrix dB dB ℂ) :
    bornProb P.mVec
        (aOp (aOp (aOp X)) : Matrix ((((dA × Anc F m) × P.EA) × Anc F m)) _ ℂ)
        (aOp Y : Matrix (dB × P.EB) _ ℂ)
      = bornProb ψ X Y :=
  calc bornProb P.mVec
        (aOp (aOp (aOp X)) : Matrix ((((dA × Anc F m) × P.EA) × Anc F m)) _ ℂ)
        (aOp Y : Matrix (dB × P.EB) _ ℂ)
      = bornProb P.Φ (aOp (aOp X)) (aOp (Y ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))) :=
        bornProb_regroupVec P.Φ (aOp (aOp X) : Matrix ((dA × Anc F m) × P.EA) _ ℂ) Y 1
    _ = bornProb (hatVec (F := F) (m := m) ψ) (X ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ))
          (Y ⊗ₖ (1 : Matrix (Anc F m) (Anc F m) ℂ)) :=
        P.bornProb_aOp_aOp _ _
    _ = bornProb ψ X Y := by
        rw [hatVec, bornProb_expVec_kron ψ _ Matrix.PosSemidef.one Matrix.PosSemidef.one,
          bornProb_one_one (epr_unit (F := F) (n := Fin m → Bool)), mul_one]

/-- **And so it reproduces the strategy's cross-party deviations.** -/
theorem xSqNorm_mVec_ext {X : Matrix dA dA ℂ} (hX : Xᴴ = X) (Y : Matrix dB dB ℂ) :
    xSqNorm P.mVec
        (aOp (aOp (aOp X)) : Matrix ((((dA × Anc F m) × P.EA) × Anc F m)) _ ℂ)
        (aOp Y : Matrix (dB × P.EB) _ ℂ)
      = xSqNorm ψ X Y := by
  have hsa : ((aOp (aOp (aOp X)) : Matrix ((((dA × Anc F m) × P.EA) × Anc F m)) _ ℂ))ᴴ
      = aOp (aOp (aOp X)) := by
    rw [aOp_conjTranspose, aOp_conjTranspose, aOp_conjTranspose, hX]
  have e1 : stateSqNorm P.mVec
      (aOp (aOp (aOp X)) : Matrix ((((dA × Anc F m) × P.EA) × Anc F m)) _ ℂ)
      = stateSqNorm ψ X := by
    rw [stateSqNorm_eq_bornProb_one, stateSqNorm_eq_bornProb_one, hsa, hX, ← aOp_mul, ← aOp_mul,
      ← aOp_mul, show (1 : Matrix (dB × P.EB) (dB × P.EB) ℂ) = aOp 1 from aOp_one.symm]
    exact P.bornProb_mVec_ext (X * X) 1
  have e2 : ‖stateVecB P.mVec (aOp Y : Matrix (dB × P.EB) _ ℂ)‖ ^ 2
      = ‖stateVecB ψ Y‖ ^ 2 := by
    rw [normSq_stateVecB_eq_one_bornProb, normSq_stateVecB_eq_one_bornProb, aOp_conjTranspose,
      ← aOp_mul, show (1 : Matrix ((((dA × Anc F m) × P.EA) × Anc F m))
          ((((dA × Anc F m) × P.EA) × Anc F m)) ℂ) = aOp (aOp (aOp 1)) from by
        rw [aOp_one, aOp_one, aOp_one]]
    exact P.bornProb_mVec_ext 1 (Yᴴ * Y)
  rw [xSqNorm_eq_expand _ hsa, xSqNorm_eq_expand _ hX, e1, e2, P.bornProb_mVec_ext X Y]

/-- **The cost of `eq:qld-pulling-3`**: the point measurements' own cross-party deviation, read
on the cut the chain runs on, is the game's point--point consistency and nothing more. -/
theorem sum_uniform_xSqNorm_pt_le {hm : m ∣ Fintype.card F} {ε : ℝ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) :
    ∑ u, uniform (Point F m) u * ∑ k : F, xSqNorm P.mVec (P.ptA W u k) (P.ptB W u k)
      ≤ 2 * (86 * ε) := by
  classical
  have hM : ∀ u : Point F m, IsPVM fun o => (((ptAtPOVM MA W u).mats o).val) :=
    fun u => isPVM_povm_map _ (hprojA _) _
  have hN : ∀ u : Point F m, IsPVM fun o => (((ptAtPOVM MB W u).mats o).val) :=
    fun u => isPVM_povm_map _ (hprojB _) _
  have hkey : (∑ u, uniform (Point F m) u
        * ∑ k : F, xSqNorm P.mVec (P.ptA W u k) (P.ptB W u k))
      = xPovmDist (uniform (Point F m)) ψ (fun u => ptAtPOVM MA W u)
        (fun u => ptAtPOVM MB W u) := by
    rw [xPovmDist]
    exact Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun k _ =>
      P.xSqNorm_mVec_ext ((hM u).isSelfAdjoint k) _)
  rw [hkey]
  have h := inconsistency_pt_pt_le (hm := hm) hψ hfail hprojA hprojB W
  rw [inconsistency_eq_half_xPovmDist (uniform (Point F m)) hψ _ _ hM hN] at h
  linarith

end SimulPair

end Probe

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- A deviation that vanishes on the state has no state-norm. -/
theorem snorm_sub_eq_zero_of_mulVec {N : Type*} [Fintype N] [DecidableEq N] (w : N → ℂ)
    {X Y : Matrix N N ℂ} (h : X *ᵥ w = Y *ᵥ w) : snorm w (X - Y) = 0 := by
  rw [snorm, Matrix.sub_mulVec, h, sub_self]
  simp [evec]

section Physical

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

set_option synthInstance.maxSize 1000

namespace MirrorSimul

variable (M : MirrorSimul ψ MA MB δ)

/-- **The chain, on the physical cut.** Ten terms: the four displays `eq:qld-pulling-0` to `-3`
lifted from the cut `Phi` lives on, then `-5`, `-7`, `-9a`, `-10`, `-11` and `-12`. The three
terms between `-3` and `-5` are left out, the chain paying nothing for them. -/
def chainT (W : Bas) (v : Anc F m) (u : Point F m) :
    ℕ → F → Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m))
      ((((dA × Anc F m) × M.Ea) × Anc F m) × (((dB × Anc F m) × M.Eb) × Anc F m)) ℂ
  | 0 => fun a => M.physLift (M.toFirst.chainS W v u 0 a)
  | 1 => fun a => M.physLift (M.toFirst.chainS W v u 1 a)
  | 2 => fun a => M.physLift (M.toFirst.chainS W v u 2 a)
  | 3 => fun a => M.physLift (M.toFirst.chainS W v u 3 a)
  | 4 => fun a => ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d)
          × Anc F m) × Anc F m => dotF (chainLabel t.1.1 t.1.2) v = a,
      M.chainP W t * (aOp (M.aliceHat W u (t.1.1.eval u))
        * bOp (M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))))
  | 5 => fun a => ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d)
          × Anc F m) × Anc F m => dotF (chainLabel t.1.1 t.1.2) v = a,
      M.chainP W t
        * bOp (M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u)))
  | 6 => fun a => ∑ q ∈ univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          dotF (chainLabel q.1.1 q.1.2) v = a,
      M.chainQ W q * M.chainV W u q
  | 7 => fun a => ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
      M.chainQ W q * M.chainV W u q
  | 8 => fun a => ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
      M.chainQ W q
  | _ => fun a => M.endOp W v a

/-- The lift preserves a deviation's state-norm, being a `*`-homomorphism. -/
theorem snorm_physLift_sub (U V : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb))
    ((((dA × Anc F m) × M.Ea) × Anc F m) × (dB × M.Eb)) ℂ) :
    snorm M.physVec (M.physLift U - M.physLift V) = snorm M.toFirst.mVec (U - V) := by
  rw [← M.physLift_sub, M.snorm_physLift]

/-- **Step 0 to 1 is `eq:qld-pulling-1`**, at item 1 of `lem:qld-helper`'s own constant. -/
theorem sum_uniform_snorm_sq_chainT_zero_one
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 0 a - M.chainT W v u 1 a) ^ 2) ≤ δ := by
  refine le_trans (le_of_eq ?_) (M.toFirst.sum_uniform_snorm_sq_chainS_zero_one hprojB W v)
  exact Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ =>
    congrArg (· ^ 2) (M.snorm_physLift_sub _ _))

/-- **Step 1 to 2 is free**, being displays `eq:qld-pulling-2` and `-2b`. -/
theorem sum_snorm_sq_chainT_one_two (W : Bas) (v : Anc F m) (u : Point F m) :
    (∑ a : F, snorm M.physVec (M.chainT W v u 1 a - M.chainT W v u 2 a) ^ 2) = 0 := by
  refine Eq.trans (Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    congrArg (· ^ 2) (M.snorm_physLift_sub (M.toFirst.chainS W v u 1 a)
      (M.toFirst.chainS W v u 2 a))) ?_
  exact M.toFirst.sum_snorm_sq_chainS_one_two W v u

/-- **Step 2 to 3 is `eq:qld-pulling-3`**, the insertion, at the game's point--point
consistency. -/
theorem sum_uniform_snorm_sq_chainT_two_three {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 2 a - M.chainT W v u 3 a) ^ 2)
      ≤ 2 * (86 * ε) := by
  have hstep : ∀ u : Point F m,
      (∑ a : F, snorm M.physVec (M.chainT W v u 2 a - M.chainT W v u 3 a) ^ 2)
        ≤ ∑ k : F, xSqNorm M.toFirst.mVec (M.toFirst.ptA W u k) (M.toFirst.ptB W u k) := by
    intro u
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      congrArg (· ^ 2) (M.snorm_physLift_sub _ _))) ?_
    exact M.toFirst.sum_snorm_sq_chainS_two_three W v u hprojB (le_refl _)
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hstep u) (uniform_nonneg (Point F m) u)) ?_
  exact M.toFirst.sum_uniform_xSqNorm_pt_le (hm := hm) hψ hfail hprojA hprojB W

/-- **Step 3 to 4 is free**, being displays `eq:qld-pulling-3a`, `-3b`, `-4` and `-5`. -/
theorem snorm_chainT_three_four (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    snorm M.physVec (M.chainT W v u 3 a - M.chainT W v u 4 a) = 0 := by
  refine snorm_sub_eq_zero_of_mulVec _ ?_
  have h1 : M.physLift (M.toFirst.chainS W v u 3 a) *ᵥ M.physVec
      = M.physLift (M.chainU3b W v u a) *ᵥ M.physVec :=
    M.physLift_mulVec_congr (by
      rw [M.chainU3b_eq]
      exact M.toFirst.chainS_three_mulVec W v u a)
  exact h1.trans (M.physLift_chainU3b_mulVec W v u a)

/-- **Step 4 to 5 is what `eq:qld-pulling-5` to `-7` bounds**: the gap between Alice's pair
measurement with her own point measurement beside it and without. -/
theorem chainT_five_sub_four (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 5 a - M.chainT W v u 4 a
      = ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
          => dotF (chainLabel t.1.1 t.1.2) v = a,
        M.chainP W t * M.chainW W u t := by
  classical
  have h5 : M.chainT W v u 5 a
      = ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
          => dotF (chainLabel t.1.1 t.1.2) v = a,
        M.chainP W t
          * bOp (M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))) := rfl
  have h4 : M.chainT W v u 4 a
      = ∑ t ∈ univ.filter fun t : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) × Anc F m
          => dotF (chainLabel t.1.1 t.1.2) v = a,
        M.chainP W t * (aOp (M.aliceHat W u (t.1.1.eval u))
          * bOp (M.bobHat W u (t.1.1.eval u + dotF t.1.2 (indVec u) + dotF t.2 (indVec u))))
      := rfl
  rw [h5, h4, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hone : (aOp ((1 : Matrix (((dA × Anc F m) × M.Ea) × Anc F m)
          (((dA × Anc F m) × M.Ea) × Anc F m) ℂ) - M.aliceHat W u (t.1.1.eval u))
        : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
          × (((dB × Anc F m) × M.Eb) × Anc F m)) _ ℂ)
      = 1 - aOp (M.aliceHat W u (t.1.1.eval u)) := by
    rw [aOp_sub, aOp_one]
  rw [chainW, hone, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]

/-- **And its cost is display `eq:qld-pulling-9`**, item 2 of `lem:qld-helper`. -/
theorem sum_uniform_snorm_sq_chainT_four_five {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 4 a - M.chainT W v u 5 a) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (le_of_eq ?_)
    (M.sum_uniform_snorm_sq_chainP_le (hm := hm) hψ hfail hprojB W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [← snorm_sub_comm, M.chainT_five_sub_four W v u a]

/-- **Step 5 to 6 is free**, being display `eq:qld-pulling-9a`: left-multiplying by Bob's own
pair measurement, which is the identity. -/
theorem chainT_five_eq_six (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 5 a = M.chainT W v u 6 a := by
  classical
  have h5 : M.chainT W v u 5 a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a, ∑ h' : Anc F m,
        M.chainP W (p, h')
          * bOp (M.bobHat W u (p.1.eval u + dotF p.2 (indVec u) + dotF h' (indVec u))) :=
    sum_chainLabel_filter v a _
  have h6 : M.chainT W v u 6 a
      = ∑ p ∈ chainIdx (F := F) (m := m) (d := d) v a,
        ∑ r : LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m,
          M.chainQ W (p, r) * M.chainV W u (p, r) :=
    sum_chainLabel_filter v a _
  rw [h5, h6]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h' _ => ?_
  have hV : ∀ g' : LowIndDegPoly (F := F) (m := m) (d := d),
      M.chainV W u (p, (g', h'))
        = bOp (M.bobHat W u (p.1.eval u + dotF p.2 (indVec u) + dotF h' (indVec u))) := by
    intro g'
    rw [chainV, bobTail, aOp_one, Matrix.one_mul]
    rfl
  rw [Finset.sum_congr rfl fun g' (_ : g' ∈ univ) => by rw [hV g'], ← Finset.sum_mul,
    M.sum_poly_chainQ W p h']

/-- **Step 6 to 7 is `eq:qld-pulling-10`**: what the chain drops is the pairs whose outcomes
disagree at the sampled point. -/
theorem chainT_six_sub_seven (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 6 a - M.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q ≠ q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q * M.chainV W u q := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
      × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
      dotF (chainLabel q.1.1 q.1.2) v = a)
    (fun q => chainQShift u q = q.2.1.eval u)
    (fun q => M.chainQ W q * M.chainV W u q)
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
  have h6 : M.chainT W v u 6 a
      = ∑ q ∈ univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
          × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
          dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q * M.chainV W u q := rfl
  have h7 : M.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q * M.chainV W u q := rfl
  rw [h6, h7, ← hsplit, add_sub_cancel_left]

/-- Bob's sandwiched marginal, read on the second cut. -/
theorem bornProb_bobSand_eq (W : Bas) (u : Point F m) (c : F)
    (g : LowIndDegPoly (F := F) (m := m) (d := d)) :
    bornProb M.physVec 1 (aOp (M.bobSand W u c g))
      = qform M.Φ' ((aOp (aOp (hatMats MB W u c))
            : Matrix (((dB × Anc F m) × M.Eb) × ((dA × Anc F m) × M.Ea)) _ ℂ)
          * aOp (((polyMarg M.SA' W).mats g).val) * aOp (aOp (hatMats MB W u c))) := by
  have hsa : ((aOp (hatMats MB W u c) : Matrix ((dB × Anc F m) × M.Eb) _ ℂ))ᴴ
      = aOp (hatMats MB W u c) := by
    rw [aOp_conjTranspose, SimulPair.hatMats_conjTranspose]
  rw [M.bornProb_physVec_bOp, bornProb_eq_qform, bOp_one, Matrix.mul_one, bobSand, hsa,
    aOp_mul, aOp_mul]

set_option maxHeartbeats 1000000 in
/-- **And its cost**, which is display `eq:qld-pulling-10` complete, read on the second cut. -/
theorem sum_uniform_snorm_sq_chainT_six_seven {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 6 a - M.chainT W v u 7 a) ^ 2)
      ≤ δ + 2 * Real.sqrt (172 * ε) := by
  classical
  have hstep : ∀ u : Point F m,
      (∑ a : F, snorm M.physVec (M.chainT W v u 6 a - M.chainT W v u 7 a) ^ 2)
        ≤ ∑ q ∈ univ.filter fun q : LowIndDegPoly (F := F) (m := m) (d := d) × F =>
            q.2 ≠ q.1.eval u,
          qform M.Φ' ((aOp (aOp (hatMats MB W u q.2))
              : Matrix (((dB × Anc F m) × M.Eb) × ((dA × Anc F m) × M.Ea)) _ ℂ)
            * aOp (((polyMarg M.SA' W).mats q.1).val) * aOp (aOp (hatMats MB W u q.2))) := by
    intro u
    have h1 : (∑ a : F, snorm M.physVec (M.chainT W v u 6 a - M.chainT W v u 7 a) ^ 2)
        ≤ ∑ q, ∑ c ∈ univ.filter fun c : F => c ≠ q.2.1.eval u,
            qform M.physVec ((M.bobTail W u c)ᴴ * M.chainQ W q * M.bobTail W u c) := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
        congrArg (· ^ 2) (congrArg (snorm M.physVec) (M.chainT_six_sub_seven W v u a)))) ?_
      exact M.sum_snorm_sq_chainQ_disagree_le W v u
    rw [M.sum_qform_bobTail_eq W u] at h1
    refine le_trans h1 (le_of_eq (Eq.symm ?_))
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => (M.bornProb_bobSand_eq W u c g).symm
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (hstep u) (uniform_nonneg (Point F m) u)) ?_
  exact M.toSecond.sum_uniform_qform_ne_le (hm := hm) (swapVec_unit hψ)
    (povmValue_swapped_le hfail) hprojB hprojA W

/-- Bob's lift is unital. -/
theorem bobLift_one :
    M.bobLift (1 : Matrix ((dB × Anc F m) × M.Eb) ((dB × Anc F m) × M.Eb) ℂ) = 1 := by
  rw [bobLift, aOp_one, aOp_one, bOp_one, Matrix.one_mul]

/-- And additive. -/
theorem bobLift_sub (T S : Matrix ((dB × Anc F m) × M.Eb) ((dB × Anc F m) × M.Eb) ℂ) :
    M.bobLift (T - S) = M.bobLift T - M.bobLift S := by
  rw [bobLift, bobLift, bobLift, aOp_sub, bOp_sub, Matrix.mul_sub]

/-- **Step 7 to 8 is `eq:qld-pulling-11`**: dropping Bob's point measurement from his side. -/
theorem chainT_eight_sub_seven (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 8 a - M.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q
          * M.bobLift (1 - (aOp (hatMats MB W u (q.2.1.eval u))
              : Matrix ((dB × Anc F m) × M.Eb) _ ℂ)) := by
  classical
  have h8 : M.chainT W v u 8 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q := rfl
  have h7 : M.chainT W v u 7 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q * M.chainV W u q := rfl
  rw [h8, h7, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hag : chainQShift u q = q.2.1.eval u :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hV : M.chainV W u q
      = M.bobLift (aOp (hatMats MB W u (q.2.1.eval u))
          : Matrix ((dB × Anc F m) × M.Eb) _ ℂ) := by
    rw [chainV, hag]
    rfl
  rw [hV, M.bobLift_sub, M.bobLift_one, Matrix.mul_sub, Matrix.mul_one]

/-- **And its cost**, which is item 2 of `lem:qld-helper` at the second cut. -/
theorem sum_uniform_snorm_sq_chainT_seven_eight {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 7 a - M.chainT W v u 8 a) ^ 2)
      ≤ 4 * δ + 2 * (172 * ε) := by
  refine le_trans (le_of_eq ?_)
    (M.sum_uniform_snorm_sq_chainQ_agree_le (hm := hm) hψ hfail hprojA W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [← snorm_sub_comm, M.chainT_eight_sub_seven W v u a]

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

variable (M : MirrorSimul ψ MA MB δ)

/-- **Step 8 to 9 is `eq:qld-pulling-12`**: what the chain drops is the pairs that agree at the
sampled point without being coupled. -/
theorem chainT_eight_sub_nine (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 8 a - M.chainT W v u 9 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            MIPRE.QLD.chainQShift u q = q.2.1.eval u
              ∧ ¬ ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
        × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
        MIPRE.QLD.chainQShift u q = q.2.1.eval u).filter
      fun q => dotF (chainLabel q.1.1 q.1.2) v = a)
    (fun q => ChainCoupled q.1.1 q.2.1 q.1.2 q.2.2) (fun q => M.chainQ W q)
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
  have h9 : M.chainT W v u 9 a
      = ∑ q ∈ coupledIdx (F := F) (m := m) (d := d) v a, M.chainQ W q :=
    M.endOp_eq_sum_chainQ W v a
  have h8 : M.chainT W v u 8 a
      = ∑ q ∈ (univ.filter fun q : (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m)
            × (LowIndDegPoly (F := F) (m := m) (d := d) × Anc F m) =>
            MIPRE.QLD.chainQShift u q = q.2.1.eval u).filter
          fun q => dotF (chainLabel q.1.1 q.1.2) v = a,
        M.chainQ W q := rfl
  rw [h8, h9, ← hsplit, add_sub_cancel_left]

/-- **And its cost is `md/q`**, by Schwartz--Zippel. -/
theorem sum_uniform_snorm_sq_chainT_eight_nine (hd : 1 ≤ d) (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 8 a - M.chainT W v u 9 a) ^ 2)
      ≤ (m : ℝ) * d / Fintype.card F := by
  refine le_trans (le_of_eq ?_) (M.sum_uniform_snorm_sq_chainQ_notCoupled_le hd W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [M.chainT_eight_sub_nine W v u a]

/-! ## The three free steps, averaged -/

theorem sum_uniform_snorm_sq_chainT_one_two (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 1 a - M.chainT W v u 2 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by rw [M.sum_snorm_sq_chainT_one_two W v u, mul_zero]

theorem sum_uniform_snorm_sq_chainT_three_four (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 3 a - M.chainT W v u 4 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by
    rw [Finset.sum_eq_zero fun a (_ : a ∈ univ) => by
      rw [M.snorm_chainT_three_four W v u a]
      norm_num, mul_zero]

theorem sum_uniform_snorm_sq_chainT_five_six (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 5 a - M.chainT W v u 6 a) ^ 2) = 0 :=
  Finset.sum_eq_zero fun u _ => by
    rw [Finset.sum_eq_zero fun a (_ : a ∈ univ) => by
      rw [M.chainT_five_eq_six W v u a, sub_self, snorm, Matrix.zero_mulVec]
      simp [evec], mul_zero]

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

variable (M : MirrorSimul ψ MA MB δ)

/-- The chain starts at Alice's exact Pauli measurement on her physical triple. -/
theorem chainT_zero_eq (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 0 a = aOp (M.toFirst.mTildeAnc W v a) :=
  M.physLift_aOp _

/-- And ends at `eq:qld-pulling-12`. -/
theorem chainT_nine_eq (W : Bas) (v : Anc F m) (u : Point F m) (a : F) :
    M.chainT W v u 9 a = M.endOp W v a := rfl

set_option maxHeartbeats 1000000 in
/-- **The pulling chain, assembled.** Nine steps, of which three are free; the chain's total
deviation is at most nine times the sum of the steps', by Cauchy--Schwarz against the constant
one. -/
theorem sum_uniform_snorm_sq_chainT_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u
        * ∑ a : F, snorm M.physVec (M.chainT W v u 0 a - M.chainT W v u 9 a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  classical
  refine le_trans (Finset.sum_le_sum fun u (_ : u ∈ univ) =>
    mul_le_mul_of_nonneg_left (sum_snorm_sq_chain_le M.physVec 9 (M.chainT W v u))
      (uniform_nonneg (Point F m) u)) ?_
  rw [sum_mul_const_mul_sum_range (uniform (Point F m)) 9
    (fun k u => ∑ a : F, snorm M.physVec (M.chainT W v u k a - M.chainT W v u (k + 1) a) ^ 2)
    ((9 : ℕ) : ℝ)]
  have b0 := M.sum_uniform_snorm_sq_chainT_zero_one hprojB W v
  have b1 := M.sum_uniform_snorm_sq_chainT_one_two W v
  have b2 := M.sum_uniform_snorm_sq_chainT_two_three (hm := hm) hψ hfail hprojA hprojB W v
  have b3 := M.sum_uniform_snorm_sq_chainT_three_four W v
  have b4 := M.sum_uniform_snorm_sq_chainT_four_five (hm := hm) hψ hfail hprojB W v
  have b5 := M.sum_uniform_snorm_sq_chainT_five_six W v
  have b6 := M.sum_uniform_snorm_sq_chainT_six_seven (hm := hm) hψ hfail hprojA hprojB W v
  have b7 := M.sum_uniform_snorm_sq_chainT_seven_eight (hm := hm) hψ hfail hprojA W v
  have b8 := M.sum_uniform_snorm_sq_chainT_eight_nine hd W v
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  linarith

/-- **Display `eq:qld-pulling-cons` for Alice**: her exact Pauli measurement on her physical
triple is close, in summed squared state distance, to the chain's endpoint. -/
theorem sum_uniform_snorm_sq_mTildeAnc_endOp_le {hm : m ∣ Fintype.card F} {ε : ℝ}
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hd : 1 ≤ d)
    (W : Bas) (v : Anc F m) :
    (∑ u, uniform (Point F m) u * ∑ a : F, snorm M.physVec
        ((aOp (M.toFirst.mTildeAnc W v a)
          : Matrix ((((dA × Anc F m) × M.Ea) × Anc F m)
            × (((dB × Anc F m) × M.Eb) × Anc F m)) _ ℂ) - M.endOp W v a) ^ 2)
      ≤ 9 * (10 * δ + 860 * ε + 2 * Real.sqrt (172 * ε)
        + (m : ℝ) * d / Fintype.card F) := by
  refine le_trans (le_of_eq ?_)
    (M.sum_uniform_snorm_sq_chainT_le (hm := hm) hψ hfail hprojA hprojB hd W v)
  refine Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
  rw [M.chainT_zero_eq W v u a, M.chainT_nine_eq W v u a]
  rfl

end MirrorSimul

end Physical


end MIPRE.QLD
