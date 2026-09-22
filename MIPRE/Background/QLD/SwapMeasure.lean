/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.Pulling

/-!
# Conjugating the exact Pauli *measurement* by the swap unitary

`MIPRE/Background/QLD/SwapUnitary.lean` conjugates the exact Pauli *observable*: the two signs
cancel and `V W~^e(u) V^dagger = Id (x) tau^W(e . u)`, exactly. Item 2 of `lem:qld-swap` needs the
same statement one level down, on the measurement the observable is read off --- the appendix's
display `eq:qld-unitary-6`,

`V M~^{W,u}_a V^dagger = Id (x) tau^W_{[g_h(u) = a]}` ,

again exactly. This file is that identity.

## What conjugation does to a spectral projector

The observable's proof only needed the twisted commutation relation, which says conjugation by the
ancilla factor multiplies each Weyl operator by a character. On the *projectors* that becomes a
shift: a spectral projector is the Fourier average of the family against a character
(`proj_def`), two characters multiply by adding their labels, and so conjugation moves the
eigenvalue pattern by the label of the twist (`conj_proj_of_sign`). A syndrome projector is the
sum of the spectral projectors over a level set of the pairing with the probe, so its outcome
moves by the shift's own pairing with the probe (`conj_syn_of_sign`).

In `M~^{W,u}_a` the outcome carried at the pair outcome `p` is `cd(pi p) . u + a`, and the shift
conjugation applies there is `cd(pi p)`, whose pairing with `u` is that same `cd(pi p) . u`. The
two cancel --- in characteristic two, `x + a + x = a` --- so every factor of the conjugated sum is
the *same* syndrome projector `tau^W_{[g_h(u)=a]}`, with the pair outcome gone from it, and the
measurement in front sums to the identity.

That cancellation is the paper's relabelling `h' = h + coded(g_W)`, the passage its `\cnote`
records as repaired: the repair was to keep `coded(g_W) . ind_m(u)` rather than the false
`g_W(u)` throughout, and what makes the relabelling exact here is that the shift and the outcome
are written with the same `cd(pi p) . u` by construction.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

set_option linter.unusedSectionVars false

/-! ## A twist of the family is a shift of its projectors -/

section Conj

variable {w : (n → F) → Matrix (n → F) (n → F) ℂ} {U : Matrix (n → F) (n → F) ℂ} {s : n → F}

/-- **Conjugation that twists a Weyl family by a character shifts its spectral projectors.** The
projector at the pattern `e` is the Fourier average against the character of `e`; conjugating
multiplies the term at `a` by the character of `s`, and the two characters compose by adding their
labels. -/
theorem conj_proj_of_sign (h : ∀ a, U * w a * Uᴴ = sgn (trDot a s) • w a) (e : n → F) :
    U * proj w e * Uᴴ = proj w (e + s) := by
  rw [proj_def, proj_def, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, h a, smul_smul, ← sgn_add, ← trDot_add_right]

/-- **...and shifts a syndrome projector's outcome by the shift's own pairing with the probe.**
The level set of the pairing at `a` is carried onto the level set at `a + s . v` by adding `s`,
which is an involution of the index group in characteristic two. -/
theorem conj_syn_of_sign (h : ∀ a, U * w a * Uᴴ = sgn (trDot a s) • w a) (v : n → F) (a : F) :
    U * syn w v a * Uᴴ = syn w v (a + dotF s v) := by
  classical
  have hadd : ∀ e : n → F, dotF (e + s) v = dotF e v + dotF s v := fun e => by
    rw [dotF_comm, dotF_add_right, dotF_comm v e, dotF_comm v s]
  rw [syn, syn, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl fun e (_ : e ∈ univ.filter fun e => dotF e v = a) =>
      conj_proj_of_sign h e]
  refine Finset.sum_equiv (Equiv.addRight s) (fun e => ?_) (fun e _ => rfl)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight, hadd]
  exact ⟨fun he => by rw [he], fun he => add_right_cancel he⟩

end Conj

/-! ## Display `eq:qld-unitary-6` -/

section Measure

variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}

/-- **Conjugation by the swap unitary strips the pair measurement off the exact Pauli
measurement.** For a family each of whose operators the ancilla factor twists by the character of
`cd (pi p)` --- the very shift the outcome of `M~^{W,u}_a` is written with --- the two cancel and
only the bare syndrome projector survives:
`V M~^{W,u}_a V^dagger = Id (x) tau^W_{[g_h(u) = a]}`. -/
theorem swapU_conj_mTilde (hS : IsPVM S) {pi : G × G → G}
    {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (h : ∀ (p : G × G) (b : n → F),
      uOf cd p * w b * (uOf cd p)ᴴ = sgn (trDot b (cd (pi p))) • w b)
    (u : n → F) (a : F) :
    swapU S cd * mTilde S pi cd w u a * (swapU S cd)ᴴ = 1 ⊗ₖ syn w u a := by
  rw [mTilde_eq_sTensor, swapU, sTensor_mul hS, sTensor_conjTranspose hS, sTensor_mul hS]
  rw [show (fun p => uOf cd p * syn w u (dotF (cd (pi p)) u + a) * (uOf cd p)ᴴ)
      = fun _ => syn w u a from funext fun p => by
    rw [conj_syn_of_sign (h p) u (dotF (cd (pi p)) u + a)]
    congr 1
    rw [add_comm (dotF (cd (pi p)) u) a, add_assoc, add_self_eq_zero', add_zero]]
  show (∑ p, S p ⊗ₖ syn w u a) = 1 ⊗ₖ syn w u a
  rw [← sum_kron, hS.sum_eq_one]

/-- **The `X`-side identity.** -/
theorem swapU_conj_mTilde_X (hS : IsPVM S) (u : n → F) (a : F) :
    swapU S cd * mTilde S Prod.fst cd wX u a * (swapU S cd)ᴴ = 1 ⊗ₖ syn wX u a :=
  swapU_conj_mTilde hS (fun p b => uOf_conj_wX cd p b) u a

/-- **The `Z`-side identity.** -/
theorem swapU_conj_mTilde_Z (hS : IsPVM S) (u : n → F) (a : F) :
    swapU S cd * mTilde S Prod.snd cd wZ u a * (swapU S cd)ᴴ = 1 ⊗ₖ syn wZ u a :=
  swapU_conj_mTilde hS (fun p b => by rw [uOf_conj_wZ, trDot_comm]) u a

end Measure

/-! ## Display `eq:qld-unitary-7`: the deviation of two measurements on one party

The endgame of item 2 opens by expanding the squared deviation of the conjugated Pauli measurement
from the bare ancilla family. Both act on the *same* party, so the bipartite expansion
`one_sub_sum_bornProb_eq` does not apply; the same three-term expansion does, with the two
diagonal sums exactly one because both families are projective. -/

section Deviation

variable {N : Type*} [Fintype N] [DecidableEq N] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The summed deviation of two projective measurements on one party is twice one minus their
agreement.** The cross term appears twice and the two copies are conjugate, so no real part
survives in the statement --- `qform` is already the real part, and the flipped product has the
same one. -/
theorem sum_snorm_sq_sub_eq_two_sub {v : N → ℂ} (hv : ‖evec v‖ = 1) {A T : Λ → Matrix N N ℂ}
    (hA : IsPVM A) (hT : IsPVM T) :
    ∑ h, snorm v (A h - T h) ^ 2 = 2 - 2 * ∑ h, qform v (A h * T h) := by
  have hterm : ∀ h : Λ, snorm v (A h - T h) ^ 2
      = qform v (A h) + qform v (T h) - 2 * qform v (A h * T h) := by
    intro h
    have hflip : qform v (T h * A h) = qform v (A h * T h) := by
      rw [← qform_conjTranspose v (T h * A h), Matrix.conjTranspose_mul, hA.isSelfAdjoint,
        hT.isSelfAdjoint]
    rw [snorm_sq_eq_qform, Matrix.conjTranspose_sub, hA.isSelfAdjoint, hT.isSelfAdjoint,
      show (A h - T h) * (A h - T h)
          = A h * A h + T h * T h - A h * T h - T h * A h from by noncomm_ring,
      hA.idem, hT.idem, qform_sub, qform_sub, qform_add, hflip]
    ring
  rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) => hterm h, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← qform_sum, ← qform_sum, hA.sum_eq_one,
    hT.sum_eq_one, qform_one v hv]
  ring

end Deviation

/-! ## Display `eq:qld-unitary-8`: the off-diagonal agreement

The endgame's one estimate is Schwartz--Zippel, in the same packaging as `eq:qld-pulling-12`: a
sum weighted by Born probabilities, restricted to the pairs whose two encoded polynomials agree at
the sampled point. Here the index is a *pair* of Pauli outcomes and the diagonal is excluded by
the weight rather than by the index set, which is why `sum_uniform_agree_mass_le` asks for the
polynomials to be distinct only where the weight is nonzero. -/

section Agree

open MIPRE.LIDT MIPRE.LowDegree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The off-diagonal agreement of two projective families across the parties costs `md/q`**,
when the index is encoded injectively by low-individual-degree polynomials. The weights are Born
probabilities of a pair of projective measurements, so they are nonnegative and sum to one. -/
theorem sum_uniform_agree_bornProb_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {A : Λ → Matrix dA dA ℂ} {T : Λ → Matrix dB dB ℂ} (hA : IsPVM A) (hT : IsPVM T)
    {enc : Λ → LowIndDegPoly (F := F) (m := m) (d := d)}
    (hinj : ∀ h h' : Λ, h ≠ h' → (enc h).toMv ≠ (enc h').toMv) :
    ∑ u, uniform (Point F m) u
        * ∑ hh ∈ univ.filter fun hh : Λ × Λ => (enc hh.1).eval u = (enc hh.2).eval u,
            (if hh.1 = hh.2 then (0 : ℝ) else bornProb ψ (A hh.1) (T hh.2))
      ≤ (m : ℝ) * d / Fintype.card F := by
  classical
  have hnn : ∀ hh : Λ × Λ,
      (0 : ℝ) ≤ if hh.1 = hh.2 then (0 : ℝ) else bornProb ψ (A hh.1) (T hh.2) := fun hh => by
    split_ifs
    · exact le_rfl
    · exact bornProb_nonneg ψ (hA.posSemidef _) (hT.posSemidef _)
  refine sum_uniform_agree_mass_le (p := fun hh : Λ × Λ => enc hh.1)
    (q := fun hh : Λ × Λ => enc hh.2) _
    (fun hh h0 => hinj hh.1 hh.2 fun he => h0 (if_pos he)) hnn ?_
  calc ∑ hh : Λ × Λ, (if hh.1 = hh.2 then (0 : ℝ) else bornProb ψ (A hh.1) (T hh.2))
      ≤ ∑ hh : Λ × Λ, bornProb ψ (A hh.1) (T hh.2) :=
        Finset.sum_le_sum fun hh _ => by
          split_ifs
          · exact bornProb_nonneg ψ (hA.posSemidef _) (hT.posSemidef _)
          · exact le_rfl
    _ = 1 := by
        rw [Fintype.sum_prod_type,
          Finset.sum_congr rfl fun h (_ : h ∈ univ) =>
            (bornProb_sum_right ψ univ (A h) T).symm,
          hT.sum_eq_one, ← bornProb_sum_left, hA.sum_eq_one, bornProb_one_one hψ]

end Agree

/-! ## Display `eq:qld-unitary-5`: the triangle chain

Three consistencies chain to a fourth. The paper's `fact:triangle-for-simeq` item 1 is already in
Foundations as `agreeSum_triangle`, on the *agreement* of two POVM families; the appendix's
interface states everything as an *inconsistency* instead, and the two are the same number
(`sum_bornProb_diag_eq`). This is the adapter, and with it `eq:qld-unitary-5` is the estimate
applied to `eq:qld-unitary-2`, `-3` and `-4`.

The constant is the Lean one, `11 delta` where the paper has `9 delta`: the padding into a
four-dimensional auxiliary space that buys the `9` is what `agreeSum_triangle` does without, and
`delta_qld` absorbs the difference. -/

section Triangle

variable {X Λ : Type*} [Fintype X] [Fintype Λ] [DecidableEq Λ]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The agreement triangle, read as inconsistencies.** `A` against `D` through `B` and `C`,
where the two middle legs share a family on each side. -/
theorem inconsistency_triangle {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (A C : X → POVM Λ dA) (B D : X → POVM Λ dB)
    {δ : ℝ} (hAB : inconsistency μ ψ A B ≤ δ) (hCB : inconsistency μ ψ C B ≤ δ)
    (hCD : inconsistency μ ψ C D ≤ δ) :
    inconsistency μ ψ A D ≤ 11 * δ := by
  have hbridge : ∀ (M : X → POVM Λ dA) (N : X → POVM Λ dB),
      1 - agreeSum μ ψ M N = inconsistency μ ψ M N := fun M N => by
    rw [agreeSum, sum_bornProb_diag_eq hμ1 hψ M N]
    ring
  have h := agreeSum_triangle (δ := δ) hμ0 hμ1 hψ A C B D
    ((hbridge A B).symm ▸ hAB) ((hbridge C B).symm ▸ hCB) ((hbridge C D).symm ▸ hCD)
  rwa [hbridge] at h

end Triangle

/-! ## Moving an expectation to a nearby state

The endgame of item 2 computes against the product state `|aux> (x) |EPR>^M` and then transports
the answer back to the padded state, across item 1's bound on the distance between them. Item 1
bounds the *squared* norm, so the transport costs a square root of it --- which is where the
fourth root in `delta_qld` comes from. -/

section StateMove

variable {N : Type*} [Fintype N]

/-- **Moving a quadratic form to a nearby state costs twice the bound times the distance.** The
difference splits into two terms, each with the deviation on one side, and each is bounded by
Cauchy--Schwarz against a state of norm at most one. -/
theorem abs_qform_sub_qform_le (v w : N → ℂ) {X : Matrix N N ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hX : Bnd X K) (hv : ‖evec v‖ ≤ 1) (hw : ‖evec w‖ ≤ 1) :
    |qform v X - qform w X| ≤ 2 * K * ‖evec (v - w)‖ := by
  have hsplit : star v ⬝ᵥ (X *ᵥ v) - star w ⬝ᵥ (X *ᵥ w)
      = star (v - w) ⬝ᵥ (X *ᵥ v) + star w ⬝ᵥ (X *ᵥ (v - w)) := by
    rw [Matrix.mulVec_sub, star_sub, sub_dotProduct, dotProduct_sub]
    ring
  have h1 : ‖star (v - w) ⬝ᵥ (X *ᵥ v)‖ ≤ K * ‖evec (v - w)‖ := by
    rw [← inner_evec]
    refine le_trans (norm_inner_le_norm _ _) ?_
    calc ‖evec (v - w)‖ * ‖evec (X *ᵥ v)‖ ≤ ‖evec (v - w)‖ * (K * ‖evec v‖) :=
          mul_le_mul_of_nonneg_left (hX v) (norm_nonneg _)
      _ ≤ ‖evec (v - w)‖ * (K * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hK) (norm_nonneg _)
      _ = K * ‖evec (v - w)‖ := by ring
  have h2 : ‖star w ⬝ᵥ (X *ᵥ (v - w))‖ ≤ K * ‖evec (v - w)‖ := by
    rw [← inner_evec]
    refine le_trans (norm_inner_le_norm _ _) ?_
    calc ‖evec w‖ * ‖evec (X *ᵥ (v - w))‖ ≤ 1 * ‖evec (X *ᵥ (v - w))‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ ≤ K * ‖evec (v - w)‖ := by rw [one_mul]; exact hX (v - w)
  have hre : qform v X - qform w X = (star v ⬝ᵥ (X *ᵥ v) - star w ⬝ᵥ (X *ᵥ w)).re := by
    rw [qform, qform, Complex.sub_re]
  rw [hre, hsplit]
  refine le_trans (Complex.abs_re_le_norm _) (le_trans (norm_add_le _ _) ?_)
  linarith

end StateMove

/-! ## Carrying a consistency across the regrouped cut

The three legs of `eq:qld-unitary-5` are not read along the same cut. `M~^{W,u}` needs the ancilla
half with the first party, which is the regrouped cut `mVec`; the strategy's own point and Pauli
measurements are local to the unpadded registers and are stated along the padded state's own cut.
For operators that ignore the register the regrouping moves --- which the strategy's measurements
do, being extended by the identity there --- the two readings are the same number, since the
regrouping is a reindexing of the whole space and the moved factor carries the identity. -/

section Transport

variable {R S T E X Λ : Type*} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E] [Fintype X] [Fintype Λ] [DecidableEq Λ]

/-- **A consistency between operators that ignore the moved register reads the same on both
cuts.** -/
theorem inconsistency_regroupVec (μ : X → ℝ) (ψ : R × ((S × T) × E) → ℂ)
    (A : X → POVM Λ R) (B : X → POVM Λ S) :
    inconsistency μ (regroupVec ψ) (fun x => (A x).aOp (E := T)) (fun x => (B x).aOp (E := E))
      = inconsistency μ ψ A fun x => ((B x).aOp (E := T)).aOp (E := E) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rfl
  · show bornProb (regroupVec ψ) _ _ = bornProb ψ _ _
    rw [POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats]
    exact bornProb_regroupVec ψ ((A x).mats a).val ((B x).mats b).val 1

end Transport

/-! ## The same, on the interface of `lem:qld-simultaneous`

The swap unitary of the appendix is built from the simultaneous pair measurement, so at the
interface it is `swapU` of `SA` along `cubeData`, and the identity above applies at both bases at
once: `PolyPair.proj .X` is the first projection and `weylOf .X` is `wX`, and likewise for `Z`, so
the two instances are the two cases of `Bas`. -/

section Interface

open MIPRE.LIDT MIPRE.LowDegree

set_option synthInstance.maxSize 1000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {δ : ℝ}

/-- **The `(Pauli, W)` measurement, read at a point.** The paper's
`M^{(Pauli,W)}_{[g_h(u) = a]}`: the strategy's Pauli measurement coarse-grained by the value at
`u` of the low-degree encoding of the answer it returns. -/
def pauliAtPOVM {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) : POVM F d' :=
  (M (.pauli W)).map (rdPauli u)

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **Alice's swap unitary**, built from the simultaneous pair measurement along the encoding. -/
def swapA : Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  swapU (fun p => ((P.SA.mats p).val)) cubeData

theorem swapA_mul_conjTranspose : P.swapA * P.swapAᴴ = 1 :=
  swapU_mul_conjTranspose P.SA_proj

theorem swapA_conjTranspose_mul : P.swapAᴴ * P.swapA = 1 :=
  swapU_conjTranspose_mul P.SA_proj

/-- **A Born probability of the strategy's own measurements reads the same on the padded state.**
Both operators are extended by the identity on the expansion's ancillas and on the padding, so the
padded state's reduction carries them to the expanded state and the expanded state's factorization
carries them down to the original one, the entangled pair contributing its own norm and nothing
else. -/
theorem bornProb_padded (X : Matrix dA dA ℂ) (Y : Matrix dB dB ℂ) :
    bornProb P.Φ (aOp (aOp X)) (aOp (aOp Y)) = bornProb ψ X Y := by
  rw [P.Φ_reduced (aOp X) (aOp Y)]
  show bornProb (expVec ψ (epr (F := F) (n := Fin m → Bool))) (X ⊗ₖ 1) (Y ⊗ₖ 1) = _
  rw [bornProb_expVec_kron ψ _ Matrix.PosSemidef.one Matrix.PosSemidef.one,
    bornProb_one_one epr_unit, mul_one]

/-- **And so does a consistency between them.** This is what puts the game's own consistencies ---
which are statements about the strategy's measurements on the original state --- into the
vocabulary the appendix's interface reads them in. -/
theorem inconsistency_padded {Y Λ : Type*} [Fintype Y] [Fintype Λ] [DecidableEq Λ] (μ : Y → ℝ)
    (M : Y → POVM Λ dA) (N : Y → POVM Λ dB) :
    inconsistency μ P.Φ (fun y => ((M y).aOp (E := Anc F m)).aOp (E := P.EA))
        (fun y => ((N y).aOp (E := Anc F m)).aOp (E := P.EB))
      = inconsistency μ ψ M N := by
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rfl
  · show bornProb P.Φ _ _ = bornProb ψ _ _
    rw [POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats, POVM.aOp_mats]
    exact P.bornProb_padded ((M y).mats a).val ((N y).mats b).val

/-- **Display `eq:qld-unitary-5` at the interface.** The exact Pauli measurement agrees with the
strategy's `(Pauli, W)` measurement, read at the sampled point, to within eleven times whatever
bounds the three legs. Its own leg is item 1 of Lemma `lem:qld-exact-paulis`
(\texttt{inconsistency\_mTilde\_le}); the two middle legs are the game's own consistencies ---
point against point and point against Pauli --- and are hypotheses here, stated along the padded
state's own cut and carried across by \texttt{inconsistency\_regroupVec}. -/
theorem inconsistency_mTilde_pauli_le (W : Bas) {δ' : ℝ}
    (hpt : inconsistency (uniform (Point F m)) P.Φ
        (fun u => ((ptAtPOVM MA W u).aOp (E := Anc F m)).aOp (E := P.EA))
        (fun u => ((ptAtPOVM MB W u).aOp (E := Anc F m)).aOp (E := P.EB)) ≤ δ')
    (hpauli : inconsistency (uniform (Point F m)) P.Φ
        (fun u => ((ptAtPOVM MA W u).aOp (E := Anc F m)).aOp (E := P.EA))
        (fun u => ((pauliAtPOVM MB W u).aOp (E := Anc F m)).aOp (E := P.EB)) ≤ δ')
    (hmt : inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (ptAtPOVM MB W u).aOp) ≤ δ') :
    inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (pauliAtPOVM MB W u).aOp)
      ≤ 11 * δ' := by
  refine inconsistency_triangle (uniform_nonneg (Point F m)) (sum_uniform_eq_one (Point F m))
    P.mVec_unit _ (fun u => (((ptAtPOVM MA W u).aOp (E := Anc F m)).aOp (E := P.EA)).aOp
      (E := Anc F m)) _ _ hmt ?_ ?_
  · rw [SimulPair.mVec, inconsistency_regroupVec]
    exact hpt
  · rw [SimulPair.mVec, inconsistency_regroupVec]
    exact hpauli

/-- **Display `eq:qld-unitary-5`, with its two middle legs read on the strategy's own state.**
This is the form the game supplies them in: `agree_subtest_le` bounds a cross-party deviation of
the strategy's measurements on `psi`, and nothing there knows about the expansion or the padding.
-/
theorem inconsistency_mTilde_pauli_le' (W : Bas) {δ' : ℝ}
    (hpt : inconsistency (uniform (Point F m)) ψ (fun u => ptAtPOVM MA W u)
      (fun u => ptAtPOVM MB W u) ≤ δ')
    (hpauli : inconsistency (uniform (Point F m)) ψ (fun u => ptAtPOVM MA W u)
      (fun u => pauliAtPOVM MB W u) ≤ δ')
    (hmt : inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (ptAtPOVM MB W u).aOp) ≤ δ') :
    inconsistency (uniform (Point F m)) P.mVec
        (fun u => (P.isPVM_mTildeAt W u).toPOVM) (fun u => (pauliAtPOVM MB W u).aOp)
      ≤ 11 * δ' :=
  P.inconsistency_mTilde_pauli_le W (by rw [P.inconsistency_padded]; exact hpt)
    (by rw [P.inconsistency_padded]; exact hpauli) hmt

/-- **Display `eq:qld-unitary-6` at the interface.** -/
theorem swapU_conj_mTildeAt (W : Bas) (u : Point F m) (a : F) :
    P.swapA * P.mTildeAt W u a * P.swapAᴴ = 1 ⊗ₖ syn (weylOf W) (indVec u) a := by
  rw [SimulPair.swapA, SimulPair.mTildeAt]
  cases W with
  | X => exact swapU_conj_mTilde_X P.SA_proj (indVec u) a
  | Z => exact swapU_conj_mTilde_Z P.SA_proj (indVec u) a

end SimulPair

end Interface

end MIPRE.QLD

end
