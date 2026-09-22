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

namespace SimulPair

variable (P : SimulPair ψ MA MB δ)

/-- **Alice's swap unitary**, built from the simultaneous pair measurement along the encoding. -/
def swapA : Matrix (((dA × Anc F m) × P.EA) × Anc F m) (((dA × Anc F m) × P.EA) × Anc F m) ℂ :=
  swapU (fun p => ((P.SA.mats p).val)) cubeData

theorem swapA_mul_conjTranspose : P.swapA * P.swapAᴴ = 1 :=
  swapU_mul_conjTranspose P.SA_proj

theorem swapA_conjTranspose_mul : P.swapAᴴ * P.swapA = 1 :=
  swapU_conjTranspose_mul P.SA_proj

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
