/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.Pulling

@[expose] public section

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

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The exact half is stated over
any `⋆`-algebra `R`, as `ExactPauli.lean` and `SwapUnitary.lean` are: the pair measurement is a
projective measurement in `R`, the conjugated measurement a matrix over `R` on the register, and
`Id (x) B` is `smulKron 1 B`. The single-vector and two-party estimates are stated in a state model
and in a bipartite model. The interface half lives in the physical model `phys N K` of a pair
measurement on the first cut (`CutSimul`): the exact Pauli measurement is the first player's
`mTildePOVM`, and the strategy's own point and Pauli measurements are read there with the registers
inert (`physInert`), an embedding of `N` along which the game's consistencies transfer unchanged.
The matrix route's regrouping of the cut (`inconsistency_regroupVec`) and its reduction of the
padded state (`bornProb_padded`, `inconsistency_padded`) are those transfers
(`BipartiteModel.Embedding.inconsistency_pushforward`), and the transport of an expectation to a
nearby state is `StateModel.abs_qform_sub_qform_le` of `MIPRE/Foundations/ModelCalculus.lean`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]

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

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] {S : G × G → R}
  {cd : G → (n → F)}

/-- **Conjugation by the swap unitary strips the pair measurement off the exact Pauli
measurement.** For a family each of whose operators the ancilla factor twists by the character of
`cd (pi p)` --- the very shift the outcome of `M~^{W,u}_a` is written with --- the two cancel and
only the bare syndrome projector survives:
`V M~^{W,u}_a V^dagger = Id (x) tau^W_{[g_h(u) = a]}`. -/
theorem swapU_conj_mTilde (hS : IsPVMIn S) {pi : G × G → G}
    {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (h : ∀ (p : G × G) (b : n → F),
      uOf cd p * w b * (uOf cd p)ᴴ = sgn (trDot b (cd (pi p))) • w b)
    (u : n → F) (a : F) :
    swapU S cd * mTilde S pi cd w u a * star (swapU S cd) = smulKron 1 (syn w u a) := by
  rw [mTilde_eq_sTensor, swapU, sTensor_mul hS, sTensor_conjTranspose hS, sTensor_mul hS]
  rw [show (fun p => uOf cd p * syn w u (dotF (cd (pi p)) u + a) * (uOf cd p)ᴴ)
      = fun _ => syn w u a from funext fun p => by
    rw [conj_syn_of_sign (h p) u (dotF (cd (pi p)) u + a)]
    congr 1
    rw [add_comm (dotF (cd (pi p)) u) a, add_assoc, add_self_eq_zero', add_zero]]
  show (∑ p, smulKron (S p) (syn w u a)) = smulKron 1 (syn w u a)
  rw [← sum_kron, hS.sum_eq_one]

/-- **The `X`-side identity.** -/
theorem swapU_conj_mTilde_X (hS : IsPVMIn S) (u : n → F) (a : F) :
    swapU S cd * mTilde S Prod.fst cd wX u a * star (swapU S cd) = smulKron 1 (syn wX u a) :=
  swapU_conj_mTilde hS (fun p b => uOf_conj_wX cd p b) u a

/-- **The `Z`-side identity.** -/
theorem swapU_conj_mTilde_Z (hS : IsPVMIn S) (u : n → F) (a : F) :
    swapU S cd * mTilde S Prod.snd cd wZ u a * star (swapU S cd) = smulKron 1 (syn wZ u a) :=
  swapU_conj_mTilde hS (fun p b => by rw [uOf_conj_wZ, trDot_comm]) u a

end Measure

/-! ## Display `eq:qld-unitary-7`: the deviation of two measurements on one party

The endgame of item 2 opens by expanding the squared deviation of the conjugated Pauli measurement
from the bare ancilla family. Both act on the *same* party, so the bipartite expansion
`BipartiteModel.one_sub_sum_bornProb_eq` does not apply; the same three-term expansion does, with
the two diagonal sums exactly one because both families are projective. -/

section Deviation

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] {Λ : Type*} [Fintype Λ]
  [DecidableEq Λ]

/-- **The summed deviation of two projective measurements on one party is twice one minus their
agreement.** The cross term appears twice and the two copies are conjugate, so no real part
survives in the statement --- `qform` is already the real part, and the flipped product has the
same one. -/
theorem sum_snorm_sq_sub_eq_two_sub {M : StateModel 𝒞} (hM : ‖M.ψ‖ = 1) {A T : Λ → 𝒞}
    (hA : IsPVMIn A) (hT : IsPVMIn T) :
    ∑ h, M.snorm (A h - T h) ^ 2 = 2 - 2 * ∑ h, M.qform (A h * T h) := by
  have hterm : ∀ h : Λ, M.snorm (A h - T h) ^ 2
      = M.qform (A h) + M.qform (T h) - 2 * M.qform (A h * T h) := by
    intro h
    have hflip : M.qform (T h * A h) = M.qform (A h * T h) := by
      rw [← M.qform_star (T h * A h), star_mul, hA.star_eq, hT.star_eq]
    rw [M.snorm_sq_eq_qform, star_sub, hA.star_eq, hT.star_eq,
      show (A h - T h) * (A h - T h)
          = A h * A h + T h * T h - A h * T h - T h * A h from by noncomm_ring,
      hA.idem, hT.idem, M.qform_sub, M.qform_sub, M.qform_add, hflip]
    ring
  rw [Finset.sum_congr rfl fun h (_ : h ∈ univ) => hterm h, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← M.qform_sum, ← M.qform_sum, hA.sum_eq_one,
    hT.sum_eq_one, M.qform_one hM]
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
  {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **The off-diagonal agreement of two projective families across the parties costs `md/q`**,
when the index is encoded injectively by low-individual-degree polynomials. The weights are Born
probabilities of a pair of projective measurements, so they are nonnegative and sum to one. -/
theorem sum_uniform_agree_bornProb_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1)
    {A : Λ → 𝒜} {T : Λ → ℬ} (hA : IsPVMIn A) (hT : IsPVMIn T)
    {enc : Λ → LowIndDegPoly (F := F) (m := m) (d := d)}
    (hinj : ∀ h h' : Λ, h ≠ h' → (enc h).toMv ≠ (enc h').toMv) :
    ∑ u, uniform (Point F m) u
        * ∑ hh ∈ univ.filter fun hh : Λ × Λ => (enc hh.1).eval u = (enc hh.2).eval u,
            (if hh.1 = hh.2 then (0 : ℝ) else M.bornProb (A hh.1) (T hh.2))
      ≤ (m : ℝ) * d / Fintype.card F := by
  have hnn : ∀ hh : Λ × Λ,
      (0 : ℝ) ≤ if hh.1 = hh.2 then (0 : ℝ) else M.bornProb (A hh.1) (T hh.2) := fun hh => by
    split_ifs
    · exact le_rfl
    · exact M.bornProb_nonneg (hA.nonneg _) (hT.nonneg _)
  refine sum_uniform_agree_mass_le (p := fun hh : Λ × Λ => enc hh.1)
    (q := fun hh : Λ × Λ => enc hh.2) _
    (fun hh h0 => hinj hh.1 hh.2 fun he => h0 (ite_eq_left he)) hnn ?_
  calc ∑ hh : Λ × Λ, (if hh.1 = hh.2 then (0 : ℝ) else M.bornProb (A hh.1) (T hh.2))
      ≤ ∑ hh : Λ × Λ, M.bornProb (A hh.1) (T hh.2) :=
        Finset.sum_le_sum fun hh _ => by
          split_ifs
          · exact M.bornProb_nonneg (hA.nonneg _) (hT.nonneg _)
          · exact le_rfl
    _ = 1 := by
        rw [Fintype.sum_prod_type,
          Finset.sum_congr rfl fun h (_ : h ∈ univ) => (M.bornProb_sum_right (A h) univ T).symm,
          hT.sum_eq_one, ← M.bornProb_sum_left, hA.sum_eq_one, M.bornProb_one_one hM]

end Agree

/-! ## Display `eq:qld-unitary-5`: the triangle chain

Three consistencies chain to a fourth. The paper's `fact:triangle-for-simeq` item 1 is already in
Foundations as `BipartiteModel.agreeSum_triangle`, on the *agreement* of two families of POVMs; the
appendix's interface states everything as an *inconsistency* instead, and the two are the same
number (`sum_bornProb_diag_eq`). This is the adapter, and with it `eq:qld-unitary-5` is the
estimate applied to `eq:qld-unitary-2`, `-3` and `-4`.

The constant is the Lean one, `11 delta` where the paper has `9 delta`: the padding into a
four-dimensional auxiliary space that buys the `9` is what `agreeSum_triangle` does without, and
`delta_qld` absorbs the difference. -/

section Triangle

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {X Λ : Type*} [Fintype X] [Fintype Λ] [DecidableEq Λ]

/-- **The agreement triangle, read as inconsistencies.** `A` against `D` through `B` and `C`,
where the two middle legs share a family on each side. -/
theorem inconsistency_triangle {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1) (A C : X → POVMIn Λ 𝒜)
    (B D : X → POVMIn Λ ℬ) {δ : ℝ} (hAB : M.inconsistency μ A B ≤ δ)
    (hCB : M.inconsistency μ C B ≤ δ) (hCD : M.inconsistency μ C D ≤ δ) :
    M.inconsistency μ A D ≤ 11 * δ := by
  have hbridge : ∀ (P : X → POVMIn Λ 𝒜) (Q : X → POVMIn Λ ℬ),
      1 - M.agreeSum μ P Q = M.inconsistency μ P Q := fun P Q => by
    rw [BipartiteModel.agreeSum, sum_bornProb_diag_eq hμ1 hM P Q]
    ring
  have h := M.agreeSum_triangle (δ := δ) hμ0 hμ1 hM A C B D
    ((hbridge A B).symm ▸ hAB) ((hbridge C B).symm ▸ hCB) ((hbridge C D).symm ▸ hCD)
  rwa [hbridge] at h

end Triangle

/-! ## The same, on the interface of `lem:qld-simultaneous`

The swap unitary of the appendix is built from the simultaneous pair measurement, so at the
interface it is `swapU` of `SA` along `cubeData`, and the identity above applies at both bases at
once: `PolyPair.proj .X` is the first projection and `weylOf .X` is `wX`, and likewise for `Z`, so
the two instances are the two cases of `Bas`. -/

section Interface

open MIPRE.LIDT MIPRE.LowDegree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **The `(Pauli, W)` measurement, read at a point.** The paper's
`M^{(Pauli,W)}_{[g_h(u) = a]}`: the strategy's Pauli measurement coarse-grained by the value at
`u` of the low-degree encoding of the answer it returns. -/
def pauliAtPOVM {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (P : Question F m → POVMIn (Answer F m d) R) (W : Bas) (u : Point F m) : POVMIn F R :=
  (P (.pauli W)).map (rdPauli u)

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-! ## The two middle legs, from the game

`eq:qld-unitary-5`'s two middle legs are `lem:qld-win`'s items 1 and 3, which the game supplies as
*cross-party deviations* averaged over the verifier's content. Three steps turn each into the
inconsistency the triangle wants: the point question a content asks is the point the content
carries, so the average over contents of a function of that point is the uniform average over
points (`sum_content_pt`); and for projective families the deviation is exactly twice the
inconsistency. Nothing here is an estimate --- the estimate is `agree_subtest_le`, and it is
already in. -/

section GameLegs

variable {ε : ℝ}

/-- **A cross-party deviation is exactly twice the inconsistency**, for projective families on a
unit state. Only `≤` holds for POVMs (`BipartiteModel.xSqNorm_sum_le_two_mul`); what makes it an
equality here is that both families' masses are exactly one. -/
theorem inconsistency_eq_half_xPovmDist {X Λ : Type*} [Fintype X] [Fintype Λ] [DecidableEq Λ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} (μ : X → ℝ) (hM : ‖M.ψ‖ = 1) (P : X → POVMIn Λ 𝒜)
    (Q : X → POVMIn Λ ℬ) (hP : ∀ x, IsPVMIn (P x).op) (hQ : ∀ x, IsPVMIn (Q x).op) :
    M.inconsistency μ P Q = M.xPovmDist μ P Q / 2 := by
  rw [show M.inconsistency μ P Q = ∑ x, μ x * pairInconsistency M (P x) (Q x) from rfl,
    BipartiteModel.xPovmDist, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 := sum_diag_eq_one_sub hM (P x) (Q x)
  have h2 := M.one_sub_sum_bornProb_eq hM (hP x) (hQ x)
  rw [mul_div_assoc]
  congr 1
  linarith

/-- **The game's point--point consistency**, as an inconsistency over uniform points: item 1 of
`lem:qld-win` at the type `(Point, W)`, read through the answer's field element. -/
theorem inconsistency_pt_pt_le {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) (W : Bas) :
    M.inconsistency (uniform (Point F m)) (fun u => ptAtPOVM PA W u)
        (fun u => ptAtPOVM PB W u) ≤ 86 * ε := by
  have hP : ∀ u : Point F m, IsPVMIn (ptAtPOVM PA W u).op :=
    fun u => POVMIn.isPVMIn_map (hPA _) _
  have hQ : ∀ u : Point F m, IsPVMIn (ptAtPOVM PB W u).op :=
    fun u => POVMIn.isPVMIn_map (hPB _) _
  rw [inconsistency_eq_half_xPovmDist (uniform (Point F m)) hM _ _ hP hQ,
    BipartiteModel.xPovmDist,
    ← sum_content_pt W fun u => ∑ o : F, M.xSqNorm ((ptAtPOVM PA W u).op o)
      ((ptAtPOVM PB W u).op o)]
  have h := item_consistency (hm := hm) hM hfail (.point W) (φ := rdVal)
  rw [BipartiteModel.xPovmDist] at h
  simp only [show ∀ c : Content F m, (PA (Content.question hm c (Ty.point W))).map rdVal
      = ptAtPOVM PA W (c.pt W) from fun _ => rfl,
    show ∀ c : Content F m, (PB (Content.question hm c (Ty.point W))).map rdVal
      = ptAtPOVM PB W (c.pt W) from fun _ => rfl] at h
  linarith

/-- **The game's point--Pauli consistency**, likewise: item 3 of `lem:qld-win`, the low-degree
encoding of the Pauli answer evaluated at the sampled point against the point answer. -/
theorem inconsistency_pt_pauli_le {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
    {PA : Question F m → POVMIn (Answer F m d) 𝒜} {PB : Question F m → POVMIn (Answer F m d) ℬ}
    (hM : ‖M.ψ‖ = 1) (hfail : 1 - M.povmValue (qldGame hm) PA PB ≤ ε)
    (hPA : ∀ q, IsPVMIn (PA q).op) (hPB : ∀ q, IsPVMIn (PB q).op) (W : Bas) :
    M.inconsistency (uniform (Point F m)) (fun u => ptAtPOVM PA W u)
        (fun u => pauliAtPOVM PB W u) ≤ 86 * ε := by
  have hP : ∀ u : Point F m, IsPVMIn (ptAtPOVM PA W u).op :=
    fun u => POVMIn.isPVMIn_map (hPA _) _
  have hQ : ∀ u : Point F m, IsPVMIn (pauliAtPOVM PB W u).op :=
    fun u => POVMIn.isPVMIn_map (hPB _) _
  rw [inconsistency_eq_half_xPovmDist (uniform (Point F m)) hM _ _ hP hQ,
    BipartiteModel.xPovmDist,
    ← sum_content_pt W fun u => ∑ o : F, M.xSqNorm ((ptAtPOVM PA W u).op o)
      ((pauliAtPOVM PB W u).op o)]
  have h := item_pauli_consistency (hm := hm) hM hfail W
  simp only [show ∀ c : Content F m, (PA (Content.question hm c (Ty.point W))).map rdVal
      = ptAtPOVM PA W (c.pt W) from fun _ => rfl,
    show ∀ c : Content F m, (PB (Content.question hm c (Ty.pauli W))).map (rdPauli (c.pt W))
      = pauliAtPOVM PB W (c.pt W) from fun _ => rfl] at h
  linarith

end GameLegs

variable [StarModule ℂ 𝒜] [StarProper 𝒜] [StarModule ℂ ℬ] [StarProper ℬ]

namespace SimulPair

section Generic

variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ']
variable {hm : m ∣ Fintype.card F} {M : BipartiteModel 𝒞 𝒜 ℬ}
  {S : M.ProjStrat (qldGame (d := d) hm)} {K : BipartiteModel 𝒞' 𝒜' ℬ'}
  {ι : (M.reg (Anc F m)).Embedding K} {δ : ℝ}

variable (P : SimulPair M S K ι δ)

/-- **Alice's swap unitary**, built from the simultaneous pair measurement along the encoding: a
matrix over `K`'s first algebra on the register. -/
def swapA : Matrix (Anc F m) (Anc F m) 𝒜' :=
  swapU P.SA.op cubeData

theorem swapA_mul_conjTranspose [StarModule ℂ 𝒜'] : P.swapA * star P.swapA = 1 :=
  swapU_mul_conjTranspose P.SA_proj

theorem swapA_conjTranspose_mul [StarModule ℂ 𝒜'] : star P.swapA * P.swapA = 1 :=
  swapU_conjTranspose_mul P.SA_proj

/-- **Display `eq:qld-unitary-6` at the interface.** -/
theorem swapU_conj_mTildeAt [StarModule ℂ 𝒜'] (W : Bas) (u : Point F m) (a : F) :
    P.swapA * P.mTildeAt W u a * star P.swapA = smulKron 1 (syn (weylOf W) (indVec u) a) := by
  rw [SimulPair.swapA, SimulPair.mTildeAt]
  cases W with
  | X => exact swapU_conj_mTilde_X P.SA_proj (indVec u) a
  | Z => exact swapU_conj_mTilde_Z P.SA_proj (indVec u) a

end Generic

/-! ### On the physical model

The three legs of `eq:qld-unitary-5` are read on the physical state: the exact Pauli measurement is
an operator of the physical model's first player (`mTildePOVM`), and the strategy's own point and
Pauli measurements are read there with the registers inert (`physInert`). The game's consistencies
are statements about the strategy's measurements on the model's own state, and the embedding
carries them to the physical state unchanged. -/

section Physical

variable {hm : m ∣ Fintype.card F} {N : BipartiteModel 𝒞 𝒜 ℬ}
  {S : N.ProjStrat (qldGame (d := d) hm)} {K : ℕ} {δ : ℝ}

/-- **Display `eq:qld-unitary-5` at the interface.** The exact Pauli measurement agrees with the
strategy's `(Pauli, W)` measurement, read at the sampled point, to within eleven times whatever
bounds the three legs. Its own leg is item 1 of Lemma `lem:qld-exact-paulis`
(\texttt{inconsistency\_mTilde\_le}); the two middle legs are the game's own consistencies ---
point against point and point against Pauli --- and are hypotheses here, stated on the physical
state with the strategy's measurements read along \texttt{physInert}. -/
theorem inconsistency_mTilde_pauli_le (P : CutSimul N S K δ) (W : Bas) {δ' : ℝ}
    (hpt : (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => (ptAtPOVM S.PA W u).pushforward (physInert (Anc F m) F m d N K).ΦA
          (physInert (Anc F m) F m d N K).ΦA_one)
        (fun u => (ptAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one) ≤ δ')
    (hpauli : (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => (ptAtPOVM S.PA W u).pushforward (physInert (Anc F m) F m d N K).ΦA
          (physInert (Anc F m) F m d N K).ΦA_one)
        (fun u => (pauliAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one) ≤ δ')
    (hmt : (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => P.mTildePOVM W u)
        (fun u => (ptAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one) ≤ δ') :
    (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => P.mTildePOVM W u)
        (fun u => (pauliAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one)
      ≤ 11 * δ' :=
  inconsistency_triangle (uniform_nonneg (Point F m)) (sum_uniform_eq_one (Point F m))
    P.mVec_unit _ (fun u => (ptAtPOVM S.PA W u).pushforward (physInert (Anc F m) F m d N K).ΦA
      (physInert (Anc F m) F m d N K).ΦA_one) _ _ hmt hpt hpauli

/-- **Display `eq:qld-unitary-5`, with its two middle legs read on the strategy's own state.**
This is the form the game supplies them in: `agree_subtest_le` bounds a cross-party deviation of
the strategy's measurements on the model's state, and nothing there knows about the registers. -/
theorem inconsistency_mTilde_pauli_le' (P : CutSimul N S K δ) (W : Bas) {δ' : ℝ}
    (hpt : N.inconsistency (uniform (Point F m)) (fun u => ptAtPOVM S.PA W u)
      (fun u => ptAtPOVM S.PB W u) ≤ δ')
    (hpauli : N.inconsistency (uniform (Point F m)) (fun u => ptAtPOVM S.PA W u)
      (fun u => pauliAtPOVM S.PB W u) ≤ δ')
    (hmt : (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => P.mTildePOVM W u)
        (fun u => (ptAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one) ≤ δ') :
    (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => P.mTildePOVM W u)
        (fun u => (pauliAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one)
      ≤ 11 * δ' :=
  P.inconsistency_mTilde_pauli_le W
    (by rw [(physInert (Anc F m) F m d N K).inconsistency_pushforward]; exact hpt)
    (by rw [(physInert (Anc F m) F m d N K).inconsistency_pushforward]; exact hpauli) hmt

/-- **Display `eq:qld-unitary-5`, from the game's soundness and item 1 of
`lem:qld-exact-paulis` alone.** The two middle legs are now discharged: they are items 1 and 3 of
`lem:qld-win` at the point and Pauli types, and `86 = 172/2` is `agree_subtest_le`'s constant
halved by the passage from a cross-party deviation to an inconsistency. -/
theorem inconsistency_mTilde_pauli_le_of_win (P : CutSimul N S K δ) {ε δ' : ℝ}
    (hfail : 1 - S.value ≤ ε) (W : Bas) (hε : 86 * ε ≤ δ')
    (hmt : (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => P.mTildePOVM W u)
        (fun u => (ptAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one) ≤ δ') :
    (phys (Anc F m) F m d N K).inconsistency (uniform (Point F m))
        (fun u => P.mTildePOVM W u)
        (fun u => (pauliAtPOVM S.PB W u).pushforward (physInert (Anc F m) F m d N K).ΦB
          (physInert (Anc F m) F m d N K).ΦB_one)
      ≤ 11 * δ' :=
  P.inconsistency_mTilde_pauli_le' W
    (le_trans (inconsistency_pt_pt_le S.ψ_unit hfail S.projA S.projB W) hε)
    (le_trans (inconsistency_pt_pauli_le S.ψ_unit hfail S.projA S.projB W) hε) hmt

end Physical

end SimulPair

end Interface

end MIPRE.QLD

end

end
