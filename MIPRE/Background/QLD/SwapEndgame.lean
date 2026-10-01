/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.QLD.SwapMeasure
public import MIPRE.Background.QLD.SwapState

@[expose] public section

/-!
# The endgame of `lem:qld-swap` item 2

Item 1 produces a product state `|aux> (x) |EPR_q>^M` close to the conjugated padded state
(`exists_auxVec_close`). Item 2's endgame computes against that product state and transports the
answer back. This file is the part of that computation that is about the product state itself.

## What an operator on the ancilla pair does to a product state

`auxVec aux` is a product: one factor is the maximally entangled pair, the other is arbitrary. So
an operator acting on the pair alone acts on the pair's factor and leaves the other, and two
operators that agree on `|EPR_q>` agree on the whole product. That is the last line of display
`eq:qld-unitary-7`, where a generalized Pauli's spectral projector is moved from one half of the
pair to the other: the projectors are symmetric matrices, so `stateVec_epr_proj` moves them across
the pair, and `mulVec_auxVec_congr` carries that to the product state.

## Stated in a bipartite model

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`). The product state is
`auxVec aux`, a vector of the `ℓ²` sum `Ampl (T x T) H` for a vector `aux` of an arbitrary complex
Hilbert space `H`, and a matrix of scalars on the pair acts on it as `regAct`
(`MIPRE/Foundations/EPRContraction.lean`); in a register model, whose state is such a product, the
transport across the pair is the mirror identity `reg_mirror`. The endgame's arithmetic is stated in
a state model (`sum_snorm_sq_sub_le_of_agree`) and its Schwartz--Zippel step in a bipartite model
(`sum_uniform_bornProb_fibre_le`), with the matrix constants. Item 1's cut is the register model
`tgt` of `MIPRE/Background/QLD/PhysModel.lean`, into which the physical registers are regrouped by
the local isometry `unassoc`, with no reindexing of the players' spaces: the matrix regrouping
`endEquiv`, its state `endVec` and its reindexing lemma are gone, and what they were for --- the
norm and the Born probabilities of a regrouped vector --- is read off `unassoc` (`endVec_unit`,
`qform_endVec`). The twirl's expectation on any vector of `Ampl (T x T) H` is the uniform average of
the per-probe ones (`qform_bOp_twirl`).
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl OperatorMatrix
open scoped Kronecker ComplexOrder MatrixOrder InnerProductSpace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedSectionVars false

/-! ## An operator on the ancilla pair, against the product state -/

section Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **An operator on the ancilla pair acts on the pair's factor of the product and leaves the
auxiliary vector.** One component computation. -/
theorem bOp_mulVec_auxVec (aux : H) (P : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ)
    (t : (n → F) × (n → F)) :
    regAct P (auxVec (F := F) (n := n) aux) t = (P *ᵥ epr (F := F) (n := n)) t • aux := by
  rw [auxVec, regAct_toLp_smul, PiLp.toLp_apply]

/-- **Two operators that agree on the entangled pair agree on the product state.** -/
theorem mulVec_auxVec_congr (aux : H)
    {P Q : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ}
    (h : P *ᵥ (epr (F := F) (n := n)) = Q *ᵥ epr) :
    regAct P (auxVec (F := F) (n := n) aux) = regAct Q (auxVec (F := F) (n := n) aux) := by
  rw [auxVec, regAct_toLp_smul, regAct_toLp_smul, h]

/-- **Display `eq:qld-unitary-7`'s last line, on the product state.** A generalized Pauli's
spectral projector moves from one half of the entangled pair to the other at no cost: the
projectors are symmetric, being real Fourier averages of a symmetric family. -/
theorem mulVec_auxVec_proj (aux : H) {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) (e : n → F) :
    regAct (proj w e ⊗ₖ (1 : Matrix (n → F) (n → F) ℂ)) (auxVec (F := F) (n := n) aux)
      = regAct ((1 : Matrix (n → F) (n → F) ℂ) ⊗ₖ proj w e) (auxVec (F := F) (n := n) aux) :=
  mulVec_auxVec_congr aux (congrArg WithLp.ofLp (stateVec_epr_proj hw e))

/-- **And so does a syndrome projector**, being a sum of spectral projectors over a level set. -/
theorem mulVec_auxVec_syn (aux : H) {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) (v : n → F) (a : F) :
    regAct (syn w v a ⊗ₖ (1 : Matrix (n → F) (n → F) ℂ)) (auxVec (F := F) (n := n) aux)
      = regAct ((1 : Matrix (n → F) (n → F) ℂ) ⊗ₖ syn w v a) (auxVec (F := F) (n := n) aux) :=
  mulVec_auxVec_congr aux (congrArg WithLp.ofLp (stateVec_epr_syn hw v a))

end Aux

/-! ## The endgame, as arithmetic

Everything after display `eq:qld-unitary-7` is a lower bound on one number: the agreement of the
conjugated Pauli measurement with the bare ancilla family on the product state. The deviation the
lemma asks about is twice its deficit, and no more. -/

section Arithmetic

variable {𝒞 : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] {Λ : Type*} [Fintype Λ]
  [DecidableEq Λ]

/-- **Display `eq:qld-unitary-7`, read as a bound.** Once the agreement of two projective families
on one party is at least `1 - c`, their summed deviation is at most `2c`. -/
theorem sum_snorm_sq_sub_le_of_agree {M : StateModel 𝒞} (hM : ‖M.ψ‖ = 1) {A T : Λ → 𝒞}
    (hA : IsPVMIn A) (hT : IsPVMIn T) {c : ℝ} (hagree : 1 - c ≤ ∑ h, M.qform (A h * T h)) :
    ∑ h, M.snorm (A h - T h) ^ 2 ≤ 2 * c := by
  rw [sum_snorm_sq_sub_eq_two_sub hM hA hT]
  linarith

end Arithmetic

/-! ## Display `eq:qld-unitary-8`: coarse-graining raises the agreement by at most `md/q`

The chain reads the two families at the *value* of the encoding at the sampled point rather than at
the full outcome. That can only add agreeing pairs, and the pairs it adds are the distinct ones
whose encodings collide there --- which is Schwartz--Zippel, already packaged as
`sum_uniform_agree_bornProb_le`. -/

section Coarse

open MIPRE.LIDT MIPRE.LowDegree

variable {m d : ℕ} [NeZero m] {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜]
  [StarRing 𝒜] [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜]
  [StarOrderedRing 𝒜] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- **Display `eq:qld-unitary-8`.** For two projective families of the two players, indexed
injectively by low-individual-degree polynomials, the agreement of their coarse-grainings by the
value at a uniform point exceeds their own agreement by at most `md/q`. -/
theorem sum_uniform_bornProb_fibre_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {M : BipartiteModel 𝒞 𝒜 ℬ} (hM : ‖M.ψ‖ = 1)
    {A : Λ → 𝒜} {T : Λ → ℬ} (hA : IsPVMIn A) (hT : IsPVMIn T)
    {enc : Λ → LowIndDegPoly (F := F) (m := m) (d := d)}
    (hinj : ∀ h h' : Λ, h ≠ h' → (enc h).toMv ≠ (enc h').toMv) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        M.bornProb (∑ h ∈ univ.filter fun h => (enc h).eval u = a, A h)
          (∑ h ∈ univ.filter fun h => (enc h).eval u = a, T h)
      ≤ (∑ h, M.bornProb (A h) (T h)) + (m : ℝ) * d / Fintype.card F := by
  classical
  -- the agreeing pairs at `u`, fibred by the common value
  have hset : ∀ (u : Point F m) (a : F),
      (univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u).filter
          (fun p => (enc p.1).eval u = a)
        = (univ.filter fun h => (enc h).eval u = a) ×ˢ
          (univ.filter fun h => (enc h).eval u = a) := by
    intro u a
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hagree, ha⟩
      exact ⟨ha, hagree ▸ ha⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans h2.symm, h1⟩
  -- at each `u`, the coarse agreement is the sum over agreeing pairs
  have hu : ∀ u : Point F m, (∑ a : F,
        M.bornProb (∑ h ∈ univ.filter fun h => (enc h).eval u = a, A h)
          (∑ h ∈ univ.filter fun h => (enc h).eval u = a, T h))
      = ∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
          M.bornProb (A p.1) (T p.2) := by
    intro u
    rw [← Finset.sum_fiberwise (univ.filter fun p : Λ × Λ =>
      (enc p.1).eval u = (enc p.2).eval u) (fun p => (enc p.1).eval u)
      fun p => M.bornProb (A p.1) (T p.2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [M.bornProb_sum_sum, hset u a, Finset.sum_product]
  -- and that sum splits into its diagonal and the off-diagonal Schwartz--Zippel mass
  have hsplit : ∀ u : Point F m,
      (∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
          M.bornProb (A p.1) (T p.2))
        = (∑ h, M.bornProb (A h) (T h))
          + ∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
              (if p.1 = p.2 then (0 : ℝ) else M.bornProb (A p.1) (T p.2)) := by
    intro u
    rw [show (∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
          M.bornProb (A p.1) (T p.2))
        = ∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
            ((if p.1 = p.2 then M.bornProb (A p.1) (T p.2) else 0)
              + (if p.1 = p.2 then (0 : ℝ) else M.bornProb (A p.1) (T p.2))) from
      Finset.sum_congr rfl fun p _ => by split_ifs <;> ring, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_eq_single h (fun h' _ hh' => by simp [Ne.symm hh']) fun hmem =>
      absurd (mem_univ h) hmem]
    simp
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) => by rw [hu u, hsplit u],
    Finset.sum_congr rfl fun u (_ : u ∈ univ) =>
      mul_add (uniform (Point F m) u) _ _, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_uniform_eq_one (Point F m), one_mul]
  linarith [sum_uniform_agree_bornProb_le hM hA hT hinj]

end Coarse

/-! ## Item 1's cut, as a regrouping

`exists_auxVec_close` reads the state along a cut of its own: the two parties' non-ancilla
registers as one space, their two far halves `A''`, `B''` adjacent as one register. The physical
state groups the registers by party, `(A'', (Ea, A'))` against `(B'', (Eb, B'))`, so the two are a
regrouping of the finite registers apart: item 1's cut is the register model `tgt` (the extension
of the strategy's model by the padded registers `((Ea, A'), (Eb, B'))`, with the EPR register
`(A'', B'')` outside), and `unassoc` regroups the physical model into it --- moving both far halves
out of the party grouping, where the first cut moved one across it.

Nothing here is an estimate. It is what the threading of item 2 has to say before any of the
endgame's steps can be pointed at the same vector. -/

section EndCut

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ]
variable {I : Type*} [Fintype I] [DecidableEq I] {m d K : ℕ} {N : BipartiteModel 𝒞 𝒜 ℬ}

omit [Algebra (ZMod 2) F] in
/-- **A regrouped unit vector is a unit vector**: `unassoc` is isometric. -/
theorem endVec_unit {φ : (phys I F m d N K).H} (hφ : ‖φ‖ = 1) :
    ‖(unassoc I F m d N K).W φ‖ = 1 := by
  rw [LinearIsometry.norm_map, hφ]

omit [Algebra (ZMod 2) F] in
/-- **The same Born probability, read on the two cuts.** A product of an operator of each player of
item 1's cut, on a vector regrouped by `unassoc`, has the expectation the two regrouped-back
operators have on the vector itself in the physical model: each player's operator is a block matrix
over that player's far half, and `compHom` flattens it onto the player's physical registers. -/
theorem qform_endVec (φ : (phys I F m d N K).H)
    (X : Matrix I I (Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) 𝒜))
    (Y : Matrix I I (Matrix (PadAnc F m d K × I) (PadAnc F m d K × I) ℬ)) :
    ((tgt I F m d N K).withState ((unassoc I F m d N K).W φ)).bornProb X Y
      = ((phys I F m d N K).withState φ).bornProb (compHom X) (compHom Y) := by
  have h := (unassoc I F m d N K).intertwine (compHom X) (compHom Y) φ
  rw [unassoc_ΦA, unassoc_ΦB, uncompHom_compHom, uncompHom_compHom] at h
  show (⟪(unassoc I F m d N K).W φ, (tgt I F m d N K).π
      ((tgt I F m d N K).πA X * (tgt I F m d N K).πB Y) ((unassoc I F m d N K).W φ)⟫_ℂ).re
    = (⟪φ, (phys I F m d N K).π ((phys I F m d N K).πA (compHom X)
      * (phys I F m d N K).πB (compHom Y)) φ⟫_ℂ).re
  rw [h, LinearIsometry.inner_map_map]

end EndCut

/-! ## The twirl, as an average over probes

Item 1 asks for a near-invariance of the state under the Weyl twirl on its two ancilla halves.
What `lem:qld-pauli-selfcons` supplies is an agreement of the two parties' exact Pauli observables
averaged over a *uniform* probe. The twirl is by definition that average, so the two statements are
one rewriting apart --- which is the edge the blueprint's dependency graph was missing, made
explicit. -/

section Twirl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Field F] [Algebra (ZMod 2) F] in
/-- **The twirl's expectation is the uniform average of the per-probe ones**, on any vector of
`Ampl (T x T) H`. -/
theorem qform_bOp_twirl (θ : Ampl ((n → F) × (n → F)) H)
    (w : (n → F) → Matrix (n → F) (n → F) ℂ) :
    Op.qform θ (regAct (twirl w))
      = ∑ u, uniform (n → F) u * Op.qform θ (regAct (w u ⊗ₖ w u)) := by
  have hsc : ((Fintype.card (n → F) : ℂ))⁻¹ = ((((Fintype.card (n → F) : ℝ))⁻¹ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [regAct_twirl, hsc, Op.qform_smul_real, Op.qform_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => rfl

end Twirl

end MIPRE.QLD

end

end
