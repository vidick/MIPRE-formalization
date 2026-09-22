/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.SwapMeasure
import MIPRE.Background.QLD.SwapState

/-!
# The endgame of `lem:qld-swap` item 2

Item 1 produces a product state `|aux> (x) |EPR_q>^M` close to the conjugated padded state
(`exists_auxVec_close`). Item 2's endgame computes against that product state and transports the
answer back. This file is the part of that computation that is about the product state itself.

## What an operator on the ancilla pair does to a product state

`auxVec aux` is a product: the first factor is arbitrary, the second is the maximally entangled
pair. So an operator acting on the pair alone acts on the second factor and leaves the first, and
two operators that agree on `|EPR_q>` agree on the whole product. That is the last line of display
`eq:qld-unitary-7`, where a generalized Pauli's spectral projector is moved from one half of the
pair to the other: the projectors are symmetric matrices, so `stateVec_epr_proj` moves them across
the pair, and `mulVec_auxVec_congr` carries that to the product state.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Fintype R] [DecidableEq R]

set_option linter.unusedSectionVars false

/-! ## An operator on the ancilla pair, against the product state -/

section Aux

/-- **An operator on the ancilla pair acts on the second factor of the product and leaves the
first.** One entry computation. -/
theorem bOp_mulVec_auxVec (aux : R → ℂ)
    (P : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ) (r : R)
    (t : (n → F) × (n → F)) :
    ((bOp P : Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ
        auxVec (F := F) (n := n) aux) (r, t)
      = aux r * (P *ᵥ (epr (F := F) (n := n))) t := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single r (fun r' _ hr' => Finset.sum_eq_zero fun t' _ => by
        rw [bOp, Matrix.kronecker_apply, Matrix.one_apply_ne (Ne.symm hr'), zero_mul, zero_mul])
      fun hmem => absurd (mem_univ r) hmem,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [bOp, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul, auxVec]
  ring

/-- **Two operators that agree on the entangled pair agree on the product state.** -/
theorem mulVec_auxVec_congr (aux : R → ℂ)
    {P Q : Matrix ((n → F) × (n → F)) ((n → F) × (n → F)) ℂ}
    (h : P *ᵥ (epr (F := F) (n := n)) = Q *ᵥ epr) :
    (bOp P : Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ auxVec aux
      = (bOp Q : Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ auxVec aux := by
  funext p
  obtain ⟨r, t⟩ := p
  rw [bOp_mulVec_auxVec, bOp_mulVec_auxVec, h]

/-- **Display `eq:qld-unitary-7`'s last line, on the product state.** A generalized Pauli's
spectral projector moves from one half of the entangled pair to the other at no cost: the
projectors are symmetric, being real Fourier averages of a symmetric family. -/
theorem mulVec_auxVec_proj (aux : R → ℂ) {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) (e : n → F) :
    (bOp (aOp (proj w e)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ auxVec aux
      = (bOp (bOp (proj w e)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ auxVec aux :=
  mulVec_auxVec_congr aux (congrArg WithLp.ofLp (stateVec_epr_proj hw e))

/-- **And so does a syndrome projector**, being a sum of spectral projectors over a level set. -/
theorem mulVec_auxVec_syn (aux : R → ℂ) {w : (n → F) → Matrix (n → F) (n → F) ℂ}
    (hw : ∀ a, (w a)ᵀ = w a) (v : n → F) (a : F) :
    (bOp (aOp (syn w v a)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ auxVec aux
      = (bOp (bOp (syn w v a)) :
        Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ auxVec aux :=
  mulVec_auxVec_congr aux (congrArg WithLp.ofLp (stateVec_epr_syn hw v a))

end Aux

/-! ## The endgame, as arithmetic

Everything after display `eq:qld-unitary-7` is a lower bound on one number: the agreement of the
conjugated Pauli measurement with the bare ancilla family on the product state. The deviation the
lemma asks about is twice its deficit, and no more. -/

section Arithmetic

variable {N Λ : Type*} [Fintype N] [DecidableEq N] [Fintype Λ] [DecidableEq Λ]

/-- **Display `eq:qld-unitary-7`, read as a bound.** Once the agreement is at least `1 - c`, the
summed deviation is at most `2c`. -/
theorem sum_snorm_sq_sub_le_of_agree {v : N → ℂ} (hv : ‖evec v‖ = 1) {A T : Λ → Matrix N N ℂ}
    (hA : IsPVM A) (hT : IsPVM T) {c : ℝ} (hagree : 1 - c ≤ ∑ h, qform v (A h * T h)) :
    ∑ h, snorm v (A h - T h) ^ 2 ≤ 2 * c := by
  rw [sum_snorm_sq_sub_eq_two_sub hv hA hT]
  linarith

end Arithmetic

/-! ## Display `eq:qld-unitary-8`: coarse-graining raises the agreement by at most `md/q`

The chain reads the two families at the *value* of the encoding at the sampled point rather than at
the full outcome. That can only add agreeing pairs, and the pairs it adds are the distinct ones
whose encodings collide there --- which is Schwartz--Zippel, already packaged as
`sum_uniform_agree_bornProb_le`. -/

section Coarse

open MIPRE.LIDT MIPRE.LowDegree

variable {m d : ℕ} [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]

/-- **Display `eq:qld-unitary-8`.** -/
theorem sum_uniform_bornProb_fibre_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {A : Λ → Matrix dA dA ℂ} {T : Λ → Matrix dB dB ℂ} (hA : IsPVM A) (hT : IsPVM T)
    {enc : Λ → LowIndDegPoly (F := F) (m := m) (d := d)}
    (hinj : ∀ h h' : Λ, h ≠ h' → (enc h).toMv ≠ (enc h').toMv) :
    ∑ u, uniform (Point F m) u * ∑ a : F,
        bornProb ψ (∑ h ∈ univ.filter fun h => (enc h).eval u = a, A h)
          (∑ h ∈ univ.filter fun h => (enc h).eval u = a, T h)
      ≤ (∑ h, bornProb ψ (A h) (T h)) + (m : ℝ) * d / Fintype.card F := by
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
        bornProb ψ (∑ h ∈ univ.filter fun h => (enc h).eval u = a, A h)
          (∑ h ∈ univ.filter fun h => (enc h).eval u = a, T h))
      = ∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
          bornProb ψ (A p.1) (T p.2) := by
    intro u
    rw [← Finset.sum_fiberwise (univ.filter fun p : Λ × Λ =>
      (enc p.1).eval u = (enc p.2).eval u) (fun p => (enc p.1).eval u)
      fun p => bornProb ψ (A p.1) (T p.2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [bornProb_sum_sum, hset u a, Finset.sum_product]
  -- and that sum splits into its diagonal and the off-diagonal Schwartz--Zippel mass
  have hsplit : ∀ u : Point F m,
      (∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
          bornProb ψ (A p.1) (T p.2))
        = (∑ h, bornProb ψ (A h) (T h))
          + ∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
              (if p.1 = p.2 then (0 : ℝ) else bornProb ψ (A p.1) (T p.2)) := by
    intro u
    rw [show (∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
          bornProb ψ (A p.1) (T p.2))
        = ∑ p ∈ univ.filter fun p : Λ × Λ => (enc p.1).eval u = (enc p.2).eval u,
            ((if p.1 = p.2 then bornProb ψ (A p.1) (T p.2) else 0)
              + (if p.1 = p.2 then (0 : ℝ) else bornProb ψ (A p.1) (T p.2))) from
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
  linarith [sum_uniform_agree_bornProb_le hψ hA hT hinj]

end Coarse

end MIPRE.QLD

end
