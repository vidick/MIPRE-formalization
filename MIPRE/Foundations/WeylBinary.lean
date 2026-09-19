/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.WeylEPR
import MIPRE.Foundations.LowDegree.NormalBasis

/-!
# From qudits to qubits: the generalized Pauli system is a qubit Pauli system

Blueprint `lem:pauli-binary`. A self-dual basis of `F_q` over `F_2` identifies `F_q^n` with
`F_2^{n x k}`, and under that identification **every piece of the Weyl data over `F_q` becomes the
corresponding piece over `F_2`**: the form `trDot`, the two operator families, their spectral
projectors, and the maximally entangled state.
-/

noncomputable section

namespace MIPRE.Weyl

open Finset Matrix MIPRE MIPRE.LowDegree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-! ## The relabelling -/

/-- **The coordinate relabelling** `F_q^n ≃ F_2^{n x k}` attached to a basis `b` of `F_q` over
`F_2`: send `a` to its matrix of coordinates. -/
def binEquiv (b : Module.Basis ι (ZMod 2) F) : (n → F) ≃ (n × ι → ZMod 2) :=
  (Equiv.piCongrRight fun _ => b.equivFun.toEquiv).trans (Equiv.curry n ι (ZMod 2)).symm

variable {b : Module.Basis ι (ZMod 2) F}

@[simp] theorem binEquiv_apply (a : n → F) (p : n × ι) :
    binEquiv (n := n) b a p = b.repr (a p.1) p.2 := rfl

theorem binEquiv_add (a a' : n → F) :
    binEquiv (n := n) b (a + a') = binEquiv b a + binEquiv b a' := by
  funext p
  simp [Pi.add_apply]

theorem binEquiv_injective : Function.Injective (binEquiv (n := n) b) :=
  (binEquiv b).injective

theorem binEquiv_eq_iff (a a' : n → F) :
    binEquiv (n := n) b a = binEquiv b a' ↔ a = a' :=
  (binEquiv b).apply_eq_iff_eq

/-! ## The form -/

/-- **Self-duality is exactly what makes the form transport.** -/
theorem trDot_binEquiv (hb : IsSelfDualBasis b) (a a' : n → F) :
    trDot (binEquiv (n := n) b a) (binEquiv b a') = trDot a a' := by
  rw [trDot, trDot, Algebra.trace_self_apply, Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [trace_mul_eq_dot hb]
  rfl

/-! ## The operator families

Both are carried over by `Matrix.submatrix` along the relabelling --- which is conjugation by the
permutation unitary the paper calls the isometry `phi`, written as a reindexing of rows and
columns so that no unitary has to be constructed. -/

/-- **The `X`-type family transports**, and needs no self-duality: the relabelling is additive,
which is all a shift knows about. -/
theorem wX_binEquiv (a : n → F) :
    (wX (binEquiv (n := n) b a)).submatrix (binEquiv b) (binEquiv b) = wX a := by
  ext j i
  rw [Matrix.submatrix_apply, wX_apply, wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, if_pos (by rw [h, binEquiv_add])]
  · rw [if_neg h, if_neg ?_]
    intro hh
    exact h (binEquiv_eq_iff (b := b) j (i + a) |>.mp (by rw [hh, binEquiv_add]))

/-- **The `Z`-type family transports**, by self-duality of the basis. -/
theorem wZ_binEquiv (hb : IsSelfDualBasis b) (c : n → F) :
    (wZ (binEquiv (n := n) b c)).submatrix (binEquiv b) (binEquiv b) = wZ c := by
  ext j i
  rw [Matrix.submatrix_apply, wZ_apply, wZ_apply, trDot_binEquiv hb]
  by_cases h : j = i
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg fun hh => h (binEquiv_eq_iff (b := b) j i |>.mp hh)]

/-! ## The spectral projectors

The Fourier average commutes with the relabelling: the index group is reindexed by it, the
character is the transported form, and the normalization is the same cardinality counted on
either side. -/

theorem card_binEquiv (b : Module.Basis ι (ZMod 2) F) :
    Fintype.card (n × ι → ZMod 2) = Fintype.card (n → F) :=
  (Fintype.card_congr (binEquiv (n := n) b)).symm

/-- **The Fourier average commutes with the relabelling**, for an arbitrary family: no group law
and no self-duality beyond the form's. -/
theorem proj_binEquiv (hb : IsSelfDualBasis b)
    (w : (n × ι → ZMod 2) → Matrix (n × ι → ZMod 2) (n × ι → ZMod 2) ℂ) (e : n → F) :
    (proj w (binEquiv b e)).submatrix (binEquiv b) (binEquiv b)
      = proj (fun a => (w (binEquiv (n := n) b a)).submatrix (binEquiv b) (binEquiv b)) e := by
  ext j i
  rw [Matrix.submatrix_apply, proj_def, proj_def, card_binEquiv (n := n) b]
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.submatrix_apply, smul_eq_mul]
  congr 1
  refine Fintype.sum_equiv (binEquiv (n := n) b).symm _ _ fun x => ?_
  rw [← trDot_binEquiv hb ((binEquiv (n := n) b).symm x) e, Equiv.apply_symm_apply]

/-- **The `Z`-side projectors transport.** -/
theorem proj_wZ_binEquiv (hb : IsSelfDualBasis b) (e : n → F) :
    (proj wZ (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b)
      = proj (wZ (F := F) (n := n)) e := by
  rw [proj_binEquiv hb]
  congr 1
  exact funext fun a => wZ_binEquiv hb a

/-- **The `X`-side projectors transport.** -/
theorem proj_wX_binEquiv (hb : IsSelfDualBasis b) (e : n → F) :
    (proj wX (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b)
      = proj (wX (F := F) (n := n)) e := by
  rw [proj_binEquiv hb]
  congr 1
  exact funext fun a => wX_binEquiv a

/-! ## The maximally entangled state -/

theorem eprScale_binEquiv (b : Module.Basis ι (ZMod 2) F) :
    eprScale (F := ZMod 2) (n := n × ι) = eprScale (F := F) (n := n) := by
  rw [eprScale, eprScale, card_binEquiv (n := n) b]

/-- **The maximally entangled state transports**: `phi ⊗ phi |EPR_q⟩^{⊗ n} = |EPR_2⟩^{⊗ nk}`,
in the relabelled form. Both sides are the normalized diagonal, and a relabelling of the index set
preserves the diagonal; the two normalizations agree because the two index sets have the same
cardinality. -/
theorem epr_binEquiv (p : (n → F) × (n → F)) :
    epr (F := ZMod 2) (n := n × ι) (binEquiv b p.1, binEquiv b p.2) = epr p := by
  obtain ⟨a, a'⟩ := p
  by_cases h : a = a'
  · subst h
    rw [epr_same, epr_same, eprScale_binEquiv (n := n) b]
  · rw [epr_ne fun hh => h ((binEquiv_eq_iff a a').mp hh), epr_ne h]

/-! ## The five items together -/

/-- **`lem:pauli-binary`.** Given a self-dual basis of `F_q` over `F_2`, the coordinate
relabelling carries the whole Weyl system over `F_q` on `n` registers to the Weyl system over
`F_2` on `n x k` registers --- the maximally entangled state, both operator families, and both
families of spectral projectors.

The paper's `phi` is a genuine isometry `(C^q)^{⊗ L} → (C^2)^{⊗ Lk}` and the transported operator
is `phi^† (...) phi`; here the isometry is a bijection of basis index sets, so conjugating by it is
`Matrix.submatrix`, and no unitary has to be built. -/
theorem pauli_binary (hb : IsSelfDualBasis b) :
    (∀ p : (n → F) × (n → F),
        epr (F := ZMod 2) (n := n × ι) (binEquiv b p.1, binEquiv b p.2) = epr p) ∧
      (∀ a : n → F, (wX (binEquiv (n := n) b a)).submatrix (binEquiv b) (binEquiv b) = wX a) ∧
      (∀ c : n → F, (wZ (binEquiv (n := n) b c)).submatrix (binEquiv b) (binEquiv b) = wZ c) ∧
      (∀ e : n → F,
        (proj wX (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b) = proj wX e) ∧
      (∀ e : n → F,
        (proj wZ (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b) = proj wZ e) :=
  ⟨epr_binEquiv, wX_binEquiv, wZ_binEquiv hb, proj_wX_binEquiv hb, proj_wZ_binEquiv hb⟩

/-- **The relabelling exists** for every field of characteristic two and odd degree over `F_2`:
`lem:pauli-binary` composed with the existence half of `lem:self-dual-basis`. The oddness is the
hypothesis of `exists_isSelfDualBasis_isNormalBasis`, not of anything here; the paper's admissible
field sizes satisfy it. -/
theorem exists_binEquiv_pauli_binary (hodd : Odd (Module.finrank (ZMod 2) F)) (n : Type*) [Fintype n] [DecidableEq n] :
    ∃ (k : ℕ) (b : Module.Basis (Fin k) (ZMod 2) F), IsSelfDualBasis b ∧ IsNormalBasis b ∧
      (∀ p : (n → F) × (n → F),
          epr (F := ZMod 2) (n := n × Fin k) (binEquiv b p.1, binEquiv b p.2) = epr p) ∧
        (∀ a : n → F, (wX (binEquiv (n := n) b a)).submatrix (binEquiv b) (binEquiv b) = wX a) ∧
        (∀ c : n → F, (wZ (binEquiv (n := n) b c)).submatrix (binEquiv b) (binEquiv b) = wZ c) ∧
        (∀ e : n → F,
          (proj wX (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b) = proj wX e) ∧
        (∀ e : n → F,
          (proj wZ (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b) = proj wZ e) := by
  classical
  obtain ⟨b, hsd, hnb⟩ := exists_isSelfDualBasis_isNormalBasis (ZMod 2) F (ZMod.charP 2) hodd
  obtain ⟨h1, h2, h3, h4, h5⟩ := pauli_binary (n := n) hsd
  exact ⟨_, b, hsd, hnb, h1, h2, h3, h4, h5⟩

/-! ## The target system is qubits, register by register

The binary Weyl system is `Weyl` at `F = F_2` and index set `n x k`, whose matrices are indexed by
the functions `n x k → F_2` --- that is, by the computational basis of `(C^2)^{⊗ nk}`. These three
identities say that the operators are the *tensor products* of the single-qubit ones, in the only
sense the one-matrix presentation can state it: entry by entry, as a product over the qubits. They
are what makes "these are qubit Paulis" a checked statement rather than a reading of the encoding.
-/

section Qubits

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Over `F_2` the form is the plain dot product: the field trace of a one-dimensional extension
is the identity. -/
theorem trDot_two (a c : m → ZMod 2) : trDot a c = ∑ p, a p * c p := by
  rw [trDot, Algebra.trace_self_apply]

/-- The character of the binary form factorizes over the qubits. -/
theorem sgn_trDot_two (a c : m → ZMod 2) : sgn (trDot a c) = ∏ p, sgn (a p * c p) := by
  rw [trDot_two, sgn_sum]

/-- **The binary `Z`-type operator is the tensor product of single-qubit `Z`s**: it is diagonal
(`wZ_apply`) and its diagonal entries are products over the qubits. -/
theorem wZ_two_diag (c i : m → ZMod 2) : wZ c i i = ∏ p, sgn (c p * i p) := by
  rw [wZ_apply, if_pos rfl, sgn_trDot_two]

/-- **The binary `X`-type operator is the tensor product of single-qubit `X`s**: every entry is
the product of the single-qubit entries. -/
theorem wX_two_apply (a j i : m → ZMod 2) :
    wX a j i = ∏ p, (if j p = i p + a p then (1 : ℂ) else 0) := by
  rw [wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, Finset.prod_eq_one]
    intro p _
    rw [if_pos (by rw [h]; rfl)]
  · rw [if_neg h]
    obtain ⟨p, hp⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)).symm

end Qubits

end MIPRE.Weyl

end
