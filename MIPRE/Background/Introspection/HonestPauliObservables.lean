/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.Game
import MIPRE.Foundations.Introspection.HonestMagicSquare
import MIPRE.Foundations.Pasting

/-! # The concrete Pauli probes of the honest QLD strategy

Low-degree evaluation followed by the verifier's field trace is exactly the
binary spectral measurement of a Weyl observable. The verifier's `gam` is
proved to equal the commutation phase of the two observables.
-/

noncomputable section

namespace MIPRE.QLD.Honest

open Matrix Finset Weyl LCS

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}

abbrev Register (F : Type*) (m : ℕ) := (Fin m → Bool) → F

def basis (W : Bas) : Register F m → Matrix (Register F m) (Register F m) ℂ :=
  match W with
  | .X => wX
  | .Z => wZ

theorem basis_isWeyl (W : Bas) : IsWeylFamily (basis (F := F) (m := m) W) := by
  cases W
  · exact isWeylFamily_wX
  · exact isWeylFamily_wZ

def pauliOp (W : Bas) : Register F m → Matrix (Register F m) (Register F m) ℂ := proj (basis W)

theorem pauliOp_isPVM (W : Bas) : IsPVM (pauliOp (F := F) (m := m) W) where
  isSelfAdjoint := proj_conjTranspose (basis_isWeyl W)
  idem h := by rw [pauliOp, proj_mul_proj (basis_isWeyl W), if_pos rfl]
  sum_eq_one := sum_proj (basis_isWeyl W)

def probeVector (ω : Omega F m) (W : Bas) : Register F m :=
  ω.r W • LowDegree.indVec (ω.pt W)

def probeLabel (ω : Omega F m) (W : Bas) (h : Register F m) : ZMod 2 :=
  prb (MvPolynomial.eval (ω.pt W) (LowDegree.ldEnc h)) (ω.r W)

omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
theorem eval_ldEnc_dot (h : Register F m) (u : LIDT.Point F m) :
    MvPolynomial.eval u (LowDegree.ldEnc h) = ∑ y, h y * LowDegree.indVec u y := by
  simp [LowDegree.ldEnc, LowDegree.indVec]

omit [Fintype F] [DecidableEq F] in
theorem probeVector_trace (ω : Omega F m) (W : Bas) (h : Register F m) :
    trDot (probeVector ω W) h = probeLabel ω W h := by
  unfold probeLabel prb trDot probeVector
  rw [eval_ldEnc_dot, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

def probeOp (ω : Omega F m) (W : Bas) : ZMod 2 → Matrix (Register F m) (Register F m) ℂ :=
  fibSum (pauliOp W) (probeLabel ω W)

theorem probeOp_isPVM (ω : Omega F m) (W : Bas) : IsPVM (probeOp ω W) :=
  isPVM_fibSum (pauliOp_isPVM W) _

private theorem signed_fibre {X I : Type*} [Fintype X] [Fintype I] [DecidableEq I]
    (P : X → Matrix I I ℂ) (f : X → ZMod 2) :
    ∑ b : ZMod 2, sgn b • fibSum P f b = ∑ x, sgn (f x) • P x := by
  unfold fibSum
  simp only [Finset.smul_sum]
  calc
    _ = ∑ b : ZMod 2, ∑ x ∈ univ.filter (fun x => f x = b), sgn (f x) • P x := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := Finset.sum_fiberwise univ f (fun x => sgn (f x) • P x)

/-- The actual verifier probe is the binary spectral measurement of this Weyl operator. -/
theorem probe_observable (ω : Omega F m) (W : Bas) :
    observableOfMeasurementSystem (probeOp ω W) = basis W (probeVector ω W) := by
  rw [eq_sum_proj (w := basis W) (probeVector ω W)]
  simp only [probeVector_trace]
  have h := signed_fibre (pauliOp W) (probeLabel ω W)
  rw [sum_univ_zmod_two] at h
  simpa only [sgn_zero, sgn_one, one_smul, neg_smul, sub_eq_add_neg,
    probeOp, observableOfMeasurementSystem, pauliOp] using h

theorem probeOp_isMeasurementSystem (ω : Omega F m) (W : Bas) :
    IsMeasurementSystem (probeOp ω W) where
  sum_one := (probeOp_isPVM ω W).sum_eq_one
  idempotent := (probeOp_isPVM ω W).idem
  orthogonal _ _ hab := (probeOp_isPVM ω W).orthogonal hab
  self_adjoint := (probeOp_isPVM ω W).isSelfAdjoint

theorem probe_basis_isObservable (ω : Omega F m) (W : Bas) :
    IsObservable (basis W (probeVector ω W)) := by
  rw [← probe_observable]
  exact isObservable_observableOfMeasurementSystem _ (probeOp_isMeasurementSystem ω W)

omit [Fintype F] [DecidableEq F] in
/-- The phase tested by the verifier is precisely the Pauli commutation phase. -/
theorem probe_phase (ω : Omega F m) :
    trDot (probeVector ω .X) (probeVector ω .Z) = gam ω := by
  unfold trDot probeVector gam LowDegree.acGamma LowDegree.indPair
  congr 1
  simp only [Omega.r, Omega.pt, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem probe_basis_commute (ω : Omega F m) (h : gam ω = 0) :
    Commute (basis .X (probeVector ω .X)) (basis .Z (probeVector ω .Z)) := by
  exact wX_mul_wZ_of_eq _ _ (by rwa [probe_phase])

theorem probe_basis_anticommute (ω : Omega F m) (h : gam ω ≠ 0) :
    basis .X (probeVector ω .X) * basis .Z (probeVector ω .Z) =
      -(basis .Z (probeVector ω .Z) * basis .X (probeVector ω .X)) := by
  apply wX_mul_wZ_of_ne
  rw [probe_phase]
  rcases zmod_two_eq_zero_or_one (gam ω) with h0 | h1
  · exact (h h0).elim
  · exact h1

end MIPRE.QLD.Honest
