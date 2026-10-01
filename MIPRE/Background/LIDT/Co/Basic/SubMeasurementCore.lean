/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors, and Thomas Vidick. All rights
reserved. Released under Apache 2.0 license as described in the file LICENSE.
Ported from https://github.com/LionSR/MIPStarRE (commit 507e8122), MIPStarRE/LDT/Basic/
SubMeasurementCore.lean, to the symmetric model of `planning/c6b-plan.md`; not a vendored file.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Co.Basic.QuantumState
public import MIPRE.Foundations.Measurement

@[expose] public section

/-!
# Core submeasurement structures for the low individual degree test

Foundational measurement, submeasurement, and projective-measurement structures: the counterpart
of `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementCore.lean` in the port of
`planning/c6b-plan.md` (milestone M0, section "Port conventions").

The vendored structures have their effects in the matrix algebra `Op ι`. Here they are generic
over an ordered `⋆`-ring `R` (`[Ring R] [StarRing R] [PartialOrder R]`), with the vendored field
names verbatim: local families take `R = 𝔓`, the local C*-algebra of a symmetric model, and joint
families `R = K →L[ℂ] K`. Each lemma asks for what its proof uses: positivity facts for a
star-ordered ring, and the two projective lemmas (`ProjSubMeas.outcome_mul_total_eq_outcome`,
`ProjSubMeas.outcome_orthogonal`) for a C*-algebra, where the C*-identity
`star x * x = 0 → x = 0` (`CStarRing.star_mul_self_eq_zero_iff`) replaces the vendored
`Matrix.conjTranspose_mul_self_eq_zero`.

## New here

* `SubMeas.map`, `Measurement.map`, `ProjSubMeas.map`, `ProjMeas.map`: the image of a
  (sub)measurement under a `⋆`-algebra homomorphism. This is how the port places a local family
  on a tensor factor: the vendored `SubMeas.liftLeft` (`LDT/Basic/SubMeasurementFamilies.lean`)
  becomes `A.map S.L`, and `liftRight` becomes `A.map S.R`.
* The bridges to the repository's measurement vocabulary (`MIPRE/Foundations/Measurement.lean`):
  `Measurement.toPOVMIn` and `Measurement.ofPOVMIn`, inverse to each other, and
  `ProjMeas.isPVMIn` and `ProjMeas.ofIsPVMIn`.

## Not ported

Every declaration of the vendored file has a counterpart here.
-/

open scoped BigOperators

namespace MIPRE.LIDT.Co

/-- A paper-local submeasurement with outcomes in `α` and effects in the ordered `⋆`-ring `R`.

There is intentionally no global `Inhabited` instance: the zero family satisfies
these raw axioms, but using it as an ambient default would silently turn later
arguments into vacuous submeasurement statements. -/
structure SubMeas (α : Type*) [Fintype α] (R : Type*) [Ring R] [StarRing R] [PartialOrder R] where
  outcome : α → R := fun _ => 0
  total : R := 0
  outcome_pos : ∀ a, 0 ≤ outcome a
  sum_eq_total : ∑ a, outcome a = total
  total_le_one : total ≤ 1

/-- A paper-local measurement: a POVM whose positive effects sum to the identity. -/
structure Measurement (α : Type*) (R : Type*) [Fintype α] [Ring R] [StarRing R] [PartialOrder R]
    extends SubMeas α R where
  total_eq_one : total = 1

open scoped Classical in
/-- For a trivial distinguished-outcome measurement, every outcome operator is
positive: `0 ≤ if a = a₀ then 1 else 0`. -/
theorem Measurement.trivialDistinguishedOutcome_outcome_pos
    {α : Type*} {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (a₀ a : α) :
    (0 : R) ≤ if a = a₀ then 1 else 0 := by
  split_ifs
  · exact zero_le_one
  · exact le_rfl

open scoped Classical in
/-- ⚠️ DEGENERATE — Construct a trivial measurement where only the distinguished
outcome `a₀` is the identity and all other outcomes are zero.

This is a valid POVM but highly degenerate: it is only used in vacuous
fallback branches of the proof where the error bound is ≥ 1 (see the vendored
`Test/MainTheorem.lean:mainFormal_trivial_witness`).

Call this function explicitly with a chosen outcome.  There is intentionally no
ambient `Inhabited (Measurement α R)` instance: choosing a hidden
`default : α` would make degenerate witnesses available to paper-facing
existential statements without displaying the selected outcome. -/
noncomputable def Measurement.trivialDistinguishedOutcome
    {α : Type*} {R : Type*} [Fintype α] [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (a₀ : α) : Measurement α R where
  toSubMeas := {
    outcome := fun a => if a = a₀ then 1 else 0
    total := 1
    outcome_pos := fun a => Measurement.trivialDistinguishedOutcome_outcome_pos a₀ a
    sum_eq_total :=
      (Finset.sum_ite_eq' Finset.univ a₀ fun _ => 1).trans (ite_eq_left (Finset.mem_univ a₀))
    total_le_one := le_rfl
  }
  total_eq_one := rfl

/-- A paper-local projective submeasurement (each effect is idempotent).

There is intentionally no global `Inhabited` instance: any such default would
again collapse to the degenerate zero family. -/
structure ProjSubMeas (α : Type*) [Fintype α] (R : Type*) [Ring R] [StarRing R]
    [PartialOrder R] extends SubMeas α R where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- A paper-local projective measurement (complete POVM + projective). -/
structure ProjMeas (α : Type*) (R : Type*) [Fintype α] [Ring R] [StarRing R] [PartialOrder R]
    extends Measurement α R where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- For a trivial distinguished-outcome projective measurement, every outcome operator
is idempotent. -/
theorem ProjMeas.trivialDistinguishedOutcome_proj
    {α : Type*} {R : Type*} [Fintype α] [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (a₀ a : α) :
    (Measurement.trivialDistinguishedOutcome (R := R) a₀).outcome a *
        (Measurement.trivialDistinguishedOutcome (R := R) a₀).outcome a =
      (Measurement.trivialDistinguishedOutcome (R := R) a₀).outcome a := by
  classical
  by_cases h : a = a₀ <;> simp [Measurement.trivialDistinguishedOutcome, h]

/-- ⚠️ DEGENERATE — Construct a trivial projective measurement where only the
distinguished outcome `a₀` is the identity and all other outcomes are zero.

This is a valid projective POVM but highly degenerate: see the discussion at
`Measurement.trivialDistinguishedOutcome`.  As for `Measurement`, there is intentionally no
ambient `Inhabited (ProjMeas α R)` instance. -/
noncomputable def ProjMeas.trivialDistinguishedOutcome
    {α : Type*} {R : Type*} [Fintype α] [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (a₀ : α) : ProjMeas α R where
  toMeasurement := Measurement.trivialDistinguishedOutcome a₀
  proj := ProjMeas.trivialDistinguishedOutcome_proj a₀

/-! ### Derived properties -/

section Derived

variable {α : Type*} [Fintype α] {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- Two submeasurements are equal when they have the same outcome operators and
the same total operator. -/
@[ext] theorem SubMeas.ext {A B : SubMeas α R}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a)
    (htotal : A.total = B.total) :
    A = B := by
  obtain ⟨oA, tA, _, _, _⟩ := A
  obtain ⟨oB, tB, _, _, _⟩ := B
  obtain rfl : oA = oB := funext houtcome
  obtain rfl : tA = tB := htotal
  rfl

/-- Two measurements are equal when they have the same outcome operators. -/
@[ext] theorem Measurement.ext {A B : Measurement α R}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a) :
    A = B := by
  obtain ⟨A, hA⟩ := A
  obtain ⟨B, hB⟩ := B
  obtain rfl : A = B := SubMeas.ext houtcome (hA.trans hB.symm)
  rfl

/-- Two projective measurements are equal when they have the same outcome
operators. -/
@[ext] theorem ProjMeas.ext {A B : ProjMeas α R}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a) :
    A = B := by
  obtain ⟨A, _⟩ := A
  obtain ⟨B, _⟩ := B
  obtain rfl : A = B := Measurement.ext houtcome
  rfl

/-- A one-outcome submeasurement associated to a single positive operator
bounded by the identity. -/
def SubMeas.singleOutcome (A : R) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    SubMeas Unit R where
  outcome := fun _ => A
  total := A
  outcome_pos := fun _ => hA_pos
  sum_eq_total := Fintype.sum_unique fun _ => A
  total_le_one := hA_le_one

@[simp] theorem SubMeas.singleOutcome_outcome (A : R) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1)
    (u : Unit) :
    (SubMeas.singleOutcome A hA_pos hA_le_one).outcome u = A :=
  rfl

@[simp] theorem SubMeas.singleOutcome_total (A : R) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    (SubMeas.singleOutcome A hA_pos hA_le_one).total = A :=
  rfl

/-- A submeasurement is complete exactly when its outcome operators sum to `1`. -/
theorem SubMeas.sum_eq_one_iff_total_eq_one (A : SubMeas α R) :
    (∑ a, A.outcome a = 1) ↔ A.total = 1 := by
  rw [A.sum_eq_total]

/-- Promote a complete submeasurement to a measurement.

This is the explicit bridge from the paper's sub-measurement convention
`∑ a, A_a ≤ I` to the POVM convention `∑ a, A_a = I`: callers must supply the
completion proof rather than relying on a degenerate default. -/
def SubMeas.toMeasurement (A : SubMeas α R) (hcomplete : A.total = 1) :
    Measurement α R where
  toSubMeas := A
  total_eq_one := hcomplete

@[simp] theorem SubMeas.toMeasurement_toSubMeas (A : SubMeas α R) (hcomplete : A.total = 1) :
    (A.toMeasurement hcomplete).toSubMeas = A :=
  rfl

@[simp] theorem SubMeas.toMeasurement_outcome (A : SubMeas α R) (hcomplete : A.total = 1)
    (a : α) :
    (A.toMeasurement hcomplete).outcome a = A.outcome a :=
  rfl

/-- The outcome operators of a measurement sum to the identity. -/
theorem Measurement.sum_eq (M : Measurement α R) :
    ∑ a, M.outcome a = 1 := by
  rw [M.sum_eq_total, M.total_eq_one]

variable [StarOrderedRing R]

/-- Positive outcomes are self-adjoint. -/
theorem SubMeas.outcome_hermitian (A : SubMeas α R) (a : α) :
    star (A.outcome a) = A.outcome a :=
  (IsSelfAdjoint.of_nonneg (A.outcome_pos a)).star_eq

/-- Positive outcomes are self-adjoint. -/
theorem Measurement.outcome_hermitian (M : Measurement α R) (a : α) :
    star (M.outcome a) = M.outcome a :=
  SubMeas.outcome_hermitian M.toSubMeas a

/-- Every submeasurement outcome is bounded by the total operator. -/
theorem SubMeas.outcome_le_total (A : SubMeas α R) (a : α) :
    A.outcome a ≤ A.total :=
  (Finset.single_le_sum (fun i _ => A.outcome_pos i) (Finset.mem_univ a)).trans_eq
    A.sum_eq_total

/-- Each POVM element is bounded by the identity: `outcome a ≤ 1`.
Proof: `outcome a = 1 - ∑_{b ≠ a} outcome b ≤ 1` since all terms are positive. -/
theorem Measurement.outcome_le_one (M : Measurement α R) (a : α) :
    M.outcome a ≤ 1 :=
  (M.toSubMeas.outcome_le_total a).trans_eq M.total_eq_one

/-- Every submeasurement outcome is bounded by the identity. -/
theorem SubMeas.outcome_le_one (A : SubMeas α R) (a : α) :
    A.outcome a ≤ 1 :=
  le_trans (A.outcome_le_total a) A.total_le_one

/-- The total operator of a submeasurement is positive. -/
theorem SubMeas.total_nonneg (A : SubMeas α R) : 0 ≤ A.total := by
  rw [← A.sum_eq_total]
  exact Finset.sum_nonneg fun a _ => A.outcome_pos a

/-- Projective submeasurement outcomes are self-adjoint (positive by assumption). -/
theorem ProjSubMeas.outcome_hermitian (P : ProjSubMeas α R) (a : α) :
    star (P.outcome a) = P.outcome a :=
  SubMeas.outcome_hermitian P.toSubMeas a

/-- Projective measurement outcomes are self-adjoint (inherited from
`Measurement.outcome_pos`). -/
theorem ProjMeas.outcome_hermitian (P : ProjMeas α R) (a : α) :
    star (P.outcome a) = P.outcome a :=
  Measurement.outcome_hermitian P.toMeasurement a

end Derived

/-! ### Projective submeasurements in a C*-algebra -/

section Projective

variable {α : Type*} [Fintype α] {R : Type*} [CStarAlgebra R] [PartialOrder R]
  [StarOrderedRing R]

/-- Each projective outcome is absorbed by the total operator. -/
theorem ProjSubMeas.outcome_mul_total_eq_outcome (P : ProjSubMeas α R) (a : α) :
    P.outcome a * P.total = P.outcome a := by
  set Pa := P.outcome a
  -- the defect `Q = 1 - total` (the vendored `R`)
  set Q : R := 1 - P.total with hQ_def
  have hPa : IsSelfAdjoint Pa := P.outcome_hermitian a
  have hQ0 : 0 ≤ Q := sub_nonneg.2 P.total_le_one
  have hQ : IsSelfAdjoint Q := IsSelfAdjoint.of_nonneg hQ0
  have hQ_le : Q ≤ 1 - Pa := sub_le_sub_left (P.outcome_le_total a) 1
  have hPa_one_sub_Pa : Pa * (1 - Pa) * Pa = 0 := by
    rw [mul_sub, mul_one, P.proj a, sub_self, zero_mul]
  have hPaQPa : Pa * Q * Pa = 0 :=
    le_antisymm ((hPa.conjugate_le_conjugate hQ_le).trans_eq hPa_one_sub_Pa)
      (hPa.conjugate_nonneg hQ0)
  have hQ_sq_le : Q * Q ≤ Q := sq_le_self hQ0 (sub_le_self 1 P.toSubMeas.total_nonneg)
  have hQQ0 : 0 ≤ Q * Q := by simpa only [hQ.star_eq] using star_mul_self_nonneg Q
  have hQPa : Q * Pa = 0 := by
    rw [← CStarRing.star_mul_self_eq_zero_iff, star_mul, hPa.star_eq, hQ.star_eq,
      ← mul_assoc, mul_assoc Pa]
    exact le_antisymm ((hPa.conjugate_le_conjugate hQ_sq_le).trans_eq hPaQPa)
      (hPa.conjugate_nonneg hQQ0)
  have hPaQ : Pa * Q = 0 := by
    simpa only [star_mul, hPa.star_eq, hQ.star_eq, star_zero] using congrArg star hQPa
  calc
    Pa * P.total = Pa * (1 - Q) := by rw [hQ_def, sub_sub_cancel]
    _ = Pa := by rw [mul_sub, mul_one, hPaQ, sub_zero]

/-- The total operator of a projective submeasurement is itself a projector. -/
theorem ProjSubMeas.total_proj (P : ProjSubMeas α R) :
    P.total * P.total = P.total := by
  calc
    P.total * P.total = (∑ a : α, P.outcome a) * P.total := by rw [P.sum_eq_total]
    _ = ∑ a : α, P.outcome a * P.total := Finset.sum_mul _ _ _
    _ = ∑ a : α, P.outcome a :=
          Finset.sum_congr rfl fun a _ => P.outcome_mul_total_eq_outcome a
    _ = P.total := P.sum_eq_total

/-- Distinct outcomes of a projective submeasurement are orthogonal. -/
theorem ProjSubMeas.outcome_orthogonal (P : ProjSubMeas α R) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  classical
  set Pa := P.outcome a
  set Pb := P.outcome b
  have hsum : Pa + Pb ≤ P.total := by
    calc
      Pa + Pb = ∑ i ∈ ({a, b} : Finset α), P.outcome i := (Finset.sum_pair hab).symm
      _ ≤ ∑ i : α, P.outcome i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => P.outcome_pos i)
      _ = P.total := P.sum_eq_total
  have hPb_le : Pb ≤ 1 - Pa := by
    calc
      Pb = Pa + Pb - Pa := (add_sub_cancel_left Pa Pb).symm
      _ ≤ P.total - Pa := sub_le_sub_right hsum Pa
      _ ≤ 1 - Pa := sub_le_sub_right P.total_le_one Pa
  have hPa : IsSelfAdjoint Pa := P.outcome_hermitian a
  have hPb : IsSelfAdjoint Pb := P.outcome_hermitian b
  have hPa_idem : Pa * (1 - Pa) * Pa = 0 := by
    rw [mul_sub, mul_one, P.proj a, sub_self, zero_mul]
  have hPaPbPa_eq_zero : Pa * Pb * Pa = 0 :=
    le_antisymm ((hPa.conjugate_le_conjugate hPb_le).trans_eq hPa_idem)
      (hPa.conjugate_nonneg (P.outcome_pos b))
  have hPbPa_eq_zero : Pb * Pa = 0 := by
    rw [← CStarRing.star_mul_self_eq_zero_iff, star_mul, hPa.star_eq, hPb.star_eq,
      ← mul_assoc, mul_assoc Pa, P.proj b]
    exact hPaPbPa_eq_zero
  simpa only [star_mul, hPa.star_eq, hPb.star_eq, star_zero] using congrArg star hPbPa_eq_zero

/-- Distinct outcomes of a projective measurement are orthogonal. -/
theorem ProjMeas.outcome_orthogonal (P : ProjMeas α R) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 :=
  ProjSubMeas.outcome_orthogonal ⟨P.toSubMeas, P.proj⟩ a b hab

/-- Any two outcomes of a ProjMeas commute. -/
theorem ProjMeas.outcome_commute (P : ProjMeas α R) (a b : α) :
    P.outcome a * P.outcome b =
      P.outcome b * P.outcome a := by
  by_cases hab : a = b
  · subst hab; rfl
  · rw [P.outcome_orthogonal a b hab, P.outcome_orthogonal b a (Ne.symm hab)]

end Projective

/-! ### Images under `⋆`-homomorphisms

The port's placement of a local family on a tensor factor: `A.map S.L` is the vendored
`SubMeas.liftLeft A`, and `A.map S.R` the vendored `SubMeas.liftRight A`. -/

section Map

variable {α : Type*} [Fintype α]
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [PartialOrder R] [StarOrderedRing R]
  {T : Type*} [Ring T] [StarRing T] [Algebra ℂ T] [PartialOrder T] [StarOrderedRing T]

/-- The image of a submeasurement under a `⋆`-algebra homomorphism. -/
def SubMeas.map (f : R →⋆ₐ[ℂ] T) (A : SubMeas α R) : SubMeas α T where
  outcome a := f (A.outcome a)
  total := f A.total
  outcome_pos a := map_nonneg f (A.outcome_pos a)
  sum_eq_total := by rw [← map_sum, A.sum_eq_total]
  total_le_one := (OrderHomClass.mono f A.total_le_one).trans_eq (map_one f)

@[simp] theorem SubMeas.map_outcome (f : R →⋆ₐ[ℂ] T) (A : SubMeas α R) (a : α) :
    (A.map f).outcome a = f (A.outcome a) :=
  rfl

@[simp] theorem SubMeas.map_total (f : R →⋆ₐ[ℂ] T) (A : SubMeas α R) :
    (A.map f).total = f A.total :=
  rfl

/-- The image of a measurement under a `⋆`-algebra homomorphism. -/
def Measurement.map (f : R →⋆ₐ[ℂ] T) (M : Measurement α R) : Measurement α T where
  toSubMeas := M.toSubMeas.map f
  total_eq_one := (congrArg f M.total_eq_one).trans (map_one f)

@[simp] theorem Measurement.map_toSubMeas (f : R →⋆ₐ[ℂ] T) (M : Measurement α R) :
    (M.map f).toSubMeas = M.toSubMeas.map f :=
  rfl

@[simp] theorem Measurement.map_outcome (f : R →⋆ₐ[ℂ] T) (M : Measurement α R) (a : α) :
    (M.map f).outcome a = f (M.outcome a) :=
  rfl

/-- The image of a projective submeasurement under a `⋆`-algebra homomorphism. -/
def ProjSubMeas.map (f : R →⋆ₐ[ℂ] T) (P : ProjSubMeas α R) : ProjSubMeas α T where
  toSubMeas := P.toSubMeas.map f
  proj a := (map_mul f _ _).symm.trans (congrArg f (P.proj a))

@[simp] theorem ProjSubMeas.map_toSubMeas (f : R →⋆ₐ[ℂ] T) (P : ProjSubMeas α R) :
    (P.map f).toSubMeas = P.toSubMeas.map f :=
  rfl

/-- The image of a projective measurement under a `⋆`-algebra homomorphism. -/
def ProjMeas.map (f : R →⋆ₐ[ℂ] T) (P : ProjMeas α R) : ProjMeas α T where
  toMeasurement := P.toMeasurement.map f
  proj a := (map_mul f _ _).symm.trans (congrArg f (P.proj a))

@[simp] theorem ProjMeas.map_toMeasurement (f : R →⋆ₐ[ℂ] T) (P : ProjMeas α R) :
    (P.map f).toMeasurement = P.toMeasurement.map f :=
  rfl

end Map

/-! ### Bridges to `MIPRE.POVMIn` and `MIPRE.IsPVMIn` -/

section Bridge

variable {α : Type*} [Fintype α]

section POVM

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R]

/-- A positive operator valued measure of the repository as a measurement. -/
def Measurement.ofPOVMIn (P : POVMIn α R) : Measurement α R where
  outcome := P.op
  total := 1
  outcome_pos := P.op_nonneg
  sum_eq_total := P.sum_op
  total_le_one := le_rfl
  total_eq_one := rfl

@[simp] theorem Measurement.ofPOVMIn_outcome (P : POVMIn α R) (a : α) :
    (Measurement.ofPOVMIn P).outcome a = P.op a :=
  rfl

variable [StarOrderedRing R]

/-- A measurement as a positive operator valued measure of the repository
(`MIPRE/Foundations/Measurement.lean`). -/
def Measurement.toPOVMIn (M : Measurement α R) : POVMIn α R where
  mats a := ⟨M.outcome a, M.outcome_hermitian a⟩
  nonneg a := M.outcome_pos a
  normalized := Subtype.ext <| by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact M.sum_eq

@[simp] theorem Measurement.toPOVMIn_op (M : Measurement α R) (a : α) :
    M.toPOVMIn.op a = M.outcome a :=
  rfl

@[simp] theorem Measurement.ofPOVMIn_toPOVMIn (M : Measurement α R) :
    Measurement.ofPOVMIn M.toPOVMIn = M :=
  Measurement.ext fun _ => rfl

@[simp] theorem Measurement.toPOVMIn_ofPOVMIn (P : POVMIn α R) :
    (Measurement.ofPOVMIn P).toPOVMIn = P :=
  POVMIn.ext' fun _ => rfl

/-- A family of self-adjoint idempotents summing to one, mutually orthogonal, as a projective
measurement. -/
def ProjMeas.ofIsPVMIn (P : α → R) (h : IsPVMIn P) : ProjMeas α R where
  outcome := P
  total := 1
  outcome_pos := h.nonneg
  sum_eq_total := h.sum_eq_one
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := h.idem

@[simp] theorem ProjMeas.ofIsPVMIn_outcome (P : α → R) (h : IsPVMIn P) (a : α) :
    (ProjMeas.ofIsPVMIn P h).outcome a = P a :=
  rfl

end POVM

/-- **A projective measurement is a projective measurement of the repository**
(`MIPRE/Foundations/Measurement.lean`): orthogonality is `ProjSubMeas.outcome_orthogonal`. -/
theorem ProjMeas.isPVMIn {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    (P : ProjMeas α R) : IsPVMIn P.outcome where
  star_eq := P.outcome_hermitian
  idem := P.proj
  sum_eq_one := P.toMeasurement.sum_eq
  orthogonal hab := P.outcome_orthogonal _ _ hab

end Bridge

end MIPRE.LIDT.Co

end
