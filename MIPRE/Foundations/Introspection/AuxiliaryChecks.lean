/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.SamplingPrefix
import MIPRE.Foundations.Introspection.RegisterCoordinates
import MIPRE.Foundations.Introspection.Types

/-! # The concrete auxiliary introspection checks

These are the finite predicates in the sampling, hiding and original-game
tests. They operate on parsed answers. Byte parsing, the global length checks,
and clocked calls to the original programs are separate machine obligations.
In particular, prefixes are read from a claimed output without applying its
CL map again, and both tail projections in a hiding edge use the later answer.
-/

noncomputable section

namespace MIPRE.Introspection

open Finset Classical

variable {F ι A : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

namespace CLChecks

/-- Registers visited while reading the first `k` components of a claimed output. -/
def prefixRegister : {ℓ : ℕ} → CL.CLFun F ι ℓ → ℕ → (ι → F) → Finset ι
  | _, _, 0, _ => ∅
  | _, .zero, _ + 1, _ => ∅
  | _, .cons S _ next, k + 1, y =>
      S ∪ prefixRegister (next (CL.proj S y)) k (CL.proj Sᶜ y)

/-- The dual linear readout at a selected stage, in its actual local coordinates. -/
def dualReadout : {ℓ : ℕ} → CL.CLFun F ι ℓ → ℕ → (ι → F) → (ι → F) → (ι → F)
  | _, .zero, _, _, _ => 0
  | _, .cons S L _, 0, _, x =>
      coordinateInsert S (CL.lperp (coordinateLinear L) (coordinateRestrict S x))
  | _, .cons S _ next, k + 1, y, x =>
      dualReadout (next (CL.proj S y)) k (CL.proj Sᶜ y) x

/-- Even an arbitrary claimed output selects registers inside the presentation's support. -/
theorem prefixRegister_subset {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) : prefixRegister P k y ⊆ T := by
  induction P generalizing T k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      apply union_subset hP.1
      exact (ih _ (hP.2 _) k _).trans sdiff_subset

/-- Claimed-output prefix extraction is exactly projection onto the selected registers. -/
theorem proj_prefixRegister {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    CL.proj (prefixRegister P k y) y = P.outputPrefix k y := by
  induction P generalizing T k y with
  | zero => cases k <;> simp [prefixRegister, CL.CLFun.outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      have hU := prefixRegister_subset (hP.2 (CL.proj S y)) k (CL.proj Sᶜ y)
      have hc : prefixRegister (next (CL.proj S y)) k (CL.proj Sᶜ y) ⊆ Sᶜ := by
        intro i hi
        exact mem_compl.mpr (mem_sdiff.mp (hU hi)).2
      have hd : Disjoint S (prefixRegister (next (CL.proj S y)) k (CL.proj Sᶜ y)) :=
        disjoint_of_subset_right hc disjoint_compl_right
      rw [prefixRegister, CL.proj_union_of_disjoint hd, CL.CLFun.outputPrefix_cons,
        ← ih _ (hP.2 _) k (CL.proj Sᶜ y), CL.proj_proj_of_subset hc]

/-- Every full-length claimed output selects the full partition, including nonimage outputs. -/
theorem prefixRegister_full {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) (y : ι → F) : prefixRegister P ℓ y = T := by
  induction P generalizing T y with
  | zero => simpa [prefixRegister] using hP.symm
  | cons S L next ih =>
    rw [prefixRegister, ih _ (hP.2 _) _]
    exact union_sdiff_of_subset hP.1

/-- The sampling-introspection check retains the original answer as well as the question. -/
def sampling (P : CL.CLFun F ι ℓ) (u v : (ι → F) × A) : Prop :=
  u.1 = P.eval v.1 ∧ u.2 = v.2

/-- The reading-introspection check forgets only the dual readout. -/
def reading (u : (ι → F) × A) (v : (ι → F) × (ι → F) × A) : Prop :=
  u.1 = v.1 ∧ u.2 = v.2.2

/-- The last hiding measurement and Read agree on the earlier question and full dual answer. -/
def hidingRead (P : CL.CLFun F ι ℓ)
    (u : (ι → F) × (ι → F) × (ι → F)) (v : (ι → F) × (ι → F) × A) : Prop :=
  P.outputPrefix (ℓ - 1) u.1 = P.outputPrefix (ℓ - 1) v.1 ∧ u.2.1 = v.2.1

/-- The four comparisons on the edge from hiding level `k+1` to `k+2`.
The later player's question fixes both tail projections and the new dual map. -/
def hidingNext (P : CL.CLFun F ι ℓ) (k : ℕ)
    (u v : (ι → F) × (ι → F) × (ι → F)) : Prop :=
  P.outputPrefix k u.1 = P.outputPrefix k v.1 ∧
    CL.proj (prefixRegister P (k + 1) v.1) u.2.1 =
      CL.proj (prefixRegister P (k + 1) v.1) v.2.1 ∧
    CL.proj (prefixRegister P (k + 2) v.1)ᶜ u.2.2 =
      CL.proj (prefixRegister P (k + 2) v.1)ᶜ v.2.2 ∧
    CL.proj (P.factorOfPrefix (k + 1) (P.outputPrefix (k + 1) v.1)) v.2.1 =
      dualReadout P (k + 1) v.1 u.2.2

/-- The first hiding edge compares with the Pauli-X answer on the original register. -/
def hidingPauli (P : CL.CLFun F ι ℓ) (x : ι → F)
    (v : (ι → F) × (ι → F) × (ι → F)) : Prop :=
  CL.proj (P.factorOfPrefix 0 0) v.2.1 = dualReadout P 0 0 x ∧
    CL.proj (P.factorOfPrefix 0 0)ᶜ x = CL.proj (P.factorOfPrefix 0 0)ᶜ v.2.2

/-- Acceptance of the full sampling check implies every prefix comparison,
including outcomes outside the honest image on the introspecting side. -/
theorem sampling_prefix {P : CL.CLFun F ι ℓ} (hP : P.SupportedOn univ)
    {u v : (ι → F) × A} (h : sampling P u v) (k : ℕ) :
    (P.outputPrefix k u.1, u.2) = ((P.truncate k).eval v.1, v.2) := by
  rcases h with ⟨hy, ha⟩
  rw [hy, hP.outputPrefix_eval, ha]

/-- The first hiding marginal is exactly the tested coarsening of the Pauli-X answer. -/
theorem hidingPauli_coarse {P : CL.CLFun F ι ℓ} {x : ι → F}
    {v : (ι → F) × (ι → F) × (ι → F)} (h : hidingPauli P x v) :
    (CL.proj (P.factorOfPrefix 0 0) v.2.1, CL.proj (P.factorOfPrefix 0 0)ᶜ v.2.2) =
      (dualReadout P 0 0 x, CL.proj (P.factorOfPrefix 0 0)ᶜ x) :=
  Prod.ext h.1 h.2.symm

/-- The checked adjacent hiding answers share their coarse prefix/dual/tail data. -/
theorem hidingNext_coarse {P : CL.CLFun F ι ℓ} {k : ℕ}
    {u v : (ι → F) × (ι → F) × (ι → F)} (h : hidingNext P k u v) :
    (P.outputPrefix k u.1, CL.proj (prefixRegister P (k + 1) v.1) u.2.1,
      CL.proj (prefixRegister P (k + 2) v.1)ᶜ u.2.2) =
    (P.outputPrefix k v.1, CL.proj (prefixRegister P (k + 1) v.1) v.2.1,
      CL.proj (prefixRegister P (k + 2) v.1)ᶜ v.2.2) :=
  Prod.ext h.1 (Prod.ext h.2.1 h.2.2.1)

end CLChecks

end MIPRE.Introspection

end
