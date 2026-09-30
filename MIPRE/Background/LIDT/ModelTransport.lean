/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.ModelIso
public import MIPRE.Background.LIDT.ModelSoundness

@[expose] public section

/-!
# The low-individual-degree test, moved between models

`LIDT.Simul.SoundIn M` (`MIPRE/Background/LIDT/ModelSoundness.lean`) is stated through the
Born probabilities of `M`'s projective measurements, so it is a property of the model up to
isomorphism (`BipartiteModel.Iso`): a strategy of `M` is pushed forward along the isomorphism with
its value, the extracted measurements are pulled back along its inverse, and the three
inconsistencies are carried over (`SoundIn.of_iso`). The seeded CL test is symmetric in the
players --- the verifier samples an ordered pair of types uniformly, and every subtest is written
in both orientations (`CL.clGame_μ_swap`, `CL.clGame_D_swap`) --- so soundness passes to the
model with the players exchanged (`SoundIn.swap`).

Three consequences for the models the Pauli basis test builds:

* the test is sound in the tensor-product model of a state on **any** finite factors
  (`soundIn_tensor_fintype`), `soundIn_tensor` read along a numbering of the factors;
* it is sound in every **ancilla extension of a tensor-product model**
  (`soundIn_expand_tensor`), the extension being the tensor-product model of the expanded vector;
* soundness in every extension of a model gives soundness in every extension of the model with the
  players exchanged (`soundIn_swap_expand`, and `soundIn_swap_expand_of_norm` for extensions by unit
  vectors).
-/

noncomputable section

/-! ## The symmetry of the seeded CL test -/

namespace MIPRE.LIDT.CL

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}

/-- A sample with the two players' types exchanged. -/
def Sample.swapTy (sm : Sample F m) : Sample F m := { sm with tyA := sm.tyB, tyB := sm.tyA }

/-- The exchange of the two players' types, an involution of the samples. -/
def Sample.swapTyEquiv : Sample F m ≃ Sample F m where
  toFun := Sample.swapTy
  invFun := Sample.swapTy
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The subtests are symmetric in the players**: each is written in both orientations, and
agreement is symmetric. -/
theorem subtests_swap [NeZero m] (hm : m ∣ Fintype.card F) (x y : Question F m)
    (a b : Answer F m d ldc) : subtests hm x y a b = subtests hm y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;> simp only [subtests, decide_eq_decide] <;>
    exact eq_comm

/-- **The decision predicate is symmetric in the players.** -/
theorem accepts_swap [NeZero m] (hm : m ∣ Fintype.card F) (x y : Question F m)
    (a b : Answer F m d ldc) : accepts hm x y a b = accepts hm y x b a := by
  rw [accepts, accepts, subtests_swap hm x y a b, Bool.and_comm (x.fmtOk a)]

/-- **The question distribution is symmetric in the players**: exchanging the two types is a
bijection of the samples. -/
theorem clGame_μ_swap [NeZero m] (hm : m ∣ Fintype.card F) (x y : Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y = (clGame (d := d) (ldc := ldc) hm).μ y x := by
  show ∑ sm : Sample F m, _ = ∑ sm : Sample F m, _
  refine Fintype.sum_equiv Sample.swapTyEquiv _ _ fun sm => ?_
  congr 1
  show (if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then (1 : ℝ) else 0) =
    if (sm.question hm sm.tyB, sm.question hm sm.tyA) = (y, x) then 1 else 0
  simp only [Prod.mk.injEq, and_comm]

/-- **The seeded CL test accepts the exchanged answers to the exchanged questions.** -/
theorem clGame_D_swap [NeZero m] (hm : m ∣ Fintype.card F) (x y : Question F m)
    (a b : Answer F m d ldc) :
    (clGame (d := d) (ldc := ldc) hm).D x y a b = (clGame (d := d) (ldc := ldc) hm).D y x b a :=
  accepts_swap hm x y a b

end MIPRE.LIDT.CL

/-! ## Soundness in a model, up to isomorphism and exchange -/

namespace MIPRE.LIDT.Simul

open Finset MIPRE.LIDT.CL
open scoped MatrixOrder

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {𝒞' 𝒜' ℬ' : Type*} [Ring 𝒞'] [StarRing 𝒞'] [Algebra ℂ 𝒞'] [Ring 𝒜'] [StarRing 𝒜']
  [Algebra ℂ 𝒜'] [Ring ℬ'] [StarRing ℬ'] [Algebra ℂ ℬ'] [PartialOrder 𝒜'] [StarOrderedRing 𝒜']
  [PartialOrder ℬ'] [StarOrderedRing ℬ'] {M' : BipartiteModel 𝒞' 𝒜' ℬ'}

section Readings

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m d r : ℕ} [NeZero m]
  {hm : m ∣ Fintype.card F}

/-- The first player's point measurements of a pushed-forward strategy are pushed forward. -/
theorem tuplePOVMAIn_pushStrat (Φ : BipartiteModel.Iso M M')
    (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) (y : Point F m) (a : Fin r → F) :
    (tuplePOVMAIn hm (Φ.pushStrat S) y).op a = Φ.ΦA ((tuplePOVMAIn hm S y).op a) := by
  simp only [tuplePOVMAIn, POVMIn.map_op, map_sum, BipartiteModel.Iso.pushStrat_PA,
    BipartiteModel.Iso.pushA_op]

/-- The second player's point measurements of a pushed-forward strategy are pushed forward. -/
theorem tuplePOVMBIn_pushStrat (Φ : BipartiteModel.Iso M M')
    (S : M.ProjStrat (clGame (d := d) (ldc := r) hm)) (y : Point F m) (b : Fin r → F) :
    (tuplePOVMBIn hm (Φ.pushStrat S) y).op b = Φ.ΦB ((tuplePOVMBIn hm S y).op b) := by
  simp only [tuplePOVMBIn, POVMIn.map_op, map_sum, BipartiteModel.Iso.pushStrat_PB,
    BipartiteModel.Iso.pushB_op]

omit [NeZero m] [PartialOrder ℬ] [StarOrderedRing ℬ] [PartialOrder ℬ'] [StarOrderedRing ℬ'] in
/-- The evaluations of a measurement of the first player pulled back along the inverse. -/
theorem evalTuplePOVMIn_symm_pushA (Φ : BipartiteModel.Iso M M')
    (G : POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) 𝒜') (y : Point F m)
    (a : Fin r → F) :
    (evalTuplePOVMIn G y).op a = Φ.ΦA ((evalTuplePOVMIn (Φ.symm.pushA G) y).op a) := by
  simp only [evalTuplePOVMIn, POVMIn.map_op, map_sum, BipartiteModel.Iso.pushA_op,
    BipartiteModel.Iso.symm_ΦA, StarAlgEquiv.apply_symm_apply]

omit [NeZero m] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [PartialOrder 𝒜'] [StarOrderedRing 𝒜'] in
/-- The evaluations of a measurement of the second player pulled back along the inverse. -/
theorem evalTuplePOVMIn_symm_pushB (Φ : BipartiteModel.Iso M M')
    (G : POVMIn (Fin r → LowIndDegPoly (F := F) (m := m) (d := d)) ℬ') (y : Point F m)
    (b : Fin r → F) :
    (evalTuplePOVMIn G y).op b = Φ.ΦB ((evalTuplePOVMIn (Φ.symm.pushB G) y).op b) := by
  simp only [evalTuplePOVMIn, POVMIn.map_op, map_sum, BipartiteModel.Iso.pushB_op,
    BipartiteModel.Iso.symm_ΦB, StarAlgEquiv.apply_symm_apply]

end Readings

/-- **Soundness passes along an isomorphism**: a strategy of `M` is pushed forward to `M'` with its
value, the measurements `M'`'s soundness extracts are pulled back along the inverse, and the
three inconsistencies are carried over. -/
theorem SoundIn.of_iso (Φ : BipartiteModel.Iso M M') (h : SoundIn M') : SoundIn M := by
  intro F _ _ _ m d r k _ hq hm hd hr S ε hε hS
  obtain ⟨GA, GB, hGA, hGB, h1, h2, h3⟩ :=
    h hq hm hd hr (Φ.pushStrat S) ε hε (by rw [Φ.value_pushStrat]; exact hS)
  refine ⟨Φ.symm.pushA GA, Φ.symm.pushB GB, Φ.symm.isPVMIn_pushA hGA, Φ.symm.isPVMIn_pushB hGB,
    ?_, ?_, ?_⟩
  · refine le_of_eq_of_le ?_ h1
    exact (Φ.inconsistency_eq _ (tuplePOVMAIn_pushStrat Φ S)
      (evalTuplePOVMIn_symm_pushB Φ GB)).symm
  · refine le_of_eq_of_le ?_ h2
    exact (Φ.inconsistency_eq _ (evalTuplePOVMIn_symm_pushA Φ GA)
      (tuplePOVMBIn_pushStrat Φ S)).symm
  · refine le_of_eq_of_le ?_ h3
    exact (Φ.inconsistency_eq _ (fun _ a => (Φ.ΦA.apply_symm_apply (GA.op a)).symm)
      (fun _ b => (Φ.ΦB.apply_symm_apply (GB.op b)).symm)).symm

/-- **Soundness is invariant under isomorphism.** -/
theorem SoundIn.iff_of_iso (Φ : BipartiteModel.Iso M M') : SoundIn M ↔ SoundIn M' :=
  ⟨SoundIn.of_iso Φ.symm, SoundIn.of_iso Φ⟩

/-- **Soundness passes to the model with the players exchanged**: the seeded CL test is symmetric
in the players (`CL.clGame_μ_swap`, `CL.clGame_D_swap`), so a strategy of the exchanged model is
one of the model with the same value (`BipartiteModel.ProjStrat.value_swap`), and the measurements
extracted for it serve, exchanged, with the inconsistencies exchanged
(`BipartiteModel.inconsistency_swap`). -/
theorem SoundIn.swap (h : SoundIn M) : SoundIn M.swap := by
  intro F _ _ _ m d r k _ hq hm hd hr S ε hε hS
  let S' : M.ProjStrat (clGame hm) := S.swap (clGame hm)
  have hS' : S'.value = S.value :=
    S.value_swap (fun x y => clGame_μ_swap hm y x) fun x y a b => clGame_D_swap hm y x b a
  obtain ⟨GA, GB, hGA, hGB, h1, h2, h3⟩ := h hq hm hd hr S' ε hε (hS'.symm ▸ hS)
  refine ⟨GB, GA, hGB, hGA, ?_, ?_, ?_⟩
  · rw [BipartiteModel.inconsistency_swap]
    exact h2
  · rw [BipartiteModel.inconsistency_swap]
    exact h1
  · rw [BipartiteModel.inconsistency_swap]
    exact h3

/-! ## Tensor-product models on any finite factors, and their extensions -/

/-- **The seeded CL test is sound in the tensor-product model of a state on any finite factors**:
`soundIn_tensor`, along a numbering of the two factors (`BipartiteModel.tensorReindexIso`). -/
theorem soundIn_tensor_fintype {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : dA × dB → ℂ) : SoundIn (BipartiteModel.tensor ψ) :=
  SoundIn.of_iso (BipartiteModel.tensorReindexIso (Fintype.equivFin dA) (Fintype.equivFin dB) ψ)
    (soundIn_tensor _)

/-- **The seeded CL test is sound in every extension of a tensor-product model**: the extension is
the tensor-product model of the expanded vector (`BipartiteModel.tensorExpandIso`). -/
theorem soundIn_expand_tensor {dA dB α β : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ψ : dA × dB → ℂ)
    (e : α × β → ℂ) : SoundIn ((BipartiteModel.tensor ψ).expand e) :=
  SoundIn.of_iso (BipartiteModel.tensorExpandIso ψ e) (soundIn_tensor_fintype _)

/-! ## Extensions of the model with the players exchanged -/

section SwapExpand

variable [StarProper 𝒜] [StarProper ℬ]

/-- **Soundness in the extensions of a model gives soundness in the extensions of the model with
the players exchanged**: the extension of the exchanged model in `e` is the exchanged extension in
`e` read backwards (`BipartiteModel.swapExpandIso`). -/
theorem soundIn_swap_expand
    (h : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), SoundIn (M.expand e))
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α × β → ℂ) :
    SoundIn (M.swap.expand e) :=
  SoundIn.of_iso (M.swapExpandIso (e ∘ Prod.swap)).symm (SoundIn.swap (h (e ∘ Prod.swap)))

/-- `soundIn_swap_expand` for the extensions by unit vectors. -/
theorem soundIn_swap_expand_of_norm
    (h : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (e : α × β → ℂ), ‖evec e‖ = 1 → SoundIn (M.expand e))
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (e : α × β → ℂ)
    (he : ‖evec e‖ = 1) : SoundIn (M.swap.expand e) :=
  SoundIn.of_iso (M.swapExpandIso (e ∘ Prod.swap)).symm
    (SoundIn.swap (h (e ∘ Prod.swap) ((norm_evec_comp_swap e).trans he)))

end SwapExpand

end MIPRE.LIDT.Simul

end

end
