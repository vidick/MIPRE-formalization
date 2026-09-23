/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Downsize
import MIPRE.Foundations.Introspection.AdaptiveResidual

/-! # Coordinate transport of adaptive auxiliary registers

These identities transport the actual coordinate bijection, including on
unattained claimed outputs. They do not identify canonical dual representatives.
-/

noncomputable section
namespace MIPRE.Introspection.CLChecks
open Finset CL
variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] {ℓ : ℕ}

theorem map_compl (e : ι ≃ κ) (S : Finset ι) :
    (Sᶜ).map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext i
  simp only [mem_map_equiv, mem_compl]

theorem outputPrefix_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (P.reindex e).outputPrefix k (reindexEquiv e y) =
      reindexEquiv e (P.outputPrefix k y) := by
  induction P generalizing k y with
  | zero => cases k <;> simp [CLFun.outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [CLFun.reindex_cons, CLFun.outputPrefix_cons, CLFun.outputPrefix_cons,
        ← map_compl, ← reindexEquiv_proj, ← reindexEquiv_proj,
        LinearEquiv.symm_apply_apply, ih, map_add]

theorem prefixRegister_reindex (e : ι ≃ κ) (P : CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixRegister (P.reindex e) k (reindexEquiv e y) =
      (prefixRegister P k y).map e.toEmbedding := by
  induction P generalizing k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      rw [CLFun.reindex_cons]
      simp only [prefixRegister]
      rw [← map_compl, ← reindexEquiv_proj, ← reindexEquiv_proj,
        LinearEquiv.symm_apply_apply, ih, map_union]

end MIPRE.Introspection.CLChecks
end
