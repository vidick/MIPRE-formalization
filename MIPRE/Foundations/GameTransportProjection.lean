/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Foundations.GameTransport

@[expose] public section

/-! # Projections of relabeled tensor-product strategies

These equations expose the unchanged registers and state without unfolding the
game carried by a strategy. Measurement equations expose only the relabeling.
-/

namespace MIPRE.TensorProductStrategy

variable {X Y A B X' Y' A' B' : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
  {G : Game X Y A B} (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
  (eX : X' → X) (eY : Y' → Y) (eA : A' ≃ A) (eB : B' ≃ B)

/-- Relabeling preserves Alice's register dimension. -/
@[simp] theorem relabel_dA : (S.relabel G' eX eY eA eB).dA = S.dA := rfl

/-- Relabeling preserves Bob's register dimension. -/
@[simp] theorem relabel_dB : (S.relabel G' eX eY eA eB).dB = S.dB := rfl

/-- Relabeling preserves the literal shared state. -/
@[simp] theorem relabel_ψ : (S.relabel G' eX eY eA eB).ψ = S.ψ := rfl

/-- Alice's relabeled effects are the original effects at relabeled questions and answers. -/
@[simp] theorem relabel_PA_M (x : X') (a : A') :
    (S.relabel G' eX eY eA eB).PA.M x a = S.PA.M (eX x) (eA a) := rfl

/-- Bob's relabeled effects are the original effects at relabeled questions and answers. -/
@[simp] theorem relabel_PB_M (y : Y') (b : B') :
    (S.relabel G' eX eY eA eB).PB.M y b = S.PB.M (eY y) (eB b) := rfl

end MIPRE.TensorProductStrategy

end
