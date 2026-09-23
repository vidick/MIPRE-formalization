/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.GameTransport

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

/-- Literal equality of states under relabeling. Keeping the proposition named
avoids comparing concrete game parameters while elaborating dependent registers. -/
def RelabelStateEq : Prop := (S.relabel G' eX eY eA eB).ψ = S.ψ

/-- Relabeling has the identical state, as the named exact equality. -/
theorem relabelStateEq : S.RelabelStateEq G' eX eY eA eB := rfl

/-- Literal equality of one relabeled Alice effect with a selected original effect. -/
def RelabelPAEq (x' : X') (a' : A') (x : X) (a : A) : Prop :=
  (S.relabel G' eX eY eA eB).PA.M x' a' = S.PA.M x a

/-- Question and answer equalities identify the relabeled Alice effect. -/
theorem relabelPAEq (x' : X') (a' : A') (x : X) (a : A)
    (hx : eX x' = x) (ha : eA a' = a) : S.RelabelPAEq G' eX eY eA eB x' a' x a := by
  simp only [RelabelPAEq, relabel_PA_M, hx, ha]
  rfl

/-- Literal equality of one relabeled Bob effect with a selected original effect. -/
def RelabelPBEq (y' : Y') (b' : B') (y : Y) (b : B) : Prop :=
  (S.relabel G' eX eY eA eB).PB.M y' b' = S.PB.M y b

/-- Question and answer equalities identify the relabeled Bob effect. -/
theorem relabelPBEq (y' : Y') (b' : B') (y : Y) (b : B)
    (hy : eY y' = y) (hb : eB b' = b) : S.RelabelPBEq G' eX eY eA eB y' b' y b := by
  simp only [RelabelPBEq, relabel_PB_M, hy, hb]
  rfl

end MIPRE.TensorProductStrategy
