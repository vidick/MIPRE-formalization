/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.TypeEncoding

/-! # Faithful finite routing of the Pauli decision rules

Only the fixed twenty-six types are tabulated. The route retains orientation,
basis and actual Magic Square indices. Equal-type consistency is selected only
for equal types, and every edge selects a substantive rule rather than the
off-graph default. Field computations remain uniform programs supplied by the
caller; this finite dispatcher never tabulates field elements or answers.
-/

noncomputable section
namespace MIPRE.QLD.PauliBranchProgram
open Cost Cost.PolyTimeFun SAT

/-- Rule number, orientation reversal, primary index, secondary index.
Rules zero through seven are consistency and the seven rules of `pairTest`;
eight is its unconditional off-graph fallback. -/
abbrev Route := ℕ × Bool × ℕ × ℕ

def basisIndex : Bas → ℕ
  | .X => 0
  | .Z => 1

def pairRoute : Ty → Ty → Route
  | .point W, .aline W' => if W = W' then (1, false, basisIndex W, 0) else (8, false, 0, 0)
  | .aline W', .point W => if W = W' then (1, true, basisIndex W, 0) else (8, false, 0, 0)
  | .point W, .dline W' => if W = W' then (2, false, basisIndex W, 0) else (8, false, 0, 0)
  | .dline W', .point W => if W = W' then (2, true, basisIndex W, 0) else (8, false, 0, 0)
  | .point W, .pauli W' => if W = W' then (3, false, basisIndex W, 0) else (8, false, 0, 0)
  | .pauli W', .point W => if W = W' then (3, true, basisIndex W, 0) else (8, false, 0, 0)
  | .pairB W, .pair => (4, false, basisIndex W, 0)
  | .pair, .pairB W => (4, true, basisIndex W, 0)
  | .point W, .pairB W' => if W = W' then (5, false, basisIndex W, 0) else (8, false, 0, 0)
  | .pairB W', .point W => if W = W' then (5, true, basisIndex W, 0) else (8, false, 0, 0)
  | .con i, .var j => (6, false, i.val, j.val)
  | .var j, .con i => (6, true, i.val, j.val)
  | .point W, .var j => (7, false, basisIndex W, j.val)
  | .var j, .point W => (7, true, basisIndex W, j.val)
  | _, _ => (8, false, 0, 0)

def route (T U : Ty) : Route :=
  if T = U then (0, false, 0, 0) else pairRoute T U

def routeProg : PolyTimeFun (Ty × Ty) Route :=
  finiteFunction (fun p => route p.1 p.2)

@[simp] theorem routeProg_apply (T U : Ty) : routeProg (T, U) = route T U := rfl

theorem consistency_iff (T U : Ty) : (route T U).1 = 0 ↔ T = U := by
  revert T U
  decide

theorem route_lt_nine (T U : Ty) : (route T U).1 < 9 := by
  revert T U
  decide

/-- In particular no two different constraint or variable indices become a
consistency test, despite sharing the same sampling stages and answer format. -/
theorem route_adj (T U : Ty) (h : adj T U = true) : (route T U).1 < 8 := by
  revert T U
  decide

theorem route_con_var (i : Fin LCS.MagicSquare.layout.r)
    (j : Fin LCS.MagicSquare.layout.s) :
    route (.con i) (.var j) = (6, false, i.val, j.val) := by
  simp [route, pairRoute]

theorem route_var_con (i : Fin LCS.MagicSquare.layout.r)
    (j : Fin LCS.MagicSquare.layout.s) :
    route (.var j) (.con i) = (6, true, i.val, j.val) := by
  simp [route, pairRoute]

/-- The first eight supplied Boolean checks have the order of the route
numbers. The finite fallback is `true`, exactly as in `pairTest`. -/
def selectProg : PolyTimeFun (Route × List Bool) Bool :=
  (ArrayProg.getD true).comp ((fst.comp fst).pair snd)

theorem selectProg_apply (r : Route) (checks : List Bool) :
    selectProg (r, checks) = checks.getD r.1 true := rfl

def dispatchProg : PolyTimeFun ((Ty × Ty) × List Bool) Bool :=
  selectProg.comp ((routeProg.comp fst).pair snd)

theorem dispatchProg_apply (T U : Ty) (checks : List Bool) :
    dispatchProg ((T, U), checks) = checks.getD (route T U).1 true := rfl

/-- Put the distinguished point, half-pair or constraint on the left before
calling the corresponding uniform field/bit check. -/
def orientProg {α : Type*} [SizedEncoding α] : PolyTimeFun (Bool × α × α) (α × α) :=
  ite fst ((snd.comp snd).pair (fst.comp snd))
    ((fst.comp snd).pair (snd.comp snd))

theorem orientProg_apply {α : Type*} [SizedEncoding α] (swap : Bool) (a b : α) :
    orientProg (swap, a, b) = if swap then (b, a) else (a, b) := rfl

/-- Reject either malformed payload before using the selected Boolean rule. -/
def formatGuard : PolyTimeFun (Bool × Bool × Bool) Bool :=
  ite fst (ite (fst.comp snd) (snd.comp snd) (const false)) (const false)

theorem formatGuard_apply (ha hb result : Bool) :
    formatGuard (ha, hb, result) = (ha && hb && result) := by
  cases ha <;> cases hb <;> rfl

end MIPRE.QLD.PauliBranchProgram
end
