/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game
import MIPRE.Foundations.Distances

/-!
# Quantum soundness of the classical low individual degree test

Theorem `thm:main-formal` of Ji, Natarajan, Vidick, Wright, Yuen, *Quantum soundness of
the classical low individual degree test* (arXiv:2009.12982), for the game
`MIPRE.LIDT.lidtGame`: a strategy passing the test with probability `≥ 1 - ε` has point
measurements consistent, up to the error `lidtError`, with the evaluations of a single
projective measurement with outcomes in the polynomials of individual degree `≤ d` (one
per player, the two being consistent with each other).

Two corrections to the printed statement, established by the MIPStarRE formalization
(`MIPRE.Background.LIDT.MIPStarRE`), are built in: the sampling parameter `k` satisfies
`400·m·d ≤ k` (the paper prints `m·d ≤ k`) and `0 < k`. The parameter `k` is free, since
the error has both a factor `k²` and a term `exp(−k / (2560000 m²))`.

The proof is delegated to `MIPStarRE.LDT.Test.mainFormal` through the bridge in
`MIPRE.Background.LIDT.Bridge`; until the bridge is complete the proof is `sorry`.
-/

namespace MIPRE.LIDT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-- Polynomials in `m` variables of individual degree at most `d`, given by their
coefficients on the monomials `∏ᵢ Xᵢ^(eᵢ)` with all `eᵢ ≤ d`. -/
abbrev LowIndDegPoly := (Fin m → Fin (d + 1)) → F

/-- Evaluation at a point of `F^m`. -/
def LowIndDegPoly.eval (p : LowIndDegPoly (F := F) (m := m) (d := d)) (u : Point F m) : F :=
  ∑ e, p e * ∏ i, u i ^ (e i : ℕ)

/-- The field element answered to a point question; ill-typed answers are read as `0`
(they are rejected by the test, so this only helps the strategy). -/
def Answer.toValue : Answer F m d → F
  | .value a => a
  | _ => 0

/-- The point measurements of player A in a strategy for the test, as POVMs with outcomes
in `F`. -/
noncomputable def pointPOVMA (S : TensorProductStrategy (lidtGame F m d)) (u : Point F m) :
    POVM F (Fin S.dA) :=
  (S.PA.toPOVM (.point u)).map Answer.toValue

/-- The point measurements of player B in a strategy for the test, as POVMs with outcomes
in `F`. -/
noncomputable def pointPOVMB (S : TensorProductStrategy (lidtGame F m d)) (u : Point F m) :
    POVM F (Fin S.dB) :=
  (S.PB.toPOVM (.point u)).map Answer.toValue

/-- Evaluation at `u` of a measurement `G` with polynomial outcomes: the POVM with outcomes
in `F` whose operator for `a` is the sum of the operators of the polynomials `p` with
`p(u) = a`. -/
noncomputable def evalPOVM {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d)) (Matrix n n ℂ))
    (u : Point F m) : POVM F n :=
  (G.toPOVM ()).map fun p => p.eval u

/-- The error bound of the soundness theorem, as proved in the MIPStarRE development:
`100000 · k² · m⁴ · (ε^(1/40000) + (d/q)^(1/40000) + exp(−k / (2560000 m²)))`. -/
noncomputable def lidtError (m d q k : ℕ) (ε : ℝ) : ℝ :=
  100000 * (k : ℝ) ^ 2 * (m : ℝ) ^ 4 *
    (ε ^ (1 / 40000 : ℝ) + ((d : ℝ) / q) ^ (1 / 40000 : ℝ) +
      Real.exp (-(k : ℝ) / (2560000 * (m : ℝ) ^ 2)))

/-- **Quantum soundness of the classical low individual degree test**
(JNVWY21qld, `thm:main-formal`, with the corrections `400·m·d ≤ k` and `0 < k`).

If a strategy `S` for the `(m, q, d)`-low individual degree test, `q = |F|`, passes with
probability at least `1 - ε`, and `k ≥ 400·m·d` is positive, then there are projective
measurements `GA`, `GB` on the two players' spaces with outcomes in the polynomials of
individual degree at most `d` such that, with `δ = lidtError m d q k ε` and for a uniform
point `u`: A's point measurement at `u` is `δ`-consistent with `GB` evaluated at `u`,
`GA` evaluated at `u` is `δ`-consistent with B's point measurement at `u`, and `GA` and
`GB` are `δ`-consistent. Consistency is `MIPRE.inconsistency`,
`𝔼_{x∼μ} ∑_{a≠b} ⟨ψ| M^x_a ⊗ N^x_b |ψ⟩`. -/
theorem lowIndividualDegree_soundness
    (S : TensorProductStrategy (lidtGame F m d)) (ε : ℝ) (hS : 1 - ε ≤ S.value)
    (k : ℕ) (hk : 400 * m * d ≤ k) (hk0 : 0 < k) :
    ∃ GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dA) (Fin S.dA) ℂ),
    ∃ GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d))
        (Matrix (Fin S.dB) (Fin S.dB) ℂ),
      inconsistency (uniform (Point F m)) S.ψ (pointPOVMA S) (evalPOVM GB) ≤
          lidtError m d (Fintype.card F) k ε ∧
        inconsistency (uniform (Point F m)) S.ψ (evalPOVM GA) (pointPOVMB S) ≤
          lidtError m d (Fintype.card F) k ε ∧
        inconsistency (uniform Unit) S.ψ (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) ≤
          lidtError m d (Fintype.card F) k ε := by
  sorry

end MIPRE.LIDT
