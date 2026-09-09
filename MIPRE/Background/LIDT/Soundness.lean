/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.LIDT.Game
import MIPRE.Background.LIDT.Bridge.Main

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
`MIPRE.Background.LIDT.Bridge` (`Bridge.soundness`), which translates our game,
strategies, measurements and consistency relation into MIPStarRE's and back.
-/

namespace MIPRE.LIDT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

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
          lidtError m d (Fintype.card F) k ε :=
  Bridge.soundness S ε hS k hk hk0

end MIPRE.LIDT
