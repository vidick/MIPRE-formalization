/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# The parameter regime of `thm:qld`

Stage 4 of the appendix runs at the padded dimension `4m`, so it needs `4m | q`; the theorem is
stated for every tuple with `m | q`. The paper closes the gap in a `\cnote` of `qld-combining.tex`
("admissibility makes `m` a power of two") and `lem:qld-global-setup` lists `4m | q` beside the
regime `16md <= q` as though it were a further hypothesis. Neither says what the derivation uses,
and the derivation is short enough to be worth getting exactly right, because the obvious reading
of it is false.

**`m | q` and `q` a power of two do not give `4m | q`.** Take `m = q`. What they give is that `m`
is itself a power of two, `m = 2^j` with `2^j | 2^n`; `4m = 2^{j+2}` then divides `2^n` exactly when
`j + 2 <= n`, which is `4m <= q`. So the size condition is load-bearing, and it is the *regime*
that supplies it: `48 m d <= q` with `d >= 1` gives `4m <= q`. Outside the regime the theorem takes
the trivial bound and never needs `4m | q`, which is why the derivation is only ever made inside it.

**And "admissible" is not needed at all.** The paper's admissible sizes are `q = 2^t` with `t`
odd; the oddness is for the self-dual basis. What this step uses is only that `q` is a power of
two, and a finite field of characteristic two has that for free (`FiniteField.card`). The
characteristic-two hypothesis `[Algebra (ZMod 2) F]` is already on every declaration of the
appendix, so the step costs no hypothesis the theorem does not already carry.
-/

namespace MIPRE.QLD

variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- **The field size is a power of two**: a finite field of characteristic two. -/
theorem exists_card_eq_two_pow : ∃ n : ℕ, Fintype.card F = 2 ^ n := by
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, hn⟩

/-- **A divisor of the field size is a power of two.** This is the content of the paper's
`\cnote` that admissibility makes `m` a power of two, and it needs characteristic two only. -/
theorem exists_eq_two_pow_of_dvd_card {m : ℕ} (hm : m ∣ Fintype.card F) :
    ∃ j : ℕ, m = 2 ^ j := by
  obtain ⟨n, hn⟩ := exists_card_eq_two_pow (F := F)
  rw [hn] at hm
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hm
  exact ⟨j, rfl⟩

/-- **`4m | q` from `m | q` and `4m <= q`.** The size condition cannot be dropped: at `m = q` the
divisibility holds and the conclusion fails. -/
theorem four_mul_dvd_card {m : ℕ} (hm : m ∣ Fintype.card F) (h4 : 4 * m ≤ Fintype.card F) :
    4 * m ∣ Fintype.card F := by
  obtain ⟨n, hn⟩ := exists_card_eq_two_pow (F := F)
  obtain ⟨j, rfl⟩ := exists_eq_two_pow_of_dvd_card hm
  rw [hn] at h4 ⊢
  have h : 2 ^ (j + 2) ≤ 2 ^ n := by rw [pow_add]; linarith
  have hle : j + 2 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  rw [show 4 * 2 ^ j = 2 ^ (j + 2) by ring]
  exact pow_dvd_pow 2 hle

/-- **Inside the regime, stage 4's divisibility holds.** `48 m d <= q` with `d >= 1` gives
`4m <= q`, which is the size condition `four_mul_dvd_card` needs. This is the form
`MIPRE.QLD.exists_mirrorSimul` consumes: it takes `4m | q` and `48 m d <= q` as separate
hypotheses, and the first is a consequence of the second together with `m | q`. -/
theorem four_mul_dvd_card_of_regime {m d : ℕ} (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (hq : 48 * m * d ≤ Fintype.card F) : 4 * m ∣ Fintype.card F := by
  refine four_mul_dvd_card hm ?_
  calc 4 * m ≤ 48 * m * d := by nlinarith
    _ ≤ Fintype.card F := hq

end MIPRE.QLD
