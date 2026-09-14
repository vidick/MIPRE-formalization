/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Growth
import Mathlib.Tactic.Linarith

/-!
# Polynomially bounded functions

The time accounting of the instantiation (`Halting/Wrapper.lean`, `Halting/Compressor.lean`)
composes a dozen explicit cost bounds, each a polynomial in the values it depends on. What the
argument eventually needs is only that the total is bounded by *some* polynomial in the level,
so that it falls under `2 ^ n` above a threshold. `PolyBounded f` records exactly that —
`f n ≤ P.eval n` for some `P : Polynomial ℕ` — with the closure properties that let the
bounds be composed without ever writing the polynomial down:

* constants, the identity, sums, products, powers, `Nat.size`;
* `PolyBounded.comp`: a polynomially bounded function of a polynomially bounded function;
* `PolyBounded.eval`: a fixed polynomial evaluated at a polynomially bounded argument;
* `PolyBounded.mono`: domination by a polynomially bounded function;
* `PolyBounded.exists_le_two_pow`: the threshold, `f n ≤ 2 ^ n` for all `n` above some `n₀`.

The polynomial of a `PolyBounded` function can be extracted (`PolyBounded.choose`) where an
explicit `Polynomial ℕ` is required, as in the `timeBound` field of `PolyTimeFun`.
-/

namespace MIPRE.Cost

open Polynomial

/-- `f` is bounded by a polynomial. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n

namespace PolyBounded

theorem const (c : ℕ) : PolyBounded fun _ => c := ⟨C c, fun _ => by simp⟩

theorem id : PolyBounded fun n => n := ⟨X, fun _ => by simp⟩

theorem mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ n, f n ≤ g n) : PolyBounded f :=
  let ⟨P, hP⟩ := hg
  ⟨P, fun n => (h n).trans (hP n)⟩

theorem add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded fun n => f n + g n :=
  let ⟨P, hP⟩ := hf
  let ⟨Q, hQ⟩ := hg
  ⟨P + Q, fun n => by simp only [eval_add]; exact Nat.add_le_add (hP n) (hQ n)⟩

theorem mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded fun n => f n * g n :=
  let ⟨P, hP⟩ := hf
  let ⟨Q, hQ⟩ := hg
  ⟨P * Q, fun n => by simp only [eval_mul]; exact Nat.mul_le_mul (hP n) (hQ n)⟩

theorem pow {f : ℕ → ℕ} (hf : PolyBounded f) (k : ℕ) : PolyBounded fun n => f n ^ k := by
  induction k with
  | zero => exact (const 1).mono fun n => by simp
  | succ k ih => exact (ih.mul hf).mono fun n => by rw [pow_succ]

theorem const_mul {f : ℕ → ℕ} (c : ℕ) (hf : PolyBounded f) : PolyBounded fun n => c * f n :=
  (const c).mul hf

theorem add_const {f : ℕ → ℕ} (hf : PolyBounded f) (c : ℕ) : PolyBounded fun n => f n + c :=
  hf.add (const c)

/-- A fixed polynomial at a polynomially bounded argument. -/
theorem eval (P : Polynomial ℕ) {f : ℕ → ℕ} (hf : PolyBounded f) :
    PolyBounded fun n => P.eval (f n) :=
  let ⟨Q, hQ⟩ := hf
  ⟨P.comp Q, fun n => by rw [eval_comp]; exact polynomial_eval_mono P (hQ n)⟩

/-- A polynomially bounded function of a polynomially bounded argument. Polynomials over `ℕ`
are monotone, so no monotonicity of `g` is needed. -/
theorem comp {g f : ℕ → ℕ} (hg : PolyBounded g) (hf : PolyBounded f) :
    PolyBounded fun n => g (f n) :=
  let ⟨Q, hQ⟩ := hg
  (eval Q hf).mono fun n => hQ (f n)

theorem size : PolyBounded Nat.size :=
  id.mono fun _ => Nat.size_le.2 Nat.lt_two_pow_self

theorem two_mul_add_one : PolyBounded fun n => 2 * n + 1 := (id.const_mul 2).add_const 1

/-- The polynomial of a polynomially bounded function. -/
noncomputable def poly {f : ℕ → ℕ} (hf : PolyBounded f) : Polynomial ℕ := Exists.choose hf

theorem le_poly_eval {f : ℕ → ℕ} (hf : PolyBounded f) (n : ℕ) : f n ≤ hf.poly.eval n :=
  Exists.choose_spec hf n

/-- **The threshold.** A polynomially bounded function is below `2 ^ n` from some `n₀` on. -/
theorem exists_le_two_pow {f : ℕ → ℕ} (hf : PolyBounded f) : ∃ n₀, ∀ n, n₀ ≤ n → f n ≤ 2 ^ n := by
  obtain ⟨P, hP⟩ := hf
  set A := ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i with hA
  set D := P.natDegree with hD
  refine ⟨A * (D + 1) ^ (D + 1) + 1, fun n hn => ?_⟩
  have h1 : P.eval n ≤ A * n ^ D := polynomial_eval_le_sum_coeff_mul_pow P (by omega)
  have h2 : A * n ^ D ≤ 2 ^ n := mul_pow_le_two_pow A D n (by omega)
  exact (hP n).trans (h1.trans h2)

end PolyBounded

/-- The size of the binary encoding of `n` is polynomially bounded. -/
theorem polyBounded_esize_nat : PolyBounded fun n => esize n :=
  ((PolyBounded.size.const_mul 4).add_const 1).mono fun n => esize_nat_le n

end MIPRE.Cost
