/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Binary

/-!
# Iterating a polynomial-time step, and running programs in sequence

Two program combinators for routines whose running time is not polynomial in the size of their
input, such as the computation of `(λn + 1)^μ` from binary `λ, n, μ`:

* `whileProg f` iterates a total step `f : Data → Bool × Data` from a state, continuing on
  `(true, s')` with the state `s'` and stopping on `(false, r)` with the result `r`; a run of
  `N + 1` steps costs the sum of the steps' bounds (`whileProg_runs`);
* `seqProg p q` runs `q` on the output of `p` (`seqProg_runs`).
-/

namespace MIPRE.Cost

open PolyTimeFun

/-- Iterate the step `f` until it stops. -/
def whileProg (f : PolyTimeFun Data (Bool × Data)) : Prog := .loop f.code

theorem whileProg_closed (f : PolyTimeFun Data (Bool × Data)) : (whileProg f).WellScoped 1 :=
  ⟨Nat.zero_lt_one, f.closed⟩

/-- **A run of the loop** through the states `s 0, …, s N`, stopping at `s N` with `r`. -/
theorem whileProg_runs (f : PolyTimeFun Data (Bool × Data)) (N : ℕ) (s : ℕ → Data) (r : Data)
    (hcont : ∀ i < N, f (s i) = (true, s (i + 1))) (hstop : f (s N) = (false, r)) :
    ∃ t ≤ ∑ i ∈ Finset.range (N + 1), (f.timeBound.eval (s i).size + 1),
      (whileProg f).Runs (s 0) r t := by
  induction N generalizing s with
  | zero =>
    obtain ⟨t, ht, hr⟩ := f.computes (s 0)
    rw [hstop] at hr
    refine ⟨t + 1, by simpa using ht, ?_⟩
    exact Eval.loop_stop (b := f.code) (env := [s 0]) (r := r) hr
  | succ N ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := f.computes (s 0)
    rw [hcont 0 (by omega)] at h₀
    obtain ⟨t, ht, hrun⟩ := ih (fun i => s (i + 1)) (fun i hi => hcont (i + 1) (by omega)) hstop
    refine ⟨t₀ + t + 1, ?_, Eval.loop_step (x := .nil) (y := .nil) h₀ hrun⟩
    rw [Finset.sum_range_succ']
    simp only [esize_data] at ht₀
    have : ∑ i ∈ Finset.range (N + 1), (f.timeBound.eval (s (i + 1)).size + 1) ≥ t := ht
    omega

/-- Run `q` on the output of `p`. -/
def seqProg (p q : Prog) : Prog := .let_ p q

theorem seqProg_closed {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
    (seqProg p q).WellScoped 1 :=
  ⟨hp, hq.mono (by omega) _⟩

theorem seqProg_runs {p q : Prog} (hq : q.WellScoped 1) {x y r : Data} {s t : ℕ}
    (hp : p.Runs x y s) (hq' : q.Runs y r t) : (seqProg p q).Runs x r (s + t + 1) :=
  Eval.let_ hp (Eval.append_of_wellScoped hq' hq [x])

end MIPRE.Cost
