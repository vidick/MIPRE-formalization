/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Instantiation
import MIPRE.Foundations.Halting.WrapperCost

/-!
# The two distinguished strings

Obligation **O1** of the halting reduction (`Halting/Reduction.lean`, which applies `yYes_mem`
and `yNo_mem` directly): a string whose verifier lies in `classA n` at every level above a
threshold, and one whose verifier lies in `classB n`.

Both are descriptions `descOf 0 𝒟` with the compressed sampler at parameter `0` and a decider
program of three or four nodes:

* `decNo` is the program `nil`. Its result is `nil`, never `encode true`, so the wrapped
  decider accepts nothing, the verifier is synchronous at every index for want of an accepting
  tuple, and `val* = 0` (`Verifier.inClassB_of_rejects_all`).
* `decYes` takes the input `(n, x, y, a, b)` apart and returns `encode true` exactly when both
  answers are the empty string. The paper's halting case is a decider that accepts
  *everything*; in the synchronous framework that verifier is not synchronous at all — equal
  questions with unequal answers must be rejected — so the fixed-answer form is what item 1 of
  `thm:halting` takes here (`Verifier.inClassA_of_accepts_diagonal`, the paper's trivial
  strategy).

`λ`-boundedness of both comes from `Verifier.ofSamplerDecider_isBounded`, whose three
hypotheses are fields of `MIPRE.GapCompression` for the sampler and immediate for these two
programs, each of which halts at constant cost.
-/

namespace MIPRE.Halting

open Cost

/-! ## The two decider programs -/

/-- **The rejecting decider**: the program `nil`, which returns `nil` on every input. -/
def decNo : Prog := .nil

/-- **The fixed-answer decider**: on `(n, x, y, a, b)` it returns `encode true` exactly when
`a` and `b` are both the empty bit string. Four `elim`s take the tuple apart and two more test
the answers. -/
def decYes : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil
    (.elim 0 (.elim 1 (.const (encode true)) .nil) .nil))))

theorem decNo_runs (v : Data) : decNo.Runs v .nil 1 := Eval.nil _

theorem decNo_hasPolyCost : decNo.HasPolyCost :=
  ⟨fun _ => 1, 0, PolyBounded.const 1, fun n d => ⟨.nil, 1, by simp, decNo_runs _⟩⟩

/-- The rejecting decider never returns `encode true`. -/
theorem decNo_not_runs_true (v : Data) (t : ℕ) : ¬ decNo.Runs v (encode true) t := by
  intro h
  obtain ⟨he, -⟩ := (decNo_runs v).deterministic h
  exact absurd he.symm (by simp [encode_bool, Data.ofBool])

/-! ## The fixed-answer decider -/

/-- On an input with at least four nodes on its right spine — the shape of a well-formed tuple
`(n, x, y, a, b)` — `decYes` returns `encode true` exactly when the last two components are
both `nil`. -/
private theorem decYes_run_deep (A B C D E : Data) :
    ∃ t ≤ 10, decYes.Runs (.cons A (.cons B (.cons C (.cons D E))))
      (if D = .nil ∧ E = .nil then encode true else .nil) t := by
  rcases D with _ | ⟨D₁, D₂⟩
  · rcases E with _ | ⟨E₁, E₂⟩
    · refine ⟨9, by omega, ?_⟩
      rw [if_pos ⟨rfl, rfl⟩]
      exact Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_cons rfl
        (Eval.elim_cons rfl (Eval.elim_nil rfl (Eval.elim_nil rfl (Eval.const _ _))))))
    · refine ⟨7, by omega, ?_⟩
      rw [if_neg (by simp)]
      exact Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_cons rfl
        (Eval.elim_cons rfl (Eval.elim_nil rfl (Eval.elim_cons rfl (Eval.nil _))))))
  · refine ⟨6, by omega, ?_⟩
    rw [if_neg (by simp)]
    exact Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_cons rfl
      (Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.nil _)))))

/-- `decYes` halts on every input, well formed or not, at constant cost: each of its `elim`s
either returns `nil` at once or descends one node. -/
theorem decYes_halts (v : Data) : ∃ r t, t ≤ 10 ∧ decYes.Runs v r t := by
  match v with
  | .nil => exact ⟨.nil, 2, by omega, Eval.elim_nil rfl (Eval.nil _)⟩
  | .cons A .nil => exact ⟨.nil, 3, by omega, Eval.elim_cons rfl (Eval.elim_nil rfl (Eval.nil _))⟩
  | .cons A (.cons B .nil) =>
    exact ⟨.nil, 4, by omega,
      Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_nil rfl (Eval.nil _)))⟩
  | .cons A (.cons B (.cons C .nil)) =>
    exact ⟨.nil, 5, by omega,
      Eval.elim_cons rfl (Eval.elim_cons rfl (Eval.elim_cons rfl
        (Eval.elim_nil rfl (Eval.nil _))))⟩
  | .cons A (.cons B (.cons C (.cons D E))) =>
    obtain ⟨t, ht, h⟩ := decYes_run_deep A B C D E
    exact ⟨_, t, ht, h⟩

theorem decYes_hasPolyCost : decYes.HasPolyCost :=
  ⟨fun _ => 10, 0, PolyBounded.const 10, fun n d =>
    let ⟨r, t, ht, hr⟩ := decYes_halts (.cons (encode n) d); ⟨r, t, by simpa using ht, hr⟩⟩

/-- **What `decYes` accepts**: the empty answer from both players, on every question pair. -/
theorem decYes_runs_true_iff (n : ℕ) (x y a b : BitStr) :
    (∃ t, decYes.Runs (encode (n, x, y, a, b)) (encode true) t) ↔ (a = [] ∧ b = []) := by
  have hin : (encode (n, x, y, a, b) : Data) =
      .cons (encode n) (.cons (encode x) (.cons (encode y) (.cons (encode a) (encode b)))) := rfl
  have henc : ∀ l : BitStr, (encode l : Data) = .nil ↔ l = [] := by
    intro l
    cases l with
    | nil => simp [encode_bitStr_nil]
    | cons c l => simp [encode_bitStr_cons]
  obtain ⟨t', -, h'⟩ := decYes_run_deep (encode n) (encode x) (encode y) (encode a) (encode b)
  rw [← hin] at h'
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨he, -⟩ := h'.deterministic h
    by_contra hc
    rw [if_neg (by rw [henc, henc]; exact hc)] at he
    exact absurd he.symm (by simp [encode_bool, Data.ofBool])
  · rintro ⟨ha, hb⟩
    rw [if_pos ⟨(henc a).2 ha, (henc b).2 hb⟩] at h'
    exact ⟨t', h'⟩

/-! ## The compressed sampler -/

variable (G : GapCompression) (U : UniversalMachine)

/-- The compressed sampler's cost is polynomially bounded: its time bound is
`bound (n + λ)` at the fixed degree `deg` (`GapCompression.sampler_time`). -/
theorem sampler_hasPolyCost (lam : ℕ) : (G.sampler lam).prog.HasPolyCost :=
  CL.Sampler.hasPolyCost_of_timeBound (T := fun n => G.bound.eval (n + lam)) (k := G.deg)
    (PolyBounded.eval G.bound (PolyBounded.id.add_const lam)) fun n => G.sampler_time lam n

/-- Its dimension is polynomially bounded (`GapCompression.sampler_dim`). -/
theorem sampler_polyBounded_dim (lam : ℕ) : PolyBounded (G.sampler lam).dim :=
  (PolyBounded.eval G.bound (PolyBounded.id.add_const lam)).mono (G.sampler_dim lam)

/-! ## The two strings -/

/-- **The string of the class `B`**: parameter `0`, decider `nil`. -/
def yNo : BitStr := descOf 0 decNo

/-- **The string of the class `A`**: parameter `0`, the fixed-answer decider. -/
def yYes : BitStr := descOf 0 decYes

@[simp] theorem Vof_yNo : Vof G U yNo = Verifier.ofSamplerDecider U (G.sampler 0) decNo := by
  simp [Vof, yNo, Verifier.ofSamplerDecider]

@[simp] theorem Vof_yYes : Vof G U yYes = Verifier.ofSamplerDecider U (G.sampler 0) decYes := by
  simp [Vof, yYes, Verifier.ofSamplerDecider]

/-- **O1, the rejecting side.** `yNo` lies in the class `B` at every level from some `n₀` on:
its verifier accepts nothing, hence is synchronous and has `val* = 0`, and it is `n`-bounded
above the threshold of `Verifier.ofSamplerDecider_isBounded`. -/
theorem yNo_mem : ∃ n₀, ∀ n, n₀ ≤ n → yNo ∈ classB G U n := by
  obtain ⟨n₀, hn₀⟩ := Verifier.ofSamplerDecider_isBounded U (G.sampler 0) decNo
    (sampler_hasPolyCost G 0) (sampler_polyBounded_dim G 0) decNo_hasPolyCost
  refine ⟨n₀, fun n hn => ?_⟩
  show (Vof G U yNo).InClassB n (ansBound G yNo n)
  rw [Vof_yNo]
  refine Verifier.inClassB_of_rejects_all _ (hn₀ n hn) fun x y a b hacc => ?_
  rw [Verifier.ofSamplerDecider_accepts] at hacc
  obtain ⟨-, -, t, ht⟩ := hacc
  exact decNo_not_runs_true _ _ ht

/-- **O1, the accepting side.** `yYes` lies in the class `A` at every level from some `n₀` on:
its verifier accepts the empty answer from both players on every question pair and nothing
else, so the constant strategy is a value-`1` PCC strategy and every long answer is
rejected. -/
theorem yYes_mem : ∃ n₀, ∀ n, n₀ ≤ n → yYes ∈ classA G U n := by
  obtain ⟨n₀, hn₀⟩ := Verifier.ofSamplerDecider_isBounded U (G.sampler 0) decYes
    (sampler_hasPolyCost G 0) (sampler_polyBounded_dim G 0) decYes_hasPolyCost
  refine ⟨n₀, fun n hn => ?_⟩
  show (Vof G U yYes).InClassA n (ansBound G yYes n)
  rw [Vof_yYes]
  refine Verifier.inClassA_of_accepts_diagonal _ (hn₀ n hn) ?_
    (⟨[], by simp⟩ : Verifier.Answers (ansBound G yYes n)) fun p q => ?_
  · -- only the empty answers are accepted, so every long one is rejected
    intro x y a b hlen hacc
    rw [Verifier.ofSamplerDecider_accepts] at hacc
    obtain ⟨-, -, hrun⟩ := hacc
    obtain ⟨rfl, rfl⟩ := (decYes_runs_true_iff n x y a b).1 hrun
    simp at hlen
  · rw [Verifier.ofSamplerDecider_accepts]
    exact ⟨CL.length_toBits p, CL.length_toBits q, (decYes_runs_true_iff n _ _ [] []).2 ⟨rfl, rfl⟩⟩

end MIPRE.Halting
