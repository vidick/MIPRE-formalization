/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.PauliSamplerExtension

/-! # A zero-dimensional sampler at the exceptional index

The branch inspects the index in place. At zero it returns the empty answer
without copying the query or reading the underlying sampler description.
-/

noncomputable section
namespace MIPRE.Introspection.ZeroIndexSampler
open Cost Cost.Prog Cost.PolyTimeFun CL

def emptySampler (ℓ : ℕ) : CL.Sampler ℓ where
  prog := .nil
  closed := trivial
  dim := fun _ => 0
  cl := fun _ _ => CLFun.zeroOn Finset.univ ℓ
  cl_exactlyOn := fun _ _ => CLFun.zeroOn_exactlyOn _ _ (by intro _; simp)
  runs_dimension := fun n => ⟨1, Eval.nil _⟩
  runs_marginal := by
    intro n w j z _ _ _
    exact ⟨1, Eval.nil _⟩
  runs_linear := by
    intro n w j u y _ _ _ _
    exact ⟨1, Eval.nil _⟩
  runs_factor := by
    intro n w j u _ _ _
    exact ⟨1, Eval.nil _⟩
  halts := fun _ _ => ⟨.nil, 1, Eval.nil _⟩

theorem emptySampler_timeBound (ℓ n : ℕ) : (emptySampler ℓ).TimeBoundAt n 1 0 := by
  intro d
  exact ⟨.nil, 1, by simp, Eval.nil _⟩

def wrap (p : Prog) : Prog := .elim 0 .nil (.elim 0 .nil (callVar 4 p))

theorem wrap_closed {p : Prog} (hp : p.WellScoped 1) : (wrap p).WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, callVar_wellScoped (by decide) hp⟩

theorem wrap_zero (p : Prog) (d : Data) :
    (wrap p).Runs (.cons (encode (0 : ℕ)) d) .nil 3 :=
  Eval.elim_cons (by rfl) (Eval.elim_nil (by rfl) (Eval.nil _))

theorem wrap_positive {p : Prog} (hp : p.WellScoped 1) {n : ℕ} (hn : n ≠ 0)
    (d r : Data) (t : ℕ) (hr : p.Runs (.cons (encode n) d) r t) :
    (wrap p).Runs (.cons (encode n) d) r ((.cons (encode n) d : Data).size + t + 4) := by
  have he : encode n ≠ Data.nil := by
    intro h
    apply hn
    exact encode_injective (show encode n = encode (0 : ℕ) from h)
  cases henc : encode n with
  | nil => exact (he henc).elim
  | cons a b =>
    have hcall := callVar_eval (env := [a,b,encode n,d,Data.cons (encode n) d])
      (i := 4) hp (by rfl) hr
    have hrun := Eval.elim_cons (env := [Data.cons (encode n) d]) (i := 0)
      (n := Prog.nil) (by rfl)
      (Eval.elim_cons (i := 0) (n := Prog.nil) (by exact henc) hcall)
    have ht : (Data.cons (encode n) d).size + 1 + t + 1 + 1 + 1 =
        (Data.cons (encode n) d).size + t + 4 := by omega
    rw [ht] at hrun
    simpa only [wrap, Prog.Runs, henc] using hrun

def compiler : PolyTimeFun Prog Prog :=
  ap₂ ClockSimulation.codeElim (const Prog.nil)
    (ap₂ ClockSimulation.codeElim (const Prog.nil) (ClockSimulation.codeCall 4))

@[simp] theorem compiler_apply (p : Prog) : compiler p = wrap p := rfl

def chosen {ℓ : ℕ} (S : CL.Sampler ℓ) (n : ℕ) : CL.Sampler ℓ :=
  if n = 0 then emptySampler ℓ else S

theorem wrap_chosen {ℓ : ℕ} (S : CL.Sampler ℓ) (n : ℕ) (d r : Data) (t : ℕ)
    (h : (chosen S n).prog.Runs (.cons (encode n) d) r t) :
    ∃ s, (wrap S.prog).Runs (.cons (encode n) d) r s := by
  by_cases hn : n = 0
  · subst n
    have he := h.deterministic (show (chosen S 0).prog.Runs
      (.cons (encode (0 : ℕ)) d) .nil 1 from Eval.nil _)
    rw [he.1]
    exact ⟨3, wrap_zero S.prog d⟩
  · have hr : S.prog.Runs (.cons (encode n) d) r t := by simpa [chosen, hn] using h
    exact ⟨_, wrap_positive S.closed hn d r t hr⟩

def atZero {ℓ : ℕ} (S : CL.Sampler ℓ) : CL.Sampler ℓ where
  prog := wrap S.prog
  closed := wrap_closed S.closed
  dim := fun n => (chosen S n).dim n
  cl := fun n w => (chosen S n).cl n w
  cl_exactlyOn := fun n w => (chosen S n).cl_exactlyOn n w
  runs_dimension := fun n => by
    obtain ⟨t, ht⟩ := (chosen S n).runs_dimension n
    exact wrap_chosen S n _ _ t ht
  runs_marginal := fun n w j z hj hℓ hz => by
    obtain ⟨t, ht⟩ := (chosen S n).runs_marginal n w j z hj hℓ hz
    exact wrap_chosen S n _ _ t ht
  runs_linear := fun n w j u y hj hℓ hu hy => by
    obtain ⟨t, ht⟩ := (chosen S n).runs_linear n w j u y hj hℓ hu hy
    exact wrap_chosen S n _ _ t ht
  runs_factor := fun n w j u hj hℓ hu => by
    obtain ⟨t, ht⟩ := (chosen S n).runs_factor n w j u hj hℓ hu
    exact wrap_chosen S n _ _ t ht
  halts := fun n d => by
    obtain ⟨r, t, ht⟩ := (chosen S n).halts n d
    obtain ⟨s, hs⟩ := wrap_chosen S n d r t ht
    exact ⟨r, s, hs⟩

@[simp] theorem atZero_dim_zero {ℓ : ℕ} (S : CL.Sampler ℓ) : (atZero S).dim 0 = 0 := rfl

theorem atZero_dim_pos {ℓ n : ℕ} (S : CL.Sampler ℓ) (hn : n ≠ 0) :
    (atZero S).dim n = S.dim n := by simp [atZero, chosen, hn]

theorem atZero_cl_pos {ℓ n : ℕ} (S : CL.Sampler ℓ) (hn : n ≠ 0) (w : Player) :
    HEq ((atZero S).cl n w) (S.cl n w) := by
  change HEq ((chosen S n).cl n w) (S.cl n w)
  have hc : chosen S n = S := by simp [chosen, hn]
  have he (A B : CL.Sampler ℓ) (h : A = B) : HEq (A.cl n w) (B.cl n w) := by
    subst B
    rfl
  exact he _ _ hc

theorem atZero_timeBound_zero {ℓ : ℕ} (S : CL.Sampler ℓ) :
    (atZero S).TimeBoundAt 0 1 2 := by
  intro d
  refine ⟨.nil, 3, ?_, wrap_zero S.prog d⟩
  have hd := d.size_pos
  simp only [one_mul]
  nlinarith

/-- The positive branch only copies the original input once before running the sampler. -/
theorem atZero_timeBound_pos {ℓ n B k : ℕ} (S : CL.Sampler ℓ) (hn : n ≠ 0)
    (h : S.TimeBoundAt n B k) :
    (atZero S).TimeBoundAt n (B + esize n + 5) (max k 1) := by
  intro d
  obtain ⟨r, t, ht, hr⟩ := h d
  refine ⟨r, (Data.cons (encode n) d).size + t + 4, ?_,
    wrap_positive S.closed hn d r t hr⟩
  have hp : (d.size + 1) ^ k ≤ (d.size + 1) ^ max k 1 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hq : d.size + 1 ≤ (d.size + 1) ^ max k 1 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 1 ≤ d.size + 1 by omega) (le_max_right k 1))
  have hone : 1 ≤ (d.size + 1) ^ max k 1 := by omega
  have ht' : t ≤ B * (d.size + 1) ^ max k 1 :=
    ht.trans (Nat.mul_le_mul_left _ hp)
  change esize n + d.size + 1 + t + 4 ≤ _
  nlinarith

end MIPRE.Introspection.ZeroIndexSampler
end
