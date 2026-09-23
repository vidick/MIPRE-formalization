/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Pipeline.PowDom
import MIPRE.Foundations.Pipeline.UnaryArith
import MIPRE.Foundations.Cost.Universal
import MIPRE.Foundations.CL.DetypingProgCost

/-!
# Runs within a powered monomial

`PRuns W X K c m e p x r`: the program `p` runs from `x` to `r` at a cost below
`(c (W + 1)^m X^e)^{K + 1}` (`MIPRE.Pipeline.PDom`). The combinators follow the program
constructors the pipeline's routines are built from — a polynomial-time function's code
(`ptf`), sequencing (`seq`), a stage keeping a context (`stage`), hardcoding (`hardcode`), the
universal machine (`univ`), and the two unary loops (`toUnary`, `pow`) — and each returns its
constants from those of its arguments, so that a chain of them has constants uniform in `W`, `X`,
`K` and the data.

The explicit running times of the unary loops are `toUnaryProg_time` and `powProg_time`: they are
polynomial in the *values* involved.
-/

namespace MIPRE.Pipeline

open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic

/-! ## The unary loops -/

theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)

theorem sum_range_le_mul {N B : ℕ} {f : ℕ → ℕ} (h : ∀ i ≤ N, f i ≤ B) :
    ∑ i ∈ Finset.range (N + 1), f i ≤ (N + 1) * B := by
  calc ∑ i ∈ Finset.range (N + 1), f i ≤ ∑ _i ∈ Finset.range (N + 1), B :=
        Finset.sum_le_sum fun i hi => h i (by simp at hi; omega)
    _ = (N + 1) * B := by simp

/-- The initialization of `toUnaryProg`. -/
noncomputable abbrev toUnaryInit : PolyTimeFun Data Data :=
  encoded.comp ((readNat).pair (const ([] : Unary)))

/-- **The running time of `toUnaryProg`**, polynomial in the value `x`. -/
theorem toUnaryProg_time (x : ℕ) :
    ∃ t ≤ toUnaryInit.timeBound.eval (4 * x + 1) +
        (x + 1) * (toUnaryStep.timeBound.eval (4 * x + 3) + 1) + 1,
      toUnaryProg.Runs (encode x) (encode (unary x)) t := by
  obtain ⟨t₀, ht₀, h₀⟩ := toUnaryInit.computes (encode x)
  have hi : toUnaryInit (encode x) = encode (x, ([] : Unary)) := by simp [readNat_encode]
  rw [hi] at h₀
  obtain ⟨t, ht, hrun⟩ := whileProg_runs toUnaryStep x (fun i => encode (x - i, unary i))
    (encode (unary x)) (fun i hi => by
      obtain ⟨y, hy⟩ : ∃ y, x - i = y + 1 := ⟨x - i - 1, by omega⟩
      rw [hy, toUnaryStep_succ, show x - (i + 1) = y by omega]
      simp [unary, List.replicate_succ])
    (by simp only [Nat.sub_self, toUnaryStep_zero])
  refine ⟨_, ?_, seqProg_runs (whileProg_closed _) h₀ (by simpa [unary] using hrun)⟩
  have h1 : t₀ ≤ toUnaryInit.timeBound.eval (4 * x + 1) :=
    ht₀.trans (polynomial_eval_mono _ (esize_nat_le_four x))
  have h2 : t ≤ (x + 1) * (toUnaryStep.timeBound.eval (4 * x + 3) + 1) := by
    refine ht.trans (sum_range_le_mul fun i hi => Nat.add_le_add_right
      (polynomial_eval_mono _ ?_) 1)
    have := esize_nat_le_four (x - i)
    simp only [encode_prod, Data.size_cons]
    change esize (x - i) + esize (unary i) + 1 ≤ _
    rw [esize_unary]
    omega
  omega

/-- The initialization of `powProg`. -/
noncomputable abbrev powInit : PolyTimeFun Data Data :=
  encoded.comp ((readNat.comp treeTail).pair ((const (unary 1)).pair (readUnary.comp treeHead)))

/-- **The running time of `powProg`**, polynomial in `e`, `|b|` and `|b|^e`. -/
theorem powProg_time (b : Unary) (e : ℕ) (hb : 1 ≤ b.length) :
    ∃ t ≤ powInit.timeBound.eval (2 * b.length + 4 * e + 3) +
        (e + 1) * (powStep.timeBound.eval (4 * e + 2 * b.length ^ e + 2 * b.length + 5) + 1) + 1,
      powProg.Runs (encode (b, e)) (encode (unary (b.length ^ e))) t := by
  obtain ⟨t₀, ht₀, h₀⟩ := powInit.computes (encode (b, e))
  have hi : powInit (encode (b, e)) = encode (e, unary 1, b) := by
    simp [encode_prod, readNat_encode]
  rw [hi] at h₀
  obtain ⟨t, ht, hrun⟩ := whileProg_runs powStep e
    (fun i => encode (e - i, unary (b.length ^ i), b)) (encode (unary (b.length ^ e)))
    (fun i hi => by
      obtain ⟨y, hy⟩ : ∃ y, e - i = y + 1 := ⟨e - i - 1, by omega⟩
      rw [hy, powStep_succ, show e - (i + 1) = y by omega, length_unary, pow_succ])
    (by simp only [Nat.sub_self, powStep_zero])
  refine ⟨_, ?_, seqProg_runs (whileProg_closed _) h₀ (by simpa using hrun)⟩
  have hbsz : esize b = 2 * b.length + 1 := esize_unary_list b
  have h1 : t₀ ≤ powInit.timeBound.eval (2 * b.length + 4 * e + 3) := by
    refine ht₀.trans (polynomial_eval_mono _ ?_)
    have := esize_nat_le_four e
    simp only [esize_data, encode_prod, Data.size_cons]
    change esize b + esize e + 1 ≤ _
    omega
  have h2 : t ≤ (e + 1) *
      (powStep.timeBound.eval (4 * e + 2 * b.length ^ e + 2 * b.length + 5) + 1) := by
    refine ht.trans (sum_range_le_mul fun i hi => Nat.add_le_add_right
      (polynomial_eval_mono _ ?_) 1)
    have := esize_nat_le_four (e - i)
    have hp : b.length ^ i ≤ b.length ^ e := Nat.pow_le_pow_right hb hi
    simp only [encode_prod, Data.size_cons]
    change esize (e - i) + (esize (unary (b.length ^ i)) + esize b + 1) + 1 ≤ _
    rw [esize_unary]
    omega
  omega

/-! ## Runs within a powered monomial -/

/-- `p` runs from `x` to `r` at a cost below `(c (W + 1)^m X^e)^{K + 1}`. -/
def PRuns (W X K c m e : ℕ) (p : Prog) (x r : Data) : Prop :=
  ∃ t, PDom W X K c m e t ∧ p.Runs x r t

namespace PRuns

variable {W X K : ℕ}

theorem size_le {c m e : ℕ} {p : Prog} {x r : Data} (h : PRuns W X K c m e p x r) :
    PDom W X K c m e r.size :=
  let ⟨_, ht, hr⟩ := h
  ht.of_le hr.size_le

theorem mono (hX : 1 ≤ X) {c m e c' m' e' : ℕ} {p : Prog} {x r : Data}
    (h : PRuns W X K c m e p x r) (hc : c ≤ c') (hm : m ≤ m') (he : e ≤ e') :
    PRuns W X K c' m' e' p x r :=
  let ⟨t, ht, hr⟩ := h
  ⟨t, ht.mono hX hc hm he, hr⟩

theorem seq (hX : 1 ≤ X) {c₁ m₁ e₁ c₂ m₂ e₂ : ℕ} {p q : Prog} (hq : q.WellScoped 1)
    {x y r : Data} (h₁ : PRuns W X K c₁ m₁ e₁ p x y) (h₂ : PRuns W X K c₂ m₂ e₂ q y r) :
    PRuns W X K (c₁ + c₂ + 2) (max (max m₁ m₂) 0) (max (max e₁ e₂) 0) (seqProg p q) x r :=
  let ⟨_, hs, hp⟩ := h₁
  let ⟨_, ht, hq'⟩ := h₂
  ⟨_, (hs.add hX ht).add hX (PDom.const 1), seqProg_runs hq hp hq'⟩

/-- **A polynomial-time function's code**, on an input of dominated size. -/
theorem ptf {α β : Type*} [SizedEncoding α] [SizedEncoding β] (f : PolyTimeFun α β)
    (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (a : α), 1 ≤ X → PDom W X K c m e (esize a) →
      PRuns W X K C M E f.code (encode a) (encode (f a)) :=
  ⟨_, _, _, fun a hX ha => by
    obtain ⟨t, ht, hr⟩ := f.computes a
    exact ⟨t, (ha.poly hX f.timeBound).of_le ht, hr⟩⟩

/-- A polynomial-time function's value, of dominated size. -/
theorem ptf_size {α β : Type*} [SizedEncoding α] [SizedEncoding β] (f : PolyTimeFun α β)
    (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (a : α), 1 ≤ X → PDom W X K c m e (esize a) →
      PDom W X K C M E (esize (f a)) :=
  ⟨_, _, _, fun a hX ha => (ha.poly hX f.timeBound).of_le (f.esize_apply_le a)⟩

/-- **A stage** keeping a context: `stageProg pre p post` on `x`, with `pre x = (a, ctx)`. -/
theorem stage (pre : PolyTimeFun Data Data) (post : PolyTimeFun (Data × Data) Data)
    (c m e c' m' e' : ℕ) : ∃ C M E, ∀ {W X K : ℕ} {p : Prog}, p.WellScoped 1 →
      ∀ (x a ctx r : Data), 1 ≤ X → pre x = .cons a ctx → PDom W X K c m e x.size →
      PRuns W X K c' m' e' p a r → PRuns W X K C M E (stageProg pre p post) x (post (ctx, r)) :=
  ⟨_, _, _, fun {W X K p} hp x a ctx r hX hpre hx hrun => by
    obtain ⟨t, ht, hr⟩ := hrun
    obtain ⟨t₀, ht₀, h₀⟩ := pre.computes x
    rw [encode_data, hpre] at h₀
    obtain ⟨t₁, ht₁, h₁⟩ := Prog.callWithContext_cost hp post a ctx r t hr
    have hP : PDom W X K _ _ _ (pre.timeBound.eval x.size) := hx.poly hX pre.timeBound
    have hsz : (Data.cons a ctx).size ≤ pre.timeBound.eval x.size := by
      have := pre.esize_apply_le x
      rw [hpre] at this
      simpa [esize_data] using this
    simp only [Data.size_cons] at hsz
    have hrs : r.size ≤ t := hr.size_le
    have hQ := ((hP.add hX ht).add hX (PDom.const 1)).poly hX post.timeBound
    refine ⟨_, ?_, seqProg_runs (Prog.callWithContext_closed hp post) h₀ h₁⟩
    have hpost : post.timeBound.eval (ctx.size + r.size + 1) ≤
        post.timeBound.eval (pre.timeBound.eval x.size + t + 1) :=
      polynomial_eval_mono _ (by omega)
    refine ((((((PDom.const 3).mul hP).add hX ((PDom.const 2).mul ht)).add hX hQ).add hX
      (PDom.const 13))).of_le ?_
    simp only [esize_data] at ht₀
    omega⟩

/-- **Hardcoding** a datum `d`. -/
theorem hardcode (hX : 1 ≤ X) {c m e c₁ m₁ e₁ c₂ m₂ e₂ : ℕ} {p : Prog} (hp : p.WellScoped 1)
    {d x r : Data} (h : PRuns W X K c m e p (.cons d x) r) (hd : PDom W X K c₁ m₁ e₁ d.size)
    (hx : PDom W X K c₂ m₂ e₂ x.size) :
    PRuns W X K (c + c₁ + c₂ + 4) (max (max (max m m₁) m₂) 0) (max (max (max e e₁) e₂) 0)
      (Cost.hardcode p d) x r :=
  let ⟨_, ht, hr⟩ := h
  ⟨_, ((ht.add hX hd).add hX hx).add hX (PDom.const 3), hardcode_time hp hr⟩

/-- **The universal machine**, simulating a run of dominated cost. -/
theorem univ (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (q : Prog) (v r : Data) (t : ℕ), 1 ≤ X →
    q.Runs v r t → PDom W X K c m e (esize q + v.size + t) →
    PRuns W X K C M E selfUniversal.univ (.cons (encode q) v) r :=
  ⟨_, _, _, fun q v r t hX hr ht => by
    obtain ⟨t', ht', hu⟩ := selfUniversal.time_le q v r t hr
    exact ⟨t', (ht.poly hX selfUniversal.bound).of_le ht', hu⟩⟩

/-- **Writing a dominated number in unary.** -/
theorem toUnary (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (x : ℕ), 1 ≤ X → PDom W X K c m e x →
    PRuns W X K C M E toUnaryProg (encode x) (encode (unary x)) :=
  ⟨_, _, _, fun x hX hx => by
    obtain ⟨t, ht, hr⟩ := toUnaryProg_time x
    refine ⟨t, ?_, hr⟩
    have h4 := ((PDom.const 4).mul hx).add hX (PDom.const 1)
    have h3 := ((PDom.const 4).mul hx).add hX (PDom.const 3)
    exact ((((h4.poly hX toUnaryInit.timeBound).add hX ((hx.add hX (PDom.const 1)).mul
      ((h3.poly hX toUnaryStep.timeBound).add hX (PDom.const 1)))).add hX
      (PDom.const 1))).of_le ht⟩

/-- **A unary power** `|b|^e`, all three of `|b|`, `e` and `|b|^e` dominated. -/
theorem pow (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (b : Unary) (k : ℕ), 1 ≤ X → 1 ≤ b.length →
    PDom W X K c m e b.length → PDom W X K c m e k → PDom W X K c m e (b.length ^ k) →
    PRuns W X K C M E powProg (encode (b, k)) (encode (unary (b.length ^ k))) :=
  ⟨_, _, _, fun b k hX hb hL hk hLk => by
    obtain ⟨t, ht, hr⟩ := powProg_time b k hb
    refine ⟨t, ?_, hr⟩
    have hi := ((((PDom.const 2).mul hL).add hX ((PDom.const 4).mul hk)).add hX (PDom.const 3))
    have hs := (((((PDom.const 4).mul hk).add hX ((PDom.const 2).mul hLk)).add hX
      ((PDom.const 2).mul hL)).add hX (PDom.const 5))
    exact ((((hi.poly hX powInit.timeBound).add hX ((hk.add hX (PDom.const 1)).mul
      ((hs.poly hX powStep.timeBound).add hX (PDom.const 1)))).add hX
      (PDom.const 1))).of_le ht⟩

end PRuns

end MIPRE.Pipeline
