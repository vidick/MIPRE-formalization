/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.Lists
import MIPRE.Foundations.Halting.Arith

/-!
# Primitives of the repeated sampler and decider

Three loops of the ambient model that the programs of `thm:parallel-repetition` share
(`planning/repetition-verifier.md`, R3(a)–(b)):

* `powBody`: on the state `(e, bl, bn, acc)` — `e` a unary counter, `bl` and `bn` the bit
  lists of `λ` and `n`, `acc` a list — prepend `|bl| + |bn|` copies of `nil` to `acc`, `e`
  times (`powLoop_runs`). With `acc = []` the result is the unary numeral
  `e · (|λ| + |n|)`; with `acc` the numeral `1` it is the binary numeral `2^{e(|λ| + |n|)}`,
  the repetition count `k(n)` and the parse length `B(n)` of `MIPRE.Repetition`; with `acc`
  the bits of `s ≠ 0` it is `2^{e(|λ| + |n|)} · s`, the dimension of the repeated sampler.
* `dblBody`: on `(m, acc)`, `m` a unary counter and `acc` a unary numeral, double `acc` `m`
  times (`dblLoop_runs`): the unary numeral `2^m` from the unary numeral `m`.
* `takeBody` and `chunkBody`: cut a list into pieces of `s` elements (`Data.chunks`), `s`
  given in unary (`chunkLoop_runs`): the blocks of a vector of `𝔽₂^{k s}`.
-/

namespace MIPRE.Cost

open Data

namespace Data

/-- The elements of a datum read as a list: every datum is a `cons`-chain ending in `nil`. -/
def toList : Data → List Data
  | nil => []
  | cons a b => a :: toList b

@[simp] theorem list_toList : ∀ d : Data, list (toList d) = d
  | nil => rfl
  | cons a b => by simp [toList, list_toList b]

@[simp] theorem toList_list : ∀ l : List Data, toList (list l) = l
  | [] => rfl
  | a :: l => by simp [toList, toList_list l]

theorem size_list_append (l₁ l₂ : List Data) :
    (list (l₁ ++ l₂)).size + 1 = (list l₁).size + (list l₂).size := by
  induction l₁ with
  | nil => simp only [List.nil_append, list_nil, size_nil]; omega
  | cons a l ih => simp only [List.cons_append, size_list_cons] at ih ⊢; omega

theorem size_list_reverse (l : List Data) : (list l.reverse).size = (list l).size := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have := size_list_append l.reverse [a]
    simp only [List.reverse_cons, size_list_cons, list_nil, size_nil] at this ⊢
    omega

theorem size_list_take_le (s : ℕ) (l : List Data) : (list (l.take s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => simp only [List.take_zero, list_nil, size_nil, size_list_cons]; omega
    | succ s => simp only [List.take_succ_cons, size_list_cons]; have := ih s; omega

theorem size_list_drop_le (s : ℕ) (l : List Data) : (list (l.drop s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => exact le_rfl
    | succ s => simp only [List.drop_succ_cons, size_list_cons]; have := ih s; omega

theorem length_le_size_list' (l : List Data) : l.length + 1 ≤ (list l).size := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, size_list_cons]; have := size_pos a; omega

/-- The pieces of `s` consecutive elements of a list, the last one possibly shorter
(`s > 0`). -/
def chunks {α : Type*} (s : ℕ) (hs : 0 < s) : List α → List (List α)
  | [] => []
  | h :: l => (h :: l).take s :: chunks s hs ((h :: l).drop s)
termination_by l => l.length
decreasing_by simp; omega

theorem chunks_nil {α : Type*} (s : ℕ) (hs : 0 < s) : chunks s hs ([] : List α) = [] := by
  rw [chunks]

theorem chunks_cons {α : Type*} (s : ℕ) (hs : 0 < s) (h : α) (l : List α) :
    chunks s hs (h :: l) = (h :: l).take s :: chunks s hs ((h :: l).drop s) := by rw [chunks]

theorem chunks_of_ne_nil {α : Type*} (s : ℕ) (hs : 0 < s) {l : List α} (hl : l ≠ []) :
    chunks s hs l = l.take s :: chunks s hs (l.drop s) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons h l => exact chunks_cons s hs h l

/-- The pieces reassemble the list. -/
theorem flatten_chunks {α : Type*} (s : ℕ) (hs : 0 < s) (l : List α) :
    (chunks s hs l).flatten = l := by
  induction l using chunks.induct s hs with
  | case1 => simp [chunks_nil]
  | case2 h l ih => rw [chunks_cons, List.flatten_cons, ih, List.take_append_drop]

/-- The `i`-th piece of `s` elements of a list. -/
def chunk {α : Type*} (s i : ℕ) (l : List α) : List α := (l.drop (i * s)).take s

/-- A list of length `k · s` cuts into the `k` pieces `chunk s i l`. -/
theorem chunks_eq_ofFn {α : Type*} (s : ℕ) (hs : 0 < s) : ∀ (k : ℕ) (l : List α),
    l.length = k * s → chunks s hs l = List.ofFn fun i : Fin k => chunk s i l
  | 0, l, hl => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    simp [chunks_nil]
  | k + 1, l, hl => by
    have hne : l ≠ [] := by
      intro h; subst h; simp at hl; nlinarith
    rw [chunks_of_ne_nil s hs hne, List.ofFn_succ]
    have hlen : (l.drop s).length = k * s := by
      rw [List.length_drop, hl]; rw [Nat.succ_mul]; omega
    rw [chunks_eq_ofFn s hs k (l.drop s) hlen]
    congr 1
    · simp [chunk]
    · congr 1
      funext i
      simp only [chunk, Fin.val_succ, List.drop_drop]
      congr 2
      ring

theorem chunks_of_length_mul {α : Type*} (s : ℕ) (hs : 0 < s) (k : ℕ) (l : List α)
    (hl : l.length = k * s) : (chunks s hs l).length = k ∧ ∀ p ∈ chunks s hs l, p.length = s := by
  rw [chunks_eq_ofFn s hs k l hl]
  refine ⟨by simp, fun p hp => ?_⟩
  rw [List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  simp only [chunk, List.length_take, List.length_drop, hl]
  have hi : (i + 1) * s ≤ k * s := Nat.mul_le_mul_right s i.isLt
  rw [Nat.add_mul, one_mul] at hi
  rw [min_eq_left (by omega)]

theorem chunks_map {α β : Type*} (s : ℕ) (hs : 0 < s) (f : α → β) (l : List α) :
    chunks s hs (l.map f) = (chunks s hs l).map (List.map f) := by
  induction l using chunks.induct s hs with
  | case1 => simp [chunks_nil]
  | case2 h l ih =>
    have e : (h :: l).map f = f h :: l.map f := rfl
    rw [e, chunks_cons, chunks_cons, List.map_cons, ← e, ← List.map_take, ← List.map_drop, ih]

/-- The pieces of `s` elements of two lists, in lockstep: as many as the first list has, the
second one's possibly shorter or empty. -/
def chunkPairs (s : ℕ) (hs : 0 < s) : List Data → List Data → List (List Data × List Data)
  | [], _ => []
  | h :: l, y => ((h :: l).take s, y.take s) :: chunkPairs s hs ((h :: l).drop s) (y.drop s)
termination_by l => l.length
decreasing_by simp; omega

theorem chunkPairs_nil (s : ℕ) (hs : 0 < s) (y : List Data) : chunkPairs s hs [] y = [] := by
  rw [chunkPairs]

theorem chunkPairs_cons (s : ℕ) (hs : 0 < s) (h : Data) (l y : List Data) :
    chunkPairs s hs (h :: l) y =
      ((h :: l).take s, y.take s) :: chunkPairs s hs ((h :: l).drop s) (y.drop s) := by
  rw [chunkPairs]

theorem chunkPairs_of_ne_nil (s : ℕ) (hs : 0 < s) {l : List Data} (hl : l ≠ []) (y : List Data) :
    chunkPairs s hs l y = (l.take s, y.take s) :: chunkPairs s hs (l.drop s) (y.drop s) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons h l => exact chunkPairs_cons s hs h l y

/-- With the first list of length `k · s`, the pairs are the `k` pairs of pieces. -/
theorem chunkPairs_eq_ofFn (s : ℕ) (hs : 0 < s) : ∀ (k : ℕ) (l y : List Data),
    l.length = k * s → chunkPairs s hs l y = List.ofFn fun i : Fin k => (chunk s i l, chunk s i y)
  | 0, l, y, hl => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    simp [chunkPairs_nil]
  | k + 1, l, y, hl => by
    have hne : l ≠ [] := by
      intro h; subst h; simp at hl; nlinarith
    rw [chunkPairs_of_ne_nil s hs hne, List.ofFn_succ]
    have hlen : (l.drop s).length = k * s := by
      rw [List.length_drop, hl]; rw [Nat.succ_mul]; omega
    rw [chunkPairs_eq_ofFn s hs k (l.drop s) (y.drop s) hlen]
    congr 1
    · simp [chunk]
    · congr 1
      funext i
      simp only [chunk, Fin.val_succ, List.drop_drop]
      congr 3 <;> ring

/-- Every piece is a piece of the list it came from: the sizes are bounded. -/
theorem size_le_of_mem_chunkPairs (s : ℕ) (hs : 0 < s) (l y : List Data) :
    ∀ p ∈ chunkPairs s hs l y, (list p.1).size ≤ (list l).size ∧ (list p.2).size ≤ (list y).size := by
  induction l, y using chunkPairs.induct s hs with
  | case1 y => simp [chunkPairs_nil]
  | case2 h l y ih =>
    intro p hp
    rw [chunkPairs_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨size_list_take_le _ _, size_list_take_le _ _⟩
    · obtain ⟨h1, h2⟩ := ih p hp
      exact ⟨h1.trans (size_list_drop_le _ _), h2.trans (size_list_drop_le _ _)⟩

/-- The binary digits of `2^m · s`, for `s ≠ 0`: `m` zeros then those of `s`. -/
theorem _root_.Nat.bits_two_pow_mul (m : ℕ) {s : ℕ} (hs : s ≠ 0) :
    (2 ^ m * s).bits = List.replicate m false ++ s.bits := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hne : 2 ^ m * s ≠ 0 := by positivity
    rw [pow_succ, mul_comm (2 ^ m) 2, mul_assoc, Nat.bit0_bits _ hne, ih, List.replicate_succ,
      List.cons_append]

end Data

namespace Prog

/-! ## Prepending `e · (|bl| + |bn|)` copies of `nil` -/

/-- Body of the power walk: on the state `cons u (cons bl (cons bn acc))`, stop with `acc` if
the counter `u` is empty, and otherwise walk `bn` then `bl`, prepending a `nil` to `acc` per
element, and decrement `u`. -/
def powBody : Prog :=
  .elim 0 .nil
    (.elim 0
      (.elim 1 .nil (.elim 1 .nil (.cons .nil (.var 1))))
      (.elim 3 .nil (.elim 1 .nil
        (.let_ (.let_ (.cons (.var 0) (.var 1)) (.loop lenBody))
          (.let_ (.let_ (.cons (.var 3) (.var 0)) (.loop lenBody))
            (.cons (.cons .nil .nil)
              (.cons (.var 7) (.cons (.var 4) (.cons (.var 2) (.var 0))))))))))

theorem powBody_wellScoped : powBody.WellScoped 1 := by
  simp [powBody, WellScoped, lenBody]

/-- The state of the power walk. -/
def powState (e : ℕ) (bl bn acc : List Data) : Data :=
  .cons (ofNat e) (.cons (.list bl) (.cons (.list bn) (.list acc)))

theorem powBody_stop (bl bn acc : List Data) :
    ∃ t ≤ (Data.list acc).size + 8,
      Eval [powState 0 bl bn acc] powBody (.cons .nil (.list acc)) t := by
  have run : Eval [powState 0 bl bn acc] powBody (.cons .nil (.list acc)) _ :=
    Eval.elim_cons (env := [powState 0 bl bn acc]) (i := 0) (n := .nil)
      (a := ofNat 0) (b := .cons (.list bl) (.cons (.list bn) (.list acc))) (by simp [powState])
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (Eval.elim_cons (i := 1) (n := .nil) (a := .list bl) (b := .cons (.list bn) (.list acc))
          (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := .list bn) (b := .list acc) (by simp)
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .list acc) (by simp))))))
  exact ⟨_, by omega, run⟩

/-- The size of a list of `m` copies of `nil` in front of `acc`. -/
theorem size_list_replicate_nil_append (m : ℕ) (acc : List Data) :
    (Data.list (List.replicate m .nil ++ acc)).size = 2 * m + (Data.list acc).size := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.cons_append, Data.size_list_cons, ih]; simp; omega

/-- One iteration of the power walk. -/
theorem powBody_step (e : ℕ) (bl bn acc : List Data) :
    ∃ t ≤ (bn.length + 1) * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size +
        2 * bn.length + 13) +
      (bl.length + 1) * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size +
        2 * bn.length + 2 * bl.length + 13) +
      4 * ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size + 2 * e + 2 * bn.length +
        2 * bl.length) + 40,
      Eval [powState (e + 1) bl bn acc] powBody
        (.cons (.cons .nil .nil)
          (powState e bl bn (List.replicate (bl.length + bn.length) .nil ++ acc))) t := by
  set r' : Data := .cons (.list bn) (.list acc) with hr'
  set r : Data := .cons (.list bl) r' with hr
  set st : Data := powState (e + 1) bl bn acc with hst
  have hS₁ : (Data.list bn).size + (Data.list acc).size + 2 * bn.length ≤
      (Data.list bl).size + (Data.list bn).size + (Data.list acc).size + 2 * bn.length := by omega
  obtain ⟨t₁, ht₁, h₁⟩ := lenLoop_runs bn acc
    [.list bn, .list acc, .list bl, r', .nil, ofNat e, ofNat (e + 1), r, st] _ hS₁
  set acc₁ : List Data := List.replicate bn.length .nil ++ acc with hacc₁
  have hsz₁ : (Data.list acc₁).size = 2 * bn.length + (Data.list acc).size :=
    size_list_replicate_nil_append _ _
  have hS₂ : (Data.list bl).size + (Data.list acc₁).size + 2 * bl.length ≤
      (Data.list bl).size + (Data.list bn).size + (Data.list acc).size + 2 * bn.length +
        2 * bl.length := by rw [hsz₁]; omega
  obtain ⟨t₂, ht₂, h₂⟩ := lenLoop_runs bl acc₁
    [.list acc₁, .list bn, .list acc, .list bl, r', .nil, ofNat e, ofNat (e + 1), r, st] _ hS₂
  have hfin : List.replicate bl.length .nil ++ acc₁ =
      List.replicate (bl.length + bn.length) .nil ++ acc := by
    rw [hacc₁, ← List.append_assoc, ← List.replicate_add]
  rw [hfin] at h₂
  set acc₂ : List Data := List.replicate (bl.length + bn.length) .nil ++ acc with hacc₂
  have hsz₂ : (Data.list acc₂).size = 2 * (bl.length + bn.length) + (Data.list acc).size :=
    size_list_replicate_nil_append _ _
  have run : Eval [st] powBody (.cons (.cons .nil .nil) (powState e bl bn acc₂)) _ :=
    Eval.elim_cons (env := [st]) (i := 0) (n := .nil) (a := ofNat (e + 1)) (b := r)
      (by simp [hst, powState, hr, hr'])
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat e) (by simp [ofNat])
        (Eval.elim_cons (i := 3) (n := .nil) (a := .list bl) (b := r') (by simp [hr])
          (Eval.elim_cons (i := 1) (n := .nil) (a := .list bn) (b := .list acc) (by simp [hr'])
            (Eval.let_
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := .list bn) (by simp))
                (Eval.var_of_get (i := 1) (v := .list acc) (by simp))) h₁)
              (Eval.let_
                (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := .list bl) (by simp))
                  (Eval.var_of_get (i := 0) (v := .list acc₁) (by simp))) h₂)
                (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                  (Eval.cons (Eval.var_of_get (i := 7) (v := ofNat e) (by simp))
                    (Eval.cons (Eval.var_of_get (i := 4) (v := .list bl) (by simp))
                      (Eval.cons (Eval.var_of_get (i := 2) (v := .list bn) (by simp))
                        (Eval.var_of_get (i := 0) (v := .list acc₂) (by simp)))))))))))
  refine ⟨_, ?_, run⟩
  simp only [size_ofNat, hsz₁, hsz₂]
  omega

/-- The cost of the power walk with counter `e` on lists of total length `L` and total size
`Σ`: `(e + 1)` rounds, each polynomial in the sizes. -/
def powCost (e L sz : ℕ) : ℕ := (e + 1) * (8 * (L + 1) * (sz + 2 * e * L + e + 14))

/-- The power walk: `e` rounds, each prepending `|bl| + |bn|` copies of `nil`. -/
theorem powLoop_runs (e : ℕ) (bl bn acc : List Data) (env : Env) :
    ∃ t ≤ powCost e (bl.length + bn.length)
        ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size),
      Eval (powState e bl bn acc :: env) (.loop powBody)
        (.list (List.replicate (e * (bl.length + bn.length)) .nil ++ acc)) t := by
  induction e generalizing acc with
  | zero =>
    obtain ⟨t, ht, h⟩ := powBody_stop bl bn acc
    refine ⟨t + 1, ?_, ?_⟩
    · unfold powCost
      nlinarith [Nat.zero_le ((bl.length + bn.length) * (Data.list acc).size),
        Nat.zero_le ((bl.length + bn.length) * ((Data.list bl).size + (Data.list bn).size))]
    · simpa using Eval.loop_stop (Eval.append_of_wellScoped h powBody_wellScoped env)
  | succ e ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := powBody_step e bl bn acc
    obtain ⟨t₂, ht₂, h₂⟩ := ih (List.replicate (bl.length + bn.length) .nil ++ acc)
    have hres : List.replicate (e * (bl.length + bn.length)) .nil ++
        (List.replicate (bl.length + bn.length) .nil ++ acc) =
        List.replicate ((e + 1) * (bl.length + bn.length)) .nil ++ acc := by
      rw [← List.append_assoc, ← List.replicate_add]; congr 2; ring
    rw [hres] at h₂
    refine ⟨t₁ + t₂ + 1, ?_,
      Eval.loop_step (Eval.append_of_wellScoped h₁ powBody_wellScoped env) h₂⟩
    rw [size_list_replicate_nil_append] at ht₂
    set L := bl.length + bn.length with hL
    set sz := (Data.list bl).size + (Data.list bn).size + (Data.list acc).size with hsz
    set D : ℕ := 8 * (L + 1) * (sz + 2 * (e + 1) * L + (e + 1) + 14) with hD
    have hbl : bl.length ≤ L := by omega
    have hbn : bn.length ≤ L := by omega
    -- the step is below one round's budget
    have hstep : t₁ + 1 ≤ D := by
      rw [hD]
      have h1 : (bn.length + 1) * (sz + 2 * bn.length + 13) ≤ (L + 1) * (sz + 2 * L + 13) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (bl.length + 1) * (sz + 2 * bn.length + 2 * bl.length + 13) ≤
          (L + 1) * (sz + 2 * L + 13) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : 4 * (sz + 2 * e + 2 * bn.length + 2 * bl.length) ≤ 4 * (sz + 2 * e + 2 * L) := by
        omega
      have h4 : (L + 1) * (sz + 2 * L + 13) + (L + 1) * (sz + 2 * L + 13) + 4 * (sz + 2 * e + 2 * L) +
          40 < 8 * (L + 1) * (sz + 2 * (e + 1) * L + (e + 1) + 14) := by
        nlinarith [Nat.zero_le (L * sz), Nat.zero_le (L * L), Nat.zero_le (L * e), Nat.zero_le (e * L * L)]
      omega
    -- the remaining rounds are below their budgets
    have hrest : t₂ ≤ (e + 1) * D := by
      refine ht₂.trans ?_
      unfold powCost
      rw [hD]
      refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
      rw [hsz]
      nlinarith
    unfold powCost
    rw [← hD, Nat.succ_mul]
    omega

/-! ## Doubling a unary numeral -/

/-- Body of the doubling loop: on the state `cons u acc`, stop with `acc` if the counter `u` is
empty, and otherwise replace `acc` by `acc ++ acc` (reversal onto itself, `acc` being a list of
`nil`s) and decrement `u`. -/
def dblBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.let_ (.let_ (.cons (.var 3) (.var 3)) revOntoProg)
        (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))))

theorem dblBody_wellScoped : dblBody.WellScoped 1 := by
  simp [dblBody, WellScoped, revOntoProg, revOntoBody]

theorem dblBody_stop (a : ℕ) :
    ∃ t ≤ 2 * a + 8, Eval [Data.cons (ofNat 0) (ofNat a)] dblBody (.cons .nil (ofNat a)) t := by
  have run : Eval [Data.cons (ofNat 0) (ofNat a)] dblBody (.cons .nil (ofNat a)) _ :=
    Eval.elim_cons (env := [Data.cons (ofNat 0) (ofNat a)]) (i := 0) (n := .nil) (a := ofNat 0)
      (b := ofNat a) (by simp)
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := ofNat a) (by simp))))
  exact ⟨_, by simp only [size_ofNat]; omega, run⟩

theorem dblBody_step (m a : ℕ) :
    ∃ t ≤ (a + 1) * (4 * a + 14) + 10 * a + 2 * m + 30,
      Eval [Data.cons (ofNat (m + 1)) (ofNat a)] dblBody
        (.cons (.cons .nil .nil) (.cons (ofNat m) (ofNat (2 * a)))) t := by
  have hrev := revOntoProg_runs (List.replicate a .nil) (List.replicate a .nil)
    [.nil, ofNat m, ofNat (m + 1), ofNat a, Data.cons (ofNat (m + 1)) (ofNat a)] (4 * a + 2)
    (by rw [← ofNat_eq_list_replicate, size_ofNat]; omega)
  obtain ⟨t₁, ht₁, h₁⟩ := hrev
  have hres : Data.list ((List.replicate a Data.nil).reverse ++ List.replicate a .nil) = ofNat (2 * a) := by
    rw [List.reverse_replicate, ← List.replicate_add, ← ofNat_eq_list_replicate, Nat.two_mul]
  rw [hres, ← ofNat_eq_list_replicate] at h₁
  have run : Eval [Data.cons (ofNat (m + 1)) (ofNat a)] dblBody
      (.cons (.cons .nil .nil) (.cons (ofNat m) (ofNat (2 * a)))) _ :=
    Eval.elim_cons (env := [Data.cons (ofNat (m + 1)) (ofNat a)]) (i := 0) (n := .nil)
      (a := ofNat (m + 1)) (b := ofNat a) (by simp)
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat m) (by simp [ofNat])
        (Eval.let_
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := ofNat a) (by simp))
            (Eval.var_of_get (i := 3) (v := ofNat a) (by simp))) h₁)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 2) (v := ofNat m) (by simp))
              (Eval.var_of_get (i := 0) (v := ofNat (2 * a)) (by simp))))))
  refine ⟨_, ?_, run⟩
  simp only [size_ofNat, List.length_replicate] at ht₁ ⊢
  have : (a + 1) * (4 * a + 2 + 12) = (a + 1) * (4 * a + 14) := by ring
  omega

/-- The cost of the doubling loop: `m` rounds from the numeral `a`, the last on `2^m a`. -/
def dblCost (m a : ℕ) : ℕ := (m + 1) * ((2 ^ m * a + 1) * (4 * 2 ^ m * a + 14) + 10 * 2 ^ m * a + 2 * m + 32)

/-- The doubling loop: `dblBody` on `(m, a)` computes `2^m · a`. -/
theorem dblLoop_runs (m a : ℕ) (env : Env) :
    ∃ t ≤ dblCost m a,
      Eval (Data.cons (ofNat m) (ofNat a) :: env) (.loop dblBody) (ofNat (2 ^ m * a)) t := by
  induction m generalizing a with
  | zero =>
    obtain ⟨t, ht, h⟩ := dblBody_stop a
    refine ⟨t + 1, ?_, ?_⟩
    · unfold dblCost; simp only [pow_zero, one_mul]; nlinarith
    · simpa using Eval.loop_stop (Eval.append_of_wellScoped h dblBody_wellScoped env)
  | succ m ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := dblBody_step m a
    obtain ⟨t₂, ht₂, h₂⟩ := ih (2 * a)
    have hres : 2 ^ m * (2 * a) = 2 ^ (m + 1) * a := by ring
    rw [hres] at h₂
    refine ⟨t₁ + t₂ + 1, ?_,
      Eval.loop_step (Eval.append_of_wellScoped h₁ dblBody_wellScoped env) h₂⟩
    unfold dblCost at ht₂ ⊢
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [hpow]
    have ha : a ≤ 2 ^ m * a := Nat.le_mul_of_pos_left a (pow_pos (by norm_num) m)
    have h1 : (a + 1) * (4 * a + 14) ≤ (2 * 2 ^ m * a + 1) * (4 * (2 * 2 ^ m) * a + 14) :=
      Nat.mul_le_mul (by nlinarith) (by nlinarith)
    have h2 : (2 ^ m * (2 * a) + 1) * (4 * 2 ^ m * (2 * a) + 14) + 10 * 2 ^ m * (2 * a) + 2 * m + 32 ≤
        (2 * 2 ^ m * a + 1) * (4 * (2 * 2 ^ m) * a + 14) + 10 * (2 * 2 ^ m) * a + 2 * (m + 1) + 32 := by
      have e1 : 2 ^ m * (2 * a) = 2 * 2 ^ m * a := by ring
      have e2 : 4 * 2 ^ m * (2 * a) = 4 * (2 * 2 ^ m) * a := by ring
      have e3 : 10 * 2 ^ m * (2 * a) = 10 * (2 * 2 ^ m) * a := by ring
      rw [e1, e2, e3]; omega
    have h3 : t₂ ≤ (m + 1) * ((2 * 2 ^ m * a + 1) * (4 * (2 * 2 ^ m) * a + 14) +
        10 * (2 * 2 ^ m) * a + 2 * (m + 1) + 32) := ht₂.trans (Nat.mul_le_mul_left _ h2)
    rw [Nat.succ_mul]
    nlinarith

/-! ## Taking a prefix of given unary length -/

/-- Body of the take loop: on the state `cons u (cons rem cur)`, stop with `cons rem cur` if the
counter `u` is empty or `rem` is; otherwise move the head of `rem` onto `cur` and decrement. -/
def takeBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 3 .nil
        (.elim 0 (.cons .nil (.cons .nil (.var 1)))
          (.cons (.cons .nil .nil)
            (.cons (.var 5) (.cons (.var 1) (.cons (.var 0) (.var 3))))))))

theorem takeBody_wellScoped : takeBody.WellScoped 1 := by
  simp [takeBody, WellScoped]

/-- The state of the take loop. -/
def takeState (c : ℕ) (rem cur : List Data) : Data :=
  .cons (ofNat c) (.cons (.list rem) (.list cur))

theorem takeBody_stop_counter (rem cur : List Data) :
    ∃ t ≤ (Data.list rem).size + (Data.list cur).size + 8,
      Eval [takeState 0 rem cur] takeBody (.cons .nil (.cons (.list rem) (.list cur))) t := by
  have run : Eval [takeState 0 rem cur] takeBody (.cons .nil (.cons (.list rem) (.list cur))) _ :=
    Eval.elim_cons (env := [takeState 0 rem cur]) (i := 0) (n := .nil) (a := ofNat 0)
      (b := .cons (.list rem) (.list cur)) (by simp [takeState])
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (Eval.cons (Eval.nil _)
          (Eval.var_of_get (i := 1) (v := .cons (.list rem) (.list cur)) (by simp))))
  exact ⟨_, by simp only [Data.size_cons]; omega, run⟩

theorem takeBody_stop_empty (c : ℕ) (cur : List Data) :
    ∃ t ≤ (Data.list cur).size + 2 * c + 12,
      Eval [takeState (c + 1) [] cur] takeBody (.cons .nil (.cons (.list []) (.list cur))) t := by
  have run : Eval [takeState (c + 1) [] cur] takeBody (.cons .nil (.cons (.list []) (.list cur))) _ :=
    Eval.elim_cons (env := [takeState (c + 1) [] cur]) (i := 0) (n := .nil) (a := ofNat (c + 1))
      (b := .cons (.list []) (.list cur)) (by simp [takeState])
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat c) (by simp [ofNat])
        (Eval.elim_cons (i := 3) (n := .nil) (a := .list []) (b := .list cur) (by simp)
          (Eval.elim_nil (i := 0) (by simp)
            (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _)
              (Eval.var_of_get (i := 1) (v := .list cur) (by simp)))))))
  exact ⟨_, by omega, run⟩

theorem takeBody_step (c : ℕ) (h : Data) (rem cur : List Data) :
    ∃ t ≤ (Data.list rem).size + h.size + (Data.list cur).size + 2 * c + 18,
      Eval [takeState (c + 1) (h :: rem) cur] takeBody
        (.cons (.cons .nil .nil) (takeState c rem (h :: cur))) t := by
  have run : Eval [takeState (c + 1) (h :: rem) cur] takeBody
      (.cons (.cons .nil .nil) (takeState c rem (h :: cur))) _ :=
    Eval.elim_cons (env := [takeState (c + 1) (h :: rem) cur]) (i := 0) (n := .nil)
      (a := ofNat (c + 1)) (b := .cons (.list (h :: rem)) (.list cur)) (by simp [takeState])
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat c) (by simp [ofNat])
        (Eval.elim_cons (i := 3) (n := .nil) (a := .list (h :: rem)) (b := .list cur) (by simp)
          (Eval.elim_cons (i := 0) (a := h) (b := .list rem) (by simp)
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.cons (Eval.var_of_get (i := 5) (v := ofNat c) (by simp))
                (Eval.cons (Eval.var_of_get (i := 1) (v := .list rem) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 0) (v := h) (by simp))
                    (Eval.var_of_get (i := 3) (v := .list cur) (by simp)))))))))
  exact ⟨_, by simp only [size_ofNat]; omega, run⟩

/-- The take loop: `c` elements moved from `rem` onto `cur`, reversed. -/
theorem takeLoop_runs (c : ℕ) (rem cur : List Data) (env : Env) :
    ∃ t ≤ (c + 1) * ((Data.list rem).size + (Data.list cur).size + 2 * c + 20),
      Eval (takeState c rem cur :: env) (.loop takeBody)
        (.cons (.list (rem.drop c)) (.list ((rem.take c).reverse ++ cur))) t := by
  induction c generalizing rem cur with
  | zero =>
    obtain ⟨t, ht, h⟩ := takeBody_stop_counter rem cur
    refine ⟨t + 1, by omega, ?_⟩
    simpa using Eval.loop_stop (Eval.append_of_wellScoped h takeBody_wellScoped env)
  | succ c ih =>
    cases rem with
    | nil =>
      obtain ⟨t, ht, h⟩ := takeBody_stop_empty c cur
      refine ⟨t + 1, ?_, ?_⟩
      · simp only [Data.list_nil, Data.size_nil] at ht ⊢; nlinarith
      · simpa using Eval.loop_stop (Eval.append_of_wellScoped h takeBody_wellScoped env)
    | cons h rem =>
      obtain ⟨t₁, ht₁, h₁⟩ := takeBody_step c h rem cur
      obtain ⟨t₂, ht₂, h₂⟩ := ih rem (h :: cur)
      have hres : (rem.take c).reverse ++ (h :: cur) = ((h :: rem).take (c + 1)).reverse ++ cur := by
        simp [List.take_succ_cons, List.reverse_cons]
      rw [hres] at h₂
      refine ⟨t₁ + t₂ + 1, ?_,
        Eval.loop_step (Eval.append_of_wellScoped h₁ takeBody_wellScoped env) h₂⟩
      simp only [Data.size_list_cons] at ht₁ ht₂ ⊢
      have := Nat.succ_mul (c + 1) ((h.size + (Data.list rem).size + 1) + (Data.list cur).size + 2 * (c + 1) + 20)
      nlinarith

end Prog

end MIPRE.Cost
