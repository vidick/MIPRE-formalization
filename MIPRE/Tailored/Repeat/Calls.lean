/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Cost.Kleene
public import MIPRE.Foundations.Cost.Loops
public import MIPRE.Foundations.Cost.Unary
public import MIPRE.Foundations.Cost.PolyTime

@[expose] public section

/-!
# Programs in stages, and a loop of calls to a stored program

The programs of the repeated tailored verifier (Phase 2 of `planning/aldous-lyons-track.md`,
issue #280) are built in stages: polynomial-time functions, which prepare the next stage's input
while carrying what later stages need, alternate with calls to the input programs through the
universal machine. This module is the glue.

* `seq p q` runs `q` on the result of `p` (`seq_runs`, and its inversion `seq_inv`).
* `withCtx p` runs `p` on the second component of a pair and keeps the first: the context a
  later stage needs passes over a stage that does not.
* `mapCall univ`, on `(c, [q₁, …, q_m])`, runs `univ` on `(c, qᵢ)` for every `i` and returns the
  list of results. With `univ` the universal machine and `c` a program's description, it runs
  the program on every query. It halts with `[r₁, …, r_m]` when every call halts with `rᵢ`, at
  the cost of the calls plus a quadratic overhead (`mapCall_runs`), and only then
  (`mapCall_inv`), which is what lets a halting repeated program say that every coordinate's
  program halted.
-/

namespace MIPRE.Tailored.Calls

open Cost Cost.Data Cost.Prog

/-! ## Sequencing -/

/-- Run `q` on the result of `p`. -/
def seq (p q : Prog) : Prog := .let_ p q

theorem seq_wellScoped {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
    (seq p q).WellScoped 1 :=
  ⟨hp, hq.mono (by omega) _⟩

theorem seq_runs {p q : Prog} (hq : q.WellScoped 1) {x v r : Data} {s t : ℕ}
    (hp : p.Runs x v s) (hq' : q.Runs v r t) : (seq p q).Runs x r (s + t + 1) :=
  Eval.let_ hp (Eval.append_of_wellScoped hq' hq [x])

theorem seq_inv {p q : Prog} (hq : q.WellScoped 1) {x r : Data} {t : ℕ}
    (h : (seq p q).Runs x r t) : ∃ v s t', s + t' + 1 = t ∧ p.Runs x v s ∧ q.Runs v r t' := by
  change Eval [x] (.let_ p q) r t at h
  cases h with
  | let_ h₁ h₂ =>
    exact ⟨_, _, _, rfl, h₁, Eval.of_append_of_wellScoped (env := [_]) (extra := [x]) h₂ hq⟩

/-- A polynomial-time stage followed by `q`: a run of `q` on the stage's value is a run of the
sequence. -/
theorem seq_pure_runs {α β : Type*} [SizedEncoding α] [SizedEncoding β] (F : PolyTimeFun α β)
    {q : Prog} (hq : q.WellScoped 1) (a : α) {r : Data} {t : ℕ} (h : q.Runs (encode (F a)) r t) :
    ∃ s ≤ F.timeBound.eval (esize a), (seq F.code q).Runs (encode a) r (s + t + 1) := by
  obtain ⟨s, hs, hF⟩ := F.computes a
  exact ⟨s, hs, seq_runs hq hF h⟩

/-- Inversion of a polynomial-time stage followed by `q`. -/
theorem seq_pure_inv {α β : Type*} [SizedEncoding α] [SizedEncoding β] (F : PolyTimeFun α β)
    {q : Prog} (hq : q.WellScoped 1) (a : α) {r : Data} {t : ℕ}
    (h : (seq F.code q).Runs (encode a) r t) : ∃ t', q.Runs (encode (F a)) r t' := by
  obtain ⟨v, s, t', -, h₁, h₂⟩ := seq_inv hq h
  obtain ⟨s', -, hF⟩ := F.computes a
  obtain ⟨rfl, -⟩ := Eval.deterministic h₁ hF
  exact ⟨t', h₂⟩

/-- Inversion of a sequence whose first stage has a known run. -/
theorem seq_det_inv {p q : Prog} (hq : q.WellScoped 1) {x v r : Data} {s t : ℕ}
    (hp : p.Runs x v s) (h : (seq p q).Runs x r t) : ∃ t', q.Runs v r t' := by
  obtain ⟨v', s', t', -, h₁, h₂⟩ := seq_inv hq h
  obtain ⟨rfl, -⟩ := Eval.deterministic h₁ hp
  exact ⟨t', h₂⟩

/-! ## Keeping a context -/

/-- On `cons a b`, the pair `cons a (p b)`. -/
def withCtx (p : Prog) : Prog := .elim 0 .nil (.cons (.var 0) (callVar 1 p))

theorem withCtx_wellScoped {p : Prog} (hp : p.WellScoped 1) : (withCtx p).WellScoped 1 := by
  simp only [withCtx, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, by omega, hp.mono (by omega) _⟩

theorem withCtx_runs {p : Prog} (hp : p.WellScoped 1) (a : Data) {b r : Data} {t : ℕ}
    (h : p.Runs b r t) : (withCtx p).Runs (.cons a b) (.cons a r) (a.size + b.size + t + 5) := by
  have run : Eval [Data.cons a b] (withCtx p) (.cons a r) _ :=
    Eval.elim_cons (i := 0) (a := a) (b := b) rfl
      (Eval.cons (Eval.var_of_get (i := 0) (v := a) rfl)
        (callVar_eval hp (i := 1) (v := b) rfl h))
  exact run.cast_cost (by omega)

theorem withCtx_inv {p : Prog} (hp : p.WellScoped 1) {a b r : Data} {t : ℕ}
    (h : (withCtx p).Runs (.cons a b) r t) : ∃ r' t', t' ≤ t ∧ p.Runs b r' t' ∧ r = .cons a r' := by
  change Eval [Data.cons a b] (.elim 0 .nil _) r t at h
  cases h with
  | elim_nil hn _ => cases hn
  | elim_cons hc h₁ =>
    simp only [Env.get_cons_zero, Data.cons.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    cases h₁ with
    | cons h₂ h₃ =>
      cases h₂
      obtain ⟨t', ht', h'⟩ := callVar_runs_rev hp h₃
      exact ⟨_, t', by omega, h', rfl⟩

/-! ## The loop of calls -/

theorem sumSize_append (l₁ l₂ : List Data) : sumSize (l₁ ++ l₂) = sumSize l₁ + sumSize l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, sumSize_cons, ih]; omega

theorem size_list_reverse (l : List Data) : (list l.reverse).size = (list l).size := by
  rw [size_list_eq, size_list_eq, List.length_reverse]
  congr 2
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.reverse_cons, sumSize_append, ih, sumSize_cons, sumSize_nil]; omega

/-- The body of the loop, on the state `cons c (cons rem acc)`: stop with `acc` when `rem` is
empty; otherwise run `univ` on `cons c q` for the head `q` of `rem`, push the result onto `acc`
and continue with the tail. -/
def mapBody (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.elim 0 (.cons .nil (.var 1))
        (.let_ (.cons (.var 4) (.var 0))
          (.let_ (callVar 0 univ)
            (.cons (.cons .nil .nil) (.cons (.var 6) (.cons (.var 3) (.cons (.var 0) (.var 5)))))))))

theorem mapBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (mapBody univ).WellScoped 1 := by
  simp only [mapBody, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, trivial, by omega, ⟨trivial, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, hU.mono (by omega) _⟩, ⟨trivial, trivial⟩, by omega, by omega, by omega, by omega⟩

/-- **The loop of calls**: on `cons c (list qs)`, the list of the results of `univ` on
`cons c q`, `q ∈ qs`, in order. -/
def mapCall (univ : Prog) : Prog :=
  .elim 0 .nil
    (.let_ (.cons (.var 0) (.cons (.var 1) .nil))
      (.let_ (.loop (mapBody univ)) (callVar 0 revProg)))

theorem mapCall_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (mapCall univ).WellScoped 1 := by
  simp only [mapCall, WellScoped, callVar]
  exact ⟨by omega, trivial, ⟨by omega, by omega, trivial⟩,
    ⟨by omega, (mapBody_wellScoped hU).mono (by omega) _⟩,
    by omega, revProg_wellScoped.mono (by omega) _⟩

/-- The state of the loop. -/
def mapState (c : Data) (rem acc : List Data) : Data := .cons c (.cons (list rem) (list acc))

theorem mapBody_stop (univ : Prog) (c : Data) (acc : List Data) :
    Eval [mapState c [] acc] (mapBody univ) (.cons .nil (list acc)) ((list acc).size + 6) := by
  have run : Eval [mapState c [] acc] (mapBody univ) (.cons .nil (list acc)) _ :=
    Eval.elim_cons (i := 0) (a := c) (b := .cons .nil (list acc)) rfl
      (Eval.elim_cons (i := 1) (a := .nil) (b := list acc) rfl
        (Eval.elim_nil (i := 0) rfl (Eval.cons (Eval.nil _)
          (Eval.var_of_get (i := 1) (v := list acc) rfl))))
  exact run.cast_cost (by omega)

theorem mapBody_step {univ : Prog} (hU : univ.WellScoped 1) (c q : Data) (rest acc : List Data)
    {r : Data} {t : ℕ} (h : univ.Runs (.cons c q) r t) :
    Eval [mapState c (q :: rest) acc] (mapBody univ)
      (.cons (.cons .nil .nil) (mapState c rest (r :: acc)))
      (t + 3 * c.size + 2 * q.size + r.size + (list rest).size + (list acc).size + 22) := by
  have run : Eval [mapState c (q :: rest) acc] (mapBody univ)
      (.cons (.cons .nil .nil) (mapState c rest (r :: acc))) _ :=
    Eval.elim_cons (i := 0) (a := c) (b := .cons (list (q :: rest)) (list acc)) rfl
      (Eval.elim_cons (i := 1) (a := list (q :: rest)) (b := list acc) rfl
        (Eval.elim_cons (i := 0) (a := q) (b := list rest) rfl
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := c) rfl)
              (Eval.var_of_get (i := 0) (v := q) rfl))
            (Eval.let_ (callVar_eval hU (i := 0) (v := .cons c q) rfl h)
              (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.cons (Eval.var_of_get (i := 6) (v := c) rfl)
                  (Eval.cons (Eval.var_of_get (i := 3) (v := list rest) rfl)
                    (Eval.cons (Eval.var_of_get (i := 0) (v := r) rfl)
                      (Eval.var_of_get (i := 5) (v := list acc) rfl)))))))))
  exact run.cast_cost (by simp only [mapState, size_cons, size_list_cons]; omega)

/-- Inversion of the body: on an empty `rem` it stops with `acc`; otherwise it ran `univ` on the
head and continues. -/
theorem mapBody_inv {univ : Prog} (hU : univ.WellScoped 1) (c : Data) (rem acc : List Data)
    {out : Data} {t : ℕ} (h : Eval [mapState c rem acc] (mapBody univ) out t) :
    (rem = [] ∧ out = .cons .nil (list acc)) ∨
      ∃ q rest r, rem = q :: rest ∧ (∃ t', univ.Runs (.cons c q) r t') ∧
        out = .cons (.cons .nil .nil) (mapState c rest (r :: acc)) := by
  rcases rem with _ | ⟨q, rest⟩
  · exact Or.inl ⟨rfl, (h.deterministic (mapBody_stop univ c acc)).1⟩
  · refine Or.inr ⟨q, rest, ?_⟩
    change Eval _ (.elim 0 .nil _) out t at h
    cases h with
    | elim_nil hn _ => cases hn
    | elim_cons hc h₁ =>
      simp only [mapState, Env.get_cons_zero, Data.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h₁ with
      | elim_nil hn _ => cases hn
      | elim_cons hc h₂ =>
        simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        cases h₂ with
        | elim_nil hn _ => cases hn
        | elim_cons hc h₃ =>
          simp only [Env.get_cons_zero, list_cons, Data.cons.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h₃ with
          | let_ h₄ h₅ =>
            cases h₄ with
            | cons h₆ h₇ =>
              cases h₆; cases h₇
              cases h₅ with
              | let_ h₈ h₉ =>
                obtain ⟨t', -, hr⟩ := callVar_runs_rev hU h₈
                refine ⟨_, rfl, ⟨t', hr⟩, ?_⟩
                cases h₉ with
                | cons h₁₀ h₁₁ =>
                  cases h₁₀ with
                  | cons h₁₂ h₁₃ =>
                    cases h₁₂; cases h₁₃
                    cases h₁₁ with
                    | cons h₁₄ h₁₅ =>
                      cases h₁₄
                      cases h₁₅ with
                      | cons h₁₆ h₁₇ =>
                        cases h₁₆
                        cases h₁₇ with
                        | cons h₁₈ h₁₉ => cases h₁₈; cases h₁₉; rfl

/-- The loop with the results known: from the state `(c, rem, acc)`, the loop stops with the
results on `rem`, reversed, before `acc`. -/
theorem mapLoop_runs {univ : Prog} (hU : univ.WellScoped 1) (c : Data) (f : Data → Data)
    (T Z : ℕ) (env : Env) :
    ∀ (rem acc : List Data),
      (∀ q ∈ rem, ∃ t ≤ T, univ.Runs (.cons c q) (f q) t) →
      (list rem).size + (list (rem.map f)).size + (list acc).size ≤ Z →
      ∃ t ≤ (rem.length + 1) * (T + 3 * c.size + 2 * Z + 25),
        Eval (mapState c rem acc :: env) (.loop (mapBody univ))
          (list ((rem.map f).reverse ++ acc)) t
  | [], acc, _, hZ => by
    refine ⟨_, ?_, .loop_stop (Eval.append_of_wellScoped (mapBody_stop univ c acc)
      (mapBody_wellScoped hU) env)⟩
    simp only [list_nil, List.map_nil, size_nil] at hZ
    simp only [List.length_nil, zero_add, one_mul, List.map_nil, List.reverse_nil,
      List.nil_append]
    omega
  | q :: rest, acc, hq, hZ => by
    obtain ⟨t₁, ht₁, h₁⟩ := hq q (by simp)
    have hb := mapBody_step hU c q rest acc h₁
    have hZ' : (list rest).size + (list (rest.map f)).size + (list (f q :: acc)).size ≤ Z := by
      simp only [List.map_cons, size_list_cons] at hZ ⊢
      omega
    obtain ⟨t₂, ht₂, h₂⟩ := mapLoop_runs hU c f T Z env rest (f q :: acc)
      (fun q' hq' => hq q' (by simp [hq'])) hZ'
    refine ⟨_, ?_, .loop_step (Eval.append_of_wellScoped hb (mapBody_wellScoped hU) env)
      (by simpa using h₂)⟩
    simp only [List.map_cons, size_list_cons] at hZ
    simp only [List.length_cons]
    have : (rest.length + 1 + 1) * (T + 3 * c.size + 2 * Z + 25) =
        (rest.length + 1) * (T + 3 * c.size + 2 * Z + 25) + (T + 3 * c.size + 2 * Z + 25) := by
      ring
    omega

/-- Inversion of the loop: a halting loop ran every call. -/
theorem mapLoop_inv {univ : Prog} (hU : univ.WellScoped 1) (c : Data) (env : Env) :
    ∀ (rem acc : List Data) {r : Data} {t : ℕ},
      Eval (mapState c rem acc :: env) (.loop (mapBody univ)) r t →
      ∃ rs : List Data, List.Forall₂ (fun q r => ∃ t', univ.Runs (.cons c q) r t') rem rs ∧
        r = list (rs.reverse ++ acc)
  | rem, acc, r, t, h => by
    cases h with
    | loop_nil hb =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (mapBody_wellScoped hU)
      rcases mapBody_inv hU c rem acc hb' with ⟨-, h⟩ | ⟨_, _, _, -, -, h⟩ <;> cases h
    | loop_stop hb =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (mapBody_wellScoped hU)
      rcases mapBody_inv hU c rem acc hb' with ⟨rfl, h⟩ | ⟨_, _, _, -, -, h⟩
      · simp only [Data.cons.injEq, true_and] at h
        exact ⟨[], .nil, by simp [h]⟩
      · simp at h
    | loop_step hb hrest =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (mapBody_wellScoped hU)
      rcases mapBody_inv hU c rem acc hb' with ⟨-, h⟩ | ⟨q, rest, rq, rfl, hq, h⟩
      · simp at h
      · simp only [Data.cons.injEq, true_and] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨rs, hrs, rfl⟩ := mapLoop_inv hU c env rest (rq :: acc) (by simpa using hrest)
        exact ⟨rq :: rs, .cons hq hrs, by simp⟩

/-- The cost of `mapCall` with calls of cost at most `T`, `m` queries and sizes at most `Z`. -/
def mapCallCost (m T C Z : ℕ) : ℕ := (m + 1) * (T + 3 * C + 2 * Z + 25) + (m + 2) * (Z + 13) + 4 * C + 3 * Z + 20

/-- **The loop of calls with the results known.** -/
theorem mapCall_runs {univ : Prog} (hU : univ.WellScoped 1) (c : Data) (qs : List Data)
    (f : Data → Data) (T Z : ℕ) (hq : ∀ q ∈ qs, ∃ t ≤ T, univ.Runs (.cons c q) (f q) t)
    (hZ : (list qs).size + (list (qs.map f)).size + 1 ≤ Z) :
    ∃ t ≤ mapCallCost qs.length T c.size Z,
      (mapCall univ).Runs (.cons c (list qs)) (list (qs.map f)) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := mapLoop_runs hU c f T Z
    [c, list qs, .cons c (list qs)] qs [] hq (by simpa using hZ)
  obtain ⟨t₂, ht₂, h₂⟩ := revProg_runs (qs.map f).reverse
  rw [List.reverse_reverse] at h₂
  rw [List.append_nil] at h₁
  have run : Eval [Data.cons c (list qs)] (mapCall univ) (list (qs.map f)) _ :=
    Eval.elim_cons (i := 0) (a := c) (b := list qs) rfl
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := c) rfl)
          (Eval.cons (Eval.var_of_get (i := 1) (v := list qs) rfl) (Eval.nil _)))
        (Eval.let_ h₁
          (callVar_eval revProg_wellScoped (i := 0) (v := list (qs.map f).reverse) rfl h₂)))
  refine ⟨_, ?_, run⟩
  have hl : ((qs.map f).reverse).length = qs.length := by simp
  have hs := size_list_reverse (qs.map f)
  unfold mapCallCost
  rw [hl, hs] at ht₂
  have h2 : (qs.length + 1 + 1) * ((list (qs.map f)).size + 1 + 12) ≤ (qs.length + 2) * (Z + 13) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **Inversion of the loop of calls**: a halting run ran `univ` on every query, and returned
the results in order. -/
theorem mapCall_inv {univ : Prog} (hU : univ.WellScoped 1) (c : Data) (qs : List Data)
    {r : Data} {t : ℕ} (h : (mapCall univ).Runs (.cons c (list qs)) r t) :
    ∃ rs : List Data, List.Forall₂ (fun q r => ∃ t', univ.Runs (.cons c q) r t') qs rs ∧
      r = list rs := by
  change Eval [Data.cons c (list qs)] (.elim 0 .nil _) r t at h
  cases h with
  | elim_nil hn _ => cases hn
  | elim_cons hc h₁ =>
    simp only [Env.get_cons_zero, Data.cons.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    cases h₁ with
    | let_ h₂ h₃ =>
      cases h₂ with
      | cons h₄ h₅ =>
        cases h₄
        cases h₅ with
        | cons h₆ h₇ =>
          cases h₆; cases h₇
          cases h₃ with
          | let_ h₈ h₉ =>
            obtain ⟨rs, hrs, rfl⟩ := mapLoop_inv hU _ _ qs [] (by simpa [mapState] using h₈)
            obtain ⟨t', -, h'⟩ := callVar_runs_rev revProg_wellScoped h₉
            obtain ⟨t₂, -, h₂⟩ := revProg_runs rs.reverse
            rw [List.reverse_reverse] at h₂
            simp only [Env.get_cons_zero, List.append_nil] at h'
            exact ⟨rs, hrs, (Eval.deterministic h' h₂).1⟩

/-! ## Runs within a bound -/

/-- `p` runs on `x` to `r` within cost `T`. -/
def RunsLe (p : Prog) (x r : Data) (T : ℕ) : Prop := ∃ t ≤ T, p.Runs x r t

namespace RunsLe

theorem runs {p : Prog} {x r : Data} {T : ℕ} (h : RunsLe p x r T) : ∃ t, p.Runs x r t :=
  let ⟨t, _, h⟩ := h; ⟨t, h⟩

theorem mono {p : Prog} {x r : Data} {T T' : ℕ} (h : RunsLe p x r T) (hT : T ≤ T') :
    RunsLe p x r T' :=
  let ⟨t, ht, h⟩ := h; ⟨t, ht.trans hT, h⟩

theorem seq {p q : Prog} (hq : q.WellScoped 1) {x v r : Data} {S T : ℕ} (hp : RunsLe p x v S)
    (hq' : RunsLe q v r T) : RunsLe (Calls.seq p q) x r (S + T + 1) :=
  let ⟨s, hs, hp⟩ := hp
  let ⟨t, ht, hq'⟩ := hq'
  ⟨_, by omega, seq_runs hq hp hq'⟩

theorem withCtx {p : Prog} (hp : p.WellScoped 1) (a : Data) {b r : Data} {T : ℕ}
    (h : RunsLe p b r T) : RunsLe (Calls.withCtx p) (.cons a b) (.cons a r) (a.size + b.size + T + 5) :=
  let ⟨t, ht, h⟩ := h
  ⟨_, by omega, withCtx_runs hp a h⟩

theorem pure {α β : Type*} [SizedEncoding α] [SizedEncoding β] (F : PolyTimeFun α β) (a : α) :
    RunsLe F.code (encode a) (encode (F a)) (F.timeBound.eval (esize a)) :=
  F.computes a

theorem size_le {p : Prog} {x r : Data} {T : ℕ} (h : RunsLe p x r T) : r.size ≤ T :=
  let ⟨_, ht, h⟩ := h; (Eval.size_le h).trans ht

theorem mapCall {univ : Prog} (hU : univ.WellScoped 1) (c : Data) (qs : List Data)
    (f : Data → Data) (T Z : ℕ) (hq : ∀ q ∈ qs, RunsLe univ (.cons c q) (f q) T)
    (hZ : (list qs).size + (list (qs.map f)).size + 1 ≤ Z) :
    RunsLe (Calls.mapCall univ) (.cons c (list qs)) (list (qs.map f))
      (mapCallCost qs.length T c.size Z) :=
  mapCall_runs hU c qs f T Z hq hZ

end RunsLe

end MIPRE.Tailored.Calls

end
