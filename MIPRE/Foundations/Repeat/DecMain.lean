/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.DecLoop
import MIPRE.Foundations.Halting.Serial
import MIPRE.Foundations.Halting.Arith
import MIPRE.Foundations.Repeat.Bits
import MIPRE.Foundations.Repeat.Sampler

/-!
# The program of the repeated decider

The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`;
`planning/repetition-verifier.md`, R3(c)) as a program of the ambient model, before the s-m-n
construction. On `((S̄, D̄, λ, τ, β), (n, x, y, a, b))` it

1. sanitizes `x, y, a, b` into bit strings (`bitsProg`: every element read as a bit), so that
   the rest of the program is total on every datum;
2. computes, in unary, `s = s(n)` from `S̄`, `m = τ(|λ| + |n|)`, the repetition count
   `k = 2^m`, the question length `k s`, and the parse length `B = 2^{β(|λ| + |n|)}`;
3. checks `|x| = |y| = k s` and that `a`, `b` are the serializations of the data they parse to
   (`Data.parse`, `Data.toBitsPost`), the four verdicts combined by `andExpr`;
4. runs the coordinate loop `coordBody` on the state `(k, x, y, parse a, parse b, (D̄, n, s, B))`.

`prepProg` is steps 1–3, returning the state of the loop or `nil`; its run lemma
`prepProg_runs` is a straight line of deterministic steps, generated mechanically.
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## Sanitizing a list into a bit string -/

/-- Body of the sanitizer: on `cons rem acc`, move the head of `rem`, read as a bit, onto `acc`. -/
def bitsBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 0
        (.cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3))))
        (.cons (.cons .nil .nil) (.cons (.var 3) (.cons (.cons .nil .nil) (.var 5))))))

theorem bitsBody_wellScoped : bitsBody.WellScoped 1 := by simp [bitsBody, WellScoped]

/-- The sanitizer: the bits of a list, `encode (bitsOf l)`. -/
def bitsProg : Prog := .let_ (.cons (.var 0) .nil) (.let_ (.loop bitsBody) (callVar 0 revProg))

theorem bitsProg_wellScoped : bitsProg.WellScoped 1 := by
  simp [bitsProg, WellScoped, bitsBody, callVar, revProg, revOntoProg, revOntoBody]

theorem bitsBody_stop (acc : List Data) :
    ∃ t ≤ (list acc).size + 6, Eval [Data.cons (list []) (list acc)] bitsBody (.cons .nil (list acc)) t :=
  ⟨_, by omega, Eval.elim_cons (i := 0) (n := .nil) (a := list []) (b := list acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := list acc) (by simp))))⟩

theorem bitsBody_step (h : Data) (l acc : List Data) :
    ∃ t ≤ (list l).size + (list acc).size + h.size + 12,
      Eval [Data.cons (list (h :: l)) (list acc)] bitsBody
        (.cons (.cons .nil .nil) (.cons (list l) (list (ofBool (bitOf h) :: acc)))) t := by
  rcases h with _ | ⟨h₀, h₁⟩
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (n := .nil) (a := list (.nil :: l)) (b := list acc) (by simp)
      (Eval.elim_cons (i := 0) (a := .nil) (b := list l) (by simp)
        (Eval.elim_nil (i := 0) (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 1) (v := list l) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 3) (v := list acc) (by simp)))))))⟩
    simp only [size_cons, size_nil]; omega
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (n := .nil) (a := list (.cons h₀ h₁ :: l)) (b := list acc)
      (by simp)
      (Eval.elim_cons (i := 0) (a := .cons h₀ h₁) (b := list l) (by simp)
        (Eval.elim_cons (i := 0) (a := h₀) (b := h₁) (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 3) (v := list l) (by simp))
              (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.var_of_get (i := 5) (v := list acc) (by simp)))))))⟩
    have := size_pos h₀
    have := size_pos h₁
    simp only [size_cons, size_nil, bitOf, ofBool]; omega

theorem bitsLoop_runs (l acc : List Data) (env : Env) (S : ℕ)
    (hS : (list l).size + (list acc).size + 2 * l.length ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 14),
      Eval (Data.cons (list l) (list acc) :: env) (.loop bitsBody)
        (list ((l.map fun h => ofBool (bitOf h)).reverse ++ acc)) t := by
  induction l generalizing acc with
  | nil =>
    obtain ⟨t, ht, h⟩ := bitsBody_stop acc
    refine ⟨t + 1, by simp at hS ⊢; omega, ?_⟩
    simpa using Eval.loop_stop (Eval.append_of_wellScoped h bitsBody_wellScoped env)
  | cons h l ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := bitsBody_step h l acc
    have hb : (ofBool (bitOf h)).size ≤ 3 := size_ofBool _
    have hh := size_pos h
    obtain ⟨t₂, ht₂, h₂⟩ := ih (ofBool (bitOf h) :: acc) (by
      simp only [size_list_cons, List.length_cons] at hS ⊢
      omega)
    have hres : (l.map fun h => ofBool (bitOf h)).reverse ++ ofBool (bitOf h) :: acc =
        ((h :: l).map fun h => ofBool (bitOf h)).reverse ++ acc := by
      simp
    rw [hres] at h₂
    refine ⟨t₁ + t₂ + 1, ?_, Eval.loop_step (Eval.append_of_wellScoped h₁ bitsBody_wellScoped env) h₂⟩
    simp only [size_list_cons, List.length_cons] at hS ht₂ ⊢
    have : (l.length + 1 + 1) * (S + 14) = (l.length + 1) * (S + 14) + (S + 14) := by ring
    omega

/-- The sanitizer computes `encode (bitsOf l)` on `list l`. -/
theorem bitsProg_runs (l : List Data) :
    ∃ t ≤ (l.length + 2) * ((list l).size + 2 * l.length + 15) + (l.length + 2) * (4 * l.length + 20),
      bitsProg.Runs (list l) (encode (bitsOf l)) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := bitsLoop_runs l [] [list l] ((list l).size + 1 + 2 * l.length) (by simp)
  set rev := (l.map fun h => ofBool (bitOf h)).reverse ++ [] with hrev
  obtain ⟨t₂, ht₂, h₂⟩ := revProg_runs rev
  have hrev' : rev.reverse = l.map fun h => ofBool (bitOf h) := by simp [hrev]
  rw [hrev'] at h₂
  have hlen : rev.length = l.length := by simp [hrev]
  have hsz : (list rev).size ≤ 4 * l.length + 1 := by
    rw [hrev, List.append_nil, size_list_reverse, ← ofList_eq_list]
    exact size_ofList_le (fun h => by cases bitOf h <;> simp [ofBool]) l
  have run : bitsProg.Runs (list l) (encode (bitsOf l)) _ :=
    Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := list l) (by simp)) (Eval.nil _))
      (Eval.let_ (by simpa using h₁)
        (by
          have := callVar_eval revProg_wellScoped (env := [list rev, .cons (list l) (list []), list l])
            (i := 0) (v := list rev) (by simp) h₂
          simpa [bitsOf, encode_bitStr_eq_list, List.map_map, Function.comp_def] using this))
  refine ⟨_, ?_, run⟩
  rw [hlen] at ht₂
  have h₂' : (l.length + 1 + 1) * ((list rev).size + 1 + 12) ≤ (l.length + 2) * (4 * l.length + 15) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h₁' : (l.length + 1) * ((list l).size + 1 + 2 * l.length + 14) ≤
      (l.length + 2) * ((list l).size + 2 * l.length + 15) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (l.length + 2) * (4 * l.length + 20) =
      (l.length + 2) * (4 * l.length + 15) + 5 * l.length + 10 := by ring
  have e2 : (l.length + 2) * ((list l).size + 2 * l.length + 15) =
      (l.length + 1) * ((list l).size + 1 + 2 * l.length + 14) + ((list l).size + 2 * l.length + 15) := by
    ring
  omega

/-! ## Conjunction of four verdicts -/

/-- `ok₁ ∧ ok₂ ∧ ok₃ ∧ ok₄` on encoded booleans at the given indices (each test extends the
environment by two entries). -/
def andExpr (i₁ i₂ i₃ i₄ : ℕ) : Prog :=
  .elim i₁ .nil (.elim (i₂ + 2) .nil (.elim (i₃ + 4) .nil (.elim (i₄ + 6) .nil (.cons .nil .nil))))

theorem andExpr_runs {env : Env} {i₁ i₂ i₃ i₄ : ℕ} {c₁ c₂ c₃ c₄ : Bool}
    (h₁ : env.get i₁ = ofBool c₁) (h₂ : env.get i₂ = ofBool c₂) (h₃ : env.get i₃ = ofBool c₃)
    (h₄ : env.get i₄ = ofBool c₄) :
    ∃ t ≤ 8, Eval env (andExpr i₁ i₂ i₃ i₄) (ofBool (c₁ && c₂ && c₃ && c₄)) t := by
  unfold andExpr
  cases c₁
  · exact ⟨2, by omega, Eval.elim_nil (i := i₁) (by simpa [ofBool] using h₁) (Eval.nil _)⟩
  cases c₂
  · exact ⟨3, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_nil (i := i₂ + 2) (by simpa [ofBool] using h₂) (Eval.nil _))⟩
  cases c₃
  · exact ⟨4, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_cons (i := i₂ + 2) (a := .nil) (b := .nil) (by simpa [ofBool] using h₂)
        (Eval.elim_nil (i := i₃ + 4) (by simpa [ofBool] using h₃) (Eval.nil _)))⟩
  cases c₄
  · exact ⟨5, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_cons (i := i₂ + 2) (a := .nil) (b := .nil) (by simpa [ofBool] using h₂)
        (Eval.elim_cons (i := i₃ + 4) (a := .nil) (b := .nil) (by simpa [ofBool] using h₃)
          (Eval.elim_nil (i := i₄ + 6) (by simpa [ofBool] using h₄) (Eval.nil _))))⟩
  · exact ⟨7, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_cons (i := i₂ + 2) (a := .nil) (b := .nil) (by simpa [ofBool] using h₂)
        (Eval.elim_cons (i := i₃ + 4) (a := .nil) (b := .nil) (by simpa [ofBool] using h₃)
          (Eval.elim_cons (i := i₄ + 6) (a := .nil) (b := .nil) (by simpa [ofBool] using h₄)
            (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩

theorem powLoop_wellScoped : (Prog.loop powBody).WellScoped 1 := ⟨Nat.zero_lt_one, powBody_wellScoped⟩
theorem dblLoop_wellScoped : (Prog.loop dblBody).WellScoped 1 := ⟨Nat.zero_lt_one, dblBody_wellScoped⟩

/-! ## The straight-line prefix of the decider (generated) -/

/-- The input of `prepProg`: `(S̄, D̄, λ, τ, β, n, x, y, a, b)`. -/
def decInput (sP dP lamD tauD betaD nD xD yD aD bD : Data) : Data :=
  (Data.cons sP (Data.cons dP (Data.cons lamD (Data.cons tauD (Data.cons betaD (Data.cons nD (Data.cons xD (Data.cons yD (Data.cons aD bD)))))))))

/-- Steps 1–3 of the repeated decider, returning the state of the coordinate loop or `nil`. -/
def prepProg (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.let_ (.cons (.var 16) (.cons (.var 6) (.const (encode CL.Sampler.Query.dimension)))) (.let_ (callVar 0 univ) (.let_ (callVar 0 toUnaryProg) (.let_ (callVar 13 toUnaryProg) (.let_ (.cons (.var 0) (.cons (.var 16) (.cons (.var 10) .nil))) (.let_ (callVar 0 (.loop powBody)) (.let_ (.cons (.var 0) (.var 3)) (.let_ (callVar 0 (.loop dblBody)) (.let_ (.const (ofNat 1)) (.let_ (.cons (.var 3) (.var 0)) (.let_ (callVar 0 (.loop dblBody)) (.let_ (callVar 19 toUnaryProg) (.let_ (.cons (.var 0) (.cons (.var 24) (.cons (.var 18) .nil))) (.let_ (callVar 0 (.loop powBody)) (.let_ (.cons (.var 0) (.var 5)) (.let_ (callVar 0 (.loop dblBody)) (.let_ (callVar 20 bitsProg) (.let_ (callVar 19 bitsProg) (.let_ (callVar 18 bitsProg) (.let_ (callVar 20 bitsProg) (.let_ (callVar 3 lenProg) (.let_ (.cons (.var 0) (.var 13)) (.let_ (callVar 0 eqBitsProg) (.let_ (callVar 5 lenProg) (.let_ (.cons (.var 0) (.var 16)) (.let_ (callVar 0 eqBitsProg) (.let_ (callVar 7 parseProg) (.let_ (callVar 0 serProg) (.let_ (.cons (.var 0) (.var 9)) (.let_ (callVar 0 eqBitsProg) (.let_ (callVar 10 parseProg) (.let_ (callVar 0 serProg) (.let_ (.cons (.var 0) (.var 12)) (.let_ (callVar 0 eqBitsProg) ((.let_ (andExpr 11 8 4 0) (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19)))) (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11) (.cons (.var 7) (.var 2))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The environment of `prepProg` after its straight-line prefix, in terms of the parameters. -/
def prepEnv (univ : Prog) (sP dP : Data) (lam tau beta n s : ℕ) (xD yD aD bD : Data) : Env :=
  [(ofBool ((parse (bitsOf (toList bD))).toBitsPost == (bitsOf (toList bD)))), (Data.cons (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD)))), (encode (parse (bitsOf (toList bD))).toBitsPost), (parse (bitsOf (toList bD))), (ofBool ((parse (bitsOf (toList aD))).toBitsPost == (bitsOf (toList aD)))), (Data.cons (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD)))), (encode (parse (bitsOf (toList aD))).toBitsPost), (parse (bitsOf (toList aD))), (ofBool (decide ((bitsOf (toList yD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))), (Data.cons (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))), (ofNat (bitsOf (toList yD)).length), (ofBool (decide ((bitsOf (toList xD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))), (Data.cons (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))), (ofNat (bitsOf (toList xD)).length), (encode (bitsOf (toList bD))), (encode (bitsOf (toList aD))), (encode (bitsOf (toList yD))), (encode (bitsOf (toList xD))), (ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))), (Data.cons (ofNat (beta * (Nat.size lam + Nat.size n))) (ofNat 1)), (ofNat (beta * (Nat.size lam + Nat.size n))), (Data.cons (ofNat beta) (Data.cons (encode lam) (Data.cons (encode n) Data.nil))), (ofNat beta), (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))), (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat 1)), (ofNat 1), (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)), (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat s)), (ofNat (tau * (Nat.size lam + Nat.size n))), (Data.cons (ofNat tau) (Data.cons (encode lam) (Data.cons (encode n) Data.nil))), (ofNat tau), (ofNat s), (encode s), (Data.cons sP (Data.cons (encode n) (encode CL.Sampler.Query.dimension))), aD, bD, yD, (Data.cons aD bD), xD, (Data.cons yD (Data.cons aD bD)), (encode n), (Data.cons xD (Data.cons yD (Data.cons aD bD))), (encode beta), (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))), (encode tau), (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))), (encode lam), (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))), dP, (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))))), sP, (Data.cons dP (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))))), decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD]

-- indices: ex 11, ey 8, ea 4, eb 0, ok 1; final: uk 27, xq 21, yq 20, pa 11, pb 7, ctx 2

/-- The cost of the sanitizer on a list of length `L` and size `sz`. -/
def bitsCost (L sz : ℕ) : ℕ := (L + 2) * (sz + 2 * L + 15) + (L + 2) * (4 * L + 20)

/-- The cost of `lenProg` on a list of length `L` and size `sz`. -/
def lenCost (L sz : ℕ) : ℕ := (L + 1 + 1) * (sz + 1 + 2 * L + 13)

/-- The cost of `eqBitsProg` on `l₁`, `l₂`. -/
def eqCost (l₁ l₂ : Data) : ℕ := (l₁.spine + 1) * (l₁.size + l₂.size + 21)

/-- The cost of `parseProg` on `x`. -/
def parseCost (x : BitStr) : ℕ := (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25)

/-- The cost of `serProg` on `d`. -/
def serCost (d : Data) : ℕ := (3 * d.size + 2) * (16 * d.size + 42) + (d.size + 2) * (5 * d.size + 30)

/-- The cost of the straight-line prefix of `prepProg`. -/
def prepPreCost (sP dP : Data) (lam tau beta n s : ℕ) (xD yD aD bD : Data) (td : ℕ) : ℕ :=
  6 * (td + toUnaryCost s + toUnaryCost tau + toUnaryCost beta +
    powCost tau (Nat.size lam + Nat.size n) ((encode lam : Data).size + (encode n : Data).size + 1) +
    powCost beta (Nat.size lam + Nat.size n) ((encode lam : Data).size + (encode n : Data).size + 1) +
    dblCost (tau * (Nat.size lam + Nat.size n)) s + dblCost (tau * (Nat.size lam + Nat.size n)) 1 + dblCost (beta * (Nat.size lam + Nat.size n)) 1 +
    bitsCost (toList xD).length xD.size + bitsCost (toList yD).length yD.size +
    bitsCost (toList aD).length aD.size + bitsCost (toList bD).length bD.size +
    lenCost (bitsOf (toList xD)).length (encode (bitsOf (toList xD)) : Data).size + lenCost (bitsOf (toList yD)).length (encode (bitsOf (toList yD)) : Data).size +
    eqCost (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) + eqCost (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) +
    parseCost (bitsOf (toList aD)) + serCost (parse (bitsOf (toList aD))) +
    eqCost (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD))) +
    parseCost (bitsOf (toList bD)) + serCost (parse (bitsOf (toList bD))) +
    eqCost (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD)))) +
  8 * (sP.size + dP.size + (encode lam : Data).size + (encode tau : Data).size +
    (encode beta : Data).size + (encode n : Data).size + xD.size + yD.size + aD.size + bD.size) + 500

theorem prepProg_prefix {univ : Prog} (hU : univ.WellScoped 1) (sP dP : Data)
    (lam tau beta n s : ℕ) (xD yD aD bD : Data) {td : ℕ}
    (hdim : Eval [Data.cons sP (.cons (encode n) (encode CL.Sampler.Query.dimension))] univ (encode s) td)
    {r : Data} {t : ℕ}
    (hc : Eval (prepEnv univ sP dP lam tau beta n s xD yD aD bD) (.let_ (andExpr 11 8 4 0) (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19)))) (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11) (.cons (.var 7) (.var 2))))))))) r t) :
    ∃ t' ≤ t + prepPreCost sP dP lam tau beta n s xD yD aD bD td,
      Eval [decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD] (prepProg univ) r t' := by
  obtain ⟨t_us, ht_us, h_us⟩ := toUnaryProg_runs s
  obtain ⟨t_ut, ht_ut, h_ut⟩ := toUnaryProg_runs tau
  obtain ⟨t_ub, ht_ub, h_ub⟩ := toUnaryProg_runs beta
  obtain ⟨t_mt, ht_mt, h_mt⟩ := powLoop_runs tau (lam.bits.map ofBool) (n.bits.map ofBool) [] []
  obtain ⟨t_mb, ht_mb, h_mb⟩ := powLoop_runs beta (lam.bits.map ofBool) (n.bits.map ofBool) [] []
  simp only [List.append_nil, ← ofNat_eq_list_replicate, List.length_map, Nat.size_eq_bits_len,
    powState, list_nil, ← encode_nat_eq_list, size_nil] at h_mt h_mb ht_mt ht_mb
  obtain ⟨t_uks, ht_uks, h_uks⟩ := dblLoop_runs (tau * (Nat.size lam + Nat.size n)) s []
  obtain ⟨t_uk, ht_uk, h_uk⟩ := dblLoop_runs (tau * (Nat.size lam + Nat.size n)) 1 []
  rw [mul_one] at h_uk
  obtain ⟨t_uB, ht_uB, h_uB⟩ := dblLoop_runs (beta * (Nat.size lam + Nat.size n)) 1 []
  rw [mul_one] at h_uB
  obtain ⟨t_x, ht_x, h_x⟩ := bitsProg_runs (toList xD)
  obtain ⟨t_y, ht_y, h_y⟩ := bitsProg_runs (toList yD)
  obtain ⟨t_a, ht_a, h_a⟩ := bitsProg_runs (toList aD)
  obtain ⟨t_b, ht_b, h_b⟩ := bitsProg_runs (toList bD)
  rw [list_toList] at h_x h_y h_a h_b ht_x ht_y ht_a ht_b
  obtain ⟨t_lx, ht_lx, h_lx⟩ := lenProg_runs ((bitsOf (toList xD)).map ofBool)
  obtain ⟨t_ly, ht_ly, h_ly⟩ := lenProg_runs ((bitsOf (toList yD)).map ofBool)
  rw [← encode_bitStr_eq_list, List.length_map] at h_lx h_ly ht_lx ht_ly
  obtain ⟨t_ex, ht_ex, h_ex⟩ := eqBitsProg_runs (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) [] _ le_rfl
  obtain ⟨t_ey, ht_ey, h_ey⟩ := eqBitsProg_runs (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) [] _ le_rfl
  rw [eqBits_ofNat] at h_ex h_ey
  simp only [encode_bool] at h_ex h_ey
  obtain ⟨t_pa, ht_pa, h_pa⟩ := parseProg_runs (bitsOf (toList aD))
  obtain ⟨t_sa, ht_sa, h_sa⟩ := serProg_runs (parse (bitsOf (toList aD)))
  obtain ⟨t_ea, ht_ea, h_ea⟩ := eqBitsProg_runs (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD))) [] _ le_rfl
  obtain ⟨t_pb, ht_pb, h_pb⟩ := parseProg_runs (bitsOf (toList bD))
  obtain ⟨t_sb, ht_sb, h_sb⟩ := serProg_runs (parse (bitsOf (toList bD)))
  obtain ⟨t_eb, ht_eb, h_eb⟩ := eqBitsProg_runs (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD))) [] _ le_rfl
  rw [eqBits_encode] at h_ea h_eb
  simp only [encode_bool] at h_ea h_eb
  have run : Eval [decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD] (prepProg univ) r _ :=
    Eval.elim_cons (i := 0) (n := .nil) (a := sP) (b := (Data.cons dP (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))))))) (by simp [decInput]) (Eval.elim_cons (i := 1) (n := .nil) (a := dP) (b := (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode lam)) (b := (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode tau)) (b := (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode beta)) (b := (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode n)) (b := (Data.cons xD (Data.cons yD (Data.cons aD bD)))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := xD) (b := (Data.cons yD (Data.cons aD bD))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := yD) (b := (Data.cons aD bD)) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := aD) (b := bD) (by simp) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 16) (v := sP) (by simp)) (Eval.cons (Eval.var_of_get (i := 6) (v := (encode n)) (by simp)) (Eval.const _ _))) (Eval.let_ (callVar_eval hU (i := 0) (v := (Data.cons sP (Data.cons (encode n) (encode CL.Sampler.Query.dimension)))) (by simp) hdim) (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 0) (v := (encode s)) (by simp) h_us) (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 13) (v := (encode tau)) (by simp) h_ut) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat tau)) (by simp)) (Eval.cons (Eval.var_of_get (i := 16) (v := (encode lam)) (by simp)) (Eval.cons (Eval.var_of_get (i := 10) (v := (encode n)) (by simp)) (Eval.nil _)))) (Eval.let_ (callVar_eval powLoop_wellScoped (i := 0) (v := (Data.cons (ofNat tau) (Data.cons (encode lam) (Data.cons (encode n) Data.nil)))) (by simp) h_mt) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (tau * (Nat.size lam + Nat.size n)))) (by simp)) (Eval.var_of_get (i := 3) (v := (ofNat s)) (by simp))) (Eval.let_ (callVar_eval dblLoop_wellScoped (i := 0) (v := (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat s))) (by simp) h_uks) (Eval.let_ (Eval.const _ _) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := (ofNat (tau * (Nat.size lam + Nat.size n)))) (by simp)) (Eval.var_of_get (i := 0) (v := (ofNat 1)) (by simp))) (Eval.let_ (callVar_eval dblLoop_wellScoped (i := 0) (v := (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat 1))) (by simp) h_uk) (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 19) (v := (encode beta)) (by simp) h_ub) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat beta)) (by simp)) (Eval.cons (Eval.var_of_get (i := 24) (v := (encode lam)) (by simp)) (Eval.cons (Eval.var_of_get (i := 18) (v := (encode n)) (by simp)) (Eval.nil _)))) (Eval.let_ (callVar_eval powLoop_wellScoped (i := 0) (v := (Data.cons (ofNat beta) (Data.cons (encode lam) (Data.cons (encode n) Data.nil)))) (by simp) h_mb) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (beta * (Nat.size lam + Nat.size n)))) (by simp)) (Eval.var_of_get (i := 5) (v := (ofNat 1)) (by simp))) (Eval.let_ (callVar_eval dblLoop_wellScoped (i := 0) (v := (Data.cons (ofNat (beta * (Nat.size lam + Nat.size n))) (ofNat 1))) (by simp) h_uB) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 20) (v := xD) (by simp) h_x) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 19) (v := yD) (by simp) h_y) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 18) (v := aD) (by simp) h_a) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 20) (v := bD) (by simp) h_b) (Eval.let_ (callVar_eval lenProg_wellScoped (i := 3) (v := (encode (bitsOf (toList xD)))) (by simp) h_lx) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (bitsOf (toList xD)).length)) (by simp)) (Eval.var_of_get (i := 13) (v := (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))) (by simp) h_ex) (Eval.let_ (callVar_eval lenProg_wellScoped (i := 5) (v := (encode (bitsOf (toList yD)))) (by simp) h_ly) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (bitsOf (toList yD)).length)) (by simp)) (Eval.var_of_get (i := 16) (v := (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))) (by simp) h_ey) (Eval.let_ (callVar_eval parseProg_wellScoped (i := 7) (v := (encode (bitsOf (toList aD)))) (by simp) h_pa) (Eval.let_ (callVar_eval serProg_wellScoped (i := 0) (v := (parse (bitsOf (toList aD)))) (by simp) h_sa) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (encode (parse (bitsOf (toList aD))).toBitsPost)) (by simp)) (Eval.var_of_get (i := 9) (v := (encode (bitsOf (toList aD)))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD))))) (by simp) h_ea) (Eval.let_ (callVar_eval parseProg_wellScoped (i := 10) (v := (encode (bitsOf (toList bD)))) (by simp) h_pb) (Eval.let_ (callVar_eval serProg_wellScoped (i := 0) (v := (parse (bitsOf (toList bD)))) (by simp) h_sb) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (encode (parse (bitsOf (toList bD))).toBitsPost)) (by simp)) (Eval.var_of_get (i := 12) (v := (encode (bitsOf (toList bD)))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD))))) (by simp) h_eb) (hc)))))))))))))))))))))))))))))))))))))))))))
  refine ⟨_, ?_, run⟩
  have s_us := h_us.size_le
  have s_ut := h_ut.size_le
  have s_ub := h_ub.size_le
  have s_mt := h_mt.size_le
  have s_mb := h_mb.size_le
  have s_uks := h_uks.size_le
  have s_uk := h_uk.size_le
  have s_uB := h_uB.size_le
  have s_x := h_x.size_le
  have s_y := h_y.size_le
  have s_a := h_a.size_le
  have s_b := h_b.size_le
  have s_lx := h_lx.size_le
  have s_ly := h_ly.size_le
  have s_ex := h_ex.size_le
  have s_ey := h_ey.size_le
  have s_pa := h_pa.size_le
  have s_sa := h_sa.size_le
  have s_ea := h_ea.size_le
  have s_pb := h_pb.size_le
  have s_sb := h_sb.size_le
  have s_eb := h_eb.size_le
  have s_sD := hdim.size_le
  have s_one : (ofNat 1).size = 3 := rfl
  have ht_us' : t_us ≤ toUnaryCost s := ht_us
  have ht_ut' : t_ut ≤ toUnaryCost tau := ht_ut
  have ht_ub' : t_ub ≤ toUnaryCost beta := ht_ub
  have ht_x' : t_x ≤ bitsCost (toList xD).length xD.size := ht_x
  have ht_y' : t_y ≤ bitsCost (toList yD).length yD.size := ht_y
  have ht_a' : t_a ≤ bitsCost (toList aD).length aD.size := ht_a
  have ht_b' : t_b ≤ bitsCost (toList bD).length bD.size := ht_b
  have ht_lx' : t_lx ≤ lenCost _ _ := ht_lx
  have ht_ly' : t_ly ≤ lenCost _ _ := ht_ly
  have ht_ex' : t_ex ≤ eqCost _ _ := ht_ex
  have ht_ey' : t_ey ≤ eqCost _ _ := ht_ey
  have ht_pa' : t_pa ≤ parseCost _ := ht_pa
  have ht_sa' : t_sa ≤ serCost _ := ht_sa
  have ht_ea' : t_ea ≤ eqCost _ _ := ht_ea
  have ht_pb' : t_pb ≤ parseCost _ := ht_pb
  have ht_sb' : t_sb ≤ serCost _ := ht_sb
  have ht_eb' : t_eb ≤ eqCost _ _ := ht_eb
  clear ht_us ht_ut ht_ub ht_x ht_y ht_a ht_b ht_lx ht_ly ht_ex ht_ey ht_pa ht_sa ht_ea ht_pb ht_sb ht_eb
  unfold prepPreCost
  simp only [size_cons, size_encode_dimension, size_nil]
  omega


/-! ## The full preparation, the main program and the core -/

/-- The four verdicts of the checks: `|x| = |y| = k s`, and `a`, `b` canonical. -/
def prepOk (lam tau n s : ℕ) (x y a b : BitStr) : Bool :=
  decide (x.length = 2 ^ (tau * (Nat.size lam + Nat.size n)) * s) &&
    decide (y.length = 2 ^ (tau * (Nat.size lam + Nat.size n)) * s) &&
    ((parse a).toBitsPost == a) && ((parse b).toBitsPost == b)

/-- The state of the coordinate loop assembled by `prepProg`. -/
def prepState (dP : Data) (lam tau beta n s : ℕ) (x y a b : BitStr) : Data :=
  .cons (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))) (.cons (encode x) (.cons (encode y)
    (.cons (parse a) (.cons (parse b)
      (decCtx dP (encode n) s (2 ^ (beta * (Nat.size lam + Nat.size n))))))))

theorem prepState_eq (dP : Data) (lam tau beta n s : ℕ) (x y a b : BitStr) :
    prepState dP lam tau beta n s x y a b =
      decState (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))) (x.map ofBool) (y.map ofBool)
        (toList (parse a)) (toList (parse b))
        (decCtx dP (encode n) s (2 ^ (beta * (Nat.size lam + Nat.size n)))) := by
  simp [prepState, decState, encode_bitStr_eq_list, list_toList]

/-- The result of `prepProg`: the state when the checks pass, `nil` otherwise. -/
def prepResult (dP : Data) (lam tau beta n s : ℕ) (x y a b : BitStr) : Data :=
  if prepOk lam tau n s x y a b then prepState dP lam tau beta n s x y a b else .nil

/-- The cost of `prepProg`. -/
def prepCost (sP dP : Data) (lam tau beta n s : ℕ) (xD yD aD bD : Data) (td : ℕ) : ℕ :=
  prepPreCost sP dP lam tau beta n s xD yD aD bD td +
    8 * (dP.size + (encode n : Data).size + 2 * s + 2 * 2 ^ (beta * (Nat.size lam + Nat.size n)) +
      2 * 2 ^ (tau * (Nat.size lam + Nat.size n)) + (encode (bitsOf (toList xD)) : Data).size +
      (encode (bitsOf (toList yD)) : Data).size + (parse (bitsOf (toList aD))).size +
      (parse (bitsOf (toList bD))).size) + 100

/-- **`prepProg` computes `prepResult`**, on every input of the right shape. -/
theorem prepProg_runs {univ : Prog} (hU : univ.WellScoped 1) (sP dP : Data)
    (lam tau beta n s : ℕ) (xD yD aD bD : Data) {td : ℕ}
    (hdim : Eval [Data.cons sP (.cons (encode n) (encode CL.Sampler.Query.dimension))] univ
      (encode s) td) :
    ∃ t ≤ prepCost sP dP lam tau beta n s xD yD aD bD td,
      Eval [decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD]
        (prepProg univ)
        (prepResult dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD))
          (bitsOf (toList aD)) (bitsOf (toList bD))) t := by
  set E := prepEnv univ sP dP lam tau beta n s xD yD aD bD with hE
  obtain ⟨t_ok, ht_ok, h_ok⟩ := andExpr_runs (env := E) (i₁ := 11) (i₂ := 8) (i₃ := 4) (i₄ := 0)
    (c₁ := decide ((bitsOf (toList xD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))) (c₂ := decide ((bitsOf (toList yD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))
    (c₃ := (parse (bitsOf (toList aD))).toBitsPost == (bitsOf (toList aD))) (c₄ := (parse (bitsOf (toList bD))).toBitsPost == (bitsOf (toList bD)))
    (by simp [hE, prepEnv]) (by simp [hE, prepEnv]) (by simp [hE, prepEnv]) (by simp [hE, prepEnv])
  set okv := decide ((bitsOf (toList xD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) && decide ((bitsOf (toList yD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) &&
    ((parse (bitsOf (toList aD))).toBitsPost == (bitsOf (toList aD))) && ((parse (bitsOf (toList bD))).toBitsPost == (bitsOf (toList bD))) with hokv
  have hokv' : prepOk lam tau n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) = okv := rfl
  set ctxv : Data := .cons dP (.cons (encode n) (.cons (ofNat s) (ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))))) with hctxv
  have hctx_build : Eval (ofBool okv :: E)
      (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19)))) ctxv
      (dP.size + 1 + ((encode n : Data).size + 1 + ((ofNat s).size + 1 + ((ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))).size + 1) + 1) + 1) + 1) :=
    Eval.cons (Eval.var_of_get (i := 49) (v := dP) (by simp [hE, prepEnv]))
      (Eval.cons (Eval.var_of_get (i := 41) (v := encode n) (by simp [hE, prepEnv]))
        (Eval.cons (Eval.var_of_get (i := 32) (v := ofNat s) (by simp [hE, prepEnv]))
          (Eval.var_of_get (i := 19) (v := ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))) (by simp [hE, prepEnv]))))
  have hsx : (encode (bitsOf (toList xD)) : Data).size ≤ 4 * (bitsOf (toList xD)).length + 1 := esize_bitStr_le (bitsOf (toList xD))
  have hsy : (encode (bitsOf (toList yD)) : Data).size ≤ 4 * (bitsOf (toList yD)).length + 1 := esize_bitStr_le (bitsOf (toList yD))
  by_cases hok : okv = true
  · have hc : Eval E (.let_ (andExpr 11 8 4 0)
        (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19))))
          (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11)
            (.cons (.var 7) (.var 2)))))))))
        (prepState dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD))) _ :=
      Eval.let_ h_ok
        (Eval.let_ hctx_build
          (Eval.elim_cons (i := 1) (n := .nil) (a := .nil) (b := .nil) (by simp [hok, ofBool])
            (Eval.cons (Eval.var_of_get (i := 27) (v := ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))) (by simp [hE, prepEnv]))
              (Eval.cons (Eval.var_of_get (i := 21) (v := encode (bitsOf (toList xD))) (by simp [hE, prepEnv]))
                (Eval.cons (Eval.var_of_get (i := 20) (v := encode (bitsOf (toList yD))) (by simp [hE, prepEnv]))
                  (Eval.cons (Eval.var_of_get (i := 11) (v := parse (bitsOf (toList aD))) (by simp [hE, prepEnv]))
                    (Eval.cons (Eval.var_of_get (i := 7) (v := parse (bitsOf (toList bD))) (by simp [hE, prepEnv]))
                      (Eval.var_of_get (i := 2) (v := ctxv) (by simp [hctxv])))))))))
    obtain ⟨t', ht', run⟩ := prepProg_prefix hU sP dP lam tau beta n s xD yD aD bD hdim hc
    rw [show prepResult dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) = prepState dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) by
      simp [prepResult, hokv', hok]]
    refine ⟨t', ?_, run⟩
    have hpa := size_parse_le (bitsOf (toList aD))
    have hpb := size_parse_le (bitsOf (toList bD))
    unfold prepCost
    simp only [size_ofNat, hctxv, size_cons] at ht' ⊢
    omega
  · have hc : Eval E (.let_ (andExpr 11 8 4 0)
        (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19))))
          (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11)
            (.cons (.var 7) (.var 2)))))))))
        .nil _ :=
      Eval.let_ h_ok
        (Eval.let_ hctx_build
          (Eval.elim_nil (i := 1) (by simp [Bool.eq_false_iff.mpr hok, ofBool]) (Eval.nil _)))
    obtain ⟨t', ht', run⟩ := prepProg_prefix hU sP dP lam tau beta n s xD yD aD bD hdim hc
    rw [show prepResult dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) = .nil by
      simp [prepResult, hokv', hok]]
    refine ⟨t', ?_, run⟩
    unfold prepCost
    simp only [size_ofNat] at ht' ⊢
    omega

theorem prepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (prepProg univ).WellScoped 1 := by
  simp only [prepProg, WellScoped, callVar, andExpr]
  repeat' first
    | exact hU.mono (by omega) _
    | exact toUnaryProg_wellScoped.mono (by omega) _
    | exact powLoop_wellScoped.mono (by omega) _
    | exact dblLoop_wellScoped.mono (by omega) _
    | exact bitsProg_wellScoped.mono (by omega) _
    | exact lenProg_wellScoped.mono (by omega) _
    | exact eqBitsProg_wellScoped.mono (by omega) _
    | exact parseProg_wellScoped.mono (by omega) _
    | exact serProg_wellScoped.mono (by omega) _
    | constructor
    | trivial
    | omega

/-- The main program: the preparation, then the coordinate loop on its state. -/
def decMain (univ : Prog) : Prog :=
  .let_ (prepProg univ) (.elim 0 .nil (callVar 2 (.loop (coordBody univ))))

theorem coordLoop_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (Prog.loop (coordBody univ)).WellScoped 1 := ⟨Nat.zero_lt_one, coordBody_wellScoped hU⟩

theorem decMain_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (decMain univ).WellScoped 1 :=
  ⟨prepProg_wellScoped hU, by omega, trivial,
    callVar_wellScoped (by omega) (coordLoop_wellScoped hU)⟩

theorem decMain_runs_nil {univ : Prog} (inp : Data) {t₀ : ℕ} (hp : Eval [inp] (prepProg univ) .nil t₀) :
    Eval [inp] (decMain univ) .nil (t₀ + 3) :=
  (Eval.let_ hp (Eval.elim_nil (i := 0) (by simp) (Eval.nil _))).cast_cost (by omega)

theorem decMain_runs_state {univ : Prog} (hU : univ.WellScoped 1) (inp st₀ st₁ : Data) {t₀ t₁ : ℕ}
    (hp : Eval [inp] (prepProg univ) (.cons st₀ st₁) t₀) {r : Data}
    (hl : Eval [Data.cons st₀ st₁] (.loop (coordBody univ)) r t₁) :
    Eval [inp] (decMain univ) r (t₀ + t₁ + (Data.cons st₀ st₁).size + 4) :=
  (Eval.let_ hp (Eval.elim_cons (i := 0) (a := st₀) (b := st₁) (by simp)
    (callVar_eval (coordLoop_wellScoped hU) (i := 2) (v := .cons st₀ st₁) (by simp) hl))).cast_cost
    (by omega)

/-- **Inversion of the main program.** -/
theorem decMain_inv {univ : Prog} (hU : univ.WellScoped 1) (inp : Data) {out : Data} {t : ℕ}
    (h : Eval [inp] (decMain univ) out t) :
    ∃ p t₀, Eval [inp] (prepProg univ) p t₀ ∧
      ((p = .nil ∧ out = .nil) ∨
        ∃ st₀ st₁, p = .cons st₀ st₁ ∧ ∃ t₁, Eval [Data.cons st₀ st₁] (.loop (coordBody univ)) out t₁) := by
  change Eval [inp] (.let_ (prepProg univ) _) out t at h
  cases h with
  | let_ hA hB =>
    refine ⟨_, _, hA, ?_⟩
    cases hB with
    | elim_nil hn hc =>
      simp only [Env.get_cons_zero] at hn
      subst hn
      cases hc
      exact Or.inl ⟨rfl, rfl⟩
    | @elim_cons _ _ _ _ st₀ st₁ _ _ hc hd =>
      simp only [Env.get_cons_zero] at hc
      subst hc
      obtain ⟨t₁, -, h₁⟩ := callVar_runs_rev (coordLoop_wellScoped hU) hd
      simp only [Env.get_cons_succ, Env.get_cons_zero] at h₁
      exact Or.inr ⟨st₀, st₁, rfl, t₁, h₁⟩

/-- The hardcoded datum `((S̄, D̄), λ, τ, β)`. -/
def decParams (sP dP lamD tauD betaD : Data) : Data :=
  .cons (.cons sP dP) (.cons lamD (.cons tauD betaD))

/-- The core of the repeated decider, before the s-m-n construction: on
`(((S̄, D̄), λ, τ, β), (n, x, y, a, b))`, the main program on `(S̄, D̄, λ, τ, β, n, x, y, a, b)`. -/
def repDecCore (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil (.elim 3 .nil (.elim 1 .nil (.elim 9 .nil (.elim 1 .nil
    (.elim 1 .nil (.elim 1 .nil
      (.let_ (.cons (.var 12) (.cons (.var 13) (.cons (.var 10) (.cons (.var 8) (.cons (.var 9)
          (.cons (.var 6) (.cons (.var 4) (.cons (.var 2) (.cons (.var 0) (.var 1))))))))))
        (callVar 0 (decMain univ)))))))))))

theorem repDecCore_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (repDecCore univ).WellScoped 1 := by
  simp only [repDecCore, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial,
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
    by omega, (decMain_wellScoped hU).mono (by omega) _⟩

/-- The environment of the core after its input is taken apart. -/
def coreDecEnv (sP dP lamD tauD betaD nD xD yD aD bD : Data) : Env :=
  [aD, bD, yD, .cons aD bD, xD, .cons yD (.cons aD bD), nD, .cons xD (.cons yD (.cons aD bD)), tauD,
    betaD, lamD, .cons tauD betaD, sP, dP, .cons sP dP, .cons lamD (.cons tauD betaD),
    decParams sP dP lamD tauD betaD, .cons nD (.cons xD (.cons yD (.cons aD bD))),
    .cons (decParams sP dP lamD tauD betaD) (.cons nD (.cons xD (.cons yD (.cons aD bD))))]

theorem repDecCore_runs {univ : Prog} (hU : univ.WellScoped 1) (sP dP lamD tauD betaD nD xD yD aD bD : Data)
    {r : Data} {t : ℕ}
    (h : Eval [decInput sP dP lamD tauD betaD nD xD yD aD bD] (decMain univ) r t) :
    Eval [Data.cons (decParams sP dP lamD tauD betaD) (.cons nD (.cons xD (.cons yD (.cons aD bD))))]
      (repDecCore univ) r
      (t + 2 * (sP.size + dP.size + lamD.size + tauD.size + betaD.size + nD.size + xD.size +
        yD.size + aD.size + bD.size) + 40) := by
  have run : Eval [Data.cons (decParams sP dP lamD tauD betaD)
      (.cons nD (.cons xD (.cons yD (.cons aD bD))))] (repDecCore univ) r _ :=
    Eval.elim_cons (i := 0) (n := .nil) (a := decParams sP dP lamD tauD betaD)
      (b := .cons nD (.cons xD (.cons yD (.cons aD bD)))) (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := .cons sP dP) (b := .cons lamD (.cons tauD betaD))
        (by simp [decParams])
        (Eval.elim_cons (i := 0) (n := .nil) (a := sP) (b := dP) (by simp)
          (Eval.elim_cons (i := 3) (n := .nil) (a := lamD) (b := .cons tauD betaD) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := tauD) (b := betaD) (by simp)
              (Eval.elim_cons (i := 9) (n := .nil) (a := nD) (b := .cons xD (.cons yD (.cons aD bD)))
                (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := xD) (b := .cons yD (.cons aD bD)) (by simp)
                  (Eval.elim_cons (i := 1) (n := .nil) (a := yD) (b := .cons aD bD) (by simp)
                    (Eval.elim_cons (i := 1) (n := .nil) (a := aD) (b := bD) (by simp)
                      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 12) (v := sP) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 13) (v := dP) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 10) (v := lamD) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 8) (v := tauD) (by simp))
                                (Eval.cons (Eval.var_of_get (i := 9) (v := betaD) (by simp))
                                  (Eval.cons (Eval.var_of_get (i := 6) (v := nD) (by simp))
                                    (Eval.cons (Eval.var_of_get (i := 4) (v := xD) (by simp))
                                      (Eval.cons (Eval.var_of_get (i := 2) (v := yD) (by simp))
                                        (Eval.cons (Eval.var_of_get (i := 0) (v := aD) (by simp))
                                          (Eval.var_of_get (i := 1) (v := bD) (by simp)))))))))))
                        (callVar_eval (decMain_wellScoped hU) (i := 0)
                          (v := decInput sP dP lamD tauD betaD nD xD yD aD bD) (by simp [decInput]) h))))))))))
  refine run.cast_cost ?_
  simp only [decInput, size_cons]
  omega

/-- **Inversion of the core** on an input of the right shape. -/
theorem repDecCore_inv {univ : Prog} (hU : univ.WellScoped 1) (sP dP lamD tauD betaD nD xD yD aD bD : Data)
    {r : Data} {t : ℕ}
    (h : Eval [Data.cons (decParams sP dP lamD tauD betaD) (.cons nD (.cons xD (.cons yD (.cons aD bD))))]
      (repDecCore univ) r t) :
    ∃ t', Eval [decInput sP dP lamD tauD betaD nD xD yD aD bD] (decMain univ) r t' := by
  change Eval _ (.elim 0 .nil _) r t at h
  cases h with
  | elim_nil hn _ => simp at hn
  | elim_cons hc h1 =>
    simp only [Env.get_cons_zero, Data.cons.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    cases h1 with
    | elim_nil hn _ => simp [decParams] at hn
    | elim_cons hc h2 =>
      simp only [Env.get_cons_zero, decParams, Data.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h2 with
      | elim_nil hn _ => simp at hn
      | elim_cons hc h3 =>
        simp only [Env.get_cons_zero, Data.cons.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        cases h3 with
        | elim_nil hn _ => simp at hn
        | elim_cons hc h4 =>
          simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h4 with
          | elim_nil hn _ => simp at hn
          | elim_cons hc h5 =>
            simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            cases h5 with
            | elim_nil hn _ => simp at hn
            | elim_cons hc h6 =>
              simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
              obtain ⟨rfl, rfl⟩ := hc
              cases h6 with
              | elim_nil hn _ => simp at hn
              | elim_cons hc h7 =>
                simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
                obtain ⟨rfl, rfl⟩ := hc
                cases h7 with
                | elim_nil hn _ => simp at hn
                | elim_cons hc h8 =>
                  simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
                  obtain ⟨rfl, rfl⟩ := hc
                  cases h8 with
                  | elim_nil hn _ => simp at hn
                  | elim_cons hc h9 =>
                    simp only [Env.get_cons_succ, Env.get_cons_zero, Data.cons.injEq] at hc
                    obtain ⟨rfl, rfl⟩ := hc
                    cases h9 with
                    | let_ hA hB =>
                      obtain ⟨rfl, -⟩ := hA.deterministic (Eval.cons (Eval.var_of_get (i := 12) (v := sP) (by simp))
                        (Eval.cons (Eval.var_of_get (i := 13) (v := dP) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 10) (v := lamD) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 8) (v := tauD) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 9) (v := betaD) (by simp))
                                (Eval.cons (Eval.var_of_get (i := 6) (v := nD) (by simp))
                                  (Eval.cons (Eval.var_of_get (i := 4) (v := xD) (by simp))
                                    (Eval.cons (Eval.var_of_get (i := 2) (v := yD) (by simp))
                                      (Eval.cons (Eval.var_of_get (i := 0) (v := aD) (by simp))
                                        (Eval.var_of_get (i := 1) (v := bD) (by simp)))))))))))
                      obtain ⟨t', -, h'⟩ := callVar_runs_rev (decMain_wellScoped hU) hB
                      simp only [Env.get_cons_zero] at h'
                      exact ⟨t', h'⟩

/-- The core on a malformed `(n, d)`: `nil`. -/
theorem repDecCore_runs_malformed (univ : Prog) (sP dP lamD tauD betaD nD d : Data)
    (hd : d = .nil ∨ (∃ xD, d = .cons xD .nil) ∨ ∃ xD yD, d = .cons xD (.cons yD .nil)) :
    ∃ t ≤ 10, Eval [Data.cons (decParams sP dP lamD tauD betaD) (.cons nD d)] (repDecCore univ) .nil t := by
  have pre : ∀ {c : Prog} {r : Data} {t : ℕ},
      Eval [nD, d, tauD, betaD, lamD, .cons tauD betaD, sP, dP, .cons sP dP,
        .cons lamD (.cons tauD betaD), decParams sP dP lamD tauD betaD, .cons nD d,
        .cons (decParams sP dP lamD tauD betaD) (.cons nD d)] c r t →
      Eval [Data.cons (decParams sP dP lamD tauD betaD) (.cons nD d)]
        (.elim 0 .nil (.elim 0 .nil (.elim 0 .nil (.elim 3 .nil (.elim 1 .nil (.elim 9 .nil c)))))) r
        (t + 6) := fun hc =>
    Eval.elim_cons (i := 0) (n := .nil) (a := decParams sP dP lamD tauD betaD) (b := .cons nD d) (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := .cons sP dP) (b := .cons lamD (.cons tauD betaD))
        (by simp [decParams])
        (Eval.elim_cons (i := 0) (n := .nil) (a := sP) (b := dP) (by simp)
          (Eval.elim_cons (i := 3) (n := .nil) (a := lamD) (b := .cons tauD betaD) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := tauD) (b := betaD) (by simp)
              (Eval.elim_cons (i := 9) (n := .nil) (a := nD) (b := d) (by simp) hc)))))
  rcases hd with rfl | ⟨xD, rfl⟩ | ⟨xD, yD, rfl⟩
  · exact ⟨_, by omega, pre (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))⟩
  · exact ⟨_, by omega, pre (Eval.elim_cons (i := 1) (n := .nil) (a := xD) (b := .nil) (by simp)
      (Eval.elim_nil (i := 1) (by simp) (Eval.nil _)))⟩
  · exact ⟨_, by omega, pre (Eval.elim_cons (i := 1) (n := .nil) (a := xD) (b := .cons yD .nil) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := yD) (b := .nil) (by simp)
        (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))))⟩

end Prog

end MIPRE.Cost
