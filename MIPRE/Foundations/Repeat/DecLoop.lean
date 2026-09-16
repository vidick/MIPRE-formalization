/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.MapLoop
import MIPRE.Foundations.Halting.Lists
import MIPRE.Foundations.Cost.Kleene

/-!
# The coordinate loop of the repeated decider

The repeated decider of `thm:parallel-repetition` runs the input decider `D̄` on each of the
`k` coordinates of its input (`planning/repetition-verifier.md`, R3(c)). This module is that
loop, on the state `(k, remX, remY, remA, remB, ctx)` — `k` a unary counter, `remX, remY` the
questions still to be cut into blocks of `s`, `remA, remB` the answers still to be checked,
`ctx = (D̄, n, s, B)`:

* `preProg` cuts a block off `remX` and `remY`, checks that the current answers are bit
  strings of length at most `B` (`okBits`), and returns the query `(D̄, (n, x_i, y_i, a_i, b_i))`
  for the universal machine with the next state, or `nil` when a check fails;
* `stepProg` runs the query through `univ` and continues when the answer is `1`;
* `finalProg` accepts, once the counter is exhausted, when no answer is left over;
* `coordBody` is the body of the loop.

Two readings of the loop are proved: a forward one, `decLoop_of_acc` — the loop accepts when
every coordinate passes (`DecAcc`) — and an *inversion*, `decLoop_inv` — the loop accepts
only then, obtained from `stepProg_inv` by determinism of the semantics. The inversion is
what the game equivalence of the repeated verifier needs, since the input decider may not
halt on inputs it does not accept. A third, `decLoop_runs_bounded`, is the forward reading
with costs, against an oracle for the answers of `univ`, for the time bound.
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## Bit strings of bounded length -/

/-- `d` is the encoding of a bit string of length at most `B`: the walk `bitWalk` against the
unary budget `B` ends with the string exhausted. -/
def okBits (B : ℕ) (d : Data) : Bool :=
  match bitWalk d (ofNat B) with
  | .cons .nil _ => true
  | _ => false

theorem isBit_iff (d : Data) : isBit d = true ↔ ∃ b : Bool, d = ofBool b := by
  constructor
  · intro h
    rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
    all_goals simp [isBit] at h
  · rintro ⟨b, rfl⟩
    exact isBit_ofBool b

theorem okBits_encode (B : ℕ) (x : BitStr) : okBits B (encode x) = decide (x.length ≤ B) := by
  unfold okBits
  rw [ofNat_eq_list_replicate, bitWalk_encode, List.length_replicate]
  by_cases h : x.length ≤ B
  · rw [List.drop_of_length_le h]
    simp [h]
  · obtain ⟨c, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by
      rw [List.length_drop]; omega) : x.drop B ≠ [])
    rw [hl]
    simp [h, encode_bitStr_cons, ofBool]

theorem okBits_iff (B : ℕ) (d : Data) :
    okBits B d = true ↔ ∃ x : BitStr, d = encode x ∧ x.length ≤ B := by
  constructor
  · induction d generalizing B with
    | nil => intro _; exact ⟨[], rfl, by simp⟩
    | cons h l _ ih =>
      intro hok
      cases B with
      | zero => simp [okBits, bitWalk, ofNat] at hok
      | succ B =>
        simp only [okBits, ofNat, bitWalk] at hok
        by_cases hb : isBit h = true
        · rw [if_pos hb] at hok
          obtain ⟨b, rfl⟩ := (isBit_iff h).mp hb
          obtain ⟨x, rfl, hx⟩ := ih B (by unfold okBits; exact hok)
          exact ⟨b :: x, rfl, by simp; omega⟩
        · rw [if_neg hb] at hok
          simp at hok
  · rintro ⟨x, rfl, hx⟩
    rw [okBits_encode]
    simpa using hx

/-! ## The state and the programs -/

/-- The context of the loop: the input decider `D̄`, the index `n`, and `s`, `B` in unary. -/
def decCtx (dD nD : Data) (s B : ℕ) : Data := .cons dD (.cons nD (.cons (ofNat s) (ofNat B)))

/-- The query to the universal machine on one coordinate: `(D̄, (n, x_i, y_i, a_i, b_i))`. -/
def decQuery (dD nD xi yi ai bi : Data) : Data :=
  .cons dD (.cons nD (.cons xi (.cons yi (.cons ai bi))))

/-- The state of the loop. -/
def decState (uk : Data) (remX remY remA remB : List Data) (ctx : Data) : Data :=
  .cons uk (.cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))

/-- On the exhausted counter: accept iff no answer is left over. -/
def finalProg : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.elim 1 .nil
        (.elim 0
          (.elim 1 .nil (.elim 0 (.cons .nil (.cons .nil .nil)) (.cons .nil .nil)))
          (.cons .nil .nil))))

theorem finalProg_wellScoped : finalProg.WellScoped 1 := by simp [finalProg, WellScoped]

theorem finalProg_runs (remX remY remA remB : List Data) (ctx : Data) :
    ∃ t ≤ 12, Eval [Data.cons (list remX) (.cons (list remY) (.cons (list remA)
      (.cons (list remB) ctx)))] finalProg
      (.cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) t := by
  rcases remA with _ | ⟨a, remA⟩
  · rcases remB with _ | ⟨b, remB⟩
    · have run : Eval [Data.cons (list remX) (.cons (list remY) (.cons (list [])
          (.cons (list []) ctx)))] finalProg (.cons .nil (.cons .nil .nil)) _ :=
        Eval.elim_cons (i := 0) (n := .nil) (a := list remX)
          (b := .cons (list remY) (.cons (list []) (.cons (list []) ctx))) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
            (b := .cons (list []) (.cons (list []) ctx)) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list []) ctx) (by simp)
              (Eval.elim_nil (i := 0) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := ctx) (by simp)
                  (Eval.elim_nil (i := 0) (by simp)
                    (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.nil _))))))))
      refine ⟨_, ?_, by simpa [ofBool] using run⟩
      norm_num
    · have run : Eval [Data.cons (list remX) (.cons (list remY) (.cons (list [])
          (.cons (list (b :: remB)) ctx)))] finalProg (.cons .nil .nil) _ :=
        Eval.elim_cons (i := 0) (n := .nil) (a := list remX)
          (b := .cons (list remY) (.cons (list []) (.cons (list (b :: remB)) ctx))) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
            (b := .cons (list []) (.cons (list (b :: remB)) ctx)) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list (b :: remB)) ctx)
              (by simp)
              (Eval.elim_nil (i := 0) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := list (b :: remB)) (b := ctx) (by simp)
                  (Eval.elim_cons (i := 0) (n := .cons .nil (.cons .nil .nil)) (a := b)
                    (b := list remB) (by simp)
                    (Eval.cons (Eval.nil _) (Eval.nil _)))))))
      refine ⟨_, ?_, by simpa [ofBool] using run⟩
      norm_num
  · have run : Eval [Data.cons (list remX) (.cons (list remY) (.cons (list (a :: remA))
        (.cons (list remB) ctx)))] finalProg (.cons .nil .nil) _ :=
      Eval.elim_cons (i := 0) (n := .nil) (a := list remX)
        (b := .cons (list remY) (.cons (list (a :: remA)) (.cons (list remB) ctx))) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
          (b := .cons (list (a :: remA)) (.cons (list remB) ctx)) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list (a :: remA)) (b := .cons (list remB) ctx)
            (by simp)
            (Eval.elim_cons (i := 0) (n := _) (a := a) (b := list remA) (by simp)
              (Eval.cons (Eval.nil _) (Eval.nil _)))))
    refine ⟨_, ?_, by simpa [ofBool] using run⟩
    norm_num

/-- Before the call: cut a block off `remX` and `remY`, check the current answers, and return
the query with the next state — or `nil`. -/
def preProg : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil
    (.elim 2 .nil (.elim 2 .nil
      (.elim 5 .nil (.elim 1 .nil (.elim 1 .nil
        (.let_ (.cons (.var 0) (.cons (.var 16) (.var 14)))
          (.let_ (callVar 0 pairTakeProg)
            (.let_ (.cons (.var 10) (.var 3))
              (.let_ (callVar 0 bitWalkProg)
                (.elim 0 .nil
                  (.elim 0
                    (.let_ (.cons (.var 12) (.var 7))
                      (.let_ (callVar 0 bitWalkProg)
                        (.elim 0 .nil
                          (.elim 0
                            (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
                              (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                                  (.cons (.var 1) (.cons (.var 24) (.var 22))))))
                                (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                                  (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
                            .nil))))
                    .nil)))))))))))))))

theorem preProg_wellScoped : preProg.WellScoped 1 := by
  simp only [preProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, ⟨by omega, by omega, by omega⟩, ⟨by omega, pairTakeProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega, trivial,
    by omega, ⟨⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega,
      trivial, by omega, ⟨by omega, trivial, by omega, trivial, by omega, trivial,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩, trivial⟩, trivial⟩

/-- The cost of `preProg` at `s`, `B`, on remainders of sizes `U, Y`, answer lists of sizes
`A, Bs`, a context of size `C` and a counter of size `K`. -/
def preCost (s B U Y A Bs C K : ℕ) : ℕ :=
  pairTakeCost s U Y + (B + 1) * (A + (2 * B + 1) + 21) + (B + 1) * (Bs + (2 * B + 1) + 21) +
    8 * (U + Y + A + Bs + C + K) + 8 * s + 8 * B + 120

theorem preProg_runs_nilA (uk : Data) (remX remY remB : List Data) (ctx : Data) :
    ∃ t ≤ 7, Eval [decState uk remX remY [] remB ctx] preProg .nil t :=
  ⟨7, le_rfl, Eval.elim_cons (i := 0) (n := .nil) (a := uk)
    (b := .cons (list remX) (.cons (list remY) (.cons (list []) (.cons (list remB) ctx))))
    (by simp [decState])
    (Eval.elim_cons (i := 1) (n := .nil) (a := list remX)
      (b := .cons (list remY) (.cons (list []) (.cons (list remB) ctx))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
        (b := .cons (list []) (.cons (list remB) ctx)) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list remB) ctx) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remB) (b := ctx) (by simp)
            (Eval.elim_nil (i := 2) (by simp) (Eval.nil _))))))⟩

theorem preProg_runs_nilB (uk : Data) (remX remY : List Data) (a : Data) (remA : List Data)
    (ctx : Data) :
    ∃ t ≤ 8, Eval [decState uk remX remY (a :: remA) [] ctx] preProg .nil t :=
  ⟨8, le_rfl, Eval.elim_cons (i := 0) (n := .nil) (a := uk)
    (b := .cons (list remX) (.cons (list remY) (.cons (list (a :: remA)) (.cons (list []) ctx))))
    (by simp [decState])
    (Eval.elim_cons (i := 1) (n := .nil) (a := list remX)
      (b := .cons (list remY) (.cons (list (a :: remA)) (.cons (list []) ctx))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
        (b := .cons (list (a :: remA)) (.cons (list []) ctx)) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list (a :: remA)) (b := .cons (list []) ctx)
          (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := ctx) (by simp)
            (Eval.elim_cons (i := 2) (n := .nil) (a := a) (b := list remA) (by simp)
              (Eval.elim_nil (i := 2) (by simp) (Eval.nil _)))))))⟩

/-- The result of `preProg` on a state with answers `ai, bi` at hand. -/
def preResult (dD nD : Data) (s B : ℕ) (uk : Data) (remX remY : List Data) (ai bi : Data)
    (remA remB : List Data) : Data :=
  if okBits B ai && okBits B bi then
    .cons (decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi)
      (decState uk (remX.drop s) (remY.drop s) remA remB (decCtx dD nD s B))
  else .nil

/-- `preProg` on a state with answers at hand. -/
theorem preProg_runs (dD nD : Data) (s B : ℕ) (uk : Data) (remX remY : List Data) (ai bi : Data)
    (remA remB : List Data) :
    ∃ t ≤ preCost s B (list remX).size (list remY).size (list (ai :: remA)).size
        (list (bi :: remB)).size (decCtx dD nD s B).size uk.size,
      Eval [decState uk remX remY (ai :: remA) (bi :: remB) (decCtx dD nD s B)] preProg
        (preResult dD nD s B uk remX remY ai bi remA remB) t := by
  set ctx := decCtx dD nD s B with hctx
  set st := decState uk remX remY (ai :: remA) (bi :: remB) ctx with hst
  set remX' := remX.drop s with hremX'
  set remY' := remY.drop s with hremY'
  set xi := remX.take s with hxi
  set yi := remY.take s with hyi
  obtain ⟨t₁, ht₁, h₁⟩ := pairTakeProg_runs s remX remY
  set pin : Data := .cons (ofNat s) (.cons (list remX) (list remY)) with hpin
  set pr : Data := .cons (list remX') (.cons (list remY') (.cons (list xi) (list yi))) with hpr
  obtain ⟨t₂, ht₂, h₂⟩ := bitWalkProg_runs ai (ofNat B) [] (ai.size + (ofNat B).size) le_rfl
  obtain ⟨t₃, ht₃, h₃⟩ := bitWalkProg_runs bi (ofNat B) [] (bi.size + (ofNat B).size) le_rfl
  have hpin' : pin.size = 2 * s + 1 + (list remX).size + (list remY).size + 2 := by
    simp [hpin, size_ofNat]; omega
  have hpr' : pr.size = (list remX').size + (list remY').size + (list xi).size + (list yi).size + 3 := by
    simp [hpr]; omega
  have hctx' : ctx.size = dD.size + nD.size + 2 * s + 2 * B + 5 := by
    simp [hctx, decCtx, size_ofNat]; omega
  have hU' : (list remX').size ≤ (list remX).size := size_list_drop_le s remX
  have hY' : (list remY').size ≤ (list remY).size := size_list_drop_le s remY
  have hxi' : (list xi).size ≤ (list remX).size := size_list_take_le s remX
  have hyi' : (list yi).size ≤ (list remY).size := size_list_take_le s remY
  simp only [size_ofNat, spine_ofNat] at ht₂ ht₃
  have hA : (B + 1) * (ai.size + (2 * B + 1) + 21) ≤
      (B + 1) * ((list (ai :: remA)).size + (2 * B + 1) + 21) :=
    Nat.mul_le_mul_left _ (by simp only [size_list_cons]; omega)
  have hBs : (B + 1) * (bi.size + (2 * B + 1) + 21) ≤
      (B + 1) * ((list (bi :: remB)).size + (2 * B + 1) + 21) :=
    Nat.mul_le_mul_left _ (by simp only [size_list_cons]; omega)
  have hAsz : ai.size + 1 ≤ (list (ai :: remA)).size := by simp only [size_list_cons]; omega
  have hBsz : bi.size + 1 ≤ (list (bi :: remB)).size := by simp only [size_list_cons]; omega
  -- the common prefix, up to the first check
  set E : Env := [bitWalk ai (ofNat B), .cons ai (ofNat B), pr, pin, ofNat s, ofNat B, nD,
    .cons (ofNat s) (ofNat B), dD, .cons nD (.cons (ofNat s) (ofNat B)), bi, list remB, ai,
    list remA, list (bi :: remB), ctx, list (ai :: remA), .cons (list (bi :: remB)) ctx,
    list remY, .cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx), list remX,
    .cons (list remY) (.cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx)), uk,
    .cons (list remX) (.cons (list remY) (.cons (list (ai :: remA))
      (.cons (list (bi :: remB)) ctx))), st] with hE
  set CONT : Prog := .let_ (.cons (.var 12) (.var 7))
    (.let_ (callVar 0 bitWalkProg)
      (.elim 0 .nil
        (.elim 0
          (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
            (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                (.cons (.var 1) (.cons (.var 24) (.var 22))))))
              (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
          .nil))) with hCONT
  have hpre : ∀ {r : Data} {t : ℕ},
      Eval E (.elim 0 .nil (.elim 0 CONT .nil)) r t →
      ∃ t' ≤ t + t₁ + t₂ + 2 * (ai.size + (2 * s + 1) + (2 * B + 1) + (list remX).size +
          (list remY).size) + 40, Eval [st] preProg r t' := fun hc => by
    have run : Eval [st] preProg _ _ :=
      Eval.elim_cons (env := [st]) (i := 0) (n := .nil) (a := uk)
        (b := .cons (list remX) (.cons (list remY) (.cons (list (ai :: remA))
          (.cons (list (bi :: remB)) ctx))))
        (by simp [hst, decState])
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remX)
          (b := .cons (list remY) (.cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx)))
          (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
            (b := .cons (list (ai :: remA)) (.cons (list (bi :: remB)) ctx)) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := list (ai :: remA))
              (b := .cons (list (bi :: remB)) ctx) (by simp)
              (Eval.elim_cons (i := 1) (n := .nil) (a := list (bi :: remB)) (b := ctx) (by simp)
                (Eval.elim_cons (i := 2) (n := .nil) (a := ai) (b := list remA) (by simp)
                  (Eval.elim_cons (i := 2) (n := .nil) (a := bi) (b := list remB) (by simp)
                    (Eval.elim_cons (i := 5) (n := .nil) (a := dD)
                      (b := .cons nD (.cons (ofNat s) (ofNat B))) (by simp [hctx, decCtx])
                      (Eval.elim_cons (i := 1) (n := .nil) (a := nD)
                        (b := .cons (ofNat s) (ofNat B)) (by simp)
                        (Eval.elim_cons (i := 1) (n := .nil) (a := ofNat s) (b := ofNat B) (by simp)
                          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := ofNat s) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 16) (v := list remX) (by simp))
                                (Eval.var_of_get (i := 14) (v := list remY) (by simp))))
                            (Eval.let_ (callVar_eval pairTakeProg_wellScoped (i := 0) (v := pin)
                                (by simp [hpin]) h₁)
                              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 10) (v := ai) (by simp))
                                  (Eval.var_of_get (i := 3) (v := ofNat B) (by simp)))
                                (Eval.let_ (callVar_eval bitWalkProg_wellScoped (i := 0)
                                    (v := .cons ai (ofNat B)) (by simp) h₂)
                                  hc)))))))))))))
    refine ⟨_, ?_, run⟩
    simp only [size_cons, hpin', size_ofNat]
    omega
  -- the continuation after the first check, when it passes
  have hcont : ∀ (wa1 : Data) {r : Data} {t : ℕ},
      Eval (bitWalk bi (ofNat B) :: .cons bi (ofNat B) :: .nil :: wa1 :: E)
        (.elim 0 .nil (.elim 0
          (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
            (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                (.cons (.var 1) (.cons (.var 24) (.var 22))))))
              (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
          .nil)) r t →
      ∃ t' ≤ t + t₃ + 2 * (bi.size + (2 * B + 1)) + 12,
        Eval (.nil :: wa1 :: E) CONT r t' := fun wa1 {r t} hc => by
    have run : Eval (.nil :: wa1 :: E) CONT _ _ :=
      Eval.let_ (Eval.cons (Eval.var_of_get (i := 12) (v := bi) (by simp [hE]))
          (Eval.var_of_get (i := 7) (v := ofNat B) (by simp [hE])))
        (Eval.let_ (callVar_eval bitWalkProg_wellScoped (i := 0) (v := .cons bi (ofNat B))
          (by simp) h₃) hc)
    refine ⟨_, ?_, run⟩
    simp only [size_cons, size_ofNat]
    omega
  have hok_nil : ∀ {d : Data}, bitWalk d (ofNat B) = .nil → okBits B d = false := fun h => by
    simp [okBits, h]
  have hok_cons : ∀ {d a b c : Data}, bitWalk d (ofNat B) = .cons (.cons a b) c →
      okBits B d = false := fun h => by simp [okBits, h]
  have hok_ok : ∀ {d c : Data}, bitWalk d (ofNat B) = .cons .nil c → okBits B d = true :=
    fun h => by simp [okBits, h]
  rcases hwa : bitWalk ai (ofNat B) with _ | ⟨_ | ⟨wa00, wa01⟩, wa1⟩
  · -- the first check fails
    rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
      simp [preResult, hok_nil hwa]]
    obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_nil (i := 0) (by simp [hE, hwa]) (Eval.nil _))
    refine ⟨t', ?_, run'⟩
    unfold preCost
    omega
  · -- the first check passes; the second
    rcases hwb : bitWalk bi (ofNat B) with _ | ⟨_ | ⟨wb00, wb01⟩, wb1⟩
    · rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
        simp [preResult, hok_nil hwb]]
      obtain ⟨t₄, ht₄, run₄⟩ := hcont wa1 (Eval.elim_nil (i := 0) (by simp [hwb]) (Eval.nil _))
      obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wa1)
        (by simp [hE, hwa]) (Eval.elim_nil (i := 0) (by simp) run₄))
      refine ⟨t', ?_, run'⟩
      unfold preCost
      omega
    · -- both pass: the query and the next state
      rw [show preResult dD nD s B uk remX remY ai bi remA remB =
          .cons (decQuery dD nD (list xi) (list yi) ai bi)
            (decState uk remX' remY' remA remB ctx) by
        simp [preResult, hok_ok hwa, hok_ok hwb, hremX', hremY', hxi, hyi, hctx]]
      have run₅ : Eval (bitWalk bi (ofNat B) :: .cons bi (ofNat B) :: .nil :: wa1 :: E)
          (.elim 0 .nil (.elim 0
            (.elim 8 .nil (.elim 1 .nil (.elim 1 .nil
              (.cons (.cons (.var 20) (.cons (.var 18) (.cons (.var 0)
                  (.cons (.var 1) (.cons (.var 24) (.var 22))))))
                (.cons (.var 34) (.cons (.var 4) (.cons (.var 2)
                  (.cons (.var 25) (.cons (.var 23) (.var 27))))))))))
            .nil))
          (.cons (decQuery dD nD (list xi) (list yi) ai bi)
            (decState uk remX' remY' remA remB ctx)) _ :=
        Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wb1) (by simp [hwb])
          (Eval.elim_nil (i := 0) (by simp)
            (Eval.elim_cons (i := 8) (n := .nil) (a := list remX')
              (b := .cons (list remY') (.cons (list xi) (list yi))) (by simp [hE, hpr])
              (Eval.elim_cons (i := 1) (n := .nil) (a := list remY')
                (b := .cons (list xi) (list yi)) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := list xi) (b := list yi) (by simp)
                  (Eval.cons
                    (Eval.cons (Eval.var_of_get (i := 20) (v := dD) (by simp [hE]))
                      (Eval.cons (Eval.var_of_get (i := 18) (v := nD) (by simp [hE]))
                        (Eval.cons (Eval.var_of_get (i := 0) (v := list xi) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 1) (v := list yi) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 24) (v := ai) (by simp [hE]))
                              (Eval.var_of_get (i := 22) (v := bi) (by simp [hE])))))))
                    (Eval.cons (Eval.var_of_get (i := 34) (v := uk) (by simp [hE]))
                      (Eval.cons (Eval.var_of_get (i := 4) (v := list remX') (by simp))
                        (Eval.cons (Eval.var_of_get (i := 2) (v := list remY') (by simp))
                          (Eval.cons (Eval.var_of_get (i := 25) (v := list remA) (by simp [hE]))
                            (Eval.cons (Eval.var_of_get (i := 23) (v := list remB) (by simp [hE]))
                              (Eval.var_of_get (i := 27) (v := ctx) (by simp [hE]))))))))))))
      obtain ⟨t₄, ht₄, run₄⟩ := hcont wa1 run₅
      obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wa1)
        (by simp [hE, hwa]) (Eval.elim_nil (i := 0) (by simp) run₄))
      refine ⟨t', ?_, run'⟩
      have hA' := size_list_cons ai remA
      have hB' := size_list_cons bi remB
      unfold preCost
      omega
    · rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
        simp [preResult, hok_cons hwb]]
      obtain ⟨t₄, ht₄, run₄⟩ := hcont wa1 (Eval.elim_cons (i := 0) (n := .nil)
        (a := .cons wb00 wb01) (b := wb1) (by simp [hwb])
        (Eval.elim_cons (i := 0) (a := wb00) (b := wb01) (by simp) (Eval.nil _)))
      obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := wa1)
        (by simp [hE, hwa]) (Eval.elim_nil (i := 0) (by simp) run₄))
      refine ⟨t', ?_, run'⟩
      unfold preCost
      omega
  · -- the first check fails on a non-bit
    rw [show preResult dD nD s B uk remX remY ai bi remA remB = .nil by
      simp [preResult, hok_cons hwa]]
    obtain ⟨t', ht', run'⟩ := hpre (Eval.elim_cons (i := 0) (n := .nil) (a := .cons wa00 wa01)
      (b := wa1) (by simp [hE, hwa])
      (Eval.elim_cons (i := 0) (a := wa00) (b := wa01) (by simp) (Eval.nil _)))
    refine ⟨t', ?_, run'⟩
    unfold preCost
    omega

/-! ## The step: the call to the input decider -/

/-- One coordinate: `preProg`, then the query through `univ`, continuing when the answer is
`1` (`cons nil nil`), stopping with `0` otherwise. -/
def stepProg (univ : Prog) : Prog :=
  .let_ (callVar 0 preProg)
    (.elim 0 (.cons .nil .nil)
      (.let_ (callVar 0 univ)
        (.elim 0 (.cons .nil .nil)
          (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.var 4)) (.cons .nil .nil))
            (.cons .nil .nil)))))

theorem stepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (stepProg univ).WellScoped 1 := by
  simp only [stepProg, WellScoped, callVar]
  exact ⟨⟨by omega, preProg_wellScoped.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩,
    ⟨by omega, hU.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩, by omega, ⟨by omega,
      ⟨⟨trivial, trivial⟩, by omega⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩

/-- The result of the step from the answer `r` of `univ`: continue with `st'` on `1`. -/
def stepResult (st' r : Data) : Data :=
  if r = .cons .nil .nil then .cons (.cons .nil .nil) st' else .cons .nil .nil

theorem stepProg_runs_nil (univ : Prog) (inp : Data) {t₀ : ℕ} (hp : Eval [inp] preProg .nil t₀) :
    Eval [inp] (stepProg univ) (.cons .nil .nil) (t₀ + inp.size + 7) := by
  have run : Eval [inp] (stepProg univ) (.cons .nil .nil) _ :=
    Eval.let_ (callVar_eval preProg_wellScoped (i := 0) (v := inp) (by simp) hp)
      (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.nil _)))
  exact run.cast_cost (by omega)

theorem stepProg_runs_call {univ : Prog} (hU : univ.WellScoped 1) (inp q st' : Data) {t₀ : ℕ}
    (hp : Eval [inp] preProg (.cons q st') t₀) {r : Data} {tr : ℕ} (hr : Eval [q] univ r tr) :
    ∃ t ≤ t₀ + tr + inp.size + q.size + st'.size + 20,
      Eval [inp] (stepProg univ) (stepResult st' r) t := by
  have hpre : ∀ {out : Data} {t : ℕ},
      Eval [r, q, st', .cons q st', inp]
        (.elim 0 (.cons .nil .nil)
          (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.var 4)) (.cons .nil .nil))
            (.cons .nil .nil))) out t →
      Eval [inp] (stepProg univ) out (t₀ + inp.size + q.size + tr + t + 7) := by
    intro out t hc
    have run : Eval [inp] (stepProg univ) out _ :=
      Eval.let_ (callVar_eval preProg_wellScoped (i := 0) (v := inp) rfl hp)
        (Eval.elim_cons (i := 0) (n := .cons .nil .nil) (a := q) (b := st') rfl
          (Eval.let_ (callVar_eval hU (i := 0) (v := q) rfl hr) hc))
    exact run.cast_cost (by omega)
  rcases r with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, d⟩⟩
  · refine ⟨_, ?_, hpre (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.nil _)))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .nil) (b := .nil) (by simp)
      (Eval.elim_nil (i := 0) (by simp) (Eval.elim_nil (i := 1) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 4) (v := st') (by simp))))))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .nil) (b := .cons c d) (by simp)
      (Eval.elim_nil (i := 0) (by simp) (Eval.elim_cons (i := 1) (a := c) (b := d) (by simp)
        (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .cons a b) (b := .nil) (by simp)
      (Eval.elim_cons (i := 0) (a := a) (b := b) (by simp)
        (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
    omega
  · refine ⟨_, ?_, hpre (Eval.elim_cons (i := 0) (a := .cons a b) (b := .cons c d) (by simp)
      (Eval.elim_cons (i := 0) (a := a) (b := b) (by simp)
        (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
    omega

/-- **Inversion of the step.** A run of `stepProg` is a run of `preProg`, then, when it returns a
query, a run of `univ` on it deciding the result. -/
theorem stepProg_inv {univ : Prog} (hU : univ.WellScoped 1) (inp : Data) {out : Data} {t : ℕ}
    (h : Eval [inp] (stepProg univ) out t) :
    ∃ p t₀, Eval [inp] preProg p t₀ ∧
      ((p = .nil ∧ out = .cons .nil .nil) ∨
        ∃ q st' r, p = .cons q st' ∧ (∃ tr, Eval [q] univ r tr) ∧ out = stepResult st' r) := by
  change Eval [inp] (.let_ (callVar 0 preProg) _) out t at h
  cases h with
  | let_ hA hB =>
    obtain ⟨t₀, -, hp⟩ := callVar_runs_rev preProg_wellScoped hA
    refine ⟨_, t₀, hp, ?_⟩
    cases hB with
    | elim_nil hn hc =>
      refine Or.inl ⟨by simpa using hn, ?_⟩
      cases hc with
      | cons h1 h2 => cases h1; cases h2; rfl
    | @elim_cons _ _ _ _ q st' _ _ hc hd =>
      refine Or.inr ⟨q, st', ?_⟩
      cases hd with
      | let_ hC hD =>
        obtain ⟨tr, -, hr⟩ := callVar_runs_rev hU hC
        simp only [Env.get_cons_zero] at hr
        refine ⟨_, by simpa using hc, ⟨tr, hr⟩, ?_⟩
        cases hD with
        | elim_nil hn he =>
          simp only [Env.get_cons_zero] at hn
          subst hn
          cases he with
          | cons h1 h2 => cases h1; cases h2; rfl
        | @elim_cons _ _ _ _ r0 r1 _ _ hc2 he =>
          simp only [Env.get_cons_zero] at hc2
          subst hc2
          cases he with
          | elim_nil hn2 hf =>
            simp only [Env.get_cons_zero] at hn2
            subst hn2
            cases hf with
            | elim_nil hn3 hg =>
              simp only [Env.get_cons_succ, Env.get_cons_zero] at hn3
              subst hn3
              cases hg with
              | cons h1 h2 =>
                cases h1 with
                | cons h3 h4 => cases h3; cases h4; cases h2; rfl
            | elim_cons hc3 hg =>
              simp only [Env.get_cons_succ, Env.get_cons_zero] at hc3
              subst hc3
              cases hg with
              | cons h1 h2 => cases h1; cases h2; simp [stepResult]
          | elim_cons hc2' hf =>
            simp only [Env.get_cons_zero] at hc2'
            subst hc2'
            cases hf with
            | cons h1 h2 => cases h1; cases h2; simp [stepResult]

/-! ## The body -/

/-- The body of the coordinate loop: on the exhausted counter, `finalProg`; otherwise the
step on the decremented state. -/
def coordBody (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 0 (callVar 1 finalProg)
      (.let_ (.cons (.var 1) (.var 3)) (callVar 0 (stepProg univ))))

theorem coordBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (coordBody univ).WellScoped 1 := by
  simp only [coordBody, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, ⟨by omega, finalProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, by omega, (stepProg_wellScoped hU).mono (by omega) _⟩

theorem coordBody_stop (univ : Prog) (remX remY remA remB : List Data) (ctx : Data) :
    ∃ t ≤ (list remX).size + (list remY).size + (list remA).size + (list remB).size + ctx.size + 24,
      Eval [decState (ofNat 0) remX remY remA remB ctx] (coordBody univ)
        (.cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) t := by
  obtain ⟨t, ht, h⟩ := finalProg_runs remX remY remA remB ctx
  have run : Eval [decState (ofNat 0) remX remY remA remB ctx] (coordBody univ)
      (.cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) _ :=
    Eval.elim_cons (i := 0) (n := .nil) (a := ofNat 0)
      (b := .cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))
      (by simp [decState])
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (callVar_eval finalProg_wellScoped (i := 1)
          (v := .cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))
          (by simp) h))
  refine ⟨_, ?_, run⟩
  simp only [size_cons]
  omega

theorem coordBody_step {univ : Prog} (hU : univ.WellScoped 1) (k : ℕ)
    (remX remY remA remB : List Data) (ctx : Data)
    {out : Data} {t : ℕ}
    (h : Eval [decState (ofNat k) remX remY remA remB ctx] (stepProg univ) out t) :
    Eval [decState (ofNat (k + 1)) remX remY remA remB ctx] (coordBody univ) out
      (t + 2 * (decState (ofNat k) remX remY remA remB ctx).size + 7) := by
  have run : Eval [decState (ofNat (k + 1)) remX remY remA remB ctx] (coordBody univ) out _ :=
    Eval.elim_cons (i := 0) (n := .nil) (a := ofNat (k + 1))
      (b := .cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))
      (by simp [decState])
      (Eval.elim_cons (i := 0) (a := .nil) (b := ofNat k) (by simp [ofNat])
        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := ofNat k) (by simp))
            (Eval.var_of_get (i := 3)
              (v := .cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))
              (by simp)))
          (callVar_eval (stepProg_wellScoped hU) (i := 0)
            (v := decState (ofNat k) remX remY remA remB ctx) (by simp [decState]) h)))
  exact run.cast_cost (by simp only [decState, size_cons, size_ofNat]; omega)

/-- **Inversion of the body.** On the exhausted counter, the body stops with the verdict of
`finalProg`; otherwise it is a run of the step on the decremented state. -/
theorem coordBody_inv {univ : Prog} (hU : univ.WellScoped 1) (k : ℕ)
    (remX remY remA remB : List Data) (ctx : Data) {out : Data} {t : ℕ}
    (h : Eval [decState (ofNat k) remX remY remA remB ctx] (coordBody univ) out t) :
    (k = 0 ∧ out = .cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) ∨
      ∃ k', k = k' + 1 ∧
        ∃ t', Eval [decState (ofNat k') remX remY remA remB ctx] (stepProg univ) out t' := by
  cases k with
  | zero =>
    obtain ⟨t₀, -, h₀⟩ := coordBody_stop univ remX remY remA remB ctx
    exact Or.inl ⟨rfl, (h.deterministic h₀).1⟩
  | succ k =>
    refine Or.inr ⟨k, rfl, ?_⟩
    change Eval _ (.elim 0 .nil _) out t at h
    cases h with
    | elim_nil hn _ => simp [decState] at hn
    | elim_cons hc h1 =>
      simp only [decState, Env.get_cons_zero, Data.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h1 with
      | elim_nil hn _ => simp [ofNat] at hn
      | elim_cons hc2 h2 =>
        simp only [Env.get_cons_zero, ofNat, Data.cons.injEq] at hc2
        obtain ⟨rfl, rfl⟩ := hc2
        cases h2 with
        | let_ hA hB =>
          obtain ⟨rfl, -⟩ := hA.deterministic (Eval.cons (Eval.var_of_get (i := 1) (v := ofNat k)
            (by simp)) (Eval.var_of_get (i := 3) (v := .cons (list remX) (.cons (list remY)
              (.cons (list remA) (.cons (list remB) ctx)))) (by simp)))
          obtain ⟨t', -, h'⟩ := callVar_runs_rev (stepProg_wellScoped hU) hB
          simp only [Env.get_cons_zero] at h'
          exact ⟨t', h'⟩

/-! ## The loop -/

/-- **Acceptance of the coordinate loop**: `k` answers on each side, each a bit string of
length at most `B`, and the input decider, through `univ`, answering `1` on every
coordinate. -/
def DecAcc (univ : Prog) (dD nD : Data) (s B : ℕ) :
    ℕ → List Data → List Data → List Data → List Data → Prop
  | 0, _, _, remA, remB => remA = [] ∧ remB = []
  | k + 1, remX, remY, ai :: remA', bi :: remB' =>
      okBits B ai = true ∧ okBits B bi = true ∧
      (∃ t, Eval [decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi] univ
        (.cons .nil .nil) t) ∧
      DecAcc univ dD nD s B k (remX.drop s) (remY.drop s) remA' remB'
  | _ + 1, _, _, [], _ => False
  | _ + 1, _, _, _ :: _, [] => False

/-- **The loop accepts on `DecAcc`.** -/
theorem coordLoop_of_acc {univ : Prog} (hU : univ.WellScoped 1) (dD nD : Data) (s B : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data) (env : Env),
      DecAcc univ dD nD s B k remX remY remA remB →
      ∃ t, Eval (decState (ofNat k) remX remY remA remB (decCtx dD nD s B) :: env)
        (.loop (coordBody univ)) (.cons .nil .nil) t
  | 0, remX, remY, remA, remB, env, hacc => by
    obtain ⟨rfl, rfl⟩ := hacc
    obtain ⟨t, -, h⟩ := coordBody_stop univ remX remY [] [] (decCtx dD nD s B)
    simp only [and_self, decide_true, ofBool] at h
    exact ⟨_, Eval.loop_stop (Eval.append_of_wellScoped h (coordBody_wellScoped hU) env)⟩
  | k + 1, remX, remY, [], remB, env, hacc => hacc.elim
  | k + 1, remX, remY, _ :: _, [], env, hacc => hacc.elim
  | k + 1, remX, remY, ai :: remA', bi :: remB', env, hacc => by
    obtain ⟨hoka, hokb, ⟨tr, hr⟩, hrec⟩ := hacc
    obtain ⟨t₀, -, hp⟩ := preProg_runs dD nD s B (ofNat k) remX remY ai bi remA' remB'
    rw [show preResult dD nD s B (ofNat k) remX remY ai bi remA' remB' =
        .cons (decQuery dD nD (list (remX.take s)) (list (remY.take s)) ai bi)
          (decState (ofNat k) (remX.drop s) (remY.drop s) remA' remB' (decCtx dD nD s B)) by
      simp [preResult, hoka, hokb]] at hp
    obtain ⟨t₁, -, h₁⟩ := stepProg_runs_call hU _ _ _ hp hr
    simp only [stepResult, if_true] at h₁
    have h₂ := coordBody_step hU k remX remY (ai :: remA') (bi :: remB') (decCtx dD nD s B) h₁
    obtain ⟨t₃, h₃⟩ := coordLoop_of_acc hU dD nD s B k (remX.drop s) (remY.drop s) remA' remB' env hrec
    exact ⟨_, Eval.loop_step (Eval.append_of_wellScoped h₂ (coordBody_wellScoped hU) env) h₃⟩

/-- **The loop accepts only on `DecAcc`.** -/
theorem coordLoop_inv {univ : Prog} (hU : univ.WellScoped 1) (dD nD : Data) (s B : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data) (env : Env) {t : ℕ},
      Eval (decState (ofNat k) remX remY remA remB (decCtx dD nD s B) :: env)
        (.loop (coordBody univ)) (.cons .nil .nil) t →
      DecAcc univ dD nD s B k remX remY remA remB := by
  intro k
  induction k with
  | zero =>
    intro remX remY remA remB env t h
    cases h with
    | loop_stop hb =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU 0 remX remY remA remB _ hb' with ⟨-, h⟩ | ⟨k', hk, -⟩
      · simp only [Data.cons.injEq, true_and] at h
        show remA = [] ∧ remB = []
        rcases hd : decide (remA = [] ∧ remB = []) with _ | _
        · rw [hd] at h; cases h
        · exact of_decide_eq_true hd
      · omega
    | loop_step hb _ =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU 0 remX remY remA remB _ hb' with ⟨-, h⟩ | ⟨k', hk, -⟩
      · cases h
      · omega
  | succ k ih =>
    intro remX remY remA remB env t h
    cases h with
    | loop_stop hb =>
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU (k + 1) remX remY remA remB _ hb' with ⟨h0, -⟩ | ⟨k', hk, t', hs⟩
      · omega
      · obtain rfl : k = k' := by omega
        obtain ⟨p, t₀, -, hcase⟩ := stepProg_inv hU _ hs
        rcases hcase with ⟨-, h⟩ | ⟨q, st', r, -, -, h⟩
        · cases h
        · simp only [stepResult] at h
          split_ifs at h <;> cases h
    | loop_step hb hrest =>
      rename_i x y v s₁ t₁
      have hb' := Eval.of_append_of_wellScoped (env := [_]) hb (coordBody_wellScoped hU)
      rcases coordBody_inv hU (k + 1) remX remY remA remB _ hb' with ⟨h0, -⟩ | ⟨k', hk, t', hs⟩
      · omega
      · obtain rfl : k = k' := by omega
        obtain ⟨p, t₀, hp, hcase⟩ := stepProg_inv hU _ hs
        rcases hcase with ⟨-, h⟩ | ⟨q, st', r, rfl, ⟨tr, hr⟩, h⟩
        · cases h
        · -- the query and the next state are those of `preProg`
          rcases remA with _ | ⟨ai, remA'⟩
          · obtain ⟨t₂, -, h₂⟩ := preProg_runs_nilA (ofNat k) remX remY remB (decCtx dD nD s B)
            cases (hp.deterministic h₂).1
          rcases remB with _ | ⟨bi, remB'⟩
          · obtain ⟨t₂, -, h₂⟩ := preProg_runs_nilB (ofNat k) remX remY ai remA' (decCtx dD nD s B)
            cases (hp.deterministic h₂).1
          obtain ⟨t₂, -, h₂⟩ := preProg_runs dD nD s B (ofNat k) remX remY ai bi remA' remB'
          have hpq := (hp.deterministic h₂).1
          simp only [preResult] at hpq
          split_ifs at hpq with hok
          · simp only [Data.cons.injEq] at hpq
            obtain ⟨rfl, rfl⟩ := hpq
            simp only [Bool.and_eq_true] at hok
            simp only [stepResult] at h
            split_ifs at h with hr1
            · subst hr1
              simp only [Data.cons.injEq] at h
              obtain ⟨-, rfl⟩ := h
              refine ⟨hok.1, hok.2, ⟨tr, hr⟩, ?_⟩
              exact ih _ _ _ _ env hrest
            · cases h

end Prog

end MIPRE.Cost
