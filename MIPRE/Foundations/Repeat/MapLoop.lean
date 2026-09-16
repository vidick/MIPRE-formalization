/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.Prims
import MIPRE.Foundations.Cost.Closure

/-!
# The block loop of the repeated sampler

The repeated sampler of `thm:parallel-repetition` answers a marginal, linear or factor query
on `𝔽₂^{k s}` by cutting the vectors of the query into `k` blocks of `s` coordinates, asking
the input sampler about each block, and concatenating the answers
(`planning/repetition-verifier.md`, R3(b)). This module is that loop:

* `pairTakeProg` cuts the first `s` elements off two lists at once;
* `mapBody` is the body of the loop, on the state `(s, remU, remY, ctx, acc)`: stop with `acc`
  once `remU` is exhausted, and otherwise cut a block off `remU` and `remY`, build the query
  `(n, kind, w, j, blockU, blockY)` from the context `ctx = (S̄, n, kind, w, j)`, run the input
  sampler `S̄` on it through the universal machine `univ`, and push the answer, reversed, onto
  `acc`;
* `mapLoop_runs` is the loop: its output is the reversed concatenation of the answers on the
  pairs of blocks `Data.chunkPairs`, in time `(|remU| + 1)` times a quadratic in a bound `Z`
  on the sizes in play and the cost `Tu` of one call.

The loop is uniform in the query kind: the blocks of an absent vector are empty, which is the
encoding of the empty bit string, so a marginal or factor query — whose last component is
empty — goes through the same code as a linear one. The answers are a parameter `f` of the
run lemma, known only on the pairs of blocks that occur: on well-formed queries they are the
input sampler's answers, on arbitrary ones whatever it halts with.
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## Cutting a block off two lists -/

/-- On `cons us (cons remU remY)` with `us` the unary numeral `s`: the pair of remainders and
the pair of blocks, `cons remU' (cons remY' (cons blockU blockY))`. -/
def pairTakeProg : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.let_ (.cons (.var 2) (.cons (.var 0) .nil))
        (.let_ (.loop takeBody)
          (.let_ (.cons (.var 4) (.cons (.var 3) .nil))
            (.let_ (.loop takeBody)
              (.elim 2 .nil
                (.elim 2 .nil
                  (.let_ (callVar 3 revProg)
                    (.let_ (callVar 2 revProg)
                      (.cons (.var 4) (.cons (.var 2) (.cons (.var 1) (.var 0)))))))))))))

theorem pairTakeProg_wellScoped : pairTakeProg.WellScoped 1 := by
  simp [pairTakeProg, WellScoped, takeBody, callVar, revProg, revOntoProg, revOntoBody]

/-- The cost of `pairTakeProg` on a numeral `s` and lists of sizes `U`, `Y`. -/
def pairTakeCost (s U Y : ℕ) : ℕ :=
  2 * ((s + 1) * (U + Y + 2 * s + 21)) + 2 * ((U + 2) * (U + Y + 13)) +
    2 * ((Y + 2) * (U + Y + 13)) + 4 * s + 8 * U + 8 * Y + 40

theorem pairTakeProg_runs (s : ℕ) (remU remY : List Data) :
    ∃ t ≤ pairTakeCost s (list remU).size (list remY).size,
      pairTakeProg.Runs (.cons (ofNat s) (.cons (list remU) (list remY)))
        (.cons (list (remU.drop s)) (.cons (list (remY.drop s))
          (.cons (list (remU.take s)) (list (remY.take s))))) t := by
  set inp : Data := .cons (ofNat s) (.cons (list remU) (list remY)) with hinp
  obtain ⟨t₁, ht₁, h₁⟩ := takeLoop_runs s remU [] [list remU, list remY, ofNat s,
    .cons (list remU) (list remY), inp]
  set tu : Data := .cons (list (remU.drop s)) (list ((remU.take s).reverse ++ [])) with htu
  obtain ⟨t₂, ht₂, h₂⟩ := takeLoop_runs s remY [] [tu, takeState s remU [], list remU, list remY,
    ofNat s, .cons (list remU) (list remY), inp]
  set ty : Data := .cons (list (remY.drop s)) (list ((remY.take s).reverse ++ [])) with hty
  obtain ⟨t₃, ht₃, h₃⟩ := revProg_runs ((remU.take s).reverse ++ [])
  obtain ⟨t₄, ht₄, h₄⟩ := revProg_runs ((remY.take s).reverse ++ [])
  have e₃ : ((remU.take s).reverse ++ []).reverse = remU.take s := by simp
  have e₄ : ((remY.take s).reverse ++ []).reverse = remY.take s := by simp
  rw [e₃] at h₃
  rw [e₄] at h₄
  have run : Eval [inp] pairTakeProg (.cons (list (remU.drop s)) (.cons (list (remY.drop s))
      (.cons (list (remU.take s)) (list (remY.take s))))) _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := ofNat s)
      (b := .cons (list remU) (list remY)) (by simp [hinp])
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remU) (b := list remY) (by simp)
        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := ofNat s) (by simp))
            (Eval.cons (Eval.var_of_get (i := 0) (v := list remU) (by simp)) (Eval.nil _)))
          (Eval.let_ h₁
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := ofNat s) (by simp))
                (Eval.cons (Eval.var_of_get (i := 3) (v := list remY) (by simp)) (Eval.nil _)))
              (Eval.let_ h₂
                (Eval.elim_cons (i := 2) (n := .nil) (a := list (remU.drop s))
                  (b := list ((remU.take s).reverse ++ [])) (by simp [htu])
                  (Eval.elim_cons (i := 2) (n := .nil) (a := list (remY.drop s))
                    (b := list ((remY.take s).reverse ++ [])) (by simp [hty])
                    (Eval.let_ (callVar_eval revProg_wellScoped (i := 3)
                        (v := list ((remU.take s).reverse ++ [])) (by simp) h₃)
                      (Eval.let_ (callVar_eval revProg_wellScoped (i := 2)
                          (v := list ((remY.take s).reverse ++ [])) (by simp) h₄)
                        (Eval.cons (Eval.var_of_get (i := 4) (v := list (remU.drop s)) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 2) (v := list (remY.drop s)) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 1) (v := list (remU.take s)) (by simp))
                              (Eval.var_of_get (i := 0) (v := list (remY.take s)) (by simp))))))))))))))
  refine ⟨_, ?_, run⟩
  simp only [size_ofNat, List.append_nil, size_list_reverse, list_nil, size_nil,
    List.length_reverse] at ht₁ ht₂ ht₃ ht₄ ⊢
  have hU : (list (remU.take s)).size ≤ (list remU).size := size_list_take_le s remU
  have hY : (list (remY.take s)).size ≤ (list remY).size := size_list_take_le s remY
  have hU' : (list (remU.drop s)).size ≤ (list remU).size := size_list_drop_le s remU
  have hY' : (list (remY.drop s)).size ≤ (list remY).size := size_list_drop_le s remY
  have hlU : (remU.take s).length + 1 ≤ (list (remU.take s)).size := length_le_size_list' _
  have hlY : (remY.take s).length + 1 ≤ (list (remY.take s)).size := length_le_size_list' _
  have h₃' : ((remU.take s).length + 1 + 1) * ((list (remU.take s)).size + 1 + 12) ≤
      ((list remU).size + 2) * ((list remU).size + 13) := Nat.mul_le_mul (by omega) (by omega)
  have h₄' : ((remY.take s).length + 1 + 1) * ((list (remY.take s)).size + 1 + 12) ≤
      ((list remY).size + 2) * ((list remY).size + 13) := Nat.mul_le_mul (by omega) (by omega)
  have h₁' : (s + 1) * ((list remU).size + 1 + 2 * s + 20) ≤
      (s + 1) * ((list remU).size + (list remY).size + 2 * s + 21) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₂' : (s + 1) * ((list remY).size + 1 + 2 * s + 20) ≤
      (s + 1) * ((list remU).size + (list remY).size + 2 * s + 21) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₃'' : ((list remU).size + 2) * ((list remU).size + 13) ≤
      ((list remU).size + 2) * ((list remU).size + (list remY).size + 13) :=
    Nat.mul_le_mul_left _ (by omega)
  have h₄'' : ((list remY).size + 2) * ((list remY).size + 13) ≤
      ((list remY).size + 2) * ((list remU).size + (list remY).size + 13) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold pairTakeCost
  omega

/-! ## The loop body -/

/-- The context of the loop: the input sampler `S̄` and the fixed part `(n, kind, w, j)` of the
query. -/
def mapCtx (sD nD kD wD jD : Data) : Data := .cons sD (.cons nD (.cons kD (.cons wD jD)))

/-- The input of the universal machine for one block: `(S̄, (n, kind, w, j, blockU, blockY))`. -/
def mapQuery (sD nD kD wD jD cU cY : Data) : Data :=
  .cons sD (.cons nD (.cons kD (.cons wD (.cons jD (.cons cU cY)))))

/-- The state of the loop. -/
def mapState (s : ℕ) (remU remY : List Data) (ctx : Data) (acc : List Data) : Data :=
  .cons (ofNat s) (.cons (list remU) (.cons (list remY) (.cons ctx (list acc))))

/-- The body of the block loop, with `univ` the universal machine. -/
def mapBody (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.elim 1 .nil
        (.elim 1 .nil
          (.elim 4 (.cons .nil (.var 1))
            (.let_ (.cons (.var 8) (.cons (.var 6) (.var 4)))
              (.let_ (callVar 0 pairTakeProg)
                (.elim 0 .nil
                  (.elim 1 .nil
                    (.elim 1 .nil
                      (.elim 10 .nil
                        (.elim 1 .nil
                          (.elim 1 .nil
                            (.elim 1 .nil
                              (.let_ (.cons (.var 6) (.cons (.var 4) (.cons (.var 2)
                                  (.cons (.var 0) (.cons (.var 1) (.cons (.var 8) (.var 9)))))))
                                (.let_ (callVar 0 univ)
                                  (.let_ (.cons (.var 0) (.var 21))
                                    (.let_ (callVar 0 revOntoProg)
                                      (.cons (.cons .nil .nil)
                                        (.cons (.var 28) (.cons (.var 16) (.cons (.var 14)
                                          (.cons (.var 22) (.var 0)))))))))))))))))))))))

theorem mapBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (mapBody univ).WellScoped 1 := by
  simp only [mapBody, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    ⟨trivial, by omega⟩, ⟨⟨by omega, by omega, by omega⟩, ⟨⟨by omega,
      pairTakeProg_wellScoped.mono (by omega) _⟩, by omega, trivial, by omega, trivial, by omega,
      trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial,
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
      ⟨⟨by omega, hU.mono (by omega) _⟩, ⟨by omega, by omega⟩, ⟨⟨by omega,
        revOntoProg_wellScoped.mono (by omega) _⟩, ⟨trivial, trivial⟩, by omega, by omega,
        by omega, by omega, by omega⟩⟩⟩⟩⟩

theorem mapBody_stop (univ : Prog) (s : ℕ) (remY : List Data) (ctx : Data) (acc : List Data) :
    ∃ t ≤ (list acc).size + 8,
      Eval [mapState s [] remY ctx acc] (mapBody univ) (.cons .nil (list acc)) t := by
  have run : Eval [mapState s [] remY ctx acc] (mapBody univ) (.cons .nil (list acc)) _ :=
    Eval.elim_cons (env := [mapState s [] remY ctx acc]) (i := 0) (n := .nil) (a := ofNat s)
      (b := .cons (list []) (.cons (list remY) (.cons ctx (list acc)))) (by simp [mapState])
      (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list remY) (.cons ctx (list acc)))
        (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remY) (b := .cons ctx (list acc)) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := ctx) (b := list acc) (by simp)
            (Eval.elim_nil (i := 4) (by simp)
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := list acc) (by simp)))))))
  exact ⟨_, by omega, run⟩

/-- The cost of one iteration, in the numeral `s`, the sizes `U, Y` of the remainders, `C` of
the context, `A` of the accumulator, and the cost `Tu` of the call. -/
def mapStepCost (s U Y C A Tu : ℕ) : ℕ :=
  pairTakeCost s U Y + (Tu + 1) * (Tu + A + 12) + 6 * s + 6 * U + 6 * Y + 3 * C + 3 * A +
    4 * Tu + 70

/-- One iteration: the block is cut, the call made, its answer pushed reversed onto `acc`. -/
theorem mapBody_step {univ : Prog} (hU : univ.WellScoped 1) (s : ℕ) (h : Data)
    (l remY : List Data) (sD nD kD wD jD : Data) (acc : List Data) {r : Data} {tu : ℕ}
    (hr : Eval [mapQuery sD nD kD wD jD (list ((h :: l).take s)) (list (remY.take s))] univ r tu) :
    ∃ t ≤ mapStepCost s (list (h :: l)).size (list remY).size (mapCtx sD nD kD wD jD).size
        (list acc).size tu,
      Eval [mapState s (h :: l) remY (mapCtx sD nD kD wD jD) acc] (mapBody univ)
        (.cons (.cons .nil .nil)
          (mapState s ((h :: l).drop s) (remY.drop s) (mapCtx sD nD kD wD jD)
            ((toList r).reverse ++ acc))) t := by
  set remU : List Data := h :: l with hremU
  set ctx : Data := mapCtx sD nD kD wD jD with hctx
  set st : Data := mapState s remU remY ctx acc with hst
  set cU : List Data := remU.take s with hcU
  set cY : List Data := remY.take s with hcY
  set remU' : List Data := remU.drop s with hremU'
  set remY' : List Data := remY.drop s with hremY'
  obtain ⟨t₁, ht₁, h₁⟩ := pairTakeProg_runs s remU remY
  set pin : Data := .cons (ofNat s) (.cons (list remU) (list remY)) with hpin
  set pr : Data := .cons (list remU') (.cons (list remY') (.cons (list cU) (list cY))) with hpr
  set q : Data := mapQuery sD nD kD wD jD (list cU) (list cY) with hq
  have hr' : Eval [q] univ r tu := hr
  obtain ⟨t₂, ht₂, h₂⟩ := revOntoProg_runs (toList r) acc [] (r.size + (list acc).size)
    (by rw [list_toList])
  rw [list_toList] at h₂
  set acc' : List Data := (toList r).reverse ++ acc with hacc'
  have run : Eval [st] (mapBody univ) (.cons (.cons .nil .nil) (mapState s remU' remY' ctx acc')) _ :=
    Eval.elim_cons (env := [st]) (i := 0) (n := .nil) (a := ofNat s)
      (b := .cons (list remU) (.cons (list remY) (.cons ctx (list acc)))) (by simp [hst, mapState])
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remU)
        (b := .cons (list remY) (.cons ctx (list acc))) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remY) (b := .cons ctx (list acc)) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := ctx) (b := list acc) (by simp)
            (Eval.elim_cons (i := 4) (n := .cons .nil (.var 1)) (a := h) (b := list l)
              (by simp [hremU])
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 8) (v := ofNat s) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 6) (v := list remU) (by simp [hremU]))
                    (Eval.var_of_get (i := 4) (v := list remY) (by simp))))
                (Eval.let_ (callVar_eval pairTakeProg_wellScoped (i := 0) (v := pin) (by simp [hpin]) h₁)
                  (Eval.elim_cons (i := 0) (n := .nil) (a := list remU')
                    (b := .cons (list remY') (.cons (list cU) (list cY))) (by simp [hpr])
                    (Eval.elim_cons (i := 1) (n := .nil) (a := list remY')
                      (b := .cons (list cU) (list cY)) (by simp)
                      (Eval.elim_cons (i := 1) (n := .nil) (a := list cU) (b := list cY) (by simp)
                        (Eval.elim_cons (i := 10) (n := .nil) (a := sD)
                          (b := .cons nD (.cons kD (.cons wD jD))) (by simp [hctx, mapCtx])
                          (Eval.elim_cons (i := 1) (n := .nil) (a := nD)
                            (b := .cons kD (.cons wD jD)) (by simp)
                            (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := .cons wD jD)
                              (by simp)
                              (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := jD) (by simp)
                                (Eval.let_ (Eval.cons (Eval.var_of_get (i := 6) (v := sD) (by simp))
                                    (Eval.cons (Eval.var_of_get (i := 4) (v := nD) (by simp))
                                      (Eval.cons (Eval.var_of_get (i := 2) (v := kD) (by simp))
                                        (Eval.cons (Eval.var_of_get (i := 0) (v := wD) (by simp))
                                          (Eval.cons (Eval.var_of_get (i := 1) (v := jD) (by simp))
                                            (Eval.cons
                                              (Eval.var_of_get (i := 8) (v := list cU) (by simp))
                                              (Eval.var_of_get (i := 9) (v := list cY) (by simp))))))))
                                  (Eval.let_ (callVar_eval hU (i := 0) (v := q) (by simp [hq, mapQuery]) hr')
                                    (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := r) (by simp))
                                        (Eval.var_of_get (i := 21) (v := list acc) (by simp)))
                                      (Eval.let_ (callVar_eval revOntoProg_wellScoped (i := 0)
                                          (v := .cons r (list acc)) (by simp) h₂)
                                        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                                          (Eval.cons (Eval.var_of_get (i := 28) (v := ofNat s) (by simp))
                                            (Eval.cons
                                              (Eval.var_of_get (i := 16) (v := list remU') (by simp))
                                              (Eval.cons
                                                (Eval.var_of_get (i := 14) (v := list remY') (by simp))
                                                (Eval.cons
                                                  (Eval.var_of_get (i := 22) (v := ctx) (by simp))
                                                  (Eval.var_of_get (i := 0) (v := list acc')
                                                    (by simp [hacc']))))))))))))))))))))))))
  refine ⟨_, ?_, run⟩
  have hrs : r.size ≤ tu := hr.size_le
  have hlr : (toList r).length + 1 ≤ r.size := by
    have := length_le_size_list' (toList r); rwa [list_toList] at this
  have hacc'sz : (list acc').size + 1 = r.size + (list acc).size := by
    rw [hacc', size_list_append, size_list_reverse, list_toList]
  have hU' : (list remU').size ≤ (list remU).size := size_list_drop_le s remU
  have hY' : (list remY').size ≤ (list remY).size := size_list_drop_le s remY
  have hcU : (list cU).size ≤ (list remU).size := size_list_take_le s remU
  have hcY : (list cY).size ≤ (list remY).size := size_list_take_le s remY
  have hq : q.size = sD.size + nD.size + kD.size + wD.size + jD.size + (list cU).size +
      (list cY).size + 6 := by simp [hq, mapQuery]; omega
  have hctx' : ctx.size = sD.size + nD.size + kD.size + wD.size + jD.size + 4 := by
    simp [hctx, mapCtx]; omega
  have hpin' : pin.size = 2 * s + 1 + (list remU).size + (list remY).size + 2 := by
    simp [hpin, size_ofNat]; omega
  have h₂' : ((toList r).length + 1) * (r.size + (list acc).size + 12) ≤
      (tu + 1) * (tu + (list acc).size + 12) := Nat.mul_le_mul (by omega) (by omega)
  have hpr' : pr.size = (list remU').size + (list remY').size + (list cU).size + (list cY).size + 3 := by
    simp [hpr]; omega
  simp only [size_ofNat, size_cons] at ht₁ ht₂ ⊢
  unfold mapStepCost
  omega

/-- The output of the loop from the pairs of blocks: the answers, each reversed, in reverse
order, in front of `acc`. -/
def mapAcc (f : List Data → List Data → Data) (pairs : List (List Data × List Data))
    (acc : List Data) : List Data :=
  (pairs.map fun p => (toList (f p.1 p.2)).reverse).reverse.flatten ++ acc

/-- Reversing the output with `acc = []` gives the concatenation of the answers. -/
theorem mapAcc_reverse (f : List Data → List Data → Data) (pairs : List (List Data × List Data)) :
    (mapAcc f pairs []).reverse = (pairs.map fun p => toList (f p.1 p.2)).flatten := by
  simp only [mapAcc, List.append_nil, List.reverse_flatten, List.map_reverse, List.reverse_reverse,
    List.map_map]
  congr 1
  simp [Function.comp_def]

theorem mapAcc_cons (f : List Data → List Data → Data) (p : List Data × List Data)
    (pairs : List (List Data × List Data)) (acc : List Data) :
    mapAcc f (p :: pairs) acc = mapAcc f pairs ((toList (f p.1 p.2)).reverse ++ acc) := by
  simp [mapAcc]

/-- The per-iteration budget of the loop, in a bound `Z` on the sizes in play. -/
def mapIter (Z : ℕ) : ℕ := 22 * (Z + 30) ^ 2

theorem pairTakeCost_le {s U Y Z : ℕ} (h : s + U + Y ≤ Z) :
    pairTakeCost s U Y ≤ 17 * (Z + 30) ^ 2 := by
  unfold pairTakeCost
  have h1 : (s + 1) * (U + Y + 2 * s + 21) ≤ (Z + 30) * (2 * (Z + 30)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (Z + 30) * (2 * (Z + 30)) = 2 * ((Z + 30) * (Z + 30)) := by ring
  rw [e] at h1
  have h2 : (U + 2) * (U + Y + 13) ≤ (Z + 30) * (Z + 30) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (Y + 2) * (U + Y + 13) ≤ (Z + 30) * (Z + 30) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : 4 * s + 8 * U + 8 * Y + 40 ≤ 9 * ((Z + 30) * (Z + 30)) := by nlinarith
  rw [pow_two]
  omega

theorem mapStepCost_le {s U Y C A Tu Z : ℕ} (h : s + U + Y + C + A + Tu ≤ Z) :
    mapStepCost s U Y C A Tu + 1 ≤ mapIter Z := by
  unfold mapStepCost mapIter
  have h1 := pairTakeCost_le (Z := Z) (s := s) (U := U) (Y := Y) (by omega)
  have h2 : (Tu + 1) * (Tu + A + 12) ≤ (Z + 30) * (Z + 30) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 6 * s + 6 * U + 6 * Y + 3 * C + 3 * A + 4 * Tu + 71 ≤ 4 * ((Z + 30) * (Z + 30)) := by
    nlinarith
  rw [pow_two] at h1 ⊢
  omega

/-- **The block loop.** With `f` the answer of the universal machine on each pair of blocks
that occurs, at cost at most `Tu`, and `Z` a bound on the sizes in play, the loop from
`(s, remU, remY, ctx, acc)` outputs `mapAcc f (chunkPairs s remU remY) acc` in time
`(|remU| + 1) · mapIter Z`. -/
theorem mapLoop_runs {univ : Prog} (hU : univ.WellScoped 1) {s : ℕ} (hs : 0 < s)
    (sD nD kD wD jD : Data) (f : List Data → List Data → Data) (Tu Z : ℕ) :
    ∀ (remU remY acc : List Data) (env : Env),
      (∀ p ∈ chunkPairs s hs remU remY,
        ∃ t ≤ Tu, Eval [mapQuery sD nD kD wD jD (list p.1) (list p.2)] univ (f p.1 p.2) t) →
      s + (list remU).size + (list remY).size + (mapCtx sD nD kD wD jD).size + (list acc).size +
        remU.length * (Tu + 1) + Tu ≤ Z →
      ∃ t ≤ (remU.length + 1) * mapIter Z,
        Eval (mapState s remU remY (mapCtx sD nD kD wD jD) acc :: env) (.loop (mapBody univ))
          (list (mapAcc f (chunkPairs s hs remU remY) acc)) t := by
  intro remU remY
  induction remU, remY using chunkPairs.induct s hs with
  | case1 remY =>
    intro acc env _ hZ
    obtain ⟨t, ht, h⟩ := mapBody_stop univ s remY (mapCtx sD nD kD wD jD) acc
    refine ⟨t + 1, ?_, ?_⟩
    · have : (list acc).size + 9 ≤ mapIter Z := by
        unfold mapIter; nlinarith
      simp only [List.length_nil, zero_add, one_mul]
      omega
    · simpa [chunkPairs_nil, mapAcc] using
        Eval.loop_stop (Eval.append_of_wellScoped h (mapBody_wellScoped hU) env)
  | case2 h l remY ih =>
    intro acc env hf hZ
    rw [chunkPairs_cons] at hf ⊢
    obtain ⟨tu, htu, hr⟩ := hf _ (List.mem_cons_self ..)
    obtain ⟨t₁, ht₁, h₁⟩ := mapBody_step hU s h l remY sD nD kD wD jD acc hr
    have hlen : ((h :: l).drop s).length + 1 ≤ (h :: l).length := by
      simp only [List.length_drop, List.length_cons]; omega
    set r := f ((h :: l).take s) (remY.take s) with hr'
    have hrs : r.size ≤ tu := hr.size_le
    have hacc' : (list ((toList r).reverse ++ acc)).size + 1 = r.size + (list acc).size := by
      rw [size_list_append, size_list_reverse, list_toList]
    have hZ' : s + (list ((h :: l).drop s)).size + (list (remY.drop s)).size +
        (mapCtx sD nD kD wD jD).size + (list ((toList r).reverse ++ acc)).size +
        ((h :: l).drop s).length * (Tu + 1) + Tu ≤ Z := by
      have h1 := size_list_drop_le s (h :: l)
      have h2 := size_list_drop_le s remY
      have h3 : (((h :: l).drop s).length + 1) * (Tu + 1) ≤ (h :: l).length * (Tu + 1) :=
        Nat.mul_le_mul_right _ hlen
      rw [Nat.add_mul, one_mul] at h3
      omega
    obtain ⟨t₂, ht₂, h₂⟩ := ih ((toList r).reverse ++ acc) env
      (fun p hp => hf p (List.mem_cons_of_mem _ hp)) hZ'
    refine ⟨t₁ + t₂ + 1, ?_, ?_⟩
    · have hstep : t₁ + 1 ≤ mapIter Z :=
        le_trans (Nat.add_le_add_right ht₁ 1) (mapStepCost_le (by omega))
      have h3 : (((h :: l).drop s).length + 1) * mapIter Z ≤ (h :: l).length * mapIter Z :=
        Nat.mul_le_mul_right _ hlen
      rw [Nat.add_mul, one_mul] at h3 ht₂
      rw [Nat.add_mul, one_mul]
      omega
    · rw [mapAcc_cons]
      exact Eval.loop_step (Eval.append_of_wellScoped h₁ (mapBody_wellScoped hU) env) h₂

end Prog

end MIPRE.Cost
