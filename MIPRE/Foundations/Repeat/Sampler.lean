/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.MapLoop
import MIPRE.Foundations.Cost.Toolkit
import MIPRE.Foundations.CL.Sampler

/-!
# The program of the repeated sampler

The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`;
`planning/repetition-verifier.md`, R3(b)) as a program of the ambient model. It is one fixed
program `repSampCore univ` — `univ` a universal machine — run through the s-m-n construction
`hardcode` on the datum `(S̄, λ, τ)`: its input is then `((S̄, λ, τ), (n, q))`, with `S̄` the
input sampler's program, `λ, τ` in binary and `q` a query. It

1. asks `S̄` for its dimension `s = s(n)`, through `univ`;
2. on the dimension query (`kind = 0`, i.e. `nil`) runs `dimProg`: the numeral `2^m s` with
   `m = τ (|λ| + |n|)`, written as `m` zero bits in front of the bits of `s` (`powBody`);
3. on any other query `(kind, w, j, u, y)` runs `lockProg`: `s` in unary, then the block loop
   `mapBody` over `u` and `y` in blocks of `s`, and the concatenation of the answers.

Every input of the form `((S̄, λ, τ), (n, d))` halts: the missing components of a malformed
`d` are `nil`, on which each `elim` stops with `nil`. The costs are explicit throughout, for
the time bound of the repeated verifier (`MIPRE.Foundations.Repeat.SamplerCost`).
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## The dimension branch -/

/-- On `(s, λ, n, τ)` — `s` in binary and nonzero, `λ, n` bit lists, `τ` in binary — the bits
of `2^{τ (|λ| + |n|)} s`; `nil` when `s` is `nil`. -/
def dimProg : Prog :=
  .elim 0 .nil
    (.elim 0 .nil
      (.elim 3 .nil
        (.elim 1 .nil
          (.let_ (callVar 1 toUnaryProg)
            (.let_ (.cons (.var 0) (.cons (.var 3) (.cons (.var 1) (.var 7))))
              (.loop powBody))))))

theorem dimProg_wellScoped : dimProg.WellScoped 1 := by
  simp only [dimProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial,
    ⟨by omega, toUnaryProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega, by omega, by omega⟩, by omega, powBody_wellScoped.mono (by omega) _⟩

theorem dimProg_runs_nil (r : Data) : Eval [Data.cons .nil r] dimProg .nil 3 :=
  Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := r) (by simp)
    (Eval.elim_nil (i := 0) (by simp) (Eval.nil _))

/-- The cost of converting a numeral to unary (`toUnaryProg_runs`). -/
def toUnaryCost (n : ℕ) : ℕ :=
  (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90)

/-- The cost of `dimProg` with exponent `tau`, lists of lengths `L` and sizes `Λ + N`, and a
numeral of size `Ssz`. -/
def dimCost (tau L Λ N Ssz : ℕ) : ℕ :=
  toUnaryCost tau + esize tau + powCost tau L (Λ + N + Ssz) + 2 * tau + Λ + N + Ssz + 20

theorem dimProg_runs (tau : ℕ) (bl bn : List Data) (h : Data) (l : List Data) :
    ∃ t ≤ dimCost tau (bl.length + bn.length) (list bl).size (list bn).size (list (h :: l)).size,
      Eval [Data.cons (list (h :: l)) (.cons (list bl) (.cons (list bn) (encode tau)))] dimProg
        (list (List.replicate (tau * (bl.length + bn.length)) .nil ++ (h :: l))) t := by
  set inp : Data := .cons (list (h :: l)) (.cons (list bl) (.cons (list bn) (encode tau))) with hinp
  set r2 : Data := .cons (list bn) (encode tau) with hr2
  set r : Data := .cons (list bl) r2 with hr
  obtain ⟨t₁, ht₁, h₁⟩ := toUnaryProg_runs tau
  obtain ⟨t₂, ht₂, h₂⟩ := powLoop_runs tau bl bn (h :: l)
    [ofNat tau, list bn, encode tau, list bl, r2, h, list l, list (h :: l), r, inp]
  have run : Eval [inp] dimProg (list (List.replicate (tau * (bl.length + bn.length)) .nil ++ (h :: l))) _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := list (h :: l)) (b := r)
      (by simp [hinp, hr, hr2])
      (Eval.elim_cons (i := 0) (n := .nil) (a := h) (b := list l) (by simp)
        (Eval.elim_cons (i := 3) (n := .nil) (a := list bl) (b := r2) (by simp [hr])
          (Eval.elim_cons (i := 1) (n := .nil) (a := list bn) (b := encode tau) (by simp [hr2])
            (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 1) (v := encode tau) (by simp) h₁)
              (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := ofNat tau) (by simp))
                  (Eval.cons (Eval.var_of_get (i := 3) (v := list bl) (by simp))
                    (Eval.cons (Eval.var_of_get (i := 1) (v := list bn) (by simp))
                      (Eval.var_of_get (i := 7) (v := list (h :: l)) (by simp)))))
                h₂)))))
  refine ⟨_, ?_, run⟩
  unfold dimCost toUnaryCost
  have : (encode tau : Data).size = esize tau := rfl
  simp only [size_ofNat, this]
  omega

/-! ## The block branch -/

/-- On `(S̄, n, s, kind, w, j, u, y)` — `s` in binary — the concatenation of the answers of
`S̄` on the blocks of `u` and `y`, through `univ`; `nil` when `s = 0`. -/
def lockProg (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 1 .nil
      (.elim 1 .nil
        (.elim 1 .nil
          (.elim 1 .nil
            (.elim 1 .nil
              (.elim 1 .nil
                (.let_ (callVar 8 toUnaryProg)
                  (.elim 0 .nil
                    (.let_ (.cons (.var 15) (.cons (.var 13) (.cons (.var 9)
                        (.cons (.var 7) (.var 5)))))
                      (.let_ (.cons (.var 3) (.cons (.var 4) (.cons (.var 5) (.cons (.var 0) .nil))))
                        (.let_ (.loop (mapBody univ))
                          (callVar 0 revProg))))))))))))

theorem lockProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (lockProg univ).WellScoped 1 := by
  simp only [lockProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, ⟨by omega, toUnaryProg_wellScoped.mono (by omega) _⟩,
    by omega, trivial, ⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, trivial⟩, ⟨by omega, (mapBody_wellScoped hU).mono (by omega) _⟩,
    by omega, revProg_wellScoped.mono (by omega) _⟩

/-- The input of `lockProg`. -/
def lockInput (sD nD sz kD wD jD uD yD : Data) : Data :=
  .cons sD (.cons nD (.cons sz (.cons kD (.cons wD (.cons jD (.cons uD yD))))))

theorem lockProg_runs_zero (univ : Prog) (sD nD kD wD jD uD yD : Data) :
    ∃ t ≤ esize (0 : ℕ) + toUnaryCost 0 + sD.size + nD.size + kD.size + wD.size + jD.size +
        uD.size + yD.size + 30,
      Eval [lockInput sD nD (encode 0) kD wD jD uD yD] (lockProg univ) .nil t := by
  obtain ⟨t₁, ht₁, h₁⟩ := toUnaryProg_runs 0
  set inp := lockInput sD nD (encode 0) kD wD jD uD yD with hinp
  have run : Eval [inp] (lockProg univ) .nil _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := sD)
      (b := .cons nD (.cons (encode 0) (.cons kD (.cons wD (.cons jD (.cons uD yD))))))
      (by simp [hinp, lockInput])
      (Eval.elim_cons (i := 1) (n := .nil) (a := nD)
        (b := .cons (encode 0) (.cons kD (.cons wD (.cons jD (.cons uD yD))))) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := encode 0)
          (b := .cons kD (.cons wD (.cons jD (.cons uD yD)))) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := .cons wD (.cons jD (.cons uD yD)))
            (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := .cons jD (.cons uD yD)) (by simp)
              (Eval.elim_cons (i := 1) (n := .nil) (a := jD) (b := .cons uD yD) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := uD) (b := yD) (by simp)
                  (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 8) (v := encode 0) (by simp) h₁)
                    (Eval.elim_nil (i := 0) (by simp [ofNat]) (Eval.nil _)))))))))
  refine ⟨_, ?_, run⟩
  unfold toUnaryCost
  have : (encode 0 : Data).size = esize 0 := rfl
  simp only [this]
  omega

/-- The cost of `lockProg` at dimension `s`, context pieces of total size `C`, vectors of
sizes `U, Y`, and a bound `Z` on the sizes in the loop. -/
def lockCost (s C U Y Z : ℕ) : ℕ :=
  esize s + toUnaryCost s + 4 * C + 4 * s + 4 * U + 4 * Y + (U + 1) * mapIter Z +
    (Z + 2) * (Z + 13) + 3 * Z + 60

theorem length_chunkPairs_le (s : ℕ) (hs : 0 < s) (l y : List Data) :
    (chunkPairs s hs l y).length ≤ l.length := by
  induction l, y using chunkPairs.induct s hs with
  | case1 y => simp [chunkPairs_nil]
  | case2 h l y ih =>
    rw [chunkPairs_cons, List.length_cons]
    have := ih
    simp only [List.length_drop, List.length_cons] at this ⊢
    omega

theorem size_list_flatten_le : ∀ (L : List (List Data)) (B : ℕ),
    (∀ l ∈ L, (list l).size ≤ B + 1) → (list L.flatten).size ≤ L.length * B + 1
  | [], _, _ => by simp
  | l :: L, B, hL => by
    have h1 := hL l (List.mem_cons_self ..)
    have h2 := size_list_flatten_le L B fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')
    have h3 := size_list_append l L.flatten
    rw [List.flatten_cons, List.length_cons, Nat.succ_mul]
    omega

theorem size_list_mapAcc_le (f : List Data → List Data → Data) (pairs : List (List Data × List Data))
    (Tu : ℕ) (hf : ∀ p ∈ pairs, (f p.1 p.2).size ≤ Tu) :
    (list (mapAcc f pairs [])).size ≤ pairs.length * Tu + 1 := by
  unfold mapAcc
  rw [List.append_nil]
  have := size_list_flatten_le ((pairs.map fun p => (toList (f p.1 p.2)).reverse).reverse) Tu
    (fun l hl => by
      rw [List.mem_reverse, List.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      rw [size_list_reverse, list_toList]
      exact (hf p hp).trans (Nat.le_succ _))
  simpa using this

/-- `lockProg` on a nonzero dimension: the block loop, then the reversal. -/
theorem lockProg_runs {univ : Prog} (hU : univ.WellScoped 1) {s : ℕ} (hs : 0 < s)
    (sD nD kD wD jD : Data) (u y : List Data) (f : List Data → List Data → Data) (Tu Z : ℕ)
    (hf : ∀ p ∈ chunkPairs s hs u y,
      ∃ t ≤ Tu, Eval [mapQuery sD nD kD wD jD (list p.1) (list p.2)] univ (f p.1 p.2) t)
    (hZ : s + (list u).size + (list y).size + (mapCtx sD nD kD wD jD).size + 1 +
      u.length * (Tu + 1) + Tu ≤ Z) :
    ∃ t ≤ lockCost s (mapCtx sD nD kD wD jD).size (list u).size (list y).size Z,
      Eval [lockInput sD nD (encode s) kD wD jD (list u) (list y)] (lockProg univ)
        (list ((chunkPairs s hs u y).map fun p => toList (f p.1 p.2)).flatten) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := toUnaryProg_runs s
  set inp := lockInput sD nD (encode s) kD wD jD (list u) (list y) with hinp
  set ctx := mapCtx sD nD kD wD jD with hctx
  set B6 : Data := .cons (list u) (list y) with hB6
  set B5 : Data := .cons jD B6 with hB5
  set B4 : Data := .cons wD B5 with hB4
  set B3 : Data := .cons kD B4 with hB3
  set B2 : Data := .cons (encode s) B3 with hB2
  set B1 : Data := .cons nD B2 with hB1
  obtain ⟨s', hs'⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hus : ofNat s = .cons .nil (ofNat s') := by rw [hs']; rfl
  obtain ⟨t₂, ht₂, h₂⟩ := mapLoop_runs hU hs sD nD kD wD jD f Tu Z u y []
    [ctx, .nil, ofNat s', ofNat s, list u, list y, jD, B6, wD, B5, kD, B4, encode s, B3, nD, B2,
      sD, B1, inp] hf (by simp only [list_nil, size_nil]; omega)
  set res := mapAcc f (chunkPairs s hs u y) [] with hres
  obtain ⟨t₃, ht₃, h₃⟩ := revProg_runs res
  rw [mapAcc_reverse] at h₃
  have run : Eval [inp] (lockProg univ)
      (list ((chunkPairs s hs u y).map fun p => toList (f p.1 p.2)).flatten) _ :=
    Eval.elim_cons (env := [inp]) (i := 0) (n := .nil) (a := sD) (b := B1)
      (by simp [hinp, lockInput, hB1, hB2, hB3, hB4, hB5, hB6])
      (Eval.elim_cons (i := 1) (n := .nil) (a := nD) (b := B2) (by simp [hB1])
        (Eval.elim_cons (i := 1) (n := .nil) (a := encode s) (b := B3) (by simp [hB2])
          (Eval.elim_cons (i := 1) (n := .nil) (a := kD) (b := B4) (by simp [hB3])
            (Eval.elim_cons (i := 1) (n := .nil) (a := wD) (b := B5) (by simp [hB4])
              (Eval.elim_cons (i := 1) (n := .nil) (a := jD) (b := B6) (by simp [hB5])
                (Eval.elim_cons (i := 1) (n := .nil) (a := list u) (b := list y) (by simp [hB6])
                  (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 8) (v := encode s) (by simp) h₁)
                    (Eval.elim_cons (i := 0) (n := .nil) (a := .nil) (b := ofNat s') (by simp [hus])
                      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 15) (v := sD) (by simp))
                          (Eval.cons (Eval.var_of_get (i := 13) (v := nD) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 9) (v := kD) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 7) (v := wD) (by simp))
                                (Eval.var_of_get (i := 5) (v := jD) (by simp))))))
                        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := ofNat s) (by simp))
                            (Eval.cons (Eval.var_of_get (i := 4) (v := list u) (by simp))
                              (Eval.cons (Eval.var_of_get (i := 5) (v := list y) (by simp))
                                (Eval.cons (Eval.var_of_get (i := 0) (v := ctx) (by simp [hctx, mapCtx]))
                                  (Eval.nil _)))))
                          (Eval.let_ h₂
                            (callVar_eval revProg_wellScoped (i := 0) (v := list res) (by simp [hres])
                              h₃))))))))))))
  refine ⟨_, ?_, run⟩
  have hres_sz : (list res).size ≤ u.length * Tu + 1 := by
    refine (size_list_mapAcc_le f _ Tu fun p hp => ?_).trans ?_
    · obtain ⟨t, ht, h⟩ := hf p hp
      exact h.size_le.trans ht
    · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (length_chunkPairs_le s hs u y)) 1
  have hres_len : res.length + 1 ≤ (list res).size := length_le_size_list' res
  have hZ' : u.length * Tu + 1 ≤ Z := by
    have : u.length * Tu ≤ u.length * (Tu + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
    omega
  have h₃' : (res.length + 1 + 1) * ((list res).size + 1 + 12) ≤ (Z + 2) * (Z + 13) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hctx' : ctx.size = sD.size + nD.size + kD.size + wD.size + jD.size + 4 := by
    simp [hctx, mapCtx]; omega
  have he : (encode s : Data).size = esize s := rfl
  have ht₂' : (u.length + 1) * mapIter Z ≤ ((list u).size + 1) * mapIter Z :=
    Nat.mul_le_mul_right _ (by have := length_le_size_list' u; omega)
  unfold lockCost toUnaryCost
  simp only [size_ofNat, he] at ht₁ ⊢
  rw [hctx']
  omega

/-! ## The core program -/

/-- The dispatch on the kind of the query, in the environment `coreEnv`: `dimProg` on
`(s, λ, n, τ)` when the kind is `nil`, `lockProg` on `(S̄, n, s, kind, rest)` otherwise. -/
def coreDispatch (univ : Prog) : Prog :=
  .elim 3 .nil
    (.elim 0
      (.let_ (.cons (.var 2) (.cons (.var 6) (.cons (.var 4) (.var 7)))) (callVar 0 dimProg))
      (.let_ (.cons (.var 10) (.cons (.var 6) (.cons (.var 4) (.cons (.var 2) (.var 3)))))
        (callVar 0 (lockProg univ))))

theorem coreDispatch_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (coreDispatch univ).WellScoped 11 := by
  simp only [coreDispatch, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega,
    ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, dimProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, by omega,
    (lockProg_wellScoped hU).mono (by omega) _⟩

/-- The core of the repeated sampler, before the s-m-n construction: on
`((S̄, λ, τ), (n, q))`, the dimension of `S̄` at `n` through `univ`, then the dispatch. -/
def repSampCore (univ : Prog) : Prog :=
  .elim 0 .nil
    (.elim 0 .nil
      (.elim 1 .nil
        (.elim 5 .nil
          (.let_ (.cons (.var 4) (.cons (.var 0) (.const (encode CL.Sampler.Query.dimension))))
            (.let_ (callVar 0 univ) (coreDispatch univ))))))

theorem repSampCore_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (repSampCore univ).WellScoped 1 := by
  simp only [repSampCore, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial,
    ⟨by omega, by omega, trivial⟩, ⟨by omega, hU.mono (by omega) _⟩, coreDispatch_wellScoped hU⟩

/-- The hardcoded datum `(S̄, λ, τ)`. -/
def sampParams (sD lD tD : Data) : Data := .cons sD (.cons lD tD)

/-- The size of the encoded dimension query. -/
theorem size_encode_dimension : (encode CL.Sampler.Query.dimension : Data).size = 9 := rfl

/-- The environment of the dispatch: the dimension `sz`, the dimension query, `n`, the query
`d`, `λ`, `τ`, `S̄`, and the input's spine. -/
def coreEnv (sD lD tD nD d sz : Data) : Env :=
  [sz, .cons sD (.cons nD (encode CL.Sampler.Query.dimension)), nD, d, lD, tD, sD,
    .cons lD tD, sampParams sD lD tD, .cons nD d, .cons (sampParams sD lD tD) (.cons nD d)]

/-- The common prefix of the core: the input taken apart and the dimension query answered,
then the dispatch. -/
theorem repSampCore_prefix {univ : Prog} (hU : univ.WellScoped 1) (sD lD tD nD d : Data)
    {sz : Data} {td : ℕ}
    (hdim : Eval [Data.cons sD (.cons nD (encode CL.Sampler.Query.dimension))] univ sz td)
    {r : Data} {t : ℕ} (hc : Eval (coreEnv sD lD tD nD d sz) (coreDispatch univ) r t) :
    Eval [Data.cons (sampParams sD lD tD) (.cons nD d)] (repSampCore univ) r
      (t + td + 2 * (sD.size + nD.size) + 32) := by
  have run : Eval [Data.cons (sampParams sD lD tD) (.cons nD d)] (repSampCore univ) r _ :=
    Eval.elim_cons (env := [Data.cons (sampParams sD lD tD) (.cons nD d)]) (i := 0) (n := .nil)
      (a := sampParams sD lD tD) (b := .cons nD d) (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := sD) (b := .cons lD tD) (by simp [sampParams])
        (Eval.elim_cons (i := 1) (n := .nil) (a := lD) (b := tD) (by simp)
          (Eval.elim_cons (i := 5) (n := .nil) (a := nD) (b := d) (by simp)
            (Eval.let_ (Eval.cons (Eval.var_of_get (i := 4) (v := sD) (by simp))
                (Eval.cons (Eval.var_of_get (i := 0) (v := nD) (by simp)) (Eval.const _ _)))
              (Eval.let_ (callVar_eval hU (i := 0)
                  (v := .cons sD (.cons nD (encode CL.Sampler.Query.dimension))) (by simp) hdim)
                hc)))))
  refine run.cast_cost ?_
  simp only [size_cons, size_encode_dimension]
  omega

/-- The dispatch on an empty query: `nil`. -/
theorem coreDispatch_nil (univ : Prog) (sD lD tD nD sz : Data) :
    Eval (coreEnv sD lD tD nD .nil sz) (coreDispatch univ) .nil 2 :=
  Eval.elim_nil (i := 3) (by simp [coreEnv]) (Eval.nil _)

/-- The dispatch on a dimension query (kind `nil`): `dimProg` on `(sz, λ, n, τ)`. -/
theorem coreDispatch_dim (univ : Prog) (sD lD tD nD qr sz : Data) {r : Data} {t : ℕ}
    (hd : Eval [Data.cons sz (.cons lD (.cons nD tD))] dimProg r t) :
    Eval (coreEnv sD lD tD nD (.cons .nil qr) sz) (coreDispatch univ) r
      (t + 2 * (sz.size + lD.size + nD.size + tD.size) + 15) := by
  have run : Eval (coreEnv sD lD tD nD (.cons .nil qr) sz) (coreDispatch univ) r _ :=
    Eval.elim_cons (i := 3) (n := .nil) (a := .nil) (b := qr) (by simp [coreEnv])
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := sz) (by simp [coreEnv]))
            (Eval.cons (Eval.var_of_get (i := 6) (v := lD) (by simp [coreEnv]))
              (Eval.cons (Eval.var_of_get (i := 4) (v := nD) (by simp [coreEnv]))
                (Eval.var_of_get (i := 7) (v := tD) (by simp [coreEnv])))))
          (callVar_eval dimProg_wellScoped (i := 0) (v := .cons sz (.cons lD (.cons nD tD)))
            (by simp) hd)))
  refine run.cast_cost ?_
  simp only [size_cons]
  omega

/-- The dispatch on a query of nonzero kind: `lockProg` on `(S̄, n, sz, kind, rest)`. -/
theorem coreDispatch_lock {univ : Prog} (hU : univ.WellScoped 1) (sD lD tD nD k₀ k₁ qr sz : Data)
    {r : Data} {t : ℕ}
    (hl : Eval [Data.cons sD (.cons nD (.cons sz (.cons (.cons k₀ k₁) qr)))] (lockProg univ) r t) :
    Eval (coreEnv sD lD tD nD (.cons (.cons k₀ k₁) qr) sz) (coreDispatch univ) r
      (t + 2 * (sD.size + nD.size + sz.size + k₀.size + k₁.size + qr.size) + 20) := by
  have run : Eval (coreEnv sD lD tD nD (.cons (.cons k₀ k₁) qr) sz) (coreDispatch univ) r _ :=
    Eval.elim_cons (i := 3) (n := .nil) (a := .cons k₀ k₁) (b := qr) (by simp [coreEnv])
      (Eval.elim_cons (i := 0) (a := k₀) (b := k₁) (by simp)
        (Eval.let_ (Eval.cons (Eval.var_of_get (i := 10) (v := sD) (by simp [coreEnv]))
            (Eval.cons (Eval.var_of_get (i := 6) (v := nD) (by simp [coreEnv]))
              (Eval.cons (Eval.var_of_get (i := 4) (v := sz) (by simp [coreEnv]))
                (Eval.cons (Eval.var_of_get (i := 2) (v := .cons k₀ k₁) (by simp [coreEnv]))
                  (Eval.var_of_get (i := 3) (v := qr) (by simp [coreEnv]))))))
          (callVar_eval (lockProg_wellScoped hU) (i := 0)
            (v := .cons sD (.cons nD (.cons sz (.cons (.cons k₀ k₁) qr)))) (by simp) hl)))
  refine run.cast_cost ?_
  simp only [size_cons]
  omega

end Prog

end MIPRE.Cost
