/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Halting.CompressorCost

/-!
# The compressor as a program, and the halting reduction from compression alone

The last piece of obligation O4: the map `(c, n) ↦ comprStr c n (λ(n))` as a polynomial-time
function of the ambient model (`comprPoly`), which `exists_compressorSpec` turns into a
`CompressorSpec`, hence into `Obligations`, hence — through `halting_reduction` — into the
halting reduction with **no hypothesis but gap-preserving compression**: `halting_reduction_of`
in `val*`, and `halting_reduces_to_gameValue_of` in the headline's `gameValue`.

The program writes `λ(n) = 2 ^ (2 · size n)` in binary by walking the bits of `n` twice with
`lenBody`, prepending a `0` per bit to the numeral `1` (`lamProg`); assembles `(c, n, λ(n))`;
hardcodes it into `haltProg` with `smnProg`; pairs the parameter with the result; and serializes
the pair with `serProg`. Every stage is linear or quadratic in its input, so the whole is
quadratic in `|c| + |n|`.
-/

namespace MIPRE

open Cost

namespace Cost.Prog

open Data

/-! ## The parameter in binary -/

/-- The bits of `2 ^ e`: `e` zeros then a one. -/
theorem bits_two_pow (e : ℕ) : (2 ^ e).bits = List.replicate e false ++ [true] := by
  have hval : ∀ e, (List.replicate e false ++ [true]).foldr Nat.bit 0 = 2 ^ e := by
    intro e
    induction e with
    | zero => rfl
    | succ e ih =>
      rw [List.replicate_succ, List.cons_append, List.foldr_cons, ih, Nat.bit_false, pow_succ]
      ring
  have hcanon : List.replicate e false ++ [true] = [] ∨
      (List.replicate e false ++ [true]).getLast? = some true := Or.inr (by simp)
  rw [← hval e, bits_foldr_of_canon _ hcanon]

/-- `encode (2 ^ e)`, as a list of `e` `nil`s in front of the numeral `1`. -/
theorem encode_two_pow_list (e : ℕ) :
    (encode (2 ^ e) : Data) = Data.list (List.replicate e .nil ++ [.cons .nil .nil]) := by
  show (encode (2 ^ e).bits : Data) = _
  rw [bits_two_pow, encode_bitStr_eq_list, List.map_append, List.map_replicate]
  rfl

/-- `lamProg` on `encode n` computes `encode (2 ^ (2 · size n))`: two walks over the bits of
`n`, each prepending a `nil` per bit to the accumulator, from the numeral `1`. -/
def lamProg : Prog :=
  .let_ (.cons (.var 0) (.const (.cons (.cons .nil .nil) .nil)))
    (.let_ (.loop lenBody)
      (.let_ (.cons (.var 2) (.var 0)) (.loop lenBody)))

theorem lamProg_wellScoped : lamProg.WellScoped 1 := by
  simp [lamProg, WellScoped, lenBody]

theorem lamProg_runs (n : ℕ) :
    ∃ t ≤ 50 * (esize n + 5) ^ 2,
      lamProg.Runs (encode n) (encode (2 ^ (2 * Nat.size n))) t := by
  set l : List Data := n.bits.map Data.ofBool with hl
  have hen : (encode n : Data) = Data.list l := by
    show (encode n.bits : Data) = _; rw [encode_bitStr_eq_list]
  have hlen : l.length = Nat.size n := by rw [hl, List.length_map, Nat.size_eq_bits_len]
  have hsz : (Data.list l).size = esize n := by rw [← hen]; rfl
  have hsn : Nat.size n ≤ esize n := size_le_esize_nat n
  have hacc : ∀ k, (Data.list (List.replicate k .nil ++ [.cons .nil .nil])).size = 2 * k + 5 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append, Data.size_list_cons, ih]
      simp only [Data.size_nil]; omega
  -- the first walk
  obtain ⟨t₁, ht₁, h₁⟩ := lenLoop_runs l [.cons .nil .nil] [Data.list l] (esize n + 5 + 2 * esize n)
    (by simp only [Data.list_cons, Data.list_nil, Data.size_cons, Data.size_nil, hsz]; omega)
  -- the second walk, from the first's result
  obtain ⟨t₂, ht₂, h₂⟩ := lenLoop_runs l (List.replicate l.length .nil ++ [.cons .nil .nil])
    [Data.list (List.replicate l.length .nil ++ [.cons .nil .nil]), Data.cons (Data.list l)
      (.cons (.cons .nil .nil) .nil), Data.list l] (esize n + (2 * esize n + 5) + 2 * esize n)
    (by rw [hacc, hsz, hlen]; omega)
  -- the result is `encode (2 ^ (2 · size n))`
  have hres : Data.list (List.replicate l.length .nil ++
      (List.replicate l.length .nil ++ [.cons .nil .nil])) = encode (2 ^ (2 * Nat.size n)) := by
    rw [encode_two_pow_list, ← List.append_assoc, ← List.replicate_add, hlen, Nat.two_mul]
  rw [hres] at h₂
  have hstate : Data.cons (Data.list l) (Data.list [.cons .nil .nil]) =
      Data.cons (Data.list l) (.cons (.cons .nil .nil) .nil) := rfl
  rw [hstate] at h₁
  rw [hen]
  refine ⟨_, ?_, Eval.let_ (Eval.cons (Eval.var_of_get (env := [Data.list l]) (i := 0)
      (v := Data.list l) (by simp)) (Eval.const _ _))
    (Eval.let_ h₁
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := Data.list l) (by simp))
          (Eval.var_of_get (i := 0)
            (v := Data.list (List.replicate l.length .nil ++ [.cons .nil .nil])) (by simp)))
        h₂))⟩
  -- the arithmetic
  rw [hlen] at ht₁ ht₂
  have h1 : (Nat.size n + 1) * (esize n + 5 + 2 * esize n + 13) ≤ (esize n + 1) * (3 * esize n + 18) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (Nat.size n + 1) * (esize n + (2 * esize n + 5) + 2 * esize n + 13) ≤
      (esize n + 1) * (5 * esize n + 18) := Nat.mul_le_mul (by omega) (by omega)
  simp only [Data.size_cons, Data.size_nil, hsz, hacc, hlen]
  nlinarith

end Cost.Prog

namespace Halting

open Cost Cost.Prog

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The compressor's program -/

/-- The compressor: on `encode (c, n)`, the parameter in binary, the triple `(c, n, λ(n))`,
its hardcoding into `haltProg` (`smnProg`), the pair `(λ(n), decider)`, and its serialization. -/
def comprProg : Prog :=
  .elim 0 .nil                                            -- [cD, nD, input]
    (.let_ (callVar 1 lamProg)                            -- [lamD, cD, nD, input]
      (.let_ (.cons (.var 1) (.cons (.var 2) (.var 0)))    -- [P, lamD, cD, nD, input]
        (.let_ (.let_ (.cons (.const (encode (haltProg G U))) (.var 0)) smnProg)
                                                          -- [H, P, lamD, cD, nD, input]
          (.let_ (.cons (.var 2) (.var 0)) serProg))))    -- serProg on `cons lamD H`

theorem comprProg_wellScoped : (comprProg G U).WellScoped 1 := by
  refine ⟨Nat.zero_lt_one, trivial, callVar_wellScoped (by decide) lamProg_wellScoped, ?_⟩
  refine ⟨by simp [WellScoped], ?_⟩
  refine ⟨⟨⟨trivial, by simp [WellScoped]⟩, smnProg_wellScoped.mono (by omega) _⟩, ?_⟩
  exact ⟨by simp [WellScoped], serProg_wellScoped.mono (by omega) _⟩

/-- The description of the hardcoded decider, as `smnProg` builds it. -/
theorem smn_outDec (c : Prog) (n lam : ℕ) :
    Data.cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) (encode (c, n, lam)))
      (.cons .nil .nil))) (encode (haltProg G U))) = encode (outDec G U c n lam) :=
  (toData_hardcode _ _).symm

/-- **The compressor computes its output.** -/
theorem comprProg_runs (c : Prog) (n : ℕ) :
    ∃ t ≤ 20000 * (esize (c, n) + esize (haltProg G U) + 62) ^ 2,
      (comprProg G U).Runs (encode (c, n)) (encode (comprStr G U c n (lamOf n))) t := by
  obtain ⟨t₁, ht₁, h₁⟩ := lamProg_runs n
  have hlam : (encode (2 ^ (2 * Nat.size n)) : Data) = encode (lamOf n) := rfl
  rw [hlam] at h₁
  have h₂ := smnProg_runs (encode (haltProg G U)) (encode (c, n, lamOf n))
  rw [smn_outDec] at h₂
  obtain ⟨t₃, ht₃, h₃⟩ := serProg_runs (.cons (encode (lamOf n)) (encode (outDec G U c n (lamOf n))))
  have hP : (Data.cons (encode c) (.cons (encode n) (encode (lamOf n))) : Data) =
      encode (c, n, lamOf n) := rfl
  have hout : (encode (Data.cons (encode (lamOf n)) (encode (outDec G U c n (lamOf n)))).toBitsPost
      : Data) = encode (comprStr G U c n (lamOf n)) := rfl
  rw [hout] at h₃
  refine ⟨_, ?_, Eval.elim_cons (env := [encode (c, n)]) (i := 0) (a := encode c) (b := encode n)
      (by simp; rfl)
    (Eval.let_ (callVar_eval lamProg_wellScoped (i := 1) (v := encode n) (by simp) h₁)
      (Eval.let_ (Eval.cons (Eval.var_of_get (i := 1) (v := encode c) (by simp))
          (Eval.cons (Eval.var_of_get (i := 2) (v := encode n) (by simp))
            (Eval.var_of_get (i := 0) (v := encode (lamOf n)) (by simp))))
        (Eval.let_ (Eval.let_ (Eval.cons (Eval.const _ (encode (haltProg G U)))
              (Eval.var_of_get (i := 0) (v := encode (c, n, lamOf n))
                (by rw [Env.get_cons_zero]; rfl)))
            (Eval.append_of_wellScoped h₂ smnProg_wellScoped _))
          (Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := encode (lamOf n)) (by simp))
              (Eval.var_of_get (i := 0) (v := encode (outDec G U c n (lamOf n))) (by simp)))
            (Eval.append_of_wellScoped h₃ serProg_wellScoped _)))))⟩
  -- the arithmetic: everything is linear in `E = |c| + |n| + |haltProg|` but the serialization,
  -- which is quadratic
  obtain ⟨E, hEdef⟩ : ∃ E, E = esize c + esize n + esize (haltProg G U) := ⟨_, rfl⟩
  have hE : esize (c, n) = esize c + esize n + 1 := rfl
  have hec : (encode c : Data).size = esize c := rfl
  have hen : (encode n : Data).size = esize n := rfl
  have hel : (encode (lamOf n) : Data).size = esize (lamOf n) := rfl
  have heh : (encode (haltProg G U) : Data).size = esize (haltProg G U) := rfl
  have hl : esize (lamOf n) ≤ 8 * Nat.size n + 5 := esize_lamOf_le n
  have hsn : Nat.size n ≤ esize n := size_le_esize_nat n
  have hP' : (encode (c, n, lamOf n) : Data).size = esize c + (esize n + esize (lamOf n) + 1) + 1 := rfl
  have hO : (encode (outDec G U c n (lamOf n)) : Data).size =
      esize (haltProg G U) + esize c + esize n + esize (lamOf n) + 37 := esize_outDec G U c n (lamOf n)
  have hD : (Data.cons (encode (lamOf n)) (encode (outDec G U c n (lamOf n)))).size ≤ 18 * E + 48 := by
    rw [Data.size_cons, hel, hO]; omega
  have ht₃' : t₃ ≤ (3 * (18 * E + 48) + 2) * (16 * (18 * E + 48) + 42) +
      ((18 * E + 48) + 2) * (5 * (18 * E + 48) + 30) :=
    ht₃.trans (Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul (by omega) (by omega)))
  have ht₃'' : t₃ ≤ 17172 * E ^ 2 + 95148 * E + 131760 := ht₃'.trans (le_of_eq (by ring))
  have ht₁' : t₁ ≤ 50 * (E + 5) ^ 2 := ht₁.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have ht₁'' : t₁ ≤ 50 * E ^ 2 + 500 * E + 1250 := ht₁'.trans (le_of_eq (by ring))
  have hsq : (esize (c, n) + esize (haltProg G U) + 62) ^ 2 = (E + 63) ^ 2 := by rw [hE]; congr 1; omega
  rw [hsq]
  have hfin : 17222 * E ^ 2 + 96000 * E + 140000 ≤ 20000 * (E + 63) ^ 2 := by nlinarith
  omega

/-- **The compressor, as a polynomial-time function.** -/
noncomputable def comprPoly : PolyTimeFun (Prog × ℕ) BitStr where
  toFun p := comprStr G U p.1 p.2 (lamOf p.2)
  code := comprProg G U
  closed := comprProg_wellScoped G U
  timeBound := Polynomial.C 20000 * (Polynomial.X + Polynomial.C (esize (haltProg G U) + 62)) ^ 2
  computes := by
    rintro ⟨c, n⟩
    obtain ⟨t, ht, h⟩ := comprProg_runs G U c n
    refine ⟨t, ?_, h⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X]
    exact ht.trans (le_of_eq (by ring))

@[simp] theorem comprPoly_apply (c : Prog) (n : ℕ) :
    comprPoly G U (c, n) = comprStr G U c n (lamOf n) := rfl

/-! ## Obligation O4, discharged -/

/-- **The compressor's specification is inhabited.** -/
theorem exists_compressorSpec' : Nonempty (CompressorSpec G U) :=
  let ⟨S, _⟩ := exists_compressorSpec G U (comprPoly G U) fun _ _ => rfl
  ⟨S⟩

/-- **Obligation O4 is discharged**: `Obligations G U` is inhabited. -/
theorem exists_obligations : Nonempty (Obligations G U) :=
  let ⟨S⟩ := exists_compressorSpec' G U
  ⟨S.toObligations⟩

include G U in
/-- **The halting reduction from gap-preserving compression alone**, in `val*`. -/
theorem halting_reduction_of :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → quantumValue (g pc).game = 1) ∧
        (¬ (pc.eval 0).Dom → quantumValue (g pc).game ≤ 1 / 2) :=
  let ⟨O⟩ := exists_obligations G U
  halting_reduction G U O

-- The tabulation is opaque here as in `halting_reduction`, and for the same reason.
attribute [local irreducible] tab

include G U in
/-- **The headline, conditionally** (blueprint `thm:main` from `thm:compression`): from a
`GapCompression`, a computable map from machines to game descriptions whose *synchronous* game
value is `1` when the machine halts on the empty input and at most `1/2` when it does not.
This is `HaltingGameValue.halting_reduces_to_gameValue` with the compression theorem as a
hypothesis; the unconditional statement keeps its `sorry` as the target of chapter 6. -/
theorem halting_reduces_to_gameValue_of :
    ∃ g : Nat.Partrec.Code → HaltingGameValue.GameData, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        (HaltingGameValue.HaltsOnEmptyInput pc → HaltingGameValue.gameValue (g pc).toGame = 1) ∧
        (¬ HaltingGameValue.HaltsOnEmptyInput pc →
          HaltingGameValue.gameValue (g pc).toGame ≤ 1 / 2) := by
  obtain ⟨O⟩ := exists_obligations G U
  obtain ⟨nY, hyes⟩ := yYes_mem G U
  obtain ⟨nN, hno⟩ := yNo_mem G U
  obtain ⟨sem, hsem_closed, hsem⟩ := exists_sem G U
  obtain ⟨g, K, hg⟩ := Cost.compressibility_criterion_levels
    (classA G U) (classB G U) (max (max nY nN) O.n₀)
    yYes (fun n hn => hyes n (by omega)) yNo (fun n hn => hno n (by omega))
    sem hsem_closed hsem O.compr (fun c x n hn => O.compr_spec c x n (by omega))
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  have hsize : Computable fun pc : Nat.Partrec.Code => esize (compile pc) :=
    Data.primrec_size.to_comp.comp hc
  have hlevel : Computable fun pc : Nat.Partrec.Code => 2 ^ (K + 1 + esize (compile pc)) :=
    (primrec_two_pow.comp (Primrec.nat_add.comp (Primrec.const (K + 1)) Primrec.id)).to_comp.comp
      hsize
  refine ⟨fun pc => tab G U (g (compile pc)) (2 ^ (K + 1 + esize (compile pc))),
    (tab_computable G U).comp
      ((PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp).pair hlevel),
    fun pc => ⟨fun hdom => ?_, fun hdom => ?_⟩⟩
  · have hx := (hg (compile pc)).2.1 ((hspec pc).2 hdom)
    exact gameValue_tab_eq_one G U _ _ hx.1 hx.2.2
  · have hx := (hg (compile pc)).2.2 fun h => hdom ((hspec pc).1 h)
    obtain ⟨eX, eA, hμ, hD⟩ := tab_match G U _ _ hx.1
    exact Verifier.gameValue_toGame_le_of_valStar_le_doubled _ _ _ _ eX eA hμ hD hx.2.2

end Halting

end MIPRE
