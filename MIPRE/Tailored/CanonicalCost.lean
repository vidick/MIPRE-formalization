/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Canonical
public import MIPRE.Foundations.CL.DetypingProgParse
public import MIPRE.Tailored.Repeat.DomTools

@[expose] public section

/-!
# The running time of the canonical decider

P1b deferred the cost of the canonical decider `canonProg L LP` (`MIPRE.Tailored.Canonical`):
a bound on the running time of a decider in `MIPRE.Verifier.TimeBoundAt` quantifies over every
input `(n, d)`, malformed ones included, while the steps of `canonProg` are polynomial-time
functions, whose bounds hold on encodings only. This file puts a total parse in front
(`parseDIn`, the identity on encodings, `canonProgT L LP`) and bounds the running time.

* `pushProg_runs_le`, `step_runs`: a step of the decider, timed — the call's input built from the
  state, the input program run within its bound, the output pushed;
* `parseDIn`, `canonProgT`, `canonProgT_runs_iff`: the parse reads `(n, x, y, a, b)` off any
  data, and is the identity on encodings, so the decider accepts what `canonProg` accepts;
* `canonProgT_halts`: on every input `(n, d)` the decider halts within the explicit
  `canonBound`, when `L` and `LP` halt within `T (|d'| + 1)^k` on every `(n, d')` — every call's
  argument is a component of the parsed input, of size linear in `|d|`;
* `canonProgT_timeBound`: hence within `c (T + 10^k + |n| + 1)^m (|d| + 1)^{e (k + 1)}` for
  constants `c, m, e` independent of everything (`dom_canonBound`, with the domination tools of
  the repeated programs);
* `esize_canonProgT`: its description is `4 |L| + |LP|` plus a constant.

What remains for `MIPRE.Verifier.IsBounded` of the normal form verifier a tailored verifier
denotes, at a `λ'` linear in `λ`, is the wrapper of `Verifier.ofSamplerDecider` (the question-length
check and the universal machine), whose explicit cost is `wrapCore_cost'`.
-/

namespace MIPRE.Cost.Prog

open Data

theorem pushProg_runs_le {F P : Prog} (hP : P.WellScoped 1) {s v r : Data} {t₁ t₂ : ℕ}
    (h₁ : F.Runs s v t₁) (h₂ : P.Runs v r t₂) :
    ∃ t ≤ t₁ + t₂ + v.size + r.size + s.size + 8, (pushProg F P).Runs s (.cons r s) t := by
  have hcall : Eval [v, s] (.let_ (.var 0) P) r ((v.size + 1) + t₂ + 1) :=
    Eval.let_ (Eval.var_of_get (env := [v, s]) (i := 0) rfl)
      (Eval.append_of_wellScoped (env := [v]) h₂ hP [v, s])
  have hcons : Eval [r, v, s] (.cons (.var 0) (.var 2)) (.cons r s)
      ((r.size + 1) + (s.size + 1) + 1) :=
    Eval.cons (Eval.var_of_get (env := [r, v, s]) (i := 0) rfl)
      (Eval.var_of_get (env := [r, v, s]) (i := 2) rfl)
  refine ⟨_, ?_, Eval.let_ h₁ (Eval.let_ hcall hcons)⟩
  omega

end MIPRE.Cost.Prog

namespace MIPRE.Tailored

open Cost Cost.PolyTimeFun Cost.Data CL.Detyping.Program

/-! ## The total parse -/

/-- Read a decider's input `(n, x, y, a, b)` off any data, the identity on encodings. -/
noncomputable def parseDIn : PolyTimeFun Data DIn :=
  (readNat.comp treeHead).pair ((readBits.comp (treeHead.comp treeTail)).pair
    ((readBits.comp (treeHead.comp (treeTail.comp treeTail))).pair
      ((readBits.comp (treeHead.comp (treeTail.comp (treeTail.comp treeTail)))).pair
        (readBits.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))))))

theorem parseDIn_encode (i : DIn) : parseDIn (encode i) = i := by
  obtain ⟨n, x, y, a, b⟩ := i
  simp only [parseDIn, pair_apply, comp_apply, encode_prod, treeHead_cons, treeTail_cons,
    readNat_encode, readBits_encode]

theorem size_treeHead_le (d : Data) : (treeHead d).size ≤ d.size := by
  cases d with
  | nil => exact le_rfl
  | cons a b => simp only [treeHead_cons, size_cons]; omega

theorem size_treeTail_le (d : Data) : (treeTail d).size ≤ d.size := by
  cases d with
  | nil => exact le_rfl
  | cons a b => simp only [treeTail_cons, size_cons]; omega

theorem length_rawList_le' : ∀ d : Data, (rawList d).length ≤ d.size
  | .nil => by simp [rawList]
  | .cons a b => by
    have := length_rawList_le' b
    simp only [rawList, List.length_cons, size_cons]
    omega

theorem esize_readBits_le (d : Data) : esize (readBits d) ≤ 4 * d.size + 1 := by
  refine (esize_bitStr_le _).trans ?_
  have : (readBits d).length ≤ d.size := by
    change ((rawList d).map rawTruth).length ≤ _
    rw [List.length_map]; exact length_rawList_le' d
  omega

/-- The parsed index is the index. -/
theorem parseDIn_fst (n : ℕ) (d : Data) : (parseDIn (.cons (encode n) d)).1 = n := by
  simp only [parseDIn, pair_apply, comp_apply, treeHead_cons, readNat_encode]

/-- **The parsed strings are of size linear in the input.** -/
theorem esize_parseDIn_le (n : ℕ) (d : Data) :
    esize (parseDIn (.cons (encode n) d)).2.1 ≤ 4 * d.size + 1 ∧
      esize (parseDIn (.cons (encode n) d)).2.2.1 ≤ 4 * d.size + 1 ∧
      esize (parseDIn (.cons (encode n) d)).2.2.2.1 ≤ 4 * d.size + 1 ∧
      esize (parseDIn (.cons (encode n) d)).2.2.2.2 ≤ 4 * d.size + 1 := by
  simp only [parseDIn, pair_apply, comp_apply, treeTail_cons]
  have h1 := size_treeHead_le d
  have h2 := size_treeTail_le d
  have h3 := size_treeHead_le (treeTail d)
  have h4 := size_treeTail_le (treeTail d)
  have h5 := size_treeHead_le (treeTail (treeTail d))
  have h6 := size_treeTail_le (treeTail (treeTail d))
  refine ⟨(esize_readBits_le _).trans (by omega), (esize_readBits_le _).trans (by omega),
    (esize_readBits_le _).trans (by omega), (esize_readBits_le _).trans (by omega)⟩

theorem length_parseDIn_le (n : ℕ) (d : Data) :
    (parseDIn (.cons (encode n) d)).2.2.2.1.length ≤ d.size ∧
      (parseDIn (.cons (encode n) d)).2.2.2.2.length ≤ d.size := by
  simp only [parseDIn, pair_apply, comp_apply, treeTail_cons]
  have hb : ∀ t : Data, (readBits t).length ≤ t.size := fun t => by
    change ((rawList t).map rawTruth).length ≤ _
    rw [List.length_map]; exact length_rawList_le' t
  have h2 := size_treeTail_le d
  have h4 := size_treeTail_le (treeTail d)
  have h5 := size_treeHead_le (treeTail (treeTail d))
  have h6 := size_treeTail_le (treeTail (treeTail d))
  exact ⟨(hb _).trans (by omega), (hb _).trans (by omega)⟩

theorem esize_bool_le' (b : Bool) : esize b ≤ 3 := by cases b <;> simp

/-- **The canonical decider with a total parse in front.** -/
noncomputable def canonProgT (L P : Prog) : Prog := seqProg parseDIn.code (canonProg L P)

theorem canonProgT_wellScoped {L P : Prog} (hL : L.WellScoped 1) (hP : P.WellScoped 1) :
    (canonProgT L P).WellScoped 1 :=
  seqProg_closed parseDIn.closed (canonProg_wellScoped hL hP)

/-- **On encoded inputs the parse changes nothing.** -/
theorem canonProgT_runs_iff {L P : Prog} (hL : L.WellScoped 1) (hP : P.WellScoped 1) (i : DIn)
    (out : Data) :
    (∃ t, (canonProgT L P).Runs (encode i) out t) ↔ ∃ t, (canonProg L P).Runs (encode i) out t := by
  obtain ⟨tp, -, hp⟩ := parseDIn.computes (encode i : Data)
  rw [parseDIn_encode, encode_data] at hp
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨y, s, u, h₁, h₂⟩ := seqProg_inv (canonProg_wellScoped hL hP) h
    obtain ⟨rfl, -⟩ := Eval.deterministic h₁ hp
    exact ⟨u, h₂⟩
  · rintro ⟨t, h⟩
    exact ⟨_, seqProg_runs (canonProg_wellScoped hL hP) hp h⟩

/-! ## One step: a call of an input program, pushed onto the state -/

/-- **A step of the canonical decider, timed**: from the state `s`, build the input `F s` of a
program `Q` whose first component is the index `n`, run `Q` within its time bound, and push the
output. -/
theorem step_runs {σ β : Type*} [SizedEncoding σ] [SizedEncoding β] (F : PolyTimeFun σ (ℕ × β))
    {Q : Prog} (hQ : Q.WellScoped 1) {n T k : ℕ}
    (hQt : ∀ d : Data, HaltsWithin Q (.cons (encode n) d) (T * (d.size + 1) ^ k)) (s : σ)
    (hn : (F s).1 = n) {Z : ℕ} (hZ : esize (F s).2 + 1 ≤ Z) :
    ∃ (r : Data) (t : ℕ), (Prog.pushProg F.code Q).Runs (encode s) (encode ((r, s) : Data × σ)) t ∧
      r.size ≤ T * Z ^ k ∧
      t ≤ 2 * F.timeBound.eval (esize s) + 2 * (T * Z ^ k) + esize s + 8 := by
  obtain ⟨t₁, ht₁, h₁⟩ := F.computes s
  have henc : (encode (F s) : Data) = .cons (encode n) (encode (F s).2) := by
    rw [← hn]; rfl
  obtain ⟨r, t₂, ht₂, h₂⟩ := hQt (encode (F s).2)
  have hsz : (encode (F s).2 : Data).size + 1 ≤ t₁ := by
    have := h₁.size_le
    rw [henc, Data.size_cons] at this
    omega
  have ht₂' : t₂ ≤ T * Z ^ k :=
    ht₂.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ _))
  rw [← henc] at h₂
  obtain ⟨t, ht, hrun⟩ := Prog.pushProg_runs_le hQ h₁ h₂
  have hv : (encode (F s) : Data).size ≤ t₁ := h₁.size_le
  have hr : r.size ≤ t₂ := Eval.size_le h₂
  refine ⟨r, t, ?_, hr.trans ht₂', ?_⟩
  · simpa [encode_prod, encode_data] using hrun
  · unfold esize at *
    omega

/-! ## The running time -/

/-- The explicit bound on the running time, from the time `T · Z^k` of a call and the sizes:
`S` the size of the input, `Z` a bound on the calls' argument sizes. -/
noncomputable def canonBound (T k S Z : ℕ) : ℕ :=
  let Y := T * Z ^ k
  let A0 := parseDIn.timeBound.eval S
  let A1 := Y + A0 + 1
  let A2 := Y + A1 + 1
  let A3 := Y + A2 + 1
  let A4 := Y + A3 + 1
  let A5 := Y + A4 + 1
  A0 + (2 * canonIn₁.timeBound.eval A0 + 2 * Y + A0 + 8) +
    (2 * canonIn₂.timeBound.eval A1 + 2 * Y + A1 + 8) +
    (2 * canonIn₃.timeBound.eval A2 + 2 * Y + A2 + 8) +
    (2 * canonIn₄.timeBound.eval A3 + 2 * Y + A3 + 8) +
    (2 * canonIn₅.timeBound.eval A4 + 2 * Y + A4 + 8) +
    canonFinal.timeBound.eval A5 + 6

/-- **The canonical decider halts within `canonBound`** on every input `(n, d)`, when `L` and
`LP` halt within `T (|d'| + 1)^k` on every input `(n, d')`. -/
theorem canonProgT_halts {L P : Prog} (hL : L.WellScoped 1) (hP : P.WellScoped 1) {n T k : ℕ}
    (hLt : ∀ d : Data, HaltsWithin L (.cons (encode n) d) (T * (d.size + 1) ^ k))
    (hPt : ∀ d : Data, HaltsWithin P (.cons (encode n) d) (T * (d.size + 1) ^ k)) (d : Data) :
    HaltsWithin (canonProgT L P) (.cons (encode n) d)
      (canonBound T k (Data.cons (encode n) d).size (20 * d.size + 20)) := by
  obtain ⟨tp, htp, hp⟩ := parseDIn.computes (Data.cons (encode n) d)
  rw [encode_data] at hp
  have hi1 : (parseDIn (.cons (encode n) d)).1 = n := parseDIn_fst n d
  obtain ⟨e1, e2, e3, e4⟩ := esize_parseDIn_le n d
  obtain ⟨l3, l4⟩ := length_parseDIn_le n d
  set i := parseDIn (.cons (encode n) d) with hi
  have hA0 : esize i ≤ parseDIn.timeBound.eval (Data.cons (encode n) d).size :=
    (Eval.size_le hp).trans (by simpa [esize_data] using htp)
  have hb := esize_bool_le' false
  have hb' := esize_bool_le' true
  -- the five steps
  obtain ⟨r₁, t₁, h₁, hr₁, ht₁⟩ := step_runs canonIn₁ hL hLt i (by simp [hi1])
    (Z := 20 * d.size + 20) (by simp only [canonIn₁_apply, esize_prod]; omega)
  obtain ⟨r₂, t₂, h₂, hr₂, ht₂⟩ := step_runs canonIn₂ hL hLt (r₁, i) (by simp [hi1])
    (Z := 20 * d.size + 20) (by simp only [canonIn₂_apply, esize_prod]; omega)
  obtain ⟨r₃, t₃, h₃, hr₃, ht₃⟩ := step_runs canonIn₃ hL hLt (r₂, r₁, i) (by simp [hi1])
    (Z := 20 * d.size + 20) (by simp only [canonIn₃_apply, esize_prod]; omega)
  obtain ⟨r₄, t₄, h₄, hr₄, ht₄⟩ := step_runs canonIn₄ hL hLt (r₃, r₂, r₁, i) (by simp [hi1])
    (Z := 20 * d.size + 20) (by simp only [canonIn₄_apply, esize_prod]; omega)
  obtain ⟨r₀, t₅, h₅, hr₀, ht₅⟩ := step_runs canonIn₅ hP hPt (r₄, r₃, r₂, r₁, i) (by simp [hi1])
    (Z := 20 * d.size + 20) (by
      simp only [canonIn₅_apply, esize_prod]
      have ha := esize_bitStr_le (i.2.2.2.1.take (spineList r₁).length)
      have hb₂ := esize_bitStr_le (i.2.2.2.2.take (spineList r₃).length)
      simp only [List.length_take] at ha hb₂
      have : min (spineList r₁).length i.2.2.2.1.length ≤ d.size := (min_le_right _ _).trans l3
      have : min (spineList r₃).length i.2.2.2.2.length ≤ d.size := (min_le_right _ _).trans l4
      omega)
  obtain ⟨tf, htf, hf⟩ := canonFinal.computes (r₀, r₄, r₃, r₂, r₁, i)
  -- assemble
  have c₄ := seqProg_runs canonFinal.closed h₅ hf
  have c₃ := seqProg_runs (canonTail₄_wellScoped hP) h₄ c₄
  have c₂ := seqProg_runs (canonTail₃_wellScoped hL hP) h₃ c₃
  have c₁ := seqProg_runs (canonTail₂_wellScoped hL hP) h₂ c₂
  have c₀ := seqProg_runs (canonTail₁_wellScoped hL hP) h₁ c₁
  have cT := seqProg_runs (canonProg_wellScoped hL hP) hp c₀
  refine ⟨_, _, ?_, cT⟩
  have htp' : tp ≤ parseDIn.timeBound.eval (Data.cons (encode n) d).size := by
    simpa [esize_data] using htp
  generalize hY : T * (20 * d.size + 20) ^ k = Y at hr₁ hr₂ hr₃ hr₄ hr₀ ht₁ ht₂ ht₃ ht₄ ht₅
  generalize hA : parseDIn.timeBound.eval (Data.cons (encode n) d).size = A0 at hA0 htp'
  have a1 : esize (r₁, i) ≤ Y + A0 + 1 := by simp only [esize_prod, esize_data]; omega
  have a2 : esize (r₂, r₁, i) ≤ Y + (Y + A0 + 1) + 1 := by
    simp only [esize_prod, esize_data] at a1 ⊢; omega
  have a3 : esize (r₃, r₂, r₁, i) ≤ Y + (Y + (Y + A0 + 1) + 1) + 1 := by
    simp only [esize_prod, esize_data] at a2 ⊢; omega
  have a4 : esize (r₄, r₃, r₂, r₁, i) ≤ Y + (Y + (Y + (Y + A0 + 1) + 1) + 1) + 1 := by
    simp only [esize_prod, esize_data] at a3 ⊢; omega
  have a5 : esize (r₀, r₄, r₃, r₂, r₁, i) ≤
      Y + (Y + (Y + (Y + (Y + A0 + 1) + 1) + 1) + 1) + 1 := by
    simp only [esize_prod, esize_data] at a4 ⊢; omega
  have m1 := polynomial_eval_mono canonIn₁.timeBound hA0
  have m2 := polynomial_eval_mono canonIn₂.timeBound a1
  have m3 := polynomial_eval_mono canonIn₃.timeBound a2
  have m4 := polynomial_eval_mono canonIn₄.timeBound a3
  have m5 := polynomial_eval_mono canonIn₅.timeBound a4
  have mf := polynomial_eval_mono canonFinal.timeBound a5
  unfold canonBound
  rw [hY, hA]
  dsimp only
  omega

/-! ## The bound, dominated -/

open Polynomial in
/-- One polynomial bounding every stage, evaluated at the largest state size. -/
noncomputable def canonPoly : Polynomial ℕ :=
  2 * (canonIn₁.timeBound + canonIn₂.timeBound + canonIn₃.timeBound + canonIn₄.timeBound +
    canonIn₅.timeBound) + canonFinal.timeBound + 15 * X + 46

theorem canonBound_le (T k S Z : ℕ) :
    canonBound T k S Z ≤ canonPoly.eval (5 * (T * Z ^ k) + parseDIn.timeBound.eval S + 5) := by
  generalize hY : T * Z ^ k = Y
  generalize hA : parseDIn.timeBound.eval S = A0
  have key : ∀ (P : Polynomial ℕ) {u : ℕ}, u ≤ 5 * Y + A0 + 5 →
      P.eval u ≤ P.eval (5 * Y + A0 + 5) := fun P {_} h => polynomial_eval_mono P h
  have m1 := key canonIn₁.timeBound (u := A0) (by omega)
  have m2 := key canonIn₂.timeBound (u := Y + A0 + 1) (by omega)
  have m3 := key canonIn₃.timeBound (u := Y + (Y + A0 + 1) + 1) (by omega)
  have m4 := key canonIn₄.timeBound (u := Y + (Y + (Y + A0 + 1) + 1) + 1) (by omega)
  have m5 := key canonIn₅.timeBound (u := Y + (Y + (Y + (Y + A0 + 1) + 1) + 1) + 1) (by omega)
  have mf := key canonFinal.timeBound
    (u := Y + (Y + (Y + (Y + (Y + A0 + 1) + 1) + 1) + 1) + 1) (by omega)
  unfold canonBound canonPoly
  rw [hY, hA]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/-- **The canonical decider's bound is dominated**: `c (W + 1)^m X^{e (K + 1)}`, for `W` above
the call constant `T`, `10^K` and the index's size, `X` the input's size plus one. -/
theorem dom_canonBound : ∃ c m e, ∀ (W X K T S Z : ℕ), 1 ≤ X → 10 ^ K ≤ W → T ≤ W →
    S ≤ W + X → Z ≤ 20 * X → Repeat.Dom W X K c m e (canonBound T K S Z) := by
  obtain ⟨c0, m0, e0, h0⟩ := Repeat.dom_poly parseDIn.timeBound 2 1 1
  obtain ⟨c, m, e, hQ⟩ := Repeat.dom_poly canonPoly (5 * (1 * 1) + c0 + 5)
    (max (max (0 + (1 + 2)) m0) 0) (max (max (0 + (0 + 1)) e0) 0)
  refine ⟨c, m, e, fun W X K T S Z hX hW hT hS hZ => ?_⟩
  have dS : Repeat.Dom W X K (1 + 1 + 0) 1 1 S := Repeat.Dom.ofLin hX (by omega)
  have dA0 := h0 W X K hX dS
  have dY : Repeat.Dom W X K (1 * 1) (1 + 2) (0 + 1) (T * Z ^ K) :=
    (Repeat.Dom.ofLeW hT).mul (Repeat.dom_powK hX hW (a := 20) (j := 2) (by norm_num) hZ)
  have dA := (((Repeat.Dom.const 5).mul dY).add hX dA0).add hX (Repeat.Dom.const 5)
  exact (hQ W X K hX dA).of_le (canonBound_le T K S Z)

/-- **The running time of the canonical decider.** There are constants `c, m, e` such that, when
`L` and `LP` halt within `T (|d| + 1)^k` on every input `(n, d)`, the canonical decider (with
its total parse) halts within `c (T + 10^k + |n| + 1)^m (|d| + 1)^{e (k + 1)}` on every input
`(n, d)`, malformed ones included. -/
theorem canonProgT_timeBound : ∃ c m e, ∀ {L P : Prog}, L.WellScoped 1 → P.WellScoped 1 →
    ∀ {n T k : ℕ}, (∀ d : Data, HaltsWithin L (.cons (encode n) d) (T * (d.size + 1) ^ k)) →
      (∀ d : Data, HaltsWithin P (.cons (encode n) d) (T * (d.size + 1) ^ k)) →
      ∀ d : Data, HaltsWithin (canonProgT L P) (.cons (encode n) d)
        (c * (T + 10 ^ k + esize n + 1) ^ m * (d.size + 1) ^ (e * (k + 1))) := by
  obtain ⟨c, m, e, h⟩ := dom_canonBound
  refine ⟨c, m, e, fun {L P} hL hP {n T k} hLt hPt d => ?_⟩
  obtain ⟨r, t, ht, hrun⟩ := canonProgT_halts hL hP hLt hPt d
  refine ⟨r, t, ht.trans ?_, hrun⟩
  have e0 : (Data.cons (encode n) d).size = esize n + d.size + 1 := rfl
  have hS : (Data.cons (encode n) d).size ≤ (T + 10 ^ k + esize n) + (d.size + 1) := by
    rw [e0]; generalize 10 ^ k = P; omega
  have hX : 1 ≤ d.size + 1 := by omega
  have hW : 10 ^ k ≤ T + 10 ^ k + esize n :=
    (Nat.le_add_left _ T).trans (Nat.le_add_right _ _)
  have hT : T ≤ T + 10 ^ k + esize n := (Nat.le_add_right T _).trans (Nat.le_add_right _ _)
  have hZ : 20 * d.size + 20 ≤ 20 * (d.size + 1) := by omega
  exact h (T + 10 ^ k + esize n) (d.size + 1) k T _ _ hX hW hT hS hZ

/-! ## The description size -/

/-- **The canonical decider's description is linear in those of `L` and `LP`**: `L` appears four
times and `LP` once, the rest is fixed. -/
theorem esize_canonProgT (L P : Prog) :
    esize (canonProgT L P) + 5 * esize Prog.nil =
      esize (canonProgT Prog.nil Prog.nil) + 4 * esize L + esize P := by
  simp only [canonProgT, canonProg, canonTail₁, canonTail₂, canonTail₃, canonTail₄, seqProg,
    Prog.pushProg, Prog.esize_eq_size_toData, Prog.toData, Data.size_cons]
  omega

end MIPRE.Tailored

end
