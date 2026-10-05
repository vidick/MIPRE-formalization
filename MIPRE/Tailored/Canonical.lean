/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Verifier
public import MIPRE.Foundations.Cost.Reader
public import MIPRE.Foundations.Cost.Binary
public import MIPRE.Foundations.Cost.While
public import MIPRE.Foundations.LowDegree.BinaryLinear
public import MIPRE.Foundations.SAT.PcpFormat
public import MIPRE.Foundations.SAT.FmlProg
public import MIPRE.Tactics

@[expose] public section

/-!
# The canonical decider, as a program

Paper II, II:1757–1787: the canonical decider of a tailored normal form verifier, on the questions
`x, y` and the answers `a, b` of index `n`, runs the answer-length calculator `L` on `(n, x, κ)` and
`(n, y, κ)` for both kinds `κ` of variables, checks that `|a| = ℓ^R(x) + ℓ^L(x)` and
`|b| = ℓ^R(y) + ℓ^L(y)`, runs the linear-constraints processor `LP` on the readable parts
`(n, x, y, a^R, b^R)`, and accepts when every constraint `c` it outputs satisfies
`⟨c, (a, b, 1)⟩ = 0`. This file writes it as a program of the ambient model.

* `Prog.pushProg F P`: from a state `s`, running `P` on an input `F s` built from it and pushing
  the output onto the state — with its runs and its inversion, and that of `Cost.seqProg`.
* The polynomial-time pieces: the readings of `Cost.Data.spineList` and `Cost.Data.bitsListD` as
  programs, the length check, `satF` (one linear constraint, through the parity dot product
  `LowDegree.BinaryLinear.dotBitsProg`) and `allSatF` (all of them).
* `canonProg L LP`: the four runs of `L`, the run of `LP`, and the final check, in sequence;
  `canonProg_accepts`: it accepts exactly when the five runs halt and the check passes.
-/

namespace MIPRE.Cost

/-! ## Running programs in sequence -/

/-- Inverting `seqProg`: a run of `p` then `q` is a run of `p`, and one of `q` on its output. -/
theorem seqProg_inv {p q : Prog} (hq : q.WellScoped 1) {x z : Data} {t : ℕ}
    (h : (seqProg p q).Runs x z t) : ∃ y s u, p.Runs x y s ∧ q.Runs y z u := by
  unfold seqProg Prog.Runs at h
  cases h with
  | let_ h₁ h₂ =>
    exact ⟨_, _, _, h₁, Eval.of_append_of_wellScoped (env := [_]) (extra := [x]) h₂ hq⟩

namespace Prog

open Data

/-- From a state `s`: build the input `F s`, run the closed program `P` on it, and push its
output onto the state, `cons (P (F s)) s`. -/
def pushProg (F P : Prog) : Prog := .let_ F (.let_ (.let_ (.var 0) P) (.cons (.var 0) (.var 2)))

theorem pushProg_wellScoped {F P : Prog} (hF : F.WellScoped 1) (hP : P.WellScoped 1) :
    (pushProg F P).WellScoped 1 := by
  refine ⟨hF, ⟨⟨by simp [WellScoped], hP.mono (by omega) _⟩, ?_⟩⟩
  simp [WellScoped]

theorem pushProg_runs {F P : Prog} (hP : P.WellScoped 1) {s v r : Data} {t₁ t₂ : ℕ}
    (h₁ : F.Runs s v t₁) (h₂ : P.Runs v r t₂) : ∃ t, (pushProg F P).Runs s (.cons r s) t := by
  have hcall : Eval [v, s] (.let_ (.var 0) P) r ((v.size + 1) + t₂ + 1) :=
    Eval.let_ (Eval.var_of_get (env := [v, s]) (i := 0) rfl)
      (Eval.append_of_wellScoped (env := [v]) h₂ hP [v, s])
  have hcons : Eval [r, v, s] (.cons (.var 0) (.var 2)) (.cons r s)
      ((r.size + 1) + (s.size + 1) + 1) :=
    Eval.cons (Eval.var_of_get (env := [r, v, s]) (i := 0) rfl)
      (Eval.var_of_get (env := [r, v, s]) (i := 2) rfl)
  exact ⟨_, Eval.let_ h₁ (Eval.let_ hcall hcons)⟩

theorem pushProg_inv {F P : Prog} (hP : P.WellScoped 1) {s out : Data} {t : ℕ}
    (h : (pushProg F P).Runs s out t) :
    ∃ v r t₁ t₂, F.Runs s v t₁ ∧ P.Runs v r t₂ ∧ out = .cons r s := by
  unfold pushProg Runs at h
  cases h with
  | @let_ _ _ _ v _ t₁ _ h₁ h₂ =>
    cases h₂ with
    | @let_ _ _ _ r _ _ _ h₃ h₄ =>
      cases h₃ with
      | @let_ _ _ _ w _ _ t₂ h₅ h₆ =>
        cases h₅
        cases h₄ with
        | cons h₇ h₈ =>
          cases h₇
          cases h₈
          exact ⟨v, r, t₁, t₂, h₁,
            Eval.of_append_of_wellScoped (env := [v]) (extra := [v, s]) h₆ hP, rfl⟩

end Prog

namespace PolyTimeFun

open Data Polynomial

/-! ## Steps, as polynomial-time functions -/

/-- **A step followed by the rest**: running `pushProg F P` and then `Q` from the state `s` is
running `P` on `F s`, to some output `r`, and `Q` on the new state `(r, s)`. -/
theorem pushSeq_iff {σ τ : Type*} [SizedEncoding σ] [SizedEncoding τ] (F : PolyTimeFun σ τ)
    {P Q : Prog} (hP : P.WellScoped 1) (hQ : Q.WellScoped 1) (s : σ) (out : Data) :
    (∃ t, (seqProg (Prog.pushProg F.code P) Q).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, P.Runs (encode (F s)) r t) ∧
        ∃ t, Q.Runs (encode ((r, s) : Data × σ)) out t := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨y, t₁, t₂, h₁, h₂⟩ := seqProg_inv hQ h
    obtain ⟨v, r, u₁, u₂, hF, hPr, rfl⟩ := Prog.pushProg_inv hP h₁
    obtain ⟨u, -, hF'⟩ := F.computes s
    obtain ⟨rfl, -⟩ := Eval.deterministic hF hF'
    exact ⟨r, ⟨u₂, hPr⟩, t₂, h₂⟩
  · rintro ⟨r, ⟨t₁, hPr⟩, t₂, hQr⟩
    obtain ⟨u, -, hF⟩ := F.computes s
    obtain ⟨t₃, h₃⟩ := Prog.pushProg_runs hP hF hPr
    exact ⟨_, seqProg_runs hQ h₃ hQr⟩

/-- A polynomial-time decision accepts exactly when it is `true`. -/
theorem runs_true_iff {σ : Type*} [SizedEncoding σ] (C : PolyTimeFun σ Bool) (s : σ) :
    (∃ t, C.code.Runs (encode s) (encode true) t) ↔ C s = true := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨u, -, h'⟩ := C.computes s
    obtain ⟨e, -⟩ := Eval.deterministic h h'
    cases hC : C s
    · rw [hC] at e; exact absurd e (by decide)
    · rfl
  · intro hC
    obtain ⟨u, -, h'⟩ := C.computes s
    exact ⟨u, hC ▸ h'⟩

/-! ## Reading data, as programs -/

/-- Every datum encodes its spineList. -/
noncomputable def spineF : PolyTimeFun Data (List Data) :=
  ofEncodeEq spineList fun d => ofList_id_spineList d

/-- A datum read as a bit. -/
noncomputable def bitDF : PolyTimeFun Data Bool where
  toFun := bitD
  code := .elim 0 .nil (.const (.cons .nil .nil))
  closed := by simp [Prog.WellScoped]
  timeBound := 4
  computes d := by
    cases d with
    | nil => exact ⟨2, by simp, Eval.elim_nil rfl (Eval.nil _)⟩
    | cons a b => exact ⟨4, by simp, Eval.elim_cons rfl (Eval.const _ _)⟩

/-- A datum read as a list of bit strings. -/
noncomputable def bitsListF : PolyTimeFun Data (List BitStr) :=
  (map ((map bitDF).comp spineF)).comp spineF

@[simp] theorem bitsListF_apply (d : Data) : bitsListF d = bitsListD d := rfl

/-- A datum read as a length in unary. -/
noncomputable def lenUnaryF : PolyTimeFun Data Unary := length.comp spineF

@[simp] theorem lenUnaryF_apply (d : Data) : lenUnaryF d = unary (spineList d).length := rfl

/-- A datum read as a length, written as that many `false`s. -/
noncomputable def lenBitsF : PolyTimeFun Data BitStr := (map (const false)).comp spineF

@[simp] theorem lenBitsF_apply (d : Data) : lenBitsF d = (spineList d).map fun _ => false := rfl

/-- A bit string's length, written as that many `false`s. -/
noncomputable def falsesF : PolyTimeFun BitStr BitStr := map (const false)

@[simp] theorem falsesF_apply (a : BitStr) : falsesF a = a.map fun _ => false := rfl

end PolyTimeFun

end MIPRE.Cost

namespace MIPRE.Tailored

open Cost Cost.PolyTimeFun Cost.Data Polynomial

/-! ## One linear constraint, and all of them -/

theorem map_false_eq_iff {α β : Type*} (a : List α) (b : List β) :
    (a.map fun _ => false) = (b.map fun _ => false) ↔ a.length = b.length := by
  constructor
  · intro h; simpa using congrArg List.length h
  · intro h
    induction a generalizing b with
    | nil => cases b with
      | nil => rfl
      | cons _ _ => simp at h
    | cons x a ih => cases b with
      | nil => simp at h
      | cons y b =>
        simp only [List.map_cons, List.length_cons, Nat.add_right_cancel_iff, List.cons.injEq,
          true_and] at h ⊢
        exact ih b h

/-- The parity of the number of common ones is the parity dot product of
`LowDegree.BinaryLinear`. -/
theorem even_count_zipWith_iff (c v : BitStr) :
    Even ((List.zipWith (· && ·) c v).count true) ↔
      LowDegree.BinaryLinear.dotBits c v = false := by
  have key : ∀ (c v : BitStr) (acc : Bool),
      (List.zip c v).foldl LowDegree.BinaryLinear.dotStep acc =
        xor acc (decide (Odd ((List.zipWith (· && ·) c v).count true))) := by
    intro c v
    induction c generalizing v with
    | nil => intro acc; simp
    | cons x c ih =>
      intro acc
      cases v with
      | nil => simp
      | cons y v =>
        rw [List.zip_cons_cons, List.foldl_cons, ih, List.zipWith_cons_cons, List.count_cons]
        simp only [LowDegree.BinaryLinear.dotStep]
        cases hxy : (x && y)
        · simp
        · simp only [beq_self_eq_true, ite_true, Nat.odd_add_one, decide_not]
          cases acc <;> simp
  rw [LowDegree.BinaryLinear.dotBits, key, Bool.false_xor, decide_eq_false_iff_not,
    Nat.not_odd_iff_even]

/-- One constraint: `c` and `v` have the same length and `⟨c, v⟩ = 0`. -/
noncomputable def satF : PolyTimeFun (BitStr × BitStr) Bool :=
  congr (SAT.andProg.comp
      ((SAT.ArrayProg.eqBits.comp ((falsesF.comp fst).pair (falsesF.comp snd))).pair
        (SAT.notBoolP.comp LowDegree.BinaryLinear.dotBitsProg)))
    (fun p => decide (Satisfies p.1 p.2)) (by
      rintro ⟨c, v⟩
      simp only [comp_apply, SAT.andProg, congr_apply, pair_apply, SAT.ArrayProg.eqBits_apply,
        falsesF_apply, fst_apply, snd_apply, SAT.notBoolP_apply,
        LowDegree.BinaryLinear.dotBitsProg_apply]
      unfold Satisfies
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', map_false_eq_iff,
        even_count_zipWith_iff])

@[simp] theorem satF_apply (p : BitStr × BitStr) : satF p = decide (Satisfies p.1 p.2) := rfl

/-- The step of `allSatF`: conjoin one more constraint, keeping the vector. -/
noncomputable def allSatStep : PolyTimeFun ((Bool × BitStr) × BitStr) (Bool × BitStr) :=
  (SAT.andProg.comp ((fst.comp fst).pair (satF.comp (snd.pair (snd.comp fst))))).pair (snd.comp fst)

@[simp] theorem allSatStep_apply (s : Bool × BitStr) (c : BitStr) :
    allSatStep (s, c) = (s.1 && decide (Satisfies c s.2), s.2) := rfl

theorem esize_allSatStep (s : Bool × BitStr) (c : BitStr) :
    esize (allSatStep (s, c)) ≤ esize s + (2 : Polynomial ℕ).eval (esize c) := by
  obtain ⟨b, v⟩ := s
  rw [allSatStep_apply]
  simp only [esize_prod, Polynomial.eval_ofNat]
  have h1 : ∀ b : Bool, esize b ≤ 3 := fun b => by cases b <;> decide
  have h2 : ∀ b : Bool, 1 ≤ esize b := fun b => by cases b <;> decide
  have := h1 (b && decide (Satisfies c v))
  have := h2 b
  omega

theorem foldl_allSatStep (cs : List BitStr) (b : Bool) (v : BitStr) :
    cs.foldl (fun s c => allSatStep (s, c)) (b, v) =
      (b && cs.all fun c => decide (Satisfies c v), v) := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih => rw [List.foldl_cons, allSatStep_apply, ih]; simp [Bool.and_assoc]

/-- All constraints of a list are satisfied by `v`. -/
noncomputable def allSatF : PolyTimeFun (List BitStr × BitStr) Bool :=
  congr (fst.comp ((foldlAdd allSatStep 2 esize_allSatStep).comp
      (fst.pair ((const true).pair snd))))
    (fun p => decide (∀ c ∈ p.1, Satisfies c p.2)) (by
      rintro ⟨cs, v⟩
      change (cs.foldl (fun s c => allSatStep (s, c)) (true, v)).1 = _
      rw [foldl_allSatStep, Bool.true_and, List.all_eq]
      exact decide_eq_decide.2 (by simp))

@[simp] theorem allSatF_apply (p : List BitStr × BitStr) :
    allSatF p = decide (∀ c ∈ p.1, Satisfies c p.2) := rfl

/-! ## The canonical decider -/

/-- The input of a decider, `(n, x, y, a, b)`. -/
abbrev DIn := ℕ × BitStr × BitStr × BitStr × BitStr

/-- The input of the first run of `L`, `(n, x, false)`. -/
noncomputable def canonIn₁ : PolyTimeFun DIn (ℕ × BitStr × Bool) :=
  fst.pair ((fst.comp snd).pair (const false))

/-- The input of the second run of `L`, `(n, x, true)`. -/
noncomputable def canonIn₂ : PolyTimeFun (Data × DIn) (ℕ × BitStr × Bool) :=
  (fst.pair ((fst.comp snd).pair (const true))).comp snd

/-- The input of the third run of `L`, `(n, y, false)`. -/
noncomputable def canonIn₃ : PolyTimeFun (Data × Data × DIn) (ℕ × BitStr × Bool) :=
  (fst.pair ((fst.comp (snd.comp snd)).pair (const false))).comp (snd.comp snd)

/-- The input of the fourth run of `L`, `(n, y, true)`. -/
noncomputable def canonIn₄ : PolyTimeFun (Data × Data × Data × DIn) (ℕ × BitStr × Bool) :=
  (fst.pair ((fst.comp (snd.comp snd)).pair (const true))).comp (snd.comp (snd.comp snd))

/-- The input of the run of `LP`: `(n, x, y, a^R, b^R)`, the readable parts cut at the lengths
the first and the third run of `L` wrote. -/
noncomputable def canonIn₅ : PolyTimeFun (Data × Data × Data × Data × DIn) DIn :=
  let i : PolyTimeFun (Data × Data × Data × Data × DIn) DIn := snd.comp (snd.comp (snd.comp snd))
  (fst.comp i).pair ((fst.comp (snd.comp i)).pair ((fst.comp (snd.comp (snd.comp i))).pair
    ((take.comp ((fst.comp (snd.comp (snd.comp (snd.comp i)))).pair
        (lenUnaryF.comp (fst.comp (snd.comp (snd.comp snd)))))).pair
      (take.comp ((snd.comp (snd.comp (snd.comp (snd.comp i)))).pair
        (lenUnaryF.comp (fst.comp snd)))))))

/-- The final check, on the five outputs and the input. -/
noncomputable def canonFinal : PolyTimeFun (Data × Data × Data × Data × Data × DIn) Bool :=
  let i : PolyTimeFun (Data × Data × Data × Data × Data × DIn) DIn :=
    snd.comp (snd.comp (snd.comp (snd.comp snd)))
  let a : PolyTimeFun (Data × Data × Data × Data × Data × DIn) BitStr :=
    fst.comp (snd.comp (snd.comp (snd.comp i)))
  let b : PolyTimeFun (Data × Data × Data × Data × Data × DIn) BitStr :=
    snd.comp (snd.comp (snd.comp (snd.comp i)))
  let r : ℕ → PolyTimeFun (Data × Data × Data × Data × Data × DIn) Data := fun k =>
    match k with
    | 0 => fst
    | 1 => fst.comp snd
    | 2 => fst.comp (snd.comp snd)
    | 3 => fst.comp (snd.comp (snd.comp snd))
    | _ => fst.comp (snd.comp (snd.comp (snd.comp snd)))
  SAT.andProg.comp ((SAT.ArrayProg.eqBits.comp ((falsesF.comp a).pair
      (append.comp ((lenBitsF.comp (r 4)).pair (lenBitsF.comp (r 3)))))).pair
    (SAT.andProg.comp ((SAT.ArrayProg.eqBits.comp ((falsesF.comp b).pair
        (append.comp ((lenBitsF.comp (r 2)).pair (lenBitsF.comp (r 1)))))).pair
      (allSatF.comp ((bitsListF.comp (r 0)).pair
        (append.comp ((append.comp (a.pair b)).pair (const [true]))))))))

/-- The canonical decider after the fourth run of `L`: run `LP`, then check. -/
noncomputable def canonTail₄ (P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₅.code P) canonFinal.code

/-- After the third run of `L`. -/
noncomputable def canonTail₃ (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₄.code L) (canonTail₄ P)

/-- After the second run of `L`. -/
noncomputable def canonTail₂ (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₃.code L) (canonTail₃ L P)

/-- After the first run of `L`. -/
noncomputable def canonTail₁ (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₂.code L) (canonTail₂ L P)

/-- **The canonical decider** of a tailored verifier with answer-length calculator `L` and
linear-constraints processor `P` (II:1757–1787), on `encode (n, x, y, a, b)`: four runs of `L`,
one of `P`, and the final check, in sequence. -/
noncomputable def canonProg (L P : Prog) : Prog :=
  seqProg (Prog.pushProg canonIn₁.code L) (canonTail₁ L P)

section WellScoped

variable {L P : Prog} (hL : L.WellScoped 1) (hP : P.WellScoped 1)
include hP

theorem canonTail₄_wellScoped : (canonTail₄ P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₅.closed hP) canonFinal.closed

include hL

theorem canonTail₃_wellScoped : (canonTail₃ L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₄.closed hL)
    (canonTail₄_wellScoped hP)

theorem canonTail₂_wellScoped : (canonTail₂ L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₃.closed hL)
    (canonTail₃_wellScoped hL hP)

theorem canonTail₁_wellScoped : (canonTail₁ L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₂.closed hL)
    (canonTail₂_wellScoped hL hP)

theorem canonProg_wellScoped : (canonProg L P).WellScoped 1 :=
  seqProg_closed (Prog.pushProg_wellScoped canonIn₁.closed hL)
    (canonTail₁_wellScoped hL hP)

end WellScoped

@[simp] theorem canonIn₁_apply (i : DIn) : canonIn₁ i = (i.1, i.2.1, false) := rfl

@[simp] theorem canonIn₂_apply (r : Data) (i : DIn) : canonIn₂ (r, i) = (i.1, i.2.1, true) := rfl

@[simp] theorem canonIn₃_apply (r r' : Data) (i : DIn) :
    canonIn₃ (r, r', i) = (i.1, i.2.2.1, false) := rfl

@[simp] theorem canonIn₄_apply (r r' r'' : Data) (i : DIn) :
    canonIn₄ (r, r', r'', i) = (i.1, i.2.2.1, true) := rfl

@[simp] theorem canonIn₅_apply (r₄ r₃ r₂ r₁ : Data) (i : DIn) :
    canonIn₅ (r₄, r₃, r₂, r₁, i) =
      (i.1, i.2.1, i.2.2.1, i.2.2.2.1.take (spineList r₁).length,
        i.2.2.2.2.take (spineList r₃).length) := by
  simp [canonIn₅]

/-- The final check, read: the two lengths, and every constraint. -/
theorem canonFinal_apply (r₀ r₁ r₂ r₃ r₄ : Data) (i : DIn) :
    canonFinal (r₀, r₁, r₂, r₃, r₄, i) =
      (decide (i.2.2.2.1.length = (spineList r₄).length + (spineList r₃).length) &&
        (decide (i.2.2.2.2.length = (spineList r₂).length + (spineList r₁).length) &&
          decide (∀ c ∈ bitsListD r₀, Satisfies c (i.2.2.2.1 ++ i.2.2.2.2 ++ [true])))) := by
  have hlen : ∀ (a : BitStr) (l₁ l₂ : List Data),
      decide ((a.map fun _ => false) = (l₁.map fun _ => false) ++ (l₂.map fun _ => false)) =
        decide (a.length = l₁.length + l₂.length) := by
    intro a l₁ l₂
    rw [← List.map_append]
    exact decide_eq_decide.2 ((map_false_eq_iff a (l₁ ++ l₂)).trans (by simp))
  simp only [canonFinal, comp_apply, pair_apply, fst_apply, snd_apply, const_apply, SAT.andProg,
    congr_apply, SAT.ArrayProg.eqBits_apply, falsesF_apply, append_apply, lenBitsF_apply,
    allSatF_apply,
    bitsListF_apply, hlen]

/-- **The canonical decider accepts exactly when the five runs halt and the check passes.** -/
theorem canonProg_accepts {L P : Prog} (hL : L.WellScoped 1) (hP : P.WellScoped 1) (i : DIn) :
    (∃ t, (canonProg L P).Runs (encode i) (encode true) t) ↔
      ∃ r₁ r₂ r₃ r₄ r₀ : Data,
        (∃ t, L.Runs (encode (i.1, i.2.1, false)) r₁ t) ∧
        (∃ t, L.Runs (encode (i.1, i.2.1, true)) r₂ t) ∧
        (∃ t, L.Runs (encode (i.1, i.2.2.1, false)) r₃ t) ∧
        (∃ t, L.Runs (encode (i.1, i.2.2.1, true)) r₄ t) ∧
        (∃ t, P.Runs (encode (i.1, i.2.1, i.2.2.1, i.2.2.2.1.take (spineList r₁).length,
          i.2.2.2.2.take (spineList r₃).length)) r₀ t) ∧
        i.2.2.2.1.length = (spineList r₁).length + (spineList r₂).length ∧
        i.2.2.2.2.length = (spineList r₃).length + (spineList r₄).length ∧
        ∀ c ∈ bitsListD r₀, Satisfies c (i.2.2.2.1 ++ i.2.2.2.2 ++ [true]) := by
  have e₁ : ∀ (s : DIn) (out : Data), (∃ t, (canonProg L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₁ s)) r t) ∧
        ∃ t, (canonTail₁ L P).Runs (encode ((r, s) : Data × DIn)) out t :=
    pushSeq_iff canonIn₁ hL (canonTail₁_wellScoped hL hP)
  have e₂ : ∀ (s : Data × DIn) (out : Data), (∃ t, (canonTail₁ L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₂ s)) r t) ∧
        ∃ t, (canonTail₂ L P).Runs (encode ((r, s) : Data × Data × DIn)) out t :=
    pushSeq_iff canonIn₂ hL (canonTail₂_wellScoped hL hP)
  have e₃ : ∀ (s : Data × Data × DIn) (out : Data),
      (∃ t, (canonTail₂ L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₃ s)) r t) ∧
        ∃ t, (canonTail₃ L P).Runs (encode ((r, s) : Data × Data × Data × DIn)) out t :=
    pushSeq_iff canonIn₃ hL (canonTail₃_wellScoped hL hP)
  have e₄ : ∀ (s : Data × Data × Data × DIn) (out : Data),
      (∃ t, (canonTail₃ L P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, L.Runs (encode (canonIn₄ s)) r t) ∧
        ∃ t, (canonTail₄ P).Runs (encode ((r, s) : Data × Data × Data × Data × DIn)) out t :=
    pushSeq_iff canonIn₄ hL (canonTail₄_wellScoped hP)
  have e₅ : ∀ (s : Data × Data × Data × Data × DIn) (out : Data),
      (∃ t, (canonTail₄ P).Runs (encode s) out t) ↔
      ∃ r : Data, (∃ t, P.Runs (encode (canonIn₅ s)) r t) ∧
        ∃ t, canonFinal.code.Runs (encode ((r, s) : Data × Data × Data × Data × Data × DIn))
          out t :=
    pushSeq_iff canonIn₅ hP canonFinal.closed
  simp only [e₁, e₂, e₃, e₄, e₅, runs_true_iff, canonIn₁_apply, canonIn₂_apply, canonIn₃_apply,
    canonIn₄_apply, canonIn₅_apply, canonFinal_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨r₁, h₁, r₂, h₂, r₃, h₃, r₄, h₄, r₀, h₅, ha, hb, hs⟩
    exact ⟨r₁, r₂, r₃, r₄, r₀, h₁, h₂, h₃, h₄, h₅, ha, hb, hs⟩
  · rintro ⟨r₁, r₂, r₃, r₄, r₀, h₁, h₂, h₃, h₄, h₅, ha, hb, hs⟩
    exact ⟨r₁, h₁, r₂, h₂, r₃, h₃, r₄, h₄, r₀, h₅, ha, hb, hs⟩

end MIPRE.Tailored

end
