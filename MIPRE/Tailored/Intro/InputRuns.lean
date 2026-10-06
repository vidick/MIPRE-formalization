/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Introspection.ClockedQueryProgram
public import MIPRE.Foundations.CL.DetypingClock
public import MIPRE.Foundations.Introspection.SourceDescriptionCompiler
public import MIPRE.Foundations.Introspection.Runtime
public import MIPRE.Tailored.OfTNFV
public import MIPRE.Tailored.Repeat.LpProg

@[expose] public section

/-!
# Running the input's calculator and processor on a clamped description and a clock

The linear-constraints processor of the tailored introspection verifier (issue #281, P3e) needs,
at index `m = 2^n`, the input's answer lengths `T.lenOf m q κ` (to split the input's answers in
the padded layout) and its constraints `T.consOf m qx qy aR bR` (the source check). Its own
description must have size `≤ C (λ + 1)^C` whatever the input, so the input's programs cannot be
embedded as they are. This module does what `MIPRE.Introspection.seven` does for normal form
verifiers:

* `clamp`, on `((S, L, P), λ)`, replaces every program of size above `λ` by `Prog.nil`
  (`SourceDescriptionCompiler.clampProgram`, applied three times), keeping `λ`. It is the
  identity on the programs of a `λ`-bounded verifier (`clamp_bounded`), and its output has size
  at most `19 (λ + 1)` whatever the input (`clamp_size`).
* `runLen U` and `runLp U` take a unary clock, a program description *as data*, and the
  arguments, and run the program through the clocked universal machine `U`
  (`ClockedQuery.run`, as `ClockedSourceChecks` does): `runLen` reads the output as a length
  (its spine, as `LenIs` does, and `0` on a timeout, as `lenOf` does when `len` diverges),
  `runLp` as a constraint list (`bitsListD`, as `LpIs` does, and the rejecting list
  `[rejectConstraint 0]` on a timeout, a timeout being a rejection).
* `lenRun U` and `lpRun U` read the program from the clamped metadata `((S, L, P), λ)`, as the
  decision kernel of `seven` reads its source decider from `DecisionPreparation.Metadata`.

Correctness (`runLen_eq`, `runLp_eq`, `lenRun_clamp`, `lpRun_clamp`): for a `λ`-bounded `T`,
`m ≥ 2`, and a clock of length at least the running-time bound `IsBounded` gives,
`m^λ (|args| + 1)^λ`, the runs compute `T.lenOf m q κ` and `T.consOf m qx qy aR bR` exactly.
At `m = 2^n`, `n ≥ 1`, with questions and readable answers of length at most `(2^n)^λ`, the
clock `ansBound 5 λ n = 2^{(λn + 1)^5}` that `seven` computes suffices (`len_clock_le`,
`lp_clock_le`; `lenRun_seven`, `lpRun_seven`), and any clock at least as long
(`ansBound_mono`).
-/

namespace MIPRE.Tailored

open Cost

namespace TailoredVerifier

/-- A `λ`-bounded tailored verifier has `λ ≥ 2`: every program has size at least `2`. -/
theorem IsBounded.two_le {ℓ lam : ℕ} {T : TailoredVerifier ℓ} (h : T.IsBounded lam) :
    2 ≤ lam :=
  le_trans (le_trans (Cost.Prog.two_le_esize T.sampler.prog) (le_max_left _ _)) h.2

end TailoredVerifier

namespace Intro.InputRuns

open Cost.Data Cost.PolyTimeFun MIPRE.Introspection CL.Detyping.Program

/-- The stored description of the input: its three programs and the parameter `λ`. -/
abbrev Metadata : Type := (Prog × Prog × Prog) × ℕ

/-- The arguments of the answer-length calculator: `(m, q, κ)`. -/
abbrev LenArgs : Type := ℕ × BitStr × Bool

/-- The arguments of the linear-constraints processor: `(m, qx, qy, aR, bR)`. -/
abbrev LpArgs : Type := ℕ × BitStr × BitStr × BitStr × BitStr

/-! ## Clamping the description -/

/-- Clamp the three programs independently to size `λ`, keeping `λ`. -/
noncomputable def clamp : PolyTimeFun Metadata Metadata :=
  ((SourceDescriptionCompiler.clampProgram.comp ((fst.comp fst).pair snd)).pair
    ((SourceDescriptionCompiler.clampProgram.comp ((fst.comp (snd.comp fst)).pair snd)).pair
      (SourceDescriptionCompiler.clampProgram.comp ((snd.comp (snd.comp fst)).pair snd)))).pair
    snd

@[simp] theorem clamp_apply (S L P : Prog) (lam : ℕ) :
    clamp ((S, L, P), lam) = ((SourceDescriptionCompiler.clampProgram (S, lam),
      SourceDescriptionCompiler.clampProgram (L, lam),
      SourceDescriptionCompiler.clampProgram (P, lam)), lam) := rfl

theorem clamp_eq_self (S L P : Prog) (lam : ℕ) (hS : esize S ≤ lam) (hL : esize L ≤ lam)
    (hP : esize P ≤ lam) : clamp ((S, L, P), lam) = ((S, L, P), lam) := by
  simp [hS, hL, hP]

/-- **The clamp is the identity on a `λ`-bounded verifier's programs.** -/
theorem clamp_bounded {ℓ lam : ℕ} (T : TailoredVerifier ℓ) (hT : T.IsBounded lam) :
    clamp (T.progs, lam) = (T.progs, lam) := by
  have h := hT.2
  simp only [TailoredVerifier.size] at h
  exact clamp_eq_self _ _ _ _ ((le_max_left _ _).trans h)
    ((le_max_left _ _).trans ((le_max_right _ _).trans h))
    ((le_max_right _ _).trans ((le_max_right _ _).trans h))

/-- Otherwise each program is kept or replaced by `Prog.nil`: nothing else enters. -/
theorem clampProgram_eq_or (p : Prog) (lam : ℕ) :
    SourceDescriptionCompiler.clampProgram (p, lam) = p ∨
      SourceDescriptionCompiler.clampProgram (p, lam) = Prog.nil := by
  rw [SourceDescriptionCompiler.clampProgram_apply]
  split_ifs <;> simp

/-- The clamped description has size linear in `λ + 1`, whatever the input. -/
theorem clamp_size (V : Prog × Prog × Prog) (lam : ℕ) :
    esize (clamp (V, lam)) ≤ 19 * (lam + 1) := by
  obtain ⟨S, L, P⟩ := V
  have hS := SourceDescriptionCompiler.clampProgram_size S lam
  have hL := SourceDescriptionCompiler.clampProgram_size L lam
  have hP := SourceDescriptionCompiler.clampProgram_size P lam
  have hn : Nat.size lam ≤ lam := Nat.size_le.mpr Nat.lt_two_pow_self
  have hl := esize_nat_le lam
  rw [clamp_apply, esize_prod, esize_prod, esize_prod]
  omega

/-- The clamped answer-length calculator. -/
noncomputable def lenProgOf : PolyTimeFun Metadata Prog := fst.comp (snd.comp fst)

/-- The clamped linear-constraints processor. -/
noncomputable def lpProgOf : PolyTimeFun Metadata Prog := snd.comp (snd.comp fst)

@[simp] theorem lenProgOf_apply (S L P : Prog) (lam : ℕ) :
    lenProgOf ((S, L, P), lam) = L := rfl

@[simp] theorem lpProgOf_apply (S L P : Prog) (lam : ℕ) :
    lpProgOf ((S, L, P), lam) = P := rfl

/-! ## The clocked runs -/

variable (U : ClockedUniversalMachine)

/-- Run a stored program on encoded arguments, for at most the clock's length. -/
noncomputable def runOn {α : Type*} [SizedEncoding α] : PolyTimeFun (Unary × Prog × α) Data :=
  (ClockedQuery.run U).comp (fst.pair ((fst.comp snd).pair (encoded.comp (snd.comp snd))))

@[simp] theorem runOn_apply {α : Type*} [SizedEncoding α] (c : Unary) (p : Prog) (a : α) :
    runOn U (c, p, a) = clockedResult p (encode a) c.length := rfl

/-- An in-budget run is read back with its success tag. -/
theorem runOn_of_runs {α : Type*} [SizedEncoding α] {c : Unary} {p : Prog} {a : α} {r : Data}
    {t : ℕ} (ht : t ≤ c.length) (h : p.Runs (encode a) r t) :
    runOn U (c, p, a) = .cons (encode true) r := by
  rw [runOn_apply, CL.Detyping.ClockProgram.clockedResult_eq_iff]
  exact ⟨t, ht, h⟩

/-- A clocked result read as a length: the spine of the result, `0` on a timeout. -/
noncomputable def lenRead : PolyTimeFun Data ℕ :=
  unaryToBin.comp (length.comp ((ofEncodeEq rawList encode_rawList).comp treeTail))

theorem lenRead_apply (d : Data) : lenRead d = (spineList (treeTail d)).length := by
  simp [lenRead, RepProg.rawList_eq_spineList]

theorem lenRead_cons (a d : Data) : lenRead (.cons a d) = (spineList d).length := by
  rw [lenRead_apply, treeTail_cons]

theorem lenRead_nil : lenRead .nil = 0 := by
  rw [lenRead_apply]
  rfl

/-- A clocked result read as a constraint list: `bitsListD` of the result, and the rejecting
list on a timeout. -/
noncomputable def lpRead : PolyTimeFun Data (List BitStr) :=
  ite rawTruthProg (RepProg.bitsListDF.comp treeTail) (const [rejectConstraint 0])

theorem lpRead_cons (a d : Data) : lpRead (.cons a d) = bitsListD d := rfl

theorem lpRead_nil : lpRead .nil = [rejectConstraint 0] := rfl

/-- **The clocked answer-length calculator**, on `(clock, L, (m, q, κ))`. -/
noncomputable def runLen : PolyTimeFun (Unary × Prog × LenArgs) ℕ := lenRead.comp (runOn U)

/-- **The clocked linear-constraints processor**, on `(clock, P, (m, qx, qy, aR, bR))`. -/
noncomputable def runLp : PolyTimeFun (Unary × Prog × LpArgs) (List BitStr) :=
  lpRead.comp (runOn U)

theorem runLen_apply (c : Unary) (L : Prog) (a : LenArgs) :
    runLen U (c, L, a) = lenRead (clockedResult L (encode a) c.length) := rfl

theorem runLp_apply (c : Unary) (P : Prog) (a : LpArgs) :
    runLp U (c, P, a) = lpRead (clockedResult P (encode a) c.length) := rfl

/-- On a timeout, the length read is `0` and the constraint list rejects. -/
theorem runLen_timeout {c : Unary} {L : Prog} {a : LenArgs}
    (h : ¬∃ r t, t ≤ c.length ∧ L.Runs (encode a) r t) : runLen U (c, L, a) = 0 := by
  have hn : evalWithin L (encode a) c.length = none := by
    rw [← Option.not_isSome_iff_eq_none, evalWithin_isSome_iff]
    exact h
  rw [runLen_apply, clockedResult, hn]
  exact lenRead_nil

theorem runLp_timeout {c : Unary} {P : Prog} {a : LpArgs}
    (h : ¬∃ r t, t ≤ c.length ∧ P.Runs (encode a) r t) :
    runLp U (c, P, a) = [rejectConstraint 0] := by
  have hn : evalWithin P (encode a) c.length = none := by
    rw [← Option.not_isSome_iff_eq_none, evalWithin_isSome_iff]
    exact h
  rw [runLp_apply, clockedResult, hn]
  exact lpRead_nil

theorem runLen_of_runs {c : Unary} {L : Prog} {a : LenArgs} {r : Data} {t : ℕ}
    (ht : t ≤ c.length) (h : L.Runs (encode a) r t) :
    runLen U (c, L, a) = (spineList r).length := by
  change lenRead (runOn U (c, L, a)) = _
  rw [runOn_of_runs U ht h, lenRead_cons]

theorem runLp_of_runs {c : Unary} {P : Prog} {a : LpArgs} {r : Data} {t : ℕ}
    (ht : t ≤ c.length) (h : P.Runs (encode a) r t) : runLp U (c, P, a) = bitsListD r := by
  change lpRead (runOn U (c, P, a)) = _
  rw [runOn_of_runs U ht h, lpRead_cons]

/-! ## Correctness for a bounded input -/

variable {ℓ lam m : ℕ} (T : TailoredVerifier ℓ)

/-- **The clocked calculator computes `lenOf`** for a `λ`-bounded input at an index `m ≥ 2`,
when the clock covers the input's running-time bound `m^λ (|(q, κ)| + 1)^λ`. -/
theorem runLen_eq (hT : T.IsBounded lam) (hm : 2 ≤ m) (q : BitStr) (κ : Bool) {c : Unary}
    (hc : m ^ lam * (esize (q, κ) + 1) ^ lam ≤ c.length) :
    runLen U (c, T.len.prog, (m, q, κ)) = T.lenOf m q κ := by
  obtain ⟨r, t, ht, h⟩ := (hT.1 m hm).2.2.1 (encode (q, κ))
  have h' : T.len.prog.Runs (encode (m, q, κ)) r t := h
  rw [runLen_of_runs U (ht.trans hc) h', T.lenOf_eq h']

/-- A bounded input's calculator halts at every question of an index `m ≥ 2`. -/
theorem lenDefined (hT : T.IsBounded lam) (hm : 2 ≤ m) (q : BitStr) : T.LenDefined m q := by
  intro κ
  obtain ⟨r, t, -, h⟩ := (hT.1 m hm).2.2.1 (encode (q, κ))
  exact ⟨_, t, r, h, rfl⟩

/-- **The clocked processor computes `consOf`** for a `λ`-bounded input at an index `m ≥ 2`,
when the clock covers the input's running-time bound `m^λ (|(qx, qy, aR, bR)| + 1)^λ`. -/
theorem runLp_eq (hT : T.IsBounded lam) (hm : 2 ≤ m) (qx qy aR bR : BitStr) {c : Unary}
    (hc : m ^ lam * (esize (qx, qy, aR, bR) + 1) ^ lam ≤ c.length) :
    runLp U (c, T.lp.prog, (m, qx, qy, aR, bR)) = T.consOf m qx qy aR bR := by
  obtain ⟨r, t, ht, h⟩ := (hT.1 m hm).2.2.2.1 (encode (qx, qy, aR, bR))
  have h' : T.lp.prog.Runs (encode (m, qx, qy, aR, bR)) r t := h
  rw [runLp_of_runs U (ht.trans hc) h',
    T.consOf_eq_of (lenDefined T hT hm qx) (lenDefined T hT hm qy) ⟨t, r, h', rfl⟩]

/-! ## Reading the program from the clamped description -/

/-- The calculator run, its program read from the description `((S, L, P), λ)`. -/
noncomputable def lenRun : PolyTimeFun (Unary × Metadata × LenArgs) ℕ :=
  (runLen U).comp (fst.pair ((lenProgOf.comp (fst.comp snd)).pair (snd.comp snd)))

/-- The processor run, its program read from the description `((S, L, P), λ)`. -/
noncomputable def lpRun : PolyTimeFun (Unary × Metadata × LpArgs) (List BitStr) :=
  (runLp U).comp (fst.pair ((lpProgOf.comp (fst.comp snd)).pair (snd.comp snd)))

@[simp] theorem lenRun_apply (c : Unary) (M : Metadata) (a : LenArgs) :
    lenRun U (c, M, a) = runLen U (c, M.1.2.1, a) := rfl

@[simp] theorem lpRun_apply (c : Unary) (M : Metadata) (a : LpArgs) :
    lpRun U (c, M, a) = runLp U (c, M.1.2.2, a) := rfl

/-- **`lenOf` from the clamped description**, for a `λ`-bounded input. -/
theorem lenRun_clamp (hT : T.IsBounded lam) (hm : 2 ≤ m) (q : BitStr) (κ : Bool) {c : Unary}
    (hc : m ^ lam * (esize (q, κ) + 1) ^ lam ≤ c.length) :
    lenRun U (c, clamp (T.progs, lam), (m, q, κ)) = T.lenOf m q κ := by
  rw [lenRun_apply, clamp_bounded T hT]
  exact runLen_eq U T hT hm q κ hc

/-- **`consOf` from the clamped description**, for a `λ`-bounded input. -/
theorem lpRun_clamp (hT : T.IsBounded lam) (hm : 2 ≤ m) (qx qy aR bR : BitStr) {c : Unary}
    (hc : m ^ lam * (esize (qx, qy, aR, bR) + 1) ^ lam ≤ c.length) :
    lpRun U (c, clamp (T.progs, lam), (m, qx, qy, aR, bR)) = T.consOf m qx qy aR bR := by
  rw [lpRun_apply, clamp_bounded T hT]
  exact runLp_eq U T hT hm qx qy aR bR hc

/-! ## The clock at `m = 2^n` -/

/-- The introspection clock grows with its exponent and its parameter. -/
theorem ansBound_mono {k k' lam lam' : ℕ} (n : ℕ) (hk : k ≤ k') (hl : lam ≤ lam') :
    ansBound k lam n ≤ ansBound k' lam' n := by
  apply Nat.pow_le_pow_right (by decide)
  calc (lam * n + 1) ^ k ≤ (lam' * n + 1) ^ k :=
        Nat.pow_le_pow_left (by have := Nat.mul_le_mul_right n hl; omega) k
    _ ≤ (lam' * n + 1) ^ k' := Nat.pow_le_pow_right (by omega) hk

/-- The processor's running-time bound at `2^n`, on questions and readable answers of length at
most `(2^n)^λ`, is within `seven`'s clock `2^{(λn + 1)^5}`. -/
theorem lp_clock_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (qx qy aR bR : BitStr)
    (hx : qx.length ≤ (2 ^ n) ^ lam) (hy : qy.length ≤ (2 ^ n) ^ lam)
    (ha : aR.length ≤ (2 ^ n) ^ lam) (hb : bR.length ≤ (2 ^ n) ^ lam) :
    (2 ^ n) ^ lam * (esize (qx, qy, aR, bR) + 1) ^ lam ≤ ansBound 5 lam n :=
  legal_query_cost_le hl hn qx qy aR bR hx hy ha hb

/-- The calculator's running-time bound at `2^n`, on a question of length at most `(2^n)^λ`, is
within the same clock. -/
theorem len_clock_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (q : BitStr) (κ : Bool)
    (hq : q.length ≤ (2 ^ n) ^ lam) :
    (2 ^ n) ^ lam * (esize (q, κ) + 1) ^ lam ≤ ansBound 5 lam n := by
  refine le_trans ?_ (lp_clock_le hl hn q q q q hq hq hq hq)
  have hq1 : 1 ≤ esize q := by
    change 1 ≤ (encode q).size
    cases (encode q : Data) <;> simp [Data.size]
  have hκ := esize_bool_le κ
  gcongr
  simp only [esize_prod]
  omega

/-- **`lenOf` at `2^n` with `seven`'s clock**, or any longer one. -/
theorem lenRun_seven {n : ℕ} (hT : T.IsBounded lam) (hn : 1 ≤ n) (q : BitStr) (κ : Bool)
    (hq : q.length ≤ (2 ^ n) ^ lam) {c : Unary} (hc : ansBound 5 lam n ≤ c.length) :
    lenRun U (c, clamp (T.progs, lam), (2 ^ n, q, κ)) = T.lenOf (2 ^ n) q κ :=
  lenRun_clamp U T hT ((two_le_exp_index_iff n).mpr hn) q κ
    ((len_clock_le (by have := hT.two_le; omega) hn q κ hq).trans hc)

/-- **`consOf` at `2^n` with `seven`'s clock**, or any longer one. -/
theorem lpRun_seven {n : ℕ} (hT : T.IsBounded lam) (hn : 1 ≤ n) (qx qy aR bR : BitStr)
    (hx : qx.length ≤ (2 ^ n) ^ lam) (hy : qy.length ≤ (2 ^ n) ^ lam)
    (ha : aR.length ≤ (2 ^ n) ^ lam) (hb : bR.length ≤ (2 ^ n) ^ lam) {c : Unary}
    (hc : ansBound 5 lam n ≤ c.length) :
    lpRun U (c, clamp (T.progs, lam), (2 ^ n, qx, qy, aR, bR)) =
      T.consOf (2 ^ n) qx qy aR bR :=
  lpRun_clamp U T hT ((two_le_exp_index_iff n).mpr hn) qx qy aR bR
    ((lp_clock_le (by have := hT.two_le; omega) hn qx qy aR bR hx hy ha hb).trans hc)

end Intro.InputRuns

end MIPRE.Tailored

end
