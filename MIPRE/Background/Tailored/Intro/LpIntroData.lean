/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Typed
public import MIPRE.Tailored.Intro.CLData
public import MIPRE.Tailored.Intro.InputRuns
public import MIPRE.Tailored.Intro.AuxProg
public import MIPRE.Tailored.Intro.KerGensProg

@[expose] public section

/-!
# The register data of the introspection processor

Issue #281 (Phase 3 of `planning/aldous-lyons-track.md`). The linear-constraints processor of
the tailored introspection verifier (`LpIntro.lean`) works on an environment `Env` prepared once
per input: the clock `2^{(λn + 1)^5}` in unary, the clamped description of the input `M`, the
index `2^n`, the Pauli parameters `(k, j, 2^j)` in unary and the register width `Q` and the
cutoff `R` in unary (`envOf`). This file computes from it, at an auxiliary label `t` and a
register `y` of `Q` bits, the data the readable condition `Typed.G` reads:

* `ctxP w`: the kernel's context (`CLData.context`) of role `w`;
* `srcQP t`: the input question `srcQuestion t y`;
* `splitU κ t`: the input's split `srcSplitR`/`srcSplitL` at the register, in unary, by a clocked
  run of the input's answer-length calculator (`InputRuns`);
* `GP t`: the readable condition `Typed.G` itself, as a Boolean.

Each has its correctness theorem at `envOf c λ n (clamp (T.progs, λ))`, for a `λ`-bounded
tailored
input `T`, a `λ`-bounded normal form verifier `V` with `T`'s sampler program, and `1 ≤ n`.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.LpIntro

open Cost Cost.Data Cost.PolyTimeFun CL MIPRE.Introspection CL.Detyping.Program InputRuns
open MIPRE.Introspection.SourcePadding.Program

/-! ## The environment -/

/-- The field width `k` and the selector width `j` at `(c, λ, n)`. -/
abbrev kk (c lam n : ℕ) : ℕ := SourceCompiler.fieldBits c lam n
abbrev jj (c lam n : ℕ) : ℕ := PauliSamplerParameters.selectorBits c lam n

/-- The register width `Q = 2^{2^j} k` (`SourceCompiler.registerBits`), in the form of
`Typed.Q`. -/
abbrev QQ (c lam n : ℕ) : ℕ := 2 ^ 2 ^ jj c lam n * kk c lam n

theorem QQ_eq (c lam n : ℕ) : QQ c lam n = SourceCompiler.registerBits c lam n := rfl

/-- The environment: the clock, the clamped description, the index `2^n`, the Pauli parameters,
`Q` and `R` in unary. -/
abbrev Env := Unary × Metadata × ℕ × PauliSamplerParameters.Parameters × Unary × Unary

/-- The environment at `(c, λ, n)` and the description `M`. -/
def envOf (c lam n : ℕ) (M : Metadata) : Env :=
  (unary (ansBound 5 lam n), M, 2 ^ n, PauliSamplerParameters.parameters c lam n,
    unary (SourceCompiler.registerBits c lam n), unary (SourceCompiler.originalBound lam n))

def eClock : PolyTimeFun Env Unary := fst
def eM : PolyTimeFun Env Metadata := fst.comp snd
def eIdx : PolyTimeFun Env ℕ := fst.comp (snd.comp snd)
def ePar : PolyTimeFun Env PauliSamplerParameters.Parameters := fst.comp (snd.comp (snd.comp snd))
def eQ : PolyTimeFun Env Unary := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def eR : PolyTimeFun Env Unary := snd.comp (snd.comp (snd.comp (snd.comp snd)))

@[simp] theorem eClock_apply (e : Env) : eClock e = e.1 := rfl
@[simp] theorem eM_apply (e : Env) : eM e = e.2.1 := rfl
@[simp] theorem eIdx_apply (e : Env) : eIdx e = e.2.2.1 := rfl
@[simp] theorem ePar_apply (e : Env) : ePar e = e.2.2.2.1 := rfl
@[simp] theorem eQ_apply (e : Env) : eQ e = e.2.2.2.2.1 := rfl
@[simp] theorem eR_apply (e : Env) : eR e = e.2.2.2.2.2 := rfl

/-- The kernel's context of role `w`, from the environment. -/
def ctxP (w : Bool) : PolyTimeFun Env AuxiliarySource.Context :=
  eClock.pair ((fst.comp (fst.comp eM)).pair (eIdx.pair ((const w).pair ((const 1).pair
    (zerosOf eQ)))))

theorem toBits_zero (Q : ℕ) : CL.toBits (0 : Fin Q → 𝔽₂) = List.replicate Q false := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [CL.toBits]

theorem ctxP_envOf (c lam n : ℕ) (M : Metadata) (V : Verifier 7) (hM : M.1.1 = V.sampler.prog)
    (w : Bool) :
    ctxP w (envOf c lam n M) = CLData.context V lam n (SourceCompiler.registerBits c lam n) w := by
  simp only [ctxP, pair_apply, comp_apply, eClock_apply, eM_apply, eIdx_apply, eQ_apply,
    fst_apply, const_apply, zerosOf_apply, envOf, CLData.context, queryContext, hM,
    toBits_zero, length_unary]

/-! ## The register level -/

/-- A register with the environment. -/
abbrev RIn := Env × BitStr

/-- The kernel's input of role `w`: its context and the register. -/
def cIn (w : Bool) : PolyTimeFun RIn CLData.Input := ((ctxP w).comp fst).pair snd

variable (U : ClockedUniversalMachine)

/-- The input question at an auxiliary label: `L_w` of the register at Sample, the register's
first `dim` bits otherwise. -/
def srcQP (t : AuxType 7 × Bool) : PolyTimeFun RIn BitStr :=
  if t.1 = .sample then (CLData.sourceEval U).comp (cIn t.2)
  else take.comp (snd.pair (sourceWidth.comp ((CLData.widths U).comp (cIn t.2))))

/-- A clocked result read as a length, in unary. -/
def lenReadU : PolyTimeFun Data Unary :=
  length.comp ((ofEncodeEq rawList encode_rawList).comp treeTail)

theorem length_lenReadU (d : Data) : (lenReadU d).length = lenRead d := by
  simp [lenReadU, lenRead]

theorem isEmpty_drop (u v : Unary) :
    (u.drop v.length).isEmpty = decide (u.length ≤ v.length) := by
  rw [Bool.eq_iff_iff, List.isEmpty_iff, List.drop_eq_nil_iff, decide_eq_true_iff]

/-- The input's split at an auxiliary label, in unary: readable (`κ = false`) or linear. -/
def splitU (κ : Bool) (t : AuxType 7 × Bool) : PolyTimeFun RIn Unary :=
  lenReadU.comp ((runOn U).comp ((eClock.comp fst).pair ((lenProgOf.comp (eM.comp fst)).pair
    ((eIdx.comp fst).pair ((srcQP U t).pair (const κ))))))

/-- Whether the input's answer fits the cutoff, off Hide (`srcFits`). -/
def fitsCore (t : AuxType 7 × Bool) : PolyTimeFun RIn Bool :=
  isNilOf (subOf (catF (splitU U false t) (splitU U true t)) (eR.comp fst))

/-- Whether the input's answer fits the cutoff (`srcFits`). -/
def fitsP (t : AuxType 7 × Bool) : PolyTimeFun RIn Bool :=
  if isHideT t.1 then const true else fitsCore U t

/-- The level of the prefix guard of a label: `i` at Hide `i`, `6` at Read. -/
def prefLevel : AuxType 7 → Option ℕ
  | .hide i => some i.val
  | .read => some 6
  | _ => none

/-- The prefix condition (`Typed.prefixOK`). -/
def prefP (t : AuxType 7 × Bool) : PolyTimeFun RIn Bool :=
  match prefLevel t.1 with
  | some k => (CLData.guard U k).comp (cIn t.2)
  | none => const true

/-- Source membership at an Introspect register. -/
def srcP (t : AuxType 7 × Bool) : PolyTimeFun RIn Bool :=
  if t.1 = .introspect then (CLData.inSource U).comp (cIn t.2) else const true

/-- **The readable condition** `Typed.G`, as a Boolean. -/
def GP (t : AuxType 7 × Bool) : PolyTimeFun RIn Bool :=
  andOf (fitsP U t) (andOf (prefP U t) (srcP U t))

/-! ## Correctness -/

section Correct

variable {c lam n : ℕ} (T : TailoredVerifier 7) (V : Verifier 7) (hT : T.IsBounded lam)
  (hV : V.IsBounded lam) (hn : 1 ≤ n) (hsamp : V.sampler.prog = T.sampler.prog)
  (hs : V.sampler.dim (2 ^ n) ≤ QQ c lam n)

/-- The environment of the input `T` at `(c, λ, n)`. -/
abbrev envT (c lam n : ℕ) (T : TailoredVerifier 7) : Env := envOf c lam n (clamp (T.progs, lam))

include hT hsamp in
theorem ctxP_envT (w : Bool) :
    ctxP w (envT c lam n T) = CLData.context V lam n (QQ c lam n) w := by
  apply ctxP_envOf
  rw [clamp_bounded T hT, hsamp]
  rfl

include hT hsamp in
theorem cIn_envT (w : Bool) (y : BitStr) :
    cIn w (envT c lam n T, y) = (CLData.context V lam n (QQ c lam n) w, y) := by
  simp only [cIn, pair_apply, comp_apply, fst_apply, snd_apply, ctxP_envT T V hT hsamp]

include hT hV hn hsamp in
/-- **The input question at a register.** -/
theorem srcQP_envT (t : AuxType 7 × Bool) (y : BitStr)
    (hy : y.length = QQ c lam n) :
    srcQP U t (envT c lam n T, y) = srcQuestion V hs t y := by
  have ey : CL.toBits (CL.ofBits (QQ c lam n) y) = y := toBits_ofBits hy
  obtain ⟨t, w⟩ := t
  cases t with
  | sample =>
    simp only [srcQP, ↓reduceIte, comp_apply, cIn_envT T V hT hsamp, srcQuestion]
    conv_lhs => rw [← ey]
    exact CLData.sourceEval_correct U V hV hn hs w _
  | _ =>
    simp only [srcQP, reduceCtorEq, ↓reduceIte, comp_apply, pair_apply, snd_apply,
      cIn_envT T V hT hsamp,
      CLData.widths_context U V hV hn hs w y, sourceWidth, fst_apply, take_apply, length_unary,
      srcQuestion]
    rw [← AuxiliaryProgram.ofBits_take_first hs, ey,
      toBits_ofBits (by simp only [List.length_take, hy]; omega)]

include hV hn in
/-- The input question has at most `(2^n)^λ` bits. -/
theorem length_srcQuestion_le (t : AuxType 7 × Bool) (y : BitStr) :
    (srcQuestion V hs t y).length ≤ (2 ^ n) ^ lam := by
  have h := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).1
  obtain ⟨t, w⟩ := t
  cases t <;> simpa [srcQuestion] using h

include hT hV hn hsamp in
/-- **The input's split at a register**, in unary. -/
theorem length_splitU (κ : Bool) (t : AuxType 7 × Bool) (y : BitStr)
    (hy : y.length = QQ c lam n) :
    (splitU U κ t (envT c lam n T, y)).length = T.lenOf (2 ^ n) (srcQuestion V hs t y) κ := by
  simp only [splitU, comp_apply, pair_apply, fst_apply, const_apply, eClock_apply,
    eM_apply, eIdx_apply, length_lenReadU, srcQP_envT U T V hT hV hn hsamp hs t y hy]
  rw [← lenRun_seven U T hT hn (srcQuestion V hs t y) κ
    (length_srcQuestion_le V hV hn hs t y) (c := unary (ansBound 5 lam n))
    (by simp)]
  rfl

include hT hV hn hsamp in
theorem splitU_envT (κ : Bool) (t : AuxType 7 × Bool) (y : BitStr)
    (hy : y.length = QQ c lam n) :
    splitU U κ t (envT c lam n T, y) = unary (T.lenOf (2 ^ n) (srcQuestion V hs t y) κ) := by
  rw [← length_splitU U T V hT hV hn hsamp hs κ t y hy, unary_length]

include hT hV hn hsamp in
theorem fitsP_envT (t : AuxType 7 × Bool) (y : BitStr)
    (hy : y.length = QQ c lam n) :
    fitsP U t (envT c lam n T, y) = true ↔
      srcFits ((2 ^ n) ^ lam) (srcSplitR T V hs) (srcSplitL T V hs) t y := by
  have key : fitsCore U t (envT c lam n T, y) = true ↔
      srcSplitR T V hs t y + srcSplitL T V hs t y ≤ (2 ^ n) ^ lam := by
    rw [fitsCore, isNilOf_apply, subOf_apply, catF_apply, comp_apply, fst_apply, eR_apply,
      isEmpty_drop, List.length_append, length_splitU U T V hT hV hn hsamp hs _ t y hy,
      length_splitU U T V hT hV hn hsamp hs _ t y hy, decide_eq_true_iff]
    simp only [envT, envOf, length_unary, SourceCompiler.originalBound_eq, srcSplitR, srcSplitL]
  obtain ⟨t, w⟩ := t
  cases t <;> simp only [fitsP, isHideT, srcFits, ↓reduceIte, key, Bool.false_eq_true,
    const_apply]

include hT hV hn hsamp in
theorem prefP_envT (t : AuxType 7 × Bool) (y : BitStr)
    (hy : y.length = QQ c lam n) :
    prefP U t (envT c lam n T, y) = true ↔ Typed.prefixOK (kk c lam n) (jj c lam n) V hs t y := by
  have ey : CL.toBits (CL.ofBits (QQ c lam n) y) = y := toBits_ofBits hy
  obtain ⟨t, w⟩ := t
  cases t with
  | hide i =>
    simp only [prefP, prefLevel, comp_apply, cIn_envT T V hT hsamp, Typed.prefixOK]
    conv_lhs => rw [← ey]
    exact CLData.guard_iff U V hV hn hs w (by omega) _
  | read =>
    simp only [prefP, prefLevel, comp_apply, cIn_envT T V hT hsamp, Typed.prefixOK]
    conv_lhs => rw [← ey]
    exact CLData.guard_iff U V hV hn hs w (by omega) _
  | introspect => simp [prefP, prefLevel, Typed.prefixOK]
  | sample => simp [prefP, prefLevel, Typed.prefixOK]

include hT hV hn hsamp in
theorem srcP_envT (t : AuxType 7 × Bool) (y : BitStr) :
    srcP U t (envT c lam n T, y) = true ↔
      (t.1 = .introspect → SourceCompiler.InSource (V.sampler.dim (2 ^ n)) y) := by
  obtain ⟨t, w⟩ := t
  by_cases ht : t = .introspect
  · subst ht
    simp only [srcP, ↓reduceIte, comp_apply, cIn_envT T V hT hsamp,
      CLData.inSource_correct U V hV hn, decide_eq_true_iff, forall_const]
  · simp [srcP, ht]

include hT hV hn hsamp in
/-- **The readable condition** `Typed.G` at a register of `Q` bits. -/
theorem GP_envT (t : AuxType 7 × Bool) (y : BitStr)
    (hy : y.length = QQ c lam n) :
    GP U t (envT c lam n T, y) = true ↔
      Typed.G (kk c lam n) (jj c lam n) ((2 ^ n) ^ lam) T V hs t y := by
  rw [GP, andOf_apply, andOf_apply, Bool.and_eq_true, Bool.and_eq_true,
    fitsP_envT U T V hT hV hn hsamp hs t y hy, prefP_envT U T V hT hV hn hsamp hs t y hy,
    srcP_envT U T V hT hV hn hsamp t y]
  rfl

end Correct

end MIPRE.Tailored.Intro.LpIntro

end
