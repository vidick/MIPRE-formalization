/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Introspection.AuxiliaryDecisionCorrect
public import MIPRE.Foundations.Introspection.AuxiliaryPrefixGuardProgram

@[expose] public section

/-!
# The input's CL data, computed from the kernel's context

The linear-constraints processor of the tailored introspection verifier needs, at a register
`y` (a length-`Q` bit string), data about the padded CL functions
`L w = AuxiliaryDecision.padded V hs w` of the input normal form verifier `V` at index `2^n`.
The decision kernel of `MIPRE.Introspection.seven` already computes all of it from one
`AuxiliarySource.Context`, with a clocked universal machine `U`; this file exposes each datum as
a `Cost.PolyTimeFun` on `Input = AuxiliarySource.Context × BitStr`, at the context the kernel
builds (`context V lam n Q w`, the kernel's `queryContext` with role `w`), with a correctness
theorem for a `λ`-bounded `V`, `1 ≤ n` and `hs : V.sampler.dim (2^n) ≤ Q`:

* `eval`: `(L w).eval z` (one marginal query at full depth, padded with zeros), and
  `sourceEval`, its first `dim` bits;

The sampler program is specified only at attained prefixes, so the data at a stage `k` are
correct under the prefix guard at `k`, which is itself computed exactly.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.CLData

open Cost Cost.PolyTimeFun CL.Detyping.Program MIPRE.Introspection
open MIPRE.Introspection.SourcePadding MIPRE.Introspection.SourcePadding.Program
open MIPRE.Introspection.AuxiliaryProgram

/-- A context of the decision kernel and a register, as a bit string. -/
abbrev Input := AuxiliarySource.Context × BitStr

/-- The context the kernel builds for `V`, `λ`, `n`, the register width `Q` and the role `w`:
the shared clock, the sampler program, the index `2^n`, the role, and a level and prefix
(of length `Q`) that every query below replaces. -/
def context (V : Verifier 7) (lam n Q : ℕ) (w : Bool) : AuxiliarySource.Context :=
  queryContext V lam n w 0 (0 : Fin Q → CL.𝔽₂)

/-! ## The evaluation `L_w(z)` -/

/-- The kernel's width data: the source dimension, capped by the register width. -/
def widths (U : ClockedUniversalMachine) : PolyTimeFun Input QContext := (adapt U).comp fst

/-- The marginal query at full depth `7` on the first `dim` bits of the register. -/
def marginalContext (U : ClockedUniversalMachine) : PolyTimeFun Input AuxiliarySource.Context :=
  let ctx : PolyTimeFun Input AuxiliarySource.Context := fst
  (AuxiliarySource.budget.comp ctx).pair ((AuxiliarySource.source.comp ctx).pair
    ((AuxiliarySource.index.comp ctx).pair ((AuxiliarySource.player.comp ctx).pair
      ((const 7).pair (take.comp (snd.pair (sourceWidth.comp (widths U))))))))

/-- The source's evaluation on the first `dim` bits of the register: `L_w` of the input
verifier, unpadded. -/
def sourceEval (U : ClockedUniversalMachine) : PolyTimeFun Input BitStr :=
  readBits.comp (treeTail.comp ((AuxiliarySource.query U 1).comp
    ((const ([] : BitStr)).pair (marginalContext U))))

/-- The padded evaluation: the source's, followed by zeros up to the register width. -/
def eval (U : ClockedUniversalMachine) : PolyTimeFun Input BitStr :=
  append.comp ((sourceEval U).pair
    (replicate.comp ((suffixWidth.comp (widths U)).pair (const false))))

theorem context_dimension (U : ClockedUniversalMachine) {lam n : ℕ} (V : Verifier 7)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (Q : ℕ) (w : Bool) :
    dimension U (context V lam n Q w) = V.sampler.dim (2 ^ n) :=
  queryContext_dimension U V hV hn w 0 _

theorem widths_context (U : ClockedUniversalMachine) {lam n Q : ℕ} (V : Verifier 7)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (y : BitStr) :
    widths U (context V lam n Q w, y) = (unary (V.sampler.dim (2 ^ n)), context V lam n Q w) :=
  adapt_correct U _ _ (by simpa [context, queryContext, AuxiliarySource.inputPrefix,
    CL.length_toBits] using hs) (context_dimension U V hV hn Q w)

/-- **The source evaluation**: the first `dim` bits of `L_w(z)`, i.e. `L_w` of the input
verifier at the first `dim` bits of `z`. -/
theorem sourceEval_correct (U : ClockedUniversalMachine) {lam n Q : ℕ} (V : Verifier 7)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (z : Fin Q → CL.𝔽₂) :
    sourceEval U (context V lam n Q w, CL.toBits z) =
      CL.toBits (CL.pull (firstEmbedding hs) ((AuxiliaryDecision.padded V hs w).eval z)) := by
  have hm : marginalContext U (context V lam n Q w, CL.toBits z) =
      (unary (ansBound 5 lam n), V.sampler.prog, 2 ^ n, w, 7,
        (CL.toBits z).take (V.sampler.dim (2 ^ n))) := by
    simp only [marginalContext, comp_apply, pair_apply, fst_apply, snd_apply, const_apply,
      widths_context U V hV hn hs w, sourceWidth, length_unary, take_apply]
    rfl
  have hr := bounded_marginal_result V hV hn (Player.ofBool w) 7
    ((CL.toBits z).take (V.sampler.dim (2 ^ n))) (by norm_num) le_rfl
    (AuxiliarySourceScan.level_size_le hV.two_le hn (by decide : 6 < 7))
    (by simp [CL.length_toBits, Nat.min_eq_left hs])
  simp only [sourceEval, comp_apply, pair_apply, const_apply, hm, AuxiliarySource.query_apply,
    length_unary]
  change readBits (treeTail (clockedResult V.sampler.prog
    (encode (2 ^ n, CL.Sampler.Query.marginal (Player.ofBool w) 7
      ((CL.toBits z).take (V.sampler.dim (2 ^ n))))) (ansBound 5 lam n))) = _
  rw [hr, treeTail_cons, readBits_encode, ofBits_take_first hs, CL.CLFun.truncate_self,
    AuxiliaryDecision.padded, ← CL.CLFun.truncate_self ((depthFamily _ _ w)),
    depthFamily_eval_truncate, CL.pull_push, CL.CLFun.truncate_self]
  rfl

/-- **The evaluation** `L_w(z)` of the padded input CL function, as a length-`Q` bit string. -/
theorem eval_correct (U : ClockedUniversalMachine) {lam n Q : ℕ} (V : Verifier 7)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (z : Fin Q → CL.𝔽₂) :
    eval U (context V lam n Q w, CL.toBits z) =
      CL.toBits ((AuxiliaryDecision.padded V hs w).eval z) := by
  have hp : (AuxiliaryDecision.padded V hs w).eval z = CL.push (firstEmbedding hs)
      (CL.pull (firstEmbedding hs) ((AuxiliaryDecision.padded V hs w).eval z)) := by
    rw [AuxiliaryDecision.padded, ← CL.CLFun.truncate_self ((depthFamily _ _ w)),
      depthFamily_eval_truncate, CL.pull_push]
  simp only [eval, comp_apply, pair_apply, const_apply, sourceEval_correct U V hV hn hs w z,
    widths_context U V hV hn hs w, suffixWidth, fullWidth, sourceWidth]
  rw [hp, toBits_push_first, CL.pull_push]
  simp [context, queryContext, AuxiliarySource.inputPrefix, CL.length_toBits]

end MIPRE.Tailored.Intro.CLData

end
