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
* `outputPrefix k`: the reported prefix `(L w).outputPrefix k y`, `k ≤ 7`, read off the kernel's
  attained-prefix scan (`scan`), under the guard at `k - 1` (`Guard`);

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

/-! ## The prefix scan and the reported prefixes -/

/-- The kernel's attained-prefix scan to depth `k` on the register
(`AuxiliaryScan.program` over the kernel's padded factor and matrix queries). -/
def scan (U : ClockedUniversalMachine) (k : ℕ) : PolyTimeFun Input AuxiliaryScan.State :=
  AuxiliaryScan.program (factorFromContext U) (matrixFromContext U) k

/-- The reported prefix `outputPrefix k y`, the second field of the scan state. -/
def outputPrefix (U : ClockedUniversalMachine) (k : ℕ) : PolyTimeFun Input BitStr :=
  fst.comp (snd.comp (scan U k))

/-- The prefix guard at level `k` in its semantic form: the reported `k`-prefix of `y` is
attained by the first `k` stages. -/
def Guard {Q : ℕ} (V : Verifier 7) {n : ℕ} (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (k : ℕ)
    (y : Fin Q → CL.𝔽₂) : Prop :=
  ∃ x, ((AuxiliaryDecision.padded V hs w).truncate k).eval x =
    (AuxiliaryDecision.padded V hs w).outputPrefix k y

theorem guard_mono {Q n : ℕ} (V : Verifier 7) (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    {j k : ℕ} (hj : j ≤ k) (y : Fin Q → CL.𝔽₂) (hg : Guard V hs w k y) : Guard V hs w j y := by
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, AuxiliaryScan.earlier_attained (AuxiliaryDecision.padded_supported V hs w) hj y x hx⟩

theorem guard_zero {Q n : ℕ} (V : Verifier 7) (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (y : Fin Q → CL.𝔽₂) : Guard V hs w 0 y :=
  ⟨0, by simp⟩

/-- Under the guard at `k`, the scan succeeds with the reported prefix and a seed attaining it. -/
theorem scan_of_guard (U : ClockedUniversalMachine) {lam n Q : ℕ} (V : Verifier 7)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    {k : ℕ} (hk : k ≤ 7) (y : Fin Q → CL.𝔽₂) (hg : Guard V hs w k y) :
    ∃ x, scan U k (context V lam n Q w, CL.toBits y) =
      (true, CL.toBits ((AuxiliaryDecision.padded V hs w).outputPrefix k y), CL.toBits x) ∧
      ((AuxiliaryDecision.padded V hs w).truncate k).eval x =
        (AuxiliaryDecision.padded V hs w).outputPrefix k y := by
  have hq := AuxiliarySourceScan.queriesCorrectBelow U V hV hn hs w 0 0 k hk
  obtain ⟨x, he, hx⟩ := AuxiliaryScan.program_sound (factorFromContext U) (matrixFromContext U)
    _ (AuxiliaryDecision.padded_supported V hs w) y k hq
    (AuxiliaryScan.program_complete (factorFromContext U) (matrixFromContext U) _
      (AuxiliaryDecision.padded_supported V hs w) y k hq hg)
  exact ⟨x, he, hx⟩

/-- **The reported prefix** `outputPrefix k y`, for `k ≤ 7`, under the guard one level below
(no hypothesis at `k = 0`). -/
theorem outputPrefix_correct (U : ClockedUniversalMachine) {lam n Q : ℕ} (V : Verifier 7)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    {k : ℕ} (hk : k ≤ 7) (y : Fin Q → CL.𝔽₂) (hg : Guard V hs w (k - 1) y) :
    outputPrefix U k (context V lam n Q w, CL.toBits y) =
      CL.toBits ((AuxiliaryDecision.padded V hs w).outputPrefix k y) := by
  cases k with
  | zero =>
    change (AuxiliaryScan.program (factorFromContext U) (matrixFromContext U) 0
      (context V lam n Q w, CL.toBits y)).2.1 = _
    rw [AuxiliaryScan.program_zero, AuxiliaryScan.zeros_toBits]
    simp
  | succ k =>
    obtain ⟨x, he, hx⟩ := scan_of_guard U V hV hn hs w (k := k) (by omega) y hg
    change (AuxiliaryScan.program (factorFromContext U) (matrixFromContext U) (k + 1) (context V lam n Q w, CL.toBits y)).2.1 = _
    rw [AuxiliaryScan.program_succ]
    change (AuxiliaryScan.advance _ _ k (_, scan U k (context V lam n Q w, CL.toBits y))).2.1 = _
    rw [he, AuxiliaryScan.advance_apply]
    simp only [↓reduceIte]
    exact congrArg (fun s : AuxiliaryScan.State => s.2.1)
      (AuxiliaryScan.stage_at_claimed _ _ _ (AuxiliaryDecision.padded_supported V hs w) k y x hx
        (AuxiliarySourceScan.queriesCorrectAt U V hV hn hs w 0 0 k (by omega)))

/-- The reported prefix under the guard at its own level. -/
theorem outputPrefix_correct_of_guard (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) (hs : V.sampler.dim (2 ^ n) ≤ Q)
    (w : Bool) {k : ℕ} (hk : k ≤ 7) (y : Fin Q → CL.𝔽₂) (hg : Guard V hs w k y) :
    outputPrefix U k (context V lam n Q w, CL.toBits y) =
      CL.toBits ((AuxiliaryDecision.padded V hs w).outputPrefix k y) :=
  outputPrefix_correct U V hV hn hs w hk y (guard_mono V hs w (Nat.sub_le k 1) y hg)

end MIPRE.Tailored.Intro.CLData

end
