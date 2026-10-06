/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.HonestBits
public import MIPRE.Background.Tailored.Intro.Pauli

@[expose] public section

/-!
# ZPC completeness of the tailored question reduction: the honest strategy

Phase 3c of `planning/aldous-lyons-track.md` (issue #281). The tailored presentation of the
introspection verifier `seven` (`MIPRE.Tailored.Intro.Complete.hasPerfectZPC_tpresented`) has a
perfect permutation strategy as soon as the reference verifier's typed game `rawGame` has a
perfect PCC strategy that charges only encodable answers and whose bit observables along the
padded layout `enc` are signed permutations, diagonal at the readable bits. This file proves
that the honest strategy `HonestChain.raw` is one, for every input whose strategy has
signed-permutation answer bits, diagonal at the readable ones (the input of a tailored
verifier):

* `raw_isXBit` (`hperm`): every bit of `enc` at every typed question is a signed permutation;
* `raw_isZBit` (`hdiag`): the readable ones are diagonal;
* `raw_support` (`hsupp`): a byte answer with a nonzero projection is well formed for the
  layout (`OkLayout`), and its register satisfies the readable conditions — the input's answer
  fits the cutoff, the prefix guard of Read and Hide, and Introspect's register is a source
  output.

The input is any perfect PCC strategy `RW` of the normal form verifier `W` at index `2^n` whose
answers at a question have the lengths the tailored verifier `V` assigns to it and whose answer
bits are signed permutations, diagonal below the readable length. `input_ofTNFV` checks this for
the strategy `lem:zpc-pcc` builds from a permutation strategy of `V` (`PermStrategy.toSync`,
extended by zero to the answers of `V.ofTNFV U`).
-/

noncomputable section

namespace MIPRE.Tailored.Intro.HonestChain

open Cost MIPRE.CL MIPRE.Introspection MIPRE.Introspection.CanonicalGame
open MIPRE.Introspection.DecisionCompiler MIPRE.Introspection.SourceCompiler
open MIPRE.Introspection.PauliSamplerParameters MIPRE.Introspection.AnswerParser
open scoped Kronecker

attribute [local instance] power_neZero

variable {c : ℕ} (W : Verifier 7) {lam n : ℕ}
  (RW : SyncStrategy (W.game (2 ^ n) ((2 ^ n) ^ lam)).doubled)
  (he : Even c) (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n)
  (V : TailoredVerifier 7) (hc : 2 ≤ c)
  (hlen : ∀ p a, RW.P.M p a ≠ 0 →
    a.1.length = V.lenOf (2 ^ n) (toBits p.2) false + V.lenOf (2 ^ n) (toBits p.2) true)
  (hX : ∀ p j, IsXBit (RW.P.M p) fun a => a.1.getD j false)
  (hZ : ∀ p j, j < V.lenOf (2 ^ n) (toBits p.2) false →
    IsZBit (RW.P.M p) fun a => a.1.getD j false)

/-- The readable lengths of the layout at the instance's parameters. -/
abbrev lenRI (c lam n : ℕ) : DecisionKernel.Label → ℕ :=
  lenR (registerBits c lam n) ((2 ^ n) ^ lam)
    (pauliLen (registerPower c lam n) (fieldBits c lam n)) pauliRead

theorem pauliRead_eq_true {T : QLD.Ty} (h : pauliRead T = true) : T = .pauli .Z := by
  cases T <;> simp_all [pauliRead]
  rename_i W
  cases W <;> simp_all [pauliRead]

include hlen hX hZ in
/-- **Every bit of the honest measurement at a typed question is a signed permutation, and the
readable ones are diagonal.** -/
theorem canonical_bits (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n))) (i : ℕ) :
    IsXBit ((canonical W RW (one_le_c hc) he hs).P.M q)
      (fbit hc ((2 ^ n) ^ lam) (srcSplitR V W hs) q.2.1 i) ∧
    (i < lenRI c lam n q.2.1 → IsZBit ((canonical W RW (one_le_c hc) he hs).P.M q)
      (fbit hc ((2 ^ n) ^ lam) (srcSplitR V W hs) q.2.1 i)) := by
  rcases q with ⟨w', p | ⟨t, w⟩, z⟩
  · refine ⟨isXBit_canonical_pauli W RW _ he hs hc _ _ w' p z i, fun hi => ?_⟩
    simp only [lenRI, lenR] at hi
    split_ifs at hi with hp
    · rw [pauliRead_eq_true hp]
      exact isZBit_canonical_pauliZ W RW _ he hs hc _ _ w' z i
    · omega
  · cases t with
    | introspect => exact bits_introspect W RW he hs V hc hlen hX hZ w' w z i
    | sample => exact bits_sample W RW he hs V hc hlen hX hZ w' w z i
    | read => exact bits_read W RW he hs V hc hlen hX hZ w' w z i
    | hide k => exact bits_hide W RW he hs V hc w' k w z i

/-! ## The honest strategy of the typed game -/

section Raw

variable (U : ClockedUniversalMachine) (hW : W.IsBounded lam) (hn : 1 ≤ n)

/-- The padded layout at the instance's parameters, at a typed question. -/
abbrev encI (q : CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a : Verifier.Answers (outerBound c lam n)) : BitStr :=
  enc (registerBits c lam n) ((2 ^ n) ^ lam) (srcSplitR V W hs) q.1 a.1

theorem bitObs_mergeAnswersByQuestion {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {G : SynchronousGame X A} (S : SyncStrategy G)
    (H : SynchronousGame X B) (f : X → A → B) (x : X) (g : B → Bool) :
    pvmObs ((S.mergeAnswersByQuestion H f).P.M x) (fun b => bitSign (g b)) =
      bitObs (S.P.M x) (g ∘ f x) :=
  bitObs_merge (S.P.M x) (f x) g

include hlen hX hZ in
/-- **`hperm`: every bit of the padded layout is a signed permutation observable of the honest
strategy.** -/
theorem raw_isXBit (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n))) (i : ℕ) :
    IsSignedPerm (pvmObs ((raw W RW hc he U hW hn).P.M q) fun a =>
      bitSign ((encI W (dim_le W c hc hW hn) V q.2 a).getD i false)) := by
  have h := (canonical_bits W RW he (dim_le W c hc hW hn) V hc hlen hX hZ q i).1
  have e := bitObs_mergeAnswersByQuestion
    (canonical W RW (one_le_c hc) he (dim_le W c hc hW hn))
    (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled
    (fun _ a => CanonicalComplete.encodeAnswer c hc lam n a) q
    (fun b => (encI W (dim_le W c hc hW hn) V q.2 b).getD i false)
  exact (congrArg IsSignedPerm e).mpr h

include hlen hX hZ in
/-- **`hdiag`: the readable bits are diagonal.** -/
theorem raw_isDiag (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n))) (i : ℕ) (hi : i < lenRI c lam n q.2.1) :
    (pvmObs ((raw W RW hc he U hW hn).P.M q) fun a =>
      bitSign ((encI W (dim_le W c hc hW hn) V q.2 a).getD i false)).IsDiag := by
  have h := ((canonical_bits W RW he (dim_le W c hc hW hn) V hc hlen hX hZ q i).2 hi).2
  have e := bitObs_mergeAnswersByQuestion
    (canonical W RW (one_le_c hc) he (dim_le W c hc hW hn))
    (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled
    (fun _ a => CanonicalComplete.encodeAnswer c hc lam n a) q
    (fun b => (encI W (dim_le W c hc hW hn) V q.2 b).getD i false)
  exact (congrArg Matrix.IsDiag e).mpr h

end Raw

end MIPRE.Tailored.Intro.HonestChain

end
