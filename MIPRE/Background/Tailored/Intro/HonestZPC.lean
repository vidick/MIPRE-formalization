/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.HonestBits
public import MIPRE.Background.Tailored.Intro.Pauli
public import MIPRE.Background.Tailored.Intro.Complete
public import MIPRE.Tailored.OfTNFVT
public import MIPRE.Tailored.Intro.Input

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
* `raw_isDiag` (`hdiag`): the readable ones, below `Typed.lenR`, are diagonal;
* `raw_support` (`hsupp`): a byte answer with a nonzero projection satisfies `Complete.okT`: it
  is well formed for the layout (`Complete.OkL`), and its register satisfies the readable
  conditions (`Typed.readOK`) — the input's answer fits the cutoff, the prefix guard of Read
  and Hide, and Introspect's register is a source output.

The input is any perfect PCC strategy `RW` of the normal form verifier `W` at index `2^n` whose
answers at a question have the lengths the tailored verifier `V` assigns to it and whose answer
bits are signed permutations, diagonal below the readable length (`honest_zpc`). `inputSync`
is such a strategy, built by `lem:zpc-pcc` from a permutation strategy of `V`
(`PermStrategy.toSync`, extended by zero to the answers of `V.ofTNFV U`), and `inputSyncT` is
the same strategy on the game of `V.ofTNFVT U`, which is that of `V.ofTNFV U`
(`honest_zpc_ofTNFVT`).
-/

noncomputable section

namespace MIPRE.Tailored.Intro.HonestChain

open Cost MIPRE.CL MIPRE.Introspection MIPRE.Introspection.CanonicalGame
open MIPRE.Introspection.DecisionCompiler MIPRE.Introspection.SourceCompiler
open MIPRE.Introspection.PauliSamplerParameters MIPRE.Introspection.AnswerParser
open scoped Kronecker

set_option linter.unusedSectionVars false

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

theorem pauliRead_eq_true {T : QLD.Ty} (h : pauliRead T = true) : T = .pauli .Z := by
  cases T <;> simp_all [pauliRead]
  rename_i W
  cases W <;> simp_all

include hlen hX hZ in
/-- **Every bit of the honest measurement at a typed question is a signed permutation, and the
readable ones are diagonal.** -/
theorem canonical_bits (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n))) (i : ℕ) :
    IsXBit ((canonical W RW (one_le_c hc) he hs).P.M q)
      (fbit hc ((2 ^ n) ^ lam) (srcSplitR V W hs) q.2.1 i) ∧
    (i < Typed.lenR (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) q.2.1 →
      IsZBit ((canonical W RW (one_le_c hc) he hs).P.M q)
        (fbit hc ((2 ^ n) ^ lam) (srcSplitR V W hs) q.2.1 i)) := by
  rcases q with ⟨w', p | ⟨t, w⟩, z⟩
  · refine ⟨isXBit_canonical_pauli W RW _ he hs hc _ _ w' p z i, fun hi => ?_⟩
    simp only [Typed.lenR, PauliCons.pauliLenR] at hi
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
      bitSign ((Complete.encT V W c lam (dim_le W c hc hW hn) q.2 a).getD i false)) := by
  have h := (canonical_bits W RW he (dim_le W c hc hW hn) V hc hlen hX hZ q i).1
  have e := bitObs_mergeAnswersByQuestion
    (canonical W RW (one_le_c hc) he (dim_le W c hc hW hn))
    (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled
    (fun _ a => CanonicalComplete.encodeAnswer c hc lam n a) q
    (fun b => (Complete.encT V W c lam (dim_le W c hc hW hn) q.2 b).getD i false)
  exact (congrArg IsSignedPerm e).mpr h

include hlen hX hZ in
/-- **`hdiag`: the readable bits are diagonal.** -/
theorem raw_isDiag (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n))) (i : ℕ)
    (hi : i < Typed.lenR (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) q.2.1) :
    (pvmObs ((raw W RW hc he U hW hn).P.M q) fun a =>
      bitSign ((Complete.encT V W c lam (dim_le W c hc hW hn) q.2 a).getD i false)).IsDiag := by
  have h := ((canonical_bits W RW he (dim_le W c hc hW hn) V hc hlen hX hZ q i).2 hi).2
  have e := bitObs_mergeAnswersByQuestion
    (canonical W RW (one_le_c hc) he (dim_le W c hc hW hn))
    (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled
    (fun _ a => CanonicalComplete.encodeAnswer c hc lam n a) q
    (fun b => (Complete.encT V W c lam (dim_le W c hc hW hn) q.2 b).getD i false)
  exact (congrArg Matrix.IsDiag e).mpr h

end Raw

/-! ## The support -/

section Support

theorem mergeAnswersByQuestion_ne_zero {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {G : SynchronousGame X A} (S : SyncStrategy G)
    (H : SynchronousGame X B) (f : X → A → B) (x : X) (b : B)
    (h : (S.mergeAnswersByQuestion H f).P.M x b ≠ 0) : ∃ a, f x a = b ∧ S.P.M x a ≠ 0 := by
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨a, (Finset.mem_filter.1 ha).2, hne⟩

theorem length_answerBits {k m d : ℕ} (E : SAT.BinField k) (q : QLD.Question E.carrier m)
    (a : QLD.Answer E.carrier m d) (h : q.fmtOk a = true) :
    (QLD.PauliAnswerProgram.answerBits E a).length =
      QLD.PauliAnswerProgram.count q.ty m d * QLD.PauliAnswerProgram.width q.ty k := by
  unfold QLD.PauliAnswerProgram.answerBits
  rw [List.length_flatten, List.map_congr_left
    (QLD.PauliAnswerProgram.answerRows_width E q a h), List.map_const', List.sum_replicate,
    QLD.PauliAnswerProgram.answerRows_length E q a h, smul_eq_mul]

theorem binaryDecode_ty {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {m t : ℕ} (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) (T : QLD.Ty)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) :
    (QLD.PauliCL.ExplicitSeed.binaryDecode π b T x).ty = T := by
  cases T <;> rfl

/-- The binary operator at a Pauli label vanishes off the Pauli answers. -/
theorem op_inl_eq_zero {F A : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
    (L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ)
    (D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool)
    (R : SyncStrategy (Honest.sourceGame L D).doubled) (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (hL : ∀ w, (L w).SupportedOn Finset.univ)
    (T : QLD.Ty) (x : Fin ((3 * m + 3) * t) → ZMod 2) (a : BinaryComplete.Answer F A m t d)
    (ha : ∀ p, a ≠ .pauli p) : BinaryComplete.op L D R hm b hL (.inl T, x) a = 0 := by
  cases a with
  | pauli p => exact absurd rfl (ha p)
  | _ => rfl

variable (hc1 : 1 ≤ c)

/-- At a Pauli label the honest measurement charges only Pauli answers. -/
theorem canonical_pauli_shape (w' : Bool) (T : QLD.Ty)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW hc1 he hs).P.M (w', (.inl T, z)) a ≠ 0) :
    ∃ x, a = .pauli x := by
  by_contra hn
  push Not at hn
  apply ha
  rw [canonical_M]
  generalize hq : ExplicitGame.questionEquiv (permutation c lam n) (basis c he lam n)
    (.inl T, z) = q'
  obtain ⟨p', x⟩ := q'
  have hp' : p' = .inl T := (congrArg Prod.fst hq).symm
  subst hp'
  rw [op_inl_eq_zero (family W hs) (decider W hs) (reindexed W RW hs) (divides c hc1 lam n)
    (basis c he lam n) (family_supported W hs) T x _ ?_]
  · ext
    rfl
  intro p h
  cases a with
  | pauli x => exact hn x rfl
  | _ => cases h

theorem canonical_aux_ne_zero (w' : Bool) (t : AuxType 7 × Bool)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW hc1 he hs).P.M (w', (.inr t, z)) a ≠ 0) :
    Honest.auxOp (PA := QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
      (family W hs) (decider W hs) (reindexed W RW hs) (family_supported W hs) t
      (AuxiliaryQuotient.answerEquiv (numbering c lam n) a) ≠ 0 := by
  intro h0
  apply ha
  rw [canonical_M]
  change ((Honest.auxOp (PA := QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
      (family W hs) (decider W hs) (reindexed W RW hs) (family_supported W hs) t
      (AuxiliaryQuotient.answerEquiv (numbering c lam n) a)) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix _ _ = 0
  rw [h0, Matrix.zero_kronecker]
  rfl

end Support

/-! ### The honest auxiliary measurements' support -/

section AuxSupport

variable {ι A PA : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Fintype PA]
  {ℓ : ℕ} (L : Bool → CL.CLFun 𝔽₂ ι ℓ) (D : (ι → 𝔽₂) → (ι → 𝔽₂) → A → A → Bool)
  (R : SyncStrategy (Honest.sourceGame L D).doubled)

theorem parsedCoreOp_support (t : Honest.CoreType) (b : ParsedAnswer (ι → 𝔽₂) A PA)
    (h : Honest.parsedCoreOp L D R t b ≠ 0) :
    ∃ y α, b = .pair y α ∧ R.P.M (t.2, Honest.originalQuestion L t y) α ≠ 0 := by
  cases b with
  | pair y α =>
    refine ⟨y, α, rfl, fun h0 => h ?_⟩
    change Introspection.readout _ _ ⊗ₖ R.P.M (t.2, Honest.originalQuestion L t y) α = 0
    rw [h0, Matrix.kronecker_zero]
  | _ => exact absurd rfl h

theorem parsedReadOp_support (w : Bool) (hL : (L w).SupportedOn Finset.univ)
    (b : ParsedAnswer (ι → 𝔽₂) A PA) (h : Honest.parsedReadOp L D R w hL b ≠ 0) :
    ∃ y yp α, b = .read y yp α ∧ R.P.M (w, y) α ≠ 0 := by
  cases b with
  | read y yp α =>
    refine ⟨y, yp, α, rfl, fun h0 => h ?_⟩
    change Honest.readOp (L w) hL (y, yp) ⊗ₖ R.P.M (w, y) α = 0
    rw [h0, Matrix.kronecker_zero]
  | _ => exact absurd rfl h

theorem parsedHideOp_support (w : Bool) (k : ℕ) (hL : (L w).SupportedOn Finset.univ)
    (b : ParsedAnswer (ι → 𝔽₂) A PA) (h : Honest.parsedHideOp L D R w k hL b ≠ 0) :
    ∃ y yp x, b = .hide y yp x := by
  cases b with
  | hide y yp x => exact ⟨y, yp, x, rfl⟩
  | _ => exact absurd rfl h

end AuxSupport

/-! ### The support of the honest strategy, label by label -/

section CanonicalSupport

theorem srcSplitL_eq (t : AuxType 7 × Bool) (ht : t.1 ≠ .sample)
    (y : Fin (registerBits c lam n) → 𝔽₂) :
    srcSplitL V W hs t (toBits y) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs) y)) true := by
  obtain ⟨t, w⟩ := t
  cases t <;> simp_all [srcSplitL, srcQuestion]

theorem srcSplitL_sample (w : Bool) (y : Fin (registerBits c lam n) → 𝔽₂) :
    srcSplitL V W hs (.sample, w) (toBits y) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs)
        ((AuxiliaryDecision.padded W hs w).eval y))) true := by
  simp [srcSplitL, srcQuestion]

theorem srcSplitR_symm (t : AuxType 7 × Bool) (ht : t.1 ≠ .sample)
    (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    srcSplitR (Q := Typed.Q (fieldBits c lam n) (selectorBits c lam n)) V W hs t
      (toBits ((reindexEquiv (numbering c lam n)).symm y)) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs)
        ((reindexEquiv (numbering c lam n)).symm y))) false :=
  srcSplitR_eq W hs V t ht _

theorem srcSplitL_symm (t : AuxType 7 × Bool) (ht : t.1 ≠ .sample)
    (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    srcSplitL (Q := Typed.Q (fieldBits c lam n) (selectorBits c lam n)) V W hs t
      (toBits ((reindexEquiv (numbering c lam n)).symm y)) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs)
        ((reindexEquiv (numbering c lam n)).symm y))) true :=
  srcSplitL_eq W hs V t ht _

theorem encodeAnswer_pair (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n))
    (α : Verifier.Answers ((2 ^ n) ^ lam)) :
    (CanonicalComplete.encodeAnswer c hc lam n
      ((AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm (.pair y α))).1 =
      pairBits (toBits ((reindexEquiv (numbering c lam n)).symm y)) α.1 := rfl

theorem take_enc_pair {t : AuxType 7 × Bool} (ht : t.1 = .introspect ∨ t.1 = .sample)
    {y α : BitStr} (hy : y.length = registerBits c lam n) :
    win (enc (registerBits c lam n) ((2 ^ n) ^ lam) (srcSplitR V W hs) (P := QLD.Ty) (.inr t)
      (pairBits y α)) 0 (Typed.Q (fieldBits c lam n) (selectorBits c lam n)) = y := by
  have hy' : y.length = Typed.Q (fieldBits c lam n) (selectorBits c lam n) := hy
  rw [enc_pair ht hy, List.append_assoc, win, List.drop_zero, hy'.symm, List.take_left]

include hlen in
/-- **The support at an Introspect label.** -/
theorem support_introspect (w' w : Bool) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW (one_le_c hc) he hs).P.M (w', (.inr (.introspect, w), z)) a ≠ 0) :
    Complete.OkL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs
        (.inr (.introspect, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1 ∧
      Typed.readOK (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs
        (.inr (.introspect, w))
        (enc (P := QLD.Ty) (registerBits c lam n)
        ((2 ^ n) ^ lam)
        (srcSplitR V W hs) (.inr (.introspect, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1) := by
  have h1 := canonical_aux_ne_zero W RW he hs (one_le_c hc) w' (.introspect, w) z a ha
  obtain ⟨y', α, hb, hM⟩ := parsedCoreOp_support (family W hs) (decider W hs)
    (reindexed W RW hs) (false, w) _ h1
  have ha' : a = (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm (.pair y' α) := by
    rw [← hb]
    exact (Equiv.symm_apply_apply _ a).symm
  subst ha'
  have hM' : RW.P.M (w, pull (AuxiliaryProgram.firstEmbedding hs)
      ((reindexEquiv (numbering c lam n)).symm y')) α ≠ 0 := hM
  have hl := hlen _ α hM'
  have hα := α.2
  have hR := srcSplitR_symm W hs V (.introspect, w) (by simp) y'
  have hL := srcSplitL_symm W hs V (.introspect, w) (by simp) y'
  have hR' := lenOf_le W RW V hlen (w, pull (AuxiliaryProgram.firstEmbedding hs)
    ((reindexEquiv (numbering c lam n)).symm y')) false
  have hL' := lenOf_le W RW V hlen (w, pull (AuxiliaryProgram.firstEmbedding hs)
    ((reindexEquiv (numbering c lam n)).symm y')) true
  dsimp only at hl hR' hL'
  rw [encodeAnswer_pair hc]
  refine ⟨⟨_, α.1, rfl, length_toBits_symm _, ?_, ?_, ?_⟩, ?_⟩
  · dsimp only [Typed.sR, Typed.sL]; omega
  · dsimp only [Typed.sR, Typed.sL]; omega
  · dsimp only [Typed.sR, Typed.sL]; omega
  · have ht := take_enc_pair W hs V (Or.inl rfl) (length_toBits_symm y') (α := α.1)
      (t := (.introspect, w))
    refine ⟨?_, trivial, fun _ => ?_⟩
    · show Typed.sR (fieldBits c lam n) (selectorBits c lam n) V W hs _ _ +
          Typed.sL (fieldBits c lam n) (selectorBits c lam n) V W hs _ _ ≤ _
      rw [ht]
      dsimp only [Typed.sR, Typed.sL]
      omega
    · rw [ht]
      exact AuxiliaryDecision.sourceOutput_of_attained W hs w _
        (canonical_introspect W RW (one_le_c hc) he hs w' w z _ α ha)

theorem srcSplitR_sample_symm (w : Bool)
    (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    srcSplitR (Q := Typed.Q (fieldBits c lam n) (selectorBits c lam n)) V W hs (.sample, w)
      (toBits ((reindexEquiv (numbering c lam n)).symm y)) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs)
        ((AuxiliaryDecision.padded W hs w).eval ((reindexEquiv (numbering c lam n)).symm y))))
        false :=
  srcSplitR_sample W hs V w _

theorem srcSplitL_sample_symm (w : Bool)
    (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    srcSplitL (Q := Typed.Q (fieldBits c lam n) (selectorBits c lam n)) V W hs (.sample, w)
      (toBits ((reindexEquiv (numbering c lam n)).symm y)) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs)
        ((AuxiliaryDecision.padded W hs w).eval ((reindexEquiv (numbering c lam n)).symm y))))
        true :=
  srcSplitL_sample W hs V w _

include hlen in
/-- **The support at a Sample label.** -/
theorem support_sample (w' w : Bool) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW (one_le_c hc) he hs).P.M (w', (.inr (.sample, w), z)) a ≠ 0) :
    Complete.OkL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs
        (.inr (.sample, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1 ∧
      Typed.readOK (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs
        (.inr (.sample, w))
        (enc (P := QLD.Ty) (registerBits c lam n)
        ((2 ^ n) ^ lam) (srcSplitR V W hs) (.inr (.sample, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1) := by
  have h1 := canonical_aux_ne_zero W RW he hs (one_le_c hc) w' (.sample, w) z a ha
  obtain ⟨y', α, hb, hM⟩ := parsedCoreOp_support (family W hs) (decider W hs)
    (reindexed W RW hs) (true, w) _ h1
  have ha' : a = (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm (.pair y' α) := by
    rw [← hb]
    exact (Equiv.symm_apply_apply _ a).symm
  subst ha'
  have hM' : RW.P.M (w, pull (AuxiliaryProgram.firstEmbedding hs)
      ((reindexEquiv (numbering c lam n)).symm ((family W hs w).eval y'))) α ≠ 0 := hM
  have hM'' : RW.P.M (w, pull (AuxiliaryProgram.firstEmbedding hs)
      ((AuxiliaryDecision.padded W hs w).eval ((reindexEquiv (numbering c lam n)).symm y'))) α
        ≠ 0 := by
    rw [← family_eval_symm]
    exact hM'
  have hl := hlen _ α hM''
  have hα := α.2
  have hR := srcSplitR_sample_symm W hs V w y'
  have hL := srcSplitL_sample_symm W hs V w y'
  have hR' := lenOf_le W RW V hlen (w, pull (AuxiliaryProgram.firstEmbedding hs)
    ((AuxiliaryDecision.padded W hs w).eval ((reindexEquiv (numbering c lam n)).symm y'))) false
  have hL' := lenOf_le W RW V hlen (w, pull (AuxiliaryProgram.firstEmbedding hs)
    ((AuxiliaryDecision.padded W hs w).eval ((reindexEquiv (numbering c lam n)).symm y'))) true
  dsimp only at hl hR' hL'
  rw [encodeAnswer_pair hc]
  refine ⟨⟨_, α.1, rfl, length_toBits_symm _, ?_, ?_, ?_⟩, ?_⟩
  · dsimp only [Typed.sR, Typed.sL]; omega
  · dsimp only [Typed.sR, Typed.sL]; omega
  · dsimp only [Typed.sR, Typed.sL]; omega
  · have ht := take_enc_pair W hs V (Or.inr rfl) (length_toBits_symm y') (α := α.1)
      (t := (.sample, w))
    refine ⟨?_, trivial, fun h => absurd h (by simp)⟩
    show Typed.sR (fieldBits c lam n) (selectorBits c lam n) V W hs _ _ +
        Typed.sL (fieldBits c lam n) (selectorBits c lam n) V W hs _ _ ≤ _
    rw [ht]
    dsimp only [Typed.sR, Typed.sL]
    omega

theorem take_enc_read (w : Bool) {y yp α : BitStr} (hy : y.length = registerBits c lam n)
    (hyp : yp.length = registerBits c lam n) :
    win (enc (registerBits c lam n) ((2 ^ n) ^ lam) (srcSplitR V W hs) (P := QLD.Ty)
      (.inr (.read, w)) (tripleBits y yp α)) 0
        (Typed.Q (fieldBits c lam n) (selectorBits c lam n)) = y := by
  have hy' : y.length = Typed.Q (fieldBits c lam n) (selectorBits c lam n) := hy
  simp only [enc, tripleParts_tripleBits _ y yp α hy hyp]
  rw [List.append_assoc, win, List.drop_zero, hy'.symm, List.take_left]

theorem take_enc_hide (k : Fin 7) (w : Bool) {y yp x : BitStr}
    (hy : y.length = registerBits c lam n) (hyp : yp.length = registerBits c lam n) :
    win (enc (registerBits c lam n) ((2 ^ n) ^ lam) (srcSplitR V W hs) (P := QLD.Ty)
      (.inr (.hide k, w)) (tripleBits y yp x)) 0
        (Typed.Q (fieldBits c lam n) (selectorBits c lam n)) = y := by
  have hy' : y.length = Typed.Q (fieldBits c lam n) (selectorBits c lam n) := hy
  simp only [enc, tripleParts_tripleBits _ y yp x hy hyp]
  rw [win, List.drop_zero, hy'.symm, List.take_left]

theorem ofBits_toBits_symm (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    ofBits (Typed.Q (fieldBits c lam n) (selectorBits c lam n))
      (toBits ((reindexEquiv (numbering c lam n)).symm y)) =
      (reindexEquiv (numbering c lam n)).symm y :=
  ofBits_toBits _

include hlen in
/-- **The support at a Read label.** -/
theorem support_read (w' w : Bool) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW (one_le_c hc) he hs).P.M (w', (.inr (.read, w), z)) a ≠ 0) :
    Complete.OkL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs (.inr (.read, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1 ∧
      Typed.readOK (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs
        (.inr (.read, w))
        (enc (P := QLD.Ty) (registerBits c lam n)
        ((2 ^ n) ^ lam) (srcSplitR V W hs) (.inr (.read, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1) := by
  have hpre := canonical_prefixGuard W RW (one_le_c hc) he hs _ a ha
  have h1 := canonical_aux_ne_zero W RW he hs (one_le_c hc) w' (.read, w) z a ha
  obtain ⟨y', yp', α, hb, hM⟩ := parsedReadOp_support (family W hs) (decider W hs)
    (reindexed W RW hs) w (family_supported W hs w) _ h1
  have ha' : a =
      (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm (.read y' yp' α) := by
    rw [← hb]
    exact (Equiv.symm_apply_apply _ a).symm
  subst ha'
  have hM' : RW.P.M (w, pull (AuxiliaryProgram.firstEmbedding hs)
      ((reindexEquiv (numbering c lam n)).symm y')) α ≠ 0 := hM
  have hl := hlen _ α hM'
  have hα := α.2
  have hR := srcSplitR_symm W hs V (.read, w) (by simp) y'
  have hL := srcSplitL_symm W hs V (.read, w) (by simp) y'
  have hR' := lenOf_le W RW V hlen (w, pull (AuxiliaryProgram.firstEmbedding hs)
    ((reindexEquiv (numbering c lam n)).symm y')) false
  have hL' := lenOf_le W RW V hlen (w, pull (AuxiliaryProgram.firstEmbedding hs)
    ((reindexEquiv (numbering c lam n)).symm y')) true
  dsimp only at hl hR' hL'
  rw [encodeAnswer_read hc]
  refine ⟨⟨_, _, α.1, rfl, length_toBits_symm _, length_toBits_symm _, ?_, ?_, ?_⟩, ?_⟩
  · dsimp only [Typed.sR, Typed.sL]; omega
  · dsimp only [Typed.sR, Typed.sL]; omega
  · dsimp only [Typed.sR, Typed.sL]; omega
  · have ht := take_enc_read W hs V w (length_toBits_symm y') (length_toBits_symm yp')
      (α := α.1)
    refine ⟨?_, ?_, fun h => absurd h (by simp)⟩
    · show Typed.sR (fieldBits c lam n) (selectorBits c lam n) V W hs _ _ +
          Typed.sL (fieldBits c lam n) (selectorBits c lam n) V W hs _ _ ≤ _
      rw [ht]
      dsimp only [Typed.sR, Typed.sL]
      omega
    · show Typed.prefixOK (fieldBits c lam n) (selectorBits c lam n) W hs (.read, w) _
      rw [ht]
      show ∃ x, _ = _
      rw [ofBits_toBits_symm]
      exact hpre

/-- **The support at a Hide label.** -/
theorem support_hide (w' : Bool) (k : Fin 7) (w : Bool)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW (one_le_c hc) he hs).P.M (w', (.inr (.hide k, w), z)) a ≠ 0) :
    Complete.OkL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs
        (.inr (.hide k, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1 ∧
      Typed.readOK (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs
        (.inr (.hide k, w))
        (enc (P := QLD.Ty) (registerBits c lam n)
        ((2 ^ n) ^ lam) (srcSplitR V W hs) (.inr (.hide k, w))
        (CanonicalComplete.encodeAnswer c hc lam n a).1) := by
  have hpre := canonical_prefixGuard W RW (one_le_c hc) he hs _ a ha
  have h1 := canonical_aux_ne_zero W RW he hs (one_le_c hc) w' (.hide k, w) z a ha
  obtain ⟨y', yp', x', hb⟩ := parsedHideOp_support (family W hs) (decider W hs)
    (reindexed W RW hs) w k.val (family_supported W hs w) _ h1
  have ha' : a =
      (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm (.hide y' yp' x') := by
    rw [← hb]
    exact (Equiv.symm_apply_apply _ a).symm
  subst ha'
  rw [encodeAnswer_hide hc]
  refine ⟨⟨_, _, _, rfl, length_toBits_symm _, length_toBits_symm _, length_toBits_symm _⟩, ?_⟩
  have ht := take_enc_hide W hs V k w (length_toBits_symm y') (length_toBits_symm yp')
    (x := toBits ((reindexEquiv (numbering c lam n)).symm x'))
  refine ⟨trivial, ?_, fun h => absurd h (by simp)⟩
  show Typed.prefixOK (fieldBits c lam n) (selectorBits c lam n) W hs (.hide k, w) _
  rw [ht]
  show ∃ x, _ = _
  rw [ofBits_toBits_symm]
  exact hpre

/-- **The support at a Pauli label.** -/
theorem support_pauli (w' : Bool) (T : QLD.Ty) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW (one_le_c hc) he hs).P.M (w', (.inl T, z)) a ≠ 0) :
    Complete.OkL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs (.inl T)
        (CanonicalComplete.encodeAnswer c hc lam n a).1 ∧
      Typed.readOK (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs (.inl T)
        (enc (P := QLD.Ty) (registerBits c lam n)
        ((2 ^ n) ^ lam) (srcSplitR V W hs) (.inl T)
        (CanonicalComplete.encodeAnswer c hc lam n a).1) := by
  obtain ⟨x, rfl⟩ := canonical_pauli_shape W RW he hs (one_le_c hc) w' T z a ha
  have hf := canonical_pauli_format W RW (one_le_c hc) he hs w' T z x ha
  refine ⟨?_, trivial⟩
  show (QLD.PauliAnswerProgram.answerBits (field c lam n) x).length = _
  rw [length_answerBits _ _ x hf]
  cases T <;> rfl

include hlen in
/-- **The support of the honest strategy of the guarded game.** -/
theorem canonical_support (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n))) (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW (one_le_c hc) he hs).P.M q a ≠ 0) :
    Complete.OkL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs q.2.1
        (CanonicalComplete.encodeAnswer c hc lam n a).1 ∧
      Typed.readOK (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) V W hs q.2.1
        (enc (P := QLD.Ty) (registerBits c lam n) ((2 ^ n) ^ lam)
        (srcSplitR V W hs) q.2.1 (CanonicalComplete.encodeAnswer c hc lam n a).1) := by
  rcases q with ⟨w', p | ⟨t, w⟩, z⟩
  · exact support_pauli W RW he hs V hc w' p z a ha
  · cases t with
    | introspect => exact support_introspect W RW he hs V hc hlen w' w z a ha
    | sample => exact support_sample W RW he hs V hc hlen w' w z a ha
    | read => exact support_read W RW he hs V hc hlen w' w z a ha
    | hide k => exact support_hide W RW he hs V hc w' k w z a ha

end CanonicalSupport

section RawSupport

variable (U : ClockedUniversalMachine) (hW : W.IsBounded lam) (hn : 1 ≤ n)

include hlen in
/-- **`hsupp`: the honest strategy of the typed game charges only well-formed byte answers
whose registers satisfy the readable conditions.** -/
theorem raw_support (q : Bool × CL.Detyping.Question DecisionKernel.Label
      (Fin (PauliSampler.dimension c lam n))) (a : Verifier.Answers (outerBound c lam n))
    (ha : (raw W RW hc he U hW hn).P.M q a ≠ 0) :
    Complete.okT V W c lam (dim_le W c hc hW hn) q.2 a := by
  obtain ⟨a', rfl, ha'⟩ := mergeAnswersByQuestion_ne_zero
    (canonical W RW (one_le_c hc) he (dim_le W c hc hW hn))
    (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog) lam n).doubled
    (fun _ a => CanonicalComplete.encodeAnswer c hc lam n a) q a ha
  exact canonical_support W RW he (dim_le W c hc hW hn) V hc hlen q a' ha'

end RawSupport

end MIPRE.Tailored.Intro.HonestChain

/-! ## The input: a permutation strategy of the tailored verifier -/

namespace MIPRE.Tailored.Intro.HonestChain

open Cost MIPRE.CL

section Input

variable (V : TailoredVerifier 7) (U : UniversalMachine) {n T : ℕ}
  (hT : (V.tgame (2 ^ n)).maxLen ≤ T) (SV : PermStrategy (V.tgame (2 ^ n)).doubled)

/-- **The input's strategy** (`lem:zpc-pcc`): the measurements of a permutation strategy of the
doubled tailored game on answer strings (`PermStrategy.toSync`), extended by zero to the answers
of the normal form verifier `V.ofTNFV U`. -/
noncomputable def inputSync : SyncStrategy ((V.ofTNFV U).game (2 ^ n) T).doubled :=
  SV.toSync.extend _ (Verifier.Answers.castLE hT)

theorem inputSync_isPCC : (inputSync V U hT SV).IsPCC :=
  SV.toSync.isPCC_extend SV.isPCC_toSync _ _ fun _ _ => rfl

theorem inputSync_value (h : SV.value = 1) : (inputSync V U hT SV).value = 1 := by
  have hD : ∀ (p q : Bool × V.Questions (2 ^ n)) (a b : Verifier.Answers (V.tgame (2 ^ n)).maxLen),
      ((V.ofTNFV U).game (2 ^ n) T).doubled.D p q (Verifier.Answers.castLE hT a)
        (Verifier.Answers.castLE hT b) = (V.tgame (2 ^ n)).toGame.doubled.D p q a b := by
    intro p q a b
    change (if p.1 = false ∧ q.1 = true then ((V.ofTNFV U).game (2 ^ n) T).D p.2 q.2 _ _
      else false) = (if p.1 = false ∧ q.1 = true then (V.tgame (2 ^ n)).toGame.D p.2 q.2 a b
      else false)
    split_ifs
    · exact V.ofTNFV_game_D U hT p.2 q.2 a b
    · rfl
  exact (SV.toSync.value_extend _ (Verifier.Answers.castLE hT) (fun _ _ => rfl) hD).trans
    (by rw [SV.value_toSync, h])

theorem inputSync_M (p : Bool × V.Questions (2 ^ n)) :
    (inputSync V U hT SV).P.M p =
      Function.extend (Verifier.Answers.castLE hT) (SV.ansProj (V.tgame (2 ^ n)).maxLen p) 0 :=
  rfl

/-- **The input's answers have the tailored verifier's lengths.** -/
theorem inputSync_len (p : Bool × V.Questions (2 ^ n)) (a : Verifier.Answers T)
    (ha : (inputSync V U hT SV).P.M p a ≠ 0) :
    a.1.length = V.lenOf (2 ^ n) (toBits p.2) false + V.lenOf (2 ^ n) (toBits p.2) true := by
  rw [inputSync_M] at ha
  by_cases h : ∃ a₀, Verifier.Answers.castLE hT a₀ = a
  · obtain ⟨a₀, rfl⟩ := h
    rw [(Verifier.Answers.castLE hT).injective.extend_apply] at ha
    unfold PermStrategy.ansProj at ha
    split_ifs at ha with hl
    · exact hl
    · exact absurd rfl ha
  · exact absurd (Function.extend_apply' _ _ _ h) ha

/-- **The input's answer bits are signed permutations, diagonal below the readable length.** -/
theorem inputSync_bit (p : Bool × V.Questions (2 ^ n)) (j : ℕ) :
    IsXBit ((inputSync V U hT SV).P.M p) (fun a => a.1.getD j false) ∧
      (j < V.lenOf (2 ^ n) (toBits p.2) false →
        IsZBit ((inputSync V U hT SV).P.M p) (fun a => a.1.getD j false)) := by
  have hle := (V.tgame (2 ^ n)).len_le_maxLen p.2
  have e : bitObs ((inputSync V U hT SV).P.M p) (fun a => a.1.getD j false) =
      encObs (SV.ansProj (V.tgame (2 ^ n)).maxLen p)
        (fun a (_ : Fin 1) => a.1.getD j false) 0 := by
    rw [inputSync_M]
    exact bitObs_extend _ (Verifier.Answers.castLE hT).injective _
  have h2 : (V.tgame (2 ^ n)).doubled.len p = (V.tgame (2 ^ n)).len p.2 := rfl
  unfold IsXBit IsZBit
  rw [e]
  by_cases hj : j < (V.tgame (2 ^ n)).doubled.len p
  · rw [SV.encObs_ansProj_bit p hle _ 0 ⟨j, hj⟩ fun v => by
      simp [ofVec, List.getD_eq_getElem?_getD, hj]]
    exact ⟨SV.signedPerm p _, fun h => ⟨SV.signedPerm p _, SV.zAligned p _ h⟩⟩
  · rw [SV.encObs_ansProj_const p hle _ 0 false fun v =>
      List.getD_eq_default _ _ (by simp [ofVec]; omega)]
    exact ⟨isSignedPerm_bitSign_smul_one _, fun _ =>
      ⟨isSignedPerm_bitSign_smul_one _, isDiag_bitSign_smul_one _⟩⟩

end Input

/-! ## The honest strategy, in one statement -/

open MIPRE.Introspection MIPRE.Introspection.DecisionCompiler MIPRE.Introspection.SourceCompiler
open MIPRE.Introspection.PauliSamplerParameters

/-- **ZPC completeness of the tailored question reduction, the strategy** (P3c): for an input
normal form verifier `W` presenting the tailored verifier `V`, with a perfect PCC strategy `RW`
at index `2^n` whose answers have `V`'s lengths and whose answer bits are signed permutations,
diagonal below `V`'s readable length, the honest strategy `raw` of the reference verifier's
typed game is a perfect PCC strategy that charges only well-formed answers satisfying the
readable conditions (`hsupp`), whose bit observables along the padded layout are signed
permutations (`hperm`), diagonal at the readable bits (`hdiag`). -/
theorem honest_zpc (c : ℕ) (hc : 2 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (W : Verifier 7) (lam n : ℕ) (hW : W.IsBounded lam) (hn : 1 ≤ n)
    (RW : SyncStrategy (W.game (2 ^ n) ((2 ^ n) ^ lam)).doubled) (hRW : RW.IsPCC)
    (hv : RW.value = 1) (V : TailoredVerifier 7)
    (hlen : ∀ p a, RW.P.M p a ≠ 0 →
      a.1.length = V.lenOf (2 ^ n) (toBits p.2) false + V.lenOf (2 ^ n) (toBits p.2) true)
    (hX : ∀ p j, IsXBit (RW.P.M p) fun a => a.1.getD j false)
    (hZ : ∀ p j, j < V.lenOf (2 ^ n) (toBits p.2) false →
      IsZBit (RW.P.M p) fun a => a.1.getD j false) :
    ∃ R : SyncStrategy (rawGame c (one_le_c hc) he U (W.sampler.prog, W.decider.prog)
        lam n).doubled,
      R.IsPCC ∧ R.value = 1 ∧
      (∀ q a, ¬Complete.okT V W c lam (dim_le W c hc hW hn) q.2 a → R.P.M q a = 0) ∧
      (∀ q (i : ℕ), IsSignedPerm (pvmObs (R.P.M q) fun a =>
        bitSign ((Complete.encT V W c lam (dim_le W c hc hW hn) q.2 a).getD i false))) ∧
      (∀ q (i : ℕ),
        i < Typed.lenR (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) q.2.1 →
        (pvmObs (R.P.M q) fun a =>
          bitSign ((Complete.encT V W c lam (dim_le W c hc hW hn) q.2 a).getD i false)).IsDiag) :=
  ⟨raw W RW hc he U hW hn, raw_isPCC W RW hc he U hW hn hRW,
    raw_value W RW hc he U hW hn hRW hv,
    fun q a h => by
      by_contra ha
      exact h (raw_support W RW he V hc hlen U hW hn q a ha),
    fun q i => raw_isXBit W RW he V hc hlen hX hZ U hW hn q i,
    fun q i hi => raw_isDiag W RW he V hc hlen hX hZ U hW hn q i hi⟩

/-- **The input's strategy on the game of `V.ofTNFVT U0`**, the same game as that of
`V.ofTNFV U0` (`ofTNFVT_game`). -/
noncomputable def inputSyncT (V : TailoredVerifier 7) (U0 : UniversalMachine) {n T : ℕ}
    (hT : (V.tgame (2 ^ n)).maxLen ≤ T) (SV : PermStrategy (V.tgame (2 ^ n)).doubled) :
    SyncStrategy ((V.ofTNFVT U0).game (2 ^ n) T).doubled :=
  (inputSync V U0 hT SV).copy _

theorem inputSyncT_isPCC (V : TailoredVerifier 7) (U0 : UniversalMachine) {n T : ℕ}
    (hT : (V.tgame (2 ^ n)).maxLen ≤ T) (SV : PermStrategy (V.tgame (2 ^ n)).doubled) :
    (inputSyncT V U0 hT SV).IsPCC :=
  SyncStrategy.isPCC_copy (inputSync_isPCC V U0 hT SV) _ fun x y => by
    rw [TailoredVerifier.ofTNFVT_game]; rfl

theorem inputSyncT_value (V : TailoredVerifier 7) (U0 : UniversalMachine) {n T : ℕ}
    (hT : (V.tgame (2 ^ n)).maxLen ≤ T) (SV : PermStrategy (V.tgame (2 ^ n)).doubled)
    (h : SV.value = 1) : (inputSyncT V U0 hT SV).value = 1 :=
  ((inputSync V U0 hT SV).value_copy _ (fun x y => by rw [TailoredVerifier.ofTNFVT_game]; rfl)
    (fun x y a b => by rw [TailoredVerifier.ofTNFVT_game]; rfl)).trans
    (inputSync_value V U0 hT SV h)

/-- **ZPC completeness of the tailored question reduction, the instance** (P3c): the input
`T.ofTNFVT U0` of a tailored verifier `T` with a perfect ZPC strategy at index `2^n` whose
answers fit the cutoff `(2^n)^lam`. The honest strategy of the reference verifier's typed game
meets the hypotheses `hsupp`, `hperm`, `hdiag` of `Complete.hasPerfectZPC_tpresented`. -/
theorem honest_zpc_ofTNFVT (c : ℕ) (hc : 2 ≤ c) (he : Even c) (U : ClockedUniversalMachine)
    (T : TailoredVerifier 7) (U0 : UniversalMachine) (lam n : ℕ)
    (hW : (T.ofTNFVT U0).IsBounded lam) (hn : 1 ≤ n)
    (hT : (T.tgame (2 ^ n)).maxLen ≤ (2 ^ n) ^ lam) (hV : T.HasPerfectZPC (2 ^ n)) :
    ∃ R : SyncStrategy (rawGame c (one_le_c hc) he U
        ((T.ofTNFVT U0).sampler.prog, (T.ofTNFVT U0).decider.prog) lam n).doubled,
      R.IsPCC ∧ R.value = 1 ∧
      (∀ q a, ¬Complete.okT T (T.ofTNFVT U0) c lam (dim_le (T.ofTNFVT U0) c hc hW hn) q.2 a →
        R.P.M q a = 0) ∧
      (∀ q (i : ℕ), IsSignedPerm (pvmObs (R.P.M q) fun a =>
        bitSign ((Complete.encT T (T.ofTNFVT U0) c lam (dim_le (T.ofTNFVT U0) c hc hW hn) q.2
          a).getD i false))) ∧
      (∀ q (i : ℕ),
        i < Typed.lenR (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) q.2.1 →
        (pvmObs (R.P.M q) fun a =>
          bitSign ((Complete.encT T (T.ofTNFVT U0) c lam (dim_le (T.ofTNFVT U0) c hc hW hn) q.2
            a).getD i false)).IsDiag) := by
  obtain ⟨SV, hSV⟩ := hV
  exact honest_zpc c hc he U (T.ofTNFVT U0) lam n hW hn (inputSyncT T U0 hT SV)
    (inputSyncT_isPCC T U0 hT SV) (inputSyncT_value T U0 hT SV hSV) T
    (inputSync_len T U0 hT SV) (fun p j => (inputSync_bit T U0 hT SV p j).1)
    (fun p j => (inputSync_bit T U0 hT SV p j).2)

end MIPRE.Tailored.Intro.HonestChain

end
