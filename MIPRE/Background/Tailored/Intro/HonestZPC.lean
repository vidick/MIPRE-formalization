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

/-! ## The support -/

section Support

/-- The readable condition that the input's answer fits the cutoff, at an auxiliary register
(the layout's `srcFits`). -/
def fitsI (t : AuxType 7 × Bool) (y : BitStr) : Prop :=
  match t.1 with
  | .hide _ => True
  | _ => srcSplitR V W hs t y + srcSplitL V W hs t y ≤ (2 ^ n) ^ lam

/-- The prefix condition of the kernel's prefix scan at the register of a Read or Hide answer. -/
def prefixI : AuxType 7 × Bool → BitStr → Prop
  | (.hide i, w), y => ∃ x, ((AuxiliaryDecision.padded W hs w).truncate i.val).eval x =
      (AuxiliaryDecision.padded W hs w).outputPrefix i.val (ofBits (registerBits c lam n) y)
  | (.read, w), y => ∃ x, ((AuxiliaryDecision.padded W hs w).truncate (7 - 1)).eval x =
      (AuxiliaryDecision.padded W hs w).outputPrefix (7 - 1) (ofBits (registerBits c lam n) y)
  | _, _ => True

/-- **The readable conditions at a label**, on the register of an encoded answer (its first
`Q` bits): at an auxiliary label, the input's answer fits, the prefix condition, and an
Introspect register is a source output. -/
def readOKI : DecisionKernel.Label → BitStr → Prop
  | .inl _, _ => True
  | .inr t, a => fitsI W hs V t (a.take (registerBits c lam n)) ∧
      prefixI W hs t (a.take (registerBits c lam n)) ∧
      (t.1 = .introspect →
        SourceCompiler.InSource (W.sampler.dim (2 ^ n)) (a.take (registerBits c lam n)))

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
  push_neg at hn
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

/-- The well-formedness of the layout at the instance's parameters. -/
abbrev OkI (u : DecisionKernel.Label) (bs : BitStr) : Prop :=
  OkLayout (registerBits c lam n) ((2 ^ n) ^ lam)
    (pauliLen (registerPower c lam n) (fieldBits c lam n)) (srcSplitR V W hs)
    (srcSplitL V W hs) u bs

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
    srcSplitR V W hs t (toBits ((reindexEquiv (numbering c lam n)).symm y)) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs)
        ((reindexEquiv (numbering c lam n)).symm y))) false :=
  srcSplitR_eq W hs V t ht _

theorem srcSplitL_symm (t : AuxType 7 × Bool) (ht : t.1 ≠ .sample)
    (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    srcSplitL V W hs t (toBits ((reindexEquiv (numbering c lam n)).symm y)) =
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
    (enc (registerBits c lam n) ((2 ^ n) ^ lam) (srcSplitR V W hs) (P := QLD.Ty) (.inr t)
      (pairBits y α)).take (registerBits c lam n) = y := by
  rw [enc_pair ht hy, List.append_assoc, List.take_left' hy]

include hlen in
/-- **The support at an Introspect label.** -/
theorem support_introspect (w' w : Bool) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (a : CanonicalComplete.Answer c lam n)
    (ha : (canonical W RW (one_le_c hc) he hs).P.M (w', (.inr (.introspect, w), z)) a ≠ 0) :
    OkI W hs V (.inr (.introspect, w)) (CanonicalComplete.encodeAnswer c hc lam n a).1 ∧
      readOKI W hs V (.inr (.introspect, w)) (enc (P := QLD.Ty) (registerBits c lam n) ((2 ^ n) ^ lam)
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
  · omega
  · omega
  · omega
  · have ht := take_enc_pair W hs V (Or.inl rfl) (length_toBits_symm y') (α := α.1)
      (t := (.introspect, w))
    refine ⟨?_, trivial, fun _ => ?_⟩
    · show srcSplitR V W hs _ _ + srcSplitL V W hs _ _ ≤ _
      rw [ht]
      omega
    · rw [ht]
      exact AuxiliaryDecision.sourceOutput_of_attained W hs w _
        (canonical_introspect W RW (one_le_c hc) he hs w' w z _ α ha)

end CanonicalSupport

end MIPRE.Tailored.Intro.HonestChain

end
