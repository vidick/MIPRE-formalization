/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.HonestChain
public import MIPRE.Background.Tailored.Intro.HonestPauli
public import MIPRE.Tailored.Intro.HonestAux
public import MIPRE.Tailored.Intro.LayoutBits
public import MIPRE.Tailored.Intro.Source

@[expose] public section

/-!
# The measurement of the honest strategy at a typed question

The honest strategy of the guarded game (`HonestChain.canonical`) measures, at a typed question
`(w, (p, z))`, the honest binary operator of the label `p` (`BinaryComplete.op`), relabelled to
the binary Weyl coordinates of the answers (`AuxiliaryQuotient.answerEquiv`) and conjugated by
the numbering of its space (`canonical_M`). This file reduces a bit of its outcome to a bit of
the honest Pauli measurement (`QLD.Honest.answerOp`, at a Pauli label) or of the honest auxiliary
measurement (`Honest.auxOp`, at an auxiliary label), whose bits
`MIPRE.Tailored.Intro.HonestPauli` and `MIPRE.Tailored.Intro.HonestAux` compute.
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
  (hc1 : 1 ≤ c) (he : Even c) (hs : W.sampler.dim (2 ^ n) ≤ registerBits c lam n)

/-- **The honest measurement at a typed question.** -/
theorem canonical_M (w : Bool) (p : QuestionType QLD.Ty 7)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (a : CanonicalComplete.Answer c lam n) :
    (canonical W RW hc1 he hs).P.M (w, (p, z)) a =
      (BinaryComplete.op (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
        (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
        (ExplicitGame.questionEquiv (permutation c lam n) (basis c he lam n) (p, z))
        (AuxiliaryQuotient.answerEquiv (numbering c lam n) a)).submatrix
        (Fintype.equivFin (BinaryComplete.Space (family W hs) (decider W hs)
          (reindexed W RW hs))).symm
        (Fintype.equivFin (BinaryComplete.Space (family W hs) (decider W hs)
          (reindexed W RW hs))).symm := rfl

/-- **A bit of the honest measurement at a typed question is a bit of the binary operator**, read
through the relabelling of the answers. -/
theorem isXBit_canonical (w : Bool) (p : QuestionType QLD.Ty 7)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (g : CanonicalComplete.Answer c lam n → Bool)
    (h : IsXBit (BinaryComplete.op (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
        (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
        (ExplicitGame.questionEquiv (permutation c lam n) (basis c he lam n) (p, z)))
      (g ∘ (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm)) :
    IsXBit ((canonical W RW hc1 he hs).P.M (w, (p, z))) g := by
  rw [show (canonical W RW hc1 he hs).P.M (w, (p, z)) = _ from
    funext (canonical_M W RW hc1 he hs w p z)]
  refine IsXBit.submatrix_equiv ?_ _
  unfold IsXBit at h ⊢
  exact (congrArg IsSignedPerm (bitObs_comp_equiv' _ _ _)).mpr h

theorem isZBit_canonical (w : Bool) (p : QuestionType QLD.Ty 7)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (g : CanonicalComplete.Answer c lam n → Bool)
    (h : IsZBit (BinaryComplete.op (d := 1) (family W hs) (decider W hs) (reindexed W RW hs)
        (divides c hc1 lam n) (basis c he lam n) (family_supported W hs)
        (ExplicitGame.questionEquiv (permutation c lam n) (basis c he lam n) (p, z)))
      (g ∘ (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm)) :
    IsZBit ((canonical W RW hc1 he hs).P.M (w, (p, z))) g := by
  rw [show (canonical W RW hc1 he hs).P.M (w, (p, z)) = _ from
    funext (canonical_M W RW hc1 he hs w p z)]
  refine IsZBit.submatrix_equiv ?_ _
  unfold IsZBit at h ⊢
  exact ⟨(congrArg IsSignedPerm (bitObs_comp_equiv' _ _ _)).mpr h.1,
    (congrArg Matrix.IsDiag (bitObs_comp_equiv' _ _ _)).mpr h.2⟩

/-! ## Pauli labels -/

theorem pauli_injective {V A PA : Type*} :
    Function.Injective (ParsedAnswer.pauli : PA → ParsedAnswer V A PA) :=
  fun x y h => by cases h; rfl

theorem parsedPauliOp_eq_extend {I V A PA : Type*} [Fintype I] [DecidableEq I]
    (M : PA → Matrix I I ℂ) :
    Honest.parsedPauliOp (V := V) (A := A) M = Function.extend ParsedAnswer.pauli M 0 := by
  funext a
  cases a with
  | pauli a =>
    exact (pauli_injective.extend_apply M 0 a).symm
  | _ =>
    rw [Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)]
    rfl

/-- The `i`-th bit of the tailored encoding of an answer of the guarded game. -/
def fbit (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (p : QuestionType QLD.Ty 7) (i : ℕ) (a : CanonicalComplete.Answer c lam n) : Bool :=
  (enc (registerBits c lam n) R splitR p (CanonicalComplete.encodeAnswer c hc lam n a).1).getD
    i false

theorem fbit_pauli (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (T : QLD.Ty) (i : ℕ) (a : QLD.Answer (field c lam n).carrier (registerPower c lam n) 1) :
    fbit (lam := lam) (n := n) hc R splitR (.inl T) i (.pauli a) =
      answerBit (fieldBits_pos c lam n) i a := rfl

/-- **At a Pauli label every bit is a signed permutation.** -/
theorem isXBit_canonical_pauli (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (w : Bool) (T : QLD.Ty) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (i : ℕ) :
    IsXBit ((canonical W RW hc1 he hs).P.M (w, (.inl T, z))) (fbit hc R splitR (.inl T) i) := by
  apply isXBit_canonical
  unfold IsXBit
  change IsSignedPerm (bitObs (Honest.parsedPauliOp _) _)
  rw [parsedPauliOp_eq_extend, bitObs_extend _ pauli_injective]
  exact ((isXBit_answerOp (fieldBits_pos c lam n) (divides c hc1 lam n) _ i).kronecker_one
    (Ω' := Fin (reindexed W RW hs).d)).submatrix_equiv _

/-- **At the `(Pauli, Z)` label every bit is a `±1` diagonal.** -/
theorem isZBit_canonical_pauliZ (hc : 2 ≤ c) (R : ℕ) (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (w : Bool) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (i : ℕ) :
    IsZBit ((canonical W RW hc1 he hs).P.M (w, (.inl (.pauli .Z), z)))
      (fbit hc R splitR (.inl (.pauli .Z)) i) := by
  apply isZBit_canonical
  unfold IsZBit
  change IsSignedPerm (bitObs (Honest.parsedPauliOp _) _) ∧ (bitObs (Honest.parsedPauliOp _) _).IsDiag
  rw [parsedPauliOp_eq_extend, bitObs_extend _ pauli_injective]
  exact ((isZBit_answerOp_pauliZ (fieldBits_pos c lam n) (divides c hc1 lam n) i).kronecker_one
    (Ω' := Fin (reindexed W RW hs).d)).submatrix_equiv _

/-! ## The input's answer bits

The honest strategy measures the input's strategy `RW` at the question read off the register.
What it needs of `RW`: its answer bits are signed permutations, diagonal below the readable
length the tailored verifier `V` assigns to the question. -/

section Input

variable (V : TailoredVerifier 7) (R : ℕ)

/-- The input's readable answer slot `j`: the `j`-th answer bit below the readable length, `0`
above. -/
theorem isZBit_input_readable
    (hZ : ∀ p j, j < V.lenOf (2 ^ n) (toBits p.2) false →
      IsZBit (RW.P.M p) fun a => a.1.getD j false) (p : Bool × W.Questions (2 ^ n)) (j : ℕ) :
    IsZBit (RW.P.M p) fun a =>
      if j < V.lenOf (2 ^ n) (toBits p.2) false then a.1.getD j false else false := by
  by_cases h : j < V.lenOf (2 ^ n) (toBits p.2) false
  · simp only [h, ↓reduceIte]
    exact hZ p j h
  · simp only [h, ↓reduceIte]
    exact isZBit_const (RW.isPVMIn p) false

theorem toBits_getD {Q : ℕ} (v : Fin Q → 𝔽₂) (j : ℕ) :
    (toBits v).getD j false = if h : j < Q then decide (v ⟨j, h⟩ = 1) else false := by
  split_ifs with h
  · simp [toBits, List.getD_eq_getElem?_getD, h]
  · simp [toBits, List.getD_eq_getElem?_getD, h]

/-- **The bits of an Introspect or Sample answer, at a fixed register, as bits of the input's
answer.** -/
theorem isXBit_pair_input {t : AuxType 7 × Bool} (ht : t.1 = .introspect ∨ t.1 = .sample)
    (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (hX : ∀ p j, IsXBit (RW.P.M p) fun a => a.1.getD j false)
    (hZ : ∀ p j, j < V.lenOf (2 ^ n) (toBits p.2) false →
      IsZBit (RW.P.M p) fun a => a.1.getD j false)
    (p : Bool × W.Questions (2 ^ n)) {yb : BitStr} (hyb : yb.length = registerBits c lam n)
    (hsp : splitR t yb = V.lenOf (2 ^ n) (toBits p.2) false)
    (hR : V.lenOf (2 ^ n) (toBits p.2) false ≤ R) (i : ℕ) :
    IsXBit (RW.P.M p) (fun α => (enc (registerBits c lam n) R splitR (P := QLD.Ty)
      (.inr t) (pairBits yb α.1)).getD i false) ∧
    (i < registerBits c lam n + R → IsZBit (RW.P.M p) (fun α => (enc (registerBits c lam n)
      R splitR (P := QLD.Ty) (.inr t) (pairBits yb α.1)).getD i false)) := by
  simp only [getD_enc_pair ht hyb (hsp ▸ hR), hsp]
  by_cases h1 : i < registerBits c lam n
  · simp only [h1, ↓reduceIte]
    exact ⟨(isZBit_const (RW.isPVMIn p) _).isXBit, fun _ => isZBit_const (RW.isPVMIn p) _⟩
  · by_cases h2 : i - registerBits c lam n < R
    · simp only [h1, h2, ↓reduceIte]
      exact ⟨(isZBit_input_readable W RW V hZ p _).isXBit,
        fun _ => isZBit_input_readable W RW V hZ p _⟩
    · simp only [h1, h2, ↓reduceIte]
      exact ⟨hX p _, fun h => absurd h (by omega)⟩

/-- **The bits of a Read answer outside its dual register, at a fixed register, as bits of the
input's answer.** -/
theorem isXBit_read_input {w : Bool} (splitR : AuxType 7 × Bool → BitStr → ℕ)
    (hX : ∀ p j, IsXBit (RW.P.M p) fun a => a.1.getD j false)
    (hZ : ∀ p j, j < V.lenOf (2 ^ n) (toBits p.2) false →
      IsZBit (RW.P.M p) fun a => a.1.getD j false)
    (p : Bool × W.Questions (2 ^ n)) {yb ypb : BitStr} (hyb : yb.length = registerBits c lam n)
    (hypb : ypb.length = registerBits c lam n)
    (hsp : splitR (.read, w) yb = V.lenOf (2 ^ n) (toBits p.2) false)
    (hR : V.lenOf (2 ^ n) (toBits p.2) false ≤ R) (i : ℕ)
    (hi : ¬(¬i < registerBits c lam n ∧ ¬i - registerBits c lam n < R ∧
      i - registerBits c lam n - R < registerBits c lam n)) :
    IsXBit (RW.P.M p) (fun α => (enc (registerBits c lam n) R splitR (P := QLD.Ty)
      (.inr (.read, w)) (tripleBits yb ypb α.1)).getD i false) ∧
    (i < registerBits c lam n + R → IsZBit (RW.P.M p) (fun α => (enc (registerBits c lam n)
      R splitR (P := QLD.Ty) (.inr (.read, w)) (tripleBits yb ypb α.1)).getD i false)) := by
  simp only [getD_enc_read hyb hypb (hsp ▸ hR), hsp]
  by_cases h1 : i < registerBits c lam n
  · simp only [h1, ↓reduceIte]
    exact ⟨(isZBit_const (RW.isPVMIn p) _).isXBit, fun _ => isZBit_const (RW.isPVMIn p) _⟩
  · by_cases h2 : i - registerBits c lam n < R
    · simp only [h1, h2, ↓reduceIte]
      exact ⟨(isZBit_input_readable W RW V hZ p _).isXBit,
        fun _ => isZBit_input_readable W RW V hZ p _⟩
    · have h3 : ¬i - registerBits c lam n - R < registerBits c lam n := fun h3 => hi ⟨h1, h2, h3⟩
      simp only [h1, h2, h3, ↓reduceIte]
      exact ⟨hX p _, fun h => absurd h (by omega)⟩

end Input

/-! ## Auxiliary labels -/

theorem isXBit_canonical_aux (w' : Bool) (t : AuxType 7 × Bool)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (g : CanonicalComplete.Answer c lam n → Bool)
    (h : IsXBit (Honest.auxOp (PA := QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
        (family W hs) (decider W hs) (reindexed W RW hs) (family_supported W hs) t)
      (g ∘ (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm)) :
    IsXBit ((canonical W RW hc1 he hs).P.M (w', (.inr t, z))) g :=
  isXBit_canonical W RW hc1 he hs w' (.inr t) z g h.kronecker_one

theorem isZBit_canonical_aux (w' : Bool) (t : AuxType 7 × Bool)
    (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂) (g : CanonicalComplete.Answer c lam n → Bool)
    (h : IsZBit (Honest.auxOp (PA := QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
        (family W hs) (decider W hs) (reindexed W RW hs) (family_supported W hs) t)
      (g ∘ (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm)) :
    IsZBit ((canonical W RW hc1 he hs).P.M (w', (.inr t, z))) g :=
  isZBit_canonical W RW hc1 he hs w' (.inr t) z g h.kronecker_one

section Labels

variable (V : TailoredVerifier 7) (hc : 2 ≤ c)
  (hlen : ∀ p a, RW.P.M p a ≠ 0 →
    a.1.length = V.lenOf (2 ^ n) (toBits p.2) false + V.lenOf (2 ^ n) (toBits p.2) true)
  (hX : ∀ p j, IsXBit (RW.P.M p) fun a => a.1.getD j false)
  (hZ : ∀ p j, j < V.lenOf (2 ^ n) (toBits p.2) false →
    IsZBit (RW.P.M p) fun a => a.1.getD j false)

include hlen in
/-- The input's readable length is at most the answer bound: some answer has a nonzero
projection, and it has the input's length. -/
theorem lenOf_le (p : Bool × W.Questions (2 ^ n)) (κ : Bool) :
    V.lenOf (2 ^ n) (toBits p.2) κ ≤ (2 ^ n) ^ lam := by
  obtain ⟨α, hα⟩ : ∃ α, RW.P.M p α ≠ 0 := by
    by_contra h
    push_neg at h
    have h1 := RW.P.normalized p
    simp only [h, Finset.sum_const_zero] at h1
    have : (0 : Matrix (Fin RW.d) (Fin RW.d) ℂ) ⟨0, RW.d_pos⟩ ⟨0, RW.d_pos⟩ =
        (1 : Matrix (Fin RW.d) (Fin RW.d) ℂ) ⟨0, RW.d_pos⟩ ⟨0, RW.d_pos⟩ := by rw [h1]
    simp at this
  have h1 := hlen p α hα
  have h2 := α.2
  cases κ <;> omega

theorem srcSplitR_eq (t : AuxType 7 × Bool) (ht : t.1 ≠ .sample)
    (y : Fin (registerBits c lam n) → 𝔽₂) :
    srcSplitR V W hs t (toBits y) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs) y)) false := by
  obtain ⟨t, w⟩ := t
  cases t <;> simp_all [srcSplitR, srcQuestion]

theorem srcSplitR_sample (w : Bool) (y : Fin (registerBits c lam n) → 𝔽₂) :
    srcSplitR V W hs (.sample, w) (toBits y) =
      V.lenOf (2 ^ n) (toBits (pull (AuxiliaryProgram.firstEmbedding hs)
        ((AuxiliaryDecision.padded W hs w).eval y))) false := by
  simp [srcSplitR, srcQuestion]

theorem reindexed_M (w : Bool) (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    (reindexed W RW hs).P.M (w, y) =
      RW.P.M (w, pull (AuxiliaryProgram.firstEmbedding hs)
        ((reindexEquiv (numbering c lam n)).symm y)) := rfl

theorem fbit_pair (splitR : AuxType 7 × Bool → BitStr → ℕ) (t : AuxType 7 × Bool) (i : ℕ)
    (y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n)) :
    (fun α : Verifier.Answers ((2 ^ n) ^ lam) => (fbit hc ((2 ^ n) ^ lam) splitR (.inr t) i ∘
      (AuxiliaryQuotient.answerEquiv (numbering c lam n)).symm) (.pair y α)) =
      fun α => (enc (registerBits c lam n) ((2 ^ n) ^ lam) splitR (P := QLD.Ty) (.inr t)
        (pairBits (toBits ((reindexEquiv (numbering c lam n)).symm y)) α.1)).getD i false := rfl

include hlen hX hZ in
/-- **The bits at an Introspect label.** -/
theorem bits_introspect (w' w : Bool) (z : Fin (PauliSampler.dimension c lam n) → 𝔽₂)
    (i : ℕ) :
    IsXBit ((canonical W RW (one_le_c hc) he hs).P.M (w', (.inr (.introspect, w), z)))
      (fbit hc ((2 ^ n) ^ lam) (srcSplitR V W hs) (.inr (.introspect, w)) i) ∧
    (i < registerBits c lam n + (2 ^ n) ^ lam →
      IsZBit ((canonical W RW (one_le_c hc) he hs).P.M (w', (.inr (.introspect, w), z)))
        (fbit hc ((2 ^ n) ^ lam) (srcSplitR V W hs) (.inr (.introspect, w)) i)) := by
  have key := fun y : BinaryComplete.Seed (registerPower c lam n) (fieldBits c lam n) =>
    isXBit_pair_input W RW V ((2 ^ n) ^ lam) (t := (.introspect, w)) (Or.inl rfl)
      (srcSplitR V W hs) hX hZ
      (w, pull (AuxiliaryProgram.firstEmbedding hs) ((reindexEquiv (numbering c lam n)).symm y))
      (yb := toBits ((reindexEquiv (numbering c lam n)).symm y)) (length_toBits _)
      (srcSplitR_eq W hs V _ (by simp) _) (lenOf_le W RW V hlen _ _) i
  refine ⟨isXBit_canonical_aux W RW _ he hs w' _ z _ ?_,
    fun hi => isZBit_canonical_aux W RW _ he hs w' _ z _ ?_⟩
  · change IsXBit (Honest.parsedCoreOp (PA := QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
      (family W hs) (decider W hs) (reindexed W RW hs) (false, w)) _
    refine isXBit_parsedCoreOp (family W hs) (decider W hs) (reindexed W RW hs) (false, w) _
      fun y => ?_
    rw [show Honest.originalQuestion (family W hs) (false, w) y = y from rfl, reindexed_M,
      fbit_pair hc]
    exact (key y).1
  · change IsZBit (Honest.parsedCoreOp (PA := QLD.Answer (field c lam n).carrier (registerPower c lam n) 1)
      (family W hs) (decider W hs) (reindexed W RW hs) (false, w)) _
    refine isZBit_parsedCoreOp (family W hs) (decider W hs) (reindexed W RW hs) (false, w) _
      fun y => ?_
    rw [show Honest.originalQuestion (family W hs) (false, w) y = y from rfl, reindexed_M,
      fbit_pair hc]
    exact (key y).2 hi

end Labels

end MIPRE.Tailored.Intro.HonestChain

end
