/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import MIPRE.Background.Introspection.BinaryExtraction
public import MIPRE.Foundations.Introspection.PauliErrorParameters
public import MIPRE.Background.QLD.ModelSoundness

@[expose] public section

/-! # Actual QLD soundness witnesses in the introspection interface

QLD reads all wrongly formatted Pauli answers as zero. The interface used by
introspection instead records the genuine full-register answer effects. Legal
Pauli support identifies those effects exactly, including at the zero register.

Stated in a bipartite model (Phase 4 of `planning/mipco-track.md`): the Pauli basis test enters as
the hypothesis that it is sound in the model of the strategy (`QLD.SoundIn ω M`), in the shape and
at the error `qldErr` of `thm:qld`. Its universal constants are those of `qldErr` in closed form
(`QLD.exists_qldErr_le`), a fact about that function alone, so they are fixed once for every model.
The ancilla of the conclusion is an abstract ancilla model, which needs no numbering.
-/

noncomputable section
namespace MIPRE.Introspection.RestrictedSoundness
open Matrix Finset Classical
set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m d : ℕ} [NeZero m]

/-- Only the two full-register measurements require legal support. -/
def PauliSupported {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (P : QLD.Question F m → POVMIn (QLD.Answer F m d) R) : Prop :=
  ∀ W a, (QLD.Question.pauli W).fmtOk a = false → (P (.pauli W)).op a = 0

theorem rdPauliVec_op_of_supported {R : Type*} [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (P : QLD.Question F m → POVMIn (QLD.Answer F m d) R)
    (hP : PauliSupported P) (W : QLD.Bas) (x : QLD.Honest.Register F m) :
    ((P (.pauli W)).map QLD.rdPauliVec).op x = (P (.pauli W)).op (.pauliAns x) := by
  rw [POVMIn.map_op]
  refine Finset.sum_eq_single (s := univ.filter (fun a : QLD.Answer F m d => QLD.rdPauliVec a = x))
    (f := fun a => (P (.pauli W)).op a) (.pauliAns x) ?_ ?_
  · intro a ha hne
    have hx := (Finset.mem_filter.mp ha).2
    cases a <;> try exact hP W _ rfl
    simp only [QLD.rdPauliVec] at hx
    exact (hne (congrArg QLD.Answer.pauliAns hx)).elim
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim

/-- The stronger parsed support property furnished by the executable decoder. -/
def ParsedPauliSupported {V A J R : Type*} [Fintype V] [Fintype A] [Fintype J] [Ring R]
    [StarRing R] [PartialOrder R] [StarOrderedRing R] {ℓ : ℕ}
    (M : (QuestionType QLD.Ty ℓ × (J → ZMod 2)) →
      POVMIn (ParsedAnswer V A (QLD.Answer F m d)) R) : Prop :=
  ∀ W a, (M (.inl (.pauli W),0)).op a ≠ 0 → ∃ x, a = .pauli (.pauliAns x)

/-- Scalar completion has no malformed mass when the parsed measurement only
has genuine full-register outcomes. -/
theorem completePauliPOVM_invalid_of_supported {V A R : Type*} [Fintype V] [Fintype A] [Ring R]
    [StarRing R] [PartialOrder R] [StarOrderedRing R]
    (M : POVMIn (ParsedAnswer V A (QLD.Answer F m d)) R)
    (hM : ∀ a, M.op a ≠ 0 → ∃ x, a = .pauli (.pauliAns x))
    (W : QLD.Bas) (a : QLD.Answer F m d)
    (ha : (QLD.Question.pauli W).fmtOk a = false) :
    (completePauliPOVM (.val 0) M).op a = 0 := by
  rw [completePauliPOVM_mats]
  apply Finset.sum_eq_zero
  intro c hc
  by_contra hn
  obtain ⟨x,rfl⟩ := hM c hn
  have he : QLD.Answer.pauliAns x = a := (Finset.mem_filter.mp hc).2
  rw [← he] at ha
  cases ha

/-- Fix the universal QLD constants once, before any verifier parameters: those of the closed
form of `qldErr` (`QLD.exists_qldErr_le`). -/
def qldCoefficient : ℝ := QLD.exists_qldErr_le.choose
def qldExponent : ℝ := QLD.exists_qldErr_le.choose_spec.choose

theorem qldCoefficient_one_le : 1 ≤ qldCoefficient :=
  QLD.exists_qldErr_le.choose_spec.choose_spec.1

theorem qldExponent_pos : 0 < qldExponent :=
  QLD.exists_qldErr_le.choose_spec.choose_spec.2.1

theorem qldExponent_lt_one : qldExponent < 1 :=
  QLD.exists_qldErr_le.choose_spec.choose_spec.2.2.1

theorem qldErr_le_errShape (ε : ℝ) (m d q : ℕ) (hε : 0 ≤ ε) (hm : 1 ≤ m) (hd : 1 ≤ d)
    (hq : 2 ≤ q) :
    QLD.qldErr (min ε 1) m d q ≤ QLD.errShape qldCoefficient qldExponent ε m d q :=
  QLD.exists_qldErr_le.choose_spec.choose_spec.2.2.2 ε m d q hε hm hd hq

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ]

/-- The Pauli basis test's conclusion, read at the genuine full-register answers. -/
def FieldExtraction.ofQLD {M : BipartiteModel 𝒞 𝒜 ℬ} {hm : m ∣ Fintype.card F}
    {R : M.ProjStrat (QLD.qldGame (d := d) hm)} {δ : ℝ} (E : QLD.Extraction M hm R δ)
    (hA : PauliSupported R.PA) (hB : PauliSupported R.PB) : FieldExtraction M hm R δ where
  N := E.N
  Φ := E.Φ
  state_error := E.state_error
  X_error := by
    simpa only [rdPauliVec_op_of_supported R.PA hA, QLD.weylOf] using E.alice_error .X
  Z_error := by
    simpa only [rdPauliVec_op_of_supported R.PB hB, QLD.weylOf] using E.bob_error .Z

/-- **The Pauli basis test in the model of the strategy yields the genuine-answer extraction**,
at the universal constants, for every strategy supported on correctly formatted Pauli answers;
its ancilla model is dominated by the value model. -/
theorem fieldExtraction_exists {ω : ValueModel} {M : BipartiteModel 𝒞 𝒜 ℬ}
    (hQ : QLD.SoundIn ω M) (hm : m ∣ Fintype.card F) (hd : 1 ≤ d)
    (R : M.ProjStrat (QLD.qldGame (d := d) hm))
    (hA : PauliSupported R.PA) (hB : PauliSupported R.PB)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - R.value ≤ ε) :
    ∃ w : FieldExtraction M hm R
      (QLD.errShape qldCoefficient qldExponent ε m d (Fintype.card F)),
      ω.DominatesPOVM w.N.N := by
  have hv : 0 ≤ R.value := R.value_nonneg
  obtain ⟨E, hE⟩ := hQ hm hd R (le_min hε zero_le_one) (le_min hfail (by linarith))
  have hq : 2 ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    omega
  exact ⟨(FieldExtraction.ofQLD E hA hB).mono
    (qldErr_le_errShape ε m d (Fintype.card F) hε
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)) hd hq), hE⟩

/-- The degree-one specialization has exactly the error used by the canonical
parameter estimates, with no change to the QLD exponent or tail. -/
theorem degreeOne_fieldExtraction_exists {ω : ValueModel} {M : BipartiteModel 𝒞 𝒜 ℬ}
    (hQ : QLD.SoundIn ω M) (hm : m ∣ Fintype.card F)
    (R : M.ProjStrat (QLD.qldGame (d := 1) hm))
    (hA : PauliSupported R.PA) (hB : PauliSupported R.PB)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - R.value ≤ ε) :
    ∃ w : FieldExtraction M hm R
      (PauliErrorParameters.qldError qldCoefficient qldExponent m (Fintype.card F) ε),
      ω.DominatesPOVM w.N.N := by
  obtain ⟨w, hw⟩ := fieldExtraction_exists hQ hm le_rfl R hA hB hε hfail
  exact ⟨w.mono (le_of_eq (by
    simp only [QLD.errShape, PauliErrorParameters.qldError, Nat.cast_one, mul_one, neg_mul])), hw⟩

variable {t ℓ : ℕ} {A : Type} [Fintype A] [Nonempty A]

/-- **The extraction for the restricted strategy** (`lem:intro-pauli-extraction`). In a model where
the Pauli basis test is sound with `ω`, let a projective strategy of the binary parsed introspection
game fail with probability at most `ε`, and let its two full-register Pauli measurements have
outcomes only at full-register answers. Then its restriction to the Pauli basis game has an
extraction in binary coordinates at the error `δ_qld(Nε, m, d, q)` of the universal constants, with
`N` the number of ordered edges of the typed graph, and its ancilla model is dominated by `ω`: the
restriction fails with probability at most `Nε` (`PauliRestriction.strategy_failure_le`), keeps the
support (`completePauliPOVM_invalid_of_supported`), so the test applies at the genuine answers
(`fieldExtraction_exists`), and the register is relabelled as qubits along a self-dual basis
(`FieldExtraction.toBinary`). -/
theorem exists_extraction {ω : ValueModel} {M : BipartiteModel 𝒞 𝒜 ℬ} (hQ : QLD.SoundIn ω M)
    (hm : m ∣ Fintype.card F) (hd : 1 ≤ d) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (L : Bool → CL.CLFun (ZMod 2) (BinaryComplete.Coord m t) ℓ)
    (D : BinaryComplete.Seed m t → BinaryComplete.Seed m t → A → A → Bool)
    (S : M.ProjStrat (PauliRestriction.fullGame hm b L (BinaryComplete.project (d := d) b) D))
    (hA : ParsedPauliSupported S.PA) (hB : ParsedPauliSupported S.PB) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - S.value ≤ ε) :
    ∃ E : Extraction M hm b (restriction hm b L D S)
        (QLD.errShape qldCoefficient qldExponent (edgeCount ℓ * ε) m d (Fintype.card F)),
      ω.DominatesPOVM E.N.N := by
  have hA' : PauliSupported (restriction hm b L D S).PA := fun W a ha => by
    rw [PauliRestriction.strategy_pauli_A]
    exact completePauliPOVM_invalid_of_supported _ (hA W) W a ha
  have hB' : PauliSupported (restriction hm b L D S).PB := fun W a ha => by
    rw [PauliRestriction.strategy_pauli_B]
    exact completePauliPOVM_invalid_of_supported _ (hB W) W a ha
  have he : 0 ≤ edgeCount ℓ * ε := mul_nonneg (zero_le_one.trans (edgeCount_one_le ℓ)) hε
  obtain ⟨w, hw⟩ := fieldExtraction_exists hQ hm hd (restriction hm b L D S) hA' hB' he
    (PauliRestriction.strategy_failure_le hm b L (BinaryComplete.project b) D S _ _ hfail)
  exact ⟨w.toBinary b hb, hw⟩

end MIPRE.Introspection.RestrictedSoundness
end

end
