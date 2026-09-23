/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliBinaryInterface
import MIPRE.Foundations.Introspection.DecisionPreparation
import MIPRE.Foundations.Introspection.Types
import MIPRE.Foundations.Cost.FiniteEncoding
import MIPRE.Foundations.Introspection.AuxiliaryReadProgram

/-! # Canonical raw input parsing for the introspection decision kernel

Only the fixed finite question labels are decoded by a lookup table. The
source programs arrive as typed compiler metadata, never through a claimed
polynomial-time decoder for arbitrary program syntax.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram

abbrev Label := QuestionType QLD.Ty 7
abbrev Fields := ℕ × Label × BitStr × Label × BitStr × BitStr × BitStr
abbrev Input := DecisionPreparation.KernelInput

def labelKeys : List Data := (Finset.univ.image (encode : Label → Data)).toList
def labelOption (d : Data) : Option Label := if d ∈ labelKeys then decode d else none

private theorem table_not_mem (f : Data → Data) (xs : List Data) (d : Data)
    (h : d ∉ xs) : finiteTable f xs d = .nil := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [finiteTable, PolyTimeFun.ite_apply, ap₂_apply, treeEq_apply, id_apply, const_apply,
      h.1, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ih h.2

def labelDecoder : PolyTimeFun Data (Option Label) := by
  let table := finiteTable (fun d => encode (labelOption d)) labelKeys
  exact {
    toFun := labelOption
    code := table.code
    closed := table.closed
    timeBound := table.timeBound
    computes := fun d => by
      obtain ⟨t, ht, hr⟩ := table.computes d
      have he : table d = encode (labelOption d) := by
        by_cases h : d ∈ labelKeys
        · exact finiteTable_apply_of_mem _ _ _ h
        · rw [table_not_mem _ _ _ h]
          simp only [labelOption, if_neg h]
          rfl
      rw [he] at hr
      exact ⟨t, ht, hr⟩ }

def labelReader : PolyTimeFun Data Label :=
  (finiteFunction (fun t : Option Label => t.getD (.inl (.pauli .X)))).comp labelDecoder

@[simp] theorem labelReader_encode (t : Label) : labelReader (encode t) = t := by
  have ht : encode t ∈ labelKeys := by simp [labelKeys]
  simp [labelReader, labelDecoder, labelOption, ht, SizedEncoding.decode_encode]

def tailN : ℕ → PolyTimeFun Data Data
  | 0 => PolyTimeFun.id Data
  | n + 1 => treeTail.comp (tailN n)

def indexField : PolyTimeFun Data ℕ := readNat.comp treeHead
def leftLabelField : PolyTimeFun Data Label := labelReader.comp (treeHead.comp (tailN 1))
def leftQuestionField : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (tailN 2))
def rightLabelField : PolyTimeFun Data Label := labelReader.comp (treeHead.comp (tailN 3))
def rightQuestionField : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (tailN 4))
def leftAnswerField : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (tailN 5))
def rightAnswerField : PolyTimeFun Data BitStr := readBits.comp (tailN 6)

def readFields : PolyTimeFun Data Fields :=
  indexField.pair (leftLabelField.pair (leftQuestionField.pair
    (rightLabelField.pair (rightQuestionField.pair (leftAnswerField.pair rightAnswerField)))))

@[simp] theorem readFields_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    readFields (encode (n,T,x,U,y,a,b)) = (n,T,x,U,y,a,b) := by
  simp [readFields, indexField, leftLabelField, leftQuestionField, rightLabelField,
    rightQuestionField, leftAnswerField, rightAnswerField, tailN,
    encode_prod, readBits_encode, readNat_encode]

@[simp] theorem leftLabelField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    leftLabelField (encode (n,T,x,U,y,a,b)) = T :=
  congrArg (fun z : Fields => z.2.1) (readFields_encode n T U x y a b)

@[simp] theorem leftQuestionField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    leftQuestionField (encode (n,T,x,U,y,a,b)) = x :=
  congrArg (fun z : Fields => z.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem rightLabelField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    rightLabelField (encode (n,T,x,U,y,a,b)) = U :=
  congrArg (fun z : Fields => z.2.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem rightQuestionField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    rightQuestionField (encode (n,T,x,U,y,a,b)) = y :=
  congrArg (fun z : Fields => z.2.2.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem leftAnswerField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    leftAnswerField (encode (n,T,x,U,y,a,b)) = a :=
  congrArg (fun z : Fields => z.2.2.2.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem rightAnswerField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    rightAnswerField (encode (n,T,x,U,y,a,b)) = b :=
  congrArg (fun z : Fields => z.2.2.2.2.2.2) (readFields_encode n T U x y a b)

def raw : PolyTimeFun Input Data := fst
def metadata : PolyTimeFun Input DecisionPreparation.Metadata := fst.comp snd
def resourceTail : PolyTimeFun Input (Unary × ℕ × PauliSamplerParameters.Parameters × ℕ × ℕ) :=
  snd.comp snd
def budget : PolyTimeFun Input Unary := fst.comp resourceTail
def sourceIndex : PolyTimeFun Input ℕ := fst.comp (snd.comp resourceTail)
def parameters : PolyTimeFun Input PauliSamplerParameters.Parameters :=
  fst.comp (snd.comp (snd.comp resourceTail))
def registerWidth : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp (snd.comp resourceTail)))
def originalCutoff : PolyTimeFun Input ℕ := snd.comp (snd.comp (snd.comp (snd.comp resourceTail)))
def sourceSampler : PolyTimeFun Input Prog := fst.comp (fst.comp metadata)
def sourceDecider : PolyTimeFun Input Prog := snd.comp (fst.comp metadata)

def leftType : PolyTimeFun Input Label := leftLabelField.comp raw
def rightType : PolyTimeFun Input Label := rightLabelField.comp raw
def leftQuestion : PolyTimeFun Input BitStr := leftQuestionField.comp raw
def rightQuestion : PolyTimeFun Input BitStr := rightQuestionField.comp raw
def leftBits : PolyTimeFun Input BitStr := leftAnswerField.comp raw
def rightBits : PolyTimeFun Input BitStr := rightAnswerField.comp raw

def canonical : PolyTimeFun Input Bool := equal raw (encoded.comp (readFields.comp raw))

theorem canonical_encode (M : DecisionPreparation.Metadata) (clock : Unary) (N Q R : ℕ)
    (p : PauliSamplerParameters.Parameters) (n : ℕ) (T U : Label) (x y a b : BitStr) :
    canonical (encode (n,T,x,U,y,a,b),M,clock,N,p,Q,R) = true := by
  simp [canonical, raw, readFields_encode, equal_iff]

end MIPRE.Introspection.DecisionKernel
end
