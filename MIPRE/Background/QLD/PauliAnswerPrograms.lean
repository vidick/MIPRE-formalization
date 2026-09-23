/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.TypeEncoding
import MIPRE.Foundations.Introspection.FieldAnswerParserProg

/-! # Faithful type-directed Pauli answer parsing

The exact question type is retained. Only the answer shape is shared by types
with identical formats. Counts are checked before any field table is allocated;
in particular the full Pauli count stays binary. The degree is supplied in unary
(and is the fixed constant one in the introspection application).
-/

noncomputable section
namespace MIPRE.QLD.PauliAnswerProgram
open Cost Cost.PolyTimeFun Polynomial SAT Introspection.FieldAnswerParser

def shape : Ty → ℕ
  | .point _ => 0
  | .aline _ => 1
  | .dline _ => 2
  | .pauli _ => 3
  | .pairB _ => 4
  | .pair => 5
  | .con _ => 6
  | .var _ => 4

def count (T : Ty) (m d : ℕ) : ℕ :=
  match T with
  | .point _ => 1
  | .aline _ => d + 1
  | .dline _ => m * d + 1
  | .pauli _ => 2 ^ m
  | .pairB _ | .var _ => 1
  | .pair => 2
  | .con _ => 3

def width (T : Ty) (k : ℕ) : ℕ :=
  match T with
  | .point _ | .aline _ | .dline _ | .pauli _ => k
  | _ => 1

private def flattenUnary : PolyTimeFun (List Unary) Unary :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

private def productUnary : PolyTimeFun (Unary × Unary) Unary :=
  flattenUnary.comp (replicate.comp (fst.pair snd))

private theorem productUnary_length (m d : Unary) :
    (productUnary (m, d)).length = m.length * d.length := by
  change (List.replicate m.length d).flatten.length = _
  induction m with
  | nil => simp
  | cons x xs ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

abbrev Input := Ty × Unary × Unary × Unary × BitStr

def kind : PolyTimeFun Input ℕ := (finiteFunction shape).comp fst
def dimension : PolyTimeFun Input Unary := fst.comp snd
def fieldWidth : PolyTimeFun Input Unary := fst.comp (snd.comp snd)
def degree : PolyTimeFun Input Unary := fst.comp (snd.comp (snd.comp snd))
def answer : PolyTimeFun Input BitStr := snd.comp (snd.comp (snd.comp snd))

def isKind (i : ℕ) : PolyTimeFun Input Bool := ap₂ ArrayProg.eqNat kind (const i)

def countProg : PolyTimeFun Input ℕ :=
  ite (isKind 0) (const 1)
    (ite (isKind 1) (inc.comp (unaryToBin.comp degree))
      (ite (isKind 2) (inc.comp (unaryToBin.comp
        (productUnary.comp (dimension.pair degree))))
        (ite (isKind 3) (scalePowerOfTwoProg.comp ((const 1).pair dimension))
          ((finiteFunction (fun T => count T 0 0)).comp fst))))

def widthProg : PolyTimeFun Input Unary :=
  ite ((finiteFunction (fun T => decide (shape T < 4))).comp fst)
    fieldWidth (const (unary 1))

theorem countProg_apply (T : Ty) (m k d : Unary) (bs : BitStr) :
    countProg (T, m, k, d, bs) = count T m.length d.length := by
  cases T <;> simp [countProg, isKind, kind, shape, count, degree, dimension,
    productUnary_length]

theorem widthProg_length (T : Ty) (m k d : Unary) (bs : BitStr) :
    (widthProg (T, m, k, d, bs)).length = width T k.length := by
  cases T <;> simp [widthProg, shape, fieldWidth, width]

def parser : PolyTimeFun Input (Bool × List BitStr) :=
  parserProg.comp (countProg.pair (widthProg.pair answer))

theorem parser_valid (T : Ty) (m k d : Unary) (bs : BitStr) :
    (parser (T, m, k, d, bs)).1 = true ↔
      0 < width T k.length ∧ bs.length = count T m.length d.length * width T k.length := by
  change readyProg (countProg _, widthProg _, answer _) = true ↔ _
  rw [readyProg_iff_length, countProg_apply, widthProg_length]
  rfl

/-- Every canonical payload is returned exactly, including the unit-width bit rows. -/
theorem parser_flatten (T : Ty) (m k d : Unary) (rows : List BitStr)
    (hk : 0 < width T k.length) (hn : rows.length = count T m.length d.length)
    (hw : ∀ row ∈ rows, row.length = width T k.length) :
    parser (T, m, k, d, rows.flatten) = (true, rows) := by
  have huw : widthProg (T, m, k, d, rows.flatten) = unary (width T k.length) := by
    rw [← unary_length (widthProg _), widthProg_length]
  change parserProg (countProg _, widthProg _, answer _) = _
  rw [countProg_apply, huw, ← hn]
  exact parserProg_flatten rows _ hk hw

theorem parser_runs (input : Input) :
    ∃ t ≤ parser.timeBound.eval (esize input),
      parser.code.Runs (encode input) (encode (parser input)) t := parser.computes input

end MIPRE.QLD.PauliAnswerProgram
end
