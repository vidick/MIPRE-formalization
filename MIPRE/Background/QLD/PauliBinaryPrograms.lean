/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.QLD.PauliBooleanPrograms
import MIPRE.Background.QLD.PauliRowPrograms

/-! # From raw self-dual Pauli question bits to the actual decision program

The executable block decoder converts every binary coordinate to its canonical
Shoup representation and unpacks the fixed coordinate order. The resulting
typed payloads are then passed to the uniform Boolean decision program.
-/

noncomputable section
namespace MIPRE.QLD.PauliBinaryProgram
open Cost Cost.PolyTimeFun SAT PauliCL Introspection.PauliStageProgram
  Introspection.BinaryBlock

def coordinateCount : PolyTimeFun Parameters Unary :=
  let m := snd.comp snd
  ap₂ append m (ap₂ append m (ap₂ append m (const (unary 3))))

theorem coordinateCount_apply (k j m : Unary) :
    coordinateCount (k, j, m) = unary (3 * m.length + 3) := by
  have hm : m = unary m.length := (unary_length m).symm
  simp only [coordinateCount, ap₂_apply, comp_apply, append_apply,
    snd_apply, const_apply]
  rw [hm]
  simp only [unary, ← List.replicate_add, List.length_replicate]
  congr 1
  omega

def fieldsProg : PolyTimeFun (Parameters × BitStr) Fields :=
  let rows := decodeBlocksProg.comp ((coordinateCount.comp fst).pair
    ((fst.comp fst).pair snd))
  unpackRows.comp ((snd.comp (snd.comp fst)).pair rows)

theorem fieldsProg_binaryVector (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) [NeZero m] (x : Coord m → (shoupBinField k hk).carrier) :
    fieldsProg ((unary k, unary j, unary m),
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      fieldEncoding (shoupBinField k hk) x := by
  simp only [fieldsProg, comp_apply, pair_apply, fst_apply, snd_apply,
    coordinateCount_apply, length_unary, decodeBlocksProg_binaryVector k hk hodd,
    unpackRows_numberedRows]

/-- Every full-length bit string has exactly its inverse-basis field meaning. -/
theorem fieldsProg_ofBits (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) [NeZero m] (bs : BitStr) (hbs : bs.length = (3 * m + 3) * k) :
    fieldsProg ((unary k, unary j, unary m), bs) =
      fieldEncoding (shoupBinField k hk)
        ((binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd)).symm
          (CL.ofBits ((3 * m + 3) * k) bs)) := by
  simp only [fieldsProg, comp_apply, pair_apply, fst_apply, snd_apply,
    coordinateCount_apply, length_unary, decodeBlocksProg_ofBits k hk hodd bs hbs,
    unpackRows_numberedRows]

abbrev Payload := Ty × BitStr × BitStr
abbrev Input := Parameters × Payload × Payload

def endpointProg : PolyTimeFun (Parameters × Payload) PauliBooleanProgram.Payload :=
  (fst.comp snd).pair
    ((fieldsProg.comp (fst.pair (fst.comp (snd.comp snd)))).pair (snd.comp (snd.comp snd)))

def booleanInput : PolyTimeFun Input PauliBooleanProgram.Input :=
  fst.pair ((endpointProg.comp (fst.pair (fst.comp snd))).pair
    (endpointProg.comp (fst.pair (snd.comp snd))))

def program : PolyTimeFun Input Bool := PauliBooleanProgram.program.comp booleanInput

theorem booleanInput_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j m : ℕ) [NeZero m] (T U : Ty)
    (x y : Coord m → (shoupBinField k hk).carrier) (a b : BitStr) :
    booleanInput ((unary k, unary j, unary m),
      (T, CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x), a),
      (U, CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) y), b)) =
      ((unary k, unary j, unary m),
        (T, fieldEncoding (shoupBinField k hk) x, a),
        (U, fieldEncoding (shoupBinField k hk) y, b)) := by
  simp only [booleanInput, endpointProg, comp_apply, pair_apply, fst_apply, snd_apply,
    fieldsProg_binaryVector k hk hodd]

theorem program_runs (input : Input) :
    ∃ t ≤ program.timeBound.eval (esize input),
      program.code.Runs (encode input) (encode (program input)) t := program.computes input

end MIPRE.QLD.PauliBinaryProgram
end
