/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.PauliStageProg
import MIPRE.Foundations.Introspection.BinaryBlockProg

/-! # Packing the Pauli register into consecutive field rows -/

noncomputable section
namespace MIPRE.Introspection.PauliStageProgram
open Cost Cost.PolyTimeFun

def packRows : PolyTimeFun Fields (List BitStr) :=
  ap₂ append pointX (ap₂ append pointZ
    (seed.cons (ap₂ append direction (scalarX.cons (scalarZ.cons (const []))))))

@[simp] theorem packRows_apply (x z : List BitStr) (s : BitStr)
    (v : List BitStr) (rx rz : BitStr) :
    packRows (x, z, s, v, rx, rz) = x ++ (z ++ (s :: (v ++ [rx, rz]))) := rfl

def unpackRows : PolyTimeFun (Unary × List BitStr) Fields :=
  let x := ap₂ take snd fst
  let rest := ap₂ drop snd fst
  let z := ap₂ take rest fst
  let rest := ap₂ drop rest fst
  let s := (headD []).comp rest
  let rest := tail.comp rest
  let v := ap₂ take rest fst
  let rest := ap₂ drop rest fst
  pack x z s v ((headD []).comp rest) ((headD []).comp (tail.comp rest))

theorem unpackRows_packRows (m : ℕ) (x z : List BitStr) (s : BitStr)
    (v : List BitStr) (rx rz : BitStr)
    (hx : x.length = m) (hz : z.length = m) (hv : v.length = m) :
    unpackRows (unary m, packRows (x, z, s, v, rx, rz)) = (x, z, s, v, rx, rz) := by
  simp [unpackRows, pack, hx, hz, hv]

/-- Input to a row query: widths, type, stage, prefix rows, vector rows. -/
abbrev RowInput := Parameters × Tag × ℕ × List BitStr × List BitStr

def rowInput : PolyTimeFun RowInput Input :=
  let m := snd.comp (snd.comp fst)
  let u := fst.comp (snd.comp (snd.comp snd))
  let x := snd.comp (snd.comp (snd.comp snd))
  fst.pair ((fst.comp snd).pair ((ap₂ unpackRows m u).pair (ap₂ unpackRows m x)))

def linearRows : PolyTimeFun RowInput (List BitStr) :=
  packRows.comp (linear.comp ((fst.comp (snd.comp snd)).pair rowInput))

def marginalRows : PolyTimeFun RowInput (List BitStr) :=
  packRows.comp (marginal.comp ((fst.comp (snd.comp snd)).pair rowInput))

/-- Binary queries convert basis coordinates on entry and exit. -/
abbrev BinaryInput := Parameters × Tag × ℕ × BitStr × BitStr

def binaryInput : PolyTimeFun BinaryInput RowInput :=
  let k := fst.comp fst
  let m := snd.comp (snd.comp fst)
  let count := ap₂ append m (ap₂ append m (ap₂ append m (const (unary 3))))
  let u := BinaryBlock.decodeBlocksProg.comp
    (count.pair (k.pair (fst.comp (snd.comp (snd.comp snd)))))
  let x := BinaryBlock.decodeBlocksProg.comp
    (count.pair (k.pair (snd.comp (snd.comp (snd.comp snd)))))
  fst.pair ((fst.comp snd).pair ((fst.comp (snd.comp snd)).pair (u.pair x)))

def linearBits : PolyTimeFun BinaryInput BitStr :=
  BinaryBlock.encodeBlocksProg.comp ((fst.comp fst).pair (linearRows.comp binaryInput))

def marginalBits : PolyTimeFun BinaryInput BitStr :=
  BinaryBlock.encodeBlocksProg.comp ((fst.comp fst).pair (marginalRows.comp binaryInput))

theorem linearBits_runs (x : BinaryInput) :
    ∃ t ≤ linearBits.timeBound.eval (esize x),
      linearBits.code.Runs (encode x) (encode (linearBits x)) t := linearBits.computes x

theorem marginalBits_runs (x : BinaryInput) :
    ∃ t ≤ marginalBits.timeBound.eval (esize x),
      marginalBits.code.Runs (encode x) (encode (marginalBits x)) t := marginalBits.computes x

end MIPRE.Introspection.PauliStageProgram
end
