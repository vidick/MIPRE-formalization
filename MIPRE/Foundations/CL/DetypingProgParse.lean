/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgFinite
import MIPRE.Foundations.CL.Sampler
import MIPRE.Foundations.Cost.BinaryArithmetic

/-! # Total parsing for the detyping sampler

Raw trees are converted to canonical bit strings and binary naturals before
the fixed finite graph computation. Every parser is an actual polynomial-time
ambient program, including on malformed encodings.
-/

namespace MIPRE.CL.Detyping.Program

open Cost Cost.PolyTimeFun Polynomial

def rawList : Data → List Data
  | .nil => []
  | .cons a b => a :: rawList b

theorem encode_rawList (d : Data) : encode (rawList d) = d := by
  induction d with
  | nil => rfl
  | cons a b iha ihb => simpa only [rawList, encode_list_cons, encode_data] using congrArg (Data.cons a) ihb

def rawTruth : Data → Bool
  | .nil => false
  | .cons _ _ => true

noncomputable def rawTruthProg : PolyTimeFun Data Bool where
  toFun := rawTruth
  code := .elim 0 .nil (.const (encode true))
  closed := by simp [Prog.WellScoped]
  timeBound := C 4
  computes d := by
    cases d with
    | nil => exact ⟨2, by simp, Eval.elim_nil (by simp) (Eval.nil _)⟩
    | cons a b => exact ⟨4, by simp, Eval.elim_cons (a := a) (b := b) (by simp) (Eval.const _ _)⟩

noncomputable def readBits : PolyTimeFun Data BitStr :=
  (map rawTruthProg).comp (ofEncodeEq rawList encode_rawList)

theorem readBits_encode (l : BitStr) : readBits (encode l) = l := by
  change (rawList (encode l)).map rawTruth = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    change rawTruth (Data.ofBool b) :: (rawList (encode l)).map rawTruth = b :: l
    rw [ih]
    cases b <;> rfl

noncomputable def readNat : PolyTimeFun Data ℕ := bitsValue.comp readBits

theorem readNat_encode (n : ℕ) : readNat (encode n) = n := by
  change bitsVal (readBits (encode n.bits)) = n
  rw [readBits_encode, bitsVal_bits]

theorem rawTruthProg_encode_bool (b : Bool) : rawTruthProg (encode b) = b := by cases b <;> rfl

noncomputable def encoded {α : Type*} [SizedEncoding α] : PolyTimeFun α Data :=
  ofEncodeEq encode (fun _ => rfl)

@[simp] theorem encoded_apply {α : Type*} [SizedEncoding α] (a : α) : encoded a = encode a := rfl

abbrev Parsed := Data × ℕ × Bool × ℕ × BitStr × BitStr

noncomputable def parse : PolyTimeFun Data Parsed :=
  let q := treeTail
  let q1 := treeTail.comp q
  let q2 := treeTail.comp q1
  let q3 := treeTail.comp q2
  treeHead.pair ((readNat.comp (treeHead.comp q)).pair
    ((rawTruthProg.comp (treeHead.comp q1)).pair
      ((readNat.comp (treeHead.comp q2)).pair
        ((readBits.comp (treeHead.comp q3)).pair (readBits.comp (treeTail.comp q3))))))

theorem parse_query (n : ℕ) (q : Sampler.Query) :
    parse (encode (n, q)) =
      (encode n, q.toTuple.1, q.toTuple.2.1.toBool, q.toTuple.2.2.1,
        q.toTuple.2.2.2.1, q.toTuple.2.2.2.2) := by
  change parse (.cons (encode n) (encode q.toTuple)) = _
  rcases q.toTuple with ⟨k, w, j, u, y⟩
  simp only [parse, pair_apply, comp_apply,
    encode_prod, treeHead_cons, treeTail_cons,
    readNat_encode, readBits_encode]
  cases w <;> rfl

/-- The index is retained literally, including its binary encoding. -/
theorem parse_index (n q : Data) : (parse (.cons n q)).1 = n := rfl

instance vectorEncoding (d : ℕ) : SizedEncoding (Fin d → 𝔽₂) where
  encode v := encode (toBits v)
  decode d' := (decode d' : Option BitStr).map (ofBits d)
  decode_encode v := by simp [SizedEncoding.decode_encode]

/-- Reading a fixed number of graph bits is a finite collection of array reads. -/
noncomputable def readVector (d : ℕ) : PolyTimeFun BitStr (Fin d → 𝔽₂) :=
  PolyTimeFun.cast (listOf ((List.finRange d).map fun i => nthD false i.val)) (ofBits d) (by
    intro l
    change encode (toBits (ofBits d l)) =
      encode (listOf ((List.finRange d).map fun i => nthD false i.val) l)
    apply congrArg (encode : BitStr → Data)
    simp only [listOf_apply, List.map_map]
    change List.ofFn (fun i => decide (ofBits d l i = 1)) = _
    rw [List.ofFn_eq_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply, nthD_apply]
    change decide ((if l.getD i.val false then (1 : 𝔽₂) else 0) = 1) = _
    cases l.getD i.val false <;> decide)

@[simp] theorem readVector_apply (d : ℕ) (l : BitStr) : readVector d l = ofBits d l := rfl

end MIPRE.CL.Detyping.Program
