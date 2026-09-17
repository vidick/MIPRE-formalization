/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Circuit
import MIPRE.Foundations.Cost.Binary

/-!
# Boolean formulas and their circuits

A formula (`Fml`) is a tree of `and`, `or`, `not` over input bits and constants. Its
post-order flattening (`Fml.flattenAt`) is a circuit in which every gate is read at most once
(input bits are read through fresh `input` gates, which `Circuit.WellFormed` does not count),
so a formula's circuit is well-formed whatever the formula (`Fml.toCircuit_wellFormed`), and
computes the formula (`Fml.eval_toCircuit`). The describer of the succinct Cook–Levin
theorem is built as a formula, which confines the circuit bookkeeping to this file
(`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.SAT

open Cost

/-- Boolean formulas over input bits. -/
inductive Fml where
  | inp (i : ℕ)
  | const (b : Bool)
  | and (f g : Fml)
  | or (f g : Fml)
  | not (f : Fml)
  deriving DecidableEq, Repr, Inhabited

namespace Fml

/-- The value of a formula on the input bits `x`. -/
def eval (x : ℕ → Bool) : Fml → Bool
  | inp i => x i
  | const b => b
  | and f g => f.eval x && g.eval x
  | or f g => f.eval x || g.eval x
  | not f => !f.eval x

/-- The number of nodes: the number of gates of the circuit. -/
def size : Fml → ℕ
  | inp _ => 1
  | const _ => 1
  | and f g => f.size + g.size + 1
  | or f g => f.size + g.size + 1
  | not f => f.size + 1

theorem size_pos (f : Fml) : 0 < f.size := by cases f <;> simp [size]

/-- Every input bit read is below `n`. -/
def InputsLt (n : ℕ) : Fml → Prop
  | inp i => i < n
  | const _ => True
  | and f g => f.InputsLt n ∧ g.InputsLt n
  | or f g => f.InputsLt n ∧ g.InputsLt n
  | not f => f.InputsLt n

theorem InputsLt.mono {n m : ℕ} (h : n ≤ m) {f : Fml} (hf : f.InputsLt n) : f.InputsLt m := by
  induction f with
  | inp _ => exact lt_of_lt_of_le hf h
  | const _ => trivial
  | and _ _ ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | or _ _ ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | not _ ihf => exact ihf hf

/-! ## Formulas as data: the post-order serialization -/

/-- The nodes of the post-order (reverse Polish) serialization of a formula. -/
inductive Node where
  | inp (i : ℕ)
  | const (b : Bool)
  | and
  | or
  | not
  deriving DecidableEq, Repr, Inhabited

namespace Node

/-- Nodes as data: a unary tag and the payload. -/
def toData : Node → Data
  | inp i => .cons (.ofNat 0) (encode i)
  | const b => .cons (.ofNat 1) (encode b)
  | and => .cons (.ofNat 2) .nil
  | or => .cons (.ofNat 3) .nil
  | not => .cons (.ofNat 4) .nil

/-- Decoding nodes. -/
def ofData? : Data → Option Node
  | .cons .nil p => (decode p : Option ℕ).map inp
  | .cons (.cons .nil .nil) p => (decode p : Option Bool).map const
  | .cons (.cons .nil (.cons .nil .nil)) .nil => some and
  | .cons (.cons .nil (.cons .nil (.cons .nil .nil))) .nil => some or
  | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil)))) .nil => some not
  | _ => none

theorem ofData?_toData : ∀ nd : Node, ofData? nd.toData = some nd
  | inp i => by simp [toData, ofData?, Data.ofNat, SizedEncoding.decode_encode]
  | const b => by cases b <;> rfl
  | and => rfl
  | or => rfl
  | not => rfl

instance : SizedEncoding Node where
  encode := toData
  decode := ofData?
  decode_encode := ofData?_toData

theorem encode_inp (i : ℕ) : (encode (inp i) : Data) = .cons (.ofNat 0) (encode i) := rfl
theorem encode_const (b : Bool) : (encode (const b) : Data) = .cons (.ofNat 1) (encode b) := rfl
theorem encode_and : (encode and : Data) = .cons (.ofNat 2) .nil := rfl
theorem encode_or : (encode or : Data) = .cons (.ofNat 3) .nil := rfl
theorem encode_not : (encode not : Data) = .cons (.ofNat 4) .nil := rfl

end Node

/-- The post-order serialization of a formula. -/
def rpn : Fml → List Node
  | inp i => [.inp i]
  | const b => [.const b]
  | and f g => f.rpn ++ g.rpn ++ [.and]
  | or f g => f.rpn ++ g.rpn ++ [.or]
  | not f => f.rpn ++ [.not]

@[simp] theorem length_rpn : ∀ f : Fml, f.rpn.length = f.size
  | inp _ => rfl
  | const _ => rfl
  | and f g => by simp [rpn, size, length_rpn f, length_rpn g]; omega
  | or f g => by simp [rpn, size, length_rpn f, length_rpn g]; omega
  | not f => by simp [rpn, size, length_rpn f]

/-- One step of parsing a post-order serialization with a stack of formulas (a malformed
input leaves the stack unchanged). -/
def parseStep (st : List Fml) : Node → List Fml
  | .inp i => inp i :: st
  | .const b => const b :: st
  | .and => match st with
    | g :: f :: st => and f g :: st
    | _ => st
  | .or => match st with
    | g :: f :: st => or f g :: st
    | _ => st
  | .not => match st with
    | f :: st => not f :: st
    | _ => st

theorem foldl_parseStep_rpn : ∀ (f : Fml) (rest : List Node) (st : List Fml),
    (f.rpn ++ rest).foldl parseStep st = rest.foldl parseStep (f :: st)
  | inp _, rest, st => rfl
  | const _, rest, st => rfl
  | and f g, rest, st => by
    simp only [rpn, List.append_assoc]
    rw [foldl_parseStep_rpn f, foldl_parseStep_rpn g]
    rfl
  | or f g, rest, st => by
    simp only [rpn, List.append_assoc]
    rw [foldl_parseStep_rpn f, foldl_parseStep_rpn g]
    rfl
  | not f, rest, st => by
    simp only [rpn, List.append_assoc]
    rw [foldl_parseStep_rpn f]
    rfl

/-- Parsing a post-order serialization. -/
def parse (l : List Node) : Option Fml :=
  match l.foldl parseStep [] with
  | [f] => some f
  | _ => none

theorem parse_rpn (f : Fml) : parse f.rpn = some f := by
  unfold parse
  have := foldl_parseStep_rpn f [] []
  rw [List.append_nil] at this
  rw [this]
  rfl

/-- Formulas encode as their post-order serializations, so that a program builds a formula
by appending lists. -/
instance : SizedEncoding Fml where
  encode f := encode f.rpn
  decode d := (decode d : Option (List Node)).bind parse
  decode_encode f := by simp [SizedEncoding.decode_encode, parse_rpn]

theorem encode_fml (f : Fml) : (encode f : Data) = encode f.rpn := rfl

/-- The serialization, as a polynomial-time function (the encoding is the same). -/
noncomputable def rpnF : PolyTimeFun Fml (List Node) := PolyTimeFun.ofEncodeEq rpn fun _ => rfl

@[simp] theorem rpnF_apply (f : Fml) : rpnF f = f.rpn := rfl

/-- The constructors as polynomial-time functions. -/
noncomputable def inpF : PolyTimeFun ℕ Fml :=
  PolyTimeFun.cast (PolyTimeFun.cons (PolyTimeFun.tagged 0 Node.inp Node.encode_inp)
    (PolyTimeFun.const [])) inp fun _ => rfl

noncomputable def constF : PolyTimeFun Bool Fml :=
  PolyTimeFun.cast (PolyTimeFun.cons (PolyTimeFun.tagged 1 Node.const Node.encode_const)
    (PolyTimeFun.const [])) const fun _ => rfl

noncomputable def andF : PolyTimeFun (Fml × Fml) Fml :=
  PolyTimeFun.cast (PolyTimeFun.append.comp
    ((PolyTimeFun.append.comp ((rpnF.comp PolyTimeFun.fst).pair (rpnF.comp PolyTimeFun.snd))).pair
      (PolyTimeFun.const [Node.and])))
    (fun p => and p.1 p.2) fun _ => rfl

noncomputable def orF : PolyTimeFun (Fml × Fml) Fml :=
  PolyTimeFun.cast (PolyTimeFun.append.comp
    ((PolyTimeFun.append.comp ((rpnF.comp PolyTimeFun.fst).pair (rpnF.comp PolyTimeFun.snd))).pair
      (PolyTimeFun.const [Node.or])))
    (fun p => or p.1 p.2) fun _ => rfl

noncomputable def notF : PolyTimeFun Fml Fml :=
  PolyTimeFun.cast (PolyTimeFun.append.comp (rpnF.pair (PolyTimeFun.const [Node.not]))) not
    fun _ => rfl

@[simp] theorem inpF_apply (i : ℕ) : inpF i = inp i := rfl
@[simp] theorem constF_apply (b : Bool) : constF b = const b := rfl
@[simp] theorem andF_apply (p : Fml × Fml) : andF p = and p.1 p.2 := rfl
@[simp] theorem orF_apply (p : Fml × Fml) : orF p = or p.1 p.2 := rfl
@[simp] theorem notF_apply (f : Fml) : notF f = not f := rfl

/-! ## Flattening to a circuit -/

/-- The post-order gate list of a formula whose first gate is at position `base`: the output
gate is the last one, at `base + size - 1`. -/
def flattenAt (base : ℕ) : Fml → List Gate
  | inp i => [.input i]
  | const b => [.const b]
  | and f g => f.flattenAt base ++ g.flattenAt (base + f.size) ++
      [.and (base + f.size - 1) (base + f.size + g.size - 1)]
  | or f g => f.flattenAt base ++ g.flattenAt (base + f.size) ++
      [.or (base + f.size - 1) (base + f.size + g.size - 1)]
  | not f => f.flattenAt base ++ [.not (base + f.size - 1)]

@[simp] theorem length_flattenAt (base : ℕ) : ∀ f : Fml, (f.flattenAt base).length = f.size
  | inp _ => rfl
  | const _ => rfl
  | and f g => by
    simp only [flattenAt, size, List.length_append, List.length_singleton, length_flattenAt base f,
      length_flattenAt _ g]
  | or f g => by
    simp only [flattenAt, size, List.length_append, List.length_singleton, length_flattenAt base f,
      length_flattenAt _ g]
  | not f => by
    simp only [flattenAt, size, List.length_append, List.length_singleton, length_flattenAt base f]

/-- The circuit of a formula on `n` inputs. -/
def toCircuit (n : ℕ) (f : Fml) : Circuit := ⟨n, f.flattenAt 0⟩

@[simp] theorem toCircuit_inputs (n : ℕ) (f : Fml) : (f.toCircuit n).inputs = n := rfl

@[simp] theorem toCircuit_size (n : ℕ) (f : Fml) : (f.toCircuit n).size = f.size := by
  simp [toCircuit, Circuit.size]

/-- Every reference of the gate at position `k` of `flattenAt base f` lies in `[base, base + k)`. -/
theorem refs_flattenAt (base : ℕ) : ∀ (f : Fml) (k : ℕ) (hk : k < (f.flattenAt base).length),
    ∀ u ∈ (f.flattenAt base)[k].refs, base ≤ u ∧ u < base + k
  | inp _, k, hk, u, hu => by
    simp only [flattenAt, List.length_singleton] at hk
    obtain rfl : k = 0 := by omega
    simp [flattenAt, Gate.refs] at hu
  | const _, k, hk, u, hu => by
    simp only [flattenAt, List.length_singleton] at hk
    obtain rfl : k = 0 := by omega
    simp [flattenAt, Gate.refs] at hu
  | and f g, k, hk, u, hu => by
    have hf := length_flattenAt base f
    have hg := length_flattenAt (base + f.size) g
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt] at hk hu
    rw [List.getElem_append] at hu
    split at hu
    · rename_i h1
      rw [List.getElem_append] at hu
      split at hu
      · rename_i h2
        have := refs_flattenAt base f k (by omega) u hu
        omega
      · rename_i h2
        have := refs_flattenAt (base + f.size) g (k - (f.flattenAt base).length)
          (by simp only [List.length_append, hf, hg, List.length_singleton] at hk h1 ⊢; omega) u hu
        simp only [List.length_append, hf] at h1
        omega
    · rename_i h1
      simp only [List.length_append, hf, hg, List.length_singleton] at h1 hk
      have : k - (f.size + g.size) = 0 := by omega
      simp [this, Gate.refs] at hu
      rcases hu with rfl | rfl <;> omega
  | or f g, k, hk, u, hu => by
    have hf := length_flattenAt base f
    have hg := length_flattenAt (base + f.size) g
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt] at hk hu
    rw [List.getElem_append] at hu
    split at hu
    · rename_i h1
      rw [List.getElem_append] at hu
      split at hu
      · rename_i h2
        have := refs_flattenAt base f k (by omega) u hu
        omega
      · rename_i h2
        have := refs_flattenAt (base + f.size) g (k - (f.flattenAt base).length)
          (by simp only [List.length_append, hf, hg, List.length_singleton] at hk h1 ⊢; omega) u hu
        simp only [List.length_append, hf] at h1
        omega
    · rename_i h1
      simp only [List.length_append, hf, hg, List.length_singleton] at h1 hk
      have : k - (f.size + g.size) = 0 := by omega
      simp [this, Gate.refs] at hu
      rcases hu with rfl | rfl <;> omega
  | not f, k, hk, u, hu => by
    have hf := length_flattenAt base f
    have hfp := f.size_pos
    simp only [flattenAt] at hk hu
    rw [List.getElem_append] at hu
    split at hu
    · rename_i h1
      have := refs_flattenAt base f k (by omega) u hu
      omega
    · rename_i h1
      simp only [List.length_append, hf, List.length_singleton] at h1 hk
      have : k - f.size = 0 := by omega
      simp [this, Gate.refs] at hu
      omega

/-- The number of references to `u` in a gate list. -/
def refCount (gs : List Gate) (u : ℕ) : ℕ := (gs.map fun g => g.refs.count u).sum

@[simp] theorem refCount_nil (u : ℕ) : refCount [] u = 0 := rfl

@[simp] theorem refCount_append (gs hs : List Gate) (u : ℕ) :
    refCount (gs ++ hs) u = refCount gs u + refCount hs u := by
  simp [refCount]

@[simp] theorem refCount_singleton (g : Gate) (u : ℕ) : refCount [g] u = g.refs.count u := by
  simp [refCount]

theorem Circuit.fanout_eq_refCount (C : Circuit) (u : ℕ) : C.fanout u = refCount C.gates u := rfl

/-- A gate list whose references at position `k` are in `[base, base + k)` references no `u`
outside `[base, base + length - 1)`. -/
theorem refCount_eq_zero_of_forall (gs : List Gate) (u : ℕ)
    (h : ∀ (k : ℕ) (hk : k < gs.length), u ∉ gs[k].refs) : refCount gs u = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [refCount, List.map_cons, List.sum_cons]
    have h0 : u ∉ g.refs := h 0 (by simp)
    rw [List.count_eq_zero.mpr h0, Nat.zero_add]
    exact ih fun k hk => h (k + 1) (by simpa using hk)

theorem refCount_flattenAt_eq_zero (base : ℕ) (f : Fml) (u : ℕ)
    (hu : u < base ∨ base + f.size - 1 ≤ u) : refCount (f.flattenAt base) u = 0 := by
  apply refCount_eq_zero_of_forall
  intro k hk hmem
  have := refs_flattenAt base f k hk u hmem
  simp only [length_flattenAt] at hk
  omega

/-- Every gate of the circuit of a formula is read at most once, and the output gate is read
by no gate. -/
theorem refCount_flattenAt_le (base : ℕ) : ∀ (f : Fml) (u : ℕ), refCount (f.flattenAt base) u ≤ 1
  | inp _, u => by simp [flattenAt, Gate.refs]
  | const _, u => by simp [flattenAt, Gate.refs]
  | and f g, u => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt, refCount_append, refCount_singleton, Gate.refs]
    have hf := refCount_flattenAt_le base f u
    have hg := refCount_flattenAt_le (base + f.size) g u
    have hf0 := refCount_flattenAt_eq_zero base f u
    have hg0 := refCount_flattenAt_eq_zero (base + f.size) g u
    by_cases h1 : u = base + f.size - 1
    · rw [hf0 (by omega), hg0 (by omega)]
      subst h1
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    · by_cases h2 : u = base + f.size + g.size - 1
      · rw [hf0 (by omega), hg0 (by omega)]
        subst h2
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      · have : List.count u [base + f.size - 1, base + f.size + g.size - 1] = 0 := by
          simp [Ne.symm h1, Ne.symm h2]
        rw [this]
        by_cases h3 : u < base + f.size
        · rw [hg0 (by omega)]; omega
        · rw [hf0 (by omega)]; omega
  | or f g, u => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    simp only [flattenAt, refCount_append, refCount_singleton, Gate.refs]
    have hf := refCount_flattenAt_le base f u
    have hg := refCount_flattenAt_le (base + f.size) g u
    have hf0 := refCount_flattenAt_eq_zero base f u
    have hg0 := refCount_flattenAt_eq_zero (base + f.size) g u
    by_cases h1 : u = base + f.size - 1
    · rw [hf0 (by omega), hg0 (by omega)]
      subst h1
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
    · by_cases h2 : u = base + f.size + g.size - 1
      · rw [hf0 (by omega), hg0 (by omega)]
        subst h2
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      · have : List.count u [base + f.size - 1, base + f.size + g.size - 1] = 0 := by
          simp [Ne.symm h1, Ne.symm h2]
        rw [this]
        by_cases h3 : u < base + f.size
        · rw [hg0 (by omega)]; omega
        · rw [hf0 (by omega)]; omega
  | not f, u => by
    have hfp := f.size_pos
    simp only [flattenAt, refCount_append, refCount_singleton, Gate.refs]
    have hf := refCount_flattenAt_le base f u
    have hf0 := refCount_flattenAt_eq_zero base f u
    by_cases h1 : u = base + f.size - 1
    · rw [hf0 (by omega)]; subst h1; simp
    · have : List.count u [base + f.size - 1] = 0 := by simp [List.count_cons, Ne.symm h1]
      rw [this]; omega

theorem input_mem_flattenAt (base : ℕ) : ∀ (f : Fml) (i : ℕ), Gate.input i ∈ f.flattenAt base →
    ∃ j, inp j = f ∨ True := fun _ _ _ => ⟨0, Or.inr trivial⟩

theorem inputsLt_of_mem_flattenAt {n : ℕ} (base : ℕ) :
    ∀ (f : Fml), f.InputsLt n → ∀ i, Gate.input i ∈ f.flattenAt base → i < n
  | inp j, hf, i, hi => by simp [flattenAt] at hi; subst hi; exact hf
  | const _, _, i, hi => by simp [flattenAt] at hi
  | and f g, ⟨hf, hg⟩, i, hi => by
    simp only [flattenAt, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hi
    rcases hi with hi | hi
    · exact inputsLt_of_mem_flattenAt base f hf i hi
    · exact inputsLt_of_mem_flattenAt _ g hg i hi
  | or f g, ⟨hf, hg⟩, i, hi => by
    simp only [flattenAt, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hi
    rcases hi with hi | hi
    · exact inputsLt_of_mem_flattenAt base f hf i hi
    · exact inputsLt_of_mem_flattenAt _ g hg i hi
  | not f, hf, i, hi => by
    simp only [flattenAt, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hi
    exact inputsLt_of_mem_flattenAt base f hf i hi

/-- **The circuit of a formula is well-formed.** -/
theorem toCircuit_wellFormed {n : ℕ} (f : Fml) (hf : f.InputsLt n) : (f.toCircuit n).WellFormed where
  refs_lt k hk u hu := by have := (refs_flattenAt 0 f k hk u hu).2; omega
  inputs_lt i hi := inputsLt_of_mem_flattenAt 0 f hf i hi
  fanout_le u := (refCount_flattenAt_le 0 f u).trans (by omega)
  output_terminal := by
    show refCount (f.flattenAt 0) ((f.flattenAt 0).length - 1) = 0
    rw [length_flattenAt]
    exact refCount_flattenAt_eq_zero 0 f _ (Or.inr (by omega))
  nonempty := by
    intro h
    have h1 := length_flattenAt 0 f
    have h2 := f.size_pos
    have h' : f.flattenAt 0 = [] := h
    rw [h'] at h1
    simp only [List.length_nil] at h1
    omega

/-! ## Evaluation -/

/-- The value of a gate depends only on the gates up to it: appending gates changes nothing. -/
theorem Circuit.valueAt_append (n : ℕ) (gs post : List Gate) (x : ℕ → Bool) (k : ℕ)
    (hk : k < gs.length) :
    (Circuit.mk n (gs ++ post)).valueAt x k = (Circuit.mk n gs).valueAt x k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [Circuit.valueAt_eq, Circuit.valueAt_eq]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]
    congr 1
    congr 1
    funext i
    exact ih i i.isLt (lt_trans i.isLt hk)

/-- The values of the earlier gates, as read by a gate. -/
theorem Circuit.getD_ofFn_valueAt (C : Circuit) (x : ℕ → Bool) (k u : ℕ) (hu : u < k) :
    (List.ofFn fun i : Fin k => C.valueAt x i).getD u false = C.valueAt x u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hu]
  rfl

/-- The output gate of `flattenAt` placed after `pre` computes the formula, whatever follows. -/
theorem valueAt_flattenAt (n : ℕ) (x : ℕ → Bool) :
    ∀ (f : Fml) (pre post : List Gate),
      (Circuit.mk n (pre ++ f.flattenAt pre.length ++ post)).valueAt x (pre.length + f.size - 1) =
        f.eval x
  | inp i, pre, post => by
    simp only [flattenAt, size, Nat.add_sub_cancel]
    rw [Circuit.valueAt_eq]
    simp [List.getD_eq_getElem?_getD, eval, Gate.eval]
  | const b, pre, post => by
    simp only [flattenAt, size, Nat.add_sub_cancel]
    rw [Circuit.valueAt_eq]
    simp [List.getD_eq_getElem?_getD, eval, Gate.eval]
  | and f g, pre, post => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    have hf : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size - 1) = f.eval x := by
      have := valueAt_flattenAt n x f pre (g.flattenAt (pre.length + f.size) ++
        [Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.append_assoc] at this
      exact this
    have hg : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size + g.size - 1) = g.eval x := by
      have := valueAt_flattenAt n x g (pre ++ f.flattenAt pre.length)
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.length_append, length_flattenAt, List.append_assoc] at this
      exact this
    have hlist : pre ++ (and f g).flattenAt pre.length ++ post =
        pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
          ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))) := by
      simp [flattenAt]
    rw [hlist]
    rw [Circuit.valueAt_eq]
    simp only [size, List.getD_eq_getElem?_getD]
    have hk : pre.length + (f.size + g.size + 1) - 1 = pre.length + f.size + g.size := by omega
    rw [hk]
    have hget : (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))[
          pre.length + f.size + g.size]? =
        some (Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)) := by
      rw [List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega)]
      have h0 : pre.length + f.size + g.size - pre.length - (f.flattenAt pre.length).length -
          (g.flattenAt (pre.length + f.size)).length = 0 := by
        simp only [length_flattenAt]; omega
      rw [h0]; rfl
    rw [hget]
    simp only [Option.getD_some, Gate.eval, eval]
    rw [Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), Circuit.getD_ofFn_valueAt _ _ _ _ (by omega),
      hf, hg]
  | or f g, pre, post => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    have hf : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size - 1) = f.eval x := by
      have := valueAt_flattenAt n x f pre (g.flattenAt (pre.length + f.size) ++
        [Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.append_assoc] at this
      exact this
    have hg : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size + g.size - 1) = g.eval x := by
      have := valueAt_flattenAt n x g (pre ++ f.flattenAt pre.length)
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.length_append, length_flattenAt, List.append_assoc] at this
      exact this
    have hlist : pre ++ (or f g).flattenAt pre.length ++ post =
        pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
          ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))) := by
      simp [flattenAt]
    rw [hlist]
    rw [Circuit.valueAt_eq]
    simp only [size, List.getD_eq_getElem?_getD]
    have hk : pre.length + (f.size + g.size + 1) - 1 = pre.length + f.size + g.size := by omega
    rw [hk]
    have hget : (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))[
          pre.length + f.size + g.size]? =
        some (Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)) := by
      rw [List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega)]
      have h0 : pre.length + f.size + g.size - pre.length - (f.flattenAt pre.length).length -
          (g.flattenAt (pre.length + f.size)).length = 0 := by
        simp only [length_flattenAt]; omega
      rw [h0]; rfl
    rw [hget]
    simp only [Option.getD_some, Gate.eval, eval]
    rw [Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), Circuit.getD_ofFn_valueAt _ _ _ _ (by omega),
      hf, hg]
  | not f, pre, post => by
    have hfp := f.size_pos
    have hf : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++
        ([Gate.not (pre.length + f.size - 1)] ++ post)))).valueAt x (pre.length + f.size - 1) =
          f.eval x := by
      have := valueAt_flattenAt n x f pre ([Gate.not (pre.length + f.size - 1)] ++ post)
      simp only [List.append_assoc] at this
      exact this
    have hlist : pre ++ (not f).flattenAt pre.length ++ post =
        pre ++ (f.flattenAt pre.length ++ ([Gate.not (pre.length + f.size - 1)] ++ post)) := by
      simp [flattenAt]
    rw [hlist]
    rw [Circuit.valueAt_eq]
    simp only [size, List.getD_eq_getElem?_getD]
    have hk : pre.length + (f.size + 1) - 1 = pre.length + f.size := by omega
    rw [hk]
    have hget : (pre ++ (f.flattenAt pre.length ++ ([Gate.not (pre.length + f.size - 1)] ++ post)))[
          pre.length + f.size]? = some (Gate.not (pre.length + f.size - 1)) := by
      rw [List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega)]
      have h0 : pre.length + f.size - pre.length - (f.flattenAt pre.length).length = 0 := by
        simp only [length_flattenAt]; omega
      rw [h0]; rfl
    rw [hget]
    simp only [Option.getD_some, Gate.eval, eval]
    rw [Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), hf]

/-- **The circuit of a formula computes it.** -/
theorem eval_toCircuit (n : ℕ) (f : Fml) (x : ℕ → Bool) : (f.toCircuit n).eval x = f.eval x := by
  have h : (Circuit.mk n (f.flattenAt 0)).valueAt x (0 + f.size - 1) = f.eval x := by
    have := valueAt_flattenAt n x f [] []
    rwa [List.append_nil] at this
  rw [Nat.zero_add] at h
  unfold Circuit.eval
  have hne : f.flattenAt 0 ≠ [] := by
    intro h'
    have h1 := length_flattenAt 0 f
    rw [h'] at h1
    have h2 := f.size_pos
    simp only [List.length_nil] at h1
    omega
  simp only [toCircuit, hne, ↓reduceIte, length_flattenAt]
  exact h

theorem evalBits_toCircuit (n : ℕ) (f : Fml) (l : List Bool) :
    (f.toCircuit n).evalBits l = f.eval fun i => l.getD i false :=
  eval_toCircuit n f _

end Fml

end MIPRE.SAT
