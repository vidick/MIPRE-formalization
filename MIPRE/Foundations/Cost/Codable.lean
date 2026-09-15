/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Loops
import Mathlib.Computability.Primrec.List
import Mathlib.Logic.Denumerable

/-!
# `Data` as a primcodable type

`Data` is denumerable through Cantor pairing (`Data.encodeNat`/`Data.decodeNat`), hence
`Primcodable`, with primitive recursive constructor, projections, a tree-recursion
principle (`Data.primrec_recD`), unary numerals, list indexing and the decoders of bit
strings. This is the interface between the ambient model and Mathlib's computability
(`Cost/Partrec.lean`): everything the model manipulates is `Data` — programs included,
through `Prog.toData` — so no separate encoding of `Prog` is needed.
-/

namespace MIPRE.Cost

namespace Data

/-! ## `Data ≃ ℕ` -/

/-- `Data` as natural numbers through Cantor pairing: `nil ↦ 0`, `cons a b ↦ pair a b + 1`. -/
def encodeNat : Data → ℕ
  | nil => 0
  | cons a b => Nat.pair (encodeNat a) (encodeNat b) + 1

/-- The inverse of `encodeNat`. -/
def decodeNat : ℕ → Data
  | 0 => nil
  | n + 1 => cons (decodeNat (Nat.unpair n).1) (decodeNat (Nat.unpair n).2)
decreasing_by
  all_goals
    try simp_wf
    first
    | exact Nat.lt_succ_of_le (Nat.unpair_left_le _)
    | exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

@[simp] theorem encodeNat_nil : encodeNat nil = 0 := rfl

@[simp] theorem encodeNat_cons (a b : Data) :
    encodeNat (cons a b) = Nat.pair (encodeNat a) (encodeNat b) + 1 := rfl

@[simp] theorem decodeNat_zero : decodeNat 0 = nil := by rw [decodeNat]

@[simp] theorem decodeNat_succ (n : ℕ) :
    decodeNat (n + 1) = cons (decodeNat (Nat.unpair n).1) (decodeNat (Nat.unpair n).2) := by
  rw [decodeNat]

@[simp] theorem decodeNat_encodeNat : ∀ d : Data, decodeNat (encodeNat d) = d
  | nil => by simp
  | cons a b => by
    rw [encodeNat_cons, decodeNat_succ, Nat.unpair_pair]
    simp [decodeNat_encodeNat a, decodeNat_encodeNat b]

@[simp] theorem encodeNat_decodeNat (n : ℕ) : encodeNat (decodeNat n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [decodeNat_succ, encodeNat_cons, ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
        ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le n)), Nat.pair_unpair]

/-- `Data ≃ ℕ`. -/
def equivNat : Data ≃ ℕ where
  toFun := encodeNat
  invFun := decodeNat
  left_inv := decodeNat_encodeNat
  right_inv := encodeNat_decodeNat

instance : Denumerable Data := Denumerable.mk' equivNat

theorem encode_eq (d : Data) : Encodable.encode d = encodeNat d := rfl

theorem ofNat_eq (n : ℕ) : Denumerable.ofNat Data n = decodeNat n := by
  have h := Denumerable.decode_eq_ofNat Data n
  rw [show (Encodable.decode n : Option Data) = some (decodeNat n) from rfl] at h
  exact (Option.some.inj h).symm

/-! ## Primitive recursive constructor and projections -/

theorem primrec_decodeNat : Primrec decodeNat := (Primrec.ofNat Data).of_eq ofNat_eq

theorem primrec_cons : Primrec₂ Data.cons := by
  refine Primrec₂.encode_iff.1 ?_
  refine (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
    (Primrec.encode.comp Primrec.snd))).of_eq ?_
  rintro ⟨a, b⟩
  rfl

/-- The head of a pair (`nil` on `nil`). -/
def left : Data → Data
  | nil => nil
  | cons a _ => a

/-- The tail of a pair (`nil` on `nil`). -/
def right : Data → Data
  | nil => nil
  | cons _ b => b

@[simp] theorem left_nil : left nil = nil := rfl
@[simp] theorem left_cons (a b : Data) : left (cons a b) = a := rfl
@[simp] theorem right_nil : right nil = nil := rfl
@[simp] theorem right_cons (a b : Data) : right (cons a b) = b := rfl

theorem encodeNat_left (d : Data) : encodeNat (left d) =
    if encodeNat d = 0 then 0 else (Nat.unpair (Nat.pred (encodeNat d))).1 := by
  cases d <;> simp [Nat.unpair_pair]

theorem encodeNat_right (d : Data) : encodeNat (right d) =
    if encodeNat d = 0 then 0 else (Nat.unpair (Nat.pred (encodeNat d))).2 := by
  cases d <;> simp [Nat.unpair_pair]

theorem primrec_left : Primrec left := by
  refine Primrec.encode_iff.1 ?_
  refine (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.encode (Primrec.const 0))
    (Primrec.const 0)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.encode)))).of_eq ?_
  intro d
  exact (encodeNat_left d).symm

theorem primrec_right : Primrec right := by
  refine Primrec.encode_iff.1 ?_
  refine (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.encode (Primrec.const 0))
    (Primrec.const 0)
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.encode)))).of_eq ?_
  intro d
  exact (encodeNat_right d).symm

/-- Case analysis on `Data`, primitive recursively. -/
theorem primrec_ite_nil {α σ : Type*} [Primcodable α] [Primcodable σ] {f : α → Data}
    {g : α → σ} {h : α → Data → Data → σ} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec fun p : α × Data × Data => h p.1 p.2.1 p.2.2) :
    Primrec fun a => if f a = nil then g a else h a (left (f a)) (right (f a)) :=
  Primrec.ite (PrimrecRel.comp Primrec.eq hf (Primrec.const nil)) hg
    (hh.comp (Primrec.pair Primrec.id
      (Primrec.pair (primrec_left.comp hf) (primrec_right.comp hf))))

/-! ## Tree recursion -/

/-- Structural recursion on `Data` with a first-order result. -/
def recD {σ : Type*} (base : σ) (step : Data → Data → σ → σ → σ) : Data → σ
  | nil => base
  | cons a b => step a b (recD base step a) (recD base step b)

@[simp] theorem recD_nil {σ : Type*} (base : σ) (step : Data → Data → σ → σ → σ) :
    recD base step nil = base := rfl

@[simp] theorem recD_cons {σ : Type*} (base : σ) (step : Data → Data → σ → σ → σ)
    (a b : Data) : recD base step (cons a b) = step a b (recD base step a) (recD base step b) :=
  rfl

private theorem getD_range_map {σ : Type*} [Inhabited σ] (F : ℕ → σ) {n i : ℕ} (hi : i < n) :
    ((List.range n).map F).getD i default = F i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Tree recursion is primitive recursive (through the pairing encoding, structural
recursion on `Data` is strong recursion on `ℕ`). -/
theorem primrec_recD {σ : Type*} [Primcodable σ] [Inhabited σ] (base : σ)
    (step : Data → Data → σ → σ → σ)
    (hstep : Primrec fun p : (Data × Data) × σ × σ => step p.1.1 p.1.2 p.2.1 p.2.2) :
    Primrec (recD base step) := by
  have hlen : Primrec fun p : Unit × List σ => p.2.length := Primrec.list_length.comp Primrec.snd
  have hidx : Primrec fun p : Unit × List σ => Nat.unpair (Nat.pred p.2.length) :=
    Primrec.unpair.comp (Primrec.pred.comp hlen)
  have h1 : Primrec fun p : Unit × List σ => decodeNat (Nat.unpair (Nat.pred p.2.length)).1 :=
    primrec_decodeNat.comp (Primrec.fst.comp hidx)
  have h2 : Primrec fun p : Unit × List σ => decodeNat (Nat.unpair (Nat.pred p.2.length)).2 :=
    primrec_decodeNat.comp (Primrec.snd.comp hidx)
  have h3 : Primrec fun p : Unit × List σ =>
      p.2.getD (Nat.unpair (Nat.pred p.2.length)).1 default :=
    (Primrec.list_getD default).comp Primrec.snd (Primrec.fst.comp hidx)
  have h4 : Primrec fun p : Unit × List σ =>
      p.2.getD (Nat.unpair (Nat.pred p.2.length)).2 default :=
    (Primrec.list_getD default).comp Primrec.snd (Primrec.snd.comp hidx)
  have hg' : Primrec₂ fun (_ : Unit) (l : List σ) =>
      if l.length = 0 then base else
        step (decodeNat (Nat.unpair (Nat.pred l.length)).1)
          (decodeNat (Nat.unpair (Nat.pred l.length)).2)
          (l.getD (Nat.unpair (Nat.pred l.length)).1 default)
          (l.getD (Nat.unpair (Nat.pred l.length)).2 default) :=
    Primrec.ite (PrimrecRel.comp Primrec.eq hlen (Primrec.const 0)) (Primrec.const base)
      (hstep.comp (Primrec.pair (Primrec.pair h1 h2) (Primrec.pair h3 h4)))
  have hg : Primrec₂ fun (_ : Unit) (l : List σ) =>
      some (if l.length = 0 then base else
        step (decodeNat (Nat.unpair (Nat.pred l.length)).1)
          (decodeNat (Nat.unpair (Nat.pred l.length)).2)
          (l.getD (Nat.unpair (Nat.pred l.length)).1 default)
          (l.getD (Nat.unpair (Nat.pred l.length)).2 default)) :=
    Primrec₂.option_some_iff.2 hg'
  have H : ∀ (_ : Unit) (n : ℕ),
      (fun (_ : Unit) (l : List σ) => some (if l.length = 0 then base else
        step (decodeNat (Nat.unpair (Nat.pred l.length)).1)
          (decodeNat (Nat.unpair (Nat.pred l.length)).2)
          (l.getD (Nat.unpair (Nat.pred l.length)).1 default)
          (l.getD (Nat.unpair (Nat.pred l.length)).2 default))) ()
        ((List.range n).map fun m => recD base step (decodeNat m)) =
      some (recD base step (decodeNat n)) := by
    intro _ n
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.length_map, List.length_range, Nat.pred_succ, Nat.succ_ne_zero,
        if_false, decodeNat_succ, recD_cons]
      rw [getD_range_map _ (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
        getD_range_map _ (Nat.lt_succ_of_le (Nat.unpair_right_le n))]
  have := Primrec.nat_strong_rec (fun (_ : Unit) n => recD base step (decodeNat n)) hg H
  refine (this.comp (Primrec.const ()) Primrec.encode).of_eq fun d => ?_
  rw [encode_eq, decodeNat_encodeNat]

/-! ## Unary numerals and list indexing -/

theorem ofNat_eq_iterate (n : ℕ) : Data.ofNat n = (fun d => cons nil d)^[n] nil := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem primrec_ofNat : Primrec Data.ofNat := by
  have hh : Primrec₂ fun (_ : ℕ) (d : Data) => cons nil d :=
    primrec_cons.comp (Primrec.const nil) Primrec.snd
  exact (Primrec.nat_iterate Primrec.id (Primrec.const nil) hh).of_eq fun n =>
    (ofNat_eq_iterate n).symm

/-- The length of the right spine: reads a unary numeral (`unaryToNat (ofNat n) = n`). -/
def unaryToNat : Data → ℕ := recD 0 fun _ _ _ rb => rb + 1

@[simp] theorem unaryToNat_nil : unaryToNat nil = 0 := rfl

@[simp] theorem unaryToNat_cons (a b : Data) : unaryToNat (cons a b) = unaryToNat b + 1 := rfl

@[simp] theorem unaryToNat_ofNat (n : ℕ) : unaryToNat (Data.ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Data.ofNat, ih]

theorem primrec_unaryToNat : Primrec unaryToNat :=
  primrec_recD 0 _ (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))

/-- The `n`-th element of a `cons`-chain (`nil` beyond the end). -/
def getList (d : Data) (n : ℕ) : Data := left (right^[n] d)

theorem primrec_getList : Primrec₂ getList :=
  primrec_left.comp (Primrec.nat_iterate Primrec.snd Primrec.fst
    (primrec_right.comp Primrec.snd).to₂)

theorem getList_list (l : List Data) (i : ℕ) : getList (Data.list l) i = Env.get l i := by
  induction i generalizing l with
  | zero => cases l <;> rfl
  | succ i ih =>
    unfold getList
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simp [Function.iterate_fixed right_nil, Env.get_nil]
    | cons a l => simpa [getList, Function.iterate_succ_apply] using ih l

/-! ## Decoding bit strings -/

theorem toBool?_eq (d : Data) : toBool? d =
    if d = nil then some false else if d = cons nil nil then some true else none := by
  rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩ <;> simp [toBool?]

theorem primrec_toBool? : Primrec toBool? :=
  (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const nil))
    (Primrec.const (some false))
    (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const (cons nil nil)))
      (Primrec.const (some true)) (Primrec.const none))).of_eq fun d => (toBool?_eq d).symm

theorem toList?_eq_recD {α : Type*} (g : Data → Option α) (d : Data) :
    toList? g d = recD (some []) (fun a _ _ rb => (g a).bind fun x => rb.map (x :: ·)) d := by
  induction d with
  | nil => rfl
  | cons a d _ ihd =>
    rw [recD_cons, ← ihd]
    simp only [toList?]
    cases g a <;> cases toList? g d <;> rfl

theorem primrec_toList? {α : Type*} [Primcodable α] {g : Data → Option α} (hg : Primrec g) :
    Primrec (toList? g) := by
  have hstep : Primrec fun p : (Data × Data) × Option (List α) × Option (List α) =>
      (g p.1.1).bind fun x => p.2.2.map (x :: ·) :=
    Primrec.option_bind (hg.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (primrec_recD (some []) _ hstep).of_eq fun d => (toList?_eq_recD g d).symm

/-- Decoding bit strings from `Data` is primitive recursive. -/
theorem primrec_decode_bitStr :
    Primrec fun d : Data => (SizedEncoding.decode d : Option BitStr) :=
  primrec_toList? primrec_toBool?

/-! ## Encoding naturals

The companion of `primrec_decode_bitStr` in the other direction. A natural is encoded as the
bit string of `Nat.bits`, so its encoding satisfies the halving recursion below, and strong
recursion on `ℕ` turns that into a primitive recursive definition. Every budgeted run of the
tabulation feeds the machine an `encode (n, …)`, so this is on the critical path of
`MIPRE.Halting.Obligations.tab_computable`. -/

/-- The binary encoding of a natural as data, in recursive form. -/
theorem encode_nat_rec (n : ℕ) : (encode n : Data) =
    if n = 0 then Data.nil
    else Data.cons (if n % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
      (encode (n / 2) : Data) := by
  by_cases h : n = 0
  · subst h; rfl
  rw [if_neg h]
  show (encode n.bits : Data) = Data.cons _ (encode (n / 2).bits : Data)
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.1 he
    have h2 : n = 2 * (n / 2) := by omega
    have hne : n / 2 ≠ 0 := by omega
    rw [if_neg (by omega)]
    conv_lhs => rw [h2]
    rw [Nat.bit0_bits _ hne]
    rfl
  · have h1 : n % 2 = 1 := Nat.odd_iff.1 ho
    have h2 : n = 2 * (n / 2) + 1 := by omega
    rw [if_pos h1]
    conv_lhs => rw [h2]
    rw [Nat.bit1_bits]
    rfl

/-- Encoding a natural as data is primitive recursive. -/
theorem primrec_encode_nat : Primrec fun n : ℕ => (encode n : Data) := by
  have hstep : Primrec₂ (fun (_ : Unit) (l : List Data) =>
      some (if l.length = 0 then Data.nil
        else Data.cons (if l.length % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
          (l.getD (l.length / 2) Data.nil))) := by
    have hlen : Primrec fun p : Unit × List Data => p.2.length :=
      Primrec.list_length.comp Primrec.snd
    have body : Primrec fun p : Unit × List Data =>
        (if p.2.length = 0 then Data.nil
          else Data.cons (if p.2.length % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
            (p.2.getD (p.2.length / 2) Data.nil)) := ?_
    · exact (Primrec.option_some.comp body).to₂
    refine Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const Data.nil) ?_
    refine primrec_cons.comp ?_ ?_
    · exact Primrec.ite
        (Primrec.eq.comp (Primrec.nat_mod.comp hlen (Primrec.const 2)) (Primrec.const 1))
        (Primrec.const (Data.cons Data.nil Data.nil)) (Primrec.const Data.nil)
    · exact (Primrec.list_getD Data.nil).comp Primrec.snd
        (Primrec.nat_div.comp hlen (Primrec.const 2))
  have H : ∀ (_ : Unit) (n : ℕ),
      (fun (_ : Unit) (l : List Data) =>
        some (if l.length = 0 then Data.nil
          else Data.cons (if l.length % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
            (l.getD (l.length / 2) Data.nil))) ()
        ((List.range n).map fun m => (encode m : Data)) = some (encode n : Data) := by
    intro _ n
    simp only [List.length_map, List.length_range]
    by_cases h : n = 0
    · subst h; rfl
    rw [if_neg h]
    conv_rhs => rw [encode_nat_rec n, if_neg h]
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  exact (Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => (encode n : Data)) hstep H).comp
    (Primrec.const ()) Primrec.id

end Data

/-! ## Two small gaps in the ambient library -/

/-- Exponentiation is primitive recursive. Mathlib has `Nat.Primrec.pow` on the unpaired
form but no `Primrec₂` spelling. -/
theorem primrec_nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- Two `LawfulBEq` instances give the same `List.idxOf`. `List Bool` has its own `BEq`, while
Mathlib's `Primrec.list_idxOf` is stated at the one derived from `DecidableEq`; the two are
propositionally equal, but reducing them to a common normal form sends `whnf` a very long way
indeed, so the bridge is proved once, here, rather than left to unification. -/
theorem List.idxOf_congr_inst {α : Type*} (i1 i2 : BEq α) [@LawfulBEq α i1] [@LawfulBEq α i2]
    (a : α) (l : List α) : @List.idxOf α i1 a l = @List.idxOf α i2 a l := by
  show @List.findIdx α _ l = @List.findIdx α _ l
  congr 1
  funext b
  exact Bool.eq_iff_iff.2 (by rw [@beq_iff_eq α i1 _, @beq_iff_eq α i2 _])

/-- The index of a bit string in a list of bit strings, at the instance the enumerations of
`Halting/Enumerate.lean` actually elaborate to. -/
theorem primrec_idxOf_bitStr :
    Primrec₂ (fun (a : BitStr) (l : List BitStr) => @List.idxOf BitStr List.instBEq a l) :=
  Primrec.list_idxOf.of_eq fun a l => List.idxOf_congr_inst instBEqOfDecidableEq List.instBEq a l

end MIPRE.Cost
