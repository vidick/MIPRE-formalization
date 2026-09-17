/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Formula
import MIPRE.Foundations.Cost.Binary
import Mathlib.Tactic.Linarith

/-!
# Formulas on bit vectors

The vocabulary in which the describer of the succinct Cook–Levin theorem is written
(`planning/succinct-cook-levin.md`, S3): a *field* is a list of formulas read as a binary
number, least significant bit first (`Fml.val`); the fields of an index are slices of the
input bits (`Fml.field`); and the tests on fields are conjunctions and disjunctions
(`andList`, `orList`), equality with a constant or another field (`eqConst`, `eqFields`),
comparison (`ltConst`, `ltFields`), addition of a constant with its carry (`addBits`,
`addConstRel`), subtraction of a constant by the two's complement (`subConstBits`), padding
(`padTo`) and a multiplexer (`mux`). Every test is defined by a fold or a structural
recursion whose program is the same fold (`FmlProg.lean`), and every semantics lemma is an
equation on `val`.
-/

namespace MIPRE.SAT

open Cost

/-! ## Values of bit strings -/

theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]

theorem bitsVal_lt (l : BitStr) : bitsVal l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal_nil]
  | cons b l ih => rw [bitsVal_cons', List.length_cons, Nat.pow_succ]; cases b <;> simp <;> omega

theorem bitsVal_append (l₁ l₂ : BitStr) :
    bitsVal (l₁ ++ l₂) = bitsVal l₁ + 2 ^ l₁.length * bitsVal l₂ := by
  induction l₁ with
  | nil => simp [bitsVal_nil]
  | cons b l ih =>
    rw [List.cons_append, bitsVal_cons', bitsVal_cons', ih, List.length_cons, Nat.pow_succ]; ring

theorem bitsVal_replicate_false (n : ℕ) : bitsVal (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, bitsVal_cons', ih]; rfl

/-- Equal-length bit strings with equal values are equal. -/
theorem bitsVal_injective : ∀ {l₁ l₂ : BitStr}, l₁.length = l₂.length → bitsVal l₁ = bitsVal l₂ →
    l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, hv => by
    rw [bitsVal_cons', bitsVal_cons'] at hv
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hb : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> simp at hv ⊢ <;> omega
    subst hb
    have : bitsVal l₁ = bitsVal l₂ := by cases b₁ <;> simp at hv <;> omega
    rw [bitsVal_injective hl this]

theorem bitsVal_take (l : BitStr) (n : ℕ) : bitsVal (l.take n) = bitsVal l % 2 ^ n := by
  induction l generalizing n with
  | nil => simp [bitsVal_nil]
  | cons b l ih =>
    cases n with
    | zero => simp [bitsVal_nil, Nat.mod_one]
    | succ n =>
      rw [List.take_succ_cons, bitsVal_cons', bitsVal_cons', ih, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
      have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
      generalize bitsVal l = a
      obtain ⟨q, r, rfl, hr⟩ : ∃ q r, a = q * 2 ^ n + r ∧ r < 2 ^ n :=
        ⟨a / 2 ^ n, a % 2 ^ n, (Nat.div_add_mod' a (2 ^ n)).symm, Nat.mod_lt a h2⟩
      rw [Nat.add_comm (q * 2 ^ n) r, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      cases b
      · simp only [Bool.toNat_false, Nat.add_zero]
        rw [show 2 * (r + q * 2 ^ n) = 2 * r + q * (2 * 2 ^ n) by ring, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)]
      · simp only [Bool.toNat_true]
        rw [show 2 * (r + q * 2 ^ n) + 1 = (2 * r + 1) + q * (2 * 2 ^ n) by ring,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem bitsVal_map_not (l : BitStr) : bitsVal (l.map not) + bitsVal l + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal_nil]
  | cons b l ih =>
    rw [List.map_cons, bitsVal_cons', bitsVal_cons', List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem length_incBits_ge (l : BitStr) : l.length ≤ (incBits l).length := by
  induction l with
  | nil => simp [incBits]
  | cons b l ih => cases b <;> simp only [incBits, List.length_cons] <;> omega

theorem bitsVal_incBits (l : BitStr) : bitsVal (incBits l) = bitsVal l + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp only [incBits, bitsVal_cons', ih] <;> simp <;> omega

/-- The bits of a number, padded to `W` bits with zeros (least significant bit first). -/
def padBits (W : ℕ) (l : BitStr) : BitStr := l ++ List.replicate (W - l.length) false

theorem length_padBits (W : ℕ) (l : BitStr) (h : l.length ≤ W) : (padBits W l).length = W := by
  simp [padBits]; omega

theorem bitsVal_padBits (W : ℕ) (l : BitStr) : bitsVal (padBits W l) = bitsVal l := by
  rw [padBits, bitsVal_append, bitsVal_replicate_false]; ring

/-- The two's complement of a `W`-bit string: `2^W - v` modulo `2^W`. -/
def twosComp (c : BitStr) : BitStr := (incBits (c.map not)).take c.length

theorem length_twosComp (c : BitStr) : (twosComp c).length = c.length := by
  unfold twosComp
  rw [List.length_take]
  have := length_incBits_ge (c.map not)
  simp only [List.length_map] at this
  omega

theorem bitsVal_twosComp (c : BitStr) : bitsVal (twosComp c) = (2 ^ c.length - bitsVal c) % 2 ^ c.length := by
  unfold twosComp
  rw [bitsVal_take, bitsVal_incBits]
  have := bitsVal_map_not c
  have h2 := bitsVal_lt c
  congr 1
  omega

namespace Fml

/-! ## Basic connectives -/

/-- Equivalence. -/
def xnor (f g : Fml) : Fml := or (and f g) (and (not f) (not g))

theorem eval_xnor (f g : Fml) (x : ℕ → Bool) : (xnor f g).eval x = (f.eval x == g.eval x) := by
  simp only [xnor, eval]; cases f.eval x <;> cases g.eval x <;> rfl

/-- Exclusive or. -/
def xor (f g : Fml) : Fml := or (and f (not g)) (and (not f) g)

theorem eval_xor (f g : Fml) (x : ℕ → Bool) : (xor f g).eval x = (f.eval x != g.eval x) := by
  simp only [xor, eval]; cases f.eval x <;> cases g.eval x <;> rfl

/-- The multiplexer `if s then a else b`. -/
def mux (s a b : Fml) : Fml := or (and s a) (and (not s) b)

theorem eval_mux (s a b : Fml) (x : ℕ → Bool) :
    (mux s a b).eval x = if s.eval x then a.eval x else b.eval x := by
  simp only [mux, eval]; cases s.eval x <;> simp

/-- Conjunction of a list, as a fold. -/
def andList (l : List Fml) : Fml := l.foldl and (const true)

theorem eval_foldl_and (l : List Fml) (init : Fml) (x : ℕ → Bool) :
    (l.foldl and init).eval x = (init.eval x && l.all (·.eval x)) := by
  induction l generalizing init with
  | nil => simp
  | cons f l ih => simp [List.foldl_cons, ih, eval, Bool.and_assoc]

theorem eval_andList (l : List Fml) (x : ℕ → Bool) : (andList l).eval x = l.all (·.eval x) := by
  rw [andList, eval_foldl_and]; rfl

theorem eval_andList_eq_true (l : List Fml) (x : ℕ → Bool) :
    (andList l).eval x = true ↔ ∀ f ∈ l, f.eval x = true := by
  rw [eval_andList, List.all_eq_true]

/-- Disjunction of a list, as a fold. -/
def orList (l : List Fml) : Fml := l.foldl or (const false)

theorem eval_foldl_or (l : List Fml) (init : Fml) (x : ℕ → Bool) :
    (l.foldl or init).eval x = (init.eval x || l.any (·.eval x)) := by
  induction l generalizing init with
  | nil => simp
  | cons f l ih => simp [List.foldl_cons, ih, eval, Bool.or_assoc]

theorem eval_orList (l : List Fml) (x : ℕ → Bool) : (orList l).eval x = l.any (·.eval x) := by
  rw [orList, eval_foldl_or]; rfl

theorem eval_orList_eq_true (l : List Fml) (x : ℕ → Bool) :
    (orList l).eval x = true ↔ ∃ f ∈ l, f.eval x = true := by
  rw [eval_orList, List.any_eq_true]

/-! ## Fields -/

/-- The bits of a field: the values of its formulas, least significant first. -/
def bitsOf (fs : List Fml) (x : ℕ → Bool) : BitStr := fs.map (·.eval x)

/-- The value of a field. -/
def val (fs : List Fml) (x : ℕ → Bool) : ℕ := bitsVal (bitsOf fs x)

@[simp] theorem bitsOf_nil (x : ℕ → Bool) : bitsOf [] x = [] := rfl

@[simp] theorem bitsOf_cons (f : Fml) (fs : List Fml) (x : ℕ → Bool) :
    bitsOf (f :: fs) x = f.eval x :: bitsOf fs x := rfl

@[simp] theorem length_bitsOf (fs : List Fml) (x : ℕ → Bool) : (bitsOf fs x).length = fs.length :=
  List.length_map _

theorem val_cons (f : Fml) (fs : List Fml) (x : ℕ → Bool) :
    val (f :: fs) x = 2 * val fs x + (f.eval x).toNat := by
  simp only [val, bitsOf_cons]; rw [bitsVal_cons']

theorem val_lt (fs : List Fml) (x : ℕ → Bool) : val fs x < 2 ^ fs.length := by
  have := bitsVal_lt (bitsOf fs x); rwa [length_bitsOf] at this

/-- The field of `W` input bits starting at bit `a`. -/
def field (a W : ℕ) : List Fml := (List.range' a W).map inp

@[simp] theorem length_field (a W : ℕ) : (field a W).length = W := by simp [field]

theorem bitsOf_field (a W : ℕ) (x : ℕ → Bool) : bitsOf (field a W) x = (List.range' a W).map x := by
  simp [bitsOf, field, List.map_map, Function.comp_def, eval]

/-- Constant bits as formulas. -/
def constBits (c : BitStr) : List Fml := c.map const

@[simp] theorem length_constBits (c : BitStr) : (constBits c).length = c.length := by simp [constBits]

theorem bitsOf_constBits (c : BitStr) (x : ℕ → Bool) : bitsOf (constBits c) x = c := by
  simp [bitsOf, constBits, List.map_map, Function.comp_def, eval]

/-- Padding a field to `W` bits with zeros. -/
def padTo (W : ℕ) (fs : List Fml) : List Fml := fs ++ List.replicate (W - fs.length) (const false)

theorem length_padTo (W : ℕ) (fs : List Fml) (h : fs.length ≤ W) : (padTo W fs).length = W := by
  simp [padTo]; omega

theorem bitsOf_padTo (W : ℕ) (fs : List Fml) (x : ℕ → Bool) :
    bitsOf (padTo W fs) x = padBits W (bitsOf fs x) := by
  simp [bitsOf, padTo, padBits, List.map_append, List.map_replicate, eval]

theorem val_padTo (W : ℕ) (fs : List Fml) (x : ℕ → Bool) : val (padTo W fs) x = val fs x := by
  rw [val, bitsOf_padTo, bitsVal_padBits]; rfl

/-! ## Equality -/

/-- The step of the equality test with a constant. -/
def eqStep (acc : Fml) (p : Fml × Bool) : Fml := and acc (if p.2 then p.1 else not p.1)

/-- The field `fs` equals the constant `c` (of the same length). -/
def eqConst (fs : List Fml) (c : BitStr) : Fml := (fs.zip c).foldl eqStep (const true)

theorem eval_foldl_eqStep : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      ((fs.zip c).foldl eqStep init).eval x = (init.eval x && decide (bitsOf fs x = c))
  | [], [], _, init, x => by simp
  | f :: fs, b :: c, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_eqStep fs c h]
    simp only [eqStep, eval, bitsOf_cons, List.cons.injEq, Bool.decide_and]
    cases b <;> cases hf : f.eval x <;> simp [hf, eval, Bool.and_assoc]

theorem eval_eqConst (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    (eqConst fs c).eval x = decide (bitsOf fs x = c) := by
  rw [eqConst, eval_foldl_eqStep fs c h]; rfl

theorem eval_eqConst_iff (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    (eqConst fs c).eval x = true ↔ val fs x = bitsVal c := by
  rw [eval_eqConst fs c h, decide_eq_true_iff, val]
  constructor
  · rintro rfl; rfl
  · intro hv; exact bitsVal_injective (by simp [h]) hv

/-- The step of the equality test of two fields. -/
def eqFStep (acc : Fml) (p : Fml × Fml) : Fml := and acc (xnor p.1 p.2)

/-- The fields `fs` and `gs` (of the same length) are equal. -/
def eqFields (fs gs : List Fml) : Fml := (fs.zip gs).foldl eqFStep (const true)

theorem eval_foldl_eqFStep : ∀ (fs gs : List Fml), fs.length = gs.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      ((fs.zip gs).foldl eqFStep init).eval x = (init.eval x && decide (bitsOf fs x = bitsOf gs x))
  | [], [], _, init, x => by simp
  | f :: fs, g :: gs, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_eqFStep fs gs h]
    simp only [eqFStep, eval, bitsOf_cons, List.cons.injEq, Bool.decide_and, eval_xnor]
    cases hg : g.eval x <;> cases hf : f.eval x <;> simp [hf, hg, Bool.and_assoc]

theorem eval_eqFields (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = decide (bitsOf fs x = bitsOf gs x) := by
  rw [eqFields, eval_foldl_eqFStep fs gs h]; rfl

theorem eval_eqFields_iff (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = true ↔ val fs x = val gs x := by
  rw [eval_eqFields fs gs h, decide_eq_true_iff, val, val]
  constructor
  · intro e; rw [e]
  · intro hv; exact bitsVal_injective (by simp [h]) hv

/-! ## Comparison -/

/-- The step of the comparison with a constant, least significant bit first: the prefix is
below the constant's prefix iff this bit is below, or equal with the lower bits below. -/
def ltStep (lt : Fml) (p : Fml × Bool) : Fml :=
  or (and (not p.1) (const p.2)) (and (xnor p.1 (const p.2)) lt)

/-- The field `fs` is below the constant `c` (of the same length). -/
def ltConst (fs : List Fml) (c : BitStr) : Fml := (fs.zip c).foldl ltStep (const false)

theorem eval_foldl_ltStep : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      (((fs.zip c).foldl ltStep init).eval x = true ↔
        val fs x < bitsVal c ∨ (val fs x = bitsVal c ∧ init.eval x = true))
  | [], [], _, init, x => by simp [val, bitsVal_nil]
  | f :: fs, b :: c, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_ltStep fs c h, val_cons, bitsVal_cons']
    simp only [ltStep, eval, eval_xnor, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq]
    cases b <;> cases hf : f.eval x <;> simp <;> omega

theorem eval_ltConst_iff (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    (ltConst fs c).eval x = true ↔ val fs x < bitsVal c := by
  rw [ltConst, eval_foldl_ltStep fs c h]; simp [eval]

/-- The step of the comparison of two fields. -/
def ltFStep (lt : Fml) (p : Fml × Fml) : Fml := or (and (not p.1) p.2) (and (xnor p.1 p.2) lt)

/-- The field `fs` is below the field `gs` (of the same length). -/
def ltFields (fs gs : List Fml) : Fml := (fs.zip gs).foldl ltFStep (const false)

theorem eval_foldl_ltFStep : ∀ (fs gs : List Fml), fs.length = gs.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      (((fs.zip gs).foldl ltFStep init).eval x = true ↔
        val fs x < val gs x ∨ (val fs x = val gs x ∧ init.eval x = true))
  | [], [], _, init, x => by simp [val, bitsVal_nil]
  | f :: fs, g :: gs, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_ltFStep fs gs h, val_cons, val_cons]
    simp only [ltFStep, eval, eval_xnor, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq]
    cases hg : g.eval x <;> cases hf : f.eval x <;> simp <;> omega

theorem eval_ltFields_iff (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (ltFields fs gs).eval x = true ↔ val fs x < val gs x := by
  rw [ltFields, eval_foldl_ltFStep fs gs h]; simp [eval]

/-! ## Addition of a constant -/

/-- The sum bit of a full adder. -/
def sum3 (f b c : Fml) : Fml := xor (xor f b) c

/-- The carry bit of a full adder. -/
def maj3 (f b c : Fml) : Fml := or (and f b) (and (or f b) c)

theorem eval_sum3_maj3 (f b c : Fml) (x : ℕ → Bool) :
    ((sum3 f b c).eval x).toNat + 2 * ((maj3 f b c).eval x).toNat =
      (f.eval x).toNat + (b.eval x).toNat + (c.eval x).toNat := by
  simp only [sum3, maj3, eval_xor, eval]
  cases f.eval x <;> cases b.eval x <;> cases c.eval x <;> rfl

/-- The sum of a field and a constant (of the same length) with a carry in: the sum bits and
the carry out. -/
def addBits : List Fml → BitStr → Fml → List Fml × Fml
  | f :: fs, b :: c, cin =>
    let r := addBits fs c (maj3 f (const b) cin)
    (sum3 f (const b) cin :: r.1, r.2)
  | _, _, cin => ([], cin)

theorem length_addBits : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length → ∀ cin,
    (addBits fs c cin).1.length = fs.length
  | [], [], _, _ => rfl
  | f :: fs, b :: c, h, cin => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [addBits, length_addBits fs c h]

/-- **The adder identity**: `sum + 2^W · carry = fs + c + cin`. -/
theorem val_addBits : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length → ∀ (cin : Fml) (x : ℕ → Bool),
    val (addBits fs c cin).1 x + 2 ^ fs.length * ((addBits fs c cin).2.eval x).toNat =
      val fs x + bitsVal c + (cin.eval x).toNat
  | [], [], _, cin, x => by simp [addBits, val, bitsVal_nil]
  | f :: fs, b :: c, h, cin, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := val_addBits fs c h (maj3 f (const b) cin) x
    have hs := eval_sum3_maj3 f (const b) cin x
    simp only [addBits, val_cons, bitsVal_cons', List.length_cons, Nat.pow_succ, eval] at ih hs ⊢
    generalize (sum3 f (const b) cin).eval x = s at *
    generalize (maj3 f (const b) cin).eval x = m at *
    generalize (addBits fs c (maj3 f (const b) cin)).2.eval x = co at *
    generalize val (addBits fs c (maj3 f (const b) cin)).1 x = vr at *
    generalize val fs x = vf at *
    generalize bitsVal c = vc at *
    generalize (f.eval x).toNat = ef at *
    generalize (cin.eval x).toNat = ec at *
    generalize (2 : ℕ) ^ fs.length = P at *
    cases s <;> cases m <;> cases b <;> cases co <;> simp at * <;> omega

/-- The sum bits of a field and a constant. -/
def addConstBits (fs : List Fml) (c : BitStr) : List Fml := (addBits fs c (const false)).1

/-- The carry out of the sum of a field and a constant. -/
def addConstCarry (fs : List Fml) (c : BitStr) : Fml := (addBits fs c (const false)).2

theorem length_addConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) :
    (addConstBits fs c).length = fs.length := length_addBits fs c h _

theorem val_addConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    val (addConstBits fs c) x + 2 ^ fs.length * ((addConstCarry fs c).eval x).toNat =
      val fs x + bitsVal c := by
  have := val_addBits fs c h (const false) x
  simpa [addConstBits, addConstCarry, eval] using this

theorem val_addConstBits_mod (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    val (addConstBits fs c) x = (val fs x + bitsVal c) % 2 ^ fs.length := by
  have h1 := val_addConstBits fs c h x
  have h2 := val_lt (addConstBits fs c) x
  rw [length_addConstBits fs c h] at h2
  cases hc : (addConstCarry fs c).eval x
  · have h1' : val (addConstBits fs c) x = val fs x + bitsVal c := by
      rw [hc] at h1; simpa using h1
    rw [← h1', Nat.mod_eq_of_lt h2]
  · have h1' : val (addConstBits fs c) x + 2 ^ fs.length = val fs x + bitsVal c := by
      rw [hc] at h1; simpa using h1
    rw [← h1', Nat.add_mod_right, Nat.mod_eq_of_lt h2]

/-- `gs = fs + c`, exactly: the sum bits agree and there is no carry out. -/
def addConstRel (fs gs : List Fml) (c : BitStr) : Fml :=
  and (eqFields gs (addConstBits fs c)) (not (addConstCarry fs c))

theorem eval_addConstRel_iff (fs gs : List Fml) (c : BitStr) (h : fs.length = c.length)
    (hg : gs.length = fs.length) (x : ℕ → Bool) :
    (addConstRel fs gs c).eval x = true ↔ val gs x = val fs x + bitsVal c := by
  have hid := val_addConstBits fs c h x
  have hlen := length_addConstBits fs c h
  simp only [addConstRel, eval, Bool.and_eq_true, Bool.not_eq_true',
    eval_eqFields_iff gs (addConstBits fs c) (by omega)]
  have hg' := val_lt gs x
  rw [hg] at hg'
  constructor
  · rintro ⟨h1, h2⟩; rw [h2] at hid; simp at hid; omega
  · intro hv
    cases hc : (addConstCarry fs c).eval x
    · rw [hc] at hid; simp at hid; exact ⟨by omega, rfl⟩
    · rw [hc] at hid; simp at hid; exfalso; omega

/-! ## Subtraction of a constant -/

/-- The difference `fs - c` by the two's complement, correct when `c ≤ fs`. -/
def subConstBits (fs : List Fml) (c : BitStr) : List Fml := addConstBits fs (twosComp c)

theorem length_subConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) :
    (subConstBits fs c).length = fs.length :=
  length_addConstBits fs _ (by rw [length_twosComp]; exact h)

theorem val_subConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool)
    (hc : bitsVal c ≤ val fs x) : val (subConstBits fs c) x = val fs x - bitsVal c := by
  rw [subConstBits, val_addConstBits_mod fs _ (by rw [length_twosComp]; exact h), bitsVal_twosComp, ← h]
  have hv := val_lt fs x
  have hc' := bitsVal_lt c
  rw [← h] at hc'
  have hpos : 0 < 2 ^ fs.length := Nat.two_pow_pos _
  rcases Nat.eq_zero_or_pos (bitsVal c) with h0 | h0
  · rw [h0]; simp [Nat.mod_eq_of_lt hv]
  · rw [Nat.mod_eq_of_lt (show 2 ^ fs.length - bitsVal c < 2 ^ fs.length by omega)]
    rw [show val fs x + (2 ^ fs.length - bitsVal c) = (val fs x - bitsVal c) + 2 ^ fs.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Input bounds -/

theorem InputsLt.xnor {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.xnor f g).InputsLt n := ⟨⟨hf, hg⟩, hf, hg⟩

theorem InputsLt.xor {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.xor f g).InputsLt n := ⟨⟨hf, hg⟩, hf, hg⟩

theorem InputsLt.mux {n : ℕ} {s a b : Fml} (hs : s.InputsLt n) (ha : a.InputsLt n) (hb : b.InputsLt n) :
    (Fml.mux s a b).InputsLt n := ⟨⟨hs, ha⟩, hs, hb⟩

theorem InputsLt.foldl_and {n : ℕ} (l : List Fml) (init : Fml) (hi : init.InputsLt n)
    (hl : ∀ f ∈ l, f.InputsLt n) : (l.foldl and init).InputsLt n := by
  induction l generalizing init with
  | nil => exact hi
  | cons f l ih =>
    exact ih (and init f) ⟨hi, hl f (List.mem_cons_self ..)⟩ fun g hg => hl g (List.mem_cons_of_mem _ hg)

theorem InputsLt.andList {n : ℕ} (l : List Fml) (hl : ∀ f ∈ l, f.InputsLt n) : (Fml.andList l).InputsLt n :=
  InputsLt.foldl_and l _ trivial hl

theorem InputsLt.foldl_or {n : ℕ} (l : List Fml) (init : Fml) (hi : init.InputsLt n)
    (hl : ∀ f ∈ l, f.InputsLt n) : (l.foldl or init).InputsLt n := by
  induction l generalizing init with
  | nil => exact hi
  | cons f l ih =>
    exact ih (or init f) ⟨hi, hl f (List.mem_cons_self ..)⟩ fun g hg => hl g (List.mem_cons_of_mem _ hg)

theorem InputsLt.orList {n : ℕ} (l : List Fml) (hl : ∀ f ∈ l, f.InputsLt n) : (Fml.orList l).InputsLt n :=
  InputsLt.foldl_or l _ trivial hl

theorem InputsLt.field {n a W : ℕ} (h : a + W ≤ n) : ∀ f ∈ Fml.field a W, f.InputsLt n := by
  intro f hf
  simp only [Fml.field, List.mem_map, List.mem_range'] at hf
  obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hf
  show i < n
  omega

theorem InputsLt.constBits {n : ℕ} (c : BitStr) : ∀ f ∈ Fml.constBits c, f.InputsLt n := by
  intro f hf
  simp only [Fml.constBits, List.mem_map] at hf
  obtain ⟨b, -, rfl⟩ := hf
  trivial

theorem InputsLt.padTo {n W : ℕ} {fs : List Fml} (h : ∀ f ∈ fs, f.InputsLt n) :
    ∀ f ∈ Fml.padTo W fs, f.InputsLt n := by
  intro f hf
  simp only [Fml.padTo, List.mem_append, List.mem_replicate] at hf
  rcases hf with hf | ⟨-, rfl⟩
  · exact h f hf
  · trivial

theorem InputsLt.foldl_zip {n : ℕ} {γ : Type*} (step : Fml → Fml × γ → Fml)
    (hstep : ∀ acc p, acc.InputsLt n → p.1.InputsLt n → (step acc p).InputsLt n)
    (fs : List Fml) (c : List γ) (init : Fml) (hi : init.InputsLt n) (hl : ∀ f ∈ fs, f.InputsLt n) :
    ((fs.zip c).foldl step init).InputsLt n := by
  induction fs generalizing c init with
  | nil => exact hi
  | cons f fs ih =>
    cases c with
    | nil => exact hi
    | cons b c =>
      rw [List.zip_cons_cons, List.foldl_cons]
      exact ih c _ (hstep init (f, b) hi (hl f (List.mem_cons_self ..)))
        fun g hg => hl g (List.mem_cons_of_mem _ hg)

theorem InputsLt.eqConst {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.eqConst fs c).InputsLt n :=
  InputsLt.foldl_zip Fml.eqStep (fun acc p ha hp => ⟨ha, by show InputsLt _ (if p.2 then p.1 else not p.1); split <;> exact hp⟩)
    fs c _ trivial h

theorem InputsLt.foldl_zip₂ {n : ℕ} (step : Fml → Fml × Fml → Fml)
    (hstep : ∀ acc p, acc.InputsLt n → p.1.InputsLt n → p.2.InputsLt n → (step acc p).InputsLt n)
    (fs gs : List Fml) (init : Fml) (hi : init.InputsLt n) (hf : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : ((fs.zip gs).foldl step init).InputsLt n := by
  induction fs generalizing gs init with
  | nil => exact hi
  | cons f fs ih =>
    cases gs with
    | nil => exact hi
    | cons g gs =>
      rw [List.zip_cons_cons, List.foldl_cons]
      exact ih gs _ (hstep init (f, g) hi (hf f (List.mem_cons_self ..)) (hg g (List.mem_cons_self ..)))
        (fun x hx => hf x (List.mem_cons_of_mem _ hx)) fun x hx => hg x (List.mem_cons_of_mem _ hx)

theorem InputsLt.eqFields {n : ℕ} {fs gs : List Fml} (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.eqFields fs gs).InputsLt n :=
  InputsLt.foldl_zip₂ Fml.eqFStep (fun _ _ ha hp hq => ⟨ha, hp.xnor hq⟩) fs gs _ trivial h hg

theorem InputsLt.ltConst {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.ltConst fs c).InputsLt n :=
  InputsLt.foldl_zip Fml.ltStep (fun _ _ ha hp => ⟨⟨hp, trivial⟩, hp.xnor trivial, ha⟩) fs c _ trivial h

theorem InputsLt.ltFields {n : ℕ} {fs gs : List Fml} (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.ltFields fs gs).InputsLt n :=
  InputsLt.foldl_zip₂ Fml.ltFStep (fun _ _ ha hp hq => ⟨⟨hp, hq⟩, hp.xnor hq, ha⟩) fs gs _ trivial h hg

theorem InputsLt.sum3 {n : ℕ} {f b c : Fml} (hf : f.InputsLt n) (hb : b.InputsLt n) (hc : c.InputsLt n) :
    (Fml.sum3 f b c).InputsLt n := (hf.xor hb).xor hc

theorem InputsLt.maj3 {n : ℕ} {f b c : Fml} (hf : f.InputsLt n) (hb : b.InputsLt n) (hc : c.InputsLt n) :
    (Fml.maj3 f b c).InputsLt n := ⟨⟨hf, hb⟩, ⟨hf, hb⟩, hc⟩

theorem InputsLt.addBits {n : ℕ} : ∀ (fs : List Fml) (c : BitStr) (cin : Fml),
    (∀ f ∈ fs, f.InputsLt n) → cin.InputsLt n →
    (∀ f ∈ (Fml.addBits fs c cin).1, f.InputsLt n) ∧ (Fml.addBits fs c cin).2.InputsLt n
  | f :: fs, b :: c, cin, hf, hc => by
    have hf0 : f.InputsLt n := hf f (List.mem_cons_self ..)
    have ih := InputsLt.addBits fs c (Fml.maj3 f (const b) cin)
      (fun g hg => hf g (List.mem_cons_of_mem _ hg))
      (InputsLt.maj3 (b := const b) hf0 trivial hc)
    refine ⟨?_, ih.2⟩
    intro g hg
    simp only [Fml.addBits, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact InputsLt.sum3 (b := const b) hf0 trivial hc
    · exact ih.1 g hg
  | [], _, cin, _, hc => ⟨fun g hg => absurd hg List.not_mem_nil, hc⟩
  | _ :: _, [], cin, _, hc => ⟨fun g hg => absurd hg List.not_mem_nil, hc⟩

theorem InputsLt.addConstBits {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    ∀ f ∈ Fml.addConstBits fs c, f.InputsLt n :=
  (InputsLt.addBits fs c (const false) h (trivial : (const false).InputsLt n)).1

theorem InputsLt.addConstCarry {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.addConstCarry fs c).InputsLt n :=
  (InputsLt.addBits fs c (const false) h (trivial : (const false).InputsLt n)).2

theorem InputsLt.addConstRel {n : ℕ} {fs gs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.addConstRel fs gs c).InputsLt n :=
  ⟨InputsLt.eqFields hg (InputsLt.addConstBits c h), InputsLt.addConstCarry c h⟩

theorem InputsLt.subConstBits {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    ∀ f ∈ Fml.subConstBits fs c, f.InputsLt n := InputsLt.addConstBits _ h

end Fml

end MIPRE.SAT
