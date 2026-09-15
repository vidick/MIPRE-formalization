/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Codable

/-!
# Deciding whether data encodes a program

`Cost/Codable.lean` deliberately gives `Data` a `Primcodable` instance and `Prog` none:
programs are their own descriptions, and nothing in the development needed to *decide* whether
an arbitrary datum is one. The tabulation of obligation O2 does.

A string names a decider through `MIPRE.Halting.descDec x = ((decode (parse x).right)).getD nil`,
which falls back on the program `nil` when the data is not an encoding. A computable tabulation
has to make that same fallback, so it has to decide program-hood — and getting it wrong would
not merely leave a gap, it would make the tabulation *wrong*: on junk data the verifier uses
`Prog.nil`, which accepts nothing, while a tabulation that ran the junk could accept.

`progNorm` is that normalization, as a primitive recursive function of data:
`progNorm d = encode ((decode d : Option Prog)).getD nil`. Its correctness (`progNorm_eq`) is
what lets the two be used interchangeably, the definitional one in the mathematics and the
primitive recursive one in the computability proof.

The recursion is `Data.recD` at a **four-component** state — is this datum a unary numeral, is
it a program encoding, is it a `cons` of two program encodings, is it a numeral consed onto
such a pair. Four components because the grammar of `Prog.toData` reaches two levels down
(`elim i n c` is a numeral consed onto a pair), and a tree recursion can see only its
children's results, never its grandchildren's. `progOk_spec` is stated against `toData`
rather than `ofData`, so the induction is structural on `Data` and `Prog.ofData`'s overlapping
match is touched exactly once, in `toData_of_ofData`.
-/

namespace MIPRE.Cost

open Data

theorem ofNat_of_toNat? : ∀ {d : Data} {n : ℕ}, d.toNat? = some n → Data.ofNat n = d
  | nil, n, h => by cases h; rfl
  | cons nil d, n, h => by
      simp only [Data.toNat?, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      rw [Data.ofNat, ofNat_of_toNat? hm]
  | cons (cons a b) d, n, h => by simp [Data.toNat?] at h

theorem toData_of_ofData : ∀ (d : Data) (p : Prog), Prog.ofData d = some p → p.toData = d := by
  intro d
  induction d using Prog.ofData.induct <;> intro p hp <;>
    simp_all [Prog.ofData, Option.bind_eq_some_iff]
  · obtain ⟨a, ha, rfl⟩ := hp
    rw [Prog.toData, ofNat_of_toNat? ha]; rfl
  · rw [← hp]; rfl
  · obtain ⟨a, ha, b, hb, rfl⟩ := hp
    rw [Prog.toData]
    simp_all [Data.ofNat]
  · obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hp
    rw [Prog.toData, ofNat_of_toNat? ha]
    simp_all [Data.ofNat]
  · obtain ⟨a, ha, b, hb, rfl⟩ := hp
    rw [Prog.toData]
    simp_all [Data.ofNat]
  · obtain ⟨a, ha, rfl⟩ := hp
    rw [Prog.toData]
    simp_all [Data.ofNat]
  · rw [← hp, Prog.toData]
    simp [Data.ofNat]


/-- Four simultaneous predicates on data, by one tree recursion: `d` is a program encoding;
`d` is a pair of program encodings; `d` is a unary numeral followed by such a pair; `d` is a
unary numeral. The last three are what the tags `2`–`4` of `Prog.toData` need of a payload,
and each is read off the children alone, which is what makes the recursion a `recD`. -/
def progOk : Data → Bool × Bool × Bool × Bool :=
  recD (false, false, false, true) fun a b ra rb =>
    ((if a = Data.ofNat 0 then rb.2.2.2
      else if a = Data.ofNat 1 then decide (b = nil)
      else if a = Data.ofNat 2 then rb.2.1
      else if a = Data.ofNat 3 then rb.2.2.1
      else if a = Data.ofNat 4 then rb.2.1
      else if a = Data.ofNat 5 then rb.1
      else if a = Data.ofNat 6 then true
      else false),
     ra.1 && rb.1,
     ra.2.2.2 && rb.2.1,
     decide (a = nil) && rb.2.2.2)

theorem ofNat_inj {i j : ℕ} (h : Data.ofNat i = Data.ofNat j) : i = j := by
  have := congrArg Data.unaryToNat h
  simpa using this

theorem progOk_spec (d : Data) :
    ((progOk d).1 = true ↔ ∃ p : Prog, p.toData = d) ∧
    ((progOk d).2.1 = true ↔ ∃ p q : Prog, d = cons p.toData q.toData) ∧
    ((progOk d).2.2.1 = true ↔
      ∃ (i : ℕ) (p q : Prog), d = cons (Data.ofNat i) (cons p.toData q.toData)) ∧
    ((progOk d).2.2.2 = true ↔ ∃ n : ℕ, d = Data.ofNat n) := by
  induction d with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [progOk, recD_nil, Bool.false_eq_true, false_iff]
      rintro ⟨p, hp⟩; cases p <;> simp [Prog.toData] at hp
    · simp only [progOk, recD_nil, Bool.false_eq_true, false_iff]
      rintro ⟨p, q, hp⟩; exact absurd hp (by simp)
    · simp only [progOk, recD_nil, Bool.false_eq_true, false_iff]
      rintro ⟨i, p, q, hp⟩; exact absurd hp (by simp)
    · simp only [progOk, recD_nil, true_iff]
      exact ⟨0, rfl⟩
  | cons a b iha ihb =>
    have h4 : ((progOk (cons a b)).2.2.2 = true) ↔ ∃ n : ℕ, cons a b = Data.ofNat n := by
      show (decide (a = nil) && (progOk b).2.2.2) = true ↔ _
      rw [Bool.and_eq_true, decide_eq_true_eq, ihb.2.2.2]
      constructor
      · rintro ⟨rfl, m, rfl⟩; exact ⟨m + 1, rfl⟩
      · rintro ⟨n, hn⟩
        cases n with
        | zero => exact absurd hn (by simp [Data.ofNat])
        | succ m =>
          rw [Data.ofNat] at hn
          exact ⟨(Data.cons.inj hn).1, m, (Data.cons.inj hn).2⟩
    have h2 : ((progOk (cons a b)).2.1 = true) ↔ ∃ p q : Prog, cons a b = cons p.toData q.toData := by
      show ((progOk a).1 && (progOk b).1) = true ↔ _
      rw [Bool.and_eq_true, iha.1, ihb.1]
      constructor
      · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩; exact ⟨p, q, rfl⟩
      · rintro ⟨p, q, hpq⟩
        exact ⟨⟨p, (Data.cons.inj hpq).1.symm⟩, ⟨q, (Data.cons.inj hpq).2.symm⟩⟩
    have h3 : ((progOk (cons a b)).2.2.1 = true) ↔
        ∃ (i : ℕ) (p q : Prog), cons a b = cons (Data.ofNat i) (cons p.toData q.toData) := by
      show ((progOk a).2.2.2 && (progOk b).2.1) = true ↔ _
      rw [Bool.and_eq_true, iha.2.2.2, ihb.2.1]
      constructor
      · rintro ⟨⟨i, rfl⟩, ⟨p, q, rfl⟩⟩; exact ⟨i, p, q, rfl⟩
      · rintro ⟨i, p, q, hpq⟩
        exact ⟨⟨i, (Data.cons.inj hpq).1⟩, ⟨p, q, (Data.cons.inj hpq).2⟩⟩
    refine ⟨?_, h2, h3, h4⟩
    show (if a = Data.ofNat 0 then (progOk b).2.2.2
      else if a = Data.ofNat 1 then decide (b = nil)
      else if a = Data.ofNat 2 then (progOk b).2.1
      else if a = Data.ofNat 3 then (progOk b).2.2.1
      else if a = Data.ofNat 4 then (progOk b).2.1
      else if a = Data.ofNat 5 then (progOk b).1
      else if a = Data.ofNat 6 then true
      else false) = true ↔ _
    constructor
    · intro h
      split_ifs at h with e0 e1 e2 e3 e4 e5 e6
      · obtain ⟨i, rfl⟩ := ihb.2.2.2.1 h
        exact ⟨.var i, by rw [Prog.toData, e0]⟩
      · rw [decide_eq_true_eq] at h
        exact ⟨.nil, by rw [Prog.toData, e1, h]⟩
      · obtain ⟨p, q, rfl⟩ := ihb.2.1.1 h
        exact ⟨.cons p q, by rw [Prog.toData, e2]⟩
      · obtain ⟨i, p, q, rfl⟩ := ihb.2.2.1.1 h
        exact ⟨.elim i p q, by rw [Prog.toData, e3]⟩
      · obtain ⟨p, q, rfl⟩ := ihb.2.1.1 h
        exact ⟨.let_ p q, by rw [Prog.toData, e4]⟩
      · obtain ⟨p, rfl⟩ := ihb.1.1 h
        exact ⟨.loop p, by rw [Prog.toData, e5]⟩
      · exact ⟨.const b, by rw [Prog.toData, e6]⟩
    · rintro ⟨p, hp⟩
      cases p with
      | var i =>
        rw [Prog.toData] at hp
        obtain ⟨rfl, rfl⟩ := Data.cons.inj hp
        rw [if_pos rfl]
        exact ihb.2.2.2.2 ⟨i, rfl⟩
      | nil =>
        rw [Prog.toData] at hp
        obtain ⟨rfl, rfl⟩ := Data.cons.inj hp
        rw [if_neg (by decide), if_pos rfl]
        simp
      | cons h t =>
        rw [Prog.toData] at hp
        obtain ⟨rfl, rfl⟩ := Data.cons.inj hp
        rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
        exact ihb.2.1.2 ⟨h, t, rfl⟩
      | elim i n c =>
        rw [Prog.toData] at hp
        obtain ⟨rfl, rfl⟩ := Data.cons.inj hp
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
        exact ihb.2.2.1.2 ⟨i, n, c, rfl⟩
      | let_ e f =>
        rw [Prog.toData] at hp
        obtain ⟨rfl, rfl⟩ := Data.cons.inj hp
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_pos rfl]
        exact ihb.2.1.2 ⟨e, f, rfl⟩
      | loop f =>
        rw [Prog.toData] at hp
        obtain ⟨rfl, rfl⟩ := Data.cons.inj hp
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_neg (by decide), if_pos rfl]
        exact ihb.1.2 ⟨f, rfl⟩
      | const e =>
        rw [Prog.toData] at hp
        obtain ⟨rfl, rfl⟩ := Data.cons.inj hp
        rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
          if_neg (by decide), if_neg (by decide), if_pos rfl]


theorem primrec_progOk : Primrec progOk := by
  have hb : Primrec fun p : (Data × Data) × (Bool × Bool × Bool × Bool) ×
      (Bool × Bool × Bool × Bool) => p.1.2 := Primrec.snd.comp Primrec.fst
  have ha : Primrec fun p : (Data × Data) × (Bool × Bool × Bool × Bool) ×
      (Bool × Bool × Bool × Bool) => p.1.1 := Primrec.fst.comp Primrec.fst
  have hra : Primrec fun p : (Data × Data) × (Bool × Bool × Bool × Bool) ×
      (Bool × Bool × Bool × Bool) => p.2.1 := Primrec.fst.comp Primrec.snd
  have hrb : Primrec fun p : (Data × Data) × (Bool × Bool × Bool × Bool) ×
      (Bool × Bool × Bool × Bool) => p.2.2 := Primrec.snd.comp Primrec.snd
  have heq : ∀ k : ℕ, PrimrecPred fun p : (Data × Data) × (Bool × Bool × Bool × Bool) ×
      (Bool × Bool × Bool × Bool) => p.1.1 = Data.ofNat k :=
    fun k => PrimrecRel.comp Primrec.eq ha (Primrec.const _)
  have hnil : PrimrecPred fun p : (Data × Data) × (Bool × Bool × Bool × Bool) ×
      (Bool × Bool × Bool × Bool) => p.1.2 = nil :=
    PrimrecRel.comp Primrec.eq hb (Primrec.const _)
  refine primrec_recD _ _ (Primrec.pair ?_ (Primrec.pair ?_ (Primrec.pair ?_ ?_)))
  · exact Primrec.ite (heq 0) (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrb)))
      (Primrec.ite (heq 1) (Primrec.ite hnil (Primrec.const true) (Primrec.const false))
        (Primrec.ite (heq 2) (Primrec.fst.comp (Primrec.snd.comp hrb))
          (Primrec.ite (heq 3) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hrb)))
            (Primrec.ite (heq 4) (Primrec.fst.comp (Primrec.snd.comp hrb))
              (Primrec.ite (heq 5) (Primrec.fst.comp hrb)
                (Primrec.ite (heq 6) (Primrec.const true) (Primrec.const false)))))))
  · exact Primrec.and.comp (Primrec.fst.comp hra) (Primrec.fst.comp hrb)
  · exact Primrec.and.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hra)))
      (Primrec.fst.comp (Primrec.snd.comp hrb))
  · have hnilA : PrimrecPred fun p : (Data × Data) × (Bool × Bool × Bool × Bool) ×
        (Bool × Bool × Bool × Bool) => p.1.1 = nil :=
      PrimrecRel.comp Primrec.eq ha (Primrec.const _)
    exact Primrec.and.comp (Primrec.ite hnilA (Primrec.const true) (Primrec.const false))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrb)))

/-- **The normalized program encoding of arbitrary data**: `d` itself when it is the encoding
of a program, and the encoding of `nil` otherwise. -/
def progNorm (d : Data) : Data := if (progOk d).1 = true then d else Prog.nil.toData

theorem progNorm_eq (d : Data) :
    progNorm d = encode ((SizedEncoding.decode d : Option Prog).getD .nil) := by
  rw [progNorm]
  by_cases h : (progOk d).1 = true
  · obtain ⟨p, rfl⟩ := (progOk_spec d).1.1 h
    rw [if_pos h]
    show _ = encode ((Prog.ofData p.toData).getD .nil)
    rw [Prog.ofData_toData]
    rfl
  · rw [if_neg h]
    have : (Prog.ofData d) = none := by
      rcases hd : Prog.ofData d with _ | p
      · rfl
      · exact absurd ((progOk_spec d).1.2 ⟨p, toData_of_ofData d p hd⟩) h
    show _ = encode ((Prog.ofData d).getD .nil)
    rw [this]
    rfl

theorem primrec_progNorm : Primrec progNorm :=
  Primrec.ite (⟨inferInstance, (Primrec.fst.comp primrec_progOk).of_eq
      fun d => by cases h : (progOk d).1 <;> simp [h]⟩)
    Primrec.id (Primrec.const _)


end MIPRE.Cost
