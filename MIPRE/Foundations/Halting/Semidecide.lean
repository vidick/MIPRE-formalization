/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.Semidecide
import MIPRE.Foundations.Halting.Serial

/-!
# Semideciders on encoded values, not only on bit strings

`MIPRE.Cost.exists_semidecider` turns a recursively enumerable predicate on *bit strings* into
a program of the ambient model halting on `encode x` exactly when the predicate holds. The
obligation `MIPRE.Halting.Obligations.sem_spec` needs it on *pairs*: a program halting on
`encode (x, n)` exactly off the class `B` at level `n`. The difference is not cosmetic —
`encode (x, n)` is `cons (encode x) (encode n)`, which is not the encoding of any bit string —
and it cannot be arranged by choosing the predicate, since the criterion consumes the
equivalence in both directions.

`exists_semidecider_of_decode` closes the gap once and for all, for every type whose
`SizedEncoding` can be decoded primitive recursively: prefix the bit-string semidecider with
`Prog.serProg`, the program that writes the postorder serialization of its input
(`Halting/Serial.lean`). Serialization and `Data.parse` invert each other
(`Data.parse_toBitsPost`), so the composite halts on `encode a` exactly when the bit-string
semidecider halts on the serialization of `encode a`, which is where the predicate is read
back. `exists_semidecider_prod_nat` is the instance the obligation asks for, and
`primrec_decode_prod_nat` the decoding it needs.

The route through a serialization rather than a direct encoding is what keeps the
`ToPartrec` translation of `Cost/Semidecide.lean` untouched: a `ToPartrec` code cannot see
trailing zeros of its input list, which is why that file exists in the shape it does, and
nothing here re-enters that argument.
-/

namespace MIPRE.Cost

/-! ## Decoding a pair of a bit string and a number -/

/-- The decoding of a pair out of a `cons`, spelled out. -/
theorem Data.decode_prod_cons {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a b : Data) :
    (decode (Data.cons a b) : Option (α × β)) =
      match (decode a : Option α), (decode b : Option β) with
      | some x, some y => some (x, y)
      | _, _ => none := rfl

/-- The decoding of `BitStr × ℕ` out of data is primitive recursive: a pair is a `cons`, and its
two components decode by `Data.primrec_decode_bitStr` and `Data.primrec_decode_nat`. -/
theorem Data.primrec_decode_prod_nat :
    Primrec fun d : Data => (decode d : Option (BitStr × ℕ)) := by
  have hinner : Primrec₂ fun (p : Data × Data × Data) (x : BitStr) =>
      (decode p.2.2 : Option ℕ).map fun n => (x, n) :=
    Primrec.option_map
      (Data.primrec_decode_nat.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hh : Primrec fun p : Data × Data × Data =>
      (decode p.2.1 : Option BitStr).bind fun x =>
        (decode p.2.2 : Option ℕ).map fun n => (x, n) :=
    Primrec.option_bind (Data.primrec_decode_bitStr.comp (Primrec.fst.comp Primrec.snd)) hinner
  refine (Data.primrec_ite_nil (f := fun d : Data => d)
    (g := fun _ : Data => (none : Option (BitStr × ℕ)))
    (h := fun _ a b => (decode a : Option BitStr).bind fun x =>
      (decode b : Option ℕ).map fun n => (x, n))
    Primrec.id (Primrec.const none) hh).of_eq fun d => ?_
  cases d with
  | nil => rfl
  | cons a b =>
    rw [if_neg (show Data.cons a b ≠ Data.nil by simp), Data.decode_prod_cons,
      Data.left_cons, Data.right_cons]
    rcases ha : (decode a : Option BitStr) with _ | x
    · rfl
    · rcases hb : (decode b : Option ℕ) with _ | n <;> rfl

/-! ## The semidecider -/

/-- **Recursively enumerable predicates on encoded values are halting sets.** For a type whose
encoding decodes primitive recursively and an r.e. predicate `p` on it, a well-scoped program
halting on `encode a` exactly when `p a`: `Cost.exists_semidecider` with the input serialized
by `Prog.serProg` first. -/
theorem exists_semidecider_of_decode {α : Type*} [SizedEncoding α] [Primcodable α] [Inhabited α]
    (hdec : Primrec fun d : Data => (decode d : Option α))
    {p : α → Prop} (hp : REPred p) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ a : α, Halts S (encode a) ↔ p a := by
  -- the predicate on bit strings: parse the string, decode it, fall back on `default`
  have hg : Computable fun y : BitStr => ((decode (Data.parse y) : Option α)).getD default :=
    (Primrec.option_getD.comp (hdec.comp Data.primrec_parse) (Primrec.const default)).to_comp
  have hre : REPred fun y : BitStr => p (((decode (Data.parse y) : Option α)).getD default) :=
    Partrec.comp hp hg
  obtain ⟨S', hws, hS'⟩ := exists_semidecider hre
  refine ⟨.let_ Prog.serProg S', ⟨Prog.serProg_wellScoped, hws.mono (by omega) _⟩, fun a => ?_⟩
  obtain ⟨s, -, hpre⟩ := Prog.serProg_runs (encode a)
  have hq : ((decode (Data.parse ((encode a : Data).toBitsPost)) : Option α)).getD default = a := by
    rw [Data.parse_toBitsPost, SizedEncoding.decode_encode]
    rfl
  have key : Halts (.let_ Prog.serProg S') (encode a) ↔
      Halts S' (encode ((encode a : Data).toBitsPost)) := by
    constructor
    · rintro ⟨r, t, h⟩
      cases h with
      | let_ h₁ h₂ =>
        obtain ⟨rfl, -⟩ := h₁.deterministic hpre
        exact ⟨r, _, Eval.of_append_of_wellScoped (env := [_]) (extra := [_]) h₂ hws⟩
    · rintro ⟨r, t, h⟩
      exact ⟨r, _, Eval.let_ hpre (Eval.append_of_wellScoped h hws _)⟩
  rw [key, hS', hq]

/-- The instance obligation **O3** asks for: an r.e. predicate on `(string, level)` pairs is
the halting set of a well-scoped program on `encode (x, n)`. -/
theorem exists_semidecider_prod_nat {p : BitStr → ℕ → Prop} (hp : REPred fun q : BitStr × ℕ =>
    p q.1 q.2) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ p x n :=
  let ⟨S, hws, hS⟩ := exists_semidecider_of_decode Data.primrec_decode_prod_nat hp
  ⟨S, hws, fun x n => hS (x, n)⟩

end MIPRE.Cost
