/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.BoundedEval
import MIPRE.Foundations.Halting.Enumerate
import MIPRE.Foundations.Cost.Semidecide

/-!
# Deciding acceptance under a time bound

The first half of obligation **O2** (blueprint `rem:compression-abstract`, item 3): the
acceptance table of the tabulated game. Filling it in needs `Decider.Accepts` — a `Σ₁`
statement, `∃ t, prog.Runs …` — to be *decided*, and that is exactly what `n`-boundedness
buys: the bound supplies a budget within which the decider must halt, so one budgeted run
settles the question (`Machine.runForD`).

* `Decider.acceptBudget`: the budget `T · (|d| + 1) ^ k` the bound gives at index `n` on the
  tuple `(x, y, a, b)`, read off the shape of `Decider.TimeBoundAt`.
* `Decider.accepts_iff_runForD`: for a decider obeying that bound, acceptance is one budgeted
  run returning `encode true`.
* `Decider.decidableAccepts` and `Verifier.decidableAccepts`: the resulting decision
  procedures, and `Verifier.accepts_iff_runForD` for the verifier a string denotes, where the
  bound comes from `Verifier.IsBounded`.

The other half of the tabulation is the question distribution, and the rest of this file is
what a `GameData` needs for it. `CL.Sampler.queryUnder` runs one sampler query under the same
kind of budget; `Verifier.bitsToIdx` turns the bit string a query returns into the number a
`GameData` names its questions by, and agrees with `Verifier.questionEquiv`; and
`Verifier.weightList` is the weight list itself — one entry of weight `1` for each point of
`𝔽₂^{s(n)}`, at the index pair its two marginals land on. Its `questionWeight` is then the
number of points landing on a given pair and its `totalWeight` is `2 ^ s(n)`, which is exactly
the quotient `CL.clDist` is: `length_filter_bitStrsOfLen` is the bridge, the bit strings of
length `s` being the vectors of `𝔽₂^s`.

`Verifier.answerEquiv_symm_val` is the same service on the answer side: an answer's index is
its position among the bit strings of length at most `T`, the enumeration `answerList` being
`bitStrsLE` mapped by a truncation that is the identity on them.

`Verifier.accList` is then the acceptance table: the index tuples of the answer tuples a
predicate accepts, enumerated over the two alphabets, with `mem_accList_iff` saying exactly
what is in it. `bitsToIdx_injOn` is what lets a tuple be read back — the index of a question
determines it, among the strings of a fixed length.

`MIPRE.Halting.tabOf` at the end assembles all of it: the `GameData` five *numbers* describe,
with `primrec_tabOf` its computability. Five numbers and not a verifier, because a `Verifier`
is a structure carrying proofs and so is not the sort of thing a `Primrec` statement can
mention; the bridge back to the verifier those numbers came from is in
`Halting/Instantiation.lean`.

Nothing here is efficient and nothing needs to be: the tabulation is a computable map, not a
polynomial-time one, and the budget it runs under is the verifier's own time bound.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)

namespace Decider

variable (D : Decider)

/-- The budget the time bound `TimeBoundAt n T k` gives on the tuple `(x, y, a, b)`: the
decider's input is `cons (encode n) (encode (x, y, a, b))`, and the bound is `T` times the
`k`-th power of one more than the size of the second component. -/
def acceptBudget (T k : ℕ) (x y a b : BitStr) : ℕ :=
  T * ((encode (x, y, a, b) : Data).size + 1) ^ k

/-- **Acceptance under a time bound is one budgeted run.** -/
theorem accepts_iff_runForD {n T k : ℕ} (hb : D.TimeBoundAt n T k) (x y a b : BitStr) :
    D.Accepts n x y a b ↔
      Machine.runForD (encode D.prog) (encode (n, x, y, a, b))
        (acceptBudget T k x y a b) = some (encode true) :=
  (Machine.runForD_eq_some_iff (hb (encode (x, y, a, b)))).symm

/-- Hence acceptance is decidable, for a decider that obeys a time bound at the index. -/
def decidableAccepts {n T k : ℕ} (hb : D.TimeBoundAt n T k) (x y a b : BitStr) :
    Decidable (D.Accepts n x y a b) :=
  decidable_of_iff _ (D.accepts_iff_runForD hb x y a b).symm

end Decider

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- **Acceptance by an `n`-bounded verifier is one budgeted run**, at the budget its own
`λ`-boundedness supplies. This is what fills in the acceptance table of the tabulation. -/
theorem accepts_iff_runForD {n : ℕ} (hb : V.IsBounded n) (hn : 2 ≤ n) (x y a b : BitStr) :
    V.decider.Accepts n x y a b ↔
      Machine.runForD (encode V.decider.prog) (encode (n, x, y, a, b))
        (Decider.acceptBudget (n ^ n) n x y a b) = some (encode true) :=
  V.decider.accepts_iff_runForD (hb.1 n hn).2.2 x y a b

/-- Hence acceptance by an `n`-bounded verifier is decidable. -/
def decidableAccepts {n : ℕ} (hb : V.IsBounded n) (hn : 2 ≤ n) (x y a b : BitStr) :
    Decidable (V.decider.Accepts n x y a b) :=
  V.decider.decidableAccepts (hb.1 n hn).2.2 x y a b

end Verifier

/-! ## Sampler queries under the budget -/

namespace CL.Sampler

variable {ℓ : ℕ} (S : CL.Sampler ℓ)

/-- One query to the sampler, run under the budget its time bound supplies. The sampler is
required to halt on *every* input of the form `(n, …)`, so this is total wherever the bound
holds. -/
def queryUnder (T k n : ℕ) (q : Query) : Option Data :=
  Machine.runForD (encode S.prog) (encode (n, q)) (T * ((encode q : Data).size + 1) ^ k)

/-- Under the bound, a budgeted query returns exactly what the sampler's correctness clauses
say it returns. -/
theorem queryUnder_eq {n T k : ℕ} (hb : S.TimeBoundAt n T k) {q : Query} {r : Data} {t : ℕ}
    (h : S.prog.Runs (encode (n, q)) r t) : S.queryUnder T k n q = some r := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb (encode q)
  obtain ⟨rfl, -⟩ := h₀.deterministic h
  exact Machine.runForD_eq_some h₀ ht₀

/-- The dimension query. -/
theorem queryUnder_dimension {n T k : ℕ} (hb : S.TimeBoundAt n T k) :
    S.queryUnder T k n Query.dimension = some (encode (S.dim n)) :=
  let ⟨_, h⟩ := S.runs_dimension n; S.queryUnder_eq hb h

/-- **The marginal at the top level is the CL function itself** (`CLFun.truncate_self`), so one
budgeted `marginal` query at level `ℓ` computes `L^w(z)` — which is what the question weights
of the tabulated game are counted from. -/
theorem queryUnder_marginal {n T k : ℕ} (hb : S.TimeBoundAt n T k) (hl : 1 ≤ ℓ) (w : Player)
    (z : BitStr) (hz : z.length = S.dim n) :
    S.queryUnder T k n (Query.marginal w ℓ z)
      = some (encode (toBits ((S.cl n w).eval (ofBits (S.dim n) z)))) := by
  obtain ⟨t, h⟩ := S.runs_marginal n w ℓ z hl le_rfl hz
  rw [CLFun.truncate_self] at h
  exact S.queryUnder_eq hb h

/-- A marginal query with the player and the level fixed is a primitive recursive function of
the point queried: a query is its tuple, encoded, and `marginal w j z` is `(1, w, j, z, [])`,
so with `w` and `j` literal only `encode z` varies. -/
theorem primrec_encode_marginal (w : Player) (j : ℕ) :
    Primrec fun z : BitStr => (encode (Query.marginal w j z) : Data) := by
  have h : ∀ z : BitStr, (encode (Query.marginal w j z) : Data)
      = Data.cons (encode (1 : ℕ)) (Data.cons (encode w)
          (Data.cons (encode j) (Data.cons (encode z) (encode ([] : BitStr))))) := fun _ => rfl
  refine (Data.primrec_cons.comp (Primrec.const _)
    (Data.primrec_cons.comp (Primrec.const _)
      (Data.primrec_cons.comp (Primrec.const _)
        (Data.primrec_cons.comp Cost.primrec_encode_bitStr (Primrec.const _))))).of_eq
    fun z => (h z).symm

end CL.Sampler

/-! ## Questions as numbers -/

namespace Verifier

/-- The index of a bit string: the number whose binary digits it is, least significant first.
This is the `ℕ`-level form of `Verifier.questionEquiv`, and it is what the tabulation can
actually compute with — the question alphabet of a `GameData` is `Fin (nX + 1)`, so every
question reached by a sampler query has to be turned into a number. -/
def bitsToIdx : BitStr → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bitsToIdx l

@[simp] theorem bitsToIdx_nil : bitsToIdx [] = 0 := rfl

@[simp] theorem bitsToIdx_cons (b : Bool) (l : BitStr) :
    bitsToIdx (b :: l) = (if b then 1 else 0) + 2 * bitsToIdx l := rfl

theorem bitsToIdx_ofFn {s : ℕ} (f : Fin s → Bool) :
    bitsToIdx (List.ofFn f) = ∑ i : Fin s, (if f i then 1 else 0) * 2 ^ (i : ℕ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [List.ofFn_succ, bitsToIdx_cons, ih, Fin.sum_univ_succ, Finset.mul_sum]
    refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun i _ => ?_)
    rw [Fin.val_succ, pow_succ]
    ring

/-- The `Fin 2` form, where `finFunctionFinEquiv` is literally applicable: `CL.𝔽₂` is `ZMod 2`,
which reduces to `Fin 2` but does not unify with it at the transparency `rw` uses. -/
private theorem bitsToIdx_ofFn_fin2 {s : ℕ} (w : Fin s → Fin 2) :
    bitsToIdx (List.ofFn fun i => decide (w i = 1)) = (finFunctionFinEquiv w : ℕ) := by
  rw [bitsToIdx_ofFn, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ rfl
  revert i
  suffices h : ∀ a : Fin 2, (if decide (a = 1) then 1 else 0) = (a : ℕ) from fun i _ => h (w i)
  decide

/-- **The index of a question is the number its bit string denotes.** This is what lets the
tabulation name questions by numbers while the value agreement is read along
`questionEquiv`. -/
@[simp] theorem questionEquiv_symm_val {s : ℕ} (v : Fin s → CL.𝔽₂) :
    (((questionEquiv s).symm v : Fin (2 ^ s)) : ℕ) = bitsToIdx (CL.toBits v) :=
  (bitsToIdx_ofFn_fin2 v).symm

@[simp] theorem bitsToIdx_toBits_questionEquiv {s : ℕ} (i : Fin (2 ^ s)) :
    bitsToIdx (CL.toBits (questionEquiv s i)) = (i : ℕ) := by
  rw [← questionEquiv_symm_val, Equiv.symm_apply_apply]

/-! ## The question weights -/

/-- The index of a bit string is below `2 ^ its length`. -/
theorem bitsToIdx_lt (l : BitStr) : bitsToIdx l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => rw [bitsToIdx_cons, List.length_cons, pow_succ]; split <;> omega

theorem primrec_bitsToIdx : Primrec bitsToIdx := by
  have key : ∀ l : BitStr, bitsToIdx l = l.foldr (fun b m => (if b then 1 else 0) + 2 * m) 0 := by
    intro l; induction l with
    | nil => rfl
    | cons b l ih => rw [bitsToIdx_cons, ih, List.foldr_cons]
  have h1 : Primrec fun q : BitStr × (Bool × ℕ) => (if q.2.1 then 1 else 0) + 2 * q.2.2 :=
    Primrec.nat_add.comp
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) h1.to₂).of_eq fun l => (key l).symm

/-- **The weight list of a tabulation**: one entry of weight `1` for each point of `𝔽₂^s`, at
the index pair its two marginals land on. -/
def weightList (s : ℕ) (fA fB : BitStr → ℕ) : List (ℕ × ℕ × ℕ) :=
  (Data.bitStrsOfLen s).map fun z => (fA z, fB z, 1)

theorem questionWeight_weightList (nX nA s : ℕ) (fA fB : BitStr → ℕ)
    (acc : List (ℕ × ℕ × ℕ × ℕ)) (i j : ℕ) :
    (GameData.mk nX nA (weightList s fA fB) acc).questionWeight i j =
      ((Data.bitStrsOfLen s).filter fun z => decide (fA z = i ∧ fB z = j)).length := by
  show ((((weightList s fA fB).filter fun t => decide (t.1 = i ∧ t.2.1 = j)).map
    fun t => t.2.2).sum) = _
  rw [weightList, List.filter_map, List.map_map]
  simp [Function.comp_def]

/-- Every point of `𝔽₂^s` is counted once, so the total weight is `2 ^ s`. -/
theorem sum_filter_length {N : ℕ} (fA fB : BitStr → ℕ) (l : List BitStr)
    (hA : ∀ z ∈ l, fA z < N) (hB : ∀ z ∈ l, fB z < N) :
    ∑ x : Fin N, ∑ y : Fin N,
      (l.filter fun z => decide (fA z = x.val ∧ fB z = y.val)).length = l.length := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have hAz : fA z < N := hA z (by simp)
    have hBz : fB z < N := hB z (by simp)
    have hstep : ∀ x y : Fin N,
        ((z :: l).filter fun w => decide (fA w = x.val ∧ fB w = y.val)).length =
          (if fA z = x.val ∧ fB z = y.val then 1 else 0) +
            (l.filter fun w => decide (fA w = x.val ∧ fB w = y.val)).length := by
      intro x y
      rw [List.filter_cons]
      by_cases h : fA z = x.val ∧ fB z = y.val
      · rw [if_pos (by simpa using h), List.length_cons, if_pos h]; omega
      · rw [if_neg (by simpa using h), if_neg h]; omega
    simp only [hstep, Finset.sum_add_distrib]
    rw [ih (fun w hw => hA w (by simp [hw])) (fun w hw => hB w (by simp [hw])),
      List.length_cons]
    have hone : ∑ x : Fin N, ∑ y : Fin N,
        (if fA z = x.val ∧ fB z = y.val then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single (⟨fA z, hAz⟩ : Fin N)]
      · rw [Finset.sum_eq_single (⟨fB z, hBz⟩ : Fin N)]
        · simp
        · intro b _ hb
          exact if_neg fun h => hb (Fin.ext h.2.symm)
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · intro a _ ha
        exact Finset.sum_eq_zero fun b _ => if_neg fun h => ha (Fin.ext h.1.symm)
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    omega

/-- The total weight of the list is `2 ^ s`: every point of `𝔽₂^s` contributes `1`, and the
index pairs it can land on are all in range. That denominator is exactly the one `CL.clDist`
divides by. -/
theorem totalWeight_weightList (nX nA s : ℕ) (fA fB : BitStr → ℕ)
    (acc : List (ℕ × ℕ × ℕ × ℕ))
    (hA : ∀ z ∈ Data.bitStrsOfLen s, fA z < nX + 1)
    (hB : ∀ z ∈ Data.bitStrsOfLen s, fB z < nX + 1) :
    (GameData.mk nX nA (weightList s fA fB) acc).totalWeight = 2 ^ s := by
  show ∑ x : Fin (nX + 1), ∑ y : Fin (nX + 1),
    (GameData.mk nX nA (weightList s fA fB) acc).questionWeight x.val y.val = _
  simp only [questionWeight_weightList]
  rw [sum_filter_length fA fB _ hA hB, Data.length_bitStrsOfLen]


/-- **Counting over `𝔽₂^s` by enumerating bit strings.** The bit strings of length `s` are the
vectors of `𝔽₂^s`, so a count over one is a count over the other — which is what turns the
tabulation's weight list into the numerator of `CL.clDist`. -/
theorem length_filter_bitStrsOfLen {s : ℕ} (P : (Fin s → CL.𝔽₂) → Bool) :
    ((Data.bitStrsOfLen s).filter fun z => P (CL.ofBits s z)).length
      = (Finset.univ.filter fun v : Fin s → CL.𝔽₂ => P v = true).card := by
  classical
  have hinj : ∀ z ∈ Data.bitStrsOfLen s, ∀ z' ∈ Data.bitStrsOfLen s,
      CL.ofBits s z = CL.ofBits s z' → z = z' := by
    intro z hz z' hz' h
    rw [← CL.toBits_ofBits ((Data.mem_bitStrsOfLen s z).1 hz),
      ← CL.toBits_ofBits ((Data.mem_bitStrsOfLen s z').1 hz'), h]
  have hnd : ((Data.bitStrsOfLen s).map (CL.ofBits s)).Nodup :=
    (Data.nodup_bitStrsOfLen s).map_on hinj
  have huniv : ((Data.bitStrsOfLen s).map (CL.ofBits s)).toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun v => List.mem_toFinset.2
      (List.mem_map.2 ⟨CL.toBits v, (Data.mem_bitStrsOfLen s _).2 (by simp), by simp⟩)
  have key : (((Data.bitStrsOfLen s).map (CL.ofBits s)).filter P).length
      = ((Data.bitStrsOfLen s).filter fun z => P (CL.ofBits s z)).length := by
    rw [List.filter_map, List.length_map]; rfl
  rw [← key, ← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter, huniv]

/-! ## Answers as numbers -/

/-- The index of a mapped element, when the map is injective on the list. -/
theorem idxOf_map_of_injOn {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (l : List α) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) {x : α} (hx : x ∈ l) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases hax : a = x
    · subst hax; simp
    · have hne : f a ≠ f x := fun h => hax (hinj a (by simp) x (by simp [hx]) h)
      have hxl : x ∈ l := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hax
        · exact h
      rw [List.map_cons, List.idxOf_cons_ne _ hne, List.idxOf_cons_ne _ hax,
        ih (fun u hu v hv h => hinj u (by simp [hu]) v (by simp [hv]) h) hxl]

/-- The answers of length at most `T` are indexed by their position among the bit strings of
length at most `T`: the enumeration `answerList` is `bitStrsLE` mapped by truncation, which is
the identity on those strings. -/
theorem answerEquiv_symm_val (T : ℕ) (a : Answers T) :
    (((answerEquiv T).symm a : Fin (answerList T).length) : ℕ) = (Data.bitStrsLE T).idxOf a.1 := by
  have hinj : ∀ x ∈ Data.bitStrsLE T, ∀ y ∈ Data.bitStrsLE T,
      toAnswer T x = toAnswer T y → x = y := by
    intro x hx y hy h
    have ex : x.take T = x := List.take_of_length_le ((Data.mem_bitStrsLE T x).1 hx)
    have ey : y.take T = y := List.take_of_length_le ((Data.mem_bitStrsLE T y).1 hy)
    rw [← ex, ← ey]
    exact congrArg Subtype.val h
  calc (((answerEquiv T).symm a : Fin (answerList T).length) : ℕ)
      = ((Data.bitStrsLE T).map (toAnswer T)).idxOf (toAnswer T a.1) := by
        rw [toAnswer_val]; rfl
    _ = (Data.bitStrsLE T).idxOf a.1 :=
        idxOf_map_of_injOn _ _ hinj ((Data.mem_bitStrsLE T a.1).2 a.2)

/-! ## The acceptance table -/

/-- `bitsToIdx` is injective on the bit strings of a fixed length: it is the binary expansion,
read through `questionEquiv`. -/
theorem bitsToIdx_injOn {s : ℕ} {x y : BitStr} (hx : x.length = s) (hy : y.length = s)
    (h : bitsToIdx x = bitsToIdx y) : x = y := by
  have hx' : CL.toBits (CL.ofBits s x) = x := CL.toBits_ofBits hx
  have hy' : CL.toBits (CL.ofBits s y) = y := CL.toBits_ofBits hy
  have := h
  rw [← hx', ← hy', ← questionEquiv_symm_val, ← questionEquiv_symm_val] at this
  rw [← hx', ← hy', (questionEquiv s).symm.injective (Fin.ext this)]

/-! ## The doubled question alphabet, indexed

A question of the doubled game is a tag bit and a point of `𝔽₂^s`. It is packed into one
number by **prepending the tag bit to the point's bit string**: the index of `(b, v)` is
`bitsToIdx (b :: CL.toBits v)`. Three things this packing buys, and they are the reason for
it:

* the packed index is `bitsToIdx` of a bit string of length `s + 1`, so `bitsToIdx_lt` bounds
  it by `2 ^ (s + 1)` and `bitsToIdx_injOn` — injectivity on strings of a *fixed length* —
  reads it back, both verbatim at `s + 1`;
* Alice's indices are even and Bob's odd, so the two copies are automatically disjoint;
* nothing else in the tabulation changes: the weight list still enumerates `𝔽₂^s`.
-/

/-- `CL.toBits` is injective: it is the binary expansion read by `questionEquiv`. -/
theorem toBits_injective (s : ℕ) :
    Function.Injective (CL.toBits (s := s)) := by
  intro v w h
  refine (questionEquiv s).symm.injective (Fin.ext ?_)
  rw [questionEquiv_symm_val, questionEquiv_symm_val, h]

/-- **The packing is injective, componentwise.** This is `bitsToIdx_injOn` at length `s + 1`,
which is why the tag is *prepended* rather than appended or added as an offset. -/
theorem bitsToIdx_cons_toBits_inj {s : ℕ} {b c : Bool} {v w : Fin s → CL.𝔽₂}
    (h : bitsToIdx (b :: CL.toBits v) = bitsToIdx (c :: CL.toBits w)) : b = c ∧ v = w := by
  have hlen : ∀ (d : Bool) (u : Fin s → CL.𝔽₂), (d :: CL.toBits u).length = s + 1 := by
    intro d u; simp
  obtain ⟨hb, hv⟩ := List.cons_eq_cons.mp (bitsToIdx_injOn (hlen b v) (hlen c w) h)
  exact ⟨hb, toBits_injective s hv⟩

theorem bitsToIdx_cons_toBits_eq_iff {s : ℕ} (b c : Bool) (v w : Fin s → CL.𝔽₂) :
    bitsToIdx (b :: CL.toBits v) = bitsToIdx (c :: CL.toBits w) ↔ b = c ∧ v = w :=
  ⟨bitsToIdx_cons_toBits_inj, fun h => by rw [h.1, h.2]⟩

/-- The packed index of a tagged question. -/
def tagIdx {s : ℕ} (p : Bool × (Fin s → CL.𝔽₂)) : Fin (2 ^ (s + 1)) :=
  ⟨bitsToIdx (p.1 :: CL.toBits p.2), by simpa using bitsToIdx_lt (p.1 :: CL.toBits p.2)⟩

theorem tagIdx_injective (s : ℕ) : Function.Injective (tagIdx (s := s)) := by
  rintro ⟨b, v⟩ ⟨c, w⟩ h
  obtain ⟨hb, hv⟩ := bitsToIdx_cons_toBits_inj (congrArg Fin.val h)
  exact Prod.ext hb hv

/-- **The doubled question alphabet.** -/
noncomputable def tagEquiv (s : ℕ) : Bool × (Fin s → CL.𝔽₂) ≃ Fin (2 ^ (s + 1)) :=
  Equiv.ofBijective tagIdx
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨tagIdx_injective s, by
      simp [Fintype.card_prod, pow_succ, mul_comm]⟩)

/-- **Reading a packed index back.** -/
theorem bitsToIdx_tagEquiv_symm (s : ℕ) (i : Fin (2 ^ (s + 1))) :
    bitsToIdx (((tagEquiv s).symm i).1 :: CL.toBits ((tagEquiv s).symm i).2) = (i : ℕ) :=
  congrArg Fin.val ((tagEquiv s).apply_symm_apply i)

@[simp] theorem tagEquiv_apply (s : ℕ) (p : Bool × (Fin s → CL.𝔽₂)) :
    ((tagEquiv s p : Fin (2 ^ (s + 1))) : ℕ) = bitsToIdx (p.1 :: CL.toBits p.2) := rfl

/-- **The acceptance table**: the index tuples of the answer tuples a predicate accepts,
enumerated over the two alphabets. -/
def accList (s T : ℕ) (acc? : BitStr → BitStr → BitStr → BitStr → Bool) :
    List (ℕ × ℕ × ℕ × ℕ) :=
  (Data.bitStrsOfLen s).flatMap fun x =>
    (Data.bitStrsOfLen s).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).filterMap fun b =>
          if acc? x y a b then
            some (bitsToIdx x, bitsToIdx y,
              (Data.bitStrsLE T).idxOf a, (Data.bitStrsLE T).idxOf b)
          else none

theorem mem_accList_iff {s T : ℕ} {acc? : BitStr → BitStr → BitStr → BitStr → Bool}
    {i j k l : ℕ} :
    (i, j, k, l) ∈ accList s T acc? ↔
      ∃ x ∈ Data.bitStrsOfLen s, ∃ y ∈ Data.bitStrsOfLen s,
        ∃ a ∈ Data.bitStrsLE T, ∃ b ∈ Data.bitStrsLE T,
          acc? x y a b = true ∧ i = bitsToIdx x ∧ j = bitsToIdx y ∧
            k = (Data.bitStrsLE T).idxOf a ∧ l = (Data.bitStrsLE T).idxOf b := by
  simp only [accList, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, h⟩
    by_cases hc : acc? x y a b
    · rw [if_pos hc] at h
      obtain ⟨hi, hj, hk, hl⟩ : bitsToIdx x = i ∧ bitsToIdx y = j ∧
          (Data.bitStrsLE T).idxOf a = k ∧ (Data.bitStrsLE T).idxOf b = l := by simpa using h
      exact ⟨x, hx, y, hy, a, ha, b, hb, hc, hi.symm, hj.symm, hk.symm, hl.symm⟩
    · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, hc, rfl, rfl, rfl, rfl⟩
    exact ⟨x, hx, y, hy, a, ha, b, hb, by rw [if_pos hc]⟩


/-! ## The acceptance table is primitive recursive

Written as four nested `Primrec.list_flatMap` the proof diverges at `whnf`: each body carries
the accumulated parameter tuple and unification grows with it. Flattening the product *first*
makes every `flatMap` body a bare tuple constructor, and the table is then one `filterMap` over
the flat list (`accList_eq_filterMap`) — with `Verifier.accList` itself unchanged.
-/

/-- The four-fold product of the two enumerations, as one flat list. -/
def tuples (s T : ℕ) : List (BitStr × BitStr × BitStr × BitStr) :=
  (Data.bitStrsOfLen s).flatMap fun x =>
    (Data.bitStrsOfLen s).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).map fun b => (x, y, a, b)

theorem primrec_tuples : Primrec₂ tuples := by
  have h4 : Primrec fun q : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1.1.2).map fun b => (q.1.1.2, q.1.2, q.2, b) := by
    refine Primrec.list_map
      (Data.primrec_bitStrsLE.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      ?_
    have hx : Primrec fun r : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hy : Primrec fun r : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have ha : Primrec fun r : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.2 := Primrec.snd.comp Primrec.fst
    exact (hx.pair (hy.pair (ha.pair Primrec.snd))).to₂
  have h3 : Primrec fun q : (((ℕ × ℕ) × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1.2).flatMap fun a =>
        (Data.bitStrsLE q.1.1.2).map fun b => (q.1.2, q.2, a, b) :=
    Primrec.list_flatMap
      (Data.primrec_bitStrsLE.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) h4.to₂
  have h2 : Primrec fun q : ((ℕ × ℕ) × BitStr) =>
      (Data.bitStrsOfLen q.1.1).flatMap fun y =>
        (Data.bitStrsLE q.1.2).flatMap fun a =>
          (Data.bitStrsLE q.1.2).map fun b => (q.2, y, a, b) :=
    Primrec.list_flatMap (Data.primrec_bitStrsOfLen.comp (Primrec.fst.comp Primrec.fst)) h3.to₂
  exact (Primrec.list_flatMap (Data.primrec_bitStrsOfLen.comp Primrec.fst) h2.to₂).to₂


def accListW (s T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) : List (ℕ × ℕ × ℕ × ℕ) :=
  (Data.bitStrsOfLen s).flatMap fun x =>
    (Data.bitStrsOfLen s).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).filterMap fun b =>
          if acc? x y a b then
            some (fA x, fB y, (Data.bitStrsLE T).idxOf a, (Data.bitStrsLE T).idxOf b)
          else none

theorem accList_eq_accListW (s T : ℕ) (acc? : BitStr → BitStr → BitStr → BitStr → Bool) :
    accList s T acc? = accListW s T bitsToIdx bitsToIdx acc? := rfl

theorem mem_accListW_iff {s T : ℕ} {fA fB : BitStr → ℕ}
    {acc? : BitStr → BitStr → BitStr → BitStr → Bool} {i j k l : ℕ} :
    (i, j, k, l) ∈ accListW s T fA fB acc? ↔
      ∃ x ∈ Data.bitStrsOfLen s, ∃ y ∈ Data.bitStrsOfLen s,
        ∃ a ∈ Data.bitStrsLE T, ∃ b ∈ Data.bitStrsLE T,
          acc? x y a b = true ∧ i = fA x ∧ j = fB y ∧
            k = (Data.bitStrsLE T).idxOf a ∧ l = (Data.bitStrsLE T).idxOf b := by
  simp only [accListW, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, h⟩
    by_cases hc : acc? x y a b
    · rw [if_pos hc] at h
      obtain ⟨hi, hj, hk, hl⟩ : fA x = i ∧ fB y = j ∧
          (Data.bitStrsLE T).idxOf a = k ∧ (Data.bitStrsLE T).idxOf b = l := by simpa using h
      exact ⟨x, hx, y, hy, a, ha, b, hb, hc, hi.symm, hj.symm, hk.symm, hl.symm⟩
    · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, hc, rfl, rfl, rfl, rfl⟩
    exact ⟨x, hx, y, hy, a, ha, b, hb, by rw [if_pos hc]⟩

theorem accListW_eq_filterMap (s T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) :
    accListW s T fA fB acc? = (tuples s T).filterMap fun q =>
      if acc? q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA q.1, fB q.2.1,
          (Data.bitStrsLE T).idxOf q.2.2.1, (Data.bitStrsLE T).idxOf q.2.2.2)
      else none := by
  simp only [accListW, tuples, List.filterMap_flatMap, List.filterMap_map, Function.comp_def]

theorem primrec_accListW {α : Type*} [Primcodable α] {s T : α → ℕ} {fA fB : BitStr → ℕ}
    {acc? : α → BitStr → BitStr → BitStr → BitStr → Bool}
    (hs : Primrec s) (hT : Primrec T) (hfA : Primrec fA) (hfB : Primrec fB)
    (hacc : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :
    Primrec fun a => Verifier.accListW (s a) (T a) fA fB (acc? a) := by
  have hbl : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Data.bitStrsLE (T q.1) := Data.primrec_bitStrsLE.comp (hT.comp Primrec.fst)
  have hbody : Primrec₂ fun (a : α) (q : BitStr × BitStr × BitStr × BitStr) =>
      (if acc? a q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA q.1, fB q.2.1,
          (Data.bitStrsLE (T a)).idxOf q.2.2.1, (Data.bitStrsLE (T a)).idxOf q.2.2.2)
        else none) := by
    refine Primrec.ite ⟨inferInstance, hacc.of_eq fun q => by
        cases h : acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 <;> simp [h]⟩ ?_ (Primrec.const none)
    refine Primrec.option_some.comp
      ((hfA.comp (Primrec.fst.comp Primrec.snd)).pair
        ((hfB.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
          ((Cost.primrec_idxOf_bitStr.comp
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl).pair
            (Cost.primrec_idxOf_bitStr.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl))))
  exact (Primrec.listFilterMap (primrec_tuples.comp hs hT) hbody).of_eq fun a =>
    (accListW_eq_filterMap (s a) (T a) fA fB (acc? a)).symm

/-- The original `primrec_accList` is the case `fA = fB = bitsToIdx`, so generalizing costs
nothing downstream. -/
theorem primrec_accList_of_W {α : Type*} [Primcodable α] {s T : α → ℕ}
    {acc? : α → BitStr → BitStr → BitStr → BitStr → Bool}
    (hs : Primrec s) (hT : Primrec T)
    (hacc : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :
    Primrec fun a => Verifier.accList (s a) (T a) (acc? a) :=
  primrec_accListW hs hT primrec_bitsToIdx primrec_bitsToIdx hacc

/-- Prepending a fixed tag bit is primitive recursive. -/
theorem primrec_tagIdxOf (b : Bool) : Primrec fun z : BitStr => bitsToIdx (b :: z) :=
  primrec_bitsToIdx.comp (Primrec.list_cons.comp (Primrec.const b) Primrec.id)

end Verifier

/-! ## The tabulation on parameters alone

`tabOf sd pd s T n` is the `GameData` five numbers describe: `sd` the encoded sampler
program, `pd` the encoded decider program, `s` the sampler's dimension at level `n`, `T` the
answer-length cut and `n` the level itself. Nothing here mentions a `Verifier`, and that is
the point — a `Verifier` is a structure carrying proofs, so a function of one is not data,
while `Primrec` needs its input to be. The bridge back, that on an `n`-bounded verifier these
numbers compute the verifier's own sampler and decider, is `MIPRE.Halting.dimOf_eq`,
`margOf_eq` and `accOf_iff` in `Halting/Instantiation.lean`.

The three components run the two programs under the budget boundedness supplies: `dimOf` and
`margOf` one sampler query each (`CL.Sampler.queryUnder` at `T = n ^ n`, `k = n`), `accOf`
one decider run (`Decider.acceptBudget`). Each defaults — to `0`, `[]`, `false` — when the
budget is missed or the answer does not decode, which is what makes them total; on a bounded
verifier the default is never taken.
-/

namespace Halting

def dimOf (sd : Data) (B k n : ℕ) : ℕ :=
  ((Machine.runForD sd (encode (n, CL.Sampler.Query.dimension))
      (B * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ k)).bind
    fun d => (SizedEncoding.decode d : Option ℕ)).getD 0

/-- Player `w`'s marginal question at the point `z`, under the budget `B * (|q| + 1) ^ k`. -/
def margOf (sd : Data) (B k n : ℕ) (w : Player) (z : BitStr) : BitStr :=
  ((Machine.runForD sd (encode (n, CL.Sampler.Query.marginal w 7 z))
      (B * ((encode (CL.Sampler.Query.marginal w 7 z) : Data).size + 1) ^ k)).bind
    fun d => (SizedEncoding.decode d : Option BitStr)).getD []

/-- Acceptance, from the encoded decider program alone. Unlike the two sampler runs this one
cannot be re-budgeted off `GapCompression.sampler_time`: the decider of the verifier a string
denotes is the string's *own*, wrapped, and nothing bounds it unconditionally. So `accOf` keeps
the budget `n`-boundedness supplies, and `MIPRE.Halting.accOf_iff` keeps its hypothesis.

`decide (… = some …)` rather than `… == some …`: the `BEq` a `==` elaborates to here is not the
one `Primrec.eq` is stated at, and reconciling them is a long detour for no gain. -/
def accOf (pd : Data) (n : ℕ) (x y a b : BitStr) : Bool :=
  decide (Machine.runForD pd (encode (n, x, y, a, b))
    (Decider.acceptBudget (n ^ n) n x y a b) = some (encode true))

/-- **The tabulation**, doubled and re-budgeted.  Alice's question index is her marginal's bit
string with a `false` tag prepended, Bob's with a `true` tag: the two blocks are disjoint and
the diagonal carries no weight.  The weight list still enumerates `𝔽₂^s` once, so the total
weight is still `2 ^ s`. -/
def tabOf (sd pd : Data) (s T B k n : ℕ) : GameData where
  nX := 2 ^ (s + 1) - 1
  nA := (Data.bitStrsLE T).length - 1
  w := Verifier.weightList s
        (fun z => Verifier.bitsToIdx (false :: margOf sd B k n .alice z))
        (fun z => Verifier.bitsToIdx (true :: margOf sd B k n .bob z))
  acc := Verifier.accListW s T (fun u => Verifier.bitsToIdx (false :: u))
          (fun v => Verifier.bitsToIdx (true :: v)) (accOf pd n)

theorem primrec_dimOf {α : Type*} [Primcodable α] {sd : α → Data} {B lvl : α → ℕ} (k : ℕ)
    (hsd : Primrec sd) (hB : Primrec B) (hlvl : Primrec lvl) :
    Primrec fun a : α => dimOf (sd a) (B a) k (lvl a) := by
  have hbudget : Primrec fun a : α =>
      B a * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ k :=
    Primrec.nat_mul.comp hB (primrec_nat_pow.comp (Primrec.const _) (Primrec.const k))
  have hinput : Primrec fun a : α => (encode (lvl a, CL.Sampler.Query.dimension) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hlvl)
      (Primrec.const (encode CL.Sampler.Query.dimension : Data))
  exact Primrec.option_getD.comp
    (Primrec.option_bind (Machine.primrec_runForD.comp ((hsd.pair hinput).pair hbudget))
      (Data.primrec_decode_nat.comp Primrec.snd).to₂)
    (Primrec.const 0)

theorem primrec_margOf {α : Type*} [Primcodable α] {sd : α → Data} {B lvl : α → ℕ} (k : ℕ)
    (hsd : Primrec sd) (hB : Primrec B) (hlvl : Primrec lvl) (w : Player) :
    Primrec fun q : α × BitStr => margOf (sd q.1) (B q.1) k (lvl q.1) w q.2 := by
  have hq : Primrec fun q : α × BitStr =>
      (encode (CL.Sampler.Query.marginal w 7 q.2) : Data) :=
    (CL.Sampler.primrec_encode_marginal w 7).comp Primrec.snd
  have hinput : Primrec fun q : α × BitStr =>
      (encode (lvl q.1, CL.Sampler.Query.marginal w 7 q.2) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp (hlvl.comp Primrec.fst)) hq
  have hbudget : Primrec fun q : α × BitStr =>
      B q.1 * ((encode (CL.Sampler.Query.marginal w 7 q.2) : Data).size + 1) ^ k :=
    Primrec.nat_mul.comp (hB.comp Primrec.fst)
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp hq)) (Primrec.const k))
  exact Primrec.option_getD.comp
    (Primrec.option_bind
      (Machine.primrec_runForD.comp (((hsd.comp Primrec.fst).pair hinput).pair hbudget))
      (Data.primrec_decode_bitStr.comp Primrec.snd).to₂)
    (Primrec.const [])

/-- The weight list of the doubled, re-budgeted tabulation.  `Verifier.weightList` itself is
untouched: only the two index maps it is applied to have changed. -/
theorem primrec_weightList {α : Type*} [Primcodable α] {sd : α → Data} {s B lvl : α → ℕ}
    (k : ℕ) (hsd : Primrec sd) (hs : Primrec s) (hB : Primrec B) (hlvl : Primrec lvl) :
    Primrec fun a : α =>
      Verifier.weightList (s a)
        (fun z => Verifier.bitsToIdx (false :: margOf (sd a) (B a) k (lvl a) .alice z))
        (fun z => Verifier.bitsToIdx (true :: margOf (sd a) (B a) k (lvl a) .bob z)) := by
  refine Primrec.list_map (Data.primrec_bitStrsOfLen.comp hs) ?_
  exact (((Verifier.primrec_tagIdxOf false).comp
      (primrec_margOf k hsd hB hlvl Player.alice)).pair
    (((Verifier.primrec_tagIdxOf true).comp
      (primrec_margOf k hsd hB hlvl Player.bob)).pair (Primrec.const 1))).to₂

set_option maxHeartbeats 1000000 in
/-- `primrec_accOf`, generic in the ambient parameter type.  `accOf` reads only the decider
data and the level, so the shape of the tuple carrying them is irrelevant.  Stating it this way
is what makes the re-budget cheap: a change to `tabOf`'s parameter list never re-runs this
proof, which measures 210049 heartbeats at one fixed tuple, and composing it with a projection
to reach a wider one times out at the default budget. -/
theorem primrec_accOf {α : Type*} [Primcodable α] {pd : α → Data} {lvl : α → ℕ}
    (hpd : Primrec pd) (hlvl : Primrec lvl) :
    Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      accOf (pd q.1) (lvl q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have hpd' : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => pd q.1 :=
    hpd.comp Primrec.fst
  have hn : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => lvl q.1 :=
    hlvl.comp Primrec.fst
  have hx : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hy : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hebs : Primrec fun l : BitStr => (encode l : Data) := primrec_encode_bitStr
  have htup : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => (encode q.2 : Data) :=
    Data.primrec_cons.comp (hebs.comp hx)
      (Data.primrec_cons.comp (hebs.comp hy)
        (Data.primrec_cons.comp (hebs.comp ha) (hebs.comp hb)))
  have hinput : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      (encode (lvl q.1, q.2) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hn) htup
  have hbudget : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Decider.acceptBudget (lvl q.1 ^ lvl q.1) (lvl q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 :=
    Primrec.nat_mul.comp (primrec_nat_pow.comp hn hn)
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp htup)) hn)
  have hfin : PrimrecPred fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Machine.runForD (pd q.1) (encode (lvl q.1, q.2))
        (Decider.acceptBudget (lvl q.1 ^ lvl q.1) (lvl q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
        = some (encode true) :=
    Primrec.eq.comp (Machine.primrec_runForD.comp ((hpd'.pair hinput).pair hbudget))
      (Primrec.const (some (encode true) : Option Data))
  exact (Primrec.ite hfin (Primrec.const true) (Primrec.const false)).of_eq fun q => by
    simp only [accOf]; split <;> simp_all

/-- **O2, computability, on numbers alone**: the doubled, re-budgeted tabulation is primitive
recursive in every one of its parameters. -/
theorem primrec_tabOf {α : Type*} [Primcodable α] {sd pd : α → Data} {s T B lvl : α → ℕ}
    (k : ℕ) (hsd : Primrec sd) (hpd : Primrec pd) (hs : Primrec s) (hT : Primrec T)
    (hB : Primrec B) (hlvl : Primrec lvl) :
    Primrec fun a : α => tabOf (sd a) (pd a) (s a) (T a) (B a) k (lvl a) := by
  have hnX : Primrec fun a : α => 2 ^ (s a + 1) - 1 :=
    Primrec.nat_sub.comp
      (primrec_nat_pow.comp (Primrec.const 2) (Primrec.succ.comp hs)) (Primrec.const 1)
  have hnA : Primrec fun a : α => (Data.bitStrsLE (T a)).length - 1 :=
    Primrec.nat_sub.comp (Primrec.list_length.comp (Data.primrec_bitStrsLE.comp hT))
      (Primrec.const 1)
  have hacc := Verifier.primrec_accListW (s := s) (T := T)
    (fA := fun u => Verifier.bitsToIdx (false :: u))
    (fB := fun v => Verifier.bitsToIdx (true :: v))
    (acc? := fun a => accOf (pd a) (lvl a)) hs hT
    (Verifier.primrec_tagIdxOf false) (Verifier.primrec_tagIdxOf true)
    (primrec_accOf hpd hlvl)
  refine ((Primrec.of_equiv_symm (e := GameData.equivTuple)).comp
    (hnX.pair (hnA.pair ((primrec_weightList k hsd hs hB hlvl).pair hacc)))).of_eq ?_
  intro a
  rfl

end Halting

end MIPRE
