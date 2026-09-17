/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.Describer
import MIPRE.TM.CookLevin.Correct
import MIPRE.TM.CookLevin.Sound

/-!
# The described formula and the answers

The two halves of item 1 of `thm:succinct-sat` for the describer: a satisfying assignment of
the described formula extending the two answer blocks exists iff the blocks are the two-bit
tape encodings (`tapeBits`) of strings of length at most `T` that the decider accepts within
`T` (`planning/succinct-cook-levin.md`, S3).

The bridge in both directions is the decoding: an assignment of the formula gives the tableau
assignment `w ∘ idxOf` (`sat_tableau_of_sat_formula3`), and an assignment of the tableau gives
the formula assignment `decodeVar · |>.elim false` (`sat_formula3_of_sat_tableau`). The answer
blocks match because the canonical index of an answer cell is its answer index (`idxOf_ans`)
and because a time-`0` row of a free tape reads exactly the tape encoding of the string it
holds (`decide_val_inputCellVal`).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost Fml

/-! ## The two-bit tape encoding on a time-`0` row -/

@[simp] theorem length_bits (l : BitStr) : (bits l).length = l.length := List.length_map _

theorem getElem_bits (l : BitStr) (k : ℕ) (h : k < (bits l).length) :
    (bits l)[k] = if l[k]'(by simpa using h) then Sym.one else Sym.zero :=
  List.getElem_map _

/-- The bit string of a list of symbols over `{0, 1}`. -/
def boolsOf (s : List Sym) : BitStr := s.map fun c => decide (c = Sym.one)

@[simp] theorem length_boolsOf (s : List Sym) : (boolsOf s).length = s.length := List.length_map _

theorem bits_boolsOf (s : List Sym) (h : ∀ c ∈ s, c = Sym.zero ∨ c = Sym.one) :
    bits (boolsOf s) = s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    rw [boolsOf, List.map_cons, bits_cons, ← boolsOf,
      ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    rcases h c (List.mem_cons_self ..) with rfl | rfl <;> simp

/-- **The time-`0` row of a free tape reads the tape encoding of the string it holds**: the
cell at position `k / 2 + 3` holds the blank for `k` even and `1` for `k` odd exactly when the
`k`-th bit of the encoding is set. -/
theorem decide_val_inputCellVal (e : ℕ) (ap : BitStr) (k : ℕ) {p : Pos (Sof e)}
    (hp : (p : ℕ) = k / 2 + 3) (hk : k < 2 * Sof e) :
    decide ((if k % 2 = 1 then CellVal.sym Sym.one else CellVal.blank) =
      inputCellVal (bits ap) p) = tapeBits ap k := by
  obtain ⟨pv, hpv⟩ := p
  subst hp
  have hnb : ¬ Pos.IsBdry (⟨k / 2 + 3, hpv⟩ : Pos (Sof e)) := by
    rw [isBdry_iff]
    simp only [Fin.val_mk]
    omega
  have hval : inputCellVal (bits ap) (⟨k / 2 + 3, hpv⟩ : Pos (Sof e)) =
      (ap[k / 2]?).elim CellVal.blank fun c => CellVal.sym (if c then Sym.one else Sym.zero) := by
    rw [inputCellVal, if_neg hnb]
    simp only [Fin.val_mk, Nat.add_sub_cancel]
    by_cases hin : k / 2 < ap.length
    · rw [dif_pos (show 3 ≤ k / 2 + 3 ∧ k / 2 < (bits ap).length from
        ⟨by omega, by simpa using hin⟩), List.getElem?_eq_getElem hin, getElem_bits]
      rfl
    · rw [dif_neg (show ¬ (3 ≤ k / 2 + 3 ∧ k / 2 < (bits ap).length) by
        rw [length_bits]; omega), List.getElem?_eq_none (by omega)]
      rfl
  rw [hval, tapeBits]
  by_cases hodd : k % 2 = 1
  · rw [if_pos hodd, if_neg (by omega : ¬ k % 2 = 0)]
    rcases hh : ap[k / 2]? with _ | c
    · simp [cellBits]
    · cases c <;> simp [cellBits]
  · rw [if_neg hodd, if_pos (by omega : k % 2 = 0)]
    rcases hh : ap[k / 2]? with _ | c
    · simp [cellBits]
    · cases c <;> simp [cellBits]

/-! ## The two bridges -/

section Bridge

variable (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)

/-- The assignment of the described formula read off a tableau assignment through the
decoding. -/
noncomputable def wOf (A : TabVar 7 6 Sym Ctl (Sof e) Gc → Bool) (i : Fin (2 ^ mOf e Gc)) : Bool :=
  (decodeVar e Gc (fieldsOf e Gc T (bitsOfNat (mOf e Gc) (i : ℕ)))).elim false A

theorem wOf_of_decode {A : TabVar 7 6 Sym Ctl (Sof e) Gc → Bool} {i : Fin (2 ^ mOf e Gc)}
    {v : TabVar 7 6 Sym Ctl (Sof e) Gc}
    (h : decodeVar e Gc (fieldsOf e Gc T (bitsOfNat (mOf e Gc) (i : ℕ))) = some v) :
    wOf e T A i = A v := by
  rw [wOf, h]
  rfl

/-- **From a tableau assignment to an assignment of the described formula.** -/
theorem sat_formula3_of_sat_tableau (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y)
    (hTm : T + 3 < 2 ^ W e) (A : TabVar 7 6 Sym Ctl (Sof e) Gc → Bool)
    (hA : (tableauPlus e T (fixedOf D n T x y) chk).Sat A) :
    ((descCirc e T D n x y).formula3 (mOf e Gc)).Sat (wOf e T A) := by
  intro c hc
  obtain ⟨cl, hcl, hdec⟩ := (mem_formula3_iff e T c D n x y hT hlen hTm).mp hc
  simp only [candOfClause, Cand.Dec, LitDec] at hdec
  obtain ⟨⟨hd1, hs1⟩, ⟨hd2, hs2⟩, ⟨hd3, hs3⟩⟩ := hdec
  have key : Clause3.eval (wOf e T A) c = Clause3.eval A cl := by
    simp only [Clause3.eval, Lit.eval, wOf_of_decode e T hd1, wOf_of_decode e T hd2,
      wOf_of_decode e T hd3, hs1, hs2, hs3]
  rw [key]
  exact hA cl hcl

/-- **From an assignment of the described formula to a tableau assignment.** -/
theorem sat_tableau_of_sat_formula3 (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y)
    (hTm : T + 3 < 2 ^ W e) (w : Fin (2 ^ mOf e Gc) → Bool)
    (hw : ((descCirc e T D n x y).formula3 (mOf e Gc)).Sat w) :
    (tableauPlus e T (fixedOf D n T x y) chk).Sat
      fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩ := by
  intro cl hcl
  refine
    let c : Clause3 (Fin (2 ^ mOf e Gc)) :=
      ⟨⟨⟨idxOf e Gc T cl.l₁.var, idxOf_lt e Gc T hT _⟩, cl.l₁.pos⟩,
        ⟨⟨idxOf e Gc T cl.l₂.var, idxOf_lt e Gc T hT _⟩, cl.l₂.pos⟩,
        ⟨⟨idxOf e Gc T cl.l₃.var, idxOf_lt e Gc T hT _⟩, cl.l₃.pos⟩⟩
    ?_
  have hc : c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) := by
    refine (mem_formula3_iff e T c D n x y hT hlen hTm).mpr ⟨cl, hcl, ?_, ?_, ?_⟩
    · exact ⟨decodeVar_fieldsOf_idxOf e Gc T hT _, rfl⟩
    · exact ⟨decodeVar_fieldsOf_idxOf e Gc T hT _, rfl⟩
    · exact ⟨decodeVar_fieldsOf_idxOf e Gc T hT _, rfl⟩
  have key : Clause3.eval w c =
      Clause3.eval (fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩) cl := by
    simp only [Clause3.eval, Lit.eval, c]
  have hres := hw c hc
  rw [key] at hres
  exact hres

end Bridge

/-! ## The input tapes of the machine -/

theorem mem_bits' {s : Sym} {l : BitStr} (h : s ∈ bits l) : s = Sym.zero ∨ s = Sym.one := by
  rw [bits, List.mem_map] at h
  obtain ⟨c, -, rfl⟩ := h
  cases c <;> simp

theorem hfix_uInput (D : Prog) (n T : ℕ) (x y ap bp : BitStr) :
    ∀ (j : Fin 7) (s : List Sym), fixedOf D n T x y j = some s →
      uInput D n T x y ap bp j = s := by
  intro j s hj
  fin_cases j <;> simp_all [fixedOf, uInput]

theorem hfree_uInput (D : Prog) (n T : ℕ) (x y ap bp : BitStr) :
    ∀ j : Fin 7, fixedOf D n T x y j = none →
      ∀ s ∈ uInput D n T x y ap bp j, s = Sym.zero ∨ s = Sym.one := by
  intro j hj s hs
  fin_cases j
  · simp [fixedOf] at hj
  · simp [fixedOf] at hj
  · simp [fixedOf] at hj
  · simp [fixedOf] at hj
  · simp [fixedOf] at hj
  · exact mem_bits' (by simpa [uInput] using hs)
  · exact mem_bits' (by simpa [uInput] using hs)

theorem decide_inputCellVal_val (e : ℕ) (ap : BitStr) (k : ℕ) {p : Pos (Sof e)}
    (hp : (p : ℕ) = k / 2 + 3) (hk : k < 2 * Sof e) :
    decide (inputCellVal (bits ap) p =
      (if k % 2 = 1 then CellVal.sym Sym.one else CellVal.blank)) = tapeBits ap k := by
  rw [← decide_val_inputCellVal e ap k hp hk]
  exact decide_eq_decide.mpr eq_comm

/-! ## Item 1 of the theorem -/

section Main

variable (𝒟 : Decider) (n T : ℕ) (x y : BitStr) (e : ℕ)

/-- **Completeness**: if the answers encode strings the decider accepts within `T`, the
described formula has a satisfying assignment extending them. -/
theorem extendsAnswers_of_encodesAccepted (hT : T ≤ Sof e)
    (hlen : FixedLen e 𝒟.prog n T x y) (hTm : T + 3 < 2 ^ W e)
    (hrb : ∀ ap bp : BitStr, ap.length ≤ T → bp.length ≤ T →
      runBound 𝒟.prog n x y ap bp T ≤ Sof e)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (a b : Fin (2 * T) → Bool)
    (h : EncodesAccepted 𝒟 n x y T a b) :
    ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)) a b := by
  obtain ⟨ap, bp, hap, hbp, ha, hb, hacc⟩ := h
  obtain ⟨m₀, hm₀, hfrom⟩ := accepts_of_acceptsWithin 𝒟 n x y ap bp T hap hbp hacc
  have hacc' : AcceptsIn U Sym.one (uInput 𝒟.prog n T x y ap bp) (Sof e) :=
    hfrom.acceptsIn (le_trans hm₀ (hrb ap bp hap hbp))
  set A := runAssign U Sym.one (input := uInput 𝒟.prog n T x y ap bp) chk with hAdef
  -- the tableau and the two answer-end clauses
  have hsatT : (tableauPlus e T (fixedOf 𝒟.prog n T x y) chk).Sat A := by
    rintro cl (hcl | hcl)
    · exact tableau_sat_of_acceptsIn U Sym.one chk Sym.zero Sym.one (fixedOf 𝒟.prog n T x y)
        chk_isCheckCircuit chk_refsLt (hfix_uInput 𝒟.prog n T x y ap bp)
        (hfree_uInput 𝒟.prog n T x y ap bp) hacc' cl hcl
    · obtain ⟨jt, p, hjt, hp, rfl⟩ := hcl
      rw [unit_eval, hAdef, runAssign_cell]
      have hcell : inputCellVal (uInput 𝒟.prog n T x y ap bp jt) p = CellVal.blank := by
        rcases hjt with hjt | hjt
        · have h5 : jt = Interp.A := Fin.ext (by rw [hjt]; rfl)
          rw [h5, uInput_A, inputCellVal, if_neg (by rw [isBdry_iff]; omega),
            dif_neg (by rw [length_bits]; omega)]
        · have h6 : jt = Interp.B := Fin.ext (by rw [hjt]; rfl)
          rw [h6, uInput_B, inputCellVal, if_neg (by rw [isBdry_iff]; omega),
            dif_neg (by rw [length_bits]; omega)]
      simp only [baseAssign, cellValAt_inl, hcell, decide_eq_true_eq]
  refine ⟨wOf e T A, ?_, ?_, sat_formula3_of_sat_tableau e T 𝒟.prog n x y hT hlen hTm A hsatT⟩
  · intro j
    obtain ⟨jt, p, hjt, hp, hdec⟩ := decodeVar_ans e Gc T hT (show (j : ℕ) < 4 * T by omega)
    have hrj : rOf T (j : ℕ) = (j : ℕ) := by unfold rOf; rw [if_pos (by omega)]
    have h5 : jt = Interp.A := Fin.ext (by rw [hjt]; unfold tapeIdx; rw [if_pos (by omega)]; rfl)
    rw [show wOf e T A ⟨(j : ℕ), by omega⟩ = A (.cell 0 (.inl jt) p (valOf T (j : ℕ))) from
      wOf_of_decode e T hdec, ha j, hAdef, runAssign_cell]
    simp only [baseAssign, cellValAt_inl, h5, uInput_A, valOf, hrj]
    exact decide_inputCellVal_val e ap (j : ℕ) (by rw [hp, hrj]) (by omega)
  · intro j
    obtain ⟨jt, p, hjt, hp, hdec⟩ :=
      decodeVar_ans e Gc T hT (show 2 * T + (j : ℕ) < 4 * T by omega)
    have hrj : rOf T (2 * T + (j : ℕ)) = (j : ℕ) := by
      unfold rOf
      rw [if_neg (by omega)]
      omega
    have h6 : jt = Interp.B := Fin.ext (by rw [hjt]; unfold tapeIdx; rw [if_neg (by omega)]; rfl)
    rw [show wOf e T A ⟨2 * T + (j : ℕ), by omega⟩ =
      A (.cell 0 (.inl jt) p (valOf T (2 * T + (j : ℕ)))) from wOf_of_decode e T hdec, hb j,
      hAdef, runAssign_cell]
    simp only [baseAssign, cellValAt_inl, h6, uInput_B, valOf, hrj]
    exact decide_inputCellVal_val e bp (j : ℕ) (by rw [hp, hrj]) (by omega)

/-- A blank at an interior cell bounds the string on the tape. -/
theorem length_le_of_inputCellVal_blank {S : ℕ} (s : List Sym) (p : Pos S) (hnb : ¬ Pos.IsBdry p)
    (h3 : 3 ≤ (p : ℕ)) (h : inputCellVal s p = CellVal.blank) : s.length ≤ (p : ℕ) - 3 := by
  rw [inputCellVal, if_neg hnb] at h
  by_contra hlt
  rw [dif_pos ⟨h3, by omega⟩] at h
  exact absurd h (by simp)

/-- **Soundness**: a satisfying assignment of the described formula extending the answers gives
strings of length at most `T`, encoded by the answers, that the decider accepts within `T`. -/
theorem encodesAccepted_of_extendsAnswers (hT : T ≤ Sof e)
    (hlen : FixedLen e 𝒟.prog n T x y) (hTm : T + 3 < 2 ^ W e)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (a b : Fin (2 * T) → Bool)
    (h : ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)) a b) :
    EncodesAccepted 𝒟 n x y T a b := by
  obtain ⟨w, hwa, hwb, hsat⟩ := h
  have hAsat := sat_tableau_of_sat_formula3 e T 𝒟.prog n x y hT hlen hTm w hsat
  set A : TabVar 7 6 Sym Ctl (Sof e) chk.gates.length → Bool :=
    fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩ with hAdef
  have hAeq : ∀ v, A v = w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩ := fun v => by rw [hAdef]
  obtain ⟨h1, h2, h3, h4⟩ := acceptsIn_of_tableau_sat U Sym.one Sym.zero Sym.one
    (fixedOf 𝒟.prog n T x y) chk A (fun cl hcl => hAsat cl (Or.inl hcl)) chk_isCheckCircuit
    chk_refsLt chk_inputsLt chk_gates_ne
  set inp := inputOf Sym.zero Sym.one (fixedOf 𝒟.prog n T x y) chk A with hinp
  -- the two free tapes hold strings over `{0, 1}`
  have hbits : ∀ jt : Fin 7, fixedOf 𝒟.prog n T x y jt = none →
      bits (boolsOf (inp jt)) = inp jt := fun jt hjt => bits_boolsOf _ (h2 jt hjt)
  have hbits5 : bits (boolsOf (inp 5)) = inp 5 := hbits 5 (by simp [fixedOf])
  have hbits6 : bits (boolsOf (inp 6)) = inp 6 := hbits 6 (by simp [fixedOf])
  -- the strings are short, by the answer-end clauses
  have hshort : ∀ jt : Fin 7, ((jt : ℕ) = 5 ∨ (jt : ℕ) = 6) → (inp jt).length ≤ T := by
    intro jt hjt
    have hpos : T + 3 < numCells (Sof e) := by unfold numCells; omega
    have hclmem : unit (.cell 0 (.inl jt) ⟨T + 3, hpos⟩ CellVal.blank) true ∈
        tableauPlus e T (fixedOf 𝒟.prog n T x y) chk :=
      Or.inr ⟨jt, ⟨T + 3, hpos⟩, hjt, rfl, rfl⟩
    have hval := (unit_eval A _ true).mp (hAsat _ hclmem)
    rw [h3 jt ⟨T + 3, hpos⟩ CellVal.blank] at hval
    have hbl := (of_decide_eq_true hval).symm
    have hle := length_le_of_inputCellVal_blank (inp jt) (⟨T + 3, hpos⟩ : Pos (Sof e))
      (by rw [isBdry_iff]; simp only [Fin.val_mk]; omega) (by simp) hbl
    simpa using hle
  -- the answer blocks are the tape encodings of the strings
  have hans : ∀ (jt : Fin 7) (k : ℕ) (hk : k < 4 * T), (jt : ℕ) = tapeIdx T k →
      bits (boolsOf (inp jt)) = inp jt →
      w ⟨k, by omega⟩ = tapeBits (boolsOf (inp jt)) (rOf T k) := by
    intro jt k hk hjt hbj
    obtain ⟨jt', p, hjt', hp, hdec⟩ := decodeVar_ans e Gc T hT hk
    have hjj : jt' = jt := Fin.ext (by rw [hjt', hjt])
    have hidx : idxOf e Gc T (.cell 0 (.inl jt') p (valOf T k)) = k :=
      idxOf_ans e Gc T hT hk hjt' hp
    have hAv : A (.cell 0 (.inl jt') p (valOf T k)) = w ⟨k, by omega⟩ := by
      rw [hAeq]
      congr 1
      simp only [Fin.mk.injEq]
      exact hidx
    have hk2 : rOf T k < 2 * Sof e := by have := rOf_lt T k hk; omega
    have hcell : inputCellVal (inp jt) p = inputCellVal (bits (boolsOf (inp jt))) p := by
      rw [hbj]
    rw [← hAv, h3 jt' p (valOf T k), hjj, hcell, valOf]
    exact decide_val_inputCellVal e _ (rOf T k) (by rw [hp]) hk2
  -- the machine's inputs are the strings read off the time-`0` rows
  have huinp : uInput 𝒟.prog n T x y (boolsOf (inp 5)) (boolsOf (inp 6)) = inp := by
    funext j
    fin_cases j
    · exact (h1 0 (S 𝒟.prog.toData) (by simp [fixedOf])).symm
    · exact (h1 1 (S (encode n)) (by simp [fixedOf])).symm
    · exact (h1 2 (List.replicate T Sym.one) (by simp [fixedOf])).symm
    · exact (h1 3 (S (encode x)) (by simp [fixedOf])).symm
    · exact (h1 4 (S (encode y)) (by simp [fixedOf])).symm
    · exact hbits5
    · exact hbits6
  refine ⟨boolsOf (inp 5), boolsOf (inp 6), by simpa using hshort 5 (Or.inl rfl),
    by simpa using hshort 6 (Or.inr rfl), ?_, ?_, ?_⟩
  · intro j
    have hrj : rOf T (j : ℕ) = (j : ℕ) := by unfold rOf; rw [if_pos (by omega)]
    have h5 : ((5 : Fin 7) : ℕ) = tapeIdx T (j : ℕ) := by
      unfold tapeIdx; rw [if_pos (by omega)]; rfl
    rw [← hwa j, hans 5 (j : ℕ) (by omega) h5 hbits5, hrj]
  · intro j
    have hrj : rOf T (2 * T + (j : ℕ)) = (j : ℕ) := by
      unfold rOf
      rw [if_neg (by omega)]
      omega
    have h6 : ((6 : Fin 7) : ℕ) = tapeIdx T (2 * T + (j : ℕ)) := by
      unfold tapeIdx; rw [if_neg (by omega)]; rfl
    rw [← hwb j, hans 6 (2 * T + (j : ℕ)) (by omega) h6 hbits6, hrj]
  · refine acceptsWithin_of_accepts 𝒟 n x y _ _ T (by simpa using hshort 5 (Or.inl rfl))
      (by simpa using hshort 6 (Or.inr rfl)) (Sof e) ?_
    rw [huinp]
    exact h4

/-- **Item 1 of `thm:succinct-sat` for the describer.** -/
theorem extendsAnswers_iff (hT : T ≤ Sof e) (hlen : FixedLen e 𝒟.prog n T x y)
    (hTm : T + 3 < 2 ^ W e)
    (hrb : ∀ ap bp : BitStr, ap.length ≤ T → bp.length ≤ T →
      runBound 𝒟.prog n x y ap bp T ≤ Sof e)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (a b : Fin (2 * T) → Bool) :
    ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)) a b ↔
      EncodesAccepted 𝒟 n x y T a b :=
  ⟨encodesAccepted_of_extendsAnswers 𝒟 n T x y e hT hlen hTm h4T a b,
    extendsAnswers_of_encodesAccepted 𝒟 n T x y e hT hlen hTm hrb h4T a b⟩

end Main

end MIPRE.TM.CookLevin.Desc
