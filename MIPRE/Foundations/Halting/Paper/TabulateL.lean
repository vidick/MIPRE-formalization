/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Instantiation
public import MIPRE.Foundations.ClassMIPStarComputable

@[expose] public section

/-!
# The tabulation of a string's verifier under its own parameter

`Halting.tab G U x n` (`Halting/Instantiation.lean`) tabulates the `n`-th game of the verifier
a string denotes with the decider budget that `n`-boundedness supplies, `n ^ n · (|d| + 1) ^ n`,
and is correct on `n`-bounded strings. The halting reduction along the paper's route
(`planning/polytime-halting.md`) runs its verifier at the *fixed* level `C₀` with a parameter
`λ = poly(|M|)` that is far larger than `C₀`; that verifier is `λ`-bounded and not
`C₀`-bounded, and its size clause alone rules the old budget out. So the decider is
re-budgeted from the string's own parameter: `n ^ λ · (|d| + 1) ^ λ` at index `n` with
`λ = descLam x`, which is exactly what `Verifier.IsBounded λ` supplies at every `n ≥ 2`.

Everything else — the sampler runs under the compressed sampler's own bound, the doubled
question set, the weight list — is `Instantiation.lean`'s, and the correctness proof is its
`tab_match` with the one budget lemma swapped (`accOfL_iff`). The semidecider for
"`val*` at level `C₀` exceeds `1/2`" on this tabulation (`exists_semL`) is what the search
branch of the paper-route decider tests.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)

namespace Halting

/-! ## Acceptance under the `λ`-budget -/

/-- Acceptance from the encoded decider program, under the budget `n ^ λ · (|d| + 1) ^ λ`. -/
def accOfL (pd : Data) (n lam : ℕ) (x y a b : BitStr) : Bool :=
  decide (Machine.runForD pd (encode (n, x, y, a, b))
    (Decider.acceptBudget (n ^ lam) lam x y a b) = some (encode true))

set_option maxHeartbeats 1000000 in
theorem primrec_accOfL {α : Type*} [Primcodable α] {pd : α → Data} {lvl lam : α → ℕ}
    (hpd : Primrec pd) (hlvl : Primrec lvl) (hlam : Primrec lam) :
    Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      accOfL (pd q.1) (lvl q.1) (lam q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have hpd' : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => pd q.1 :=
    hpd.comp Primrec.fst
  have hn : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => lvl q.1 :=
    hlvl.comp Primrec.fst
  have hl : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => lam q.1 :=
    hlam.comp Primrec.fst
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
      Decider.acceptBudget (lvl q.1 ^ lam q.1) (lam q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 :=
    Primrec.nat_mul.comp (primrec_nat_pow.comp hn hl)
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp htup)) hl)
  have hfin : PrimrecPred fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Machine.runForD (pd q.1) (encode (lvl q.1, q.2))
        (Decider.acceptBudget (lvl q.1 ^ lam q.1) (lam q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
        = some (encode true) :=
    Primrec.eq.comp (Machine.primrec_runForD.comp ((hpd'.pair hinput).pair hbudget))
      (Primrec.const (some (encode true) : Option Data))
  exact (Primrec.ite hfin (Primrec.const true) (Primrec.const false)).of_eq fun q => by
    simp only [accOfL]; split <;> simp_all

/-- The doubled tabulation with the decider under the `λ`-budget; the sampler side is
`tabOf`'s. -/
def tabOfL (sd pd : Data) (s T B k n lam : ℕ) : GameData where
  nX := 2 ^ (s + 1) - 1
  nA := (Data.bitStrsLE T).length - 1
  w := Verifier.weightList s
        (fun z => Verifier.bitsToIdx (false :: margOf sd B k n .alice z))
        (fun z => Verifier.bitsToIdx (true :: margOf sd B k n .bob z))
  acc := Verifier.accListW s T (fun u => Verifier.bitsToIdx (false :: u))
          (fun v => Verifier.bitsToIdx (true :: v)) (accOfL pd n lam)

theorem primrec_tabOfL {α : Type*} [Primcodable α] {sd pd : α → Data}
    {s T B lvl lam : α → ℕ}
    (k : ℕ) (hsd : Primrec sd) (hpd : Primrec pd) (hs : Primrec s) (hT : Primrec T)
    (hB : Primrec B) (hlvl : Primrec lvl) (hlam : Primrec lam) :
    Primrec fun a : α => tabOfL (sd a) (pd a) (s a) (T a) (B a) k (lvl a) (lam a) := by
  have hnX : Primrec fun a : α => 2 ^ (s a + 1) - 1 :=
    Primrec.nat_sub.comp
      (primrec_nat_pow.comp (Primrec.const 2) (Primrec.succ.comp hs)) (Primrec.const 1)
  have hnA : Primrec fun a : α => (Data.bitStrsLE (T a)).length - 1 :=
    Primrec.nat_sub.comp (Primrec.list_length.comp (Data.primrec_bitStrsLE.comp hT))
      (Primrec.const 1)
  have hacc := Verifier.primrec_accListW (s := s) (T := T)
    (fA := fun u => Verifier.bitsToIdx (false :: u))
    (fB := fun v => Verifier.bitsToIdx (true :: v))
    (acc? := fun a => accOfL (pd a) (lvl a) (lam a)) hs hT
    (Verifier.primrec_tagIdxOf false) (Verifier.primrec_tagIdxOf true)
    (primrec_accOfL hpd hlvl hlam)
  refine ((Primrec.of_equiv_symm (e := GameData.equivTuple)).comp
    (hnX.pair (hnA.pair ((primrec_weightList k hsd hs hB hlvl).pair hacc)))).of_eq ?_
  intro a
  rfl

variable (G : GapCompression) (U : UniversalMachine)

theorem primrec_tabOfL_tuple (k : ℕ) :
    Primrec fun q : (Data × Data) × (ℕ × ℕ) × ℕ × ℕ × ℕ =>
      tabOfL q.1.1 q.1.2 q.2.1.1 q.2.2.1 q.2.1.2 k q.2.2.2.1 q.2.2.2.2 :=
  primrec_tabOfL k (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

/-- **The tabulation of `(Vof G U x)`'s `n`-th game under the string's own parameter.** -/
noncomputable def tabL (x : BitStr) (n : ℕ) : GameData :=
  tabOfL (sampData G x) (decProgData G U x)
    (dimOf (sampData G x) (ansBound G x n) G.deg n) (ansBound G x n) (ansBound G x n) G.deg n
    (descLam x)

theorem computable_tabArgsL : Computable fun p : BitStr × ℕ =>
    ((sampData G p.1, decProgData G U p.1),
      ((dimOf (sampData G p.1) (ansBound G p.1 p.2) G.deg p.2, ansBound G p.1 p.2),
        (ansBound G p.1 p.2, (p.2, descLam p.1)))) :=
  ((computable_sampData_fst G).pair (computable_decProgData_fst G U)).pair
    (((computable_dimOf_fst G).pair (computable_ansBound G)).pair
      ((computable_ansBound G).pair (Computable.snd.pair (primrec_descLam.to_comp.comp
        Computable.fst))))

theorem tabL_computable : Computable fun p : BitStr × ℕ => tabL G U p.1 p.2 :=
  ((primrec_tabOfL_tuple G.deg).to_comp.comp (computable_tabArgsL G U)).of_eq fun _ => rfl

/-- The tabulated acceptance test **is** the verifier's acceptance, on a string whose verifier
is bounded by the string's own parameter. -/
theorem accOfL_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded (descLam x)) (hn : 2 ≤ n)
    (x' y' a b : BitStr) :
    accOfL (decProgData G U x) n (descLam x) x' y' a b = true ↔
      (Vof G U x).decider.Accepts n x' y' a b := by
  rw [accOfL, decide_eq_true_iff, decProgData_eq,
    ← (Vof G U x).decider.accepts_iff_runForD (hb.1 n hn).2.2 x' y' a b]

/-! ## The tabulation matches the verifier, doubled

Verbatim `Instantiation.lean`'s `tab_nX` … `tab_value`, at `tabL` and with `accOfL_iff` in
place of `accOf_iff`. -/

theorem tabL_nX (x : BitStr) (n : ℕ) :
    (tabL G U x n).nX + 1 = 2 ^ ((Vof G U x).sampler.dim n + 1) := by
  show 2 ^ (dimOf (sampData G x) (ansBound G x n) G.deg n + 1) - 1 + 1 = _
  rw [dimOf_eq G U x n]
  exact Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)

theorem tabL_nA (x : BitStr) (n : ℕ) :
    (tabL G U x n).nA + 1 = (Verifier.answerList (ansBound G x n)).length := by
  show (Data.bitStrsLE (ansBound G x n)).length - 1 + 1 = _
  rw [Verifier.answerList, List.length_map]
  exact Nat.succ_pred_eq_of_pos (Data.length_bitStrsLE_pos _)

/-- The question relabeling. -/
noncomputable def eXofL (x : BitStr) (n : ℕ) :
    Fin ((tabL G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n :=
  (finCongr (tabL_nX G U x n)).trans (Verifier.tagEquiv _).symm

/-- The answer relabeling. -/
noncomputable def eAofL (x : BitStr) (n : ℕ) :
    Fin ((tabL G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n) :=
  (finCongr (tabL_nA G U x n)).trans (Verifier.answerEquiv _)

theorem eXofL_apply (x : BitStr) (n : ℕ) (i : Fin ((tabL G U x n).nX + 1)) :
    Verifier.bitsToIdx ((eXofL G U x n i).1 :: CL.toBits (eXofL G U x n i).2) = (i : ℕ) := by
  rw [eXofL, Equiv.trans_apply, Verifier.bitsToIdx_tagEquiv_symm]
  simp

theorem eAofL_apply (x : BitStr) (n : ℕ) (k : Fin ((tabL G U x n).nA + 1)) :
    (Data.bitStrsLE (ansBound G x n)).idxOf (eAofL G U x n k).1 = (k : ℕ) := by
  rw [← Verifier.answerEquiv_symm_val, eAofL]
  simp

theorem margL_idx_eq (x : BitStr) (n : ℕ) (w : Player)
    (tg : Bool) (z : BitStr) (hz : z.length = (Vof G U x).sampler.dim n)
    (i : Fin ((tabL G U x n).nX + 1)) :
    Verifier.bitsToIdx (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z) = (i : ℕ)
      ↔ (tg = (eXofL G U x n i).1 ∧
          ((Vof G U x).sampler.cl n w).eval (CL.ofBits ((Vof G U x).sampler.dim n) z)
            = (eXofL G U x n i).2) := by
  rw [margOf_eq G U x n w z hz, ← eXofL_apply G U x n i,
    Verifier.bitsToIdx_cons_toBits_eq_iff]

/-- **The `μ` clause, doubled.** -/
theorem mu_clauseL (x : BitStr) (n : ℕ)
    (i j : Fin ((tabL G U x n).nX + 1)) :
    (tabL G U x n).game.μ i j
      = ((Vof G U x).doubledGame n (ansBound G x n)).μ
          (eXofL G U x n i) (eXofL G U x n j) := by
  classical
  have hdim : dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n :=
    dimOf_eq G U x n
  have hlen : ∀ (w : Player) (z : BitStr), z.length = (Vof G U x).sampler.dim n →
      (margOf (sampData G x) (ansBound G x n) G.deg n w z).length
        = (Vof G U x).sampler.dim n := by
    intro w z hz
    rw [margOf_eq G U x n w z hz, CL.length_toBits]
  have hmem : ∀ z ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n),
      z.length = (Vof G U x).sampler.dim n := by
    intro z hz
    rw [← hdim]; exact (Data.mem_bitStrsOfLen _ _).1 hz
  have hrange : ∀ (tg : Bool) (w : Player),
      ∀ z ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n),
        Verifier.bitsToIdx (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z)
          < (tabL G U x n).nX + 1 := by
    intro tg w z hz
    have hlt := Verifier.bitsToIdx_lt (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z)
    rw [List.length_cons, hlen w z (hmem z hz)] at hlt
    rw [tabL_nX G U x n]
    exact hlt
  have htot : (tabL G U x n).totalWeight = 2 ^ dimOf (sampData G x) (ansBound G x n) G.deg n :=
    Verifier.totalWeight_weightList _ _ _ _ _ _ (hrange false .alice) (hrange true .bob)
  have hqw : ∀ a b : ℕ, (tabL G U x n).questionWeight a b
      = ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter fun z =>
          decide (Verifier.bitsToIdx
              (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = a
            ∧ Verifier.bitsToIdx
              (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = b)).length :=
    fun a b => Verifier.questionWeight_weightList _ _ _ _ _ _ a b
  rw [GameData.game_μ, htot, if_neg (Nat.two_pow_pos _).ne', hqw,
    show ((Vof G U x).doubledGame n (ansBound G x n)).μ
        (eXofL G U x n i) (eXofL G U x n j)
      = if (eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true then
          (Vof G U x).sampler.dist n (eXofL G U x n i).2 (eXofL G U x n j).2 else 0 from rfl]
  by_cases htag : (eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true
  · rw [if_pos htag]
    have hnum : ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter
          fun z => decide (Verifier.bitsToIdx
              (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
            ∧ Verifier.bitsToIdx
              (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ))).length
        = (Finset.univ.filter fun v : (Vof G U x).Questions n =>
            ((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
              ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2).card := by
      rw [hdim]
      rw [show ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
          decide (Verifier.bitsToIdx
              (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
            ∧ Verifier.bitsToIdx
              (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ)))
          = ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
            (fun v : (Vof G U x).Questions n =>
              decide (((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
                ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2))
              (CL.ofBits ((Vof G U x).sampler.dim n) z)) from ?_]
      · rw [Verifier.length_filter_bitStrsOfLen (s := (Vof G U x).sampler.dim n)
          (fun v => decide (((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
            ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2))]
        congr 1
      · refine List.filter_congr fun z hz => ?_
        have hz' : z.length = (Vof G U x).sampler.dim n :=
          (Data.mem_bitStrsOfLen _ _).1 hz
        simp only [decide_eq_decide]
        rw [margL_idx_eq G U x n .alice false z hz' i,
          margL_idx_eq G U x n .bob true z hz' j, htag.1, htag.2]
        simp
    rw [hnum,
      show (Vof G U x).sampler.dist n (eXofL G U x n i).2 (eXofL G U x n j).2
        = ((Finset.univ.filter fun v : (Vof G U x).Questions n =>
            ((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
              ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2).card : ℝ)
          / (Fintype.card ((Vof G U x).Questions n) : ℝ) from rfl]
    congr 1
    rw [hdim]
    simp [Verifier.Questions]
  · rw [if_neg htag]
    have hnil : ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter
        fun z => decide (Verifier.bitsToIdx
            (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
          ∧ Verifier.bitsToIdx
            (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ))) = [] := by
      refine List.filter_eq_nil_iff.2 fun z hz => ?_
      simp only [decide_eq_true_eq, not_and]
      intro h1 h2
      exact htag ⟨((margL_idx_eq G U x n .alice false z (hmem z hz) i).1 h1).1.symm,
        ((margL_idx_eq G U x n .bob true z (hmem z hz) j).1 h2).1.symm⟩
    rw [hnil]
    simp

/-- **The acceptance table read back, doubled.** -/
theorem accL_mem_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded (descLam x)) (hn : 2 ≤ n)
    (i j : Fin ((tabL G U x n).nX + 1)) (k l : Fin ((tabL G U x n).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (tabL G U x n).acc
      ↔ ((eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true ∧
          (Vof G U x).decider.Accepts n (CL.toBits (eXofL G U x n i).2)
            (CL.toBits (eXofL G U x n j).2) (eAofL G U x n k).1 (eAofL G U x n l).1) := by
  have hdim : dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n :=
    dimOf_eq G U x n
  have hqmem : ∀ (m : Fin ((tabL G U x n).nX + 1)),
      CL.toBits (eXofL G U x n m).2
        ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n) := by
    intro m
    rw [Data.mem_bitStrsOfLen, CL.length_toBits, hdim]
  have hamem : ∀ (m : Fin ((tabL G U x n).nA + 1)),
      (eAofL G U x n m).1 ∈ Data.bitStrsLE (ansBound G x n) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (eAofL G U x n m).2
  rw [show (tabL G U x n).acc = Verifier.accListW (dimOf (sampData G x) (ansBound G x n) G.deg n)
      (ansBound G x n)
      (fun u => Verifier.bitsToIdx (false :: u)) (fun v => Verifier.bitsToIdx (true :: v))
      (accOfL (decProgData G U x) n (descLam x)) from rfl, Verifier.mem_accListW_iff]
  constructor
  · rintro ⟨u, hu, v, hv, a, ha, b, hb', hacc, hi, hj, hk, hl⟩
    have hu' : (eXofL G U x n i).1 = false ∧ CL.toBits (eXofL G U x n i).2 = u :=
      List.cons_eq_cons.mp (Verifier.bitsToIdx_injOn
        (s := (Vof G U x).sampler.dim n + 1) (by simp)
        (by rw [List.length_cons, (Data.mem_bitStrsOfLen _ _).1 hu, hdim])
        (by rw [eXofL_apply G U x n i, hi]))
    have hv' : (eXofL G U x n j).1 = true ∧ CL.toBits (eXofL G U x n j).2 = v :=
      List.cons_eq_cons.mp (Verifier.bitsToIdx_injOn
        (s := (Vof G U x).sampler.dim n + 1) (by simp)
        (by rw [List.length_cons, (Data.mem_bitStrsOfLen _ _).1 hv, hdim])
        (by rw [eXofL_apply G U x n j, hj]))
    have ha' : a = (eAofL G U x n k).1 := (List.idxOf_inj ha).1 (by rw [← hk, eAofL_apply])
    have hb'' : b = (eAofL G U x n l).1 := (List.idxOf_inj hb').1 (by rw [← hl, eAofL_apply])
    refine ⟨hu'.1, hv'.1, ?_⟩
    rw [hu'.2, hv'.2, ← ha', ← hb'']
    exact (accOfL_iff G U x n hb hn _ _ _ _).1 hacc
  · rintro ⟨ht1, ht2, h⟩
    refine ⟨_, hqmem i, _, hqmem j, _, hamem k, _, hamem l,
      (accOfL_iff G U x n hb hn _ _ _ _).2 h, ?_, ?_,
      (eAofL_apply G U x n k).symm, (eAofL_apply G U x n l).symm⟩
    · rw [← ht1, eXofL_apply G U x n i]
    · rw [← ht2, eXofL_apply G U x n j]

/-- **The match, doubled.** -/
theorem tabL_match (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded (descLam x)) (hn : 2 ≤ n) :
    ∃ (eX : Fin ((tabL G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n)
      (eA : Fin ((tabL G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n)),
      (∀ i j, (tabL G U x n).game.μ i j
        = ((Vof G U x).doubledGame n (ansBound G x n)).μ (eX i) (eX j)) ∧
      (∀ i j k l, (tabL G U x n).game.D i j k l
        = ((Vof G U x).doubledGame n (ansBound G x n)).D (eX i) (eX j) (eA k) (eA l)) := by
  classical
  refine ⟨eXofL G U x n, eAofL G U x n, mu_clauseL G U x n, fun i j k l => ?_⟩
  refine Bool.eq_iff_iff.2 ?_
  rw [GameData.game_D,
    show ((Vof G U x).doubledGame n (ansBound G x n)).D
        (eXofL G U x n i) (eXofL G U x n j) (eAofL G U x n k) (eAofL G U x n l)
      = if (eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true then
          ((Vof G U x).game n (ansBound G x n)).D (eXofL G U x n i).2
            (eXofL G U x n j).2 (eAofL G U x n k) (eAofL G U x n l) else false from rfl]
  by_cases hc : i = j ∧ k ≠ l
  · rw [if_pos hc, if_neg (by rw [hc.1]; exact fun h => by simp_all)]
  · rw [if_neg hc, decide_eq_true_iff, accL_mem_iff G U x n hb hn]
    by_cases ht : (eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true
    · rw [if_pos ht]
      show _ ↔ (decide ((Vof G U x).decider.Accepts n _ _ _ _) = true)
      rw [decide_eq_true_iff]
      exact ⟨fun h => h.2.2, fun h => ⟨ht.1, ht.2, h⟩⟩
    · rw [if_neg ht]
      simp only [Bool.false_eq_true, iff_false]
      exact fun h => ht ⟨h.1, h.2.1⟩

/-- **The value of the tabulation** is the verifier's, on a string whose verifier is bounded by
the string's own parameter, at every index `n ≥ 2`. -/
theorem tabL_value (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded (descLam x)) (hn : 2 ≤ n) :
    quantumValue (tabL G U x n).game = (Vof G U x).valStar n (ansBound G x n) := by
  obtain ⟨eX, eA, hμ, hD⟩ := tabL_match G U x n hb hn
  exact Verifier.quantumValue_toGame_eq_valStar_doubled _ _ _ _ eX eA hμ hD

/-! ## The semidecider of the search branch -/

/-- **The search branch's semidecider**: a closed program halting on `encode x` exactly when the
tabulation of `x`'s verifier at the level `n₀` has quantum value above `1/2`. On the strings this
tabulation is correct for (`tabL_value`), that is `val*(𝒱_{n₀}) > 1/2`. -/
theorem exists_semL (n₀ : ℕ) : ∃ S : Prog, S.WellScoped 1 ∧
    ∀ x : BitStr, Halts S (encode x) ↔ (1 : ℝ) / 2 < quantumValue (tabL G U x n₀).game := by
  obtain ⟨S, hS, hSx⟩ := exists_semidecider_lt_quantumValue
    (g := fun x => tabL G U x n₀)
    (((tabL_computable G U).comp (Computable.id.pair (Computable.const n₀))).of_eq
      fun _ => rfl) 1 2
  refine ⟨S, hS, fun x => (hSx x).trans ?_⟩
  simp only [Nat.cast_one, Nat.cast_ofNat]

/-- The verifier the string `descOf lam e` denotes. -/
theorem Vof_descOf (lam : ℕ) (e : Prog) :
    Vof G U (descOf lam e) = Verifier.ofSamplerDecider U (G.sampler lam) e := by
  unfold Vof
  rw [descLam_descOf, descDecD_descOf]
  rfl

end Halting

end MIPRE

end
