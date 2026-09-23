/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Honest
import MIPRE.Background.AnswerReduction.TypedGame
import MIPRE.Foundations.SyncPushQ
import MIPRE.Foundations.OracularComplete

/-!
# Completeness of the typed answer-reduced game

Piece AR-4 of `planning/answer-reduction.md`: a value-`1` PCC strategy of the input verifier gives
one of the (doubled) typed answer-reduced game (`exists_typedGame_perfectPCC`), for any PCP proofs
of the accepted answer pairs — the paper's completeness argument for `thm:ar`
(`ld_compiler.tex`), with the PCP's completeness left as a hypothesis (`ProofGood`), discharged in
`MIPRE/Background/AnswerReduction/Complete`.

The strategy is the oracularized game's honest strategy (`SeededGame.oracleStrategy`, the
oracularization's completeness), read through the question map that keeps a question's role and
its oracle half (`SyncStrategy.pushQ`), and answered honestly (`honestAns`) from data computed from
the role, the oracle half and the outcome (`hdata`):

* an oracle answering the pair `(a, b)` at seed `x` holds the PCP proof `pfOf x a b` (`ofProof`);
* an isolated player answering `a` holds the low-degree encoding of `a` at its own copy
  (`ofAnswer`), and zero elsewhere.

Two questions of positive weight are read off one seed; their oracle halves are then an
oracularized question pair of positive weight, and their PCP halves questions of one PCP vector.
There the oracularized predicate's checks are exactly the consistency `accepts_honestAns` needs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL MIPRE.LIDT MIPRE.LowDegree SAT Pcp Cost

/-! ## The oracularized question distribution -/

theorem SeededGame.oDist_oquestion_pos {W A : Type*} [Fintype W] [DecidableEq W]
    (G : SeededGame W A) (r₁ r₂ : Role) (z : W) :
    0 < G.oDist (G.oquestion r₁ z) (G.oquestion r₂ z) := by
  rw [SeededGame.oDist]
  have hc : (0 : ℝ) < Fintype.card (Role × Role × W) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨(r₁, r₂, z)⟩)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun s : Role × Role × W =>
    (Fintype.card (Role × Role × W) : ℝ)⁻¹ *
      if (G.oquestion s.1 s.2.2, G.oquestion s.2.1 s.2.2) =
        (G.oquestion r₁ z, G.oquestion r₂ z) then 1 else 0)
    (fun s _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num)) (mem_univ (r₁, r₂, z)))
  rw [if_pos rfl, mul_one]
  positivity

theorem SampledGame.exists_of_dist_pos {Sd X Y : Type*} [Fintype Sd] [Fintype X] [Fintype Y]
    {qA : Sd → X} {qB : Sd → Y} {x : X} {y : Y} (h : 0 < SampledGame.dist qA qB x y) :
    ∃ s, qA s = x ∧ qB s = y := by
  by_contra hc
  push Not at hc
  refine absurd (Finset.sum_eq_zero fun s _ => ?_) (ne_of_gt (pos_of_mul_pos_right h
    (inv_nonneg.mpr (Nat.cast_nonneg _))))
  have hne : (qA s, qB s) ≠ (x, y) := fun he => hc s (Prod.ext_iff.mp he).1 (Prod.ext_iff.mp he).2
  simp [hne]

/-! ## The players' data -/

variable {P : PcpParams} (hk : 1 ≤ P.k)

/-- The embedding of the `i`-th block of `m` coordinates into the `m'` of the sixth copy. -/
def blockEmb (i : Fin 5) : Fin P.m → Fin P.m' := fun j => ⟨i * P.m + j, by
  have h1 : (i : ℕ) * P.m ≤ 4 * P.m := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp i.isLt)
  have h2 : (j : ℕ) < P.m := j.isLt
  simp only [PcpParams.m']
  omega⟩

theorem blockEmb_injective (i : Fin 5) : Function.Injective (blockEmb (P := P) i) := by
  intro j j' h
  simp only [blockEmb, Fin.mk.injEq, Nat.add_left_cancel_iff] at h
  exact Fin.ext h

/-- **An oracle's data**, from a PCP proof: the answer polynomials, and for the sixth copy the
answer polynomials read on their blocks followed by the constraint polynomials. -/
def ofProof (pf : PcpProof P (Fq P hk)) : HPolys P (Fq P hk) where
  g := pf.g
  c j := if h : (j : ℕ) < 5 then MvPolynomial.rename (blockEmb ⟨j, h⟩) (pf.g ⟨j, h⟩)
    else pf.c ⟨j - 5, by have := j.isLt; omega⟩

/-- **An isolated player's data**: the low-degree encoding of its answer at its own copy `v`. -/
def ofAnswer (v : Fin 5) (a : BitStr) : HPolys P (Fq P hk) where
  g j := if j = v then ldEnc (answerVec (Fq P hk) P.m a) else 0
  c _ := 0

/-- A PCP proof is good for the pair `(a, b)` at seed `x`: its first two answer polynomials encode
`a` and `b`, and every point's evaluations pass the check. -/
def ProofGood {X : Type*} (check : X → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) → Bool)
    (x : X) (a b : BitStr) (pf : PcpProof P (Fq P hk)) : Prop :=
  pf.g 0 = ldEnc (answerVec (Fq P hk) P.m a) ∧ pf.g 1 = ldEnc (answerVec (Fq P hk) P.m b) ∧
    ∀ z, check x z (fun j => MvPolynomial.eval z ((ofProof hk pf).c j)) = true

theorem degreeOf_rename_le {m m' d : ℕ} {f : Fin m → Fin m'} (hf : Function.Injective f)
    {p : MvPolynomial (Fin m) (Fq P hk)} (hp : ∀ i, p.degreeOf i ≤ d) (i' : Fin m') :
    (MvPolynomial.rename f p).degreeOf i' ≤ d := by
  classical
  by_cases h : ∃ i, f i = i'
  · obtain ⟨i, rfl⟩ := h
    rw [MvPolynomial.degreeOf_rename_of_injective hf]
    exact hp i
  · push Not at h
    rw [MvPolynomial.degreeOf_le_iff]
    intro s hs
    rw [MvPolynomial.support_rename_of_injective hf] at hs
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simpa using h)]
    exact Nat.zero_le _

theorem lowDeg_ofProof (pf : PcpProof P (Fq P hk)) : (ofProof hk pf).LowDeg := by
  refine ⟨fun j i => pf.degreeOf_g j i, fun j i => ?_⟩
  simp only [ofProof]
  split_ifs
  · exact degreeOf_rename_le hk (blockEmb_injective _) (pf.degreeOf_g _) i
  · exact pf.degreeOf_c _ i

theorem lowDeg_ofAnswer (v : Fin 5) (a : BitStr) : (ofAnswer hk (P := P) v a).LowDeg := by
  refine ⟨fun j i => ?_, fun _ i => by simp [ofAnswer]⟩
  simp only [ofAnswer]
  split_ifs
  · exact (degreeOf_ldEnc_le _ i).trans (by decide)
  · simp

theorem oracle_ofProof {X : Type*}
    {check : X → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) → Bool} {x : X}
    {a b : BitStr} {pf : PcpProof P (Fq P hk)} (h : ProofGood hk check x a b pf) :
    (ofProof hk pf).Oracle (check x) := by
  refine ⟨fun j z => ?_, h.2.2⟩
  simp only [ofProof, HPolys.idx6, j.isLt, dite_true, MvPolynomial.eval_rename]
  rfl

/-! ## The answer length -/

theorem cnt_le (t : PcpTy) : cnt P t ≤ (P.m' + 6) * (P.m' * 7 + 1) := by
  have hm := P.five_mul_m_le
  have h5 : 5 ≤ P.m' := by simp only [PcpParams.m']; omega
  obtain ⟨i, τ⟩ := t
  unfold cnt
  split_ifs <;> cases τ <;> simp only [dPcp, PcpParams.d] <;> nlinarith

/-- **Honest answers fit the answer cut** `32 (k + 1)(m' + 7)^2`. -/
theorem length_enc_honestAns_le [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)}
    {hm' : P.m' ∣ Fintype.card (Fq P hk)} (S : LIDT.CL.Sel (Fq P hk) P.m hm)
    (S' : LIDT.CL.Sel (Fq P hk) P.m' hm') (H : HPolys P (Fq P hk)) (t : PcpTy)
    (y : Coord P → Fq P hk) :
    (enc (fld P hk) (honestAns S S' H t y)).length ≤
      32 * ((P.k + 1) * (P.m' + 7) * (P.m' + 7)) := by
  have h1 := length_enc_le (fld P hk) (honestAns S S' H t y)
  rw [length_elems (fld P hk) (ansFmt_honestAns S S' H t y)] at h1
  have h2 := cnt_le (P := P) t
  have h3 : (P.k + 1) * cnt P t ≤ (P.k + 1) * ((P.m' + 6) * (P.m' * 7 + 1)) :=
    Nat.mul_le_mul_left _ h2
  nlinarith

/-! ## The players' data, from the oracularized strategy's outcomes -/

section Game

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))

/-- **A player's data**, from its role, the oracle half of its question and the oracularized
strategy's outcome. -/
def hdata : Role → (Fin (V.sampler.dim n) → 𝔽₂) → OAns (Verifier.Answers B) → HPolys P (Fq P hk)
  | .oracle, x, .pair a b => ofProof hk (pfOf x a.1 b.1)
  | .alice, _, .single a => ofAnswer hk 0 a.1
  | .bob, _, .single b => ofAnswer hk 1 b.1
  | _, _, _ => ⟨0, 0⟩

theorem lowDeg_hdata (r : Role) (x : Fin (V.sampler.dim n) → 𝔽₂) (u : OAns (Verifier.Answers B)) :
    (hdata V n P hk pfOf r x u).LowDeg := by
  have h0 : (⟨0, 0⟩ : HPolys P (Fq P hk)).LowDeg :=
    ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  cases r <;> cases u
  · exact lowDeg_ofProof hk _
  · exact h0
  · exact h0
  · exact lowDeg_ofAnswer hk _ _
  · exact h0
  · exact lowDeg_ofAnswer hk _ _

variable {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
  (Fin (P.m' + 6) → Fq P hk) → Bool}

/-- **The oracularized predicate's checks are the consistency of the data**, on a question pair
read off one seed, when every accepted pair's proof is good. -/
theorem consistent_of_oaccepts
    (hpf : ∀ x (a b : Verifier.Answers B), (V.seeded n B).D ((V.sampler.cl n .alice).eval x)
      ((V.sampler.cl n .bob).eval x) a b = true → ProofGood hk check x a.1 b.1 (pfOf x a.1 b.1))
    (r₁ r₂ : Role) (x₀ : Fin (V.sampler.dim n) → 𝔽₂) {u v : OAns (Verifier.Answers B)}
    (h : (V.seeded n B).oaccepts ((V.seeded n B).oquestion r₁ x₀) ((V.seeded n B).oquestion r₂ x₀)
      u v = true) :
    Consistent r₁ r₂ (hdata V n P hk pfOf r₁ ((V.seeded n B).oquestion r₁ x₀).2 u)
      (hdata V n P hk pfOf r₂ ((V.seeded n B).oquestion r₂ x₀).2 v) := by
  simp only [SeededGame.oaccepts, Bool.and_eq_true, SeededGame.oquestion_fst] at h
  obtain ⟨⟨⟨⟨⟨⟨hsu, hsv⟩, hgu⟩, hgv⟩, heq⟩, hov⟩, -⟩ := h
  refine ⟨fun hr => ?_, fun w hr hw => ?_⟩
  · subst hr
    simp only [if_true, decide_eq_true_eq] at heq
    rw [heq]
  · subst hr
    have key : ∀ (c : Verifier.Answers B) (v' : Fin 5) (a b : Verifier.Answers B),
        (c = if v' = 0 then a else b) → (v' = 0 ∨ v' = 1) → u = .pair a b →
        (ofAnswer hk v' c.1).g v' = (hdata V n P hk pfOf .oracle x₀ u).g v' := by
      rintro c v' a b hc hv' rfl
      simp only [SeededGame.gameCheck, SeededGame.oquestion] at hgu
      have hg := hpf x₀ a b hgu
      simp only [ofAnswer, if_true, hdata, ofProof]
      rcases hv' with rfl | rfl
      · rw [hg.1, hc, if_pos rfl]
      · rw [hg.2.1, hc, if_neg (by decide)]
    cases r₂ with
    | oracle => simp [roleIdx] at hw
    | alice =>
      simp only [roleIdx, Option.some.injEq] at hw
      subst hw
      rcases u with ⟨a, b⟩ | a <;> rcases v with ⟨c, d⟩ | c <;>
        simp only [SeededGame.shapeOk, Bool.false_eq_true] at hsu hsv
      simp only [SeededGame.oquestion, SeededGame.oracleVsPlayer, decide_eq_true_eq] at hov
      exact key c 0 a b (by rw [if_pos rfl, hov]) (.inl rfl) rfl
    | bob =>
      simp only [roleIdx, Option.some.injEq] at hw
      subst hw
      rcases u with ⟨a, b⟩ | a <;> rcases v with ⟨c, d⟩ | c <;>
        simp only [SeededGame.shapeOk, Bool.false_eq_true] at hsu hsv
      simp only [SeededGame.oquestion, SeededGame.oracleVsPlayer, decide_eq_true_eq] at hov
      exact key c 1 a b (by rw [if_neg (by decide), hov]) (.inr rfl) rfl

/-- An oracle's data passes its PCP check, at a question pair the oracularized predicate
accepts. -/
theorem oracle_hdata
    (hpf : ∀ x (a b : Verifier.Answers B), (V.seeded n B).D ((V.sampler.cl n .alice).eval x)
      ((V.sampler.cl n .bob).eval x) a b = true → ProofGood hk check x a.1 b.1 (pfOf x a.1 b.1))
    (r₂ : Role) (x₀ : Fin (V.sampler.dim n) → 𝔽₂) {u v : OAns (Verifier.Answers B)}
    (h : (V.seeded n B).oaccepts ((V.seeded n B).oquestion .oracle x₀)
      ((V.seeded n B).oquestion r₂ x₀) u v = true) :
    (hdata V n P hk pfOf .oracle x₀ u).Oracle (check x₀) := by
  simp only [SeededGame.oaccepts, Bool.and_eq_true, SeededGame.oquestion_fst] at h
  obtain ⟨⟨⟨⟨⟨⟨hsu, -⟩, hgu⟩, -⟩, -⟩, -⟩, -⟩ := h
  rcases u with ⟨a, b⟩ | a
  · simp only [SeededGame.gameCheck, SeededGame.oquestion] at hgu
    exact oracle_ofProof hk (hpf x₀ a b hgu)
  · simp [SeededGame.shapeOk] at hsu

theorem SeededGame.oaccepts_comm {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A]
    [DecidableEq A] (G : SeededGame W A) (p q : Role × W) (u v : OAns A) :
    G.oaccepts p q u v = G.oaccepts q p v u := by
  unfold SeededGame.oaccepts
  rw [show (if p.1 = q.1 then decide (u = v) else true) =
      (if q.1 = p.1 then decide (v = u) else true) by
    by_cases h : p.1 = q.1
    · rw [if_pos h, if_pos h.symm]
      exact decide_eq_decide.mpr eq_comm
    · rw [if_neg h, if_neg (Ne.symm h)]]
  cases SeededGame.shapeOk p.1 u <;> cases SeededGame.shapeOk q.1 v <;>
    cases G.gameCheck p u <;> cases G.gameCheck q v <;>
    cases SeededGame.oracleVsPlayer p q u v <;> cases SeededGame.oracleVsPlayer q p v u <;>
    simp

end Game

section Strategy

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k) {B : ℕ}
  (pfOf : (Fin (V.sampler.dim n) → 𝔽₂) → BitStr → BitStr → PcpProof P (Fq P hk))
  [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')

/-- **The honest answer** to a typed question, from the oracularized strategy's outcome. -/
def honestQ (p : Detyping.Question ArTy (Fin (dim V n P))) (u : OAns (Verifier.Answers B)) :
    Ans P (Fq P hk) :=
  honestAns S S' (hdata V n P hk pfOf p.1.1 (oraclePart V n P p.2) u) p.1.2 (pcpPart V n P hk p.2)

/-- Two typed questions of positive weight are read off one seed. -/
theorem exists_of_typedGame_mu_pos
    {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
      (Fin (P.m' + 6) → Fq P hk) → Bool} {Bout : ℕ}
    {p q : Detyping.Question ArTy (Fin (dim V n P))}
    (h : 0 < (typedGame V n P hk S S' check Bout).μ p q) :
    ∃ t₁ t₂ z, p = (t₁, (cl V n P hk S S' t₁).eval z) ∧ q = (t₂, (cl V n P hk S S' t₂).eval z) := by
  change 0 < SampledGame.dist
    (CL.Detyping.typedQuestion (E := graph) (fun _ => cl V n P hk S S') false)
    (CL.Detyping.typedQuestion (E := graph) (fun _ => cl V n P hk S S') true) p q at h
  obtain ⟨s, hp, hq⟩ := SampledGame.exists_of_dist_pos h
  exact ⟨s.1.val.1, s.1.val.2, s.2, hp.symm, hq.symm⟩

variable {V n P hk S S'} in
theorem oraclePart_cl (t : ArTy) (z : Fin (dim V n P) → 𝔽₂) :
    oraclePart V n P ((cl V n P hk S S' t).eval z) =
      ((V.seeded n B).oquestion t.1 (oraclePart V n P z)).2 := by
  rw [oraclePart_eval, ← SeededGame.roleFamily_question (V.sampler.cl n) (V.game n B).D t.1]

/-- **Completeness of the typed answer-reduced game**: a value-`1` PCC strategy of `𝒱_n`, and
good PCP proofs of the pairs it accepts, give a value-`1` PCC strategy of the doubled typed game
at any answer cut above `32 (k + 1)(m' + 7)^2`. -/
theorem exists_typedGame_perfectPCC
    {check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) →
      (Fin (P.m' + 6) → Fq P hk) → Bool} (Bout : ℕ)
    (hBout : 32 * ((P.k + 1) * (P.m' + 7) * (P.m' + 7)) ≤ Bout) (hV : V.HasPerfectPCC n B)
    (hpf : ∀ x (a b : Verifier.Answers B), (V.seeded n B).D ((V.sampler.cl n .alice).eval x)
      ((V.sampler.cl n .bob).eval x) a b = true → ProofGood hk check x a.1 b.1 (pfOf x a.1 b.1)) :
    ∃ R : SyncStrategy (typedGame V n P hk S S' check Bout).doubled, R.IsPCC ∧ R.value = 1 := by
  obtain ⟨T, hT, hval⟩ := hV
  let g : Bool × Detyping.Question ArTy (Fin (dim V n P)) → Role × V.Questions n :=
    fun p => (p.2.1.1, oraclePart V n P p.2.2)
  let f : Bool × Detyping.Question ArTy (Fin (dim V n P)) → OAns (Verifier.Answers B) →
      Verifier.Answers Bout := fun p u =>
    ⟨enc (fld P hk) (honestQ V n P hk pfOf S S' p.2 u),
      (length_enc_honestAns_le hk S S' _ _ _).trans hBout⟩
  have hsupp : ∀ p q : Bool × Detyping.Question ArTy (Fin (dim V n P)),
      0 < (typedGame V n P hk S S' check Bout).doubled.μ p q →
      p.1 = false ∧ q.1 = true ∧ ∃ t₁ t₂ z, p.2 = (t₁, (cl V n P hk S S' t₁).eval z) ∧
        q.2 = (t₂, (cl V n P hk S S' t₂).eval z) := by
    intro p q h
    rw [Game.doubled_μ] at h
    split_ifs at h with hb
    · exact ⟨hb.1, hb.2, exists_of_typedGame_mu_pos V n P hk S S' h⟩
    · exact absurd h (lt_irrefl 0)
  have hg : ∀ (b : Bool) (t : ArTy) (z : Fin (dim V n P) → 𝔽₂),
      g (b, (t, (cl V n P hk S S' t).eval z)) =
        (V.seeded n B).oquestion t.1 (oraclePart V n P z) := by
    intro b t z
    exact Prod.ext (SeededGame.oquestion_fst _ _ _).symm (oraclePart_cl t z)
  refine ⟨((V.seeded n B).oracleStrategy T hT).pushQ _ g f,
    SyncStrategy.isPCC_pushQ ((V.seeded n B).isPCC_oracleStrategy T hT) _ g f ?_,
    SyncStrategy.value_pushQ_eq_one _ _ g f ?_ ?_⟩
  · rintro ⟨b₁, p⟩ ⟨b₂, q⟩ hpq
    obtain ⟨-, -, t₁, t₂, z, rfl, rfl⟩ := hsupp _ _ hpq
    rw [hg, hg]
    exact SeededGame.oDist_oquestion_pos _ _ _ _
  · intro x y hxy a b hD
    exact (V.seeded n B).oracleOp_mul_eq_zero T hT hval hxy hD
  · rintro ⟨b₁, p⟩ ⟨b₂, q⟩ hpq
    obtain ⟨hb₁, hb₂, t₁, t₂, z, hp, hq⟩ := hsupp _ _ hpq
    simp only at hb₁ hb₂ hp hq
    subst hb₁ hb₂ hp hq
    rw [hg, hg]
    refine ⟨SeededGame.oDist_oquestion_pos _ _ _ _, fun u v _ _ hD => ?_⟩
    simp only [Game.doubled_D, true_and, if_true]
    change typedPred V n P hk S S' check Bout _ _ (f _ u) (f _ v) = true
    have hD' : (V.seeded n B).oaccepts ((V.seeded n B).oquestion t₁.1 (oraclePart V n P z))
        ((V.seeded n B).oquestion t₂.1 (oraclePart V n P z)) u v = true := hD
    have hD'' := hD'
    rw [SeededGame.oaccepts_comm] at hD''
    refine typedPred_enc V n P hk S S' check ?_ _ _
    simp only [decodeQ, honestQ, pcpPart_eval]
    rw [oraclePart_cl (B := B) t₁ z, oraclePart_cl (B := B) t₂ z]
    obtain ⟨r₁, i₁⟩ := t₁
    obtain ⟨r₂, i₂⟩ := t₂
    refine accepts_honestAns S S' check (r₁, i₁) (r₂, i₂) _ _ _ _ _
      (lowDeg_hdata V n P hk pfOf _ _ _) (lowDeg_hdata V n P hk pfOf _ _ _) ?_ ?_
      (consistent_of_oaccepts V n P hk pfOf hpf r₁ r₂ _ hD')
      (consistent_of_oaccepts V n P hk pfOf hpf r₂ r₁ _ hD'')
    · rintro (rfl : r₁ = .oracle)
      exact oracle_hdata V n P hk pfOf hpf r₂ _ hD'
    · rintro (rfl : r₂ = .oracle)
      exact oracle_hdata V n P hk pfOf hpf r₁ _ hD''

end Strategy

end MIPRE.AnswerReduction

end
