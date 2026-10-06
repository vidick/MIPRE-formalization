/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.HonestBits
public import MIPRE.Foundations.OracularComplete
public import MIPRE.Foundations.SyncMergeByQuestion
public import MIPRE.Tailored.Intro.PresentationTyped

@[expose] public section

/-!
# ZPC completeness of the answer-reduced game

Slice P4d of `planning/aldous-lyons-track.md`: a perfect Z-aligned permutation strategy of the
input's `n`-th game gives one of the answer-reduced game presented by the typed data `tdata`
(`hasPerfectZPC_ar`), on the typed game of any family of CL functions whose questions carry the
oracularized input question and a question of the seeded low-degree test (`ArSampler`).

The strategy (II:10285, the completeness of thm:combi_ans_red):

1. the input's permutation strategy as a synchronous PCC strategy (`lem:zpc-pcc`), read on the
   seeded game `inSeeded` of the input;
2. its oracularization (`MIPRE.SeededGame.oracleStrategy`): the oracle measures both of its seed's
   questions jointly, an isolated player its own;
3. pulled back to the typed questions along their roles and oracularized parts (`pullStrat`), and
   pushed forward along the honest answers `honestAns` (`arStrat`).

It is PCC because the oracularization is, and perfect because the oracularized predicate accepts
every outcome it produces and `arPred_honest` turns that into acceptance by the typed data. Its bit
observables are signed permutations, diagonal at the readable bits, by `HonestBits`.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.Tailored.Intro Classical

/-! ## Support lemmas -/

theorem exists_of_dist_pos {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y] {qA : S → X}
    {qB : S → Y} {x : X} {y : Y} (h : 0 < SampledGame.dist qA qB x y) :
    ∃ s, qA s = x ∧ qB s = y := by
  rw [SampledGame.dist_eq_card] at h
  have hc : 0 < (Finset.univ.filter fun s => qA s = x ∧ qB s = y).card := by
    by_contra h0
    rw [Nat.le_zero.1 (not_lt.1 h0)] at h
    simp at h
  obtain ⟨s, hs⟩ := Finset.card_pos.1 hc
  exact ⟨s, (Finset.mem_filter.1 hs).2⟩

theorem oDist_oquestion_pos {Vs A : Type*} [Fintype Vs] [DecidableEq Vs] [Nonempty Vs]
    (Sd : SeededGame Vs A) (r₁ r₂ : Role) (z : Vs) :
    0 < Sd.oDist (Sd.oquestion r₁ z) (Sd.oquestion r₂ z) := by
  unfold SeededGame.oDist
  refine Finset.sum_pos' (fun _ _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num))
    ⟨(r₁, r₂, z), Finset.mem_univ _, ?_⟩
  rw [ite_eq_left rfl, mul_one]
  exact inv_pos.2 (by exact_mod_cast Fintype.card_pos)

/-! ## The bits of the oracularized measurements -/

section OracleBits

variable {Vs A : Type*} [Fintype Vs] [DecidableEq Vs] [Nonempty Vs] [Fintype A] [DecidableEq A]
  (Sd : SeededGame Vs A) (T : SyncStrategy Sd.toGame.doubled)

theorem bitObs_oracleOp_oracle (z : Vs) (g : OAns A → Bool) :
    bitObs (Sd.oracleOp T (.oracle, z)) g =
      bitObs (fun ab : A × A => T.P.M (false, Sd.LA z) ab.1 * T.P.M (true, Sd.LB z) ab.2)
        (fun ab => g (.pair ab.1 ab.2)) := by
  unfold bitObs pvmObs
  rw [OAns.sum_eq]
  simp

theorem bitObs_oracleOp_alice (x : Vs) (g : OAns A → Bool) :
    bitObs (Sd.oracleOp T (.alice, x)) g = bitObs (T.P.M (false, x)) (fun a => g (.single a)) := by
  unfold bitObs pvmObs
  rw [OAns.sum_eq]
  simp

theorem bitObs_oracleOp_bob (y : Vs) (g : OAns A → Bool) :
    bitObs (Sd.oracleOp T (.bob, y)) g = bitObs (T.P.M (true, y)) (fun b => g (.single b)) := by
  unfold bitObs pvmObs
  rw [OAns.sum_eq]
  simp

end OracleBits

/-! ## The answer-reduced typed game -/

/-- The type graph of the answer-reduced game: complete, loops included. -/
def arGraph : Role × LIDT.CL.Ty → Role × LIDT.CL.Ty → Prop := fun _ _ => True

instance : DecidableRel arGraph := fun _ _ => isTrue trivial

instance : Nonempty LIDT.CL.Ty := ⟨.point⟩

theorem arGraph_symm (u v : Role × LIDT.CL.Ty) (_ : arGraph u v) : arGraph v u := trivial

theorem arGraph_nonempty : (CL.Graph.edges arGraph).Nonempty :=
  ⟨Classical.arbitrary _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩⟩

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} (d : ℕ) (hM : 2 ^ j ∣ Fintype.card (Fq t ht))
  (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM) (L : PcpDims) (hLM : L.m ≤ 2 ^ j)
  {ℓV : ℕ} (V : TailoredVerifier ℓV) (n : ℕ) (Cc : V.Questions n → Circuit)
  (hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m)

/-- The typed questions of the answer-reduced game at index `n`. -/
abbrev ArQ : Type :=
  CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t))

/-- **The reference predicate of the answer-reduced game**: the typed data accepts the
answers. -/
def arDt (B : ℕ) (u v : ArQ (t := t) (j := j) V n) (a b : Verifier.Answers B) : Bool :=
  decide ((tdata t ht j d L (V.sampler.dim n) sel hLM (circOf L V n Cc hm)).Accepts u v a.1 b.1)

/-- **A sampler of the answer-reduced game**: CL functions on the typed questions whose questions
carry the oracularized input question of the seed's input part, in the type's role, and the
question of the seeded low-degree test of the seed's low-degree part, of the type's low-degree
type. -/
structure ArSampler {ℓ : ℕ}
    (P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ) :
    Prop where
  exactlyOn : ∀ w u, (P w u).ExactlyOn Finset.univ
  role : ∀ w u s, rolePart t j (V.sampler.dim n) ((P w u).eval s) =
    ((inSeeded V n).oquestion u.1 (leftPart s)).2
  ld : ∀ w u s, ldPart t ht j (V.sampler.dim n) ((P w u).eval s) =
    ((regs j).pres sel u.2).eval (ldPart t ht j (V.sampler.dim n) s)

variable {ℓ : ℕ}
  (P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ) (B : ℕ)

/-- The answer-reduced typed game, on the typed questions of `P`, accepting by the typed data. -/
abbrev arGame :
    Game (ArQ (t := t) (j := j) V n) (ArQ (t := t) (j := j) V n) (Verifier.Answers B)
      (Verifier.Answers B) :=
  CL.Detyping.typedGame arGraph arGraph_nonempty P (arDt d hM sel L hLM V n Cc hm B)

/-- On the support of the doubled typed game, the two questions are read off one seed. -/
theorem arGame_support {p q : Bool × ArQ (t := t) (j := j) V n}
    (h : 0 < (arGame d hM sel L hLM V n Cc hm P B).doubled.μ p q) :
    p.1 = false ∧ q.1 = true ∧ ∃ s, p.2.2 = (P false p.2.1).eval s ∧
      q.2.2 = (P true q.2.1).eval s := by
  rw [Game.doubled_μ] at h
  by_cases hpq : p.1 = false ∧ q.1 = true
  · rw [ite_eq_left hpq] at h
    obtain ⟨⟨e, s⟩, h1, h2⟩ := exists_of_dist_pos h
    refine ⟨hpq.1, hpq.2, s, ?_, ?_⟩
    · rw [← h1]
      rfl
    · rw [← h2]
      rfl
  · rw [ite_eq_right hpq] at h
    exact absurd h (lt_irrefl 0)

/-- The oracularized part of a typed question, with its role. -/
def piQ (p : Bool × ArQ (t := t) (j := j) V n) : Role × V.Questions n :=
  (p.2.1.1, rolePart t j (V.sampler.dim n) p.2.2)

theorem piQ_eq {w : Bool} {u : Role × LIDT.CL.Ty} {s : Fin (V.sampler.dim n + D j * t) → 𝔽₂}
    (hP : ArSampler hM sel V n P) :
    piQ V n (w, (u, (P w u).eval s)) = (inSeeded V n).oquestion u.1 (leftPart s) := by
  refine Prod.ext ?_ ?_
  · exact (SeededGame.oquestion_fst _ _ _).symm
  · exact hP.role w u s

/-- **On the support, the oracularized parts of two typed questions have positive weight** in the
oracularized game. -/
theorem oDist_piQ_pos (hP : ArSampler hM sel V n P) {p q : Bool × ArQ (t := t) (j := j) V n}
    (h : 0 < (arGame d hM sel L hLM V n Cc hm P B).doubled.μ p q) :
    0 < (inSeeded V n).oDist (piQ V n p) (piQ V n q) := by
  obtain ⟨hp, hq, s, h1, h2⟩ := arGame_support d hM sel L hLM V n Cc hm P B h
  obtain ⟨w, u, c⟩ := p
  obtain ⟨w', v, c'⟩ := q
  simp only at hp hq h1 h2
  subst hp hq h1 h2
  rw [piQ_eq hM sel V n P hP, piQ_eq hM sel V n P hP]
  exact oDist_oquestion_pos _ _ _ _

/-! ## The strategy -/

/-- The auxiliary game on the typed questions: the weights of the answer-reduced game, and the
oracularized predicate on the oracularized parts. -/
def auxGame : SynchronousGame (Bool × ArQ (t := t) (j := j) V n)
    (OAns (Verifier.Answers (V.tgame n).maxLen)) where
  μ := (arGame d hM sel L hLM V n Cc hm P B).doubled.μ
  μ_nonneg := (arGame d hM sel L hLM V n Cc hm P B).doubled.μ_nonneg
  μ_sum_one := (arGame d hM sel L hLM V n Cc hm P B).doubled.μ_sum_one
  D p q o o' := (inSeeded V n).oaccepts (piQ V n p) (piQ V n q) o o'
  synchronous _ _ _ h := (inSeeded V n).oaccepts_eq_false_of_ne h

/-- **The oracularized strategy, pulled back to the typed questions** along their oracularized
parts. -/
def pullStrat (O : SyncStrategy (inSeeded V n).oracular) :
    SyncStrategy (auxGame d hM sel L hLM V n Cc hm P B) where
  d := O.d
  d_pos := O.d_pos
  P :=
    { M := fun p => O.P.M (piQ V n p)
      selfAdjoint := fun _ => O.P.selfAdjoint _
      projective := fun _ => O.P.projective _
      normalized := fun _ => O.P.normalized _ }

variable (SV : PermStrategy (V.tgame n).doubled)

/-- The input's synchronous strategy, read on the seeded game of the input. -/
def inSync : SyncStrategy (inSeeded V n).toGame.doubled :=
  SV.toSync.copy _

theorem inSync_mu (x y : Bool × V.Questions n) :
    (inSeeded V n).toGame.doubled.μ x y = (V.tgame n).toGame.doubled.μ x y := rfl

theorem isPCC_inSync : (inSync V n SV).IsPCC :=
  SyncStrategy.isPCC_copy SV.isPCC_toSync _ (inSync_mu V n)

theorem value_inSync (h : SV.value = 1) : (inSync V n SV).value = 1 :=
  (SV.toSync.value_copy _ (inSync_mu V n) fun _ _ _ _ => rfl).trans
    (by rw [SV.value_toSync, h])

/-- The oracularization of the input's strategy. -/
def orStrat : SyncStrategy (inSeeded V n).oracular :=
  (inSeeded V n).oracleStrategy (inSync V n SV) (isPCC_inSync V n SV)

theorem isPCC_pullStrat (hP : ArSampler hM sel V n P) :
    (pullStrat d hM sel L hLM V n Cc hm P B (orStrat V n SV)).IsPCC :=
  fun _ _ h o o' => (inSeeded V n).isPCC_oracleStrategy _ (isPCC_inSync V n SV) _ _
    (oDist_piQ_pos d hM sel L hLM V n Cc hm P B hP h) o o'

theorem value_pullStrat (hP : ArSampler hM sel V n P) (hSV : SV.value = 1) :
    (pullStrat d hM sel L hLM V n Cc hm P B (orStrat V n SV)).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  refine tracialValue_eq_one_of_re_eq_zero _ _ _ ?_
  intro p q hμ o o' hrej
  rw [show (pullStrat d hM sel L hLM V n Cc hm P B (orStrat V n SV)).P.M p o *
      (pullStrat d hM sel L hLM V n Cc hm P B (orStrat V n SV)).P.M q o' = 0 from
    (inSeeded V n).oracleOp_mul_eq_zero (inSync V n SV) (isPCC_inSync V n SV)
      (value_inSync V n SV hSV) (oDist_piQ_pos d hM sel L hLM V n Cc hm P B hP hμ) hrej]
  rw [normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]

variable {B}

/-- The honest answer, as an answer of the game. -/
def arAns (hB : ∀ u, len t j d L u ≤ B) (p : Bool × ArQ (t := t) (j := j) V n)
    (o : OAns (Verifier.Answers (V.tgame n).maxLen)) : Verifier.Answers B :=
  ⟨honestAns d hM L sel hLM V n Cc hm p.2 o, by rw [length_honestAns]; exact hB _⟩

/-- **The honest strategy of the answer-reduced game.** -/
def arStrat (hB : ∀ u, len t j d L u ≤ B) :
    SyncStrategy (arGame d hM sel L hLM V n Cc hm P B).doubled :=
  (pullStrat d hM sel L hLM V n Cc hm P B (orStrat V n SV)).mergeAnswersByQuestion _
    (arAns d hM sel L hLM V n Cc hm hB)

theorem isPCC_arStrat (hP : ArSampler hM sel V n P) (hB : ∀ u, len t j d L u ≤ B) :
    (arStrat d hM sel L hLM V n Cc hm P SV hB).IsPCC :=
  SyncStrategy.isPCC_mergeAnswersByQuestion _ _ _ (fun _ _ => rfl)
    (isPCC_pullStrat d hM sel L hLM V n Cc hm P B SV hP)

theorem value_arStrat {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp L V n prm Cc Tt) (hd : 17 ≤ d) (hP : ArSampler hM sel V n P)
    (hB : ∀ u, len t j d L u ≤ B) (hSV : SV.value = 1) :
    (arStrat d hM sel L hLM V n Cc hm P SV hB).value = 1 := by
  refine SyncStrategy.perfect_mergeAnswersByQuestion _ _ _ (fun _ _ => rfl) ?_
    (value_pullStrat d hM sel L hLM V n Cc hm P B SV hP hSV)
  intro p q o o' hμ _ _ hacc
  obtain ⟨hp, hq, s, h1, h2⟩ := arGame_support d hM sel L hLM V n Cc hm P B hμ
  rw [Game.doubled_D, ite_eq_left ⟨hp, hq⟩]
  show arDt d hM sel L hLM V n Cc hm B p.2 q.2 (arAns d hM sel L hLM V n Cc hm hB p o)
    (arAns d hM sel L hLM V n Cc hm hB q o') = true
  rw [arDt, decide_eq_true_iff, accepts_iff]
  refine ⟨length_honestAns _ _ _ _ _ _ _ _ _ _ _, length_honestAns _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  obtain ⟨w, u, c⟩ := p
  obtain ⟨w', v, c'⟩ := q
  simp only at hp hq h1 h2
  subst hp hq h1 h2
  have hacc' : (inSeeded V n).oaccepts ((inSeeded V n).oquestion u.1 (leftPart s))
      ((inSeeded V n).oquestion v.1 (leftPart s)) o o' = true := by
    rw [← piQ_eq hM sel V n P hP, ← piQ_eq hM sel V n P hP]
    exact hacc
  exact arPred_honest d hM L sel hLM V n Cc hm H hd s (u, (P false u).eval s)
    (v, (P true v).eval s) (hP.role false u s) (hP.role true v s) (hP.ld false u s)
    (hP.ld true v s) o o' hacc'

/-- **The honest strategy charges only answers of the types' lengths.** -/
theorem arStrat_support (hB : ∀ u, len t j d L u ≤ B) (q : Bool × ArQ (t := t) (j := j) V n)
    (a : Verifier.Answers B) (ha : ¬a.1.length = len t j d L q.2.1) :
    (arStrat d hM sel L hLM V n Cc hm P SV hB).P.M q a = 0 := by
  change ∑ o ∈ Finset.univ.filter (fun o => arAns d hM sel L hLM V n Cc hm hB q o = a), _ = 0
  refine Finset.sum_eq_zero fun o ho => absurd ?_ ha
  rw [← (Finset.mem_filter.1 ho).2]
  exact length_honestAns _ _ _ _ _ _ _ _ _ _ _

/-- The bit observables of the honest strategy, as those of the oracularized measurement along the
honest answers. -/
theorem isXBit_arStrat_iff (hB : ∀ u, len t j d L u ≤ B) (q : Bool × ArQ (t := t) (j := j) V n)
    (f : Verifier.Answers B → Bool) :
    IsXBit ((arStrat d hM sel L hLM V n Cc hm P SV hB).P.M q) f ↔
      IsXBit ((inSeeded V n).oracleOp (inSync V n SV) (piQ V n q))
        (f ∘ arAns d hM sel L hLM V n Cc hm hB q) :=
  isXBit_merge_iff _ _ f

theorem isZBit_arStrat_iff (hB : ∀ u, len t j d L u ≤ B) (q : Bool × ArQ (t := t) (j := j) V n)
    (f : Verifier.Answers B → Bool) :
    IsZBit ((arStrat d hM sel L hLM V n Cc hm P SV hB).P.M q) f ↔
      IsZBit ((inSeeded V n).oracleOp (inSync V n SV) (piQ V n q))
        (f ∘ arAns d hM sel L hLM V n Cc hm hB q) :=
  isZBit_merge_iff _ _ f

/-- **The answer bits of the honest strategy are X-bits.** -/
theorem isXBit_arStrat (hB : ∀ u, len t j d L u ≤ B) (q : Bool × ArQ (t := t) (j := j) V n)
    (i : ℕ) :
    IsXBit ((arStrat d hM sel L hLM V n Cc hm P SV hB).P.M q) fun a => a.1.getD i false := by
  rw [isXBit_arStrat_iff]
  obtain ⟨w, ⟨r, S⟩, c⟩ := q
  cases r
  · unfold IsXBit
    rw [piQ, bitObs_oracleOp_oracle]
    exact isXBit_pair d hM hLM V n SV _ S _ _ _ i
  · unfold IsXBit
    rw [piQ, bitObs_oracleOp_alice]
    exact isXBit_diag d hM hLM V n SV (false, _) .alice S _ _ _ i
  · unfold IsXBit
    rw [piQ, bitObs_oracleOp_bob]
    exact isXBit_diag d hM hLM V n SV (true, _) .bob S _ _ _ i

/-- **The readable answer bits of the honest strategy are Z-bits.** -/
theorem isZBit_arStrat (hB : ∀ u, len t j d L u ≤ B) (q : Bool × ArQ (t := t) (j := j) V n)
    {i : ℕ} (hi : i < lenR t j d L q.2.1) :
    IsZBit ((arStrat d hM sel L hLM V n Cc hm P SV hB).P.M q) fun a => a.1.getD i false := by
  rw [isZBit_arStrat_iff]
  obtain ⟨w, ⟨r, S⟩, c⟩ := q
  cases r
  · unfold IsZBit
    rw [piQ, bitObs_oracleOp_oracle]
    exact isZBit_pair d hM hLM V n SV _ S _ _ _ hi
  · unfold IsZBit
    rw [piQ, bitObs_oracleOp_alice]
    exact isZBit_diag d hM hLM V n SV (false, _) .alice S _ _ _ hi
  · unfold IsZBit
    rw [piQ, bitObs_oracleOp_bob]
    exact isZBit_diag d hM hLM V n SV (true, _) .bob S _ _ _ hi

/-! ## Completeness -/

/-- **ZPC completeness of the answer-reduced game** (the completeness of thm:combi_ans_red,
II:10285): if the input's `n`-th game has a perfect Z-aligned permutation strategy, so does the
answer-reduced game presented by the typed data `tdata` on the typed game of an answer-reduced
sampler — for a degree `d ≥ 17`, an answer bound at least the types' lengths, and circuits under
which the honest PCPs of accepted answers satisfy the checks. -/
theorem hasPerfectZPC_ar {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp L V n prm Cc Tt) (hd : 17 ≤ d) (hP : ArSampler hM sel V n P) (hℓ : 0 < ℓ)
    (hB : ∀ u, len t j d L u ≤ B) (hV : V.HasPerfectZPC n) :
    (presented arGraph (CL.Detyping.game arGraph P (arDt d hM sel L hLM V n Cc hm B))
      (tdata t ht j d L (V.sampler.dim n) sel hLM (circOf L V n Cc hm))).doubled.HasPerfectZPC := by
  obtain ⟨SV, hSV⟩ := hV
  refine hasPerfectZPC_presented_typed arGraph arGraph_symm arGraph_nonempty P hP.exactlyOn hℓ
    (arDt d hM sel L hLM V n Cc hm B) _ (fun _ a => a.1)
    (fun u a => a.1.length = len t j d L u.1) ⟨[], Nat.zero_le _⟩ (fun u a ha => ha)
    (fun u v a b _ _ _ h => of_decide_eq_true h) (arStrat d hM sel L hLM V n Cc hm P SV hB)
    (isPCC_arStrat d hM sel L hLM V n Cc hm P SV hP hB)
    (value_arStrat d hM sel L hLM V n Cc hm P SV H hd hP hB hSV)
    (fun q a ha => arStrat_support d hM sel L hLM V n Cc hm P SV hB q a ha)
    (fun q i => isXBit_arStrat d hM sel L hLM V n Cc hm P SV hB q i)
    (fun q i hi => (isZBit_arStrat d hM sel L hLM V n Cc hm P SV hB q hi).2)

end MIPRE.Tailored.AnsRed.Typed

end
