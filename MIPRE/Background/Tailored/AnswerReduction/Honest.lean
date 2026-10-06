/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.Typed
public import MIPRE.Background.LIDT.CLHonest
public import MIPRE.Tailored.AnsRed.HonestPair

@[expose] public section

/-!
# The honest answers of the answer-reduced game

The completeness of the answer-reduced game (slice P4d of `planning/aldous-lyons-track.md`): the
honest strategy measures the oracularized input strategy and answers, at a typed question, with
the honest low-degree answers of the polynomials of the honest PCP of the input answers
(cor:functional_viewpoint_final) — the oracle with all of them, an isolated player with the two
of its own answer. This file defines those answers as bit strings and proves the four checks of
the answer-reduced predicate on them, for polynomials of the right shape.

* `encCws`: codewords of field elements as bit strings, the inverse of `cw` (`cw_encCws`);
  `honestBits`: the honest low-degree answer of a tuple of polynomials, which `decAns` reads back
  as `LIDT.CL.honest` (`decAns_honestBits`).
* `ldPolys`: a role's codewords of a PCP, on the test's variables.
* The checks: `accepts_honestBits` (low degree: `LIDT.CL.accepts_honest` on the common sample),
  `isoAgrees_honestBits` (consistency), `indOK_honestBits` (indifference: a polynomial missing a
  variable is constant along its axis), `passesV_honestBits` (the proof check, from the
  identities).
* `honestAns`: the honest answer at a typed question to an answer of the oracularized input game
  (`MIPRE.SeededGame.oracular` of `inSeeded`), and `arPred_honest`, the functional half of
  completeness: at two questions read off one seed, answers the oracularized predicate accepts
  give honest answers the answer-reduced predicate accepts.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.Tailored.Intro MvPolynomial

variable {t : ℕ} {ht : 1 ≤ t}

/-! ## Codewords as bit strings -/

theorem ofBool_decide_eq_one (z : ZMod 2) : (ofBool (decide (z = 1)) : ZMod 2) = z := by
  fin_cases z <;> rfl

variable (t ht) in
/-- **`k` codewords of `nc` field elements as a bit string**, each element as its `t` canonical
bits, codeword after codeword: the layout `cw` reads. -/
def encCws (k nc : ℕ) (coef : ℕ → ℕ → Fq t ht) : BitStr :=
  List.ofFn fun i : Fin (k * nc * t) => decide (shoupCoordinateEquiv t ht
    (coef (i / (nc * t)) (i / t % nc)) ⟨i % t, Nat.mod_lt _ (by omega)⟩ = 1)

theorem length_encCws (k nc : ℕ) (coef : ℕ → ℕ → Fq t ht) :
    (encCws t ht k nc coef).length = k * nc * t :=
  List.length_ofFn

theorem getD_encCws {k nc : ℕ} (coef : ℕ → ℕ → Fq t ht) {c e i : ℕ} (hc : c < k) (he : e < nc)
    (hi : i < t) :
    (encCws t ht k nc coef).getD ((c * nc + e) * t + i) false =
      decide (shoupCoordinateEquiv t ht (coef c e) ⟨i, hi⟩ = 1) := by
  have hce : c * nc + e < k * nc := by nlinarith
  have hlt : (c * nc + e) * t + i < k * nc * t := by nlinarith
  rw [encCws, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
  have h1 : ((c * nc + e) * t + i) / (nc * t) = c := by
    rw [show (c * nc + e) * t + i = (e * t + i) + c * (nc * t) by ring,
      Nat.add_mul_div_right _ _ (Nat.mul_pos (by omega) (by omega)),
      Nat.div_eq_of_lt (by nlinarith), zero_add]
  have h2 : ((c * nc + e) * t + i) / t % nc = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, zero_add,
      Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he]
  have h3 : ((c * nc + e) * t + i) % t = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simp only [h1, h2, h3]

variable (j d : ℕ)

/-- **`cw` reads the codewords back.** -/
theorem cw_encCws (S : LIDT.CL.Ty) {k : ℕ} (coef : ℕ → ℕ → Fq t ht) {c e : ℕ} (hc : c < k)
    (he : e < ncoef j d S) : cw t ht j d S (encCws t ht k (ncoef j d S) coef) c e = coef c e := by
  unfold cw elt
  rw [LinearEquiv.symm_apply_eq]
  funext i
  rw [getD_encCws coef hc he i.2, ofBool_decide_eq_one]

/-! ## Honest low-degree answers -/

variable {j} (hM : 2 ^ j ∣ Fintype.card (Fq t ht))

/-- **The coefficients of the honest answer** of a tuple of polynomials to a question: the values
at a point, the coefficients of the restrictions to a line. -/
def honestCoef {k : ℕ} (G : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht)) :
    LIDT.CL.Question (Fq t ht) (2 ^ j) → ℕ → ℕ → Fq t ht
  | .point u, c, _ => if hc : c < k then eval u (G ⟨c, hc⟩) else 0
  | .aline u₀ s, c, e => if hc : c < k then
      (lineRestrict u₀ (Pi.single (LIDT.CL.chi hM s) 1) (G ⟨c, hc⟩)).coeff e else 0
  | .dline u₀ _ v, c, e => if hc : c < k then (lineRestrict u₀ v (G ⟨c, hc⟩)).coeff e else 0

/-- **The honest answer of a tuple of polynomials** to a question of the low-degree type `S`, as a
bit string. -/
def honestBits (S : LIDT.CL.Ty) {k : ℕ} (G : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht))
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) : BitStr :=
  encCws t ht k (ncoef j d S) (honestCoef hM G q)

theorem length_honestBits (S : LIDT.CL.Ty) {k : ℕ}
    (G : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht))
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) :
    (honestBits d hM S G q).length = k * ncoef j d S * t :=
  length_encCws _ _ _

theorem honestCoef_congr {k k' : ℕ} {G : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht)}
    {G' : Fin k' → MvPolynomial (Fin (2 ^ j)) (Fq t ht)} {c c' : ℕ} (hc : c < k) (hc' : c' < k')
    (h : G ⟨c, hc⟩ = G' ⟨c', hc'⟩) (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) (e : ℕ) :
    honestCoef hM G q c e = honestCoef hM G' q c' e := by
  cases q <;> simp only [honestCoef, dite_eq_left hc, dite_eq_left hc', h]

variable {L : PcpDims} (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM)

/-- **`decAns` reads the honest answer back** at a question the presentation computes. -/
theorem decAns_honestBits (r : Role)
    (G : Fin (slotsOf L r).length → MvPolynomial (Fin (2 ^ j)) (Fq t ht))
    (S : LIDT.CL.Ty) (x : Fin (D j) → Fq t ht) :
    decAns t ht j d L r S (honestBits d hM S G ((regs j).questionOf sel S x)) =
      LIDT.CL.honest hM (d := d) G ((regs j).questionOf sel S x) := by
  cases S
  · simp only [decAns, LIDT.CL.Regs.questionOf, LIDT.CL.honest]
    congr 1
    funext c
    rw [honestBits, cw_encCws j d .point _ c.2 (by simp [ncoef])]
    simp [honestCoef]
  · simp only [decAns, LIDT.CL.Regs.questionOf, LIDT.CL.honest]
    congr 1
    funext c e
    rw [honestBits, cw_encCws j d .aline _ c.2 (by have := e.2; simp only [ncoef]; omega)]
    simp [honestCoef, LIDT.CL.lineCo]
  · simp only [decAns, LIDT.CL.Regs.questionOf, LIDT.CL.honest]
    congr 1
    funext c e
    rw [honestBits, cw_encCws j d .dline _ c.2 (by have := e.2; simp only [ncoef]; omega)]
    simp [honestCoef, LIDT.CL.lineCo]

theorem sampleOf_question_ty (S S' τ : LIDT.CL.Ty) (x : Fin (D j) → Fq t ht) :
    ((regs j).sampleOf sel S x).question hM τ = ((regs j).sampleOf sel S' x).question hM τ := by
  cases τ <;> rfl

/-- **The low-degree check accepts honest answers** of one tuple of polynomials of individual
degree at most `d`, at two questions of one sample. -/
theorem accepts_honestBits (r : Role)
    (G : Fin (slotsOf L r).length → MvPolynomial (Fin (2 ^ j)) (Fq t ht))
    (hG : ∀ c i, (G c).degreeOf i ≤ d) (S₁ S₂ : LIDT.CL.Ty) (x : Fin (D j) → Fq t ht) :
    LIDT.CL.accepts hM ((regs j).questionOf sel S₁ (((regs j).pres sel S₁).eval x))
      ((regs j).questionOf sel S₂ (((regs j).pres sel S₂).eval x))
      (decAns t ht j d L r S₁ (honestBits d hM S₁ G
        ((regs j).questionOf sel S₁ (((regs j).pres sel S₁).eval x))))
      (decAns t ht j d L r S₂ (honestBits d hM S₂ G
        ((regs j).questionOf sel S₂ (((regs j).pres sel S₂).eval x)))) = true := by
  rw [decAns_honestBits, decAns_honestBits, LIDT.CL.Regs.questionOf_eval,
    LIDT.CL.Regs.questionOf_eval, sampleOf_question_ty hM sel S₂ S₁ S₂]
  exact LIDT.CL.accepts_honest hG _ S₁ S₂

/-! ## A role's codewords of a PCP -/

variable (L) (hLM : L.m ≤ 2 ^ j)

/-- **A role's codewords of a PCP**, on the low-degree test's variables. -/
def ldPolys (P : Pcp L (Fq t ht)) (r : Role) :
    Fin (slotsOf L r).length → MvPolynomial (Fin (2 ^ j)) (Fq t ht) :=
  fun c => rename (Fin.castLE hLM) (P.slotPoly ((slotsOf L r).get c))

variable {L}

theorem ldPolys_eq (P : Pcp L (Fq t ht)) (r : Role) (c : Fin (slotsOf L r).length) :
    ldPolys L hLM P r c = rename (Fin.castLE hLM ∘ ((slotsOf L r).get c).emb)
      (P.slot ((slotsOf L r).get c)) := by
  rw [ldPolys, Pcp.slotPoly, rename_rename]

theorem degreeOf_ldPolys {P : Pcp L (Fq t ht)} {d' : ℕ} (hP : P.IndDeg d') (hd : d' ≤ d)
    (r : Role) (c : Fin (slotsOf L r).length) (i : Fin (2 ^ j)) :
    (ldPolys L hLM P r c).degreeOf i ≤ d := by
  rw [ldPolys_eq]
  exact (degreeOf_rename_le_of_injective ((Fin.castLE_injective hLM).comp
    ((slotsOf L r).get c).emb_injective) (hP.slot _) i).trans hd

theorem degreeOf_rename_eq_zero {k N : ℕ} {f : Fin k → Fin N} (hf : Function.Injective f)
    (p : MvPolynomial (Fin k) (Fq t ht)) {i : Fin N} (hi : ∀ a, f a ≠ i) :
    (rename f p).degreeOf i = 0 := by
  classical
  rw [degreeOf_def, degrees_rename_of_injective hf, Multiset.count_eq_zero]
  intro h
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 h
  exact hi a ha

/-- **Indifference holds of honest answers**: a codeword whose block misses the direction of an
axis-parallel line does not involve that variable, so it is constant along the line. -/
theorem indOK_honestBits (r : Role) (P : Pcp L (Fq t ht)) (S : LIDT.CL.Ty)
    (x : Fin (D j) → Fq t ht) :
    IndOK t ht j d L hM hLM r (honestBits d hM S (ldPolys L hLM P r) ((regs j).questionOf sel S x))
      ((regs j).questionOf sel S x) := by
  cases S
  · trivial
  · intro c hc e he
    rw [honestBits, cw_encCws j d .aline _ c.2 (by simp only [ncoef]; omega)]
    simp only [LIDT.CL.Regs.questionOf, honestCoef, dite_eq_left c.2, Fin.eta]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have h0 : (ldPolys L hLM P r c).degreeOf (LIDT.CL.chi hM (sel.π (x (regs j).coord))) = 0 := by
      rw [ldPolys_eq]
      exact degreeOf_rename_eq_zero ((Fin.castLE_injective hLM).comp
        ((slotsOf L r).get c).emb_injective) _
        fun a ha => hc (Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩)
    have := natDegree_lineRestrict_single_le ((regs j).ptOf x)
      (LIDT.CL.chi hM (sel.π (x (regs j).coord))) (ldPolys L hLM P r c)
    omega
  · trivial

/-- **Consistency holds of honest answers**: an isolated role's codewords of a PCP agreeing with
another in the role's slots are that PCP's oracle codewords in those slots. -/
theorem isoAgrees_honestBits (r : Role) (P Q : Pcp L (Fq t ht))
    (hPQ : ∀ s ∈ slotsOf L r, P.slot s = Q.slot s) (S : LIDT.CL.Ty)
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) :
    IsoAgrees t ht j d L r S (honestBits d hM S (ldPolys L hLM P r) q)
      (honestBits d hM S (ldPolys L hLM Q .oracle) q) := by
  intro c e he
  rw [honestBits, honestBits, cw_encCws j d S _ c.2 he, cw_encCws j d S _ (idxO_lt _) he]
  refine honestCoef_congr hM c.2 (idxO_lt _) ?_ q e
  have hs : (slotsOf L .oracle).get ⟨idxO ((slotsOf L r).get c), idxO_lt _⟩ =
      (slotsOf L r).get c := getElem_idxO _
  have hm : (slotsOf L r).get c ∈ slotsOf L r := by
    rw [List.get_eq_getElem]
    exact List.getElem_mem _
  simp only [ldPolys, Fin.eta]
  rw [hs, Pcp.slotPoly, Pcp.slotPoly, hPQ _ hm]

/-- **The proof check holds of the oracle's honest point answer** for a PCP satisfying the
identities: its values are the PCP's values at the point. -/
theorem passesV_honestBits (P : Pcp L (Fq t ht)) (T : MvPolynomial (Fin L.m) (Fq t ht))
    (hP : P.Identities T) (x : Fin (D j) → Fq t ht) :
    PassesV T (vals t ht j d L (honestBits d hM .point (ldPolys L hLM P .oracle)
        ((regs j).questionOf sel .point x)))
      (ptm L hLM ((regs j).questionOf sel .point x).base) := by
  have e : vals t ht j d L (honestBits d hM .point (ldPolys L hLM P .oracle)
      ((regs j).questionOf sel .point x)) =
        P.slotEval (ptm L hLM ((regs j).questionOf sel .point x).base) := by
    funext s
    rw [vals, honestBits, cw_encCws j d .point _ (idxO_lt s) (by simp [ncoef])]
    simp only [LIDT.CL.Regs.questionOf, honestCoef, dite_eq_left (idxO_lt s),
      LIDT.CL.Question.base, ldPolys, List.get_eq_getElem, getElem_idxO, eval_rename,
      Pcp.eval_slotPoly, ptm]
  rw [e, ← passes_iff_passesV]
  exact hP.passes _

/-! ## The honest answers at typed questions -/

section Answers

variable (L) {ℓV : ℕ} (V : TailoredVerifier ℓV) (n : ℕ)
  (Cc : V.Questions n → Circuit) (hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m)

/-- Alice's question map of the input sampler at index `n`. -/
abbrev qA (z : V.Questions n) : V.Questions n := (V.sampler.cl n .alice).eval z

/-- Bob's question map of the input sampler at index `n`. -/
abbrev qB (z : V.Questions n) : V.Questions n := (V.sampler.cl n .bob).eval z

/-- **The input's `n`-th game as a seeded game**, the oracularization's input. -/
def inSeeded : SeededGame (V.Questions n) (Verifier.Answers (V.tgame n).maxLen) :=
  ⟨qA V n, qB V n, (V.tgame n).toGame.D⟩

variable (t ht) in
/-- **The honest PCP a role answers from**, at its question, for an answer of the oracularized
game: the oracle's of the pair at the questions of the seed, an isolated player's of its own
answer paired with itself (whose polynomials in the player's slots are the oracle's, by
`slot_pairPcp_alice` and `slot_pairPcp_bob`). -/
def rolePcp {B : ℕ} : Role → OAns (Verifier.Answers B) → V.Questions n → Pcp L (Fq t ht)
  | .oracle, .pair a b, z =>
      pairPcp L V n (circOf L V n Cc hm z) (Cc z) (qA V n z) (qB V n z) a.1 b.1
  | .alice, .single a, x => pairPcp L V n (circOf L V n Cc hm x) (Cc x) x x a.1 a.1
  | .bob, .single b, y => pairPcp L V n (circOf L V n Cc hm y) (Cc y) y y b.1 b.1
  | _, _, z => pairPcp L V n (circOf L V n Cc hm z) (Cc z) z z [] []

theorem indDeg_rolePcp {B : ℕ} (r : Role) (o : OAns (Verifier.Answers B)) (z : V.Questions n) :
    (rolePcp t ht L V n Cc hm r o z).IndDeg 17 := by
  cases r <;> cases o <;> exact indDeg_pairPcp _ _ _ _ _ _ _ _

/-- **The honest answer at a typed question** to an answer of the oracularized game: the honest
low-degree answers of the role's codewords of its PCP, at the question's low-degree question. -/
def honestAns {B : ℕ}
    (u : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t)))
    (o : OAns (Verifier.Answers B)) : BitStr :=
  honestBits d hM u.1.2 (ldPolys L hLM (rolePcp t ht L V n Cc hm u.1.1 o
    (rolePart t j (V.sampler.dim n) u.2)) u.1.1) (ldQ t ht j (V.sampler.dim n) sel u.1.2 u.2)

theorem length_honestAns {B : ℕ}
    (u : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t)))
    (o : OAns (Verifier.Answers B)) :
    (honestAns d hM L sel hLM V n Cc hm u o).length = len t j d L u.1 := by
  rw [honestAns, length_honestBits, len_eq]

/-- **The functional half of completeness**: at two typed questions read off one seed — the
oracularized input question of the seed's input part in each role, and the low-degree questions
of the seed's low-degree part — answers the oracularized predicate accepts give honest answers the
answer-reduced predicate accepts, when the honest PCPs of accepted answers satisfy the checks
(`HonestHyp`) and the degree `d` is at least `17`. -/
theorem arPred_honest {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp L V n prm Cc Tt) (hd : 17 ≤ d) (s : Fin (V.sampler.dim n + D j * t) → 𝔽₂)
    (u v : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t)))
    (hu : rolePart t j _ u.2 = ((inSeeded V n).oquestion u.1.1 (leftPart s)).2)
    (hv : rolePart t j _ v.2 = ((inSeeded V n).oquestion v.1.1 (leftPart s)).2)
    (hu' : ldPart t ht j _ u.2 = ((regs j).pres sel u.1.2).eval (ldPart t ht j _ s))
    (hv' : ldPart t ht j _ v.2 = ((regs j).pres sel v.1.2).eval (ldPart t ht j _ s))
    (o₁ o₂ : OAns (Verifier.Answers (V.tgame n).maxLen))
    (hacc : (inSeeded V n).oaccepts ((inSeeded V n).oquestion u.1.1 (leftPart s))
      ((inSeeded V n).oquestion v.1.1 (leftPart s)) o₁ o₂ = true) :
    ArPred t ht j d L (V.sampler.dim n) sel hLM (circOf L V n Cc hm) u v
      (honestAns d hM L sel hLM V n Cc hm u o₁) (honestAns d hM L sel hLM V n Cc hm v o₂) := by
  obtain ⟨⟨r₁, S₁⟩, c₁⟩ := u
  obtain ⟨⟨r₂, S₂⟩, c₂⟩ := v
  simp only at hu hv hu' hv' hacc ⊢
  set z := leftPart s
  set x₀ := ldPart t ht j _ s
  have hq₁ : ldQ t ht j _ sel S₁ c₁ =
      (regs j).questionOf sel S₁ (((regs j).pres sel S₁).eval x₀) := by
    rw [ldQ, hu']
  have hq₂ : ldQ t ht j _ sel S₂ c₂ =
      (regs j).questionOf sel S₂ (((regs j).pres sel S₂).eval x₀) := by
    rw [ldQ, hv']
  simp only [SeededGame.oaccepts, Bool.and_eq_true, SeededGame.oquestion_fst] at hacc
  obtain ⟨⟨⟨⟨⟨⟨hs₁, hs₂⟩, hg₁⟩, hg₂⟩, hrr⟩, hov₁⟩, hov₂⟩ := hacc
  -- an oracle's answer is a pair the input game accepts
  have horacle : ∀ (o : OAns (Verifier.Answers (V.tgame n).maxLen)),
      SeededGame.shapeOk .oracle o = true →
      (inSeeded V n).gameCheck ((inSeeded V n).oquestion .oracle z) o = true →
      ∃ a b : Verifier.Answers (V.tgame n).maxLen, o = .pair a b ∧
        (V.tgame n).Accepts (qA V n z) (qB V n z) a.1 b.1 := by
    intro o h1 h2
    cases o with
    | pair a b =>
      refine ⟨a, b, rfl, ?_⟩
      simpa [SeededGame.gameCheck, inSeeded, TailoredGame.toGame] using h2
    | single a => simp [SeededGame.shapeOk] at h1
  have hdeg : ∀ (r : Role) (o : OAns (Verifier.Answers (V.tgame n).maxLen)) (z' : V.Questions n),
      ∀ c i,
      (ldPolys L hLM (rolePcp t ht L V n Cc hm r o z') r c).degreeOf i ≤ d := fun r o z' c i =>
    degreeOf_ldPolys d hLM (indDeg_rolePcp L V n Cc hm r o z') hd r c i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the low-degree checks, at one role: one PCP, by check 2(a)
    rintro r rfl rfl
    have ho : o₁ = o₂ := by simpa using hrr
    subst ho
    simp only [honestAns]
    rw [hu, ← hv, hq₁, hq₂]
    exact accepts_honestBits d hM sel _ _ (hdeg _ _ _) S₁ S₂ x₀
  · -- the consistency checks, at one low-degree type: the isolated player's polynomials
    rintro rfl
    have hq : ldQ t ht j _ sel S₁ c₁ = ldQ t ht j _ sel S₁ c₂ := by rw [hq₁, hq₂]
    cases r₁ <;> cases r₂ <;> try trivial
    · -- the oracle, then Alice
      obtain ⟨a, b, rfl, hab⟩ := horacle o₁ hs₁ hg₁
      cases o₂ with
      | pair _ _ => simp [SeededGame.shapeOk] at hs₂
      | single a' =>
        have haa : a = a' := by simpa [SeededGame.oracleVsPlayer] using hov₁
        subst haa
        show IsoAgrees t ht j d L .alice S₁ (honestAns d hM L sel hLM V n Cc hm _ _)
          (honestAns d hM L sel hLM V n Cc hm _ _)
        simp only [honestAns]
        rw [hu, hv, hq]
        refine isoAgrees_honestBits d hM hLM .alice _ _ (fun s' hs' => ?_) S₁ _
        exact slot_pairPcp_alice V n _ _ _ _ _ _ _
          (by rw [hab.1]; exact Nat.le_add_right _ _) (H.lenR _) s' hs'
    · -- the oracle, then Bob
      obtain ⟨a, b, rfl, hab⟩ := horacle o₁ hs₁ hg₁
      cases o₂ with
      | pair _ _ => simp [SeededGame.shapeOk] at hs₂
      | single b' =>
        have hbb : b = b' := by simpa [SeededGame.oracleVsPlayer] using hov₁
        subst hbb
        show IsoAgrees t ht j d L .bob S₁ (honestAns d hM L sel hLM V n Cc hm _ _)
          (honestAns d hM L sel hLM V n Cc hm _ _)
        simp only [honestAns]
        rw [hu, hv, hq]
        exact isoAgrees_honestBits d hM hLM .bob _ _
          (fun s' hs' => slot_pairPcp_bob V n _ _ _ _ _ _ _ _ _ _ s' hs') S₁ _
    · -- Alice, then the oracle
      obtain ⟨a, b, rfl, hab⟩ := horacle o₂ hs₂ hg₂
      cases o₁ with
      | pair _ _ => simp [SeededGame.shapeOk] at hs₁
      | single a' =>
        have haa : a = a' := by simpa [SeededGame.oracleVsPlayer] using hov₂
        subst haa
        show IsoAgrees t ht j d L .alice S₁ (honestAns d hM L sel hLM V n Cc hm _ _)
          (honestAns d hM L sel hLM V n Cc hm _ _)
        simp only [honestAns]
        rw [hu, hv, hq]
        refine isoAgrees_honestBits d hM hLM .alice _ _ (fun s' hs' => ?_) S₁ _
        exact slot_pairPcp_alice V n _ _ _ _ _ _ _
          (by rw [hab.1]; exact Nat.le_add_right _ _) (H.lenR _) s' hs'
    · -- Bob, then the oracle
      obtain ⟨a, b, rfl, hab⟩ := horacle o₂ hs₂ hg₂
      cases o₁ with
      | pair _ _ => simp [SeededGame.shapeOk] at hs₁
      | single b' =>
        have hbb : b = b' := by simpa [SeededGame.oracleVsPlayer] using hov₂
        subst hbb
        show IsoAgrees t ht j d L .bob S₁ (honestAns d hM L sel hLM V n Cc hm _ _)
          (honestAns d hM L sel hLM V n Cc hm _ _)
        simp only [honestAns]
        rw [hu, hv, hq]
        exact isoAgrees_honestBits d hM hLM .bob _ _
          (fun s' hs' => slot_pairPcp_bob V n _ _ _ _ _ _ _ _ _ _ s' hs') S₁ _
  · -- indifference of the first answer
    simp only [honestAns]
    rw [hq₁]
    exact indOK_honestBits d hM sel hLM r₁ _ S₁ _
  · -- indifference of the second answer
    simp only [honestAns]
    rw [hq₂]
    exact indOK_honestBits d hM sel hLM r₂ _ S₂ _
  · -- the proof check of the first answer
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨a, b, rfl, hab⟩ := horacle o₁ hs₁ hg₁
    simp only [honestAns]
    rw [hu, hq₁]
    exact passesV_honestBits d hM sel hLM _ _ (H.identities hm z hab) _
  · -- the proof check of the second answer
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨a, b, rfl, hab⟩ := horacle o₂ hs₂ hg₂
    simp only [honestAns]
    rw [hv, hq₂]
    exact passesV_honestBits d hM sel hLM _ _ (H.identities hm z hab) _

end Answers

end MIPRE.Tailored.AnsRed.Typed

end
