/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.SoundCheck

@[expose] public section

/-!
# Soundness of the answer-reduced game: the decoded strategy

The last step of the soundness of `𝔄𝔫𝔰ℜ𝔢𝔡` (II:10697–10760): a strategy for the typed
oracularized game of the input (`oGameT`), on the state of the strategy `T` for the answer-reduced
typed game. An oracle measures its polynomial measurement and answers the pair of answers its
polynomials in the two roles' slots decode to (`decO`); an isolated role measures its own and
answers what its polynomials decode to (`decR`). The decoding of two polynomials is the table of
the readable one on the Boolean cube, cut to the question's readable length, then the linear
one's (`decStr`): exactly the answers the PCP's soundness produces (`accepts_of_dense`).

* An oracle's decoded pair is accepted by the input whenever its polynomials are block-local and
  pass the proof check densely (`accepts_decO`): they are then a PCP of individual degree `d`
  (`Pcp.ofPolys`, `vars_toMv_subset`) whose values are their evaluations, passing the thirteen
  checks on a set of density more than `m (5 + 6(d + 1)) / q` (a fibre count from `F^M` to
  `F^m`).
* Each of the nine ordered pairs of roles fails at most an oracle's game check plus the
  disagreement of the polynomials the two answers decode from (`condFail_OO_le`,
  `condFail_Or_le`, ...), and in all the decoded strategy fails at most `errAR` of the typed
  failure (`one_sub_value_decoded_le`), by `SoundIndiff`, `SoundCheck`, `SoundPoly` and the
  extraction.

The decoded measurements are coarse-grainings of the projective polynomial measurements, so the
decoded strategy is a projective strategy in the same model, and no dilation is needed.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset Cost MIPRE.CL MIPRE.SAT MIPRE.LIDT

/-! ## Block-local polynomials -/

/-- **A coefficient vector vanishing off monomials in `S` is a polynomial in the variables of
`S`.** -/
theorem vars_toMv_subset {F : Type*} [Field F] {n d : ℕ}
    (g : LowIndDegPoly (F := F) (m := n) (d := d)) {S : Set (Fin n)}
    (h : ∀ e, g e ≠ 0 → ∀ i, i ∉ S → (e i : ℕ) = 0) : ↑g.toMv.vars ⊆ S := by
  intro i hi
  rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hi
  obtain ⟨m, hm, him⟩ := hi
  rw [MvPolynomial.mem_support_iff, LowIndDegPoly.toMv, MvPolynomial.coeff_sum] at hm
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [MvPolynomial.coeff_monomial] at he
  by_cases hem : expFinsupp e = m
  · rw [ite_eq_left hem] at he
    by_contra hiS
    rw [← hem, Finsupp.mem_support_iff, expFinsupp_apply] at him
    exact him (h e he i hiS)
  · rw [ite_eq_right hem] at he
    exact absurd rfl he

section Good

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}

theorem get_ocs (s : Slot L) : (slotsOf L .oracle).get (ocs L s) = s :=
  getElem_idxO s

/-- **A block-local outcome's polynomials are in their slots' variables.** -/
theorem good_vars {f : PolyR t ht j d L .oracle} (hf : Good j L hLM f) (s : Slot L) :
    ↑(f (ocs L s)).toMv.vars ⊆ Set.range (Fin.castLE hLM ∘ s.emb) := by
  refine vars_toMv_subset _ fun e he i hi => hf (ocs L s) e he i ?_
  rw [get_ocs]
  simp only [blockM, Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨k, rfl⟩
  exact hi ⟨k, rfl⟩

end Good

/-! ## The decoding -/

section Decode

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} (L : PcpDims) (hLM : L.m ≤ 2 ^ j) {ℓV : ℕ}
  (V : TailoredVerifier ℓV) (n : ℕ)

theorem length_rOf_lt (r : Role) : (rOf L r).length < (slotsOf L r).length := by
  cases r <;> simp [slotsOf, rOf, lOf, lSlots]

/-- The first readable codeword of a role. -/
def c0 (r : Role) : Fin (slotsOf L r).length := ⟨0, one_le_length_slotsOf L r⟩

/-- The first linear codeword of a role. -/
def c1 (r : Role) : Fin (slotsOf L r).length := ⟨(rOf L r).length, length_rOf_lt L r⟩

/-- **The answer two polynomials decode to** at a question of the input: the table of the readable
one on the Boolean cube cut to the question's readable length, then the linear one's. -/
def decStr (x : V.Questions n) {k k' : ℕ} (gR : MvPolynomial (Fin k) (Fq t ht))
    (gL : MvPolynomial (Fin k') (Fq t ht)) : Cost.BitStr :=
  (resStr gR).take ((V.tgame n).lenR x) ++ readBlock ((V.tgame n).lenL x) (resZ gL)

theorem length_decStr_le (x : V.Questions n) {k k' : ℕ} (gR : MvPolynomial (Fin k) (Fq t ht))
    (gL : MvPolynomial (Fin k') (Fq t ht)) : (decStr V n x gR gL).length ≤ (V.tgame n).maxLen := by
  simp only [decStr, List.length_append, List.length_take, length_readBlock]
  calc min ((V.tgame n).lenR x) (resStr gR).length + (V.tgame n).lenL x
      ≤ (V.tgame n).lenR x + (V.tgame n).lenL x := by omega
    _ ≤ (V.tgame n).maxLen := Finset.le_sup (f := (V.tgame n).len) (Finset.mem_univ x)

/-- **A role's decoded answer** at a question of the input: its first readable and first linear
polynomials, read on their slots' blocks, decoded. -/
def decR (r : Role) (x : V.Questions n) (g : PolyR t ht j d L r) :
    Verifier.Answers (V.tgame n).maxLen :=
  ⟨decStr V n x (slotOf (Fin.castLE hLM) (Fin.castLE_injective hLM) ((slotsOf L r).get (c0 L r))
      (g (c0 L r)).toMv)
    (slotOf (Fin.castLE hLM) (Fin.castLE_injective hLM) ((slotsOf L r).get (c1 L r))
      (g (c1 L r)).toMv), length_decStr_le V n _ _ _⟩

/-- **The oracle's decoded answer** at a seed: the two roles' answers its polynomials in their
slots decode to. -/
def decO (y : V.Questions n) (f : PolyR t ht j d L .oracle) :
    OAns (Verifier.Answers (V.tgame n).maxLen) :=
  .pair (decR L hLM V n .alice (qA V n y) (restr L .alice f))
    (decR L hLM V n .bob (qB V n y) (restr L .bob f))

end Decode

/-! ## The PCP's soundness, on a block-local outcome passing densely -/

section Accept

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} {L : PcpDims} {hLM : L.m ≤ 2 ^ j} {ℓV : ℕ}
  {V : TailoredVerifier ℓV} {n : ℕ}

/-- The density of the points of `F^M` whose first `m` coordinates satisfy a condition is that of
the points of `F^m` that satisfy it. -/
theorem card_filter_comp_castLE {F : Type*} [Fintype F] [DecidableEq F] [Nonempty F] {m M : ℕ}
    (h : m ≤ M) (Pr : (Fin m → F) → Prop) [DecidablePred Pr] :
    ((univ.filter fun u : Fin M → F => Pr (u ∘ Fin.castLE h)).card : ℝ) /
        Fintype.card (Fin M → F)
      = ((univ.filter Pr).card : ℝ) / (Fintype.card F : ℝ) ^ m := by
  have hs := MIPRE.CL.sum_comp_injective (F := F) (M := ℝ) (Fin.castLE h)
    (Fin.castLE_injective h) (fun p => if Pr p then (1 : ℝ) else 0)
  simp only [Finset.sum_boole, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [hs, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_pow]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [show (Fintype.card F : ℝ) ^ M = (Fintype.card F : ℝ) ^ (M - m) * (Fintype.card F : ℝ) ^ m
    by rw [← pow_add, Nat.sub_add_cancel h]]
  have : (0 : ℝ) < (Fintype.card F : ℝ) ^ (M - m) := by positivity
  field_simp

theorem decR_alice (x : V.Questions n) (f : PolyR t ht j d L .oracle) :
    (decR L hLM V n .alice x (restr L .alice f)).1 =
      (resStr (slotOf (Fin.castLE hLM) (Fin.castLE_injective hLM) Slot.gA
        (f (ocs L .gA)).toMv)).take ((V.tgame n).lenR x) ++
      readBlock ((V.tgame n).lenL x) (resZ (slotOf (Fin.castLE hLM) (Fin.castLE_injective hLM)
        Slot.gLa (f (ocs L .gLa)).toMv)) := rfl

theorem decR_bob (x : V.Questions n) (f : PolyR t ht j d L .oracle) :
    (decR L hLM V n .bob x (restr L .bob f)).1 =
      (resStr (slotOf (Fin.castLE hLM) (Fin.castLE_injective hLM) Slot.gB
        (f (ocs L .gB)).toMv)).take ((V.tgame n).lenR x) ++
      readBlock ((V.tgame n).lenL x) (resZ (slotOf (Fin.castLE hLM) (Fin.castLE_injective hLM)
        Slot.gLb (f (ocs L .gLb)).toMv)) := rfl

/-- **The decoded pair of a block-local outcome passing the proof check densely is accepted**
(cor:functional_viewpoint_final, clause 2, through `accepts_of_dense`). -/
theorem accepts_decO {prm : PolyTimeFun ℕ (Unary × Unary)} {Cc : V.Questions n → Circuit}
    {Tt : ℕ} (H : HonestHyp L V n prm Cc Tt) (hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m)
    (y : V.Questions n) {f : PolyR t ht j d L .oracle} (hg : Good j L hLM f)
    (hdn : Dense L hLM (circOf L V n Cc hm y) f) :
    (V.tgame n).Accepts (qA V n y) (qB V n y)
      (decR L hLM V n .alice (qA V n y) (restr L .alice f)).1
      (decR L hLM V n .bob (qB V n y) (restr L .bob f)).1 := by
  classical
  have hloc : ∀ s, ↑((fun s => (f (ocs L s)).toMv) s).vars ⊆
      Set.range (Fin.castLE hLM ∘ s.emb) := good_vars hg
  have hdeg : (Pcp.ofPolys (Fin.castLE hLM) (Fin.castLE_injective hLM)
      fun s => (f (ocs L s)).toMv).IndDeg d :=
    indDeg_ofPolys _ _ hloc fun s i => LowIndDegPoly.degreeOf_toMv_le _ i
  -- the proof check on the evaluations is the PCP's at the point's first coordinates
  have hpass : ∀ u : Fin (2 ^ j) → Fq t ht,
      PassV L hLM (circOf L V n Cc hm y) u (evalR u f) ↔
        (Pcp.ofPolys (Fin.castLE hLM) (Fin.castLE_injective hLM)
          fun s => (f (ocs L s)).toMv).Passes (circOf L V n Cc hm y) (u ∘ Fin.castLE hLM) := by
    intro u
    have e : (fun s => evalR u f (ocs L s)) = (Pcp.ofPolys (Fin.castLE hLM)
        (Fin.castLE_injective hLM) fun s => (f (ocs L s)).toMv).slotEval
          (u ∘ Fin.castLE hLM) := by
      funext s
      rw [slotEval_ofPolys _ _ hloc u s, LowIndDegPoly.eval_toMv]
      rfl
    rw [PassV, e]
    exact (passes_iff_passesV _ _ _).symm
  have hdens : (L.m : ℝ) * chkDeg 5 d / Fintype.card (Fq t ht) <
      ((univ.filter fun p => (Pcp.ofPolys (Fin.castLE hLM) (Fin.castLE_injective hLM)
        fun s => (f (ocs L s)).toMv).Passes (circOf L V n Cc hm y) p).card : ℝ) /
        (Fintype.card (Fq t ht) : ℝ) ^ L.m := by
    rw [← card_filter_comp_castLE hLM]
    have hfil : (univ.filter fun u : Fin (2 ^ j) → Fq t ht =>
        PassV L hLM (circOf L V n Cc hm y) u (evalR u f)) =
        univ.filter fun u => (Pcp.ofPolys (Fin.castLE hLM) (Fin.castLE_injective hLM)
          fun s => (f (ocs L s)).toMv).Passes (circOf L V n Cc hm y) (u ∘ Fin.castLE hLM) :=
      Finset.filter_congr fun u _ => hpass u
    rw [← hfil]
    exact hdn
  rw [decR_alice, decR_bob]
  -- elaborated before the goal is consulted, so that the PCP is the one of `hdeg`
  have hacc := accepts_of_dense prm V (qA V n y) (qB V n y) H.hℓ H.hdm (H.wf y) (H.inputs y)
    (hm y) (H.desc y) hdeg _ (fun p hp => (Finset.mem_filter.1 hp).2) hdens
  exact hacc

end Accept

/-! ## The decoded strategy -/

section Strategy

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}
  (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B)) (hL : LIDT.Simul.SoundIn M)
  (hd : 1 ≤ d)

variable (V n) in
/-- The input's seeded game on its CL functions one level up. -/
abbrev inCL : SeededGame (V.Questions n) (Verifier.Answers (V.tgame n).maxLen) :=
  SeededGame.ofCL (liftedCl V n) (V.tgame n).toGame.D

variable (V n) in
/-- **The typed oracularized game of the input** at index `n`. -/
abbrev oGameT :=
  CL.Detyping.typedGame roleGraph roleGraph_nonempty (fun _ => roleFamily (liftedCl V n))
    (inCL V n).oaccepts

/-- **Alice's decoded measurements.** -/
def MAd : CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
    POVMIn (OAns (Verifier.Answers (V.tgame n).maxLen)) 𝒜
  | (.oracle, y) => (GA T hL hd .oracle y).map (decO L hLM V n y)
  | (r, x) => (GA T hL hd r x).map fun g => .single (decR L hLM V n r x g)

/-- **Bob's decoded measurements.** -/
def MBd : CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
    POVMIn (OAns (Verifier.Answers (V.tgame n).maxLen)) ℬ
  | (.oracle, y) => (GB T hL hd .oracle y).map (decO L hLM V n y)
  | (r, x) => (GB T hL hd r x).map fun g => .single (decR L hLM V n r x g)

theorem MAd_iso {r : Role} (hr : r ≠ .oracle) (x : V.Questions n) :
    MAd T hL hd (r, x) = (GA T hL hd r x).map fun g => .single (decR L hLM V n r x g) := by
  cases r
  · exact absurd rfl hr
  · rfl
  · rfl

theorem MBd_iso {r : Role} (hr : r ≠ .oracle) (x : V.Questions n) :
    MBd T hL hd (r, x) = (GB T hL hd r x).map fun g => .single (decR L hLM V n r x g) := by
  cases r
  · exact absurd rfl hr
  · rfl
  · rfl

/-- **The decoded strategy**: a projective strategy in the model, on `T`'s state, for the typed
oracularized game of the input. -/
def decoded : M.ProjStrat (oGameT V n) where
  PA := MAd T hL hd
  PB := MBd T hL hd
  projA q := by
    obtain ⟨r, x⟩ := q
    cases r
    · exact POVMIn.isPVMIn_map (extR_proj T hL hd _ _).1 _
    · exact POVMIn.isPVMIn_map (extR_proj T hL hd _ _).1 _
    · exact POVMIn.isPVMIn_map (extR_proj T hL hd _ _).1 _
  projB q := by
    obtain ⟨r, x⟩ := q
    cases r
    · exact POVMIn.isPVMIn_map (extR_proj T hL hd _ _).2 _
    · exact POVMIn.isPVMIn_map (extR_proj T hL hd _ _).2 _
    · exact POVMIn.isPVMIn_map (extR_proj T hL hd _ _).2 _
  ψ_unit := T.ψ_unit

/-! ## The nine pairs of roles -/

/-- The weight of Alice's oracle outcomes whose decoded pair fails the game check. -/
def gcA (y : V.Questions n) : ℝ :=
  ∑ f, (if (inCL V n).gameCheck (.oracle, y) (decO L hLM V n y f) = true then 0
    else M.bornProb ((GA T hL hd .oracle y).op f) 1)

/-- The weight of Bob's oracle outcomes whose decoded pair fails the game check. -/
def gcB (y : V.Questions n) : ℝ :=
  ∑ f, (if (inCL V n).gameCheck (.oracle, y) (decO L hLM V n y f) = true then 0
    else M.bornProb 1 ((GB T hL hd .oracle y).op f))

theorem comp_decO {r : Role} (hr : r ≠ .oracle) (z : V.Questions n)
    (f : PolyR t ht j d L .oracle) :
    MIPRE.AnswerReduction.comp r (decO L hLM V n z f) =
      decR L hLM V n r (oq V n r z) (restr L r f) := by
  cases r
  · exact absurd rfl hr
  · rfl
  · rfl

/-- **Two oracles**: the two game checks and the disagreement of the two measurements. -/
theorem condFail_OO_le (y : V.Questions n) :
    M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd) (.oracle, y) (.oracle, y)
      ≤ gcA T hL hd y + gcB T hL hd y
        + M.dis (GA T hL hd .oracle y) (GB T hL hd .oracle y) := by
  have h := M.condFail_le_of (G := oGameT V n) T.ψ_unit (x := (.oracle, y)) (y := (.oracle, y))
    (MA := MAd T hL hd) (MB := MBd T hL hd)
    (fun a => ¬(SeededGame.shapeOk .oracle a = true ∧
      (inCL V n).gameCheck (.oracle, y) a = true))
    (fun b => ¬(SeededGame.shapeOk .oracle b = true ∧
      (inCL V n).gameCheck (.oracle, y) b = true)) id id (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        subst hab
        show (inCL V n).oaccepts _ _ _ _ = true
        rcases a with ⟨a1, a2⟩ | a1 <;>
          simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer])
  refine h.trans (add_le_add (add_le_add (le_of_eq ?_) (le_of_eq ?_)) ?_)
  · simp only [MAd]
    rw [M.sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · simp only [MBd]
    rw [M.sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · simp only [MAd, MBd, POVMIn.map_map]
    exact M.dis_map_le _ _ _

/-- **An oracle and an isolated role**: the oracle's game check and the disagreement of its
polynomials in the role's slots with the role's. -/
theorem condFail_Or_le {r : Role} (hr : r ≠ .oracle) (z : V.Questions n) :
    M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd) (.oracle, z) (r, oq V n r z)
      ≤ gcA T hL hd z
        + M.dis ((GA T hL hd .oracle z).map (restr L r)) (GB T hL hd r (oq V n r z)) := by
  have h := M.condFail_le_of (G := oGameT V n) T.ψ_unit (x := (.oracle, z))
    (y := (r, oq V n r z)) (MA := MAd T hL hd) (MB := MBd T hL hd)
    (fun a => ¬(SeededGame.shapeOk .oracle a = true ∧
      (inCL V n).gameCheck (.oracle, z) a = true))
    (fun b => ¬SeededGame.shapeOk r b = true) (MIPRE.AnswerReduction.comp r)
    MIPRE.AnswerReduction.sgl (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (inCL V n).oaccepts _ _ _ _ = true
        cases r
        · exact absurd rfl hr
        all_goals
          rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
            simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
              SeededGame.gameCheck, MIPRE.AnswerReduction.comp, MIPRE.AnswerReduction.sgl])
  refine h.trans ?_
  have hB : ∑ b, (if ¬SeededGame.shapeOk r b = true then M.bornProb 1
      ((MBd T hL hd (r, oq V n r z)).op b) else 0) = 0 := by
    rw [MBd_iso T hL hd hr, M.sum_ite_bornProb_one_map']
    cases r
    · exact absurd rfl hr
    all_goals simp [SeededGame.shapeOk]
  rw [hB, add_zero]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MAd]
    rw [M.sum_ite_bornProb_one_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · rw [MBd_iso T hL hd hr]
    simp only [MAd, POVMIn.map_map]
    have e1 : (fun f : PolyR t ht j d L .oracle =>
        MIPRE.AnswerReduction.comp r (decO L hLM V n z f)) =
        fun f => decR L hLM V n r (oq V n r z) (restr L r f) :=
      funext fun f => comp_decO hr z f
    have e2 : (fun g : PolyR t ht j d L r => MIPRE.AnswerReduction.sgl
        (OAns.single (decR L hLM V n r (oq V n r z) g))) =
        fun g => decR L hLM V n r (oq V n r z) g := rfl
    rw [e1, e2, ← POVMIn.map_map (GA T hL hd .oracle z) (restr L r)]
    exact M.dis_map_le _ _ _

/-- **An isolated role and an oracle**: the oracle's game check and the disagreement of the role's
polynomials with the oracle's in the role's slots. -/
theorem condFail_rO_le {r : Role} (hr : r ≠ .oracle) (z : V.Questions n) :
    M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd) (r, oq V n r z) (.oracle, z)
      ≤ gcB T hL hd z
        + M.dis (GA T hL hd r (oq V n r z)) ((GB T hL hd .oracle z).map (restr L r)) := by
  have h := M.condFail_le_of (G := oGameT V n) T.ψ_unit (x := (r, oq V n r z))
    (y := (.oracle, z)) (MA := MAd T hL hd) (MB := MBd T hL hd)
    (fun a => ¬SeededGame.shapeOk r a = true)
    (fun b => ¬(SeededGame.shapeOk .oracle b = true ∧
      (inCL V n).gameCheck (.oracle, z) b = true)) MIPRE.AnswerReduction.sgl
    (MIPRE.AnswerReduction.comp r) (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        show (inCL V n).oaccepts _ _ _ _ = true
        cases r
        · exact absurd rfl hr
        all_goals
          rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
            simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
              SeededGame.gameCheck, MIPRE.AnswerReduction.comp, MIPRE.AnswerReduction.sgl])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk r a = true then
      M.bornProb ((MAd T hL hd (r, oq V n r z)).op a) 1 else 0) = 0 := by
    rw [MAd_iso T hL hd hr, M.sum_ite_bornProb_one_map]
    cases r
    · exact absurd rfl hr
    all_goals simp [SeededGame.shapeOk]
  rw [hA, zero_add]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [MBd]
    rw [M.sum_ite_bornProb_one_map']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [decO, SeededGame.shapeOk, true_and]
    split_ifs <;> simp_all
  · rw [MAd_iso T hL hd hr]
    simp only [MBd, POVMIn.map_map]
    have e1 : (fun f : PolyR t ht j d L .oracle =>
        MIPRE.AnswerReduction.comp r (decO L hLM V n z f)) =
        fun f => decR L hLM V n r (oq V n r z) (restr L r f) :=
      funext fun f => comp_decO hr z f
    have e2 : (fun g : PolyR t ht j d L r => MIPRE.AnswerReduction.sgl
        (OAns.single (decR L hLM V n r (oq V n r z) g))) =
        fun g => decR L hLM V n r (oq V n r z) g := rfl
    rw [e1, e2, ← POVMIn.map_map (GB T hL hd .oracle z) (restr L r)]
    exact M.dis_map_le _ _ _

/-- **An isolated role against itself**: the disagreement of the two polynomial
measurements. -/
theorem condFail_rr_le {r : Role} (hr : r ≠ .oracle) (x : V.Questions n) :
    M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd) (r, x) (r, x)
      ≤ M.dis (GA T hL hd r x) (GB T hL hd r x) := by
  have h := M.condFail_le_of (G := oGameT V n) T.ψ_unit (x := (r, x)) (y := (r, x))
    (MA := MAd T hL hd) (MB := MBd T hL hd)
    (fun a => ¬SeededGame.shapeOk r a = true) (fun b => ¬SeededGame.shapeOk r b = true)
    id id (fun a b ha hb hab => by
        simp only [not_not] at ha hb
        subst hab
        show (inCL V n).oaccepts _ _ _ _ = true
        cases r
        · exact absurd rfl hr
        all_goals
          rcases a with ⟨a1, a2⟩ | a1 <;>
            simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
              SeededGame.gameCheck])
  refine h.trans ?_
  have hA : ∑ a, (if ¬SeededGame.shapeOk r a = true then
      M.bornProb ((MAd T hL hd (r, x)).op a) 1 else 0) = 0 := by
    rw [MAd_iso T hL hd hr, M.sum_ite_bornProb_one_map]
    cases r
    · exact absurd rfl hr
    all_goals simp [SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk r b = true then
      M.bornProb 1 ((MBd T hL hd (r, x)).op b) else 0) = 0 := by
    rw [MBd_iso T hL hd hr, M.sum_ite_bornProb_one_map']
    cases r
    · exact absurd rfl hr
    all_goals simp [SeededGame.shapeOk]
  rw [hA, hB, zero_add, zero_add, MAd_iso T hL hd hr, MBd_iso T hL hd hr, POVMIn.map_map,
    POVMIn.map_map]
  exact M.dis_map_le _ _ _

/-- **Two different isolated roles** never fail: only the shapes are checked. -/
theorem condFail_rr'_le {r r' : Role} (hr : r ≠ .oracle) (hr' : r' ≠ .oracle) (hrr : r ≠ r')
    (x x' : V.Questions n) :
    M.condFail (oGameT V n) (MAd T hL hd) (MBd T hL hd) (r, x) (r', x') ≤ 0 := by
  have h := M.condFail_le_of (G := oGameT V n) T.ψ_unit (x := (r, x)) (y := (r', x'))
    (MA := MAd T hL hd) (MB := MBd T hL hd)
    (fun a => ¬SeededGame.shapeOk r a = true) (fun b => ¬SeededGame.shapeOk r' b = true)
    (fun _ => ()) (fun _ => ()) (fun a b ha hb _ => by
        simp only [not_not] at ha hb
        show (inCL V n).oaccepts _ _ _ _ = true
        cases r <;> cases r'
        all_goals first
          | exact absurd rfl hr
          | exact absurd rfl hr'
          | exact absurd rfl hrr
          | (rcases a with ⟨a1, a2⟩ | a1 <;> rcases b with ⟨b1, b2⟩ | b1 <;>
              simp_all [SeededGame.oaccepts, SeededGame.shapeOk, SeededGame.oracleVsPlayer,
                SeededGame.gameCheck]))
  refine h.trans (le_of_eq ?_)
  have hA : ∑ a, (if ¬SeededGame.shapeOk r a = true then
      M.bornProb ((MAd T hL hd (r, x)).op a) 1 else 0) = 0 := by
    rw [MAd_iso T hL hd hr, M.sum_ite_bornProb_one_map]
    cases r
    · exact absurd rfl hr
    all_goals simp [SeededGame.shapeOk]
  have hB : ∑ b, (if ¬SeededGame.shapeOk r' b = true then
      M.bornProb 1 ((MBd T hL hd (r', x')).op b) else 0) = 0 := by
    rw [MBd_iso T hL hd hr', M.sum_ite_bornProb_one_map']
    cases r'
    · exact absurd rfl hr'
    all_goals simp [SeededGame.shapeOk]
  rw [hA, hB, MIPRE.AnswerReduction.dis_map_const M T.ψ_unit]
  norm_num

/-! ## The game checks -/

theorem gameCheck_decO {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ}
    (H : HonestHyp L V n prm Cc Tt) (y : V.Questions n) {f : PolyR t ht j d L .oracle}
    (hg : Good j L hLM f) (hdn : Dense L hLM (circOf L V n Cc hm y) f) :
    (inCL V n).gameCheck (.oracle, y) (decO L hLM V n y f) = true := by
  have h := accepts_decO H hm y hg hdn
  simp only [inCL, SeededGame.gameCheck, SeededGame.ofCL, decO]
  simp only [liftedCl, CLFun.eval_liftTo]
  exact decide_eq_true h

open Classical in
/-- **Alice's oracle fails the game check** at most on the outcomes that are not block-local or
pass the proof check sparsely. -/
theorem gcA_le {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ} (H : HonestHyp L V n prm Cc Tt)
    (y : V.Questions n) :
    gcA T hL hd y ≤ ∑ f, (if Good j L hLM f then 0
        else M.bornProb ((GA T hL hd .oracle y).op f) 1)
      + ∑ f, (if Dense L hLM (circOf L V n Cc hm y) f then 0
        else M.bornProb ((GA T hL hd .oracle y).op f) 1) := by
  unfold gcA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun f _ => ?_
  have hβ := M.bornProb_nonneg ((GA T hL hd .oracle y).op_nonneg f) zero_le_one
  by_cases hg : Good j L hLM f
  · by_cases hdn : Dense L hLM (circOf L V n Cc hm y) f
    · rw [ite_eq_left (gameCheck_decO H y hg hdn), ite_eq_left hg, ite_eq_left hdn, add_zero]
    · rw [ite_eq_left hg, ite_eq_right hdn, zero_add]
      split_ifs <;> linarith
  · rw [ite_eq_right hg]
    split_ifs <;> linarith

open Classical in
/-- **Bob's oracle fails the game check** at most on the outcomes that are not block-local or
pass the proof check sparsely, which weigh at most those of Alice's and the two measurements'
disagreement. -/
theorem gcB_le {prm : PolyTimeFun ℕ (Unary × Unary)} {Tt : ℕ} (H : HonestHyp L V n prm Cc Tt)
    (y : V.Questions n) :
    gcB T hL hd y ≤ M.dis (GA T hL hd .oracle y) (GB T hL hd .oracle y)
      + (∑ f, (if Good j L hLM f then 0
        else M.bornProb ((GA T hL hd .oracle y).op f) 1)
      + ∑ f, (if Dense L hLM (circOf L V n Cc hm y) f then 0
        else M.bornProb ((GA T hL hd .oracle y).op f) 1)) := by
  have h : ∑ b, (if ¬(Good j L hLM b ∧ Dense L hLM (circOf L V n Cc hm y) b)
      then M.bornProb 1 ((GB T hL hd .oracle y).op b) else 0)
      ≤ M.dis ((GA T hL hd .oracle y).map id) ((GB T hL hd .oracle y).map id)
        + ∑ a, (if ¬(Good j L hLM a ∧ Dense L hLM (circOf L V n Cc hm y) a)
          then M.bornProb ((GA T hL hd .oracle y).op a) 1 else 0) :=
    sum_ite_read_le' M T.ψ_unit (GA T hL hd .oracle y) (GB T hL hd .oracle y) id id
      (fun f => ¬(Good j L hLM f ∧ Dense L hLM (circOf L V n Cc hm y) f))
  have hdis := M.dis_map_le (GA T hL hd .oracle y) (GB T hL hd .oracle y) id
  have hB : gcB T hL hd y ≤ ∑ f, (if ¬(Good j L hLM f ∧ Dense L hLM (circOf L V n Cc hm y) f)
      then M.bornProb 1 ((GB T hL hd .oracle y).op f) else 0) := by
    unfold gcB
    refine Finset.sum_le_sum fun f _ => ?_
    have hβ := M.bornProb_nonneg zero_le_one ((GB T hL hd .oracle y).op_nonneg f)
    by_cases hgd : Good j L hLM f ∧ Dense L hLM (circOf L V n Cc hm y) f
    · rw [ite_eq_left (gameCheck_decO H y hgd.1 hgd.2), ite_eq_right (not_not.mpr hgd)]
    · rw [ite_eq_left hgd]
      split_ifs <;> linarith
  have hA : ∑ f, (if ¬(Good j L hLM f ∧ Dense L hLM (circOf L V n Cc hm y) f)
      then M.bornProb ((GA T hL hd .oracle y).op f) 1 else 0)
      ≤ ∑ f, (if Good j L hLM f then 0 else M.bornProb ((GA T hL hd .oracle y).op f) 1)
        + ∑ f, (if Dense L hLM (circOf L V n Cc hm y) f then 0
          else M.bornProb ((GA T hL hd .oracle y).op f) 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun f _ => ?_
    have hβ := M.bornProb_nonneg ((GA T hL hd .oracle y).op_nonneg f) zero_le_one
    by_cases hg : Good j L hLM f <;> by_cases hdn : Dense L hLM (circOf L V n Cc hm y) f <;>
      simp [hg, hdn, hβ]
  linarith

end Strategy

end MIPRE.Tailored.AnsRed.Typed

end
