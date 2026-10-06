/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.PcpHonest
public import MIPRE.Tailored.AnsRed.Slots

@[expose] public section

/-!
# The honest PCP of a pair of answers, slot by slot

The honest strategy of the answer-reduced game (slice P4d of `planning/aldous-lyons-track.md`)
answers with the polynomials of the honest PCP `pairPcp` of the input answers
(cor:functional_viewpoint_final): the oracle with all of them, an isolated player with the two
of its own answer. This file records what the strategy's proof needs of them, slot by slot.

* `slot_pairPcp_alice`, `slot_pairPcp_bob`: an isolated player's polynomials depend only on its
  own question and answer, so the oracle's are the player's (the consistency check).
* `slot_pairPcp_readable`: a readable polynomial depends only on the readable answers.
* `slot_pairPcp_affine`: a linear polynomial is `F₂`-affine in the linear answers, the readable
  ones fixed.
* `indDeg_pairPcp`, `identities_pairPcp`: its individual degree is at most `17`, and when the
  input game accepts the answers it satisfies the thirteen checks identically.
* `HonestHyp`: the hypotheses on the parameters and on each seed's circuit under which that holds
  at every seed (`HonestHyp.identities`), what the completeness of the answer-reduced game takes.
-/

namespace MIPRE.Tailored.AnsRed

open MvPolynomial LowDegree SAT Cost

variable {F : Type*} [Field F] {L : PcpDims}

/-! ## Encodings read only the cube -/

theorem encTbl_congr {k : ℕ} {t t' : ℕ → F} (h : ∀ c < 2 ^ k, t c = t' c) :
    encTbl k t = encTbl k t' := by
  unfold encTbl
  congr 1
  funext y
  exact h _ (cubeIndex y).isLt

theorem encB_congr {k : ℕ} {t t' : ℕ → Bool} (h : ∀ c < 2 ^ k, t c = t' c) :
    (encB k t : MvPolynomial (Fin k) F) = encB k t' :=
  encTbl_congr fun c hc => by rw [h c hc]

theorem encZ_congr [CharP F 2] {k : ℕ} {f f' : ℕ → ZMod 2} (h : ∀ c < 2 ^ k, f c = f' c) :
    (encZ k f : MvPolynomial (Fin k) F) = encZ k f' :=
  encTbl_congr fun c hc => by rw [h c hc]

/-! ## Readable and linear slots of `Induce` -/

variable [CharP F 2]

/-- **A readable polynomial of the honest PCP depends only on the readable tables.** -/
theorem slot_induce_readable (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt Lt' : LTables)
    (s : Slot L) (hs : s.readable = true) :
    (induce L T R Lt).slot s = (induce L T R Lt').slot s := by
  cases s <;> first | rfl | simp [Slot.readable] at hs

omit [CharP F 2] in
theorem assignCert_zero {k : ℕ} : assignCert (0 : MvPolynomial (Fin k) F) = 0 := by
  simp [assignCert]

/-- **A linear polynomial of the honest PCP is `F₂`-affine in the linear tables.** -/
theorem slot_induce_affine (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt₁ Lt₂ : LTables)
    (s : Slot L) (hs : s.readable = false) :
    (induce L T R (Lt₁ + Lt₂)).slot s + (induce L T R 0).slot s =
      (induce L T R Lt₁).slot s + (induce L T R Lt₂).slot s := by
  obtain ⟨hLa, hLb, hL, hαL, hβLa, hβLb, hβL⟩ := linear_induce_add T R Lt₁ Lt₂
  have e0La : (induce L T R 0).gLa = 0 := encZ_zero
  have e0Lb : (induce L T R 0).gLb = 0 := encZ_zero
  have e0L : ∀ k, (induce L T R 0).gL k = 0 := fun _ => encZ_zero
  have e0βLa : ∀ i, (induce L T R 0).βLa i = 0 := fun i => by
    show assignCert (encZ L.ℓ (0 : ℕ → ZMod 2) : MvPolynomial (Fin L.ℓ) F) i = 0
    rw [encZ_zero, assignCert_zero, Pi.zero_apply]
  have e0βLb : ∀ i, (induce L T R 0).βLb i = 0 := fun i => by
    show assignCert (encZ L.ℓ (0 : ℕ → ZMod 2) : MvPolynomial (Fin L.ℓ) F) i = 0
    rw [encZ_zero, assignCert_zero, Pi.zero_apply]
  have e0βL : ∀ k i, (induce L T R 0).βL k i = 0 := fun k i => by
    show assignCert (encZ L.dm (0 : ℕ → ZMod 2) : MvPolynomial (Fin L.dm) F) i = 0
    rw [encZ_zero, assignCert_zero, Pi.zero_apply]
  cases s <;> simp only [Slot.readable, Bool.true_eq_false] at hs
  · show (induce L T R (Lt₁ + Lt₂)).gLa + (induce L T R 0).gLa =
      (induce L T R Lt₁).gLa + (induce L T R Lt₂).gLa
    rw [hLa, e0La, add_zero]
  · show (induce L T R (Lt₁ + Lt₂)).gLb + (induce L T R 0).gLb =
      (induce L T R Lt₁).gLb + (induce L T R Lt₂).gLb
    rw [hLb, e0Lb, add_zero]
  · rename_i k
    show (induce L T R (Lt₁ + Lt₂)).gL k + (induce L T R 0).gL k =
      (induce L T R Lt₁).gL k + (induce L T R Lt₂).gL k
    rw [hL k, e0L k, add_zero]
  · rename_i X
    exact hαL X
  · rename_i i
    show (induce L T R (Lt₁ + Lt₂)).βLa i + (induce L T R 0).βLa i =
      (induce L T R Lt₁).βLa i + (induce L T R Lt₂).βLa i
    rw [hβLa i, e0βLa i, add_zero]
  · rename_i i
    show (induce L T R (Lt₁ + Lt₂)).βLb i + (induce L T R 0).βLb i =
      (induce L T R Lt₁).βLb i + (induce L T R Lt₂).βLb i
    rw [hβLb i, e0βLb i, add_zero]
  · rename_i k i
    show (induce L T R (Lt₁ + Lt₂)).βL k i + (induce L T R 0).βL k i =
      (induce L T R Lt₁).βL k i + (induce L T R Lt₂).βL k i
    rw [hβL k i, e0βL k i, add_zero]

theorem LTables.add_self (X : LTables) : X + X = 0 := by
  obtain ⟨a, b, c⟩ := X
  show (⟨a + a, b + b, c + c⟩ : LTables) = ⟨0, 0, 0⟩
  congr 1 <;> funext <;> simp [CharTwo.add_self_eq_zero]

omit [CharP F 2] in
/-- The degrees of the slots of a PCP of individual degree at most `d`. -/
theorem Pcp.IndDeg.slot {P : Pcp L F} {d : ℕ} (h : P.IndDeg d) :
    ∀ (s : Slot L) (i : Fin s.size), (P.slot s).degreeOf i ≤ d := by
  obtain ⟨hA, hB, hO, hW, hLa, hLb, hL, hαR, hαL, hβA, hβB, hβO, hβW, hβLa, hβLb, hβL⟩ := h
  intro s i
  cases s
  · exact hA i
  · exact hB i
  · exact hO i
  · exact hW _ i
  · exact hαR _ i
  · exact hβA _ i
  · exact hβB _ i
  · exact hβO _ i
  · exact hβW _ _ i
  · exact hLa i
  · exact hLb i
  · exact hL _ i
  · exact hαL _ i
  · exact hβLa _ i
  · exact hβLb _ i
  · exact hβL _ _ i

/-! ## The honest PCP of an answer pair -/

variable {ℓV : ℕ} (V : TailoredVerifier ℓV) (n : ℕ)

variable (L) in
/-- **The honest PCP of an answer pair** `(a, b)` at the questions `(x, y)`
(cor:functional_viewpoint_final), for a circuit polynomial `T` and a circuit `Cc` whose formula's
witnesses the readable tables carry: `Induce` of the readable tables of the readable parts and the
linear tables of the linear parts. -/
noncomputable def pairPcp (T : MvPolynomial (Fin L.m) F) (Cc : Circuit) (xq yq : V.Questions n)
    (a b : BitStr) : Pcp L F :=
  induce L T
    (honestR L V n Cc xq yq (a.take ((V.tgame n).lenR xq)) (b.take ((V.tgame n).lenR yq)))
    (honestL L V n xq yq (a.take ((V.tgame n).lenR xq)) (a.drop ((V.tgame n).lenR xq))
      (b.take ((V.tgame n).lenR yq)) (b.drop ((V.tgame n).lenR yq)))

theorem indDeg_pairPcp (T : MvPolynomial (Fin L.m) F) (Cc : Circuit) (xq yq : V.Questions n)
    (a b : BitStr) : (pairPcp L V n T Cc xq yq a b).IndDeg 17 :=
  indDeg_induce _ _ _

/-- **A readable polynomial of the honest PCP depends only on the readable answers.** -/
theorem slot_pairPcp_readable (T : MvPolynomial (Fin L.m) F) (Cc : Circuit)
    (xq yq : V.Questions n) {a a' b b' : BitStr}
    (ha : a.take ((V.tgame n).lenR xq) = a'.take ((V.tgame n).lenR xq))
    (hb : b.take ((V.tgame n).lenR yq) = b'.take ((V.tgame n).lenR yq)) (s : Slot L)
    (hs : s.readable = true) :
    (pairPcp L V n T Cc xq yq a b).slot s = (pairPcp L V n T Cc xq yq a' b').slot s := by
  unfold pairPcp
  rw [ha, hb]
  exact slot_induce_readable _ _ _ _ s hs

theorem toBits_add {N : ℕ} (u w : Fin N → CL.𝔽₂) :
    BinaryPolynomial.xorBits (CL.toBits u) (CL.toBits w) = CL.toBits (u + w) := by
  apply List.ext_getElem (by simp [BinaryPolynomial.xorBits, CL.toBits])
  intro i h1 h2
  simp only [BinaryPolynomial.xorBits, CL.toBits, List.getElem_zipWith, List.getElem_ofFn,
    Pi.add_apply]
  have key : ∀ x y : ZMod 2, (decide (x = 1) ^^ decide (y = 1)) = decide (x + y = 1) := by
    decide
  exact key _ _

theorem honestL_toBits_add (xq yq : V.Questions n) (aR bR : BitStr) {NA NB : ℕ}
    (u₁ u₂ : Fin NA → CL.𝔽₂) (w₁ w₂ : Fin NB → CL.𝔽₂) :
    honestL L V n xq yq aR (CL.toBits (u₁ + u₂)) bR (CL.toBits (w₁ + w₂)) =
      honestL L V n xq yq aR (CL.toBits u₁) bR (CL.toBits w₁) +
        honestL L V n xq yq aR (CL.toBits u₂) bR (CL.toBits w₂) := by
  rw [← toBits_add, ← toBits_add]
  exact honestL_xorBits V n xq yq aR bR (by simp) (by simp)

theorem honestL_toBits_zero (xq yq : V.Questions n) (aR bR : BitStr) (NA NB : ℕ) :
    honestL L V n xq yq aR (CL.toBits (0 : Fin NA → CL.𝔽₂)) bR (CL.toBits (0 : Fin NB → CL.𝔽₂)) =
      0 := by
  have h := honestL_toBits_add (L := L) V n xq yq aR bR (0 : Fin NA → CL.𝔽₂) 0
    (0 : Fin NB → CL.𝔽₂) 0
  rw [add_zero, add_zero] at h
  rw [h, LTables.add_self]

/-- **A linear polynomial of the honest PCP is `F₂`-affine in the linear answers**, the readable
answers fixed. -/
theorem slot_pairPcp_affine (T : MvPolynomial (Fin L.m) F) (Cc : Circuit)
    (xq yq : V.Questions n) {aR bR : BitStr} (haR : aR.length = (V.tgame n).lenR xq)
    (hbR : bR.length = (V.tgame n).lenR yq) {NA NB : ℕ} (u₁ u₂ : Fin NA → CL.𝔽₂)
    (w₁ w₂ : Fin NB → CL.𝔽₂) (s : Slot L) (hs : s.readable = false) :
    (pairPcp L V n T Cc xq yq (aR ++ CL.toBits (u₁ + u₂)) (bR ++ CL.toBits (w₁ + w₂))).slot s +
        (pairPcp L V n T Cc xq yq (aR ++ CL.toBits (0 : Fin NA → CL.𝔽₂))
          (bR ++ CL.toBits (0 : Fin NB → CL.𝔽₂))).slot s =
      (pairPcp L V n T Cc xq yq (aR ++ CL.toBits u₁) (bR ++ CL.toBits w₁)).slot s +
        (pairPcp L V n T Cc xq yq (aR ++ CL.toBits u₂) (bR ++ CL.toBits w₂)).slot s := by
  have tA : ∀ l : BitStr, (aR ++ l).take ((V.tgame n).lenR xq) = aR := fun l => by
    rw [← haR, List.take_left]
  have tB : ∀ l : BitStr, (bR ++ l).take ((V.tgame n).lenR yq) = bR := fun l => by
    rw [← hbR, List.take_left]
  have dA : ∀ l : BitStr, (aR ++ l).drop ((V.tgame n).lenR xq) = l := fun l => by
    rw [← haR, List.drop_left]
  have dB : ∀ l : BitStr, (bR ++ l).drop ((V.tgame n).lenR yq) = l := fun l => by
    rw [← hbR, List.drop_left]
  simp only [pairPcp, tA, tB, dA, dB]
  rw [honestL_toBits_add, honestL_toBits_zero]
  exact slot_induce_affine _ _ _ _ s hs

/-! ## The isolated players' polynomials -/

/-- **Alice's polynomials depend only on her question and answer**, when her answer carries its
readable part and that part fits the table. -/
theorem slot_pairPcp_alice (T T' : MvPolynomial (Fin L.m) F) (Cc Cc' : Circuit)
    (xq yq yq' : V.Questions n) {a b b' : BitStr} (ha : (V.tgame n).lenR xq ≤ a.length)
    (hR : (V.tgame n).lenR xq ≤ 2 ^ L.ℓ) (s : Slot L) (hs : s ∈ slotsOf L .alice) :
    (pairPcp L V n T Cc xq yq a b).slot s = (pairPcp L V n T' Cc' xq yq' a b').slot s := by
  simp only [slotsOf, rOf, lOf, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · show encB L.ℓ _ = encB L.ℓ _
    refine encB_congr fun c hc => ?_
    have hlen : ((a.take ((V.tgame n).lenR xq)) ++
        List.replicate (2 ^ L.ℓ - (V.tgame n).lenR xq) false).length = 2 ^ L.ℓ := by
      simp only [List.length_append, List.length_take, List.length_replicate]
      omega
    show (honestA L V n xq yq _ _).getD c false = (honestA L V n xq yq' _ _).getD c false
    rw [honestA, honestA, List.getD_append (a.take ((V.tgame n).lenR xq) ++
        List.replicate (2 ^ L.ℓ - (V.tgame n).lenR xq) false) _ false c (by omega),
      List.getD_append (a.take ((V.tgame n).lenR xq) ++
        List.replicate (2 ^ L.ℓ - (V.tgame n).lenR xq) false) _ false c (by omega)]
  · show encZ L.ℓ _ = encZ L.ℓ _
    refine encZ_congr fun c hc => ?_
    show tbl (2 ^ L.ℓ) _ _ c = tbl (2 ^ L.ℓ) _ _ c
    rw [tbl, tbl, ite_eq_left hc, ite_eq_left hc]

/-- **Bob's polynomials depend only on his question and answer.** -/
theorem slot_pairPcp_bob (T T' : MvPolynomial (Fin L.m) F) (Cc Cc' : Circuit)
    (xq xq' yq : V.Questions n) (a a' b : BitStr) (s : Slot L) (hs : s ∈ slotsOf L .bob) :
    (pairPcp L V n T Cc xq yq a b).slot s = (pairPcp L V n T' Cc' xq' yq a' b).slot s := by
  simp only [slotsOf, rOf, lOf, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · rfl
  · show encZ L.ℓ _ = encZ L.ℓ _
    congr 1
    funext c
    show tbl (2 ^ L.ℓ) _ _ (2 ^ L.ℓ + c) = tbl (2 ^ L.ℓ) _ _ (2 ^ L.ℓ + c)
    rw [tbl, tbl, ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## Accepted answers -/

/-- **An accepted answer pair makes the verifier's programs halt**: otherwise the constraints are
the one that rejects everything. -/
theorem accepts_halts {xq yq : V.Questions n} {a b : BitStr}
    (hacc : (V.tgame n).Accepts xq yq a b) :
    V.LenDefined n (CL.toBits xq) ∧ V.LenDefined n (CL.toBits yq) ∧
      ∃ cs, LpIs V.lp n (CL.toBits xq) (CL.toBits yq) (a.take ((V.tgame n).lenR xq))
        (b.take ((V.tgame n).lenR yq)) cs := by
  by_contra h
  have hc : (V.tgame n).cons xq yq (a.take ((V.tgame n).lenR xq))
      (b.take ((V.tgame n).lenR yq)) = [rejectConstraint
        (V.lenOf n (CL.toBits xq) false + V.lenOf n (CL.toBits xq) true +
          V.lenOf n (CL.toBits yq) false + V.lenOf n (CL.toBits yq) true)] := by
    show V.consOf n _ _ _ _ = _
    rw [TailoredVerifier.consOf, dite_eq_right h]
  exact not_satisfies_rejectConstraint _ _
    (hacc.2.2 _ (by rw [hc]; exact List.mem_singleton_self _))

/-- **The honest PCP of an accepted answer pair satisfies the thirteen checks identically**
(`identities_honest`), at parameters the lengths fit, for a circuit that describes the output
indicator through the windows within a time `L*` meets. -/
theorem identities_pairPcp (prm : PolyTimeFun ℕ (Unary × Unary)) (hℓ : (prm n).1.length = L.ℓ)
    (hdm : (prm n).2.length = L.dm) {Cc : Circuit} {Tt : ℕ} (hWF : Cc.WellFormed)
    (hin : Cc.inputs = L.nIn) (hm : Cc.inputs + Cc.size = L.m) (xq yq : V.Questions n)
    (hdesc : Cc.DescribesWindows (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r (lstar prm V) n
      (CL.toBits xq) (CL.toBits yq) Tt)
    {a b : BitStr}
    (hT : (lstar prm V).Accepts n (CL.toBits xq) (CL.toBits yq)
        (honestA L V n xq yq (a.take ((V.tgame n).lenR xq)) (b.take ((V.tgame n).lenR yq)))
        (honestB L V n yq (b.take ((V.tgame n).lenR yq))) →
      (lstar prm V).AcceptsWithin n (CL.toBits xq) (CL.toBits yq)
        (honestA L V n xq yq (a.take ((V.tgame n).lenR xq)) (b.take ((V.tgame n).lenR yq)))
        (honestB L V n yq (b.take ((V.tgame n).lenR yq))) Tt)
    (hTlen : 2 ^ L.ℓ + 2 ^ L.oW ≤ Tt)
    (hRx : (V.tgame n).lenR xq ≤ 2 ^ L.ℓ) (hLx : (V.tgame n).lenL xq ≤ 2 ^ L.ℓ)
    (hRy : (V.tgame n).lenR yq ≤ 2 ^ L.ℓ) (hLy : (V.tgame n).lenL yq ≤ 2 ^ L.ℓ)
    (hD : ((V.tgame n).cons xq yq (a.take ((V.tgame n).lenR xq))
        (b.take ((V.tgame n).lenR yq))).length * (2 ^ L.ℓ + 2 ^ L.ℓ) + (2 ^ L.ℓ + 2 ^ L.ℓ) ≤
      2 ^ L.dm)
    (hacc : (V.tgame n).Accepts xq yq a b) :
    (pairPcp L V n (rename (Fin.cast hm) (Cc.finiteArith (F := F))) Cc xq yq a b).Identities
      (rename (Fin.cast hm) Cc.finiteArith) := by
  obtain ⟨hx, hy, hlp⟩ := accepts_halts V n hacc
  have ha := hacc.1
  have hb := hacc.2.1
  have hlx : (V.tgame n).len xq = (V.tgame n).lenR xq + (V.tgame n).lenL xq := rfl
  have hly : (V.tgame n).len yq = (V.tgame n).lenR yq + (V.tgame n).lenL yq := rfl
  refine identities_honest prm V n xq yq hℓ hdm hWF hin hm hdesc hT hTlen hx hy hlp
    (by simp only [List.length_take]; omega) (by simp only [List.length_drop]; omega)
    (by simp only [List.length_take]; omega) (by simp only [List.length_drop]; omega)
    hRx hLx hRy hLy hD ?_
  rw [List.take_append_drop, List.take_append_drop]
  exact hacc

/-! ## At every seed -/

variable (L) in
/-- The circuit polynomial of each seed: the arithmetization of its circuit, on the PCP's
variables. -/
noncomputable def circOf (Cc : V.Questions n → Circuit)
    (hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m) (z : V.Questions n) :
    MvPolynomial (Fin L.m) F :=
  rename (Fin.cast (hm z)) (Cc z).finiteArith

variable (L) in
/-- **The hypotheses of the honest PCPs at every seed**: the parameters fit the lengths and the
constraints of the `n`-th game, and each seed's circuit is well formed, has the PCP's inputs, and
describes the output indicator `L*` through the windows at the seed's question pair, within a
time `L*` meets on the honest strings. -/
structure HonestHyp (prm : PolyTimeFun ℕ (Unary × Unary)) (Cc : V.Questions n → Circuit)
    (Tt : ℕ) : Prop where
  hℓ : (prm n).1.length = L.ℓ
  hdm : (prm n).2.length = L.dm
  wf : ∀ z, (Cc z).WellFormed
  inputs : ∀ z, (Cc z).inputs = L.nIn
  desc : ∀ z, (Cc z).DescribesWindows (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r (lstar prm V) n
    (CL.toBits ((V.sampler.cl n .alice).eval z)) (CL.toBits ((V.sampler.cl n .bob).eval z)) Tt
  time : ∀ z aR bR,
    (lstar prm V).Accepts n (CL.toBits ((V.sampler.cl n .alice).eval z))
        (CL.toBits ((V.sampler.cl n .bob).eval z))
        (honestA L V n ((V.sampler.cl n .alice).eval z) ((V.sampler.cl n .bob).eval z) aR bR)
        (honestB L V n ((V.sampler.cl n .bob).eval z) bR) →
      (lstar prm V).AcceptsWithin n (CL.toBits ((V.sampler.cl n .alice).eval z))
        (CL.toBits ((V.sampler.cl n .bob).eval z))
        (honestA L V n ((V.sampler.cl n .alice).eval z) ((V.sampler.cl n .bob).eval z) aR bR)
        (honestB L V n ((V.sampler.cl n .bob).eval z) bR) Tt
  hTlen : 2 ^ L.ℓ + 2 ^ L.oW ≤ Tt
  lenR : ∀ x, (V.tgame n).lenR x ≤ 2 ^ L.ℓ
  lenL : ∀ x, (V.tgame n).lenL x ≤ 2 ^ L.ℓ
  cons : ∀ x y aR bR, aR.length ≤ (V.tgame n).lenR x → bR.length ≤ (V.tgame n).lenR y →
    ((V.tgame n).cons x y aR bR).length * (2 ^ L.ℓ + 2 ^ L.ℓ) + (2 ^ L.ℓ + 2 ^ L.ℓ) ≤ 2 ^ L.dm

variable {V n} in
/-- **At every seed, the honest PCP of an accepted answer pair satisfies the checks
identically.** -/
theorem HonestHyp.identities {prm : PolyTimeFun ℕ (Unary × Unary)} {Cc : V.Questions n → Circuit}
    {Tt : ℕ} (H : HonestHyp L V n prm Cc Tt) (hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m)
    (z : V.Questions n) {a b : BitStr}
    (hacc : (V.tgame n).Accepts ((V.sampler.cl n .alice).eval z) ((V.sampler.cl n .bob).eval z)
      a b) :
    (pairPcp L V n (circOf L V n Cc hm z : MvPolynomial (Fin L.m) F) (Cc z)
      ((V.sampler.cl n .alice).eval z) ((V.sampler.cl n .bob).eval z) a b).Identities
      (circOf L V n Cc hm z) :=
  identities_pairPcp V n prm H.hℓ H.hdm (H.wf z) (H.inputs z) (hm z) _ _ (H.desc z) (H.time z _ _)
    H.hTlen (H.lenR _) (H.lenL _) (H.lenR _) (H.lenL _) (H.cons _ _ _ _ (List.length_take_le _ _) (List.length_take_le _ _)) hacc

end MIPRE.Tailored.AnsRed

end
