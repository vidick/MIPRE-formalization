/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.Honest
public import MIPRE.Tailored.ControlledBits
public import MIPRE.Tailored.Intro.Transport

@[expose] public section

/-!
# The answer bits of the honest answers

The honest strategy of the answer-reduced game data-processes the measurements of a Z-aligned
permutation strategy of the input (slice P4d of `planning/aldous-lyons-track.md`). Its answer bits
are signed permutations, diagonal at the readable bits, because of how they depend on the input
answers (cor:encodings, II:1150):

* a readable bit reads only the readable codewords (`getD_honestBits_readable`), so it is a
  function of the readable input bits (`getD_pairPcp_readable`);
* every bit is, the readable input bits fixed, `F₂`-affine in the linear input bits
  (`ofBool_getD_pairPcp_affine`): the honest PCP is affine in the linear tables, and its values,
  restrictions and the canonical bits of field elements are additive.

`ControlledBits` turns these into the bit properties: `isXBit_diag`, `isZBit_diag` for an isolated
player, who measures the input strategy at its question, and `isXBit_pair`, `isZBit_pair` for the
oracle, who measures the input strategy at both questions of its seed.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.Tailored.Intro MvPolynomial

variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} (d : ℕ) (hM : 2 ^ j ∣ Fintype.card (Fq t ht))

/-! ## The bits of an honest answer -/

theorem getD_honestBits (S : LIDT.CL.Ty) {k : ℕ}
    (G : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht)) (q : LIDT.CL.Question (Fq t ht) (2 ^ j))
    {i : ℕ} (hi : i < k * ncoef j d S * t) :
    (honestBits d hM S G q).getD i false = decide (shoupCoordinateEquiv t ht
      (honestCoef hM G q (i / (ncoef j d S * t)) (i / t % ncoef j d S))
        ⟨i % t, Nat.mod_lt _ (by omega)⟩ = 1) := by
  rw [honestBits, encCws, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem getD_honestBits_of_le (S : LIDT.CL.Ty) {k : ℕ}
    (G : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht)) (q : LIDT.CL.Question (Fq t ht) (2 ^ j))
    {i : ℕ} (hi : k * ncoef j d S * t ≤ i) : (honestBits d hM S G q).getD i false = false :=
  List.getD_eq_default _ _ (by rw [length_honestBits]; exact hi)

theorem honestCoef_add {k : ℕ} (G G' : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht))
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) (c e : ℕ) :
    honestCoef hM (G + G') q c e = honestCoef hM G q c e + honestCoef hM G' q c e := by
  cases q <;> simp only [honestCoef] <;> split_ifs <;>
    simp [lineRestrict, map_add, Polynomial.coeff_add]

/-- **A bit of honest answers is `F₂`-affine in the codewords.** -/
theorem ofBool_getD_honestBits_affine (S : LIDT.CL.Ty) {k : ℕ}
    {G₁₂ G₀ G₁ G₂ : Fin k → MvPolynomial (Fin (2 ^ j)) (Fq t ht)}
    (hG : ∀ c, G₁₂ c + G₀ c = G₁ c + G₂ c) (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) (i : ℕ) :
    (ofBool ((honestBits d hM S G₁₂ q).getD i false) : ZMod 2) +
        ofBool ((honestBits d hM S G₀ q).getD i false) =
      ofBool ((honestBits d hM S G₁ q).getD i false) +
        ofBool ((honestBits d hM S G₂ q).getD i false) := by
  by_cases hi : i < k * ncoef j d S * t
  · simp only [getD_honestBits d hM S _ q hi, ofBool_decide_eq_one]
    have key : ∀ c e, honestCoef hM G₁₂ q c e + honestCoef hM G₀ q c e =
        honestCoef hM G₁ q c e + honestCoef hM G₂ q c e := fun c e => by
      rw [← honestCoef_add, ← honestCoef_add, show G₁₂ + G₀ = G₁ + G₂ from funext hG]
    have := congrArg (fun x => shoupCoordinateEquiv t ht x ⟨i % t, Nat.mod_lt _ (by omega)⟩)
      (key (i / (ncoef j d S * t)) (i / t % ncoef j d S))
    simpa only [map_add, Pi.add_apply] using this
  · simp only [getD_honestBits_of_le d hM S _ q (not_lt.1 hi)]

variable {L : PcpDims} (hLM : L.m ≤ 2 ^ j)

/-- **A readable bit of an honest answer reads only the readable codewords.** -/
theorem getD_honestBits_readable (r : Role) (S : LIDT.CL.Ty) {P P' : Pcp L (Fq t ht)}
    (h : ∀ s : Slot L, s.readable = true → P.slot s = P'.slot s)
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) {i : ℕ} (hi : i < lenR t j d L (r, S)) :
    (honestBits d hM S (ldPolys L hLM P r) q).getD i false =
      (honestBits d hM S (ldPolys L hLM P' r) q).getD i false := by
  have hlen : lenR t j d L (r, S) ≤ (slotsOf L r).length * ncoef j d S * t :=
    (lenR_le_len t j d L (r, S)).trans (len_eq t j d L (r, S)).le
  have hi' : i < (slotsOf L r).length * ncoef j d S * t := lt_of_lt_of_le hi hlen
  have hpos : 0 < ncoef j d S * t := Nat.mul_pos (ncoef_pos j d S) (by omega)
  have hc : i / (ncoef j d S * t) < (rOf L r).length := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    simpa only [lenR, mul_assoc] using hi
  have hc' : i / (ncoef j d S * t) < (slotsOf L r).length := by
    simp only [slotsOf, List.length_append]
    omega
  rw [getD_honestBits d hM S _ q hi', getD_honestBits d hM S _ q hi',
    honestCoef_congr hM hc' hc' (G' := ldPolys L hLM P' r) ?_ q]
  simp only [ldPolys, Pcp.slotPoly, List.get_eq_getElem]
  rw [h _ ((readable_getElem_slotsOf r hc').2 hc)]

variable {ℓV : ℕ} (V : TailoredVerifier ℓV) (n : ℕ)

/-- **The readable bits of an honest answer depend only on the readable input bits.** -/
theorem getD_pairPcp_readable (r : Role) (S : LIDT.CL.Ty) (Tc : MvPolynomial (Fin L.m) (Fq t ht))
    (Cc : Circuit) (xq yq : V.Questions n) {a a' b b' : BitStr}
    (ha : a.take ((V.tgame n).lenR xq) = a'.take ((V.tgame n).lenR xq))
    (hb : b.take ((V.tgame n).lenR yq) = b'.take ((V.tgame n).lenR yq))
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) {i : ℕ} (hi : i < lenR t j d L (r, S)) :
    (honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc xq yq a b) r) q).getD i false =
      (honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc xq yq a' b') r) q).getD i false :=
  getD_honestBits_readable d hM hLM r S (slot_pairPcp_readable V n Tc Cc xq yq ha hb) q hi

theorem take_append_of_length {aR : BitStr} {k : ℕ} (h : aR.length = k) (l : BitStr) :
    (aR ++ l).take k = aR := by
  rw [← h, List.take_left]

/-- The codewords of the honest PCP are `F₂`-affine in the linear input bits. -/
theorem ldPolys_pairPcp_affine (r : Role) (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (Cc : Circuit)
    (xq yq : V.Questions n) {aR bR : BitStr} (haR : aR.length = (V.tgame n).lenR xq)
    (hbR : bR.length = (V.tgame n).lenR yq) {NA NB : ℕ} (u₁ u₂ : Fin NA → 𝔽₂)
    (w₁ w₂ : Fin NB → 𝔽₂) (c : Fin (slotsOf L r).length) :
    ldPolys L hLM (pairPcp L V n Tc Cc xq yq (aR ++ toBits (u₁ + u₂)) (bR ++ toBits (w₁ + w₂)))
          r c +
        ldPolys L hLM (pairPcp L V n Tc Cc xq yq (aR ++ toBits (0 : Fin NA → 𝔽₂))
          (bR ++ toBits (0 : Fin NB → 𝔽₂))) r c =
      ldPolys L hLM (pairPcp L V n Tc Cc xq yq (aR ++ toBits u₁) (bR ++ toBits w₁)) r c +
        ldPolys L hLM (pairPcp L V n Tc Cc xq yq (aR ++ toBits u₂) (bR ++ toBits w₂)) r c := by
  simp only [ldPolys, Pcp.slotPoly, ← map_add]
  congr 2
  by_cases hs : ((slotsOf L r).get c).readable = true
  · have e : ∀ (u : Fin NA → 𝔽₂) (w : Fin NB → 𝔽₂),
        (pairPcp L V n Tc Cc xq yq (aR ++ toBits u) (bR ++ toBits w)).slot ((slotsOf L r).get c) =
          (pairPcp L V n Tc Cc xq yq (aR ++ toBits (0 : Fin NA → 𝔽₂))
            (bR ++ toBits (0 : Fin NB → 𝔽₂))).slot ((slotsOf L r).get c) := fun u w =>
      slot_pairPcp_readable V n Tc Cc xq yq
        (by rw [take_append_of_length haR, take_append_of_length haR])
        (by rw [take_append_of_length hbR, take_append_of_length hbR]) _ hs
    rw [e (u₁ + u₂) (w₁ + w₂), e u₁ w₁, e u₂ w₂]
  · exact slot_pairPcp_affine V n Tc Cc xq yq haR hbR u₁ u₂ w₁ w₂ _ (by simpa using hs)

/-- **Every bit of an honest answer is `F₂`-affine in the linear input bits**, the readable ones
fixed. -/
theorem ofBool_getD_pairPcp_affine (r : Role) (S : LIDT.CL.Ty)
    (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (Cc : Circuit) (xq yq : V.Questions n)
    {aR bR : BitStr} (haR : aR.length = (V.tgame n).lenR xq)
    (hbR : bR.length = (V.tgame n).lenR yq) {NA NB : ℕ} (u₁ u₂ : Fin NA → 𝔽₂)
    (w₁ w₂ : Fin NB → 𝔽₂) (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) (i : ℕ) :
    (ofBool ((honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc xq yq
        (aR ++ toBits (u₁ + u₂)) (bR ++ toBits (w₁ + w₂))) r) q).getD i false) : ZMod 2) +
        ofBool ((honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc xq yq
          (aR ++ toBits (0 : Fin NA → 𝔽₂)) (bR ++ toBits (0 : Fin NB → 𝔽₂))) r) q).getD i
          false) =
      ofBool ((honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc xq yq
          (aR ++ toBits u₁) (bR ++ toBits w₁)) r) q).getD i false) +
        ofBool ((honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc xq yq
          (aR ++ toBits u₂) (bR ++ toBits w₂)) r) q).getD i false) :=
  ofBool_getD_honestBits_affine d hM S
    (ldPolys_pairPcp_affine hLM V n r Tc Cc xq yq haR hbR u₁ u₂ w₁ w₂) q i

/-! ## Reading an answer through its readable and linear bits -/

theorem decide_ofBool_eq_one (b : Bool) : decide ((ofBool b : ZMod 2) = 1) = b := by
  cases b <;> rfl

/-- The first `R` bits of an answer of length at least `R`. -/
theorem take_eq_ofFn {a : BitStr} {R : ℕ} (h : R ≤ a.length) :
    a.take R = (List.ofFn (fun m : Fin R => a.getD m false)).take R := by
  rw [List.take_of_length_le (List.length_ofFn (f := fun m : Fin R => a.getD m false)).le]
  apply List.ext_getElem (by rw [List.length_take, List.length_ofFn]; omega)
  intro m h1 h2
  rw [List.getElem_take, List.getElem_ofFn,
    List.getD_eq_getElem _ _ (by rw [List.length_take] at h1; omega)]

/-- An answer of length `R + N` is its first `R` bits followed by the rest. -/
theorem eq_ofFn_append_toBits {a : BitStr} {R N : ℕ} (h : a.length = R + N) :
    a = List.ofFn (fun m : Fin R => a.getD m false) ++
      toBits (fun m : Fin N => (ofBool (a.getD (R + m) false) : 𝔽₂)) := by
  apply List.ext_getElem (by simp [h, toBits])
  intro i h1 h2
  by_cases hi : i < R
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_ofFn]
    show a[i] = a.getD i false
    rw [List.getD_eq_getElem _ _ h1]
  · rw [List.getElem_append_right (by simpa using hi)]
    simp only [toBits, List.getElem_ofFn, List.length_ofFn]
    simp only [show R + (i - R) = i by omega, List.getD_eq_getElem _ _ h1]
    cases a[i] <;> rfl

/-! ## The bits at an isolated player -/

variable {X : Type*} [Fintype X] {G : TailoredGame X}

/-- The readable bits of an answer at a question. -/
def rdBits (lR : ℕ) (a : BitStr) : Fin lR → Bool := fun m => a.getD m false

/-- The linear bits of an answer at a question. -/
def lnBits (lR lL : ℕ) (a : BitStr) : Fin lL → Bool := fun m => a.getD (lR + m) false

variable (Cc : V.Questions n → Circuit) (hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m)

/-- **The bits of an isolated player's honest answer are X-bits** of the input strategy's
measurement at its question: for each value of its readable bits, affine in its linear bits. -/
theorem isXBit_diag (SV : PermStrategy (V.tgame n).doubled) (p : Bool × V.Questions n)
    (r : Role) (S : LIDT.CL.Ty) (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (Cc₀ : Circuit)
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) (i : ℕ) :
    IsXBit (SV.toSync.P.M p) fun a => (honestBits d hM S (ldPolys L hLM
      (pairPcp L V n Tc Cc₀ p.2 p.2 a.1 a.1) r) q).getD i false := by
  set lR := (V.tgame n).lenR p.2
  set lL := (V.tgame n).lenL p.2
  refine isXBit_of_controlledAffine (SV.toSync.isPVMIn p) (fun a => rdBits lR a.1)
    (fun m => (SV.toSync_bit p m).2 m.2) (fun a => lnBits lR lL a.1)
    (fun m => (SV.toSync_bit p (lR + m)).1)
    (fun k u => ofBool ((honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc₀ p.2 p.2
      (List.ofFn k ++ toBits u) (List.ofFn k ++ toBits u)) r) q).getD i false))
    (fun k u v => by
      have := ofBool_getD_pairPcp_affine d hM hLM V n r S Tc Cc₀ p.2 p.2
        (aR := List.ofFn k) (bR := List.ofFn k) (by simp [lR]) (by simp [lR]) u v u v q i
      exact this) _ fun a ha => ?_
  have hlen := SV.toSync_len p a ha
  have e := eq_ofFn_append_toBits (R := lR) (N := lL) hlen
  exact congrArg (fun l : BitStr => (ofBool ((honestBits d hM S (ldPolys L hLM
    (pairPcp L V n Tc Cc₀ p.2 p.2 l l) r) q).getD i false) : ZMod 2)) e

/-- **The readable bits of an isolated player's honest answer are Z-bits** of the input strategy's
measurement at its question: functions of its readable bits. -/
theorem isZBit_diag (SV : PermStrategy (V.tgame n).doubled) (p : Bool × V.Questions n)
    (r : Role) (S : LIDT.CL.Ty) (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (Cc₀ : Circuit)
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) {i : ℕ} (hi : i < lenR t j d L (r, S)) :
    IsZBit (SV.toSync.P.M p) fun a => (honestBits d hM S (ldPolys L hLM
      (pairPcp L V n Tc Cc₀ p.2 p.2 a.1 a.1) r) q).getD i false := by
  set lR := (V.tgame n).lenR p.2
  refine isZBit_of_readable (SV.toSync.isPVMIn p) (fun a => rdBits lR a.1)
    (fun m => (SV.toSync_bit p m).2 m.2)
    (fun k => (honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc₀ p.2 p.2
      (List.ofFn k) (List.ofFn k)) r) q).getD i false) _ fun a ha => ?_
  have hlen := SV.toSync_len p a ha
  have ht := take_eq_ofFn (a := a.1) (R := lR) (by rw [hlen]; exact Nat.le_add_right _ _)
  exact getD_pairPcp_readable d hM hLM V n r S Tc Cc₀ p.2 p.2 ht ht q hi

/-! ## The bits at the oracle -/

/-- The measurement of an oracle at a seed: the input strategy's measurements at both questions
of the seed, jointly. -/
def jointM (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n) :
    Verifier.Answers (V.tgame n).maxLen × Verifier.Answers (V.tgame n).maxLen →
      Matrix (Fin SV.toSync.d) (Fin SV.toSync.d) ℂ :=
  fun ab => SV.toSync.P.M (false, qA V n z) ab.1 * SV.toSync.P.M (true, qB V n z) ab.2

theorem doubled_mu_pos_seed (z : V.Questions n) :
    0 < (V.tgame n).toGame.doubled.μ (false, qA V n z) (true, qB V n z) := by
  rw [Game.doubled_μ]
  simp only [and_self, ite_true]
  show 0 < V.sampler.dist n _ _
  have hcard : (0 : ℝ) < Fintype.card (V.Questions n) := by exact_mod_cast Fintype.card_pos
  refine div_pos ?_ hcard
  have hz : z ∈ Finset.univ.filter fun w => (V.sampler.cl n .alice).eval w = qA V n z ∧
      (V.sampler.cl n .bob).eval w = qB V n z :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl, rfl⟩
  exact_mod_cast Finset.card_pos.mpr ⟨z, hz⟩

theorem isPVMIn_jointM (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n) :
    IsPVMIn (jointM V n SV z) :=
  (SV.toSync.isPVMIn _).prod_of_commute (SV.toSync.isPVMIn _) fun a b =>
    SV.isPCC_toSync _ _ (doubled_mu_pos_seed V n z) a b

theorem jointM_ne_zero {SV : PermStrategy (V.tgame n).doubled} {z : V.Questions n}
    {ab : Verifier.Answers (V.tgame n).maxLen × Verifier.Answers (V.tgame n).maxLen}
    (h : jointM V n SV z ab ≠ 0) :
    SV.toSync.P.M (false, qA V n z) ab.1 ≠ 0 ∧ SV.toSync.P.M (true, qB V n z) ab.2 ≠ 0 := by
  refine ⟨fun h1 => h ?_, fun h2 => h ?_⟩
  · simp [jointM, h1]
  · simp [jointM, h2]

theorem isZBit_jointM_fst (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n)
    {g : Verifier.Answers (V.tgame n).maxLen → Bool}
    (hg : IsZBit (SV.toSync.P.M (false, qA V n z)) g) :
    IsZBit (jointM V n SV z) fun ab => g ab.1 := by
  have e : bitObs (jointM V n SV z) (fun ab => g ab.1) =
      bitObs (SV.toSync.P.M (false, qA V n z)) g :=
    bitObs_mul_fst _ _ (SV.toSync.isPVMIn _).sum_eq_one g
  unfold IsZBit at *
  rw [e]
  exact hg

theorem isZBit_jointM_snd (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n)
    {g : Verifier.Answers (V.tgame n).maxLen → Bool}
    (hg : IsZBit (SV.toSync.P.M (true, qB V n z)) g) :
    IsZBit (jointM V n SV z) fun ab => g ab.2 := by
  have e : bitObs (jointM V n SV z) (fun ab => g ab.2) =
      bitObs (SV.toSync.P.M (true, qB V n z)) g :=
    bitObs_mul_snd _ _ (SV.toSync.isPVMIn _).sum_eq_one g
  unfold IsZBit at *
  rw [e]
  exact hg

theorem isXBit_jointM_fst (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n)
    {g : Verifier.Answers (V.tgame n).maxLen → Bool}
    (hg : IsXBit (SV.toSync.P.M (false, qA V n z)) g) :
    IsXBit (jointM V n SV z) fun ab => g ab.1 := by
  have e : bitObs (jointM V n SV z) (fun ab => g ab.1) =
      bitObs (SV.toSync.P.M (false, qA V n z)) g :=
    bitObs_mul_fst _ _ (SV.toSync.isPVMIn _).sum_eq_one g
  unfold IsXBit at *
  rw [e]
  exact hg

theorem isXBit_jointM_snd (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n)
    {g : Verifier.Answers (V.tgame n).maxLen → Bool}
    (hg : IsXBit (SV.toSync.P.M (true, qB V n z)) g) :
    IsXBit (jointM V n SV z) fun ab => g ab.2 := by
  have e : bitObs (jointM V n SV z) (fun ab => g ab.2) =
      bitObs (SV.toSync.P.M (true, qB V n z)) g :=
    bitObs_mul_snd _ _ (SV.toSync.isPVMIn _).sum_eq_one g
  unfold IsXBit at *
  rw [e]
  exact hg

/-- **The bits of the oracle's honest answer are X-bits** of its joint measurement: for each value
of the readable bits of both input answers, affine in their linear bits. -/
theorem isXBit_pair (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n)
    (S : LIDT.CL.Ty) (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (Cc₀ : Circuit)
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) (i : ℕ) :
    IsXBit (jointM V n SV z) fun ab => (honestBits d hM S (ldPolys L hLM
      (pairPcp L V n Tc Cc₀ (qA V n z) (qB V n z) ab.1.1 ab.2.1) .oracle) q).getD i false := by
  set lRA := (V.tgame n).lenR (qA V n z)
  set lLA := (V.tgame n).lenL (qA V n z)
  set lRB := (V.tgame n).lenR (qB V n z)
  set lLB := (V.tgame n).lenL (qB V n z)
  refine isXBit_of_controlledAffine (isPVMIn_jointM V n SV z)
    (fun ab => Fin.append (rdBits lRA ab.1.1) (rdBits lRB ab.2.1)) (fun m => ?_)
    (fun ab => Sum.elim (lnBits lRA lLA ab.1.1) (lnBits lRB lLB ab.2.1)) (fun m => ?_)
    (fun k v => ofBool ((honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc₀ (qA V n z)
      (qB V n z) (List.ofFn (fun m => k (Fin.castAdd lRB m)) ++ toBits (fun m => v (.inl m)))
      (List.ofFn (fun m => k (Fin.natAdd lRA m)) ++ toBits (fun m => v (.inr m)))) .oracle)
        q).getD i false))
    (fun k v w => ?_) _ fun ab hab => ?_
  · refine Fin.addCases (fun m => ?_) (fun m => ?_) m
    · simp only [Fin.append_left]
      exact isZBit_jointM_fst V n SV z ((SV.toSync_bit _ m).2 m.2)
    · simp only [Fin.append_right]
      exact isZBit_jointM_snd V n SV z ((SV.toSync_bit _ m).2 m.2)
  · rcases m with m | m
    · exact isXBit_jointM_fst V n SV z (SV.toSync_bit _ (lRA + m)).1
    · exact isXBit_jointM_snd V n SV z (SV.toSync_bit _ (lRB + m)).1
  · exact ofBool_getD_pairPcp_affine d hM hLM V n .oracle S Tc Cc₀ (qA V n z) (qB V n z)
      (by simp [lRA]) (by simp [lRB]) (fun m => v (.inl m)) (fun m => w (.inl m))
      (fun m => v (.inr m)) (fun m => w (.inr m)) q i
  · obtain ⟨ha, hb⟩ := jointM_ne_zero V n hab
    have hA := eq_ofFn_append_toBits (R := lRA) (N := lLA) (SV.toSync_len _ _ ha)
    have hB := eq_ofFn_append_toBits (R := lRB) (N := lLB) (SV.toSync_len _ _ hb)
    have e := congrArg₂ (fun l l' : BitStr => (ofBool ((honestBits d hM S (ldPolys L hLM
      (pairPcp L V n Tc Cc₀ (qA V n z) (qB V n z) l l') .oracle) q).getD i false) : ZMod 2)) hA hB
    simpa only [rdBits, lnBits, Fin.append_left, Fin.append_right, Sum.elim_inl, Sum.elim_inr]
      using e

/-- **The readable bits of the oracle's honest answer are Z-bits** of its joint measurement:
functions of the readable bits of both input answers. -/
theorem isZBit_pair (SV : PermStrategy (V.tgame n).doubled) (z : V.Questions n)
    (S : LIDT.CL.Ty) (Tc : MvPolynomial (Fin L.m) (Fq t ht)) (Cc₀ : Circuit)
    (q : LIDT.CL.Question (Fq t ht) (2 ^ j)) {i : ℕ} (hi : i < lenR t j d L (.oracle, S)) :
    IsZBit (jointM V n SV z) fun ab => (honestBits d hM S (ldPolys L hLM
      (pairPcp L V n Tc Cc₀ (qA V n z) (qB V n z) ab.1.1 ab.2.1) .oracle) q).getD i false := by
  set lRA := (V.tgame n).lenR (qA V n z)
  set lRB := (V.tgame n).lenR (qB V n z)
  refine isZBit_of_readable (isPVMIn_jointM V n SV z)
    (fun ab => Fin.append (rdBits lRA ab.1.1) (rdBits lRB ab.2.1)) (fun m => ?_)
    (fun k => (honestBits d hM S (ldPolys L hLM (pairPcp L V n Tc Cc₀ (qA V n z) (qB V n z)
      (List.ofFn (fun m => k (Fin.castAdd lRB m))) (List.ofFn (fun m => k (Fin.natAdd lRA m))))
      .oracle) q).getD i false) _ fun ab hab => ?_
  · refine Fin.addCases (fun m => ?_) (fun m => ?_) m
    · simp only [Fin.append_left]
      exact isZBit_jointM_fst V n SV z ((SV.toSync_bit _ m).2 m.2)
    · simp only [Fin.append_right]
      exact isZBit_jointM_snd V n SV z ((SV.toSync_bit _ m).2 m.2)
  · obtain ⟨ha, hb⟩ := jointM_ne_zero V n hab
    have hlA := SV.toSync_len _ _ ha
    have hlB := SV.toSync_len _ _ hb
    have e := getD_pairPcp_readable d hM hLM V n .oracle S Tc Cc₀ _ _
      (take_eq_ofFn (a := ab.1.1) (R := lRA) (by rw [hlA]; exact Nat.le_add_right _ _))
      (take_eq_ofFn (a := ab.2.1) (R := lRB) (by rw [hlB]; exact Nat.le_add_right _ _)) q hi
    simpa only [Fin.append_left, Fin.append_right, rdBits] using e

end MIPRE.Tailored.AnsRed.Typed

end
