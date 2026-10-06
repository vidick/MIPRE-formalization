/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.RegCons
public import MIPRE.Tailored.Intro.SourceCons
public import MIPRE.Foundations.Introspection.BoundedAnswerCoding
public import MIPRE.Foundations.Introspection.AuxiliaryQuotientChecks

@[expose] public section

/-!
# The auxiliary answers, read off the padded layout

In the padded layout of the tailored introspection verifier (`MIPRE.Tailored.Intro.enc`) an
auxiliary answer is a list of windows: the register `y` at `0`; at Introspect and Sample the
input's readable answer bits at `Q` and its linear ones at `Q + R`; at Read the same readable
bits at `Q`, the dual `y'` at `Q + R` and the linear bits at `2Q + R`; at Hide the dual `y'` at
`Q` and the tail `x` at `2Q`. This file reads the parsed answer of the introspection verifier's
kernel off those windows (`parsed`), and writes the comparisons of its auxiliary checks between
two such answers as linear constraints:

* `srcEqCons`, `srcEqCons_iff`: two input answers are equal: their splits and readable bits
  agree (a readable condition) and their linear bits agree (bit by bit);
* `regEqCons_iff`: two registers in windows are equal;
* `sampleCons`, `readCons`, `hideReadCons`, `hideNextCons`, `sourceCons`: the clauses of the
  directed checks (`AuxiliaryQuotient.directed`), each with its `_iff`;
* `sameCons`: consistency of two answers at one label;
* `swapCon`: a constraint on `(b, a)` as one on `(a, b)`, for the other orientation;
* `auxPair`, `auxPair_iff`: all of it at an ordered pair of auxiliary labels, with a readable
  condition `G` on each register: the constraints hold exactly when `G` holds at both registers,
  the parsed answers agree when the labels do, and the directed checks accept both ways.

The input's split of its answer at a register, `sR` and `sL`, and the source game's constraints
are parameters, as are lists of generators of the kernels of the hiding stages' linear maps
(`KerGens`); the instance supplies them.
-/

namespace MIPRE.Tailored.Intro

open Cost CL MIPRE.Introspection

/-! ## Windows -/

/-- The window of length `m` at offset `o`. -/
def win (a : BitStr) (o m : ℕ) : BitStr := (a.drop o).take m

theorem length_win {a : BitStr} {o m : ℕ} (h : o + m ≤ a.length) : (win a o m).length = m := by
  simp [win]; omega

/-- A window inside a prefix is the window of the whole. -/
theorem win_take {a : BitStr} {o m n : ℕ} (h : o + m ≤ n) : win (a.take n) o m = win a o m := by
  simp only [win, List.drop_take, List.take_take]
  congr 1; omega

variable (Q : ℕ)

/-- The register in the window of length `Q` at offset `o`. -/
def reg (a : BitStr) (o : ℕ) : Fin Q → 𝔽₂ := ofBits Q (win a o Q)

variable {Q}

theorem toBits_reg {a : BitStr} {o : ℕ} (h : o + Q ≤ a.length) : toBits (reg Q a o) = win a o Q :=
  toBits_ofBits (length_win h)

theorem reg_eq_iff {a b : BitStr} {oa ob : ℕ} (ha : oa + Q ≤ a.length) (hb : ob + Q ≤ b.length) :
    reg Q a oa = reg Q b ob ↔ win a oa Q = win b ob Q := by
  constructor
  · intro h
    rw [← toBits_reg ha, ← toBits_reg hb, h]
  · intro h
    simp only [reg, h]

/-! ## Equality of two windows of the two answers -/

/-- **Two registers in windows are equal exactly when the window constraints hold.** -/
theorem regEqCons_iff {la lb oa ob : ℕ} {a b : BitStr} (ha : a.length = la) (hb : b.length = lb)
    (hoa : oa + Q ≤ la) (hob : ob + Q ≤ lb) :
    (∀ c ∈ eqCons la lb oa ob Q, Satisfies c (a ++ b ++ [true])) ↔ reg Q a oa = reg Q b ob := by
  rw [eqCons_iff ha hb hoa hob, reg_eq_iff (by omega) (by omega)]
  rfl

/-- The constraints that two input answers are equal: the splits and the readable bits agree,
a readable condition, and the linear bits agree bit by bit. The readable bits are windows of the
readable parts `aR`, `bR`; the linear bits windows of the answers. -/
def srcEqCons (la lb oRa oLa oRb oLb sRa sLa sRb sLb : ℕ) (aR bR : BitStr) : List BitStr :=
  guardCons (decide (sRa = sRb ∧ sLa = sLb ∧ win aR oRa sRa = win bR oRb sRb)) (la + lb) ++
    eqCons la lb oLa oLb sLa

theorem forall_mem_append {l₁ l₂ : List BitStr} {p : BitStr → Prop} :
    (∀ c ∈ l₁ ++ l₂, p c) ↔ (∀ c ∈ l₁, p c) ∧ ∀ c ∈ l₂, p c := by
  simp only [List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

/-- **The input-answer equality constraints**, read: with the readable windows inside the
readable parts, they hold exactly when the splits agree and the two input answers, the readable
window followed by the linear window, are equal. -/
theorem srcEqCons_iff {la lb lRa lRb oRa oLa oRb oLb sRa sLa sRb sLb : ℕ} {a b : BitStr}
    (ha : a.length = la) (hb : b.length = lb) (hRa : oRa + sRa ≤ lRa) (hRb : oRb + sRb ≤ lRb)
    (hla : lRa ≤ la) (hlb : lRb ≤ lb) (hLa : oLa + sLa ≤ la) (hLb : oLb + sLa ≤ lb) :
    (∀ c ∈ srcEqCons la lb oRa oLa oRb oLb sRa sLa sRb sLb (a.take lRa) (b.take lRb),
        Satisfies c (a ++ b ++ [true])) ↔
      sRa = sRb ∧ sLa = sLb ∧
        win a oRa sRa ++ win a oLa sLa = win b oRb sRb ++ win b oLb sLb := by
  rw [srcEqCons, forall_mem_append, guardCons_iff, eqCons_iff ha hb hLa hLb, decide_eq_true_iff,
    win_take hRa, win_take hRb]
  constructor
  · rintro ⟨⟨rfl, rfl, h1⟩, h2⟩
    exact ⟨rfl, rfl, by rw [h1]; exact congrArg _ h2⟩
  · rintro ⟨rfl, rfl, h⟩
    have hl : (win a oRa sRa).length = (win b oRb sRa).length := by
      rw [length_win (by omega), length_win (by omega)]
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact ⟨⟨rfl, rfl, h1⟩, h2⟩

/-! ## The parsed auxiliary answer -/

variable (Q R : ℕ) (sR sL : AuxType 7 × Bool → BitStr → ℕ)

/-- The number of readable bits of an auxiliary label. -/
def auxLenR : AuxType 7 → ℕ
  | .hide _ => Q
  | _ => Q + R

/-- The number of bits of an auxiliary label. -/
def auxLen : AuxType 7 → ℕ
  | .introspect => Q + 2 * R
  | .sample => Q + 2 * R
  | .read => 2 * Q + 2 * R
  | .hide _ => 3 * Q

/-- The offset of the input's linear answer bits. -/
def srcOffL : AuxType 7 → ℕ
  | .read => 2 * Q + R
  | _ => Q + R

/-- The input's answer carried by an auxiliary answer: the readable window at `Q` and the linear
window at `srcOffL`, of the lengths the input gives at the register `y`. -/
def srcAns (t : AuxType 7 × Bool) (a : BitStr) : BitStr :=
  win a Q (sR t (win a 0 Q)) ++ win a (srcOffL Q R t.1) (sL t (win a 0 Q))

/-- The kernel's parsed answer read off the windows of an auxiliary answer. -/
def parsed {PA : Type*} : AuxType 7 × Bool → BitStr →
    ParsedAnswer (Fin Q → 𝔽₂) (Verifier.Answers R) PA
  | (.introspect, w), a =>
      .pair (reg Q a 0) (AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.introspect, w) a))
  | (.sample, w), a =>
      .pair (reg Q a 0) (AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.sample, w) a))
  | (.read, w), a => .read (reg Q a 0) (reg Q a (Q + R))
      (AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.read, w) a))
  | (.hide _, _), a => .hide (reg Q a 0) (reg Q a Q) (reg Q a (2 * Q))

/-- The readable condition on one auxiliary answer: the input's answer fits the original
cutoff. -/
def srcFits (t : AuxType 7 × Bool) (y : BitStr) : Prop :=
  match t.1 with
  | .hide _ => True
  | _ => sR t y + sL t y ≤ R

variable {Q R sR sL}

theorem length_srcAns {t : AuxType 7 × Bool} {a : BitStr} (ha : a.length = auxLen Q R t.1)
    (hf : srcFits R sR sL t (win a 0 Q)) (ht : ∀ k, t.1 ≠ .hide k) :
    (srcAns Q R sR sL t a).length = sR t (win a 0 Q) + sL t (win a 0 Q) := by
  obtain ⟨t, w⟩ := t
  cases t with
  | hide k => exact absurd rfl (ht k)
  | introspect | sample | read =>
    simp only [srcFits] at hf
    simp only [auxLen] at ha
    simp only [srcAns, srcOffL, List.length_append]
    rw [length_win (by omega), length_win (by omega)]

theorem bounded_srcAns_val {t : AuxType 7 × Bool} {a : BitStr} (ha : a.length = auxLen Q R t.1)
    (hf : srcFits R sR sL t (win a 0 Q)) (ht : ∀ k, t.1 ≠ .hide k) :
    (AuxiliaryAnswer.bounded R (srcAns Q R sR sL t a)).val = srcAns Q R sR sL t a := by
  apply AuxiliaryAnswer.bounded_val
  rw [length_srcAns ha hf ht]
  obtain ⟨t, w⟩ := t
  cases t with
  | hide k => exact absurd rfl (ht k)
  | introspect | sample | read => exact hf

/-! ## The comparisons of the auxiliary checks -/

variable (Q R sR sL) (L : Bool → CL.CLFun 𝔽₂ (Fin Q) 7)

/-- The sampling comparison between Introspect `w` (`a`) and Sample `w` (`b`): `y = L_w(z)`, a
readable condition, and equal input answers. -/
noncomputable def sampleCons (w : Bool) (aR bR : BitStr) : List BitStr :=
  guardCons (decide (ofBits Q (win aR 0 Q) = (L w).eval (ofBits Q (win bR 0 Q))))
      (auxLen Q R .introspect + auxLen Q R .sample) ++
    srcEqCons (auxLen Q R .introspect) (auxLen Q R .sample) Q (Q + R) Q (Q + R)
      (sR (.introspect, w) (win aR 0 Q)) (sL (.introspect, w) (win aR 0 Q))
      (sR (.sample, w) (win bR 0 Q)) (sL (.sample, w) (win bR 0 Q)) aR bR

/-- The reading comparison between Introspect `w` (`a`) and Read `w` (`b`): equal registers, a
readable condition, and equal input answers. -/
def readCons (w : Bool) (aR bR : BitStr) : List BitStr :=
  guardCons (decide (win aR 0 Q = win bR 0 Q)) (auxLen Q R .introspect + auxLen Q R .read) ++
    srcEqCons (auxLen Q R .introspect) (auxLen Q R .read) Q (Q + R) Q (2 * Q + R)
      (sR (.introspect, w) (win aR 0 Q)) (sL (.introspect, w) (win aR 0 Q))
      (sR (.read, w) (win bR 0 Q)) (sL (.read, w) (win bR 0 Q)) aR bR

/-- The comparison between the last Hide `w` (`a`) and Read `w` (`b`): equal prefixes of the
registers, a readable condition, and equal duals. -/
noncomputable def hideReadCons (w : Bool) (aR bR : BitStr) : List BitStr :=
  guardCons (decide ((L w).outputPrefix 6 (ofBits Q (win aR 0 Q)) =
      (L w).outputPrefix 6 (ofBits Q (win bR 0 Q))))
      (auxLen Q R (.hide 0) + auxLen Q R .read) ++
    eqCons (auxLen Q R (.hide 0)) (auxLen Q R .read) Q (Q + R) Q

/-- Lists of vectors spanning the kernel of every register-local linear map. -/
def KerGens (kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂)) : Prop :=
  ∀ S (M : CL.RegLinear 𝔽₂ S), (∀ g ∈ kg S M, M g = 0) ∧
    ∀ z, M z = 0 → z ∈ Submodule.span 𝔽₂ {g | g ∈ kg S M}

/-- The comparison between Hide level `k + 1` (`a`) and the next level (`b`), both `w`: equal
prefixes, a readable condition; the duals equal on the prefix register of `b`, the tails equal
off the next one; and the dual readout of `b` at its stage equal at `b`'s dual and `a`'s tail. -/
noncomputable def hideNextCons (kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂))
    (w : Bool) (k : ℕ) (aR bR : BitStr) : List BitStr :=
  guardCons (decide ((L w).outputPrefix k (ofBits Q (win aR 0 Q)) =
      (L w).outputPrefix k (ofBits Q (win bR 0 Q)))) (3 * Q + 3 * Q) ++
    projEqCons (3 * Q) (3 * Q) Q Q
      (CLChecks.prefixRegister (L w) (k + 1) (ofBits Q (win bR 0 Q))) ++
    projEqCons (3 * Q) (3 * Q) (2 * Q) (2 * Q)
      (CLChecks.prefixRegister (L w) (k + 2) (ofBits Q (win bR 0 Q)))ᶜ ++
    dualCons (3 * Q) (3 * Q) (2 * Q) Q ((L w).factorOfPrefix (k + 1) (ofBits Q (win bR 0 Q)))
      (kg _ (CLChecks.stageLinear (L w) (k + 1) (ofBits Q (win bR 0 Q))))

variable {Q R sR sL L}

theorem bounded_srcAns_eq_iff {t u : AuxType 7 × Bool} {a b : BitStr}
    (ha : a.length = auxLen Q R t.1) (hb : b.length = auxLen Q R u.1)
    (hfa : srcFits R sR sL t (win a 0 Q)) (hfb : srcFits R sR sL u (win b 0 Q))
    (hta : ∀ k, t.1 ≠ .hide k) (htb : ∀ k, u.1 ≠ .hide k) :
    AuxiliaryAnswer.bounded R (srcAns Q R sR sL t a) =
        AuxiliaryAnswer.bounded R (srcAns Q R sR sL u b) ↔
      srcAns Q R sR sL t a = srcAns Q R sR sL u b := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [bounded_srcAns_val ha hfa hta, bounded_srcAns_val hb hfb htb] at this
  · intro h
    exact Subtype.ext (by rw [bounded_srcAns_val ha hfa hta, bounded_srcAns_val hb hfb htb, h])

/-- **The sampling comparison as constraints.** The input's split at a Sample answer is that
at the Introspect answer of the register it samples (`hsplit`). -/
theorem sampleCons_iff {w : Bool} {a b : BitStr} (ha : a.length = auxLen Q R .introspect)
    (hb : b.length = auxLen Q R .sample)
    (hfa : srcFits R sR sL (.introspect, w) (win a 0 Q))
    (hfb : srcFits R sR sL (.sample, w) (win b 0 Q))
    (hsplit : ∀ y z : BitStr, ofBits Q y = (L w).eval (ofBits Q z) →
      sR (.introspect, w) y = sR (.sample, w) z ∧ sL (.introspect, w) y = sL (.sample, w) z) :
    (∀ c ∈ sampleCons Q R sR sL L w (a.take (Q + R)) (b.take (Q + R)),
        Satisfies c (a ++ b ++ [true])) ↔
      CLChecks.sampling (L w)
        (reg Q a 0, AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.introspect, w) a))
        (reg Q b 0, AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.sample, w) b)) := by
  simp only [srcFits] at hfa hfb
  simp only [auxLen] at ha hb
  rw [CLChecks.sampling, bounded_srcAns_eq_iff (by simpa [auxLen] using ha)
    (by simpa [auxLen] using hb) (by simpa [srcFits] using hfa) (by simpa [srcFits] using hfb)
    (by simp) (by simp)]
  rw [sampleCons, forall_mem_append, guardCons_iff, decide_eq_true_iff,
    srcEqCons_iff (by simpa [auxLen] using ha) (by simpa [auxLen] using hb)
      (by rw [win_take (by omega)]; omega) (by rw [win_take (by omega)]; omega)
      (by simp [auxLen]; omega) (by simp [auxLen]; omega)
      (by rw [win_take (by omega)]; simp [auxLen]; omega)
      (by rw [win_take (by omega)]; simp [auxLen]; omega)]
  simp only [win_take (show 0 + Q ≤ Q + R by omega), srcAns, srcOffL, reg]
  constructor
  · rintro ⟨h1, -, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨e1, e2⟩ := hsplit _ _ h1
    exact ⟨h1, e1, e2, h2⟩

/-- **The reading comparison as constraints.** The input's split at a Read answer is that at
an Introspect answer of the same register (`hsplit`). -/
theorem readCons_iff {w : Bool} {a b : BitStr} (ha : a.length = auxLen Q R .introspect)
    (hb : b.length = auxLen Q R .read)
    (hfa : srcFits R sR sL (.introspect, w) (win a 0 Q))
    (hfb : srcFits R sR sL (.read, w) (win b 0 Q))
    (hsplit : ∀ y : BitStr, sR (.introspect, w) y = sR (.read, w) y ∧
      sL (.introspect, w) y = sL (.read, w) y) :
    (∀ c ∈ readCons Q R sR sL w (a.take (Q + R)) (b.take (Q + R)),
        Satisfies c (a ++ b ++ [true])) ↔
      CLChecks.reading
        (reg Q a 0, AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.introspect, w) a))
        (reg Q b 0, reg Q b (Q + R),
          AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.read, w) b)) := by
  simp only [srcFits] at hfa hfb
  simp only [auxLen] at ha hb
  rw [CLChecks.reading, bounded_srcAns_eq_iff (by simpa [auxLen] using ha)
    (by simpa [auxLen] using hb) (by simpa [srcFits] using hfa) (by simpa [srcFits] using hfb)
    (by simp) (by simp), reg_eq_iff (by omega) (by omega)]
  rw [readCons, forall_mem_append, guardCons_iff, decide_eq_true_iff,
    srcEqCons_iff (by simpa [auxLen] using ha) (by simpa [auxLen] using hb)
      (by rw [win_take (by omega)]; omega) (by rw [win_take (by omega)]; omega)
      (by simp [auxLen]; omega) (by simp [auxLen]; omega)
      (by rw [win_take (by omega)]; simp [auxLen]; omega)
      (by rw [win_take (by omega)]; simp [auxLen]; omega)]
  simp only [win_take (show 0 + Q ≤ Q + R by omega), srcAns, srcOffL]
  constructor
  · rintro ⟨h1, -, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨e1, e2⟩ := hsplit (win a 0 Q)
    rw [← h1]
    rw [← h1] at h2
    exact ⟨rfl, e1, e2, h2⟩

/-- **The comparison of the last Hide with Read as constraints.** -/
theorem hideReadCons_iff {w : Bool} {k : Fin 7} {a b : BitStr}
    (ha : a.length = auxLen Q R (.hide k)) (hb : b.length = auxLen Q R .read)
    (α : Verifier.Answers R) :
    (∀ c ∈ hideReadCons Q R L w (a.take Q) (b.take (Q + R)),
        Satisfies c (a ++ b ++ [true])) ↔
      CLChecks.hidingRead (L w) (reg Q a 0, reg Q a Q, reg Q a (2 * Q))
        (reg Q b 0, reg Q b (Q + R), α) := by
  simp only [auxLen] at ha hb
  rw [hideReadCons, forall_mem_append, guardCons_iff, decide_eq_true_iff,
    regEqCons_iff (by simpa [auxLen] using ha) (by simpa [auxLen] using hb)
      (by simp [auxLen]; omega) (by simp [auxLen]; omega)]
  simp only [win_take (show 0 + Q ≤ Q by omega), win_take (show 0 + Q ≤ Q + R by omega),
    CLChecks.hidingRead, reg]

/-- **The comparison of consecutive Hide levels as constraints.** -/
theorem hideNextCons_iff {kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂)}
    (hkg : KerGens Q kg) {w : Bool} {k : ℕ} {a b : BitStr} (ha : a.length = 3 * Q)
    (hb : b.length = 3 * Q) :
    (∀ c ∈ hideNextCons Q L kg w k (a.take Q) (b.take Q), Satisfies c (a ++ b ++ [true])) ↔
      AuxiliaryQuotient.hidingNext (L w) k (reg Q a 0, reg Q a Q, reg Q a (2 * Q))
        (reg Q b 0, reg Q b Q, reg Q b (2 * Q)) := by
  have ta : ∀ o, o + Q ≤ 3 * Q → (a.drop o).take Q = toBits (reg Q a o) :=
    fun o h => (toBits_reg (by omega)).symm
  have tb : ∀ o, o + Q ≤ 3 * Q → (b.drop o).take Q = toBits (reg Q b o) :=
    fun o h => (toBits_reg (by omega)).symm
  rw [hideNextCons, show win (b.take Q) 0 Q = win b 0 Q from win_take (by omega),
    show win (a.take Q) 0 Q = win a 0 Q from win_take (by omega),
    forall_mem_append, forall_mem_append, forall_mem_append, guardCons_iff,
    decide_eq_true_iff,
    projEqCons_iff ha hb (by omega) (by omega) (ta Q (by omega)) (tb Q (by omega)),
    projEqCons_iff ha hb (by omega) (by omega) (ta (2 * Q) (by omega)) (tb (2 * Q) (by omega)),
    dualCons_iff ha hb (by omega) (by omega) (ta (2 * Q) (by omega)) (tb Q (by omega))
    _ _ (hkg _ _).1 (hkg _ _).2]
  simp only [AuxiliaryQuotient.hidingNext, AuxiliaryDual.stageDual, reg]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4.symm⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4.symm⟩

/-! ## Consistency at one label -/

variable (Q R sR sL) in
/-- The comparison of two answers at the same auxiliary label: equal registers, a readable
condition, and equal duals, tails and input answers. -/
def sameCons (t : AuxType 7 × Bool) (aR bR : BitStr) : List BitStr :=
  guardCons (decide (win aR 0 Q = win bR 0 Q)) (auxLen Q R t.1 + auxLen Q R t.1) ++
  match t.1 with
  | .hide _ => eqCons (3 * Q) (3 * Q) Q Q Q ++ eqCons (3 * Q) (3 * Q) (2 * Q) (2 * Q) Q
  | .read => eqCons (2 * Q + 2 * R) (2 * Q + 2 * R) (Q + R) (Q + R) Q ++
      srcEqCons (2 * Q + 2 * R) (2 * Q + 2 * R) Q (2 * Q + R) Q (2 * Q + R)
        (sR t (win aR 0 Q)) (sL t (win aR 0 Q)) (sR t (win bR 0 Q)) (sL t (win bR 0 Q)) aR bR
  | _ => srcEqCons (Q + 2 * R) (Q + 2 * R) Q (Q + R) Q (Q + R)
        (sR t (win aR 0 Q)) (sL t (win aR 0 Q)) (sR t (win bR 0 Q)) (sL t (win bR 0 Q)) aR bR

/-- **Consistency at one label as constraints**: they hold exactly when the parsed answers are
equal. -/
theorem sameCons_iff {PA : Type*} {t : AuxType 7 × Bool} {a b : BitStr}
    (ha : a.length = auxLen Q R t.1) (hb : b.length = auxLen Q R t.1)
    (hfa : srcFits R sR sL t (win a 0 Q)) (hfb : srcFits R sR sL t (win b 0 Q)) :
    (∀ c ∈ sameCons Q R sR sL t (a.take (auxLenR Q R t.1)) (b.take (auxLenR Q R t.1)),
        Satisfies c (a ++ b ++ [true])) ↔
      (parsed Q R sR sL t a : ParsedAnswer _ _ PA) = parsed Q R sR sL t b := by
  obtain ⟨t, w⟩ := t
  cases t with
  | hide k =>
    simp only [auxLen, auxLenR] at ha hb ⊢
    rw [sameCons, forall_mem_append, guardCons_iff, decide_eq_true_iff]
    simp only [forall_mem_append]
    rw [eqCons_iff ha hb (by omega) (by omega), eqCons_iff ha hb (by omega) (by omega),
      win_take (by omega), win_take (by omega)]
    simp only [parsed, ParsedAnswer.hide.injEq, reg_eq_iff (by omega : 0 + Q ≤ a.length)
      (by omega : 0 + Q ≤ b.length), reg_eq_iff (by omega : Q + Q ≤ a.length)
      (by omega : Q + Q ≤ b.length), reg_eq_iff (by omega : 2 * Q + Q ≤ a.length)
      (by omega : 2 * Q + Q ≤ b.length)]
    rfl
  | read =>
    simp only [srcFits] at hfa hfb
    simp only [auxLen, auxLenR] at ha hb ⊢
    rw [sameCons, forall_mem_append, guardCons_iff, decide_eq_true_iff]
    simp only [forall_mem_append]
    rw [eqCons_iff ha hb (by omega) (by omega),
      srcEqCons_iff ha hb (by rw [win_take (by omega)]; omega) (by rw [win_take (by omega)]; omega)
        (by omega) (by omega) (by rw [win_take (by omega)]; omega)
        (by rw [win_take (by omega)]; omega)]
    simp only [win_take (show 0 + Q ≤ Q + R by omega)]
    simp only [parsed, ParsedAnswer.read.injEq, reg_eq_iff (by omega : 0 + Q ≤ a.length)
      (by omega : 0 + Q ≤ b.length), reg_eq_iff (by omega : Q + R + Q ≤ a.length)
      (by omega : Q + R + Q ≤ b.length)]
    rw [bounded_srcAns_eq_iff (t := (.read, w)) (u := (.read, w)) (by simpa [auxLen] using ha)
        (by simpa [auxLen] using hb) (by simpa [srcFits] using hfa)
        (by simpa [srcFits] using hfb) (by simp) (by simp)]
    simp only [srcAns, srcOffL]
    constructor
    · rintro ⟨h0, h1, -, -, h2⟩
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0, h1, by rw [h0], by rw [h0], h2⟩
  | introspect | sample =>
    simp only [srcFits] at hfa hfb
    simp only [auxLen, auxLenR] at ha hb ⊢
    rw [sameCons, forall_mem_append, guardCons_iff, decide_eq_true_iff]
    rw [srcEqCons_iff ha hb (by rw [win_take (by omega)]; omega)
        (by rw [win_take (by omega)]; omega) (by omega) (by omega)
        (by rw [win_take (by omega)]; omega) (by rw [win_take (by omega)]; omega)]
    simp only [win_take (show 0 + Q ≤ Q + R by omega)]
    simp only [parsed, ParsedAnswer.pair.injEq, reg_eq_iff (by omega : 0 + Q ≤ a.length)
      (by omega : 0 + Q ≤ b.length)]
    rw [bounded_srcAns_eq_iff (t := (_, w)) (u := (_, w)) (by simpa [auxLen] using ha)
        (by simpa [auxLen] using hb) (by simpa [srcFits] using hfa)
        (by simpa [srcFits] using hfb) (by simp) (by simp)]
    simp only [srcAns, srcOffL]
    constructor
    · rintro ⟨h0, -, -, h2⟩
      exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩
      exact ⟨h0, by rw [h0], by rw [h0], h2⟩

/-! ## The source game -/

variable (Q R sR sL) in
/-- The source game's constraints at the edge `(Introspect false, Introspect true)`: the
input's constraints `srcCons` at the two registers and the two readable input answers,
re-indexed onto the windows of the two Introspect answers. -/
def sourceCons (srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr) (aR bR : BitStr) :
    List BitStr :=
  (srcCons (win aR 0 Q) (win bR 0 Q) (win aR Q (sR (.introspect, false) (win aR 0 Q)))
      (win bR Q (sR (.introspect, true) (win bR 0 Q)))).map
    (reindex Q R (sR (.introspect, false) (win aR 0 Q)) (sL (.introspect, false) (win aR 0 Q))
      (sR (.introspect, true) (win bR 0 Q)) (sL (.introspect, true) (win bR 0 Q))
      (auxLen Q R .introspect) (auxLen Q R .introspect))

/-- **The source game's constraints**: when the source predicate `D` accepts exactly the input
answers of the input's lengths satisfying the input's constraints (`hD`), the re-indexed
constraints hold exactly when `D` accepts the two parsed Introspect answers. -/
theorem sourceCons_iff {srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr}
    {D : (Fin Q → 𝔽₂) → (Fin Q → 𝔽₂) → Verifier.Answers R → Verifier.Answers R → Bool}
    (hD : ∀ ya yb : BitStr, ya.length = Q → yb.length = Q → ∀ α β : Verifier.Answers R,
      D (ofBits Q ya) (ofBits Q yb) α β = true ↔
        α.1.length = sR (.introspect, false) ya + sL (.introspect, false) ya ∧
        β.1.length = sR (.introspect, true) yb + sL (.introspect, true) yb ∧
        ∀ c ∈ srcCons ya yb (α.1.take (sR (.introspect, false) ya))
          (β.1.take (sR (.introspect, true) yb)), Satisfies c (α.1 ++ β.1 ++ [true]))
    {a b : BitStr} (ha : a.length = auxLen Q R .introspect)
    (hb : b.length = auxLen Q R .introspect)
    (hfa : srcFits R sR sL (.introspect, false) (win a 0 Q))
    (hfb : srcFits R sR sL (.introspect, true) (win b 0 Q)) :
    (∀ c ∈ sourceCons Q R sR sL srcCons (a.take (Q + R)) (b.take (Q + R)),
        Satisfies c (a ++ b ++ [true])) ↔
      D (reg Q a 0) (reg Q b 0)
        (AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.introspect, false) a))
        (AuxiliaryAnswer.bounded R (srcAns Q R sR sL (.introspect, true) b)) = true := by
  have hla := length_srcAns ha hfa (by simp)
  have hlb := length_srcAns hb hfb (by simp)
  simp only [srcFits] at hfa hfb
  simp only [auxLen] at ha hb
  rw [reg, reg, hD _ _ (length_win (by omega)) (length_win (by omega)),
    bounded_srcAns_val (by simpa [auxLen] using ha) (by simpa [srcFits] using hfa) (by simp),
    bounded_srcAns_val (by simpa [auxLen] using hb) (by simpa [srcFits] using hfb) (by simp)]
  simp only [hla, hlb, true_and]
  rw [sourceCons]
  simp only [win_take (show 0 + Q ≤ Q + R by omega), List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  have hra : win (a.take (Q + R)) Q (sR (.introspect, false) (win a 0 Q)) =
      win a Q (sR (.introspect, false) (win a 0 Q)) := win_take (by omega)
  have hrb : win (b.take (Q + R)) Q (sR (.introspect, true) (win b 0 Q)) =
      win b Q (sR (.introspect, true) (win b 0 Q)) := win_take (by omega)
  have hta : (srcAns Q R sR sL (.introspect, false) a).take (sR (.introspect, false) (win a 0 Q)) =
      win a Q (sR (.introspect, false) (win a 0 Q)) :=
    List.take_left' (length_win (by omega))
  have htb : (srcAns Q R sR sL (.introspect, true) b).take (sR (.introspect, true) (win b 0 Q)) =
      win b Q (sR (.introspect, true) (win b 0 Q)) :=
    List.take_left' (length_win (by omega))
  rw [hra, hrb, hta, htb]
  refine forall₂_congr fun c _ => ?_
  rw [satisfies_reindex_iff Q R _ _ _ _ (by simpa [auxLen] using ha) (by simpa [auxLen] using hb)
    (by omega) (by simp [auxLen]; omega) (by omega) (by simp [auxLen]; omega)]
  rfl

/-! ## The other orientation -/

/-- A constraint on `(b, a)`, with `b` of length `lb` and `a` of length `la`, as one on
`(a, b)`. -/
def swapCon (la lb : ℕ) (c : BitStr) : BitStr :=
  (c.drop lb).take la ++ c.take lb ++ c.drop (lb + la)

/-- **A swapped constraint holds of `(a, b)` exactly when the constraint holds of `(b, a)`.** -/
theorem satisfies_swapCon {la lb : ℕ} {a b : BitStr} (ha : a.length = la) (hb : b.length = lb)
    (c : BitStr) :
    Satisfies (swapCon la lb c) (a ++ b ++ [true]) ↔ Satisfies c (b ++ a ++ [true]) := by
  by_cases hc : c.length = lb + la + 1
  · set α := (c.drop lb).take la with hα
    set β := c.take lb with hβ
    set ε := c.drop (lb + la) with hε
    have h1 : α.length = la := by simp [α]; omega
    have h2 : β.length = lb := by simp [β]; omega
    have h3 : ε.length = 1 := by simp [ε]; omega
    have hce : c = β ++ α ++ ε := by
      rw [hα, hβ, hε, List.append_assoc, ← List.drop_drop, List.take_append_drop,
        List.take_append_drop]
    have e1 : swapCon la lb c = α ++ β ++ ε := rfl
    rw [e1]
    conv_rhs => rw [hce]
    rw [satisfies_iff_dotL (by simp [h1, h2, h3, ha, hb]),
      satisfies_iff_dotL (by simp [h1, h2, h3, ha, hb]),
      dotL_append (by simp [h1, h2, ha, hb]), dotL_append (by simp [h1, ha]),
      dotL_append (by simp [h1, h2, ha, hb]), dotL_append (by simp [h2, hb])]
    cases dotL α a <;> cases dotL β b <;> cases dotL ε [true] <;> simp
  · constructor
    · rintro ⟨hl, -⟩
      exfalso; apply hc
      simp [swapCon, ha, hb] at hl
      omega
    · rintro ⟨hl, -⟩
      exfalso; apply hc
      simp [ha, hb] at hl
      omega

theorem forall_swapCon_iff {la lb : ℕ} {a b : BitStr} (ha : a.length = la) (hb : b.length = lb)
    (cs : List BitStr) :
    (∀ c ∈ cs.map (swapCon la lb), Satisfies c (a ++ b ++ [true])) ↔
      ∀ c ∈ cs, Satisfies c (b ++ a ++ [true]) := by
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satisfies_swapCon ha hb]

/-! ## One orientation of the directed checks between auxiliary answers -/

variable (Q R sR sL L) in
/-- The constraints of one orientation of the directed auxiliary checks, on an ordered pair of
auxiliary labels: those of `AuxiliaryQuotient.directed`'s clause for the pair, none when it has
none. -/
noncomputable def dirAux (kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂))
    (srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr) :
    AuxType 7 × Bool → AuxType 7 × Bool → BitStr → BitStr → List BitStr
  | (.introspect, w), (.sample, v), aR, bR => if w = v then sampleCons Q R sR sL L w aR bR else []
  | (.introspect, w), (.read, v), aR, bR => if w = v then readCons Q R sR sL w aR bR else []
  | (.hide k, w), (.read, v), aR, bR =>
      if w = v ∧ k.val + 1 = 7 then hideReadCons Q R L w aR bR else []
  | (.hide k, w), (.hide j, v), aR, bR =>
      if w = v ∧ k.val + 1 = j.val then hideNextCons Q L kg w k.val aR bR else []
  | (.introspect, false), (.introspect, true), aR, bR => sourceCons Q R sR sL srcCons aR bR
  | _, _, _, _ => []

/-- **One orientation of the directed auxiliary checks as constraints.** -/
theorem dirAux_iff {P PA : Type*} (X Z : P) (project : PA → Fin Q → 𝔽₂)
    {kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂)} (hkg : KerGens Q kg)
    {srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr}
    {D : (Fin Q → 𝔽₂) → (Fin Q → 𝔽₂) → Verifier.Answers R → Verifier.Answers R → Bool}
    (hD : ∀ ya yb : BitStr, ya.length = Q → yb.length = Q → ∀ α β : Verifier.Answers R,
      D (ofBits Q ya) (ofBits Q yb) α β = true ↔
        α.1.length = sR (.introspect, false) ya + sL (.introspect, false) ya ∧
        β.1.length = sR (.introspect, true) yb + sL (.introspect, true) yb ∧
        ∀ c ∈ srcCons ya yb (α.1.take (sR (.introspect, false) ya))
          (β.1.take (sR (.introspect, true) yb)), Satisfies c (α.1 ++ β.1 ++ [true]))
    (hS : ∀ (w : Bool) (y z : BitStr), ofBits Q y = (L w).eval (ofBits Q z) →
      sR (.introspect, w) y = sR (.sample, w) z ∧ sL (.introspect, w) y = sL (.sample, w) z)
    (hRd : ∀ (w : Bool) (y : BitStr), sR (.introspect, w) y = sR (.read, w) y ∧
      sL (.introspect, w) y = sL (.read, w) y)
    {t u : AuxType 7 × Bool} {a b : BitStr} (ha : a.length = auxLen Q R t.1)
    (hb : b.length = auxLen Q R u.1) (hfa : srcFits R sR sL t (win a 0 Q))
    (hfb : srcFits R sR sL u (win b 0 Q)) :
    (∀ c ∈ dirAux Q R sR sL L kg srcCons t u (a.take (auxLenR Q R t.1))
        (b.take (auxLenR Q R u.1)), Satisfies c (a ++ b ++ [true])) ↔
      AuxiliaryQuotient.directed L X Z project D (.inr t) (.inr u)
        (parsed Q R sR sL t a) (parsed Q R sR sL u b) = true := by
  obtain ⟨t, w⟩ := t
  obtain ⟨u, v⟩ := u
  cases t <;> cases u
  all_goals simp only [auxLenR] at ha hb ⊢
  case introspect.sample =>
    simp only [dirAux, parsed, AuxiliaryQuotient.directed]
    split_ifs with h
    · subst h
      simp only [decide_eq_true_eq]
      exact sampleCons_iff ha hb hfa hfb (hS w)
    · simp
  case introspect.read =>
    simp only [dirAux, parsed, AuxiliaryQuotient.directed]
    split_ifs with h
    · subst h
      simp only [decide_eq_true_eq]
      exact readCons_iff ha hb hfa hfb (hRd w)
    · simp
  case hide.read k =>
    simp only [dirAux, parsed, AuxiliaryQuotient.directed]
    split_ifs with h
    · obtain ⟨rfl, -⟩ := h
      simp only [decide_eq_true_eq]
      exact hideReadCons_iff ha hb _
    · simp
  case hide.hide k j =>
    simp only [auxLen] at ha hb
    simp only [dirAux, parsed, AuxiliaryQuotient.directed]
    split_ifs with h
    · obtain ⟨rfl, -⟩ := h
      simp only [decide_eq_true_eq]
      exact hideNextCons_iff hkg ha hb
    · simp
  case introspect.introspect =>
    cases w <;> cases v
    case false.true =>
      simp only [dirAux, parsed, AuxiliaryQuotient.directed]
      exact sourceCons_iff hD ha hb hfa hfb
    all_goals simp [dirAux, AuxiliaryQuotient.directed]
  all_goals simp [dirAux, AuxiliaryQuotient.directed]

/-! ## A pair of auxiliary answers -/

open Classical in
variable (Q R sR sL L) in
/-- The constraints at an ordered pair of auxiliary labels: a readable condition `G` on each
register, consistency when the labels agree, and the directed checks in both orientations. -/
noncomputable def auxPair (G : AuxType 7 × Bool → BitStr → Prop)
    (kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂))
    (srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr)
    (t u : AuxType 7 × Bool) (aR bR : BitStr) : List BitStr :=
  guardCons (decide (G t (win aR 0 Q) ∧ G u (win bR 0 Q)))
      (auxLen Q R t.1 + auxLen Q R u.1) ++
    ((if t = u then sameCons Q R sR sL t aR bR else []) ++
    (dirAux Q R sR sL L kg srcCons t u aR bR ++
    (dirAux Q R sR sL L kg srcCons u t bR aR).map (swapCon (auxLen Q R t.1) (auxLen Q R u.1))))

theorem auxLenR_add_le (t : AuxType 7) : Q ≤ auxLenR Q R t := by
  cases t <;> simp [auxLenR]

/-- **The constraints at a pair of auxiliary labels**: they hold exactly when the readable
condition holds at both registers, the parsed answers agree when the labels do, and the
directed checks accept in both orientations. -/
theorem auxPair_iff {P PA : Type*} (X Z : P) (project : PA → Fin Q → 𝔽₂)
    {G : AuxType 7 × Bool → BitStr → Prop} (hG : ∀ t y, G t y → srcFits R sR sL t y)
    {kg : ∀ S : Finset (Fin Q), CL.RegLinear 𝔽₂ S → List (Fin Q → 𝔽₂)} (hkg : KerGens Q kg)
    {srcCons : BitStr → BitStr → BitStr → BitStr → List BitStr}
    {D : (Fin Q → 𝔽₂) → (Fin Q → 𝔽₂) → Verifier.Answers R → Verifier.Answers R → Bool}
    (hD : ∀ ya yb : BitStr, ya.length = Q → yb.length = Q → ∀ α β : Verifier.Answers R,
      D (ofBits Q ya) (ofBits Q yb) α β = true ↔
        α.1.length = sR (.introspect, false) ya + sL (.introspect, false) ya ∧
        β.1.length = sR (.introspect, true) yb + sL (.introspect, true) yb ∧
        ∀ c ∈ srcCons ya yb (α.1.take (sR (.introspect, false) ya))
          (β.1.take (sR (.introspect, true) yb)), Satisfies c (α.1 ++ β.1 ++ [true]))
    (hS : ∀ (w : Bool) (y z : BitStr), ofBits Q y = (L w).eval (ofBits Q z) →
      sR (.introspect, w) y = sR (.sample, w) z ∧ sL (.introspect, w) y = sL (.sample, w) z)
    (hRd : ∀ (w : Bool) (y : BitStr), sR (.introspect, w) y = sR (.read, w) y ∧
      sL (.introspect, w) y = sL (.read, w) y)
    {t u : AuxType 7 × Bool} {a b : BitStr} (ha : a.length = auxLen Q R t.1)
    (hb : b.length = auxLen Q R u.1) :
    (∀ c ∈ auxPair Q R sR sL L G kg srcCons t u (a.take (auxLenR Q R t.1))
        (b.take (auxLenR Q R u.1)), Satisfies c (a ++ b ++ [true])) ↔
      G t (win a 0 Q) ∧ G u (win b 0 Q) ∧
        (t = u → (parsed Q R sR sL t a : ParsedAnswer _ _ PA) = parsed Q R sR sL u b) ∧
        AuxiliaryQuotient.directed L X Z project D (.inr t) (.inr u)
          (parsed Q R sR sL t a) (parsed Q R sR sL u b) = true ∧
        AuxiliaryQuotient.directed L X Z project D (.inr u) (.inr t)
          (parsed Q R sR sL u b) (parsed Q R sR sL t a) = true := by
  rw [auxPair, forall_mem_append, guardCons_iff]
  simp only [decide_eq_true_eq]
  rw [win_take (by have := auxLenR_add_le (Q := Q) (R := R) t.1; omega),
    win_take (by have := auxLenR_add_le (Q := Q) (R := R) u.1; omega)]
  by_cases hg : G t (win a 0 Q) ∧ G u (win b 0 Q)
  · have hfa := hG _ _ hg.1
    have hfb := hG _ _ hg.2
    simp only [hg, true_and, forall_mem_append]
    rw [forall_swapCon_iff ha hb, dirAux_iff X Z project hkg hD hS hRd ha hb hfa hfb,
      dirAux_iff X Z project hkg hD hS hRd hb ha hfb hfa]
    split_ifs with htu
    · subst htu
      rw [sameCons_iff (PA := PA) ha hb hfa hfb]
      simp
    · simp [htu]
  · constructor
    · rintro ⟨h, -⟩
      exact absurd h hg
    · rintro ⟨h1, h2, -⟩
      exact absurd ⟨h1, h2⟩ hg

end MIPRE.Tailored.Intro

end
