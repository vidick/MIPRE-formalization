/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.PauliHide
public import MIPRE.Background.Introspection.DecisionKernelSoundness
public import MIPRE.Tailored.Intro.AuxCons
public import MIPRE.Tailored.Intro.Source
public import MIPRE.Tailored.Intro.Layout
public import MIPRE.Tailored.Detyping

@[expose] public section

/-!
# The typed tailored data of the introspection verifier

The constraints of the tailored presentation of the introspection verifier, label by label
(`consL`), and their reading (`consL_iff`): at an ordered pair of labels, the constraints hold
of two answers of the labels' lengths exactly when the readable conditions hold at both and the
kernel's semantic check (`AuxiliaryQuotient.check`, the hypothesis of `program_complete` and the
conclusion of `program_sound`) accepts the two answers read off the layout (`parsedT`):

* at two Pauli labels, the Pauli basis test (`PauliCons.pauliCons`);
* at two auxiliary labels, `auxPair`, with the input's split and constraints read off the
  input verifier `T` through the normal form verifier `V` it is presented by;
* at a Pauli label and an auxiliary one, in either order, the readable condition of the
  auxiliary answer and the two Pauli clauses: the `Z` answer is the projection of the sampled
  register (readable), and the first hiding level agrees with the `X` answer
  (`PauliHide.pauliHideCons`).
-/

namespace MIPRE.Tailored.Intro.Typed

open Cost CL MIPRE.SAT MIPRE.Introspection MIPRE.QLD MIPRE.Tailored.Intro.PauliCons
open MIPRE.Tailored.Intro.PauliHide Classical

variable (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ)
  (hm : 2 ^ j ∣ Fintype.card (shoupBinField k hk).carrier) (R : ℕ) {n : ℕ}
  (T : TailoredVerifier 7) (V : Verifier 7) (hs : V.sampler.dim (2 ^ n) ≤ 2 ^ 2 ^ j * k)

/-- The register length. -/
abbrev Q : ℕ := 2 ^ 2 ^ j * k

/-- The CL functions of the auxiliary questions. -/
noncomputable abbrev L : Bool → CL.CLFun 𝔽₂ (Fin (Q k j)) 7 := AuxiliaryDecision.padded V hs

/-- The input's readable split. -/
noncomputable abbrev sR : AuxType 7 × Bool → BitStr → ℕ := srcSplitR T V hs

/-- The input's linear split. -/
noncomputable abbrev sL : AuxType 7 × Bool → BitStr → ℕ := srcSplitL T V hs

/-- The input's constraints at the two Introspect registers. -/
noncomputable def srcCons (ya yb aR bR : BitStr) : List BitStr :=
  T.consOf (2 ^ n) (srcQuestion V hs (.introspect, false) ya)
    (srcQuestion V hs (.introspect, true) yb) aR bR

/-- The prefix condition of the kernel's prefix scan, at the register of a Read or Hide
answer. -/
def prefixOK : AuxType 7 × Bool → BitStr → Prop
  | (.hide i, w), y => ∃ x, ((L k j V hs w).truncate i.val).eval x =
      (L k j V hs w).outputPrefix i.val (ofBits (Q k j) y)
  | (.read, w), y => ∃ x, ((L k j V hs w).truncate (7 - 1)).eval x =
      (L k j V hs w).outputPrefix (7 - 1) (ofBits (Q k j) y)
  | _, _ => True

/-- The readable condition at an auxiliary register: the input's answer fits the cutoff, the
prefix condition, and an Introspect register is a source output. -/
def G (t : AuxType 7 × Bool) (y : BitStr) : Prop :=
  srcFits R (sR k j T V hs) (sL k j T V hs) t y ∧ prefixOK k j V hs t y ∧
    (t.1 = .introspect → SourceCompiler.InSource (V.sampler.dim (2 ^ n)) y)

/-- The Pauli answer read off its bits. -/
noncomputable abbrev pDec (p : Ty) (a : BitStr) : QLD.Answer (shoupBinField k hk).carrier (2 ^ j) 1 :=
  DecisionKernel.Answer.pauliDecode (shoupBinField k hk) (2 ^ j) (.inl p) a

/-- The kernel's projection of a Pauli answer. -/
noncomputable abbrev proj : QLD.Answer (shoupBinField k hk).carrier (2 ^ j) 1 → Fin (Q k j) → 𝔽₂ :=
  DecisionKernel.Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd)

variable (kg : ∀ S : Finset (Fin (Q k j)), CL.RegLinear 𝔽₂ S → List (Fin (Q k j) → 𝔽₂))

/-- The directed clauses from a Pauli label to an auxiliary one: the `Z` answer against a
Sample register, a readable condition, and the `X` answer against the first hiding level. -/
noncomputable def pauliDir (p : Ty) (t : AuxType 7 × Bool) (aR bR : BitStr) : List BitStr :=
  (if p = .pauli .Z ∧ t.1 = .sample then
    guardCons (decide (proj k hk hodd j (pDec k hk j (.pauli .Z) aR) =
      ofBits (Q k j) (win bR 0 (Q k j)))) (pauliLen (2 ^ j) k p + auxLen (Q k j) R t.1)
  else []) ++
  (if p = .pauli .X ∧ t.1 = .hide 0 then pauliHideCons k hk hodd j (L k j V hs t.2)
    (kg _ (CLChecks.stageLinear (L k j V hs t.2) 0 0)) else [])

/-- The constraints from a Pauli label to an auxiliary one. -/
noncomputable def pauliAux (p : Ty) (t : AuxType 7 × Bool) (aR bR : BitStr) : List BitStr :=
  if G k j R T V hs t (win bR 0 (Q k j)) then pauliDir k hk hodd j R V hs kg p t aR bR
  else [rejectConstraint (pauliLen (2 ^ j) k p + auxLen (Q k j) R t.1)]

/-- The constraints at an ordered pair of labels, from the two question payloads `x, y` and the
two readable answers, before the length check. -/
noncomputable def consRaw : DecisionKernel.Label → DecisionKernel.Label → BitStr → BitStr →
    BitStr → BitStr → List BitStr
  | .inl p, .inl q, x, y, aR, bR => pauliCons k hk hodd j hm p q x y aR bR
  | .inr t, .inr u, _, _, aR, bR =>
      auxPair (Q k j) R (sR k j T V hs) (sL k j T V hs) (L k j V hs) (G k j R T V hs) kg
        (srcCons k j T V hs) t u aR bR
  | .inl p, .inr t, _, _, aR, bR => pauliAux k hk hodd j R T V hs kg p t aR bR
  | .inr t, .inl p, _, _, aR, bR =>
      (pauliAux k hk hodd j R T V hs kg p t bR aR).map
        (swapCon (auxLen (Q k j) R t.1) (pauliLen (2 ^ j) k p))

/-- The number of readable bits of a label. -/
def lenR : DecisionKernel.Label → ℕ
  | .inl p => pauliLenR k (2 ^ j) p
  | .inr t => auxLenR (Q k j) R t.1

/-- The number of bits of a label. -/
def len : DecisionKernel.Label → ℕ
  | .inl p => pauliLen (2 ^ j) k p
  | .inr t => auxLen (Q k j) R t.1

/-- **The constraints at an ordered pair of labels**, from the two question payloads `x, y`
and the two readable answers: none unless the readable answers have the labels' readable
lengths (as they always do in the game). -/
noncomputable def consL (u v : DecisionKernel.Label) (x y aR bR : BitStr) : List BitStr :=
  if aR.length = lenR k j R u ∧ bR.length = lenR k j R v then
    consRaw k hk hodd j hm R T V hs kg u v x y aR bR
  else []

theorem lenR_le_len (t : DecisionKernel.Label) : lenR k j R t ≤ len k j R t := by
  rcases t with p | ⟨t, w⟩
  · simp only [lenR, len, PauliCons.pauliLenR]
    split_ifs <;> omega
  · cases t <;> simp [lenR, len, auxLenR, auxLen] <;> omega

/-- The kernel's parsed answer read off the bits at a label. -/
noncomputable def parsedT : (t : DecisionKernel.Label) → BitStr →
    ParsedAnswer (Fin (Q k j) → 𝔽₂) (Verifier.Answers R)
      (QLD.Answer (shoupBinField k hk).carrier (2 ^ j) 1)
  | .inl p, a => .pauli (pDec k hk j p a)
  | .inr t, a => parsed (Q k j) R (sR k j T V hs) (sL k j T V hs) t a

/-- The readable condition at a label. -/
def readOK : DecisionKernel.Label → BitStr → Prop
  | .inl _, _ => True
  | .inr t, a => G k j R T V hs t (win a 0 (Q k j))

/-! ## The Pauli-to-auxiliary constraints -/

theorem eq_win3 {Q : ℕ} {b : BitStr} (h : b.length = 3 * Q) :
    b = win b 0 Q ++ win b Q Q ++ win b (2 * Q) Q := by
  have h3 : win b (2 * Q) Q = (b.drop Q).drop Q := by
    rw [win, List.drop_drop, List.take_of_length_le (by simp; omega)]
    congr 1; omega
  rw [h3, win, win, List.drop_zero, List.append_assoc, List.take_append_drop,
    List.take_append_drop]

variable {k hk hodd j R T V hs kg} in
/-- **The constraints from a Pauli label to an auxiliary one**: the readable condition at the
auxiliary register and the kernel's directed check. -/
theorem pauliAux_iff (hkg : KerGens (Q k j) kg) (D : (Fin (Q k j) → 𝔽₂) →
      (Fin (Q k j) → 𝔽₂) → Verifier.Answers R → Verifier.Answers R → Bool)
    (p : Ty) (t : AuxType 7 × Bool) (a b : BitStr)
    (ha : a.length = pauliLen (2 ^ j) k p) (hb : b.length = auxLen (Q k j) R t.1) :
    (∀ c ∈ pauliAux k hk hodd j R T V hs kg p t (a.take (pauliLenR k (2 ^ j) p))
        (b.take (auxLenR (Q k j) R t.1)), Satisfies c (a ++ b ++ [true])) ↔
      G k j R T V hs t (win b 0 (Q k j)) ∧
        AuxiliaryQuotient.directed (L k j V hs) (.pauli .X) (.pauli .Z) (proj k hk hodd j) D
          (.inl p) (.inr t) (.pauli (pDec k hk j p a))
          (parsed (Q k j) R (sR k j T V hs) (sL k j T V hs) t b) = true := by
  rw [pauliAux, win_take (by have := auxLenR_add_le (Q := Q k j) (R := R) t.1; omega)]
  by_cases hg : G k j R T V hs t (win b 0 (Q k j))
  swap
  · rw [if_neg hg]
    simp only [hg, false_and, iff_false]
    intro h
    exact not_satisfies_rejectConstraint _ _ (h _ (List.mem_singleton_self _))
  rw [if_pos hg]
  simp only [hg, true_and]
  obtain ⟨t, w⟩ := t
  rw [pauliDir, forall_mem_append]
  cases t with
  | sample =>
    by_cases hp : p = .pauli .Z
    · subst hp
      simp only [and_self, ↓reduceIte, reduceCtorEq, and_false, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, guardCons_iff, decide_eq_true_eq]
      simp only [AuxiliaryQuotient.directed, ↓reduceIte, decide_eq_true_eq, parsed, reg,
        win_take (show 0 + Q k j ≤ auxLenR (Q k j) R .sample by simp [auxLenR])]
      rw [List.take_of_length_le (by simp [pauliLenR, pauliRead, ha])]
    · simp [hp, AuxiliaryQuotient.directed, parsed]
  | hide i =>
    simp only [auxLen] at hb
    by_cases hp : p = .pauli .X ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hp
      simp only [reduceCtorEq, and_false, ↓reduceIte, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_self, true_and]
      simp only [AuxiliaryQuotient.directed, Fin.val_zero, and_self, ↓reduceIte,
        decide_eq_true_eq, parsed, reg]
      conv_lhs => rw [eq_win3 hb]
      exact pauliHideCons_iff k hk hodd j _ _ (hkg _ _).1 (hkg _ _).2 a _ _ _ ha
        (length_win (by omega)) (length_win (by omega)) (length_win (by omega))
    · have hp' : ¬(p = .pauli .X ∧ AuxType.hide i = AuxType.hide (0 : Fin 7)) := by
        simpa using hp
      simp only [hp', ↓reduceIte, reduceCtorEq, and_false, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_self, true_iff]
      simp only [AuxiliaryQuotient.directed, parsed]
      split_ifs with h
      · exact absurd ⟨h.1, Fin.ext h.2⟩ hp
      · rfl
  | introspect => simp [AuxiliaryQuotient.directed]
  | read => simp [AuxiliaryQuotient.directed]

/-! ## All the constraints -/

/-- How the normal form verifier `V` accepts at index `2^n`: as the tailored input `T` does,
on questions of the sampler's length (`TailoredVerifier.ofTNFVT_accepts_iff`). -/
def AcceptsAsInput (n : ℕ) : Prop :=
  ∀ xs ys a b : BitStr, xs.length = V.sampler.dim (2 ^ n) → ys.length = V.sampler.dim (2 ^ n) →
    (V.decider.Accepts (2 ^ n) xs ys a b ↔
      a.length = T.lenOf (2 ^ n) xs false + T.lenOf (2 ^ n) xs true ∧
      b.length = T.lenOf (2 ^ n) ys false + T.lenOf (2 ^ n) ys true ∧
      ∀ c ∈ T.consOf (2 ^ n) xs ys (a.take (T.lenOf (2 ^ n) xs false))
        (b.take (T.lenOf (2 ^ n) ys false)), Satisfies c (a ++ b ++ [true]))

omit [NeZero k] in
variable {k j R T V hs} in
theorem hD_of_acceptsAsInput (h : AcceptsAsInput T V n) (ya yb : BitStr) (_ : ya.length = Q k j)
    (_ : yb.length = Q k j) (α β : Verifier.Answers R) :
    DecisionKernel.finiteSourcePredicate V hs (ofBits (Q k j) ya) (ofBits (Q k j) yb) α β = true ↔
      α.1.length = sR k j T V hs (.introspect, false) ya + sL k j T V hs (.introspect, false) ya ∧
      β.1.length = sR k j T V hs (.introspect, true) yb + sL k j T V hs (.introspect, true) yb ∧
      ∀ c ∈ srcCons k j T V hs ya yb (α.1.take (sR k j T V hs (.introspect, false) ya))
        (β.1.take (sR k j T V hs (.introspect, true) yb)), Satisfies c (α.1 ++ β.1 ++ [true]) := by
  simp only [DecisionKernel.finiteSourcePredicate, AuxiliaryDecision.sourcePredicate,
    decide_eq_true_eq]
  exact h _ _ _ _ (length_toBits _) (length_toBits _)

omit [NeZero k] in
variable {k j T V hs} in
theorem hS_split (w : Bool) (y z : BitStr)
    (h : ofBits (Q k j) y = (L k j V hs w).eval (ofBits (Q k j) z)) :
    sR k j T V hs (.introspect, w) y = sR k j T V hs (.sample, w) z ∧
      sL k j T V hs (.introspect, w) y = sL k j T V hs (.sample, w) z := by
  simp [sR, sL, srcSplitR, srcSplitL, srcQuestion, h]

theorem fits_parsed {PA : Type*} {Q' R' : ℕ} {sR' sL' : AuxType 7 × Bool → BitStr → ℕ}
    (t : AuxType 7 × Bool) (a : BitStr) :
    TypedPredicate.fits (PauliType := Ty) (.inr t)
      (parsed Q' R' sR' sL' t a : ParsedAnswer _ _ PA) = true := by
  obtain ⟨t, w⟩ := t
  cases t <;> rfl

@[simp] theorem fits_pauli {F ι PA A : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
    (p : Ty) (a : PA) :
    TypedPredicate.fits (ℓ := ℓ) (.inl p) (.pauli a : ParsedAnswer (ι → F) A PA) = true := rfl

theorem directed_inr_inl {PA A : Type*} {Q' : ℕ} (L' : Bool → CL.CLFun 𝔽₂ (Fin Q') 7)
    (X Z : Ty) (pr : PA → Fin Q' → 𝔽₂)
    (D : (Fin Q' → 𝔽₂) → (Fin Q' → 𝔽₂) → A → A → Bool) (t : AuxType 7 × Bool) (p : Ty)
    (a b : ParsedAnswer (Fin Q' → 𝔽₂) A PA) :
    AuxiliaryQuotient.directed L' X Z pr D (.inr t) (.inl p) a b = true := by
  obtain ⟨t, w⟩ := t
  cases t <;> cases a <;> cases b <;> rfl

variable {k hk hodd j hm R T V hs kg} in
/-- **The constraints at an ordered pair of labels**, read: for answers of the labels' lengths,
they hold exactly when the readable conditions hold at both answers and the kernel's semantic
check accepts the two answers read off the layout. -/
theorem consL_iff (hkg : KerGens (Q k j) kg) (hacc : AcceptsAsInput T V n)
    (u v : DecisionKernel.Label) (x y a b : BitStr) (ha : a.length = len k j R u)
    (hb : b.length = len k j R v) :
    (∀ c ∈ consL k hk hodd j hm R T V hs kg u v x y (a.take (lenR k j R u))
        (b.take (lenR k j R v)), Satisfies c (a ++ b ++ [true])) ↔
      readOK k j R T V hs u a ∧ readOK k j R T V hs v b ∧
        AuxiliaryQuotient.check (L k j V hs) (.pauli .X) (.pauli .Z) (proj k hk hodd j)
          (DecisionKernel.finiteSourcePredicate (R := R) V hs)
          (DecisionKernel.finitePauliCheck k hk hodd j hm x y) u v
          (parsedT k hk j R T V hs u a) (parsedT k hk j R T V hs v b) = true := by
  have hla : (a.take (lenR k j R u)).length = lenR k j R u := by
    rw [List.length_take, ha]; exact min_eq_left (lenR_le_len k j R u)
  have hlb : (b.take (lenR k j R v)).length = lenR k j R v := by
    rw [List.length_take, hb]; exact min_eq_left (lenR_le_len k j R v)
  rw [consL, if_pos ⟨hla, hlb⟩]
  simp only [AuxiliaryQuotient.check, Bool.and_eq_true]
  rcases u with p | t <;> rcases v with q | u <;> simp only [lenR, len] at ha hb ⊢
  · -- two Pauli labels
    rw [consRaw, pauliCons_iff k hk hodd j hm p q x y a b ha hb]
    simp only [readOK, parsedT, TypedPredicate.fits, Sum.inl.injEq, true_and, and_true,
      AuxiliaryQuotient.directed, DecisionKernel.finitePauliCheck]
    constructor
    · intro h
      refine ⟨?_, h⟩
      split_ifs with hpq
      · subst hpq
        simp only [QLD.accepts, QLD.subtests, Bool.and_eq_true, questionOfBits_ty,
          ↓reduceIte, decide_eq_true_eq] at h
        simp only [ParsedAnswer.pauli.injEq, decide_eq_true_eq]
        exact h.2
      · rfl
    · exact fun h => h.2
  · -- a Pauli label, then an auxiliary one
    rw [consRaw, pauliAux_iff hkg (DecisionKernel.finiteSourcePredicate (R := R) V hs) p u a b ha hb]
    simp only [readOK, parsedT, fits_parsed, fits_pauli, reduceCtorEq, ↓reduceIte,
      true_and, directed_inr_inl, and_true]
  · -- an auxiliary label, then a Pauli one
    rw [consRaw, forall_swapCon_iff ha hb,
      pauliAux_iff hkg (DecisionKernel.finiteSourcePredicate (R := R) V hs) q t b a hb ha]
    simp only [readOK, parsedT, fits_parsed, fits_pauli, reduceCtorEq, ↓reduceIte,
      true_and, directed_inr_inl]
  · -- two auxiliary labels
    rw [consRaw, auxPair_iff (Ty.pauli .X) (Ty.pauli .Z) (proj k hk hodd j) (fun _ _ h => h.1) hkg
      (hD_of_acceptsAsInput (hs := hs) hacc) (hS_split (T := T)) (fun _ _ => ⟨rfl, rfl⟩) ha hb]
    have ea : parsedT k hk j R T V hs (.inr t) a =
        parsed (Q k j) R (sR k j T V hs) (sL k j T V hs) t a := rfl
    have eb : parsedT k hk j R T V hs (.inr u) b =
        parsed (Q k j) R (sR k j T V hs) (sL k j T V hs) u b := rfl
    rw [ea, eb]
    simp only [readOK, fits_parsed, Sum.inr.injEq, true_and, and_true]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, ⟨?_, h4⟩, h5⟩
      split_ifs with htu
      · simp only [decide_eq_true_eq]
        exact h3 htu
      · rfl
    · rintro ⟨h1, h2, ⟨h3, h4⟩, h5⟩
      refine ⟨h1, h2, fun htu => ?_, h4, h5⟩
      simpa [htu] using h3

end MIPRE.Tailored.Intro.Typed

end
