/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.PauliCons
public import MIPRE.Background.Introspection.DecisionKernelAnswers
public import MIPRE.Tailored.Intro.RegCons
public import MIPRE.Foundations.Introspection.AuxiliaryQuotientChecks

@[expose] public section

/-!
# The first hiding edge as controlled linear constraints

The first hiding edge of the introspection verifier compares an `X`-basis Pauli answer `a` with
a Hide answer `(y, y', x)` of level `0`, three registers of `Q = 2^(2^j) k` bits. The kernel
reads the Pauli answer as the register `Π a = pauliProject (pauliDecode a)`: its field elements
expanded in the self-dual normal basis (`QLD.PauliFullAnswerProgram.registerVector`). The check
is the quotient relaxation `AuxiliaryQuotient.hidingPauli`: the duals of `y'` and of `Π a` under
the first stage of the conditionally linear function `P` agree, and `Π a` and `x` agree off the
first factor `S = P.factorOfPrefix 0 0`.

`Π` is `F₂`-linear in the answer bits (`pauliXProj`, `pauliXProj_eq`), so both halves are linear
checks on the two answers, with coefficients computed from `P`:

* for `z` in a list `gens` spanning the kernel of `stageLinear P 0 0`:
  `∑ zᵢ (proj S (Π a))ᵢ + ∑ zᵢ (proj S y')ᵢ = 0`, which over the whole list is the equality
  of duals (`AuxiliaryDual.registerDual_eq_iff_dot`, as in `MIPRE.Tailored.Intro.dualCons_iff`);
* for `i ∉ S`, enumerated along `List.finRange`: `(Π a)ᵢ = xᵢ`.

`hideChecks` writes them for the two answers at arbitrary offsets of one bit vector, and
`hideChecks_iff` is their meaning; `pauliHideCons` (Pauli answer first) and `pauliHideConsRev`
(Hide answer first) are the constraint lists of the two orientations of the edge, and
`pauliHideCons_iff`, `pauliHideConsRev_iff` the main theorems.

The file also records the byte round trip of the Pauli answers at their label lengths
(`answerBits_decodeBits_of_length`), for every label.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.PauliHide

open Cost MIPRE.SAT MIPRE.LowDegree MIPRE.QLD MIPRE.QLD.PauliAnswerProgram
open MIPRE.Introspection MIPRE.Introspection.FieldTableProgram MIPRE.Tailored.Intro.PauliCons

/-! ## The byte round trip -/

/-- **The byte round trip of Pauli answers**: an answer of its label's length is the encoding of
its decoding, at every label. -/
theorem answerBits_decodeBits_of_length (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (T : Ty) (a : BitStr)
    (ha : a.length = pauliLen m k T) :
    answerBits (shoupBinField k hk) (decodeBits (shoupBinField k hk) m 1 T a) = a :=
  answerBits_decodeBits k hk m 1 T a ((parser_iff_length k hk T m a).2 ha)

/-- The decoded answer has the format of the decoded question (any payloads). -/
theorem decodeBits_fmtOk (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ) (T : Ty)
    (q a : BitStr) :
    (PauliBinaryProgram.questionOfBits k hk hodd j T q).fmtOk
      (decodeBits (shoupBinField k hk) (2 ^ j) 1 T a) = true :=
  DecisionKernel.Answer.pauliDecode_format k hk hodd j T q a

/-! ## Registers of the answer bits -/

variable {N : ℕ}

/-- The register of `s` bits starting at position `o`. -/
def regAt (N o s : ℕ) : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2) :=
  LinearMap.pi fun i : Fin s => getv N (o + i)

theorem regAt_eq {v : Fin N → ZMod 2} {o o' s : ℕ} {w : BitStr} (h : Reads v o w)
    (hw : o' + s ≤ w.length) : regAt N (o + o') s v = CL.ofBits s (w.drop o') := by
  funext i
  have := h (o' + i) (by omega)
  simp only [regAt, LinearMap.pi_apply, Nat.add_assoc, this, CL.ofBits, ofBool,
    List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem ofBits_append_left (s : ℕ) (u w : BitStr) (hu : u.length = s) :
    CL.ofBits s (u ++ w) = CL.ofBits s u := by
  funext i
  simp only [CL.ofBits, List.getD_append _ _ _ _ (show (i : ℕ) < u.length by omega)]

/-- The inner product with `w`, as a linear form. -/
def dotForm {s : ℕ} (w : Fin s → ZMod 2) : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, w i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem dotForm_apply {s : ℕ} (w x : Fin s → ZMod 2) : dotForm w x = ∑ i, w i * x i :=
  rfl

variable (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) (j : ℕ)

/-- **The full Pauli register of the answer at position `o`**: the field element of entry `z`
is read at `o + z k` (`z` numbered by `cubeEnumeration`) and expanded in the self-dual normal
basis, in the numbering `registerNumbering`. -/
def pauliXProj (N o : ℕ) : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (2 ^ 2 ^ j * k) → ZMod 2) :=
  LinearMap.pi fun i =>
    LinearMap.proj ((PauliFullAnswerProgram.registerNumbering (2 ^ j) k).symm i).2 ∘ₗ
      (shoupSelfDualNormalBasis k hk hodd).equivFun.toLinearMap ∘ₗ
        fldAt k hk N (o + (cubeEnumeration (2 ^ j)
          ((PauliFullAnswerProgram.registerNumbering (2 ^ j) k).symm i).1 : ℕ) * k)

/-- **`pauliXProj` reads the kernel's register of a Pauli answer** of its label's length, in
either basis. -/
theorem pauliXProj_eq (W : Bas) {v : Fin N → ZMod 2} {o : ℕ} {a : BitStr} (h : Reads v o a)
    (ha : a.length = pauliLen (2 ^ j) k (.pauli W)) :
    pauliXProj k hk hodd j N o v =
      DecisionKernel.Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd)
        (DecisionKernel.Answer.pauliDecode (shoupBinField k hk) (2 ^ j) (.inl (.pauli W)) a) := by
  have hr := answerBits_decodeBits_of_length k hk (2 ^ j) (.pauli W) a ha
  have hf := decodeBits_format (shoupBinField k hk) (d := 1)
    (Question.pauli W : Question (shoupBinField k hk).carrier (2 ^ j)) a
  obtain ⟨g, hg⟩ := eq_pauliAns_of_fmtOk hf
  change decodeBits (shoupBinField k hk) (2 ^ j) 1 (.pauli W) a = _ at hg
  change _ = DecisionKernel.Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd)
    (decodeBits (shoupBinField k hk) (2 ^ j) 1 (.pauli W) a)
  rw [hg] at hr ⊢
  rw [← hr] at h
  funext i
  simp only [pauliXProj, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.coe_proj, Function.eval, read_pauliAns h, DecisionKernel.Answer.pauliProject,
    PauliFullAnswerProgram.registerVector]

/-! ## The checks -/

/-- The checks of the first hiding edge, for a Pauli answer at `oP` and a Hide answer
`(y, y', x)` at `oH`, its registers at `oH`, `oH + Q`, `oH + 2Q`. -/
def hideChecks (N oP oH : ℕ) {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) : List (LinCheck N) :=
  gens.map (fun z => ⟨dotForm (CL.proj (P.factorOfPrefix 0 0) z) ∘ₗ
      (pauliXProj k hk hodd j N oP + regAt N (oH + 2 ^ 2 ^ j * k) (2 ^ 2 ^ j * k)), 0⟩) ++
    ((List.finRange (2 ^ 2 ^ j * k)).filter fun i => decide (i ∉ P.factorOfPrefix 0 0)).map
      fun i => ⟨LinearMap.proj i ∘ₗ (pauliXProj k hk hodd j N oP +
        regAt N (oH + 2 * (2 ^ 2 ^ j * k)) (2 ^ 2 ^ j * k)), 0⟩

/-- **The checks of the first hiding edge hold exactly when `hidingPauli` does**, for registers
read off the bit vector. -/
theorem hideChecks_iff {N oP oH ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂))
    (hgens : ∀ g ∈ gens, CLChecks.stageLinear P 0 0 g = 0)
    (hspan : ∀ z, CLChecks.stageLinear P 0 0 z = 0 →
      z ∈ Submodule.span CL.𝔽₂ {g | g ∈ gens})
    (v : Fin N → ZMod 2) (X Y Y' X' : Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)
    (hX : pauliXProj k hk hodd j N oP v = X)
    (hY' : regAt N (oH + 2 ^ 2 ^ j * k) (2 ^ 2 ^ j * k) v = Y')
    (hX' : regAt N (oH + 2 * (2 ^ 2 ^ j * k)) (2 ^ 2 ^ j * k) v = X') :
    (∀ χ ∈ hideChecks k hk hodd j N oP oH P gens, χ.Holds v) ↔
      AuxiliaryQuotient.hidingPauli P X (Y, Y', X') := by
  simp only [hideChecks, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  have hsplit : ∀ (p q : LinCheck N → Prop), (∀ χ, p χ ∨ q χ → χ.Holds v) ↔
      (∀ χ, p χ → χ.Holds v) ∧ (∀ χ, q χ → χ.Holds v) :=
    fun p q => ⟨fun h => ⟨fun χ hp => h χ (.inl hp), fun χ hq => h χ (.inr hq)⟩,
      fun h χ hpq => hpq.elim (h.1 χ) (h.2 χ)⟩
  rw [hsplit]
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, LinCheck.Holds,
    LinearMap.comp_apply, LinearMap.add_apply, hX, hY', hX', dotForm_apply, LinearMap.coe_proj,
    Function.eval, Pi.add_apply]
  unfold AuxiliaryQuotient.hidingPauli AuxiliaryDual.stageDual
  dsimp only
  rw [AuxiliaryDual.registerDual_eq_iff_dot]
  apply and_congr
  · have key : ∀ z : Fin (2 ^ 2 ^ j * k) → CL.𝔽₂,
        ∑ i, CL.proj (P.factorOfPrefix 0 0) z i * (X i + Y' i) =
          ∑ i, z i * CL.proj (P.factorOfPrefix 0 0) (Y' - X) i := by
      intro z
      rw [← sum_proj_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.sub_apply, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm (Y' i)]
    simp only [key]
    constructor
    · intro h z hz
      let φ : (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂) →ₗ[CL.𝔽₂] CL.𝔽₂ :=
        dotForm (CL.proj (P.factorOfPrefix 0 0) (Y' - X))
      have hker : Submodule.span CL.𝔽₂ {g | g ∈ gens} ≤ LinearMap.ker φ := by
        rw [Submodule.span_le]
        intro g hg
        change ∑ i, CL.proj (P.factorOfPrefix 0 0) (Y' - X) i * g i = 0
        simpa [mul_comm] using h g hg
      have := hker (hspan z hz)
      rw [LinearMap.mem_ker] at this
      change ∑ i, CL.proj (P.factorOfPrefix 0 0) (Y' - X) i * z i = 0 at this
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · intro h z hz
      exact h z (hgens z hz)
  · constructor
    · intro h
      funext i
      simp only [CL.proj_apply, Finset.mem_compl]
      split_ifs with hi
      · rfl
      · exact (zmod2_add_eq_zero _ _).1 (h i hi)
    · intro h i hi
      have := congrFun h i
      simp only [CL.proj_apply, Finset.mem_compl, hi, not_false_eq_true, ite_true] at this
      rw [zmod2_add_eq_zero]
      exact this

/-! ## The constraints of the two orientations -/

/-- **The constraints of the first hiding edge, Pauli answer first**: the Pauli answer has
`Q = 2^(2^j) k` bits and the Hide answer `3Q`. -/
def pauliHideCons {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) : List BitStr :=
  (hideChecks k hk hodd j (4 * (2 ^ 2 ^ j * k)) 0 (2 ^ 2 ^ j * k) P gens).map LinCheck.toCon

/-- **The constraints of the first hiding edge, Hide answer first.** -/
def pauliHideConsRev {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) : List BitStr :=
  (hideChecks k hk hodd j (4 * (2 ^ 2 ^ j * k)) (3 * (2 ^ 2 ^ j * k)) 0 P gens).map
    LinCheck.toCon

theorem length_of_mem_pauliHideCons {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) {c : BitStr}
    (hc : c ∈ pauliHideCons k hk hodd j P gens) :
    c.length = pauliLen (2 ^ j) k (.pauli .X) + 3 * (2 ^ 2 ^ j * k) + 1 := by
  obtain ⟨χ, -, rfl⟩ := List.mem_map.1 hc
  rw [LinCheck.length_toCon, pauliLen_pauli]
  ring

theorem length_of_mem_pauliHideConsRev {ℓ : ℕ}
    (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) {c : BitStr}
    (hc : c ∈ pauliHideConsRev k hk hodd j P gens) :
    c.length = 3 * (2 ^ 2 ^ j * k) + pauliLen (2 ^ j) k (.pauli .X) + 1 := by
  obtain ⟨χ, -, rfl⟩ := List.mem_map.1 hc
  rw [LinCheck.length_toCon, pauliLen_pauli]
  ring

/-- The Hide registers read off a Hide answer at `oH`. -/
theorem hide_regs {v : Fin N → ZMod 2} {oH Q : ℕ} {y y' x : BitStr}
    (h : Reads v oH (y ++ y' ++ x))
    (hy : y.length = Q) (hy' : y'.length = Q) (hx : x.length = Q) :
    regAt N (oH + Q) Q v = CL.ofBits Q y' ∧ regAt N (oH + 2 * Q) Q v = CL.ofBits Q x := by
  constructor
  · rw [regAt_eq h (by simp; omega), List.append_assoc, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append, ofBits_append_left Q _ _ hy']
  · rw [regAt_eq h (by simp; omega), List.drop_append_of_le_length (by simp; omega)]
    rw [List.drop_eq_nil_of_le (by simp; omega), List.nil_append]

/-- **The first hiding edge as linear constraints, Pauli answer first.** -/
theorem pauliHideCons_iff {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂))
    (hgens : ∀ g ∈ gens, CLChecks.stageLinear P 0 0 g = 0)
    (hspan : ∀ z, CLChecks.stageLinear P 0 0 z = 0 →
      z ∈ Submodule.span CL.𝔽₂ {g | g ∈ gens})
    (a y y' x : BitStr) (ha : a.length = pauliLen (2 ^ j) k (.pauli .X))
    (hy : y.length = 2 ^ 2 ^ j * k) (hy' : y'.length = 2 ^ 2 ^ j * k)
    (hx : x.length = 2 ^ 2 ^ j * k) :
    (∀ c ∈ pauliHideCons k hk hodd j P gens, Satisfies c (a ++ (y ++ y' ++ x) ++ [true])) ↔
      AuxiliaryQuotient.hidingPauli P
        (DecisionKernel.Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd)
          (DecisionKernel.Answer.pauliDecode (shoupBinField k hk) (2 ^ j) (.inl (.pauli .X)) a))
        (CL.ofBits _ y, CL.ofBits _ y', CL.ofBits _ x) := by
  rw [pauliLen_pauli] at ha
  have hN : (a ++ (y ++ y' ++ x)).length = 4 * (2 ^ 2 ^ j * k) := by simp; omega
  simp only [pauliHideCons, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [forall₂_congr fun χ _ => satisfies_toCon_iff χ _ hN]
  have hA := reads_left a (y ++ y' ++ x) hN.le
  have hB := reads_right a (y ++ y' ++ x) hN.le
  rw [ha] at hB
  obtain ⟨h1, h2⟩ := hide_regs hB hy hy' hx
  exact hideChecks_iff k hk hodd j P gens hgens hspan _ _ _ _ _
    (pauliXProj_eq k hk hodd j .X hA (by rw [ha, pauliLen_pauli])) h1 h2

/-- **The first hiding edge as linear constraints, Hide answer first.** -/
theorem pauliHideConsRev_iff {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂))
    (hgens : ∀ g ∈ gens, CLChecks.stageLinear P 0 0 g = 0)
    (hspan : ∀ z, CLChecks.stageLinear P 0 0 z = 0 →
      z ∈ Submodule.span CL.𝔽₂ {g | g ∈ gens})
    (a y y' x : BitStr) (ha : a.length = pauliLen (2 ^ j) k (.pauli .X))
    (hy : y.length = 2 ^ 2 ^ j * k) (hy' : y'.length = 2 ^ 2 ^ j * k)
    (hx : x.length = 2 ^ 2 ^ j * k) :
    (∀ c ∈ pauliHideConsRev k hk hodd j P gens, Satisfies c ((y ++ y' ++ x) ++ a ++ [true])) ↔
      AuxiliaryQuotient.hidingPauli P
        (DecisionKernel.Answer.pauliProject (shoupSelfDualNormalBasis k hk hodd)
          (DecisionKernel.Answer.pauliDecode (shoupBinField k hk) (2 ^ j) (.inl (.pauli .X)) a))
        (CL.ofBits _ y, CL.ofBits _ y', CL.ofBits _ x) := by
  have ha' := ha
  rw [pauliLen_pauli] at ha'
  have hN : ((y ++ y' ++ x) ++ a).length = 4 * (2 ^ 2 ^ j * k) := by simp; omega
  simp only [pauliHideConsRev, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  rw [forall₂_congr fun χ _ => satisfies_toCon_iff χ _ hN]
  have hB := reads_left (y ++ y' ++ x) a hN.le
  have hA := reads_right (y ++ y' ++ x) a hN.le
  have hl : (y ++ y' ++ x).length = 3 * (2 ^ 2 ^ j * k) := by simp; omega
  rw [hl] at hA
  obtain ⟨h1, h2⟩ := hide_regs hB hy hy' hx
  exact hideChecks_iff k hk hodd j P gens hgens hspan _ _ _ _ _
    (pauliXProj_eq k hk hodd j .X hA ha) h1 h2

end MIPRE.Tailored.Intro.PauliHide

end

end
