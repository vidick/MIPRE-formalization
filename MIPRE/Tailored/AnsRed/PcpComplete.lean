/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.PcpSound
public import MIPRE.Foundations.LowDegree.ZeroCertificate
public import MIPRE.TM.CookLevin.PcpClauses

@[expose] public section

/-!
# The completeness of the PCP

The completeness half of prop:completeness_and_soundness_of_PCP_for_V_n. `induce` is the
paper's `Induce_C` (Definition defn:inducing_to_a_PCP, II:9081): from Boolean readable tables
(the cells of the two readable answers, the table `O`, the three witness blocks) and
`F₂`-valued linear tables (the cells of the two linear answers, the three copies), the
assignments are the low-degree encodings of the tables (`encTbl`, the paper's `Ind`) and the
helpers are linear certificates (`MIPRE.LowDegree.cert`) of the polynomials the checks compare
with certificate sums.

* The assignment checks hold identically, always (`assignChecks_induce`).
* The formula check holds identically when the window tables satisfy the formula the circuit
  describes (`formulaCheck_induce`): at a Boolean point where the circuit polynomial is `1`, the
  circuit accepts the clause the point's inputs hold, and a literal of it is true.
* The system check holds identically when the linear tables satisfy the system the table of `O`
  holds (`systemCheck_induce`).
* The PCP has degree `17` (`indDeg_induce`), its readable part depends only on the readable
  tables (`readable_induce`), and its linear part is `F₂`-affine in the linear tables
  (`linear_induce_add`): the encodings are linear, the system polynomial affine, and
  `g ↦ g (1 - g)` additive in characteristic `2`, all composed with the linear `cert`.

The certificate degrees are crude bounds (each factor counted separately): `17` for the formula
polynomial, `3` for the system polynomial, `2` for an assignment.
-/

namespace MIPRE.Tailored.AnsRed

open MvPolynomial LowDegree SAT

variable {F : Type*} [Field F] {L : PcpDims}

/-! ## Encoding tables -/

/-- **The low-degree encoding of a table** on `ℕ` (the paper's `Ind`): the multilinear polynomial
whose value at the binary digits of `c < 2^k` is the table's value at `c`. -/
noncomputable def encTbl (k : ℕ) (t : ℕ → F) : MvPolynomial (Fin k) F :=
  ldEnc fun y => t (cubeIndex y)

/-- The encoding of a Boolean table. -/
noncomputable def encB (k : ℕ) (t : ℕ → Bool) : MvPolynomial (Fin k) F :=
  encTbl k fun c => ofBool (t c)

/-- The encoding of an `F₂`-valued table. -/
noncomputable def encZ [CharP F 2] (k : ℕ) (f : ℕ → ZMod 2) : MvPolynomial (Fin k) F :=
  encTbl k fun c => ZMod.castHom (dvd_refl 2) F (f c)

theorem eval_pt_encTbl {k : ℕ} (t : ℕ → F) (y : Fin k → Bool) :
    eval (pt y) (encTbl k t) = t (cubeIndex y) :=
  eval_ldEnc _ y

theorem eval_bitPt_encTbl {k : ℕ} (t : ℕ → F) {c : ℕ} (hc : c < 2 ^ k) :
    eval (bitPt k c) (encTbl k t) = t c := by
  have : (bitPt k c : Fin k → F) = pt (indexCube (⟨c, hc⟩ : Fin (2 ^ k))) := rfl
  rw [this, eval_pt_encTbl, cubeIndex_indexCube]

theorem degreeOf_encTbl_le {k : ℕ} (t : ℕ → F) (i : Fin k) : (encTbl k t).degreeOf i ≤ 1 :=
  degreeOf_ldEnc_le _ i

theorem encTbl_add {k : ℕ} (t₁ t₂ : ℕ → F) :
    encTbl k (fun c => t₁ c + t₂ c) = encTbl k t₁ + encTbl k t₂ := by
  simp only [encTbl, ldEnc, map_add, add_mul, Finset.sum_add_distrib]

theorem isAssignment_encB {k : ℕ} (t : ℕ → Bool) :
    IsAssignment (encB k t : MvPolynomial (Fin k) F) := by
  intro y
  rw [encB, eval_pt_encTbl]
  cases t (cubeIndex y) <;> simp [ofBool]

theorem isAssignment_encZ [CharP F 2] {k : ℕ} (f : ℕ → ZMod 2) :
    IsAssignment (encZ k f : MvPolynomial (Fin k) F) := by
  intro y
  rw [encZ, eval_pt_encTbl]
  generalize f (cubeIndex y) = z
  fin_cases z
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

/-- The table of the encoding of a Boolean table is the table. -/
theorem res_encB {k : ℕ} (t : ℕ → Bool) {c : ℕ} (hc : c < 2 ^ k) :
    res (encB k t : MvPolynomial (Fin k) F) c = t c := by
  unfold res
  rw [encB, eval_bitPt_encTbl _ hc]
  cases t c <;> simp [ofBool]

/-- The `F₂`-table of the encoding of an `F₂`-valued table is the table. -/
theorem resZ_encZ [CharP F 2] {k : ℕ} (f : ℕ → ZMod 2) {c : ℕ} (hc : c < 2 ^ k) :
    resZ (encZ k f : MvPolynomial (Fin k) F) c = f c := by
  unfold resZ res
  rw [encZ, eval_bitPt_encTbl _ hc]
  generalize f c = z
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
  · simp [ofBool]
  · simp [ofBool]

theorem encZ_add [CharP F 2] {k : ℕ} (f₁ f₂ : ℕ → ZMod 2) :
    (encZ k (f₁ + f₂) : MvPolynomial (Fin k) F) = encZ k f₁ + encZ k f₂ := by
  simp only [encZ, Pi.add_apply, map_add]
  exact encTbl_add _ _

theorem testBit_cubeIndex {k : ℕ} (f : Fin k → Bool) {t : ℕ} (ht : t < k) :
    (cubeIndex f : ℕ).testBit t = f ⟨t, ht⟩ :=
  congrFun (indexCube_cubeIndex f) ⟨t, ht⟩

theorem pt_eq_bitPt_cubeIndex {k : ℕ} (y : Fin k → Bool) :
    (pt y : Fin k → F) = bitPt k (cubeIndex y) := by
  conv_lhs => rw [← indexCube_cubeIndex y]
  rfl

/-! ## Certificates of assignments -/

theorem degreeOf_mul_one_sub_le {k : ℕ} {g : MvPolynomial (Fin k) F}
    (hg : ∀ i, g.degreeOf i ≤ 1) (i : Fin k) : (g * (1 - g)).degreeOf i ≤ 2 := by
  have h1 := degreeOf_mul_le i g (1 - g)
  have h2 := (degreeOf_one_sub_le g i).trans (hg i)
  have h3 := hg i
  omega

/-- The certificates of an assignment: linear certificates of `g (1 - g)`. -/
noncomputable def assignCert {k : ℕ} (g : MvPolynomial (Fin k) F) :
    Fin k → MvPolynomial (Fin k) F :=
  cert k 2 (g * (1 - g))

theorem eval_certSum_eq {k d : ℕ} {f : MvPolynomial (Fin k) F} (hf : f ∈ cubeVanishing k d)
    (x : Fin k → F) : ∑ i, x i * (1 - x i) * eval x (cert k d f i) = eval x f := by
  have h := congrArg (eval x) (cert_sum hf)
  simp only [map_sum, map_mul, cubeZero, map_sub, map_one, eval_X] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The assignment check of an assignment of degree at most `1` holds identically** with its
linear certificates (the Combinatorial Nullstellensatz, claim:combi_null). -/
theorem assignCheck_assignCert {k : ℕ} {g : MvPolynomial (Fin k) F} (hg : IsAssignment g)
    (hd : ∀ i, g.degreeOf i ≤ 1) (x : Fin k → F) : AssignCheck g (assignCert g) x := by
  have hmem : g * (1 - g) ∈ cubeVanishing k 2 := by
    refine mem_cubeVanishing.2 ⟨degreeOf_mul_one_sub_le hd, fun y => ?_⟩
    rw [map_mul, map_sub, map_one]
    rcases hg y with h | h <;> rw [h] <;> ring
  unfold AssignCheck assignCert
  rw [eval_certSum_eq hmem, map_mul, map_sub, map_one]

theorem assignCert_add [CharP F 2] {k : ℕ} (g₁ g₂ : MvPolynomial (Fin k) F) :
    assignCert (g₁ + g₂) = assignCert g₁ + assignCert g₂ := by
  have h2 : (2 : MvPolynomial (Fin k) F) = 0 := CharTwo.two_eq_zero
  have : (g₁ + g₂) * (1 - (g₁ + g₂)) = g₁ * (1 - g₁) + g₂ * (1 - g₂) := by
    linear_combination (-(g₁ * g₂)) * h2
  unfold assignCert
  rw [this, map_add]

/-! ## The polynomials the checks compare with certificate sums -/

/-- The formula polynomial: the circuit polynomial times the six literal factors. -/
noncomputable def formulaPoly (T : MvPolynomial (Fin L.m) F) (gA gB : MvPolynomial (Fin L.ℓ) F)
    (gO : MvPolynomial (Fin L.oW) F) (gW : Fin 3 → MvPolynomial (Fin L.r) F) :
    MvPolynomial (Fin L.m) F :=
  T * (X L.πA * rename L.vA gA - X (L.sgn 0)) * (X L.πB * rename L.vB gB - X (L.sgn 1)) *
    (X L.πC * rename L.vO gO - X (L.sgn 2)) *
    ∏ k : Fin 3, (rename (L.vW k) (gW k) - X (L.sgn (3 + k.castLE (by omega))))

/-- The system polynomial: the table `O` times the equation. -/
noncomputable def systemPoly (gO : MvPolynomial (Fin L.oW) F) (gLa gLb : MvPolynomial (Fin L.ℓ) F)
    (gL : Fin 3 → MvPolynomial (Fin L.dm) F) : MvPolynomial (Fin L.oW) F :=
  gO * (X (L.oSgn 0) * rename L.oA gLa + X (L.oSgn 1) * rename L.oB gLb +
    ∑ k : Fin 3, X (L.oSgn (2 + k.castLE (by omega))) * rename (L.oL k) (gL k) - X (L.oSgn 5))

theorem formulaCheck_iff_formulaPoly (T : MvPolynomial (Fin L.m) F) (P : Pcp L F)
    (p : Fin L.m → F) :
    FormulaCheck T P p ↔
      eval p (formulaPoly T P.gA P.gB P.gO P.gW) = ∑ X, p X * (1 - p X) * eval p (P.αR X) := by
  simp only [FormulaCheck, formulaPoly, eval_rename, map_sub, map_mul, map_prod, eval_X]

theorem systemCheck_iff_systemPoly (P : Pcp L F) (x : Fin L.oW → F) :
    SystemCheck P x ↔
      eval x (systemPoly P.gO P.gLa P.gLb P.gL) = ∑ X, x X * (1 - x X) * eval x (P.αL X) := by
  simp only [SystemCheck, systemPoly, eval_rename, map_sub, map_mul, map_add, map_sum, eval_X]

theorem degreeOf_formulaPoly_le {T : MvPolynomial (Fin L.m) F} (hT : ∀ i, T.degreeOf i ≤ 5)
    {gA gB : MvPolynomial (Fin L.ℓ) F} {gO : MvPolynomial (Fin L.oW) F}
    {gW : Fin 3 → MvPolynomial (Fin L.r) F} (hA : ∀ i, gA.degreeOf i ≤ 1)
    (hB : ∀ i, gB.degreeOf i ≤ 1) (hO : ∀ i, gO.degreeOf i ≤ 1) (hW : ∀ k i, (gW k).degreeOf i ≤ 1)
    (i : Fin L.m) : (formulaPoly T gA gB gO gW).degreeOf i ≤ 17 := by
  unfold formulaPoly
  have fA := (degreeOf_litFactor_le L.vA_injective hA L.πA (L.sgn 0) i).1
  have fB := (degreeOf_litFactor_le L.vB_injective hB L.πB (L.sgn 1) i).1
  have fO := (degreeOf_litFactor_le L.vO_injective hO L.πC (L.sgn 2) i).1
  have fW : (∏ k : Fin 3, (rename (L.vW k) (gW k) - X (L.sgn (3 + k.castLE (by omega)))) :
      MvPolynomial (Fin L.m) F).degreeOf i ≤ 3 * 2 := by
    refine (degreeOf_prod_le i _ _).trans ?_
    calc ∑ k : Fin 3, (rename (L.vW k) (gW k) -
          X (L.sgn (3 + k.castLE (by omega))) : MvPolynomial (Fin L.m) F).degreeOf i
        ≤ ∑ _k : Fin 3, 2 := Finset.sum_le_sum fun k _ =>
          (degreeOf_litFactor_le (L.vW_injective k) (hW k) L.πA _ i).2
      _ = 3 * 2 := by simp
  have m1 := degreeOf_mul_le i T (X L.πA * rename L.vA gA - X (L.sgn 0))
  have m2 := degreeOf_mul_le i (T * (X L.πA * rename L.vA gA - X (L.sgn 0)))
    (X L.πB * rename L.vB gB - X (L.sgn 1))
  have m3 := degreeOf_mul_le i (T * (X L.πA * rename L.vA gA - X (L.sgn 0)) *
    (X L.πB * rename L.vB gB - X (L.sgn 1))) (X L.πC * rename L.vO gO - X (L.sgn 2))
  refine (degreeOf_mul_le i _ _).trans ?_
  have := hT i
  omega

theorem degreeOf_systemPoly_le {gO : MvPolynomial (Fin L.oW) F}
    {gLa gLb : MvPolynomial (Fin L.ℓ) F} {gL : Fin 3 → MvPolynomial (Fin L.dm) F}
    (hO : ∀ i, gO.degreeOf i ≤ 1) (hLa : ∀ i, gLa.degreeOf i ≤ 1) (hLb : ∀ i, gLb.degreeOf i ≤ 1)
    (hL : ∀ k i, (gL k).degreeOf i ≤ 1) (i : Fin L.oW) :
    (systemPoly gO gLa gLb gL).degreeOf i ≤ 3 := by
  unfold systemPoly
  refine (degreeOf_mul_le i _ _).trans ?_
  have hO' := hO i
  have hlin : (X (L.oSgn 0) * rename L.oA gLa + X (L.oSgn 1) * rename L.oB gLb +
      ∑ k : Fin 3, X (L.oSgn (2 + k.castLE (by omega))) * rename (L.oL k) (gL k) -
      X (L.oSgn 5) : MvPolynomial (Fin L.oW) F).degreeOf i ≤ 2 := by
    refine (degreeOf_sub_le i _ _).trans (max_le ?_ ((degreeOf_X_le _ i).trans (by omega)))
    refine (degreeOf_add_le i _ _).trans (max_le ((degreeOf_add_le i _ _).trans
      (max_le ?_ ?_)) ?_)
    · refine (degreeOf_mul_le i _ _).trans ?_
      have := degreeOf_X_le (F := F) (L.oSgn 0) i
      have := degreeOf_rename_le_of_injective L.oA_injective hLa i
      omega
    · refine (degreeOf_mul_le i _ _).trans ?_
      have := degreeOf_X_le (F := F) (L.oSgn 1) i
      have := degreeOf_rename_le_of_injective L.oB_injective hLb i
      omega
    · refine (degreeOf_sum_le i _ _).trans (Finset.sup_le fun k _ => ?_)
      refine (degreeOf_mul_le i _ _).trans ?_
      have := degreeOf_X_le (F := F) (L.oSgn (2 + k.castLE (by omega))) i
      have := degreeOf_rename_le_of_injective (L.oL_injective k) (hL k) i
      omega
  omega

/-! ## The clause a Boolean point holds -/

section clause

theorem lt_m_of_lt_nIn {w : ℕ} (h : w < L.nIn) : w < L.m := lt_of_lt_of_le h L.nIn_le_m

variable (L) in
/-- The clause whose input the Boolean point `y` holds on its input wires. -/
def clauseOf (y : Fin L.m → Bool) : PcpClause L where
  l₁ := ⟨cubeIndex fun t : Fin (L.ℓ + 1) =>
    y ⟨t, lt_m_of_lt_nIn (by have := t.2; rw [nIn_eq]; omega)⟩, y (L.sgn 0)⟩
  l₂ := ⟨cubeIndex fun t : Fin (L.ℓ + 1) =>
    y ⟨L.ℓ + 1 + t, lt_m_of_lt_nIn (by have := t.2; rw [nIn_eq]; omega)⟩, y (L.sgn 1)⟩
  l₃ := ⟨cubeIndex fun t : Fin (L.oW + 1) =>
    y ⟨L.ℓ + 1 + (L.ℓ + 1) + t, lt_m_of_lt_nIn (by have := t.2; rw [nIn_eq]; omega)⟩, y (L.sgn 2)⟩
  l₄ := ⟨cubeIndex fun t : Fin L.r => y (L.vW 0 t), y (L.sgn 3)⟩
  l₅ := ⟨cubeIndex fun t : Fin L.r => y (L.vW 1 t), y (L.sgn 4)⟩
  l₆ := ⟨cubeIndex fun t : Fin L.r => y (L.vW 2 t), y (L.sgn 5)⟩

/-- **A Boolean point holds the input of the clause read off its input wires.** -/
theorem inputsAt_clauseOf (y : Fin L.m → Bool) : InputsAt y (clauseOf L y) := by
  intro w hw
  rw [nIn_eq] at hw
  by_cases h1 : (w : ℕ) < L.ℓ + 1
  · rw [getD_clauseInput6_one _ h1]
    simp only [clauseOf]
    rw [testBit_cubeIndex _ h1]
  by_cases h2 : (w : ℕ) < L.ℓ + 1 + (L.ℓ + 1)
  · rw [getD_clauseInput6_two _ (t := w - (L.ℓ + 1)) (by omega) (by omega)]
    simp only [clauseOf]
    rw [testBit_cubeIndex _ (by omega)]
    exact congrArg y (Fin.ext (by simp only; omega))
  by_cases h3 : (w : ℕ) < L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1)
  · rw [getD_clauseInput6_three _ (t := w - (L.ℓ + 1 + (L.ℓ + 1))) (by omega) (by omega)]
    simp only [clauseOf]
    rw [testBit_cubeIndex _ (by omega)]
    exact congrArg y (Fin.ext (by simp only; omega))
  by_cases h4 : (w : ℕ) < L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + L.r
  · rw [getD_clauseInput6_four _ (t := w - (L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1))) (by omega)
      (by omega)]
    simp only [clauseOf]
    rw [testBit_cubeIndex _ (by omega)]
    exact congrArg y (Fin.ext (by simp only [PcpDims.val_vW]; simp; omega))
  by_cases h5 : (w : ℕ) < L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + L.r + L.r
  · rw [getD_clauseInput6_five _ (t := w - (L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + L.r)) (by omega)
      (by omega)]
    simp only [clauseOf]
    rw [testBit_cubeIndex _ (by omega)]
    exact congrArg y (Fin.ext (by simp only [PcpDims.val_vW]; simp; omega))
  by_cases h6 : (w : ℕ) < L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + L.r + L.r + L.r
  · rw [getD_clauseInput6_six _
      (t := w - (L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + L.r + L.r)) (by omega) (by omega)]
    simp only [clauseOf]
    rw [testBit_cubeIndex _ (by omega)]
    exact congrArg y (Fin.ext (by simp only [PcpDims.val_vW]; simp; omega))
  obtain ⟨k, hk, hwk⟩ : ∃ k, k < 6 ∧
      (w : ℕ) = L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + L.r + L.r + L.r + k :=
    ⟨w - (L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + L.r + L.r + L.r), by omega, by omega⟩
  rw [getD_clauseInput6_sgn _ hwk]
  have hw' : w = L.sgn ⟨k, hk⟩ := Fin.ext (by rw [PcpDims.val_sgn]; simp only; omega)
  rw [hw']
  interval_cases k <;> rfl

end clause

/-! ## The honest PCP -/

/-- The readable tables of the honest PCP: the cells of the two readable answers, the table `O`
and the three witness blocks. -/
structure RTables where
  tA : ℕ → Bool
  tB : ℕ → Bool
  tO : ℕ → Bool
  tW : Fin 3 → ℕ → Bool

/-- The linear tables of the honest PCP, valued in `F₂`: the cells of the two linear answers and
the three copies. -/
structure LTables where
  fLa : ℕ → ZMod 2
  fLb : ℕ → ZMod 2
  fL : Fin 3 → ℕ → ZMod 2

instance : Add LTables := ⟨fun a b => ⟨a.fLa + b.fLa, a.fLb + b.fLb, a.fL + b.fL⟩⟩

instance : Zero LTables := ⟨⟨0, 0, 0⟩⟩

/-- The window table of a table of cells: the tape encoding, `π · t(cell)` at the index of
parity `π`. -/
def winOf (t : ℕ → Bool) (j : ℕ) : Bool := j.testBit 0 && t (j / 2)

/-- The table of a string of `2^k` bits. -/
def tblStr (k : ℕ) (t : ℕ → Bool) : Cost.BitStr := List.ofFn fun c : Fin (2 ^ k) => t c

variable [CharP F 2]

variable (L) in
/-- **The honest PCP** (`Induce_C`, Definition defn:inducing_to_a_PCP) of the circuit polynomial
`T`: the encodings of the tables, and linear certificates of the formula polynomial, of the
system polynomial and of the assignments. -/
noncomputable def induce (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt : LTables) : Pcp L F where
  gA := encB L.ℓ R.tA
  gB := encB L.ℓ R.tB
  gO := encB L.oW R.tO
  gW k := encB L.r (R.tW k)
  gLa := encZ L.ℓ Lt.fLa
  gLb := encZ L.ℓ Lt.fLb
  gL k := encZ L.dm (Lt.fL k)
  αR := cert L.m 17 (formulaPoly T (encB L.ℓ R.tA) (encB L.ℓ R.tB) (encB L.oW R.tO)
    fun k => encB L.r (R.tW k))
  αL := cert L.oW 3 (systemPoly (encB L.oW R.tO) (encZ L.ℓ Lt.fLa) (encZ L.ℓ Lt.fLb)
    fun k => encZ L.dm (Lt.fL k))
  βA := assignCert (encB L.ℓ R.tA)
  βB := assignCert (encB L.ℓ R.tB)
  βO := assignCert (encB L.oW R.tO)
  βW k := assignCert (encB L.r (R.tW k))
  βLa := assignCert (encZ L.ℓ Lt.fLa)
  βLb := assignCert (encZ L.ℓ Lt.fLb)
  βL k := assignCert (encZ L.dm (Lt.fL k))

section proj

variable (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt : LTables)

@[simp] theorem induce_gA : (induce L T R Lt).gA = encB L.ℓ R.tA := rfl
@[simp] theorem induce_gB : (induce L T R Lt).gB = encB L.ℓ R.tB := rfl
@[simp] theorem induce_gO : (induce L T R Lt).gO = encB L.oW R.tO := rfl
@[simp] theorem induce_gW : (induce L T R Lt).gW = fun k => encB L.r (R.tW k) := rfl
@[simp] theorem induce_gLa : (induce L T R Lt).gLa = encZ L.ℓ Lt.fLa := rfl
@[simp] theorem induce_gLb : (induce L T R Lt).gLb = encZ L.ℓ Lt.fLb := rfl
@[simp] theorem induce_gL : (induce L T R Lt).gL = fun k => encZ L.dm (Lt.fL k) := rfl
@[simp] theorem induce_αR : (induce L T R Lt).αR = cert L.m 17 (formulaPoly T (encB L.ℓ R.tA)
    (encB L.ℓ R.tB) (encB L.oW R.tO) fun k => encB L.r (R.tW k)) := rfl
@[simp] theorem induce_αL : (induce L T R Lt).αL = cert L.oW 3 (systemPoly (encB L.oW R.tO)
    (encZ L.ℓ Lt.fLa) (encZ L.ℓ Lt.fLb) fun k => encZ L.dm (Lt.fL k)) := rfl
@[simp] theorem induce_βA : (induce L T R Lt).βA = assignCert (encB L.ℓ R.tA) := rfl
@[simp] theorem induce_βB : (induce L T R Lt).βB = assignCert (encB L.ℓ R.tB) := rfl
@[simp] theorem induce_βO : (induce L T R Lt).βO = assignCert (encB L.oW R.tO) := rfl
@[simp] theorem induce_βW :
    (induce L T R Lt).βW = fun k => assignCert (encB L.r (R.tW k)) := rfl
@[simp] theorem induce_βLa : (induce L T R Lt).βLa = assignCert (encZ L.ℓ Lt.fLa) := rfl
@[simp] theorem induce_βLb : (induce L T R Lt).βLb = assignCert (encZ L.ℓ Lt.fLb) := rfl
@[simp] theorem induce_βL :
    (induce L T R Lt).βL = fun k => assignCert (encZ L.dm (Lt.fL k)) := rfl

end proj

omit [CharP F 2] in
theorem degreeOf_encB_le {k : ℕ} (t : ℕ → Bool) (i : Fin k) :
    (encB k t : MvPolynomial (Fin k) F).degreeOf i ≤ 17 :=
  (degreeOf_encTbl_le _ i).trans (by norm_num)

theorem degreeOf_encZ_le {k : ℕ} (f : ℕ → ZMod 2) (i : Fin k) :
    (encZ k f : MvPolynomial (Fin k) F).degreeOf i ≤ 17 :=
  (degreeOf_encTbl_le _ i).trans (by norm_num)

omit [CharP F 2] in
theorem degreeOf_assignCert_le {k : ℕ} (g : MvPolynomial (Fin k) F) (j i : Fin k) :
    (assignCert g j).degreeOf i ≤ 17 :=
  (degreeOf_cert_le _ j i).trans (by norm_num)

/-- **The honest PCP has degree `17`.** -/
theorem indDeg_induce (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt : LTables) :
    (induce L T R Lt).IndDeg 17 := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun k i => ?_, fun i => ?_, fun i => ?_,
    fun k i => ?_, fun j i => ?_, fun j i => ?_, fun j i => ?_, fun j i => ?_, fun j i => ?_,
    fun k j i => ?_, fun j i => ?_, fun j i => ?_, fun k j i => ?_⟩
  · rw [induce_gA]; exact degreeOf_encB_le _ i
  · rw [induce_gB]; exact degreeOf_encB_le _ i
  · rw [induce_gO]; exact degreeOf_encB_le _ i
  · simp only [induce_gW]; exact degreeOf_encB_le _ i
  · rw [induce_gLa]; exact degreeOf_encZ_le _ i
  · rw [induce_gLb]; exact degreeOf_encZ_le _ i
  · simp only [induce_gL]; exact degreeOf_encZ_le _ i
  · rw [induce_αR]; exact degreeOf_cert_le _ j i
  · rw [induce_αL]; exact (degreeOf_cert_le _ j i).trans (by norm_num)
  · rw [induce_βA]; exact degreeOf_assignCert_le _ j i
  · rw [induce_βB]; exact degreeOf_assignCert_le _ j i
  · rw [induce_βO]; exact degreeOf_assignCert_le _ j i
  · simp only [induce_βW]; exact degreeOf_assignCert_le _ j i
  · rw [induce_βLa]; exact degreeOf_assignCert_le _ j i
  · rw [induce_βLb]; exact degreeOf_assignCert_le _ j i
  · simp only [induce_βL]; exact degreeOf_assignCert_le _ j i

/-- **The assignment checks of the honest PCP hold identically**, whatever the tables
(eq:PCP_condition_1, eq:PCP_condition_2). -/
theorem assignChecks_induce (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt : LTables) :
    (∀ x, AssignCheck (induce L T R Lt).gA (induce L T R Lt).βA x) ∧
      (∀ x, AssignCheck (induce L T R Lt).gB (induce L T R Lt).βB x) ∧
      (∀ x, AssignCheck (induce L T R Lt).gO (induce L T R Lt).βO x) ∧
      (∀ k x, AssignCheck ((induce L T R Lt).gW k) ((induce L T R Lt).βW k) x) ∧
      (∀ x, AssignCheck (induce L T R Lt).gLa (induce L T R Lt).βLa x) ∧
      (∀ x, AssignCheck (induce L T R Lt).gLb (induce L T R Lt).βLb x) ∧
      ∀ k x, AssignCheck ((induce L T R Lt).gL k) ((induce L T R Lt).βL k) x := by
  simp only [induce_gA, induce_gB, induce_gO, induce_gW, induce_gLa, induce_gLb, induce_gL,
    induce_βA, induce_βB, induce_βO, induce_βW, induce_βLa, induce_βLb, induce_βL]
  exact ⟨assignCheck_assignCert (isAssignment_encB _) (degreeOf_encTbl_le _),
    assignCheck_assignCert (isAssignment_encB _) (degreeOf_encTbl_le _),
    assignCheck_assignCert (isAssignment_encB _) (degreeOf_encTbl_le _),
    fun _ => assignCheck_assignCert (isAssignment_encB _) (degreeOf_encTbl_le _),
    assignCheck_assignCert (isAssignment_encZ _) (degreeOf_encTbl_le _),
    assignCheck_assignCert (isAssignment_encZ _) (degreeOf_encTbl_le _),
    fun _ => assignCheck_assignCert (isAssignment_encZ _) (degreeOf_encTbl_le _)⟩

/-! ## The formula and the system checks -/

/-- **The formula polynomial vanishes on the Boolean cube** when the window tables satisfy the
formula the circuit describes: where the circuit polynomial is `1`, the circuit accepts the clause
the point holds on its input wires, and the factor of a true literal of it vanishes. -/
theorem eval_formulaPoly_eq_zero {Cc : Circuit} (hWF : Cc.WellFormed) (hin : Cc.inputs = L.nIn)
    (hm : Cc.inputs + Cc.size = L.m) (R : RTables)
    (hsat : (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat (fun j => winOf R.tA j)
      (fun j => winOf R.tB j) (fun j => winOf R.tO j) (fun j => R.tW 0 j)
      (fun j => R.tW 1 j) (fun j => R.tW 2 j)) (y : Fin L.m → Bool) :
    eval (pt y : Fin L.m → F) (formulaPoly (rename (Fin.cast hm) Cc.finiteArith)
      (encB L.ℓ R.tA) (encB L.ℓ R.tB) (encB L.oW R.tO) fun k => encB L.r (R.tW k)) = 0 := by
  let z : Fin (Cc.inputs + Cc.size) → Bool := fun i => y (Fin.cast hm i)
  have hTz : eval (pt y : Fin L.m → F) (rename (Fin.cast hm) Cc.finiteArith) =
      eval (fun i => (ofBool (z i) : F)) Cc.finiteArith := by
    rw [eval_rename]; rfl
  unfold formulaPoly
  simp only [map_mul]
  rcases Circuit.eval_finiteArith_bool (F := F) Cc hWF z with h0 | h1
  · rw [hTz, h0]; ring
  have hacc : Cc.eval (Cc.inputPart z) = true :=
    (Circuit.eval_iff_exists_finiteArith (F := F) Cc hWF _).2
      ⟨z, fun i => by simp only [Circuit.inputPart, dite_eq_left i.2], h1⟩
  have hy : InputsAt y (clauseOf L y) := inputsAt_clauseOf y
  have hc : clauseOf L y ∈ Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r := by
    show Cc.evalBits _ = true
    unfold Circuit.evalBits
    rw [Cc.eval_congr hWF.inputsLt _ (Cc.inputPart z) fun i hi => ?_]
    · exact hacc
    · refine (hy ⟨i, by omega⟩ (by simp only; omega)).symm.trans ?_
      simp only [Circuit.inputPart, dite_eq_left hi]
      exact congrArg y (Fin.ext rfl)
  have hlit := hsat _ hc
  simp only [Clause6.eval, Bool.or_eq_true, lit_eval_eq_true_iff] at hlit
  set c := clauseOf L y
  have hcell : ∀ {k : ℕ} (j : Fin (2 ^ (k + 1))), (j : ℕ) / 2 < 2 ^ k := fun j =>
    (Nat.div_lt_iff_lt_mul two_pos).2 (lt_of_lt_of_eq j.2 (pow_succ _ _))
  have fac : ∀ {a b : Bool}, a = b → (ofBool a : F) - ofBool b = 0 := fun h => by
    rw [h, sub_self]
  rcases hlit with ((((hA | hB) | hC) | h₄) | h₅) | h₆
  · have h : eval (pt y : Fin L.m → F)
        (X L.πA * rename L.vA (encB L.ℓ R.tA) - X (L.sgn 0)) = 0 := by
      rw [map_sub, map_mul, eval_X, eval_X, eval_rename, pt_πA hy, pt_comp_vA hy, pt_sgn hy, encB,
        eval_bitPt_encTbl _ (hcell c.l₁.var), ofBool_mul_ofBool]
      exact fac hA
    rw [h]; ring
  · have h : eval (pt y : Fin L.m → F)
        (X L.πB * rename L.vB (encB L.ℓ R.tB) - X (L.sgn 1)) = 0 := by
      rw [map_sub, map_mul, eval_X, eval_X, eval_rename, pt_πB hy, pt_comp_vB hy, pt_sgn hy, encB,
        eval_bitPt_encTbl _ (hcell c.l₂.var), ofBool_mul_ofBool]
      exact fac hB
    rw [h]; ring
  · have h : eval (pt y : Fin L.m → F)
        (X L.πC * rename L.vO (encB L.oW R.tO) - X (L.sgn 2)) = 0 := by
      rw [map_sub, map_mul, eval_X, eval_X, eval_rename, pt_πC hy, pt_comp_vO hy, pt_sgn hy, encB,
        eval_bitPt_encTbl _ (hcell c.l₃.var), ofBool_mul_ofBool]
      exact fac hC
    rw [h]; ring
  all_goals
    rw [map_prod]
    apply mul_eq_zero_of_right
  · refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
    rw [map_sub, eval_X, eval_rename, pt_comp_vW hy, pt_sgn hy, encB,
      eval_bitPt_encTbl (c := wVar c 0) _ c.l₄.var.2]
    exact fac h₄
  · refine Finset.prod_eq_zero (Finset.mem_univ 1) ?_
    rw [map_sub, eval_X, eval_rename, pt_comp_vW hy, pt_sgn hy, encB,
      eval_bitPt_encTbl (c := wVar c 1) _ c.l₅.var.2]
    exact fac h₅
  · refine Finset.prod_eq_zero (Finset.mem_univ 2) ?_
    rw [map_sub, eval_X, eval_rename, pt_comp_vW hy, pt_sgn hy, encB,
      eval_bitPt_encTbl (c := wVar c 2) _ c.l₆.var.2]
    exact fac h₆

/-- **The formula check of the honest PCP holds identically** when the window tables satisfy the
formula the circuit describes (eq:Tseitin_satisfiable_induced): the formula polynomial, of
individual degree at most `17` and zero on the cube, is the sum of its linear certificates. -/
theorem formulaCheck_induce {Cc : Circuit} (hWF : Cc.WellFormed) (hin : Cc.inputs = L.nIn)
    (hm : Cc.inputs + Cc.size = L.m) (R : RTables) (Lt : LTables)
    (hsat : (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat (fun j => winOf R.tA j)
      (fun j => winOf R.tB j) (fun j => winOf R.tO j) (fun j => R.tW 0 j)
      (fun j => R.tW 1 j) (fun j => R.tW 2 j)) (p : Fin L.m → F) :
    FormulaCheck (rename (Fin.cast hm) Cc.finiteArith)
      (induce L (rename (Fin.cast hm) Cc.finiteArith) R Lt) p := by
  have hT : ∀ i, (rename (Fin.cast hm) (Cc.finiteArith (F := F))).degreeOf i ≤ 5 :=
    degreeOf_rename_le_of_injective (Fin.cast_injective hm)
      (Circuit.degreeOf_finiteArith_le Cc hWF)
  have hmem : formulaPoly (rename (Fin.cast hm) Cc.finiteArith) (encB L.ℓ R.tA) (encB L.ℓ R.tB)
      (encB L.oW R.tO) (fun k => encB L.r (R.tW k)) ∈ cubeVanishing (F := F) L.m 17 :=
    mem_cubeVanishing.2 ⟨degreeOf_formulaPoly_le hT (degreeOf_encTbl_le _)
      (degreeOf_encTbl_le _) (degreeOf_encTbl_le _) (fun _ => degreeOf_encTbl_le _),
      eval_formulaPoly_eq_zero hWF hin hm R hsat⟩
  rw [formulaCheck_iff_formulaPoly, induce_gA, induce_gB, induce_gO, induce_gW, induce_αR]
  exact (eval_certSum_eq hmem p).symm

/-- **The system polynomial vanishes on the Boolean cube** when the linear tables satisfy the
system the table of `O` holds: where `O` is `1`, the equation holds in `F₂`, hence in `F`. -/
theorem eval_systemPoly_eq_zero (R : RTables) (Lt : LTables)
    (htab : TableSat (2 ^ L.ℓ) (2 ^ L.dm) (tblStr L.oW R.tO) Lt.fLa Lt.fLb (Lt.fL 0) (Lt.fL 1)
      (Lt.fL 2)) (x : Fin L.oW → Bool) :
    eval (pt x : Fin L.oW → F) (systemPoly (encB L.oW R.tO) (encZ L.ℓ Lt.fLa) (encZ L.ℓ Lt.fLb)
      fun k => encZ L.dm (Lt.fL k)) = 0 := by
  have hu : (cubeIndex x : ℕ) < 2 ^ L.oW := (cubeIndex x).2
  rw [pt_eq_bitPt_cubeIndex]
  generalize (cubeIndex x : ℕ) = u at hu
  have hN : 0 < 2 ^ L.ℓ := Nat.two_pow_pos _
  have hD : 0 < 2 ^ L.dm := Nat.two_pow_pos _
  unfold systemPoly
  simp only [map_mul, map_sub, map_add, eval_X, eval_rename, Fin.sum_univ_three]
  rw [encB, eval_bitPt_encTbl _ hu]
  cases hO : R.tO u
  · simp [ofBool]
  have heq := htab u (by rw [tableSize_eq_oW]; exact hu) (by
    rw [List.getD_eq_getElem?_getD, tblStr, List.getElem?_ofFn]
    simp [hu, hO])
  rw [bitPt_comp_oA, bitPt_comp_oB, bitPt_comp_oL₀, bitPt_comp_oL₁, bitPt_comp_oL₂,
    bitPt_oSgn, bitPt_oSgn, bitPt_oSgn, bitPt_oSgn, bitPt_oSgn, bitPt_oSgn, encZ, encZ, encZ,
    encZ, encZ, eval_bitPt_encTbl (c := idxA (2 ^ L.ℓ) u) _ (Nat.mod_lt _ hN),
    eval_bitPt_encTbl (c := idxB (2 ^ L.ℓ) u) _ (Nat.mod_lt _ hN),
    eval_bitPt_encTbl (c := idx₁ (2 ^ L.ℓ) (2 ^ L.dm) u) _ (Nat.mod_lt _ hD),
    eval_bitPt_encTbl (c := idx₂ (2 ^ L.ℓ) (2 ^ L.dm) u) _ (Nat.mod_lt _ hD),
    eval_bitPt_encTbl (c := idx₃ (2 ^ L.ℓ) (2 ^ L.dm) u) _ (Nat.mod_lt _ hD)]
  have h := congrArg (ZMod.castHom (dvd_refl 2) F) heq
  simp only [sgn, map_add, map_mul, castHom_ofBool] at h
  have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  have h30 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have h31 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have h32 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [val_two_add_castLE, h5, h30, h31, h32, Fin.val_zero, Fin.val_one, ofBool, ite_true,
    one_mul] at h ⊢
  unfold idxA idxB idx₁ idx₂ idx₃ at h ⊢
  linear_combination h

/-- **The system check of the honest PCP holds identically** when the linear tables satisfy the
system the table of `O` holds (eq:induced_system_is_satisfied). -/
theorem systemCheck_induce (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt : LTables)
    (htab : TableSat (2 ^ L.ℓ) (2 ^ L.dm) (tblStr L.oW R.tO) Lt.fLa Lt.fLb (Lt.fL 0) (Lt.fL 1)
      (Lt.fL 2)) (x : Fin L.oW → F) : SystemCheck (induce L T R Lt) x := by
  have hmem : systemPoly (encB L.oW R.tO) (encZ L.ℓ Lt.fLa) (encZ L.ℓ Lt.fLb)
      (fun k => encZ L.dm (Lt.fL k)) ∈ cubeVanishing (F := F) L.oW 3 :=
    mem_cubeVanishing.2 ⟨degreeOf_systemPoly_le (degreeOf_encTbl_le _) (degreeOf_encTbl_le _)
      (degreeOf_encTbl_le _) (fun _ => degreeOf_encTbl_le _), eval_systemPoly_eq_zero R Lt htab⟩
  rw [systemCheck_iff_systemPoly, induce_gO, induce_gLa, induce_gLb, induce_gL, induce_αL]
  exact (eval_certSum_eq hmem x).symm

/-- **The completeness of the PCP** (prop:completeness_and_soundness_of_PCP_for_V_n): when the
window tables satisfy the formula the circuit describes and the linear tables satisfy the system
the table of `O` holds, the honest PCP satisfies the thirteen checks identically. -/
theorem identities_induce {Cc : Circuit} (hWF : Cc.WellFormed) (hin : Cc.inputs = L.nIn)
    (hm : Cc.inputs + Cc.size = L.m) (R : RTables) (Lt : LTables)
    (hsat : (Cc.formula6 (L.ℓ + 1) (L.ℓ + 1) (L.oW + 1) L.r).Sat (fun j => winOf R.tA j)
      (fun j => winOf R.tB j) (fun j => winOf R.tO j) (fun j => R.tW 0 j)
      (fun j => R.tW 1 j) (fun j => R.tW 2 j))
    (htab : TableSat (2 ^ L.ℓ) (2 ^ L.dm) (tblStr L.oW R.tO) Lt.fLa Lt.fLb (Lt.fL 0) (Lt.fL 1)
      (Lt.fL 2)) :
    (induce L (rename (Fin.cast hm) (Cc.finiteArith (F := F))) R Lt).Identities
      (rename (Fin.cast hm) Cc.finiteArith) :=
  let ⟨h3, h4, h5, h6, h7, h8, h9⟩ :=
    assignChecks_induce (F := F) (rename (Fin.cast hm) Cc.finiteArith) R Lt
  ⟨formulaCheck_induce hWF hin hm R Lt hsat, systemCheck_induce _ R Lt htab, h3, h4, h5, h6, h7,
    h8, h9⟩

/-! ## The readable and the linear parts -/

/-- The readable part of a PCP: the readable assignments and their helpers. -/
def Pcp.readable (P : Pcp L F) :=
  (P.gA, P.gB, P.gO, P.gW, P.αR, P.βA, P.βB, P.βO, P.βW)

/-- **The readable part of the honest PCP depends only on the readable tables.** -/
theorem readable_induce (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt Lt' : LTables) :
    (induce L T R Lt).readable = (induce L T R Lt').readable := rfl

theorem encZ_zero {k : ℕ} : (encZ k (0 : ℕ → ZMod 2) : MvPolynomial (Fin k) F) = 0 := by
  simp [encZ, encTbl, ldEnc]

omit [CharP F 2] in
theorem systemPoly_add (gO : MvPolynomial (Fin L.oW) F) (a₁ a₂ b₁ b₂ : MvPolynomial (Fin L.ℓ) F)
    (l₁ l₂ : Fin 3 → MvPolynomial (Fin L.dm) F) :
    systemPoly gO (a₁ + a₂) (b₁ + b₂) (fun k => l₁ k + l₂ k) + systemPoly gO 0 0 (fun _ => 0) =
      systemPoly gO a₁ b₁ l₁ + systemPoly gO a₂ b₂ l₂ := by
  unfold systemPoly
  simp only [map_add, map_zero, Fin.sum_univ_three]
  ring

/-- **The linear part of the honest PCP is `F₂`-affine in the linear tables**: the encodings and
the certificates of the linear assignments are additive (`g ↦ g (1 - g)` is additive in
characteristic `2`), and the certificates of the system polynomial are affine. -/
theorem linear_induce_add (T : MvPolynomial (Fin L.m) F) (R : RTables) (Lt₁ Lt₂ : LTables) :
    (induce L T R (Lt₁ + Lt₂)).gLa = (induce L T R Lt₁).gLa + (induce L T R Lt₂).gLa ∧
      (induce L T R (Lt₁ + Lt₂)).gLb = (induce L T R Lt₁).gLb + (induce L T R Lt₂).gLb ∧
      (∀ k, (induce L T R (Lt₁ + Lt₂)).gL k = (induce L T R Lt₁).gL k + (induce L T R Lt₂).gL k) ∧
      (∀ X, (induce L T R (Lt₁ + Lt₂)).αL X + (induce L T R 0).αL X =
        (induce L T R Lt₁).αL X + (induce L T R Lt₂).αL X) ∧
      (∀ X, (induce L T R (Lt₁ + Lt₂)).βLa X =
        (induce L T R Lt₁).βLa X + (induce L T R Lt₂).βLa X) ∧
      (∀ X, (induce L T R (Lt₁ + Lt₂)).βLb X =
        (induce L T R Lt₁).βLb X + (induce L T R Lt₂).βLb X) ∧
      ∀ k X, (induce L T R (Lt₁ + Lt₂)).βL k X =
        (induce L T R Lt₁).βL k X + (induce L T R Lt₂).βL k X := by
  have hLa : (encZ L.ℓ (Lt₁ + Lt₂).fLa : MvPolynomial (Fin L.ℓ) F) =
      encZ L.ℓ Lt₁.fLa + encZ L.ℓ Lt₂.fLa := encZ_add _ _
  have hLb : (encZ L.ℓ (Lt₁ + Lt₂).fLb : MvPolynomial (Fin L.ℓ) F) =
      encZ L.ℓ Lt₁.fLb + encZ L.ℓ Lt₂.fLb := encZ_add _ _
  have hL : ∀ k, (encZ L.dm ((Lt₁ + Lt₂).fL k) : MvPolynomial (Fin L.dm) F) =
      encZ L.dm (Lt₁.fL k) + encZ L.dm (Lt₂.fL k) := fun k => encZ_add _ _
  have h0a : (encZ L.ℓ (0 : LTables).fLa : MvPolynomial (Fin L.ℓ) F) = 0 := encZ_zero
  have h0b : (encZ L.ℓ (0 : LTables).fLb : MvPolynomial (Fin L.ℓ) F) = 0 := encZ_zero
  have h0 : ∀ k, (encZ L.dm ((0 : LTables).fL k) : MvPolynomial (Fin L.dm) F) = 0 :=
    fun _ => encZ_zero
  simp only [induce_gLa, induce_gLb, induce_gL, induce_αL, induce_βLa, induce_βLb, induce_βL]
  refine ⟨hLa, hLb, hL, fun X => ?_, fun X => ?_, fun X => ?_, fun k X => ?_⟩
  · rw [hLa, hLb, h0a, h0b, show (fun k => (encZ L.dm ((Lt₁ + Lt₂).fL k) :
      MvPolynomial (Fin L.dm) F)) = fun k => encZ L.dm (Lt₁.fL k) + encZ L.dm (Lt₂.fL k) from
      funext hL, show (fun k => (encZ L.dm ((0 : LTables).fL k) : MvPolynomial (Fin L.dm) F)) =
      fun _ => 0 from funext h0, ← Pi.add_apply, ← map_add, systemPoly_add, map_add,
      Pi.add_apply]
  · rw [hLa, assignCert_add, Pi.add_apply]
  · rw [hLb, assignCert_add, Pi.add_apply]
  · rw [hL, assignCert_add, Pi.add_apply]

end MIPRE.Tailored.AnsRed

end
