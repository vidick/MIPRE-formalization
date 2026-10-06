/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.Indicator
public import MIPRE.Foundations.LowDegree.SchwartzZippel

@[expose] public section

/-!
# The PCP of the answer reduction: its blocks, its checks, and Schwartz–Zippel

Paper II's degree-`d` PCP for the combined succinct 6-decoupled SAT and 5-decoupled linear system
(Definitions defn:blocks_of_vars_circuit and defn:PCP_of_V_n_satisfied, II:8939–9013; the checks
of Observation obs:satisfiability_vs_PCP). Its variables are the wires of the circuit `C` that
describes the output indicator through three windows (`lem:ar-window-describer`): the window
`A` (a parity wire, then the `ℓ` bits of a cell of the first readable answer), the window `B`
(likewise for the second), the window `C` (a parity wire, then the `2ℓ + 3◇ + 6` bits of an index
of the table `O`), the three witness indices, the six signs, and the gates. The index of `O` is
itself the paper's `S₀`: the bits of the two linear answers' cells, of the three copies, and the six
signs of the decoupled system (the layout of `MIPRE.Tailored.AnsRed.indTable`).

* `PcpDims`: the four sizes `ℓ, ◇, r, s` and the positions of the blocks.
* `Pcp`: the eleven *assignments* — `gA, gB` on `ℓ` variables, `gO` on `2ℓ + 3◇ + 6`, three `gW` on
  `r`, readable; `gLa, gLb` on `ℓ` and three `gL` on `◇`, linear — and the helpers `α` and `β`.
* The thirteen checks at a point (`Pcp.Passes`): the formula check (`FormulaCheck`), the system
  check (`SystemCheck`), and eleven assignment checks (`AssignCheck`); as identities, each at
  every point of its own space (`Pcp.Identities`).
* The checks as the vanishing of thirteen polynomials (`chkPolys`, `passes_iff`), of degree at most
  `chkDeg dT d = dT + 6(d + 1)` in each variable for a PCP of degree `d` and a circuit polynomial
  of degree `dT` (`degreeOf_chkPolys_le`).
* The first step of the soundness of prop:completeness_and_soundness_of_PCP_for_V_n: passing on
  a set of density more than `m · chkDeg / q` makes the check polynomials zero, by Schwartz–Zippel
  (`chkPolys_eq_zero`), so the checks hold identically (`identities_of_dense`). The second step,
  from the identities to the formula and the system, is `MIPRE/Tailored/AnsRed/PcpSound.lean`.

Two departures from the paper's text. The windows of the describer hold *tape encodings*
(`0 ↦ 00`, `1 ↦ 01`), so the literal of a window at `(π, u)` is `π · g(u)` for the polynomial `g`
of the raw table: the tape encoding is affine in the table, and the paper's raw-table assignments
are kept. And a literal of the repository's clauses is true when its variable equals its sign
(`Lit.pos`), so its factor is `g - sign` where the paper writes `g + ε + 1` with `ε` the
negated sign (fact:polynomial_condition_for_satisfiability). The certificates `X_i (1 - X_i)` are
the paper's `zero_X`, `X (X + 1)` in characteristic `2`.
-/

namespace MIPRE.Tailored.AnsRed

open MvPolynomial

/-! ## The blocks -/

/-- The sizes of the PCP: the exponents `ℓ` of the table size and `◇` of the copy size, the width
`r` of the witness indices, and the number `s` of gates of the circuit. -/
structure PcpDims where
  ℓ : ℕ
  dm : ℕ
  r : ℕ
  s : ℕ

namespace PcpDims

variable (L : PcpDims)

/-- The width `2ℓ + 3◇ + 6` of an index of the table `O`, the paper's `|S₀|`. -/
def oW : ℕ := L.ℓ + L.ℓ + 3 * L.dm + 6

/-- The number of the circuit's inputs: three windows, three witness indices, six signs. -/
def nIn : ℕ := (L.ℓ + 1) + (L.ℓ + 1) + (L.oW + 1) + 3 * L.r + 6

/-- The number of variables of the PCP, the circuit's wires. -/
def m : ℕ := L.nIn + L.s

theorem nIn_le_m : L.nIn ≤ L.m := Nat.le_add_right _ _

/-- The parity wire of the window `A`. -/
def πA : Fin L.m := ⟨0, by unfold m nIn; omega⟩

/-- The cell wires of the window `A`. -/
def vA (j : Fin L.ℓ) : Fin L.m := ⟨1 + j, by have := j.2; unfold m nIn; omega⟩

/-- The parity wire of the window `B`. -/
def πB : Fin L.m := ⟨L.ℓ + 1, by unfold m nIn; omega⟩

/-- The cell wires of the window `B`. -/
def vB (j : Fin L.ℓ) : Fin L.m := ⟨L.ℓ + 1 + 1 + j, by have := j.2; unfold m nIn; omega⟩

/-- The parity wire of the window `C`. -/
def πC : Fin L.m := ⟨L.ℓ + 1 + (L.ℓ + 1), by unfold m nIn; omega⟩

/-- The wires of an index of `O`, after the parity wire of the window `C`. -/
def vO (j : Fin L.oW) : Fin L.m :=
  ⟨L.ℓ + 1 + (L.ℓ + 1) + 1 + j, by have := j.2; unfold m nIn; omega⟩

/-- The wires of the `k`-th witness index. -/
def vW (k : Fin 3) (j : Fin L.r) : Fin L.m :=
  ⟨L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + k * L.r + j, by
    have hk := k.2; have hj := j.2
    have : k * L.r + j < 3 * L.r := by nlinarith
    unfold m nIn; omega⟩

/-- The six sign wires, in the order of the windows and witness blocks: `A, B, C, w₁, w₂, w₃`. -/
def sgn (k : Fin 6) : Fin L.m :=
  ⟨L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + 3 * L.r + k, by have := k.2; unfold m nIn; omega⟩

/-- Inside an index of `O`: the cell of the first linear answer. -/
def oA (j : Fin L.ℓ) : Fin L.oW := ⟨j, by have := j.2; unfold oW; omega⟩

/-- Inside an index of `O`: the cell of the second linear answer. -/
def oB (j : Fin L.ℓ) : Fin L.oW := ⟨L.ℓ + j, by have := j.2; unfold oW; omega⟩

/-- Inside an index of `O`: the cell of the `k`-th copy. -/
def oL (k : Fin 3) (j : Fin L.dm) : Fin L.oW :=
  ⟨L.ℓ + L.ℓ + k * L.dm + j, by
    have hk := k.2; have hj := j.2
    have : k * L.dm + j < 3 * L.dm := by nlinarith
    unfold oW; omega⟩

/-- Inside an index of `O`: the six signs of the equation, `ε_A, ε_B, ε₁, ε₂, ε₃, ε₀`. -/
def oSgn (k : Fin 6) : Fin L.oW := ⟨L.ℓ + L.ℓ + 3 * L.dm + k, by have := k.2; unfold oW; omega⟩

@[simp] theorem val_πA : (L.πA : ℕ) = 0 := rfl
@[simp] theorem val_vA (j : Fin L.ℓ) : (L.vA j : ℕ) = 1 + j := rfl
@[simp] theorem val_πB : (L.πB : ℕ) = L.ℓ + 1 := rfl
@[simp] theorem val_vB (j : Fin L.ℓ) : (L.vB j : ℕ) = L.ℓ + 1 + 1 + j := rfl
@[simp] theorem val_πC : (L.πC : ℕ) = L.ℓ + 1 + (L.ℓ + 1) := rfl
@[simp] theorem val_vO (j : Fin L.oW) : (L.vO j : ℕ) = L.ℓ + 1 + (L.ℓ + 1) + 1 + j := rfl
@[simp] theorem val_vW (k : Fin 3) (j : Fin L.r) :
    (L.vW k j : ℕ) = L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + k * L.r + j := rfl
@[simp] theorem val_sgn (k : Fin 6) :
    (L.sgn k : ℕ) = L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + 3 * L.r + k := rfl
@[simp] theorem val_oA (j : Fin L.ℓ) : (L.oA j : ℕ) = j := rfl
@[simp] theorem val_oB (j : Fin L.ℓ) : (L.oB j : ℕ) = L.ℓ + j := rfl
@[simp] theorem val_oL (k : Fin 3) (j : Fin L.dm) : (L.oL k j : ℕ) = L.ℓ + L.ℓ + k * L.dm + j := rfl
@[simp] theorem val_oSgn (k : Fin 6) : (L.oSgn k : ℕ) = L.ℓ + L.ℓ + 3 * L.dm + k := rfl

theorem vA_injective : Function.Injective L.vA := fun a b h => by
  simp only [vA, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem vB_injective : Function.Injective L.vB := fun a b h => by
  simp only [vB, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem vO_injective : Function.Injective L.vO := fun a b h => by
  simp only [vO, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem vW_injective (k : Fin 3) : Function.Injective (L.vW k) := fun a b h => by
  simp only [vW, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem oA_injective : Function.Injective L.oA := fun a b h => by
  simp only [oA, Fin.mk.injEq] at h; exact Fin.ext h

theorem oB_injective : Function.Injective L.oB := fun a b h => by
  simp only [oB, Fin.mk.injEq] at h; exact Fin.ext (by omega)

theorem oL_injective (k : Fin 3) : Function.Injective (L.oL k) := fun a b h => by
  simp only [oL, Fin.mk.injEq] at h; exact Fin.ext (by omega)

end PcpDims

/-! ## The proof -/

/-- **A PCP** (Definition defn:PCP_of_V_n_satisfied): the eleven assignments and the helpers. The
readable part is `gA, gB, gO, gW, αR, βA, βB, βO, βW`; the linear part is `gLa, gLb, gL, αL, βLa,
βLb, βL`. -/
structure Pcp (L : PcpDims) (F : Type*) [CommRing F] where
  gA : MvPolynomial (Fin L.ℓ) F
  gB : MvPolynomial (Fin L.ℓ) F
  gO : MvPolynomial (Fin L.oW) F
  gW : Fin 3 → MvPolynomial (Fin L.r) F
  gLa : MvPolynomial (Fin L.ℓ) F
  gLb : MvPolynomial (Fin L.ℓ) F
  gL : Fin 3 → MvPolynomial (Fin L.dm) F
  αR : Fin L.m → MvPolynomial (Fin L.m) F
  αL : Fin L.oW → MvPolynomial (Fin L.oW) F
  βA : Fin L.ℓ → MvPolynomial (Fin L.ℓ) F
  βB : Fin L.ℓ → MvPolynomial (Fin L.ℓ) F
  βO : Fin L.oW → MvPolynomial (Fin L.oW) F
  βW : Fin 3 → Fin L.r → MvPolynomial (Fin L.r) F
  βLa : Fin L.ℓ → MvPolynomial (Fin L.ℓ) F
  βLb : Fin L.ℓ → MvPolynomial (Fin L.ℓ) F
  βL : Fin 3 → Fin L.dm → MvPolynomial (Fin L.dm) F

/-! ## The checks -/

variable {F : Type*} [CommRing F] {L : PcpDims}

/-- **An assignment check** (eq:PCP_condition_1, eq:PCP_condition_2): `g (1 - g)` is the
certificate sum at the point `x` of its block. -/
def AssignCheck {k : ℕ} (g : MvPolynomial (Fin k) F) (β : Fin k → MvPolynomial (Fin k) F)
    (x : Fin k → F) : Prop :=
  eval x g * (1 - eval x g) = ∑ i, x i * (1 - x i) * eval x (β i)

/-- **The formula check** (eq:Tseitin_satisfiable_induced) at the point `p`, against the Tseitin
polynomial `T` of the circuit: `T` times the six literal factors — the window literals the parity
times the table polynomial — is the certificate sum. -/
def FormulaCheck (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) (p : Fin L.m → F) : Prop :=
  eval p T * (p L.πA * eval (p ∘ L.vA) P.gA - p (L.sgn 0)) *
      (p L.πB * eval (p ∘ L.vB) P.gB - p (L.sgn 1)) *
      (p L.πC * eval (p ∘ L.vO) P.gO - p (L.sgn 2)) *
      ∏ k : Fin 3, (eval (p ∘ L.vW k) (P.gW k) - p (L.sgn (3 + k.castLE (by omega)))) =
    ∑ X, p X * (1 - p X) * eval p (P.αR X)

/-- **The system check** (eq:induced_system_is_satisfied) at the point `x` of the index space of
`O`: `O` times the equation `ε_A g_{La} + ε_B g_{Lb} + Σ ε_i g_{L,i} - ε₀` is the certificate
sum. -/
def SystemCheck (P : Pcp L F) (x : Fin L.oW → F) : Prop :=
  eval x P.gO * (x (L.oSgn 0) * eval (x ∘ L.oA) P.gLa + x (L.oSgn 1) * eval (x ∘ L.oB) P.gLb +
      ∑ k : Fin 3, x (L.oSgn (2 + k.castLE (by omega))) * eval (x ∘ L.oL k) (P.gL k) -
      x (L.oSgn 5)) =
    ∑ X, x X * (1 - x X) * eval x (P.αL X)

/-- **The thirteen checks at a point** (Definition defn:PCP_of_V_n_satisfied, Observation
obs:satisfiability_vs_PCP): the formula check, the system check at the point's index of `O`, and
the eleven assignment checks at the point's blocks. -/
def Pcp.Passes (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) (p : Fin L.m → F) : Prop :=
  FormulaCheck T P p ∧ SystemCheck P (p ∘ L.vO) ∧
    AssignCheck P.gA P.βA (p ∘ L.vA) ∧ AssignCheck P.gB P.βB (p ∘ L.vB) ∧
    AssignCheck P.gO P.βO (p ∘ L.vO) ∧ (∀ k, AssignCheck (P.gW k) (P.βW k) (p ∘ L.vW k)) ∧
    AssignCheck P.gLa P.βLa (p ∘ L.vO ∘ L.oA) ∧ AssignCheck P.gLb P.βLb (p ∘ L.vO ∘ L.oB) ∧
    ∀ k, AssignCheck (P.gL k) (P.βL k) (p ∘ L.vO ∘ L.oL k)

/-- **The thirteen checks as identities**: each holds at every point of its own space — what the
honest PCP satisfies (the completeness of prop:completeness_and_soundness_of_PCP_for_V_n) and what
a PCP passing often enough must satisfy (its soundness). -/
def Pcp.Identities (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) : Prop :=
  (∀ p, FormulaCheck T P p) ∧ (∀ x, SystemCheck P x) ∧ (∀ x, AssignCheck P.gA P.βA x) ∧
    (∀ x, AssignCheck P.gB P.βB x) ∧ (∀ x, AssignCheck P.gO P.βO x) ∧
    (∀ k x, AssignCheck (P.gW k) (P.βW k) x) ∧ (∀ x, AssignCheck P.gLa P.βLa x) ∧
    (∀ x, AssignCheck P.gLb P.βLb x) ∧ ∀ k x, AssignCheck (P.gL k) (P.βL k) x

/-- A PCP satisfying the identities passes the checks at every point. -/
theorem Pcp.Identities.passes {T : MvPolynomial (Fin L.m) F} {P : Pcp L F}
    (h : P.Identities T) (p : Fin L.m → F) : P.Passes T p :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  ⟨h1 p, h2 _, h3 _, h4 _, h5 _, fun k => h6 k _, h7 _, h8 _, fun k => h9 k _⟩

/-! ## The checks as polynomials -/

section polys

variable {F : Type*} [CommRing F] {L : PcpDims}

/-- The polynomial of an assignment check, on the variables of the PCP through the embedding `v`
of its block. -/
noncomputable def chkAssign {k : ℕ} (v : Fin k → Fin L.m) (g : MvPolynomial (Fin k) F)
    (β : Fin k → MvPolynomial (Fin k) F) : MvPolynomial (Fin L.m) F :=
  rename v (g * (1 - g) - ∑ i, X i * (1 - X i) * β i)

/-- The polynomial of the system check, on the index space of `O`. -/
noncomputable def chkSystemO (P : Pcp L F) : MvPolynomial (Fin L.oW) F :=
  P.gO * (X (L.oSgn 0) * rename L.oA P.gLa + X (L.oSgn 1) * rename L.oB P.gLb +
      ∑ k : Fin 3, X (L.oSgn (2 + k.castLE (by omega))) * rename (L.oL k) (P.gL k) -
      X (L.oSgn 5)) -
    ∑ i, X i * (1 - X i) * P.αL i

/-- The polynomial of the formula check. -/
noncomputable def chkFormula (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) :
    MvPolynomial (Fin L.m) F :=
  T * (X L.πA * rename L.vA P.gA - X (L.sgn 0)) * (X L.πB * rename L.vB P.gB - X (L.sgn 1)) *
      (X L.πC * rename L.vO P.gO - X (L.sgn 2)) *
      ∏ k : Fin 3, (rename (L.vW k) (P.gW k) - X (L.sgn (3 + k.castLE (by omega)))) -
    ∑ i, X i * (1 - X i) * P.αR i

theorem assignCheck_iff {k : ℕ} (v : Fin k → Fin L.m) (g : MvPolynomial (Fin k) F)
    (β : Fin k → MvPolynomial (Fin k) F) (p : Fin L.m → F) :
    AssignCheck g β (p ∘ v) ↔ eval p (chkAssign v g β) = 0 := by
  simp only [AssignCheck, chkAssign, eval_rename, map_sub, map_mul, map_sum, eval_X, map_one,
    Function.comp_apply, sub_eq_zero]

theorem systemCheck_iff (P : Pcp L F) (x : Fin L.oW → F) :
    SystemCheck P x ↔ eval x (chkSystemO P) = 0 := by
  simp only [SystemCheck, chkSystemO, eval_rename, map_sub, map_mul, map_add, map_sum, eval_X,
    map_one, sub_eq_zero]

theorem formulaCheck_iff (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) (p : Fin L.m → F) :
    FormulaCheck T P p ↔ eval p (chkFormula T P) = 0 := by
  simp only [FormulaCheck, chkFormula, eval_rename, map_sub, map_mul, map_prod, map_sum, eval_X,
    map_one, sub_eq_zero]

/-- The thirteen polynomials of the checks, on the variables of the PCP. -/
noncomputable def chkPolys (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) :
    List (MvPolynomial (Fin L.m) F) :=
  [chkFormula T P, rename L.vO (chkSystemO P), chkAssign L.vA P.gA P.βA,
    chkAssign L.vB P.gB P.βB, chkAssign L.vO P.gO P.βO] ++
    List.ofFn (fun k => chkAssign (L.vW k) (P.gW k) (P.βW k)) ++
    [chkAssign (L.vO ∘ L.oA) P.gLa P.βLa, chkAssign (L.vO ∘ L.oB) P.gLb P.βLb] ++
    List.ofFn (fun k => chkAssign (L.vO ∘ L.oL k) (P.gL k) (P.βL k))

/-- **The checks pass at a point exactly when the thirteen polynomials vanish there.** -/
theorem passes_iff (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) (p : Fin L.m → F) :
    P.Passes T p ↔ ∀ c ∈ chkPolys T P, eval p c = 0 := by
  have hO : SystemCheck P (p ∘ L.vO) ↔ eval p (rename L.vO (chkSystemO P)) = 0 := by
    rw [eval_rename]; exact systemCheck_iff P _
  simp only [Pcp.Passes, chkPolys, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false]
  rw [formulaCheck_iff, hO, assignCheck_iff L.vA, assignCheck_iff L.vB, assignCheck_iff L.vO,
    assignCheck_iff (L.vO ∘ L.oA), assignCheck_iff (L.vO ∘ L.oB)]
  simp only [assignCheck_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ c hc
    rcases hc with ((((rfl | rfl | rfl | rfl | rfl) | ⟨k, rfl⟩) | (rfl | rfl)) | ⟨k, rfl⟩)
    exacts [h1, h2, h3, h4, h5, h6 k, h7, h8, h9 k]
  · intro h
    refine ⟨h _ ?_, h _ ?_, h _ ?_, h _ ?_, h _ ?_, fun k => h _ ?_, h _ ?_, h _ ?_,
      fun k => h _ ?_⟩
    all_goals simp

end polys

/-! ## Degrees -/

section degrees

variable {F : Type*} [CommRing F] [Nontrivial F] {L : PcpDims}

omit [Nontrivial F] in
theorem degreeOf_rename_le_of_injective {k n : ℕ} {f : Fin k → Fin n}
    (hf : Function.Injective f) {p : MvPolynomial (Fin k) F} {d : ℕ}
    (hp : ∀ i, p.degreeOf i ≤ d) (j : Fin n) : (rename f p).degreeOf j ≤ d := by
  classical
  by_cases h : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := h
    rw [degreeOf_rename_of_injective hf]
    exact hp i
  · have h0 : (rename f p).degreeOf j = 0 := by
      rw [degreeOf_def, degrees_rename_of_injective hf, Multiset.count_eq_zero]
      intro hj
      obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hj
      exact h ⟨i, hi⟩
    omega

theorem degreeOf_X_le {n : ℕ} (i j : Fin n) : (X i : MvPolynomial (Fin n) F).degreeOf j ≤ 1 := by
  classical
  rw [degreeOf_X]; split_ifs <;> omega

omit [Nontrivial F] in
theorem degreeOf_one_sub_le {n : ℕ} (p : MvPolynomial (Fin n) F) (j : Fin n) :
    (1 - p).degreeOf j ≤ p.degreeOf j := by
  refine (degreeOf_sub_le j 1 p).trans ?_
  rw [degreeOf_one]
  omega

/-- A certificate sum `Σ_i X_i (1 - X_i) c_i` has degree at most `d + 2` in each variable. -/
theorem degreeOf_certSum_le {n d : ℕ} (c : Fin n → MvPolynomial (Fin n) F)
    (hc : ∀ i j, (c i).degreeOf j ≤ d) (j : Fin n) :
    (∑ i, X i * (1 - X i) * c i).degreeOf j ≤ d + 2 := by
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (degreeOf_mul_le j _ _).trans ?_
  have h1 := (degreeOf_mul_le j (X i : MvPolynomial (Fin n) F) (1 - X i))
  have h2 := degreeOf_X_le (F := F) i j
  have h3 := (degreeOf_one_sub_le (F := F) (X i) j).trans (degreeOf_X_le i j)
  have h4 := hc i j
  omega

/-- Every polynomial of the PCP has degree at most `d` in each variable. -/
def Pcp.IndDeg (P : Pcp L F) (d : ℕ) : Prop :=
  (∀ i, P.gA.degreeOf i ≤ d) ∧ (∀ i, P.gB.degreeOf i ≤ d) ∧ (∀ i, P.gO.degreeOf i ≤ d) ∧
    (∀ k i, (P.gW k).degreeOf i ≤ d) ∧ (∀ i, P.gLa.degreeOf i ≤ d) ∧
    (∀ i, P.gLb.degreeOf i ≤ d) ∧ (∀ k i, (P.gL k).degreeOf i ≤ d) ∧
    (∀ j i, (P.αR j).degreeOf i ≤ d) ∧ (∀ j i, (P.αL j).degreeOf i ≤ d) ∧
    (∀ j i, (P.βA j).degreeOf i ≤ d) ∧ (∀ j i, (P.βB j).degreeOf i ≤ d) ∧
    (∀ j i, (P.βO j).degreeOf i ≤ d) ∧ (∀ k j i, (P.βW k j).degreeOf i ≤ d) ∧
    (∀ j i, (P.βLa j).degreeOf i ≤ d) ∧ (∀ j i, (P.βLb j).degreeOf i ≤ d) ∧
    ∀ k j i, (P.βL k j).degreeOf i ≤ d

/-- The degree bound of the thirteen check polynomials, for a PCP of degree `d` and a circuit
polynomial of degree `dT`: each of the six literal factors counted separately. -/
def chkDeg (dT d : ℕ) : ℕ := dT + 6 * (d + 1)

theorem degreeOf_chkAssign_le {k d dT : ℕ} {v : Fin k → Fin L.m} (hv : Function.Injective v)
    {g : MvPolynomial (Fin k) F} {β : Fin k → MvPolynomial (Fin k) F}
    (hg : ∀ i, g.degreeOf i ≤ d) (hβ : ∀ j i, (β j).degreeOf i ≤ d) (i : Fin L.m) :
    (chkAssign v g β).degreeOf i ≤ chkDeg dT d := by
  unfold chkAssign chkDeg
  refine (degreeOf_rename_le_of_injective hv (d := 2 * d + 2) (fun j => ?_) i).trans (by omega)
  refine (degreeOf_sub_le j _ _).trans (max_le ?_ ((degreeOf_certSum_le β hβ j).trans (by omega)))
  have := degreeOf_mul_le j g (1 - g)
  have := (degreeOf_one_sub_le g j).trans (hg j)
  have := hg j
  omega

theorem degreeOf_chkSystemO_le {d : ℕ} {P : Pcp L F} (hP : P.IndDeg d) (i : Fin L.oW) :
    (chkSystemO P).degreeOf i ≤ 2 * d + 2 := by
  obtain ⟨-, -, hO, -, hLa, hLb, hL, -, hαL, -⟩ := hP
  have hinjA : Function.Injective L.oA := fun a b h => by
    simp only [PcpDims.oA, Fin.mk.injEq] at h; exact Fin.ext h
  have hinjB : Function.Injective L.oB := fun a b h => by
    simp only [PcpDims.oB, Fin.mk.injEq] at h; exact Fin.ext (by omega)
  have hinjL : ∀ k, Function.Injective (L.oL k) := fun k a b h => by
    simp only [PcpDims.oL, Fin.mk.injEq] at h; exact Fin.ext (by omega)
  unfold chkSystemO
  refine (degreeOf_sub_le i _ _).trans (max_le ?_ ((degreeOf_certSum_le _ hαL i).trans
    (by omega)))
  refine (degreeOf_mul_le i _ _).trans ?_
  have hO' := hO i
  have hlin : (X (L.oSgn 0) * rename L.oA P.gLa + X (L.oSgn 1) * rename L.oB P.gLb +
      ∑ k : Fin 3, X (L.oSgn (2 + k.castLE (by omega))) * rename (L.oL k) (P.gL k) -
      X (L.oSgn 5) : MvPolynomial (Fin L.oW) F).degreeOf i ≤ d + 1 := by
    refine (degreeOf_sub_le i _ _).trans (max_le ?_ ((degreeOf_X_le _ i).trans (by omega)))
    refine (degreeOf_add_le i _ _).trans (max_le ((degreeOf_add_le i _ _).trans
      (max_le ?_ ?_)) ?_)
    · refine (degreeOf_mul_le i _ _).trans ?_
      have := degreeOf_X_le (F := F) (L.oSgn 0) i
      have := degreeOf_rename_le_of_injective hinjA hLa i
      omega
    · refine (degreeOf_mul_le i _ _).trans ?_
      have := degreeOf_X_le (F := F) (L.oSgn 1) i
      have := degreeOf_rename_le_of_injective hinjB hLb i
      omega
    · refine (degreeOf_sum_le i _ _).trans (Finset.sup_le fun k _ => ?_)
      refine (degreeOf_mul_le i _ _).trans ?_
      have := degreeOf_X_le (F := F) (L.oSgn (2 + k.castLE (by omega))) i
      have := degreeOf_rename_le_of_injective (hinjL k) (hL k) i
      omega
  omega

/-- A factor `X_π · g ∘ v - X_ε` or `g ∘ v - X_ε` of the formula check has degree at most `d + 1`
in each variable. -/
theorem degreeOf_litFactor_le {k d : ℕ} {v : Fin k → Fin L.m} (hv : Function.Injective v)
    {g : MvPolynomial (Fin k) F} (hg : ∀ i, g.degreeOf i ≤ d) (π ε : Fin L.m) (i : Fin L.m) :
    (X π * rename v g - X ε).degreeOf i ≤ d + 1 ∧ (rename v g - X ε).degreeOf i ≤ d + 1 := by
  have h1 := degreeOf_X_le (F := F) π i
  have h2 := degreeOf_X_le (F := F) ε i
  have h3 := degreeOf_rename_le_of_injective hv hg i
  have h4 := degreeOf_mul_le i (X π : MvPolynomial (Fin L.m) F) (rename v g)
  constructor
  · refine (degreeOf_sub_le i _ _).trans (max_le ?_ ?_) <;> omega
  · refine (degreeOf_sub_le i _ _).trans (max_le ?_ ?_) <;> omega

theorem degreeOf_chkFormula_le {d dT : ℕ} {T : MvPolynomial (Fin L.m) F} {P : Pcp L F}
    (hT : ∀ i, T.degreeOf i ≤ dT) (hP : P.IndDeg d) (i : Fin L.m) :
    (chkFormula T P).degreeOf i ≤ chkDeg dT d := by
  obtain ⟨hA, hB, hO, hW, -, -, -, hαR, -⟩ := hP
  unfold chkFormula chkDeg
  refine (degreeOf_sub_le i _ _).trans (max_le ?_ ((degreeOf_certSum_le _ hαR i).trans
    (by omega)))
  have fA := (degreeOf_litFactor_le L.vA_injective hA L.πA (L.sgn 0) i).1
  have fB := (degreeOf_litFactor_le L.vB_injective hB L.πB (L.sgn 1) i).1
  have fO := (degreeOf_litFactor_le L.vO_injective hO L.πC (L.sgn 2) i).1
  have fW : (∏ k : Fin 3, (rename (L.vW k) (P.gW k) - X (L.sgn (3 + k.castLE (by omega)))) :
      MvPolynomial (Fin L.m) F).degreeOf i ≤ 3 * (d + 1) := by
    refine (degreeOf_prod_le i _ _).trans ?_
    calc ∑ k : Fin 3, (rename (L.vW k) (P.gW k) -
          X (L.sgn (3 + k.castLE (by omega))) : MvPolynomial (Fin L.m) F).degreeOf i
        ≤ ∑ _k : Fin 3, (d + 1) := Finset.sum_le_sum fun k _ =>
          (degreeOf_litFactor_le (L.vW_injective k) (hW k) L.πA _ i).2
      _ = 3 * (d + 1) := by simp
  have m1 := degreeOf_mul_le i T (X L.πA * rename L.vA P.gA - X (L.sgn 0))
  have m2 := degreeOf_mul_le i (T * (X L.πA * rename L.vA P.gA - X (L.sgn 0)))
    (X L.πB * rename L.vB P.gB - X (L.sgn 1))
  have m3 := degreeOf_mul_le i (T * (X L.πA * rename L.vA P.gA - X (L.sgn 0)) *
    (X L.πB * rename L.vB P.gB - X (L.sgn 1))) (X L.πC * rename L.vO P.gO - X (L.sgn 2))
  refine (degreeOf_mul_le i _ _).trans ?_
  have := hT i
  omega

/-- **The thirteen check polynomials have degree at most `chkDeg dT d`** in each variable, for a
PCP of degree `d` and a circuit polynomial of degree `dT`. -/
theorem degreeOf_chkPolys_le {d dT : ℕ} {T : MvPolynomial (Fin L.m) F} {P : Pcp L F}
    (hT : ∀ i, T.degreeOf i ≤ dT) (hP : P.IndDeg d) :
    ∀ c ∈ chkPolys T P, ∀ i, c.degreeOf i ≤ chkDeg dT d := by
  have hP' := hP
  obtain ⟨hA, hB, hO, hW, hLa, hLb, hL, -, -, hβA, hβB, hβO, hβW, hβLa, hβLb, hβL⟩ := hP'
  have hOA : Function.Injective (L.vO ∘ L.oA) := L.vO_injective.comp L.oA_injective
  have hOB : Function.Injective (L.vO ∘ L.oB) := L.vO_injective.comp L.oB_injective
  have hOL : ∀ k, Function.Injective (L.vO ∘ L.oL k) := fun k =>
    L.vO_injective.comp (L.oL_injective k)
  intro c hc i
  simp only [chkPolys, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil,
    or_false] at hc
  rcases hc with ((((rfl | rfl | rfl | rfl | rfl) | ⟨k, rfl⟩) | (rfl | rfl)) | ⟨k, rfl⟩)
  · exact degreeOf_chkFormula_le hT hP i
  · refine (degreeOf_rename_le_of_injective L.vO_injective
      (fun j => degreeOf_chkSystemO_le hP j) i).trans ?_
    unfold chkDeg; omega
  · exact degreeOf_chkAssign_le L.vA_injective hA hβA i
  · exact degreeOf_chkAssign_le L.vB_injective hB hβB i
  · exact degreeOf_chkAssign_le L.vO_injective hO hβO i
  · exact degreeOf_chkAssign_le (L.vW_injective k) (hW k) (hβW k) i
  · exact degreeOf_chkAssign_le hOA hLa hβLa i
  · exact degreeOf_chkAssign_le hOB hLb hβLb i
  · exact degreeOf_chkAssign_le (hOL k) (hL k) (hβL k) i

end degrees

/-! ## Soundness by Schwartz–Zippel -/

section schwartzZippel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {L : PcpDims}

open LowDegree in
/-- **The check polynomials of a PCP passing often are zero**
(prop:completeness_and_soundness_of_PCP_for_V_n, soundness, by Schwartz–Zippel): a PCP of degree
`d` passing the thirteen checks at every point of a set of density more than `m · chkDeg / q`
has all thirteen check polynomials zero. -/
theorem chkPolys_eq_zero {d dT : ℕ} {T : MvPolynomial (Fin L.m) F} {P : Pcp L F}
    (hT : ∀ i, T.degreeOf i ≤ dT) (hP : P.IndDeg d) (S : Finset (Fin L.m → F))
    (hS : ∀ p ∈ S, P.Passes T p)
    (hdens : (L.m : ℝ) * chkDeg dT d / Fintype.card F <
      (S.card : ℝ) / (Fintype.card F : ℝ) ^ L.m) :
    ∀ c ∈ chkPolys T P, c = 0 := by
  intro c hc
  by_contra hne
  have hsub : S ⊆ agree c 0 := fun p hp => by
    rw [mem_agree, map_zero]
    exact (passes_iff T P p).1 (hS p hp) c hc
  have hcard : (S.card : ℝ) ≤ (agree c 0).card := by exact_mod_cast Finset.card_le_card hsub
  have hpow : (0 : ℝ) < (Fintype.card F : ℝ) ^ L.m := pow_pos (by exact_mod_cast Fintype.card_pos) _
  have hsz := prob_agree_le_individualDegree hne (degreeOf_chkPolys_le hT hP c hc)
    (fun i => by rw [degreeOf_zero]; exact Nat.zero_le _)
  have : (S.card : ℝ) / (Fintype.card F : ℝ) ^ L.m ≤ ((agree c 0).card : ℝ) /
      (Fintype.card F : ℝ) ^ L.m := div_le_div_of_nonneg_right hcard hpow.le
  linarith

omit [Fintype F] [DecidableEq F] in
theorem assignCheck_of_chkAssign_eq_zero {k : ℕ} {v : Fin k → Fin L.m}
    (hv : Function.Injective v) {g : MvPolynomial (Fin k) F} {β : Fin k → MvPolynomial (Fin k) F}
    (h : chkAssign v g β = 0) (x : Fin k → F) : AssignCheck g β x := by
  unfold chkAssign at h
  have h' := rename_injective v hv (h.trans (map_zero _).symm)
  have := congrArg (eval x) h'
  simp only [map_sub, map_mul, map_sum, eval_X, map_one, map_zero] at this
  exact sub_eq_zero.1 this

omit [Fintype F] [DecidableEq F] in
/-- **The checks hold identically when their polynomials vanish.** -/
theorem identities_of_chkPolys_eq_zero {T : MvPolynomial (Fin L.m) F} {P : Pcp L F}
    (h : ∀ c ∈ chkPolys T P, c = 0) : P.Identities T := by
  have mem : ∀ c, c ∈ chkPolys T P → c = 0 := h
  simp only [chkPolys, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil,
    or_false] at mem
  have hF := mem _ (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
  have hS := mem _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
  have hA := mem _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))))
  have hB := mem _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hO := mem _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  have hW := fun k => mem _ (Or.inl (Or.inl (Or.inr ⟨k, rfl⟩)))
  have hLa := mem _ (Or.inl (Or.inr (Or.inl rfl)))
  have hLb := mem _ (Or.inl (Or.inr (Or.inr rfl)))
  have hL := fun k => mem _ (Or.inr ⟨k, rfl⟩)
  have hS' : chkSystemO P = 0 :=
    rename_injective _ L.vO_injective (hS.trans (map_zero _).symm)
  refine ⟨fun p => (formulaCheck_iff T P p).2 (by rw [hF, map_zero]),
    fun x => (systemCheck_iff P x).2 (by rw [hS', map_zero]),
    assignCheck_of_chkAssign_eq_zero L.vA_injective hA,
    assignCheck_of_chkAssign_eq_zero L.vB_injective hB,
    assignCheck_of_chkAssign_eq_zero L.vO_injective hO,
    fun k => assignCheck_of_chkAssign_eq_zero (L.vW_injective k) (hW k),
    assignCheck_of_chkAssign_eq_zero (L.vO_injective.comp L.oA_injective) hLa,
    assignCheck_of_chkAssign_eq_zero (L.vO_injective.comp L.oB_injective) hLb,
    fun k => assignCheck_of_chkAssign_eq_zero (L.vO_injective.comp (L.oL_injective k)) (hL k)⟩

/-- **The soundness of the PCP, first step** (prop:completeness_and_soundness_of_PCP_for_V_n): a PCP
of degree `d` passing the thirteen checks on a set of points of density more than `m · chkDeg / q`
satisfies them identically. -/
theorem identities_of_dense {d dT : ℕ} {T : MvPolynomial (Fin L.m) F} {P : Pcp L F}
    (hT : ∀ i, T.degreeOf i ≤ dT) (hP : P.IndDeg d) (S : Finset (Fin L.m → F))
    (hS : ∀ p ∈ S, P.Passes T p)
    (hdens : (L.m : ℝ) * chkDeg dT d / Fintype.card F <
      (S.card : ℝ) / (Fintype.card F : ℝ) ^ L.m) :
    P.Identities T :=
  identities_of_chkPolys_eq_zero (chkPolys_eq_zero hT hP S hS hdens)

end schwartzZippel

end MIPRE.Tailored.AnsRed

end
