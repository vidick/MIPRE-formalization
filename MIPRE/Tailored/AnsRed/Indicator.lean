/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.Linear

@[expose] public section

/-!
# The output indicator: the table of the decoupled system, and the check

Paper II's triangulated output indicator `L*` (Definition defn:decider-read, II:8381) reads the
two readable answers `a^R, b^R` and a bit string `O`, and accepts when `O` is the table of the
5-decoupled triangulated purified system of the constraints at the two questions
(claim:properties_of_L*, II:8494). This file is its mathematics; the program is
`MIPRE.Tailored.AnsRed.IndicatorProg`.

* **The index space** `[N] × [N] × [D]³ × [64]` of the table, the first coordinate fastest
  (`encIdx`, `idxA`, …, `idxS`): with `N = 2^ℓ` and `D = 2^◇` the binary digits of an index are
  those of its six coordinates in turn, the paper's embedding into `F₂^{2Λ+3◇+6}` (II:8453). The
  last coordinate holds the six signs, one per bit (`sgn`).
* `indTable N D tris`: the indicator of the decoupled system (`decInd`) over the index space, a
  bit string of length `tableSize N D = 64 N² D³` (`indTable_eq_indLoop`: the output of the loops
  over the coordinates); `TableSat`: five assignments satisfy every equation the table contains,
  the form in which the PCP checks it (fact:polynomial_condition_for_satisfiability, II:8147);
  `tableSat_indTable_iff`: on the table of a system whose equations are below `D`, that is
  `DecSat`.
* `LstarOK`: the check of the output indicator, on the table size `N` and the copy size `D` of
  the index, the four lengths at the two questions and the constraints the processor outputs on
  the readable answers, for inputs `a = a^R O` and `b = b^R`: the lengths are at most `N`, `b`
  has `N` bits and `O` has `tableSize N D`, there are enough triangulation variables, and `O` is
  the table. The readable answers are `a` and `b` cut at the readable lengths, so the honest
  answers are padded with zeros (`lstarOK_pad`).
* claim:properties_of_L*, item 2: `accepts_of_lstarOK` (a satisfying 5-tuple of the table gives
  answers the game accepts) and `tableSat_of_accepts` (answers the game accepts give the
  satisfying 5-tuple `Extend`, the last three blocks linear in the linear answers).

Here the input verifier is neither padded nor purified (II:8377, `planning/aldous-lyons-track.md`
§5, "Phase 4 slices"): the readable answers are cut at the readable lengths and the constraints
purified on the fly (`pureEqn`), so the paper's steps 3 and 4 have nothing to check.
-/

namespace MIPRE.Tailored.AnsRed

open Cost
open MIPRE.LowDegree (ofBool)

/-! ## The index space -/

/-- The number of indices of the table, `64 N² D³`. -/
def tableSize (N D : ℕ) : ℕ := N * (N * (D * (D * (D * 64))))

/-- The index of `(u_A, u_B, u₁, u₂, u₃, s)` in `[N] × [N] × [D]³ × [64]`, the first coordinate
fastest. -/
def encIdx (N D uA uB u₁ u₂ u₃ s : ℕ) : ℕ :=
  uA + N * (uB + N * (u₁ + D * (u₂ + D * (u₃ + D * s))))

/-- The first coordinate of an index, in the block `S_A`. -/
def idxA (N u : ℕ) : ℕ := u % N

/-- The second coordinate, in the block `S_B`. -/
def idxB (N u : ℕ) : ℕ := u / N % N

/-- The third coordinate, in the first copy. -/
def idx₁ (N D u : ℕ) : ℕ := u / N / N % D

/-- The fourth coordinate, in the second copy. -/
def idx₂ (N D u : ℕ) : ℕ := u / N / N / D % D

/-- The fifth coordinate, in the third copy. -/
def idx₃ (N D u : ℕ) : ℕ := u / N / N / D / D % D

/-- The last coordinate, the six signs. -/
def idxS (N D u : ℕ) : ℕ := u / N / N / D / D / D

private theorem add_mul_lt {a b N M : ℕ} (ha : a < N) (hb : b < M) : a + N * b < N * M := by
  have : N * (b + 1) ≤ N * M := Nat.mul_le_mul_left _ hb
  rw [Nat.mul_add, mul_one] at this
  omega

theorem encIdx_lt {N D uA uB u₁ u₂ u₃ s : ℕ} (hA : uA < N) (hB : uB < N) (h₁ : u₁ < D)
    (h₂ : u₂ < D) (h₃ : u₃ < D) (hs : s < 64) : encIdx N D uA uB u₁ u₂ u₃ s < tableSize N D :=
  add_mul_lt hA (add_mul_lt hB (add_mul_lt h₁ (add_mul_lt h₂ (add_mul_lt h₃ hs))))

private theorem div_add_mul {a N r : ℕ} (ha : a < N) : (a + N * r) / N = r := by
  have hN : 0 < N := by omega
  rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt ha, zero_add]

private theorem mod_add_mul {a N r : ℕ} (ha : a < N) : (a + N * r) % N = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

section decode

variable {N D uA uB u₁ u₂ u₃ s : ℕ}

theorem idxA_encIdx (hA : uA < N) : idxA N (encIdx N D uA uB u₁ u₂ u₃ s) = uA :=
  mod_add_mul hA

theorem idxB_encIdx (hA : uA < N) (hB : uB < N) : idxB N (encIdx N D uA uB u₁ u₂ u₃ s) = uB := by
  unfold idxB encIdx; rw [div_add_mul hA, mod_add_mul hB]

theorem idx₁_encIdx (hA : uA < N) (hB : uB < N) (h₁ : u₁ < D) :
    idx₁ N D (encIdx N D uA uB u₁ u₂ u₃ s) = u₁ := by
  unfold idx₁ encIdx; rw [div_add_mul hA, div_add_mul hB, mod_add_mul h₁]

theorem idx₂_encIdx (hA : uA < N) (hB : uB < N) (h₁ : u₁ < D) (h₂ : u₂ < D) :
    idx₂ N D (encIdx N D uA uB u₁ u₂ u₃ s) = u₂ := by
  unfold idx₂ encIdx; rw [div_add_mul hA, div_add_mul hB, div_add_mul h₁, mod_add_mul h₂]

theorem idx₃_encIdx (hA : uA < N) (hB : uB < N) (h₁ : u₁ < D) (h₂ : u₂ < D) (h₃ : u₃ < D) :
    idx₃ N D (encIdx N D uA uB u₁ u₂ u₃ s) = u₃ := by
  unfold idx₃ encIdx
  rw [div_add_mul hA, div_add_mul hB, div_add_mul h₁, div_add_mul h₂, mod_add_mul h₃]

theorem idxS_encIdx (hA : uA < N) (hB : uB < N) (h₁ : u₁ < D) (h₂ : u₂ < D) (h₃ : u₃ < D) :
    idxS N D (encIdx N D uA uB u₁ u₂ u₃ s) = s := by
  unfold idxS encIdx
  rw [div_add_mul hA, div_add_mul hB, div_add_mul h₁, div_add_mul h₂, div_add_mul h₃]

end decode

/-! ## The signs -/

/-- The `i`-th sign held by the last coordinate `s`: its `i`-th binary digit. -/
def sgn (s i : ℕ) : ZMod 2 := ofBool (s.testBit i)

/-- The last coordinate holding six given signs. -/
def sgnIdx (e₀ e₁ e₂ e₃ e₄ e₅ : ZMod 2) : ℕ :=
  e₀.val + 2 * e₁.val + 4 * e₂.val + 8 * e₃.val + 16 * e₄.val + 32 * e₅.val

theorem sgnIdx_lt (e₀ e₁ e₂ e₃ e₄ e₅ : ZMod 2) : sgnIdx e₀ e₁ e₂ e₃ e₄ e₅ < 64 := by
  revert e₀ e₁ e₂ e₃ e₄ e₅; decide

theorem sgn_sgnIdx (e₀ e₁ e₂ e₃ e₄ e₅ : ZMod 2) :
    sgn (sgnIdx e₀ e₁ e₂ e₃ e₄ e₅) 0 = e₀ ∧ sgn (sgnIdx e₀ e₁ e₂ e₃ e₄ e₅) 1 = e₁ ∧
      sgn (sgnIdx e₀ e₁ e₂ e₃ e₄ e₅) 2 = e₂ ∧ sgn (sgnIdx e₀ e₁ e₂ e₃ e₄ e₅) 3 = e₃ ∧
      sgn (sgnIdx e₀ e₁ e₂ e₃ e₄ e₅) 4 = e₄ ∧ sgn (sgnIdx e₀ e₁ e₂ e₃ e₄ e₅) 5 = e₅ := by
  revert e₀ e₁ e₂ e₃ e₄ e₅; decide

/-! ## The table -/

/-- Whether the equation at the index `u` is in the decoupled system of `tris` on the blocks
`[N]`, `[N]` and three copies of `[D]`. -/
def IndAt (N D : ℕ) (tris : List Tri) (u : ℕ) : Prop :=
  decInd N N D tris (idxA N u) (idxB N u) (idx₁ N D u) (idx₂ N D u) (idx₃ N D u)
    (sgn (idxS N D u) 0) (sgn (idxS N D u) 1) (sgn (idxS N D u) 2) (sgn (idxS N D u) 3)
    (sgn (idxS N D u) 4) (sgn (idxS N D u) 5)

instance (N D : ℕ) (tris : List Tri) (u : ℕ) : Decidable (IndAt N D tris u) := by
  unfold IndAt; infer_instance

/-- **The table of the decoupled system** (II:8453, rem:alg_5-decoupling): its indicator over
the index space, a bit string of length `64 N² D³`. -/
def indTable (N D : ℕ) (tris : List Tri) : BitStr :=
  List.ofFn fun u : Fin (tableSize N D) => decide (IndAt N D tris u)

@[simp] theorem length_indTable (N D : ℕ) (tris : List Tri) :
    (indTable N D tris).length = tableSize N D := by
  simp [indTable]

theorem getD_indTable {N D : ℕ} {tris : List Tri} {u : ℕ} (hu : u < tableSize N D) :
    (indTable N D tris).getD u false = decide (IndAt N D tris u) := by
  simp [indTable, List.getD_eq_getElem?_getD, hu]

/-! ### The table, loop by loop -/

theorem getElem?_flatMap_const {α β : Type*} (l : List α) (F : α → List β) {m : ℕ}
    (hF : ∀ a ∈ l, (F a).length = m) (i : ℕ) {j : ℕ} (hj : j < m) :
    (l.flatMap F)[j + m * i]? = l[i]?.bind fun a => (F a)[j]? := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    have ha : (F a).length = m := hF a List.mem_cons_self
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.add_zero, List.getElem?_append_left (by omega)]
      simp
    | succ i =>
      rw [List.getElem?_append_right (by rw [ha]; nlinarith),
        show j + m * (i + 1) - (F a).length = j + m * i by rw [ha, Nat.mul_succ]; omega,
        ih (fun b hb => hF b (List.mem_cons_of_mem _ hb)) i]
      simp

theorem length_flatMap_const {α β : Type*} (l : List α) (F : α → List β) {m : ℕ}
    (hF : ∀ a ∈ l, (F a).length = m) : (l.flatMap F).length = m * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, hF a List.mem_cons_self,
      ih (fun b hb => hF b (List.mem_cons_of_mem _ hb)), List.length_cons, Nat.mul_succ]
    omega

/-- The table at given signs and coordinates, as the loops visit them. -/
def indLoop (N D : ℕ) (tris : List Tri) : BitStr :=
  (List.range 64).flatMap fun s => (List.range D).flatMap fun u₃ =>
    (List.range D).flatMap fun u₂ => (List.range D).flatMap fun u₁ =>
      (List.range N).flatMap fun uB => (List.range N).map fun uA =>
        decide (decInd N N D tris uA uB u₁ u₂ u₃ (sgn s 0) (sgn s 1) (sgn s 2) (sgn s 3)
          (sgn s 4) (sgn s 5))

private theorem decode_eq {N D u : ℕ} :
    u = idxA N u + N * (idxB N u + N * (idx₁ N D u + D * (idx₂ N D u +
      D * (idx₃ N D u + D * idxS N D u)))) := by
  unfold idxA idxB idx₁ idx₂ idx₃ idxS
  have e1 := (Nat.mod_add_div u N).symm
  have e2 := (Nat.mod_add_div (u / N) N).symm
  have e3 := (Nat.mod_add_div (u / N / N) D).symm
  have e4 := (Nat.mod_add_div (u / N / N / D) D).symm
  have e5 := (Nat.mod_add_div (u / N / N / D / D) D).symm
  rw [← e5, ← e4, ← e3, ← e2, ← e1]

/-- **The table is the loops' output**: the sign words outermost, the first coordinate
innermost, the order of the index space. -/
theorem indTable_eq_indLoop (N D : ℕ) (tris : List Tri) : indTable N D tris = indLoop N D tris := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [indTable, indLoop, tableSize]
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp [indTable, indLoop, tableSize]
  have hlenA : ∀ (s u₃ u₂ u₁ uB : ℕ), ((List.range N).map fun uA =>
      decide (decInd N N D tris uA uB u₁ u₂ u₃ (sgn s 0) (sgn s 1) (sgn s 2) (sgn s 3)
        (sgn s 4) (sgn s 5))).length = N := by simp
  have hlenB : ∀ (s u₃ u₂ u₁ : ℕ), ((List.range N).flatMap fun uB => (List.range N).map fun uA =>
      decide (decInd N N D tris uA uB u₁ u₂ u₃ (sgn s 0) (sgn s 1) (sgn s 2) (sgn s 3)
        (sgn s 4) (sgn s 5))).length = N * N := by
    intro s u₃ u₂ u₁
    rw [length_flatMap_const _ _ (fun uB _ => hlenA s u₃ u₂ u₁ uB), List.length_range]
  have hlen1 : ∀ (s u₃ u₂ : ℕ), ((List.range D).flatMap fun u₁ =>
      (List.range N).flatMap fun uB => (List.range N).map fun uA =>
      decide (decInd N N D tris uA uB u₁ u₂ u₃ (sgn s 0) (sgn s 1) (sgn s 2) (sgn s 3)
        (sgn s 4) (sgn s 5))).length = N * N * D := by
    intro s u₃ u₂
    rw [length_flatMap_const _ _ (fun u₁ _ => hlenB s u₃ u₂ u₁), List.length_range]
  have hlen2 : ∀ (s u₃ : ℕ), ((List.range D).flatMap fun u₂ => (List.range D).flatMap fun u₁ =>
      (List.range N).flatMap fun uB => (List.range N).map fun uA =>
      decide (decInd N N D tris uA uB u₁ u₂ u₃ (sgn s 0) (sgn s 1) (sgn s 2) (sgn s 3)
        (sgn s 4) (sgn s 5))).length = N * N * D * D := by
    intro s u₃
    rw [length_flatMap_const _ _ (fun u₂ _ => hlen1 s u₃ u₂), List.length_range]
  have hlen3 : ∀ (s : ℕ), ((List.range D).flatMap fun u₃ => (List.range D).flatMap fun u₂ =>
      (List.range D).flatMap fun u₁ =>
      (List.range N).flatMap fun uB => (List.range N).map fun uA =>
      decide (decInd N N D tris uA uB u₁ u₂ u₃ (sgn s 0) (sgn s 1) (sgn s 2) (sgn s 3)
        (sgn s 4) (sgn s 5))).length = N * N * D * D * D := by
    intro s
    rw [length_flatMap_const _ _ (fun u₃ _ => hlen2 s u₃), List.length_range]
  apply List.ext_getElem?
  intro u
  by_cases hu : u < tableSize N D
  · have hsize : tableSize N D = N * N * D * D * D * 64 := by unfold tableSize; ring
    have hS : idxS N D u < 64 := by
      unfold idxS
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
        Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
      rw [hsize] at hu
      linarith
    have hA : idxA N u < N := Nat.mod_lt _ hN
    have hB : idxB N u < N := Nat.mod_lt _ hN
    have h₁ : idx₁ N D u < D := Nat.mod_lt _ hD
    have h₂ : idx₂ N D u < D := Nat.mod_lt _ hD
    have h₃ : idx₃ N D u < D := Nat.mod_lt _ hD
    -- the loops, from the outside in
    have hpos : u = (idxA N u + N * (idxB N u + N * (idx₁ N D u + D * (idx₂ N D u +
        D * idx₃ N D u)))) + N * N * D * D * D * idxS N D u := by
      conv_lhs => rw [decode_eq (u := u) (N := N) (D := D)]
      ring
    have key : (indLoop N D tris)[u]? = some (decide (IndAt N D tris u)) := by
      unfold indLoop IndAt
      conv_lhs => rw [hpos]
      rw [getElem?_flatMap_const _ _ (fun s _ => hlen3 s) _ (by
        have := add_mul_lt hA (add_mul_lt hB (add_mul_lt h₁ (add_mul_lt h₂ h₃)))
        calc _ < _ := this
          _ = _ := by ring), List.getElem?_range hS, Option.bind_some]
      rw [show idxA N u + N * (idxB N u + N * (idx₁ N D u + D * (idx₂ N D u +
          D * idx₃ N D u))) = (idxA N u + N * (idxB N u + N * (idx₁ N D u + D * idx₂ N D u))) +
          N * N * D * D * idx₃ N D u by ring]
      rw [getElem?_flatMap_const _ _ (fun u₃ _ => hlen2 _ u₃) _ (by
        have := add_mul_lt hA (add_mul_lt hB (add_mul_lt h₁ h₂))
        calc _ < _ := this
          _ = _ := by ring),
        List.getElem?_range h₃, Option.bind_some]
      rw [show idxA N u + N * (idxB N u + N * (idx₁ N D u + D * idx₂ N D u)) =
          (idxA N u + N * (idxB N u + N * idx₁ N D u)) + N * N * D * idx₂ N D u by ring]
      rw [getElem?_flatMap_const _ _ (fun u₂ _ => hlen1 _ _ u₂) _ (by
        have := add_mul_lt hA (add_mul_lt hB h₁)
        calc _ < _ := this
          _ = _ := by ring),
        List.getElem?_range h₂, Option.bind_some]
      rw [show idxA N u + N * (idxB N u + N * idx₁ N D u) =
          (idxA N u + N * idxB N u) + N * N * idx₁ N D u by ring]
      rw [getElem?_flatMap_const _ _ (fun u₁ _ => hlenB _ _ _ u₁) _ (add_mul_lt hA hB),
        List.getElem?_range h₁, Option.bind_some]
      rw [getElem?_flatMap_const _ _ (fun uB _ => hlenA _ _ _ _ uB) _ hA,
        List.getElem?_range hB, Option.bind_some, List.getElem?_map, List.getElem?_range hA,
        Option.map_some]
    rw [key, indTable, List.getElem?_ofFn]
    simp [hu]
  · have h1 : (indTable N D tris)[u]? = none := by
      rw [List.getElem?_eq_none]; simp; omega
    have h2 : (indLoop N D tris)[u]? = none := by
      rw [List.getElem?_eq_none]
      unfold indLoop
      rw [length_flatMap_const _ _ (fun s _ => hlen3 s), List.length_range]
      unfold tableSize at hu
      nlinarith
    rw [h1, h2]

/-- The equation at the index `u`, on five assignments. -/
def EqAt (N D u : ℕ) (fA fB f₁ f₂ f₃ : ℕ → ZMod 2) : Prop :=
  sgn (idxS N D u) 0 * fA (idxA N u) + sgn (idxS N D u) 1 * fB (idxB N u) +
    sgn (idxS N D u) 2 * f₁ (idx₁ N D u) + sgn (idxS N D u) 3 * f₂ (idx₂ N D u) +
    sgn (idxS N D u) 4 * f₃ (idx₃ N D u) = sgn (idxS N D u) 5

/-- **Five assignments satisfy the system a table holds**
(fact:polynomial_condition_for_satisfiability): every equation whose index the table contains
holds. -/
def TableSat (N D : ℕ) (O : BitStr) (fA fB f₁ f₂ f₃ : ℕ → ZMod 2) : Prop :=
  ∀ u < tableSize N D, O.getD u false = true → EqAt N D u fA fB f₁ f₂ f₃

private theorem zmod2_eq_of_add (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  revert a b; decide

/-- The equation at given coordinates in range, from a satisfied table. -/
private theorem tableSat_at {N D : ℕ} {tris : List Tri} {fA fB f₁ f₂ f₃ : ℕ → ZMod 2}
    (h : TableSat N D (indTable N D tris) fA fB f₁ f₂ f₃) (uA uB u₁ u₂ u₃ : ℕ)
    (hA : uA < N) (hB : uB < N) (h₁ : u₁ < D) (h₂ : u₂ < D) (h₃ : u₃ < D)
    (e₀ e₁ e₂ e₃ e₄ e₅ : ZMod 2) (hind : decInd N N D tris uA uB u₁ u₂ u₃ e₀ e₁ e₂ e₃ e₄ e₅) :
    e₀ * fA uA + e₁ * fB uB + e₂ * f₁ u₁ + e₃ * f₂ u₂ + e₄ * f₃ u₃ = e₅ := by
  obtain ⟨s₀, s₁, s₂, s₃, s₄, s₅⟩ := sgn_sgnIdx e₀ e₁ e₂ e₃ e₄ e₅
  have hu := encIdx_lt (D := D) hA hB h₁ h₂ h₃ (sgnIdx_lt e₀ e₁ e₂ e₃ e₄ e₅)
  have hbit : (indTable N D tris).getD (encIdx N D uA uB u₁ u₂ u₃ (sgnIdx e₀ e₁ e₂ e₃ e₄ e₅))
      false = true := by
    rw [getD_indTable hu, decide_eq_true_iff]
    unfold IndAt
    rw [idxA_encIdx hA, idxB_encIdx hA hB, idx₁_encIdx hA hB h₁, idx₂_encIdx hA hB h₁ h₂,
      idx₃_encIdx hA hB h₁ h₂ h₃, idxS_encIdx hA hB h₁ h₂ h₃, s₀, s₁, s₂, s₃, s₄, s₅]
    exact hind
  have := h _ hu hbit
  unfold EqAt at this
  rwa [idxA_encIdx hA, idxB_encIdx hA hB, idx₁_encIdx hA hB h₁, idx₂_encIdx hA hB h₁ h₂,
    idx₃_encIdx hA hB h₁ h₂ h₃, idxS_encIdx hA hB h₁ h₂ h₃, s₀, s₁, s₂, s₃, s₄, s₅] at this

/-- **The table holds the decoupled system** (fact:polynomial_condition_for_satisfiability): on
blocks `[N]`, `[N]` with `N > 0` and copies of `[D] ⊇ [2N]`, five assignments satisfy the table
of a system whose equations are below `D` exactly when they satisfy the system. -/
theorem tableSat_indTable_iff {N D : ℕ} {tris : List Tri} (hN : 0 < N) (hND : N + N ≤ D)
    (hbel : ∀ t ∈ tris, t.Below D) {fA fB f₁ f₂ f₃ : ℕ → ZMod 2} :
    TableSat N D (indTable N D tris) fA fB f₁ f₂ f₃ ↔ DecSat N N D tris fA fB f₁ f₂ f₃ := by
  constructor
  · intro h
    rw [decSat_iff]
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun t ht => ?_⟩
    · have := tableSat_at h j 0 j 0 0 hj hN (by omega) (by omega) (by omega) 1 0 1 0 0 0
        (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩)
      simpa [zmod2_eq_of_add] using this
    · have := tableSat_at h 0 j (N + j) 0 0 hN hj (by omega) (by omega) (by omega) 0 1 1 0 0 0
        (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩))
      simpa [zmod2_eq_of_add] using this
    · have := tableSat_at h 0 0 j j 0 hN hN hj hj (by omega) 0 0 1 1 0 0
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩)))
      simpa [zmod2_eq_of_add] using this
    · have := tableSat_at h 0 0 0 j j hN hN (by omega) hj hj 0 0 0 1 1 0
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩))))
      simpa [zmod2_eq_of_add] using this
    · obtain ⟨hb₁, hb₂, hb₃⟩ := hbel t ht
      have hD : 0 < D := by omega
      have hu : ∀ (a : ZMod 2) (v : ℕ), (a ≠ 0 → v < D) → (if a = 0 then 0 else v) < D := by
        intro a v hv
        split_ifs with h0
        · exact hD
        · exact hv h0
      have hsel : ∀ (a : ZMod 2) (v : ℕ), a ≠ 0 → (if a = 0 then 0 else v) = v :=
        fun a v h0 => ite_eq_right h0
      have := tableSat_at h 0 0 (if t.a₁ = 0 then 0 else t.v₁) (if t.a₂ = 0 then 0 else t.v₂)
        (if t.a₃ = 0 then 0 else t.v₃) hN hN (hu _ _ hb₁) (hu _ _ hb₂) (hu _ _ hb₃)
        0 0 t.a₁ t.a₂ t.a₃ t.b
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, t, ht, rfl, rfl, rfl, rfl,
          hsel _ _, hsel _ _, hsel _ _⟩))))
      have e : ∀ (a : ZMod 2) (f : ℕ → ZMod 2) (v : ℕ),
          a * f (if a = 0 then 0 else v) = a * f v := by
        intro a f v
        by_cases h0 : a = 0
        · simp [h0]
        · rw [ite_eq_right h0]
      unfold Tri.Holds3
      rw [← e t.a₁ f₁ t.v₁, ← e t.a₂ f₂ t.v₂, ← e t.a₃ f₃ t.v₃]
      simpa using this
  · intro h u hu hbit
    rw [getD_indTable hu, decide_eq_true_iff] at hbit
    exact h _ _ _ _ _ _ _ _ _ _ _ hbit

/-! ## The check of the output indicator -/

/-- The rows the output indicator decouples: the purified equations of the constraints `cs` at
the lengths `lRx, lLx, lRy, lLy`, the linear answers in tables of `N` entries. -/
def lsRows (N lRx lLx lRy lLy : ℕ) (aR bR : BitStr) (cs : List BitStr) : List Eqn :=
  cs.map (pureEqn lRx lLx lRy lLy N aR bR)

/-- The table the output indicator expects: that of the decoupled triangulation of the rows, on
copies of `[D]`. -/
def lsTable (N D lRx lLx lRy lLy : ℕ) (aR bR : BitStr) (cs : List BitStr) : BitStr :=
  indTable N D (triangle (N + N) (lsRows N lRx lLx lRy lLy aR bR cs))

/-- **The check of the output indicator** (Definition defn:decider-read), at the table size `N`
and the copy size `D` of the index, the lengths `lRx, lLx` and `lRy, lLy` at the two questions,
and the constraints `cs` that the processor outputs on the readable answers `a^R, b^R` — the
inputs `a = a^R O` and `b = b^R` cut at the readable lengths: the lengths are at most `N`
(step 1), `b` has `N` bits and `O` has `tableSize N D` (steps 1 and 8), there are enough
triangulation variables (step 5), and `O` is the table of the decoupled triangulated purified
system (steps 6 to 8). -/
def LstarOK (N D lRx lLx lRy lLy : ℕ) (cs : List BitStr) (a b : BitStr) : Prop :=
  lRx ≤ N ∧ lLx ≤ N ∧ lRy ≤ N ∧ lLy ≤ N ∧ b.length = N ∧ a.length = N + tableSize N D ∧
    cs.length * (N + N) + (N + N) ≤ D ∧
    a.drop N = lsTable N D lRx lLx lRy lLy (a.take lRx) (b.take lRy) cs

instance (N D lRx lLx lRy lLy : ℕ) (cs : List BitStr) (a b : BitStr) :
    Decidable (LstarOK N D lRx lLx lRy lLy cs a b) := by
  unfold LstarOK; infer_instance

/-- **claim:properties_of_L*, item 1**: the check passes on readable answers of the readable
lengths, padded with zeros to `N` bits, the first followed by the table — the one string `O` it
accepts after them. -/
theorem lstarOK_pad {N D lRx lLx lRy lLy : ℕ} {cs : List BitStr} {aR bR : BitStr}
    (haR : aR.length = lRx) (hbR : bR.length = lRy) (hRx : lRx ≤ N) (hLx : lLx ≤ N)
    (hRy : lRy ≤ N) (hLy : lLy ≤ N) (hD : cs.length * (N + N) + (N + N) ≤ D) :
    LstarOK N D lRx lLx lRy lLy cs
      (aR ++ List.replicate (N - lRx) false ++ lsTable N D lRx lLx lRy lLy aR bR cs)
      (bR ++ List.replicate (N - lRy) false) := by
  have hpre : (aR ++ List.replicate (N - lRx) false).length = N := by simp; omega
  have htakeA : (aR ++ List.replicate (N - lRx) false ++ lsTable N D lRx lLx lRy lLy aR bR cs).take
      lRx = aR := by
    rw [List.append_assoc, ← haR, List.take_left]
  have htakeB : (bR ++ List.replicate (N - lRy) false).take lRy = bR := by
    rw [← hbR, List.take_left]
  refine ⟨hRx, hLx, hRy, hLy, by simp; omega, ?_, hD, ?_⟩
  · simp only [List.length_append, lsTable, length_indTable] at hpre ⊢; omega
  · rw [htakeA, htakeB, List.drop_left' hpre]

/-- **The check as the program makes it**, on the exponents `ℓ` and `◇` of the table size and the
copy size: the table size is read off `b` and checked to be `2^ℓ`, and the copy size is `2^◇`
capped at one more than the length of `O`, so that no power of two larger than the input is ever
written out. It decides `LstarOK` at `(2^ℓ, 2^◇)` (`lstarCheck_eq`). -/
def lstarCheck (ℓ dm lRx lLx lRy lLy : ℕ) (cs : List BitStr) (a b : BitStr) : Bool :=
  decide (min (2 ^ ℓ) (b.length + 1) = b.length) &&
    (decide ((a.drop b.length).length =
        tableSize b.length (min (2 ^ dm) ((a.drop b.length).length + 1))) &&
      (decide (lRx ≤ b.length ∧ lLx ≤ b.length ∧ lRy ≤ b.length ∧ lLy ≤ b.length) &&
        (decide (cs.length * (b.length + b.length) + (b.length + b.length) ≤
            min (2 ^ dm) ((a.drop b.length).length + 1)) &&
          decide (a.drop b.length = lsTable b.length (min (2 ^ dm) ((a.drop b.length).length + 1))
            lRx lLx lRy lLy (a.take lRx) (b.take lRy) cs))))

theorem le_tableSize {N D : ℕ} (hN : 0 < N) : D ≤ tableSize N D := by
  unfold tableSize
  have h1 : D ≤ D * (D * 64) := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp
    · exact Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : D * (D * 64) ≤ D * (D * (D * 64)) := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp
    · nlinarith [Nat.le_mul_of_pos_left (D * 64) hD]
  have h3 : D * (D * (D * 64)) ≤ N * (N * (D * (D * (D * 64)))) := by
    have := Nat.mul_le_mul hN hN
    nlinarith
  omega

/-- The program's check decides `LstarOK` at the table size `2^ℓ` and the copy size `2^◇`. -/
theorem lstarCheck_eq (ℓ dm lRx lLx lRy lLy : ℕ) (cs : List BitStr) (a b : BitStr) :
    lstarCheck ℓ dm lRx lLx lRy lLy cs a b =
      decide (LstarOK (2 ^ ℓ) (2 ^ dm) lRx lLx lRy lLy cs a b) := by
  have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [lstarCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hN, hO, ⟨hRx, hLx, hRy, hLy⟩, hD, hT⟩
    have hb : b.length = 2 ^ ℓ := by
      rcases Nat.le_total (2 ^ ℓ) (b.length + 1) with h | h
      · rw [min_eq_left h] at hN; exact hN.symm
      · rw [min_eq_right h] at hN; omega
    rw [hb] at hO hD hT hRx hLx hRy hLy
    have hcap : min (2 ^ dm) ((a.drop (2 ^ ℓ)).length + 1) = 2 ^ dm := by
      by_contra hne
      have hlt : (a.drop (2 ^ ℓ)).length + 1 < 2 ^ dm := by
        rcases Nat.le_total (2 ^ dm) ((a.drop (2 ^ ℓ)).length + 1) with h | h
        · exact absurd (min_eq_left h) hne
        · rcases Nat.lt_or_ge ((a.drop (2 ^ ℓ)).length + 1) (2 ^ dm) with h' | h'
          · exact h'
          · exact absurd (min_eq_left (by omega)) hne
      have := le_tableSize (D := min (2 ^ dm) ((a.drop (2 ^ ℓ)).length + 1)) hpos
      rw [min_eq_right (by omega)] at this
      rw [min_eq_right (by omega)] at hO
      omega
    rw [hcap] at hO hD hT
    have hT0 : 0 < tableSize (2 ^ ℓ) (2 ^ dm) := by
      have := le_tableSize (D := 2 ^ dm) hpos
      have : 0 < 2 ^ dm := Nat.two_pow_pos dm
      omega
    have ha : a.length = 2 ^ ℓ + tableSize (2 ^ ℓ) (2 ^ dm) := by
      rw [List.length_drop] at hO; omega
    exact ⟨hRx, hLx, hRy, hLy, hb, ha, hD, hT⟩
  · rintro ⟨hRx, hLx, hRy, hLy, hb, ha, hD, hT⟩
    rw [hb]
    have hO : (a.drop (2 ^ ℓ)).length = tableSize (2 ^ ℓ) (2 ^ dm) := by
      rw [List.length_drop, ha]; omega
    have hcap : min (2 ^ dm) ((a.drop (2 ^ ℓ)).length + 1) = 2 ^ dm := by
      have := le_tableSize (D := 2 ^ dm) hpos
      exact min_eq_left (by omega)
    rw [hcap]
    exact ⟨min_eq_left (by omega), hO, ⟨hRx, hLx, hRy, hLy⟩, hD, hT⟩

section game

variable {X : Type*} [Fintype X] (G : TailoredGame X) {x y : X}

theorem lsRows_eq_pureRows {N lRx lLx lRy lLy : ℕ} {aR bR : BitStr} {cs : List BitStr}
    (hRx : G.lenR x = lRx) (hLx : G.lenL x = lLx) (hRy : G.lenR y = lRy) (hLy : G.lenL y = lLy)
    (hcs : G.cons x y aR bR = cs) :
    lsRows N lRx lLx lRy lLy aR bR cs = pureRows G N x y aR bR := by
  subst hRx hLx hRy hLy hcs; rfl

/-- **claim:properties_of_L*, item 2, from the table to the game**: when the check passes on the
lengths and constraints of the game at `(x, y)`, five assignments satisfying the table held by
`a` give answers that the game accepts — the readable answers completed by the first two
blocks, read at the linear lengths. -/
theorem accepts_of_lstarOK {N D lRx lLx lRy lLy : ℕ} {cs : List BitStr} {a b : BitStr}
    (hRx : G.lenR x = lRx) (hLx : G.lenL x = lLx) (hRy : G.lenR y = lRy) (hLy : G.lenL y = lLy)
    (hcs : G.cons x y (a.take lRx) (b.take lRy) = cs) (hN : 0 < N)
    (h : LstarOK N D lRx lLx lRy lLy cs a b) {fA fB f₁ f₂ f₃ : ℕ → ZMod 2}
    (hsat : TableSat N D (a.drop N) fA fB f₁ f₂ f₃) :
    G.Accepts x y (a.take lRx ++ readBlock lLx fA) (b.take lRy ++ readBlock lLy fB) := by
  obtain ⟨hRxN, hLxN, hRyN, hLyN, hb, ha, hD, hO⟩ := h
  rw [hO, lsTable, lsRows_eq_pureRows G hRx hLx hRy hLy hcs] at hsat
  have hx : G.lenL x ≤ N := hLx ▸ hLxN
  have hy : G.lenL y ≤ N := hLy ▸ hLyN
  have hΔ : (G.cons x y (a.take lRx) (b.take lRy)).length * (N + N) ≤ D - (N + N) := by
    rw [hcs]; omega
  have hDeq : N + N + (D - (N + N)) = D := by omega
  have hbel := triangle_below (pureRows_len G hx hy (a.take lRx) (b.take lRy))
    (pureRows_below G hx hy (a.take lRx) (b.take lRy))
    (show (pureRows G N x y (a.take lRx) (b.take lRy)).length * (N + N) ≤ D - (N + N) by
      rw [pureRows, List.length_map]; exact hΔ)
  rw [hDeq] at hbel
  have hdec := (tableSat_indTable_iff hN (by omega) hbel).1 hsat
  have hdec' : DecSat N N (N + N + (D - (N + N)))
      (triangle (N + N) (pureRows G N x y (a.take lRx) (b.take lRy))) fA fB f₁ f₂ f₃ := by
    rw [hDeq]; exact hdec
  have haR : (a.take lRx).length = G.lenR x := by rw [List.length_take]; omega
  have hbR : (b.take lRy).length = G.lenR y := by rw [List.length_take]; omega
  have := accepts_of_decSat G haR hbR hx hy hΔ hdec'
  rwa [hLx, hLy] at this

/-- **claim:properties_of_L*, item 2, from the game to the table**: answers of the right lengths
that the game accepts give the satisfying 5-tuple `Extend` of the table — the table of the
linear answers, and three times its extension, linear in the linear answers with coefficients
read from the readable ones. -/
theorem tableSat_of_accepts {N D : ℕ} {aR aL bR bL : BitStr} (haR : aR.length = G.lenR x)
    (haL : aL.length = G.lenL x) (hbR : bR.length = G.lenR y) (hbL : bL.length = G.lenL y)
    (hN : 0 < N) (hx : G.lenL x ≤ N) (hy : G.lenL y ≤ N)
    (hD : (G.cons x y aR bR).length * (N + N) + (N + N) ≤ D)
    (hacc : G.Accepts x y (aR ++ aL) (bR ++ bL)) :
    TableSat N D
      (lsTable N D (G.lenR x) (G.lenL x) (G.lenR y) (G.lenL y) aR bR (G.cons x y aR bR))
      (tbl N aL bL) (fun j => tbl N aL bL (N + j))
      (ext (N + N) (pureRows G N x y aR bR) (tbl N aL bL))
      (ext (N + N) (pureRows G N x y aR bR) (tbl N aL bL))
      (ext (N + N) (pureRows G N x y aR bR) (tbl N aL bL)) := by
  have hΔ : (pureRows G N x y aR bR).length * (N + N) ≤ D - (N + N) := by
    rw [pureRows, List.length_map]; omega
  have hDeq : N + N + (D - (N + N)) = D := by omega
  have hbel := triangle_below (pureRows_len G hx hy aR bR) (pureRows_below G hx hy aR bR) hΔ
  rw [hDeq] at hbel
  have hdec := decSat_of_accepts G (Δ := D - (N + N)) haR haL hbR hbL hx hy hacc
  rw [hDeq] at hdec
  exact (tableSat_indTable_iff hN (by omega) hbel).2 hdec

end game

end MIPRE.Tailored.AnsRed

end
