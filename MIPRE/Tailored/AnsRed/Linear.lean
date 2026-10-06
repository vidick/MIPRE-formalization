/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Forms
public import MIPRE.Foundations.LowDegree.BinaryLinear

@[expose] public section

/-!
# Linear systems over `F₂`: purification, triangulation and decoupling

Slice P4a of the Aldous–Lyons track (`planning/aldous-lyons-track.md`, §5 "Phase 4 slices"):
the transformations of a system of linear equations that paper II's answer reduction applies
before its PCP (II:7751–8316). The output indicator `L*` (II:8381) computes them from the
constraints of the input game, and the PCP checks the result.

* `Eqn`: an equation `∑_{v ∈ vars} X_v = rhs` over `F₂`, on variables indexed by `ℕ`.
* `pureEqn` (eq:purified_equation, II:7762): a constraint of the canonical decider on the
  answers `a = a^R a^L`, `b = b^R b^L` becomes an equation on the linear answers alone, the
  readable values moved to the right-hand side, the linear answers placed in a table of `2L`
  entries (`a^L` at `0`, `b^L` at `L`). `accepts_iff_pure`: the tailored game accepts exactly
  when the purified equations hold of the table. The paper purifies the input verifier first
  (II:7783); here the indicator purifies on the fly, so the input is not transformed.
* `triangle` (II:7952): each equation `X_{x₀} + ⋯ + X_{x_{k-1}} = b` becomes the chain
  `X_{x₀} = Y₀`, `Y_{i-1} + X_{xᵢ} = Yᵢ`, `Y_{k-1} = b` of equations in at most three
  variables, each row with its own fresh variables `Y` (`yv`). `ext` extends an assignment to
  the fresh variables by the partial sums, a *linear* map (`ext` is a sum over `extVars`);
  `triangle_complete` and `triangle_sound` are the correspondence of solutions
  (rem:prop_triangulated_system).
* `decInd` (II:8193, and the indicator encoding of II:8128): the 5-decoupled system on the
  blocks `S_A, S_B, S₁, S₂, S₃`, the last three copies of all the variables, as the indicator of
  the equations `ε_A X_A + ε_B X_B + ε₁ X¹ + ε₂ X² + ε₃ X³ = ε₀` it contains; a block whose
  sign is `0` takes any index. `decSat_iff` reads off what a solution is.
* `extend_complete`, `decSat_sound` (cor:triang_and_decoupling_extend): a solution `f` gives
  the solution `(f, f(ℓ_A + ·), ext f, ext f, ext f)` of the decoupled triangulated system, and
  the first two blocks of any solution glue to a solution of the original system.
  `accepts_iff_decSat` and `accepts_of_decSat` are the two directions for the canonical
  decider (claim:properties_of_L*, item 2).
-/

namespace MIPRE.Tailored.AnsRed

open Cost Finset
open MIPRE.LowDegree (ofBool)

/-! ## Bits as elements of `F₂` -/

/-- The bit of `s` at `i` as an element of `F₂`, `0` past the end. -/
def bitAt (s : BitStr) (i : ℕ) : ZMod 2 := ofBool (s.getD i false)

@[simp] theorem bitAt_cons_zero (x : Bool) (s : BitStr) : bitAt (x :: s) 0 = ofBool x := rfl

@[simp] theorem bitAt_cons_succ (x : Bool) (s : BitStr) (i : ℕ) :
    bitAt (x :: s) (i + 1) = bitAt s i := rfl

theorem bitAt_append_left {s t : BitStr} {i : ℕ} (h : i < s.length) :
    bitAt (s ++ t) i = bitAt s i := by
  simp [bitAt, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem bitAt_append_right (s t : BitStr) (i : ℕ) : bitAt (s ++ t) (s.length + i) = bitAt t i := by
  simp [bitAt, List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- The `F₂` inner product of two strings of the same length, as a sum. -/
theorem ofBool_dotL : ∀ c v : BitStr, c.length = v.length →
    (ofBool (Intro.dotL c v) : ZMod 2) = ∑ j ∈ range c.length, bitAt c j * bitAt v j
  | [], v, _ => by simp [ofBool]
  | x :: c, [], h => by simp at h
  | x :: c, y :: v, h => by
    rw [Intro.dotL_cons_cons, LowDegree.BinaryLinear.ofBool_xor, LowDegree.BinaryLinear.ofBool_and,
      ofBool_dotL c v (by simpa using h), List.length_cons, sum_range_succ']
    simp only [bitAt_cons_succ, bitAt_cons_zero]
    ring

/-- A sum over the positions of a filtered range. -/
theorem sum_map_filter_range (k : ℕ) (p : ℕ → Bool) (g : ℕ → ZMod 2) :
    (((List.range k).filter p).map g).sum = ∑ j ∈ range k, if p j then g j else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      sum_range_succ]
    rcases Bool.eq_false_or_eq_true (p k) with h | h <;> simp [List.filter, h]

/-! ## Equations -/

/-- A linear equation over `F₂`, `∑_{v ∈ vars} X_v = rhs`, on variables indexed by `ℕ`. -/
structure Eqn where
  /-- The variables with coefficient `1` (with multiplicity, which is counted mod `2`). -/
  vars : List ℕ
  /-- The right-hand side. -/
  rhs : ZMod 2

namespace Eqn

/-- An assignment satisfies the equation. -/
def Holds (e : Eqn) (f : ℕ → ZMod 2) : Prop := (e.vars.map f).sum = e.rhs

/-- The equation mentions only variables below `N`. -/
def Below (e : Eqn) (N : ℕ) : Prop := ∀ v ∈ e.vars, v < N

/-- An equation below `N` holds of two assignments that agree below `N` together. -/
theorem holds_congr {e : Eqn} {N : ℕ} (he : e.Below N) {f g : ℕ → ZMod 2}
    (hfg : ∀ v < N, f v = g v) : e.Holds f ↔ e.Holds g := by
  unfold Holds
  rw [List.map_congr_left fun v hv => hfg v (he v hv)]

end Eqn

/-! ## Purification -/

/-- The positions `j < k` at which `c` has a one at `o + j`. -/
def onesFrom (c : BitStr) (o k : ℕ) : List ℕ := (List.range k).filter fun j => c.getD (o + j) false

theorem mem_onesFrom {c : BitStr} {o k j : ℕ} (h : j ∈ onesFrom c o k) : j < k := by
  unfold onesFrom at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem length_onesFrom_le (c : BitStr) (o k : ℕ) : (onesFrom c o k).length ≤ k :=
  (List.length_filter_le _ _).trans (List.length_range).le

theorem sum_map_onesFrom (c : BitStr) (o k : ℕ) (g : ℕ → ZMod 2) :
    ((onesFrom c o k).map g).sum = ∑ j ∈ range k, bitAt c (o + j) * g j := by
  rw [onesFrom, sum_map_filter_range]
  refine sum_congr rfl fun j _ => ?_
  rcases Bool.eq_false_or_eq_true (c.getD (o + j) false) with h | h <;> simp [bitAt, ofBool]

/-- The linear answers placed in a table of `2L` entries: `a^L` at `0`, `b^L` at `L`. -/
def tbl (L : ℕ) (aL bL : BitStr) (v : ℕ) : ZMod 2 := if v < L then bitAt aL v else bitAt bL (v - L)

/-- **The purified equation** of a constraint `c` (eq:purified_equation): the constraint on the
answers `a^R a^L` (lengths `lRx`, `lLx`) and `b^R b^L` (lengths `lRy`, `lLy`) and the affine
coordinate becomes an equation on the table `tbl L a^L b^L` of the linear answers, the readable
answers `a^R, b^R` entering the right-hand side. A constraint of the wrong length, which the
canonical decider rejects, becomes `0 = 1`. -/
def pureEqn (lRx lLx lRy lLy L : ℕ) (aR bR c : BitStr) : Eqn :=
  if c.length = lRx + lLx + lRy + lLy + 1 then
    ⟨onesFrom c lRx lLx ++ (onesFrom c (lRx + lLx + lRy) lLy).map (L + ·),
      bitAt c (lRx + lLx + lRy + lLy) + ∑ j ∈ range lRx, bitAt c j * bitAt aR j +
        ∑ j ∈ range lRy, bitAt c (lRx + lLx + j) * bitAt bR j⟩
  else ⟨[], 1⟩

/-- The purified equation mentions only the positions of the two linear answers in the table. -/
theorem mem_pureEqn_vars {lRx lLx lRy lLy L : ℕ} {aR bR c : BitStr} {v : ℕ}
    (hv : v ∈ (pureEqn lRx lLx lRy lLy L aR bR c).vars) : v < lLx ∨ (L ≤ v ∧ v - L < lLy) := by
  unfold pureEqn at hv
  split_ifs at hv
  · rcases List.mem_append.1 hv with h | h
    · exact Or.inl (mem_onesFrom h)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
      have := mem_onesFrom hj
      exact Or.inr ⟨by omega, by omega⟩
  · simp at hv

theorem pureEqn_below {lRx lLx lRy lLy L : ℕ} (hx : lLx ≤ L) (hy : lLy ≤ L) (aR bR c : BitStr) :
    (pureEqn lRx lLx lRy lLy L aR bR c).Below (2 * L) := by
  intro v hv
  unfold pureEqn at hv
  split_ifs at hv
  · rcases List.mem_append.1 hv with h | h
    · have := mem_onesFrom h; omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
      have := mem_onesFrom hj; omega
  · simp at hv

theorem length_pureEqn_le {lRx lLx lRy lLy L : ℕ} (hx : lLx ≤ L) (hy : lLy ≤ L)
    (aR bR c : BitStr) : (pureEqn lRx lLx lRy lLy L aR bR c).vars.length ≤ 2 * L := by
  unfold pureEqn
  split_ifs
  · simp only [List.length_append, List.length_map]
    have := length_onesFrom_le c lRx lLx
    have := length_onesFrom_le c (lRx + lLx + lRy) lLy
    omega
  · simp

/-- The parity rearrangement behind purification. -/
private theorem zmod2_rearrange (s t u w z : ZMod 2) :
    s + t + u + w + z = 0 ↔ t + w = z + s + u := by
  revert s t u w z
  decide

/-- **Purification is exact** (fact:completeness_and_soundness_purification, at one pair of
answers): the constraint holds of the answers exactly when its purified equation holds of the
table of their linear parts. -/
theorem satisfies_iff_pureEqn {lRx lLx lRy lLy L : ℕ} {aR aL bR bL : BitStr}
    (haR : aR.length = lRx) (haL : aL.length = lLx) (hbR : bR.length = lRy)
    (hbL : bL.length = lLy) (hx : lLx ≤ L) (c : BitStr) :
    Satisfies c (aR ++ aL ++ (bR ++ bL) ++ [true]) ↔
      (pureEqn lRx lLx lRy lLy L aR bR c).Holds (tbl L aL bL) := by
  by_cases hc : c.length = lRx + lLx + lRy + lLy + 1
  · have hv : (aR ++ aL ++ (bR ++ bL) ++ [true]).length = c.length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [Intro.satisfies_iff_dotL hv.symm, pureEqn, ite_eq_left hc, Eqn.Holds]
    -- the inner product as a sum over the five windows
    have hsum : (ofBool (Intro.dotL c (aR ++ aL ++ (bR ++ bL) ++ [true])) : ZMod 2) =
        ∑ j ∈ range lRx, bitAt c j * bitAt aR j +
        ∑ j ∈ range lLx, bitAt c (lRx + j) * bitAt aL j +
        ∑ j ∈ range lRy, bitAt c (lRx + lLx + j) * bitAt bR j +
        ∑ j ∈ range lLy, bitAt c (lRx + lLx + lRy + j) * bitAt bL j +
        bitAt c (lRx + lLx + lRy + lLy) := by
      rw [ofBool_dotL _ _ hv.symm, hc, sum_range_succ, sum_range_add, sum_range_add,
        sum_range_add]
      have e1 : ∀ j ∈ range lRx,
          bitAt c j * bitAt (aR ++ aL ++ (bR ++ bL) ++ [true]) j = bitAt c j * bitAt aR j := by
        intro j hj
        have hj := mem_range.1 hj
        rw [List.append_assoc, List.append_assoc, bitAt_append_left (by omega)]
      have e2 : ∀ j ∈ range lLx,
          bitAt c (lRx + j) * bitAt (aR ++ aL ++ (bR ++ bL) ++ [true]) (lRx + j) =
            bitAt c (lRx + j) * bitAt aL j := by
        intro j hj
        have hj := mem_range.1 hj
        rw [List.append_assoc, List.append_assoc, ← haR, bitAt_append_right,
          bitAt_append_left (by omega)]
      have e3 : ∀ j ∈ range lRy,
          bitAt c (lRx + lLx + j) * bitAt (aR ++ aL ++ (bR ++ bL) ++ [true]) (lRx + lLx + j) =
            bitAt c (lRx + lLx + j) * bitAt bR j := by
        intro j hj
        have hj := mem_range.1 hj
        have : lRx + lLx + j = (aR ++ aL).length + j := by simp; omega
        rw [this, List.append_assoc, bitAt_append_right, List.append_assoc,
          bitAt_append_left (by omega)]
      have e4 : ∀ j ∈ range lLy,
          bitAt c (lRx + lLx + lRy + j) *
              bitAt (aR ++ aL ++ (bR ++ bL) ++ [true]) (lRx + lLx + lRy + j) =
            bitAt c (lRx + lLx + lRy + j) * bitAt bL j := by
        intro j hj
        have hj := mem_range.1 hj
        have : lRx + lLx + lRy + j = (aR ++ aL ++ bR).length + j := by simp; omega
        rw [this, show aR ++ aL ++ (bR ++ bL) ++ [true] = aR ++ aL ++ bR ++ (bL ++ [true]) by
          simp, bitAt_append_right, bitAt_append_left (by omega)]
      have e5 : bitAt (aR ++ aL ++ (bR ++ bL) ++ [true]) (lRx + lLx + lRy + lLy) = 1 := by
        have : lRx + lLx + lRy + lLy = (aR ++ aL ++ (bR ++ bL)).length + 0 := by simp; omega
        rw [this, bitAt_append_right]
        rfl
      rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3, sum_congr rfl e4, e5, mul_one]
    have hlin : ((onesFrom c lRx lLx ++ (onesFrom c (lRx + lLx + lRy) lLy).map (L + ·)).map
        (tbl L aL bL)).sum =
        ∑ j ∈ range lLx, bitAt c (lRx + j) * bitAt aL j +
          ∑ j ∈ range lLy, bitAt c (lRx + lLx + lRy + j) * bitAt bL j := by
      rw [List.map_append, List.sum_append, List.map_map, sum_map_onesFrom, sum_map_onesFrom]
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        have hj := mem_range.1 hj
        simp only [tbl, ite_eq_left (show j < L by omega)]
      · refine sum_congr rfl fun j _ => ?_
        simp only [Function.comp_apply, tbl, ite_eq_right (show ¬L + j < L by omega),
          Nat.add_sub_cancel_left]
    rw [hlin, ← LowDegree.BinaryLinear.ofBool_injective.eq_iff, hsum]
    change _ = (0 : ZMod 2) ↔ _
    exact zmod2_rearrange _ _ _ _ _
  · have hv : c.length ≠ (aR ++ aL ++ (bR ++ bL) ++ [true]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [pureEqn, ite_eq_right hc]
    simp only [Satisfies, hv, false_and, false_iff, Eqn.Holds, List.map_nil, List.sum_nil]
    decide

/-- **The canonical decider, purified**: a tailored game accepts answers `a^R a^L, b^R b^L` of
the right lengths exactly when the purified equations of its constraints hold of the table of
the linear answers. -/
theorem accepts_iff_pure {X : Type*} [Fintype X] (G : TailoredGame X) (x y : X)
    {aR aL bR bL : BitStr} (haR : aR.length = G.lenR x) (haL : aL.length = G.lenL x)
    (hbR : bR.length = G.lenR y) (hbL : bL.length = G.lenL y) {L : ℕ} (hx : G.lenL x ≤ L) :
    G.Accepts x y (aR ++ aL) (bR ++ bL) ↔
      ∀ e ∈ (G.cons x y aR bR).map (pureEqn (G.lenR x) (G.lenL x) (G.lenR y) (G.lenL y) L aR bR),
        e.Holds (tbl L aL bL) := by
  have htx : (aR ++ aL).take (G.lenR x) = aR := by rw [← haR, List.take_left]
  have hty : (bR ++ bL).take (G.lenR y) = bR := by rw [← hbR, List.take_left]
  unfold TailoredGame.Accepts TailoredGame.len
  simp only [List.length_append, haR, haL, hbR, hbL, true_and, htx, hty, List.forall_mem_map]
  exact forall₂_congr fun c _ =>
    (satisfies_iff_pureEqn haR haL hbR hbL hx c).trans Iff.rfl

/-! ## Triangulation -/

/-- A triangulated equation `a₁ X_{v₁} + a₂ X_{v₂} + a₃ X_{v₃} = b`: at most three variables, in
three slots, which the decoupling sends to three different copies of the variables. A slot with
coefficient `0` is unused, whatever its index. -/
structure Tri where
  v₁ : ℕ
  v₂ : ℕ
  v₃ : ℕ
  a₁ : ZMod 2
  a₂ : ZMod 2
  a₃ : ZMod 2
  b : ZMod 2

namespace Tri

/-- The equation holds of three assignments, one per slot. -/
def Holds3 (t : Tri) (f₁ f₂ f₃ : ℕ → ZMod 2) : Prop :=
  t.a₁ * f₁ t.v₁ + t.a₂ * f₂ t.v₂ + t.a₃ * f₃ t.v₃ = t.b

/-- The equation holds of one assignment. -/
def Holds (t : Tri) (f : ℕ → ZMod 2) : Prop := t.Holds3 f f f

/-- The variables of the used slots are below `ℓ`. -/
def Below (t : Tri) (ℓ : ℕ) : Prop :=
  (t.a₁ ≠ 0 → t.v₁ < ℓ) ∧ (t.a₂ ≠ 0 → t.v₂ < ℓ) ∧ (t.a₃ ≠ 0 → t.v₃ < ℓ)

/-- On three assignments that agree below `ℓ`, an equation below `ℓ` holds of all three iff it
holds of the first. -/
theorem holds3_iff_holds {t : Tri} {ℓ : ℕ} (ht : t.Below ℓ) {f₁ f₂ f₃ : ℕ → ZMod 2}
    (h₁₂ : ∀ j < ℓ, f₁ j = f₂ j) (h₂₃ : ∀ j < ℓ, f₂ j = f₃ j) :
    t.Holds3 f₁ f₂ f₃ ↔ t.Holds f₁ := by
  unfold Holds Holds3
  have e₂ : t.a₂ * f₂ t.v₂ = t.a₂ * f₁ t.v₂ := by
    by_cases h : t.a₂ = 0
    · simp [h]
    · rw [h₁₂ _ (ht.2.1 h)]
  have e₃ : t.a₃ * f₃ t.v₃ = t.a₃ * f₁ t.v₃ := by
    by_cases h : t.a₃ = 0
    · simp [h]
    · rw [← h₂₃ _ (ht.2.2 h), ← h₁₂ _ (ht.2.2 h)]
  rw [e₂, e₃]

end Tri

/-- The fresh variable `Y_{r,i}` of the triangulation: rows of stride `N` after the `N` original
variables. -/
def yv (N r i : ℕ) : ℕ := N + r * N + i

theorem yv_sub_div {N r i : ℕ} (hi : i < N) : (yv N r i - N) / N = r := by
  unfold yv
  rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt hi, Nat.zero_add]

theorem yv_sub_mod {N r i : ℕ} (hi : i < N) : (yv N r i - N) % N = i := by
  unfold yv
  rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hi]

theorem le_yv (N r i : ℕ) : N ≤ yv N r i := by unfold yv; omega

/-- The triangulation of the equation `e`, the `r`-th row: the step equations
`X_{xᵢ} + Y_{r,i-1} + Y_{r,i} = 0` (no `Y_{r,-1}` at `i = 0`), then `Y_{r,k-1} = rhs` (just
`0 = rhs` when `k = 0`). -/
def triRow (N r : ℕ) (e : Eqn) : List Tri :=
  e.vars.mapIdx (fun i x => ⟨x, yv N r (i - 1), yv N r i, 1, if i = 0 then 0 else 1, 1, 0⟩) ++
    [⟨yv N r (e.vars.length - 1), 0, 0, if e.vars.length = 0 then 0 else 1, 0, 0, e.rhs⟩]

/-- **The triangulated system** (II:7952): the rows triangulated one by one. -/
def triangle (N : ℕ) (rows : List Eqn) : List Tri :=
  (rows.mapIdx fun r e => triRow N r e).flatten

theorem mem_triangle {N : ℕ} {rows : List Eqn} {t : Tri} :
    t ∈ triangle N rows ↔ ∃ r, ∃ h : r < rows.length, t ∈ triRow N r rows[r] := by
  unfold triangle
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, ht⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hl
    rw [List.length_mapIdx] at hr
    exact ⟨r, hr, by simpa [List.getElem_mapIdx] using ht⟩
  · rintro ⟨r, hr, ht⟩
    exact ⟨_, List.getElem_mem (l := rows.mapIdx fun r e => triRow N r e)
      (by rw [List.length_mapIdx]; exact hr), by simpa [List.getElem_mapIdx] using ht⟩

/-- The variables whose sum is the extended assignment at `v`: `v` itself below `N`, the prefix
`x₀, …, xᵢ` of the `r`-th row at `Y_{r,i}`, nothing elsewhere. -/
def extVars (N : ℕ) (rows : List Eqn) (v : ℕ) : List ℕ :=
  if v < N then [v]
  else match rows[(v - N) / N]? with
    | some e => if (v - N) % N < e.vars.length then e.vars.take ((v - N) % N + 1) else []
    | none => []

/-- **The extension** of an assignment to the triangulation variables (rem:prop_triangulated_system,
item 1): the partial sums along each row. It is linear, being a sum over `extVars`. -/
def ext (N : ℕ) (rows : List Eqn) (f : ℕ → ZMod 2) (v : ℕ) : ZMod 2 :=
  ((extVars N rows v).map f).sum

/-- The extension reads only the original variables. -/
theorem extVars_below {N : ℕ} {rows : List Eqn} (hbel : ∀ e ∈ rows, e.Below N) (v : ℕ) :
    ∀ u ∈ extVars N rows v, u < N := by
  intro u hu
  unfold extVars at hu
  split_ifs at hu with hv
  · rw [List.mem_singleton] at hu
    exact hu ▸ hv
  · split at hu
    · rename_i e he
      split_ifs at hu
      · exact hbel e (List.mem_of_getElem? he) u (List.mem_of_mem_take hu)
      · simp at hu
    · simp at hu

theorem ext_of_lt {N : ℕ} {rows : List Eqn} {v : ℕ} (hv : v < N) (f : ℕ → ZMod 2) :
    ext N rows f v = f v := by
  simp [ext, extVars, hv]

theorem ext_yv {N : ℕ} {rows : List Eqn} {r i : ℕ} (hr : r < rows.length) (hi : i < N)
    (hk : i < rows[r].vars.length) (f : ℕ → ZMod 2) :
    ext N rows f (yv N r i) = ((rows[r].vars.take (i + 1)).map f).sum := by
  have hn : ¬yv N r i < N := by have := le_yv N r i; omega
  simp only [ext, extVars, ite_eq_right hn, yv_sub_div hi, yv_sub_mod hi,
    List.getElem?_eq_getElem hr,
    ite_eq_left hk]

/-- **Triangulation is complete**: the extension of a solution solves the triangulated system,
when the rows have at most `N` variables, all below `N`. -/
theorem triangle_complete {N : ℕ} {rows : List Eqn} (hlen : ∀ e ∈ rows, e.vars.length ≤ N)
    (hbel : ∀ e ∈ rows, e.Below N) {f : ℕ → ZMod 2} (hf : ∀ e ∈ rows, e.Holds f) :
    ∀ t ∈ triangle N rows, t.Holds (ext N rows f) := by
  intro t ht
  obtain ⟨r, hr, ht⟩ := mem_triangle.1 ht
  have hmem : rows[r] ∈ rows := List.getElem_mem hr
  have hk : rows[r].vars.length ≤ N := hlen _ hmem
  unfold triRow at ht
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 ht
    have hxi : rows[r].vars[i] < N := hbel _ hmem _ (List.getElem_mem hi)
    simp only [Tri.Holds, Tri.Holds3, one_mul]
    rw [ext_of_lt hxi, ext_yv hr (by omega) hi]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [↓reduceIte, zero_mul, add_zero, zero_add, List.take_one]
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi]
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      exact CharTwo.add_self_eq_zero _
    · rw [ite_eq_right (by omega), one_mul, ext_yv hr (by omega) (by omega)]
      rw [show i - 1 + 1 = i by omega]
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, add_zero]
      generalize ((rows[r].vars.take i).map f).sum = s
      generalize f rows[r].vars[i] = z
      revert s z
      decide
  · rw [List.mem_singleton] at ht
    subst ht
    simp only [Tri.Holds, Tri.Holds3, zero_mul, add_zero]
    have hfe := hf _ hmem
    unfold Eqn.Holds at hfe
    rcases Nat.eq_zero_or_pos rows[r].vars.length with h0 | hpos
    · rw [ite_eq_left h0, zero_mul]
      rw [List.length_eq_zero_iff.1 h0] at hfe
      simpa using hfe
    · rw [ite_eq_right (by omega), one_mul, ext_yv hr (by omega) (by omega),
        show rows[r].vars.length - 1 + 1 = rows[r].vars.length by omega, List.take_length]
      exact hfe

/-- The step equations force the partial sums. -/
private theorem partial_sums {N r : ℕ} {e : Eqn} {g : ℕ → ZMod 2}
    (hstep : ∀ t ∈ triRow N r e, t.Holds g) :
    ∀ i, i < e.vars.length → g (yv N r i) = ((e.vars.take (i + 1)).map g).sum := by
  intro i hi
  induction i with
  | zero =>
    have h := hstep _ (List.mem_append_left _ (List.mem_mapIdx.2 ⟨0, hi, rfl⟩))
    simp only [Tri.Holds, Tri.Holds3, one_mul, ↓reduceIte, zero_mul, add_zero] at h
    rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem hi]
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    generalize g e.vars[0] = a at h
    generalize g (yv N r 0) = b at h
    revert a b
    decide
  | succ i ih =>
    have h := hstep _ (List.mem_append_left _ (List.mem_mapIdx.2 ⟨i + 1, hi, rfl⟩))
    simp only [Tri.Holds, Tri.Holds3, one_mul, Nat.add_sub_cancel, Nat.succ_ne_zero,
      ↓reduceIte] at h
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    rw [← ih (by omega)]
    generalize g e.vars[i + 1] = a at h
    generalize g (yv N r i) = b at h
    generalize g (yv N r (i + 1)) = c at h
    revert a b c
    decide

/-- **Triangulation is sound**: a solution of the triangulated system solves every row. -/
theorem triangle_sound {N : ℕ} {rows : List Eqn} {g : ℕ → ZMod 2}
    (hg : ∀ t ∈ triangle N rows, t.Holds g) : ∀ e ∈ rows, e.Holds g := by
  intro e he
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 he
  have hrow : ∀ t ∈ triRow N r rows[r], t.Holds g := fun t ht => hg t (mem_triangle.2 ⟨r, hr, ht⟩)
  have hfin := hrow _ (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [Tri.Holds, Tri.Holds3, zero_mul, add_zero] at hfin
  unfold Eqn.Holds
  rcases Nat.eq_zero_or_pos rows[r].vars.length with h0 | hpos
  · rw [ite_eq_left h0, zero_mul] at hfin
    rw [List.length_eq_zero_iff.1 h0]
    simpa using hfin
  · rw [ite_eq_right (by omega), one_mul, partial_sums hrow _ (by omega),
      show rows[r].vars.length - 1 + 1 = rows[r].vars.length by omega, List.take_length] at hfin
    exact hfin

/-- Every equation of the triangulated system of `R` rows of at most `N` variables, all below
`N`, is below `N + Δ` when `R N ≤ Δ`. -/
theorem triangle_below {N Δ : ℕ} {rows : List Eqn} (hlen : ∀ e ∈ rows, e.vars.length ≤ N)
    (hbel : ∀ e ∈ rows, e.Below N) (hΔ : rows.length * N ≤ Δ) :
    ∀ t ∈ triangle N rows, t.Below (N + Δ) := by
  intro t ht
  obtain ⟨r, hr, ht⟩ := mem_triangle.1 ht
  have hmem : rows[r] ∈ rows := List.getElem_mem hr
  have hk := hlen _ hmem
  have hyv : ∀ i < N, yv N r i < N + Δ := by
    intro i hi
    unfold yv
    have : (r + 1) * N ≤ rows.length * N := Nat.mul_le_mul_right _ hr
    rw [Nat.add_mul, one_mul] at this
    omega
  unfold triRow at ht
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 ht
    refine ⟨fun _ => ?_, fun h => ?_, fun _ => hyv i (by omega)⟩
    · have := hbel _ hmem _ (List.getElem_mem hi); dsimp only; omega
    · have hi0 : i ≠ 0 := by intro h0; simp [h0] at h
      exact hyv _ (by omega)
  · rw [List.mem_singleton] at ht
    subst ht
    refine ⟨fun h => ?_, fun h => absurd rfl h, fun h => absurd rfl h⟩
    have : rows[r].vars.length ≠ 0 := by intro h0; simp [h0] at h
    exact hyv _ (by omega)

/-! ## Decoupling -/

/-- **The indicator of the 5-decoupled system** (II:8193, encoded as in II:8128): whether the
equation `ε_A X_A(u_A) + ε_B X_B(u_B) + ε₁ X¹(u₁) + ε₂ X²(u₂) + ε₃ X³(u₃) = ε₀` is in the system
on the blocks `S_A = [ℓ_A]`, `S_B = [ℓ_B]` and three copies `S₁, S₂, S₃` of `[ℓ]`, whose
equations are `X_A = X¹` on `S_A`, `X_B = X¹(ℓ_A + ·)` on `S_B`, `X¹ = X²` and `X² = X³` on
`[ℓ]`, and each triangulated equation of `tris` on the three copies. A block whose sign is `0`
takes any index. -/
def decInd (ℓA ℓB ℓ : ℕ) (tris : List Tri) (uA uB u₁ u₂ u₃ : ℕ)
    (εA εB ε₁ ε₂ ε₃ ε₀ : ZMod 2) : Prop :=
  (εA = 1 ∧ εB = 0 ∧ ε₁ = 1 ∧ ε₂ = 0 ∧ ε₃ = 0 ∧ ε₀ = 0 ∧ uA < ℓA ∧ u₁ = uA) ∨
  (εA = 0 ∧ εB = 1 ∧ ε₁ = 1 ∧ ε₂ = 0 ∧ ε₃ = 0 ∧ ε₀ = 0 ∧ uB < ℓB ∧ u₁ = ℓA + uB) ∨
  (εA = 0 ∧ εB = 0 ∧ ε₁ = 1 ∧ ε₂ = 1 ∧ ε₃ = 0 ∧ ε₀ = 0 ∧ u₁ < ℓ ∧ u₂ = u₁) ∨
  (εA = 0 ∧ εB = 0 ∧ ε₁ = 0 ∧ ε₂ = 1 ∧ ε₃ = 1 ∧ ε₀ = 0 ∧ u₂ < ℓ ∧ u₃ = u₂) ∨
  (εA = 0 ∧ εB = 0 ∧ ∃ t ∈ tris, ε₁ = t.a₁ ∧ ε₂ = t.a₂ ∧ ε₃ = t.a₃ ∧ ε₀ = t.b ∧
    (t.a₁ ≠ 0 → u₁ = t.v₁) ∧ (t.a₂ ≠ 0 → u₂ = t.v₂) ∧ (t.a₃ ≠ 0 → u₃ = t.v₃))

instance (ℓA ℓB ℓ : ℕ) (tris : List Tri) (uA uB u₁ u₂ u₃ : ℕ) (εA εB ε₁ ε₂ ε₃ ε₀ : ZMod 2) :
    Decidable (decInd ℓA ℓB ℓ tris uA uB u₁ u₂ u₃ εA εB ε₁ ε₂ ε₃ ε₀) := by
  unfold decInd; infer_instance

/-- Five assignments satisfy the decoupled system (fact:polynomial_condition_for_satisfiability):
every equation of the indicator holds. -/
def DecSat (ℓA ℓB ℓ : ℕ) (tris : List Tri) (fA fB f₁ f₂ f₃ : ℕ → ZMod 2) : Prop :=
  ∀ uA uB u₁ u₂ u₃ εA εB ε₁ ε₂ ε₃ ε₀, decInd ℓA ℓB ℓ tris uA uB u₁ u₂ u₃ εA εB ε₁ ε₂ ε₃ ε₀ →
    εA * fA uA + εB * fB uB + ε₁ * f₁ u₁ + ε₂ * f₂ u₂ + ε₃ * f₃ u₃ = ε₀

private theorem zmod2_eq_of_add (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  revert a b; decide

/-- **What a solution of the decoupled system is**: the copy equations and the triangulated
equations on the three copies. -/
theorem decSat_iff {ℓA ℓB ℓ : ℕ} {tris : List Tri} {fA fB f₁ f₂ f₃ : ℕ → ZMod 2} :
    DecSat ℓA ℓB ℓ tris fA fB f₁ f₂ f₃ ↔
      (∀ j < ℓA, fA j = f₁ j) ∧ (∀ j < ℓB, fB j = f₁ (ℓA + j)) ∧ (∀ j < ℓ, f₁ j = f₂ j) ∧
        (∀ j < ℓ, f₂ j = f₃ j) ∧ ∀ t ∈ tris, t.Holds3 f₁ f₂ f₃ := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun t ht => ?_⟩
    · have := h j 0 j 0 0 1 0 1 0 0 0 (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩)
      simpa [zmod2_eq_of_add] using this
    · have := h 0 j (ℓA + j) 0 0 0 1 1 0 0 0
        (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩))
      simpa [zmod2_eq_of_add] using this
    · have := h 0 0 j j 0 0 0 1 1 0 0
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩)))
      simpa [zmod2_eq_of_add] using this
    · have := h 0 0 0 j j 0 0 0 1 1 0
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, hj, rfl⟩))))
      simpa [zmod2_eq_of_add] using this
    · have := h 0 0 t.v₁ t.v₂ t.v₃ 0 0 t.a₁ t.a₂ t.a₃ t.b
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, t, ht, rfl, rfl, rfl, rfl, fun _ => rfl,
          fun _ => rfl, fun _ => rfl⟩))))
      simpa [Tri.Holds3] using this
  · rintro ⟨hA, hB, h12, h23, ht⟩ uA uB u₁ u₂ u₃ εA εB ε₁ ε₂ ε₃ ε₀ hd
    rcases hd with ⟨rfl, rfl, rfl, rfl, rfl, rfl, hu, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, hu, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, hu, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, hu, rfl⟩ |
      ⟨rfl, rfl, t, htm, rfl, rfl, rfl, rfl, h₁, h₂, h₃⟩
    · simp [hA _ hu, CharTwo.add_self_eq_zero]
    · simp [hB _ hu, CharTwo.add_self_eq_zero]
    · simp [h12 _ hu, CharTwo.add_self_eq_zero]
    · simp [h23 _ hu, CharTwo.add_self_eq_zero]
    · have key := ht t htm
      unfold Tri.Holds3 at key
      have e₁ : t.a₁ * f₁ u₁ = t.a₁ * f₁ t.v₁ := by
        by_cases h : t.a₁ = 0
        · simp [h]
        · rw [h₁ h]
      have e₂ : t.a₂ * f₂ u₂ = t.a₂ * f₂ t.v₂ := by
        by_cases h : t.a₂ = 0
        · simp [h]
        · rw [h₂ h]
      have e₃ : t.a₃ * f₃ u₃ = t.a₃ * f₃ t.v₃ := by
        by_cases h : t.a₃ = 0
        · simp [h]
        · rw [h₃ h]
      simp only [zero_mul, zero_add]
      rw [e₁, e₂, e₃, key]

/-! ## Triangulation and decoupling together -/

/-- The two first blocks glued into one assignment of the original variables: `f_A` below `ℓ_A`,
`f_B` shifted above. -/
def glue (ℓA : ℕ) (fA fB : ℕ → ZMod 2) (v : ℕ) : ZMod 2 := if v < ℓA then fA v else fB (v - ℓA)

/-- **`Extend` is complete** (cor:triang_and_decoupling_extend): a solution `f` of `R` rows of at
most `N = ℓ_A + ℓ_B` variables, all below `N`, gives the solution
`(f, f(ℓ_A + ·), ext f, ext f, ext f)` of the decoupled triangulated system with `Δ ≥ R N`
triangulation variables. The last three blocks are linear in `f` (`ext`). -/
theorem extend_complete {ℓA ℓB Δ : ℕ} {rows : List Eqn}
    (hlen : ∀ e ∈ rows, e.vars.length ≤ ℓA + ℓB) (hbel : ∀ e ∈ rows, e.Below (ℓA + ℓB))
    {f : ℕ → ZMod 2} (hf : ∀ e ∈ rows, e.Holds f) :
    DecSat ℓA ℓB (ℓA + ℓB + Δ) (triangle (ℓA + ℓB) rows) f (fun j => f (ℓA + j))
      (ext (ℓA + ℓB) rows f) (ext (ℓA + ℓB) rows f) (ext (ℓA + ℓB) rows f) := by
  rw [decSat_iff]
  refine ⟨fun j hj => (ext_of_lt (by omega) f).symm, fun j hj => (ext_of_lt (by omega) f).symm,
    fun _ _ => rfl, fun _ _ => rfl, fun t ht => triangle_complete hlen hbel hf t ht⟩

/-- **Every solution of the decoupled triangulated system comes from a solution of the
original** (cor:triang_and_decoupling_extend): its first two blocks, glued, solve the rows. -/
theorem decSat_sound {ℓA ℓB Δ : ℕ} {rows : List Eqn}
    (hlen : ∀ e ∈ rows, e.vars.length ≤ ℓA + ℓB) (hbel : ∀ e ∈ rows, e.Below (ℓA + ℓB))
    (hΔ : rows.length * (ℓA + ℓB) ≤ Δ) {fA fB f₁ f₂ f₃ : ℕ → ZMod 2}
    (h : DecSat ℓA ℓB (ℓA + ℓB + Δ) (triangle (ℓA + ℓB) rows) fA fB f₁ f₂ f₃) :
    ∀ e ∈ rows, e.Holds (glue ℓA fA fB) := by
  obtain ⟨hA, hB, h12, h23, ht⟩ := decSat_iff.1 h
  have hbelow := triangle_below hlen hbel hΔ
  have h1 : ∀ e ∈ rows, e.Holds f₁ :=
    triangle_sound fun t htm => (Tri.holds3_iff_holds (hbelow t htm) h12 h23).1 (ht t htm)
  intro e he
  refine (Eqn.holds_congr (hbel e he) fun v hv => ?_).1 (h1 e he)
  unfold glue
  split_ifs with hvA
  · exact (hA v hvA).symm
  · rw [hB (v - ℓA) (by omega), Nat.add_sub_cancel' (by omega)]

/-! ## The canonical decider, decoupled -/

/-- The purified equations of a pair of questions, with the linear answers in tables of `L`
entries. -/
def pureRows {X : Type*} [Fintype X] (G : TailoredGame X) (L : ℕ) (x y : X) (aR bR : BitStr) :
    List Eqn :=
  (G.cons x y aR bR).map (pureEqn (G.lenR x) (G.lenL x) (G.lenR y) (G.lenL y) L aR bR)

theorem pureRows_len {X : Type*} [Fintype X] (G : TailoredGame X) {L : ℕ} {x y : X}
    (hx : G.lenL x ≤ L) (hy : G.lenL y ≤ L) (aR bR : BitStr) :
    ∀ e ∈ pureRows G L x y aR bR, e.vars.length ≤ L + L := by
  intro e he
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 he
  have := length_pureEqn_le (lRx := G.lenR x) (lRy := G.lenR y) hx hy aR bR c
  omega

theorem pureRows_below {X : Type*} [Fintype X] (G : TailoredGame X) {L : ℕ} {x y : X}
    (hx : G.lenL x ≤ L) (hy : G.lenL y ≤ L) (aR bR : BitStr) :
    ∀ e ∈ pureRows G L x y aR bR, e.Below (L + L) := by
  intro e he v hv
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 he
  have := pureEqn_below (lRx := G.lenR x) (lRy := G.lenR y) hx hy aR bR c v hv
  omega

/-- **The canonical decider, triangulated and decoupled** (claim:properties_of_L*, item 2, one
direction): answers of the right lengths that the game accepts give the solution `Extend` of the
table of their linear parts of the decoupled triangulated purified system, with `Δ` at least the
number of constraints times `2L`. -/
theorem decSat_of_accepts {X : Type*} [Fintype X] (G : TailoredGame X) {x y : X}
    {aR aL bR bL : BitStr} (haR : aR.length = G.lenR x) (haL : aL.length = G.lenL x)
    (hbR : bR.length = G.lenR y) (hbL : bL.length = G.lenL y) {L Δ : ℕ} (hx : G.lenL x ≤ L)
    (hy : G.lenL y ≤ L) (hacc : G.Accepts x y (aR ++ aL) (bR ++ bL)) :
    DecSat L L (L + L + Δ) (triangle (L + L) (pureRows G L x y aR bR)) (tbl L aL bL)
      (fun j => tbl L aL bL (L + j)) (ext (L + L) (pureRows G L x y aR bR) (tbl L aL bL))
      (ext (L + L) (pureRows G L x y aR bR) (tbl L aL bL))
      (ext (L + L) (pureRows G L x y aR bR) (tbl L aL bL)) :=
  extend_complete (pureRows_len G hx hy aR bR) (pureRows_below G hx hy aR bR)
    ((accepts_iff_pure G x y haR haL hbR hbL hx).1 hacc)

/-- The linear answer of length `k` read from a block. -/
def readBlock (k : ℕ) (f : ℕ → ZMod 2) : BitStr :=
  List.ofFn fun j : Fin k => LowDegree.BinaryLinear.bit (f j)

@[simp] theorem length_readBlock (k : ℕ) (f : ℕ → ZMod 2) : (readBlock k f).length = k := by
  simp [readBlock]

theorem bitAt_readBlock {k : ℕ} {f : ℕ → ZMod 2} {j : ℕ} (hj : j < k) :
    bitAt (readBlock k f) j = f j := by
  simp [bitAt, readBlock, List.getD_eq_getElem?_getD, hj]

/-- **The canonical decider from a solution of the decoupled system** (claim:properties_of_L*,
item 2, the other direction): if five assignments solve the decoupled triangulated purified
system of the readable answers, with `Δ` at least the number of constraints times `2L`, the
game accepts the readable answers completed by the first two blocks, read at the linear lengths. -/
theorem accepts_of_decSat {X : Type*} [Fintype X] (G : TailoredGame X) {x y : X}
    {aR bR : BitStr} (haR : aR.length = G.lenR x) (hbR : bR.length = G.lenR y) {L Δ : ℕ}
    (hx : G.lenL x ≤ L) (hy : G.lenL y ≤ L)
    (hΔ : (G.cons x y aR bR).length * (L + L) ≤ Δ) {fA fB f₁ f₂ f₃ : ℕ → ZMod 2}
    (h : DecSat L L (L + L + Δ) (triangle (L + L) (pureRows G L x y aR bR)) fA fB f₁ f₂ f₃) :
    G.Accepts x y (aR ++ readBlock (G.lenL x) fA) (bR ++ readBlock (G.lenL y) fB) := by
  have hrows := decSat_sound (pureRows_len G hx hy aR bR) (pureRows_below G hx hy aR bR)
    (by rw [pureRows, List.length_map]; exact hΔ) h
  rw [accepts_iff_pure G x y haR (length_readBlock _ _) hbR (length_readBlock _ _) hx]
  intro e he
  have hc := hrows e he
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 he
  unfold Eqn.Holds at hc ⊢
  rw [← hc]
  congr 1
  refine List.map_congr_left fun v hv => ?_
  rcases mem_pureEqn_vars hv with h | ⟨h1, h2⟩
  · simp only [tbl, glue, ite_eq_left (show v < L by omega)]
    exact bitAt_readBlock h
  · simp only [tbl, glue, ite_eq_right (show ¬v < L by omega)]
    exact bitAt_readBlock h2

end MIPRE.Tailored.AnsRed

end
