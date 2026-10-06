/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.ZStrat
public import MIPRE.Tactics

@[expose] public section

/-!
# The trace identity of a Z-aligned permutation strategy

The analytic heart of paper I's Proposition I:2279 and of the completeness of Theorem I:2126,
by a trace identity in place of the paper's Fourier bases and orbit intersections
(`planning/aldous-lyons-track.md`, *A shorter route for the analytic heart*).

For a Z-aligned permutation strategy `S` the readable observables at `x` are `±1` diagonals,
so each basis point `j` carries readable signs `rsgn x j`, and the projection `P_a` vanishes
outside the rows and columns whose readable signs are `a`'s readable part
(`proj_apply_eq_zero_of_row`, `proj_apply_eq_zero_of_col`). Hence, for any set `G` of readable
values and any matrix `X` (`sum_trace_proj_mul_mul_proj`),

`∑_{a, b : (a^R, b^R) ∈ G} Tr(P_a X Q_b) = ∑_{j : (rsgn x j, rsgn y j) ∈ G} X_{jj}`.

A constraint `c` at `(x, y)` gives the matrix `consMat c = (-1)^{c_J} U^α V^β` (or `-1` for a
constraint of the wrong length), and `P_a consMat Q_b = (-1)^{consBit} P_a Q_b`, where
`consBit = false` exactly when `a b 1` satisfies `c` (`proj_mul_consMat_mul_proj`,
`satisfies_iff_consBit`). So the violation of `c` is `P_a (1 - consMat)/2 Q_b`
(`ite_satisfies_smul`), and its probability on a readable class is a sum of diagonal entries.
-/

namespace MIPRE.Tailored.Sofic

open TailoredGameValue

theorem lenAt_le_ansLen_fin (g : TailoredGameData) (x : Fin (g.nV + 1)) :
    g.lenAt x.val ≤ g.ansLen :=
  Finset.le_sup (f := fun x : Fin (g.nV + 1) => g.lenAt x.val) (Finset.mem_univ x)

theorem lenRAt_le_ansLen (g : TailoredGameData) (x : Fin (g.nV + 1)) :
    g.lenRAt x.val ≤ g.ansLen :=
  (Nat.le_add_right _ _).trans (lenAt_le_ansLen_fin g x)

/-! ## Readable signs -/

namespace ZStrat

variable {g : TailoredGameData} (S : ZStrat g)

/-- The sign bit (`true` for `-1`) of the observable `U x i` at the basis point `j`, read on
the diagonal. -/
noncomputable def rbit (x : Fin (g.nV + 1)) (i : ℕ) (j : Fin S.m) : Bool :=
  if h : i < g.ansLen then decide (S.U x ⟨i, h⟩ j j = -1) else false

/-- The readable signs at `x` of the basis point `j`. -/
noncomputable def rsgn (x : Fin (g.nV + 1)) (j : Fin S.m) : List Bool :=
  (List.range (g.lenRAt x.val)).map fun i => S.rbit x i j

/-- A readable observable is the diagonal of its sign bits. -/
theorem U_eq_diagonal (x : Fin (g.nV + 1)) (i : Fin g.ansLen) (hi : i.val < g.lenRAt x.val) :
    S.U x i = Matrix.diagonal fun j => bitSign (S.rbit x i j) := by
  obtain ⟨σ, s, h⟩ := S.signedPerm x i
  have hd := S.zAligned x i hi
  rw [h, isDiag_signedPermMatrix_iff] at hd
  subst hd
  rw [h, signedPermMatrix_one]
  congr 1
  funext j
  have hrb : S.rbit x i j = s j := by
    rw [rbit, dite_eq_left i.isLt, h, signedPermMatrix_one, Matrix.diagonal_apply_eq]
    cases s j <;> norm_num [bitSign]
  rw [hrb]

theorem readable_eq_rsgn_iff (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) (j : Fin S.m) :
    g.readable x a = S.rsgn x j ↔
      ∀ i : Fin g.ansLen, i.val < g.lenRAt x.val → a i = S.rbit x i j := by
  constructor
  · intro h i hi
    have h' := congrArg (fun l : List Bool => l.getD i.val false) h
    simp only [TailoredGameData.readable, rsgn, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some] at h'
    rwa [TailoredGameData.bit, dite_eq_left i.isLt] at h'
  · intro h
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < g.lenRAt x.val := List.mem_range.mp hi
    have hΛ : i < g.ansLen := hi'.trans_le (lenRAt_le_ansLen g x)
    rw [TailoredGameData.bit, dite_eq_left hΛ]
    exact h ⟨i, hΛ⟩ hi'

/-- **`P_a` vanishes on the rows whose readable signs are not `a`'s.** -/
theorem proj_apply_eq_zero_of_row (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) (j k : Fin S.m)
    (h : g.readable x a ≠ S.rsgn x j) : S.proj x a j k = 0 := by
  rw [Ne, readable_eq_rsgn_iff] at h
  push Not at h
  obtain ⟨i, hi, hne⟩ := h
  have h1 := congrFun (congrFun (S.U_mul_proj x i a) j) k
  rw [S.U_eq_diagonal x i hi, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at h1
  have h2 : (bitSign (S.rbit x i j) - bitSign (a i)) * S.proj x a j k = 0 := by
    rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (bitSign_injective (sub_eq_zero.mp h3)).symm hne
  · exact h3

/-- **`P_a` vanishes on the columns whose readable signs are not `a`'s.** -/
theorem proj_apply_eq_zero_of_col (x : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) (j k : Fin S.m)
    (h : g.readable x a ≠ S.rsgn x k) : S.proj x a j k = 0 := by
  rw [Ne, readable_eq_rsgn_iff] at h
  push Not at h
  obtain ⟨i, hi, hne⟩ := h
  have h1 := congrFun (congrFun (S.proj_mul_U x i a) j) k
  rw [S.U_eq_diagonal x i hi, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at h1
  have h2 : S.proj x a j k * (bitSign (S.rbit x i k) - bitSign (a i)) = 0 := by
    rw [mul_sub, h1, mul_comm, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (bitSign_injective (sub_eq_zero.mp h3)).symm hne

/-! ## The trace identity -/

/-- **The trace identity**: for a set `G` of readable values and any matrix `X`,
`∑_{a, b : (a^R, b^R) ∈ G} Tr(P_a X Q_b) = ∑_{j : (rsgn x j, rsgn y j) ∈ G} X_{jj}`. -/
theorem sum_trace_proj_mul_mul_proj (x y : Fin (g.nV + 1)) (G : List Bool → Prop)
    [DecidablePred G] (X : Matrix (Fin S.m) (Fin S.m) ℂ) :
    ∑ a, ∑ b, (if G (g.readable x a ++ g.readable y b) then
        (S.proj x a * X * S.proj y b).trace else 0) =
      ∑ j, if G (S.rsgn x j ++ S.rsgn y j) then X j j else 0 := by
  -- move `Q_b` to the front
  have h1 : ∀ a b, (S.proj x a * X * S.proj y b).trace =
      ∑ j, ∑ k, (S.proj y b * S.proj x a) j k * X k j := by
    intro a b
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
  -- the readable class of a nonzero entry of `Q_b P_a`
  have h2 : ∀ a b j k, (if G (g.readable x a ++ g.readable y b) then
      (S.proj y b * S.proj x a) j k * X k j else 0) =
      if G (S.rsgn x k ++ S.rsgn y j) then (S.proj y b * S.proj x a) j k * X k j else 0 := by
    intro a b j k
    by_cases hb : g.readable y b = S.rsgn y j
    · by_cases ha : g.readable x a = S.rsgn x k
      · rw [ha, hb]
      · have : (S.proj y b * S.proj x a) j k = 0 := by
          rw [Matrix.mul_apply]
          exact Finset.sum_eq_zero fun l _ => by
            rw [S.proj_apply_eq_zero_of_col x a l k ha, mul_zero]
        simp [this]
    · have : (S.proj y b * S.proj x a) j k = 0 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_eq_zero fun l _ => by
          rw [S.proj_apply_eq_zero_of_row y b j l hb, zero_mul]
      simp [this]
  have h3 : ∀ j k, ∑ a, ∑ b, (S.proj y b * S.proj x a) j k = (1 : Matrix (Fin S.m) (Fin S.m) ℂ) j k := by
    intro j k
    rw [← (S.isPVMIn_proj y).sum_eq_one, ← Matrix.mul_one (∑ b, S.proj y b),
      ← (S.isPVMIn_proj x).sum_eq_one, Matrix.sum_mul, Matrix.sum_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_apply]
  calc ∑ a, ∑ b, (if G (g.readable x a ++ g.readable y b) then
        (S.proj x a * X * S.proj y b).trace else 0)
      = ∑ a, ∑ b, ∑ j, ∑ k, (if G (g.readable x a ++ g.readable y b) then
          (S.proj y b * S.proj x a) j k * X k j else 0) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [h1]
        split_ifs <;> simp
    _ = ∑ j, ∑ k, (if G (S.rsgn x k ++ S.rsgn y j) then
          (∑ a, ∑ b, (S.proj y b * S.proj x a) j k) * X k j else 0) := by
        simp_rw [h2]
        have h4 : ∀ j k, (if G (S.rsgn x k ++ S.rsgn y j) then
            (∑ a, ∑ b, (S.proj y b * S.proj x a) j k) * X k j else 0) =
            ∑ a, ∑ b, (if G (S.rsgn x k ++ S.rsgn y j) then
              (S.proj y b * S.proj x a) j k * X k j else 0) := by
          intro j k
          split_ifs <;> simp [Finset.sum_mul]
        simp_rw [h4]
        calc _ = ∑ a, ∑ j, ∑ b, ∑ k, (if G (S.rsgn x k ++ S.rsgn y j) then
              (S.proj y b * S.proj x a) j k * X k j else 0) :=
              Finset.sum_congr rfl fun a _ => Finset.sum_comm
          _ = ∑ j, ∑ a, ∑ b, ∑ k, (if G (S.rsgn x k ++ S.rsgn y j) then
              (S.proj y b * S.proj x a) j k * X k j else 0) := Finset.sum_comm
          _ = ∑ j, ∑ a, ∑ k, ∑ b, (if G (S.rsgn x k ++ S.rsgn y j) then
              (S.proj y b * S.proj x a) j k * X k j else 0) :=
              Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, if G (S.rsgn x j ++ S.rsgn y j) then X j j else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp_rw [h3]
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          simp [Matrix.one_apply_ne' hk]
        · simp

end ZStrat

/-! ## Constraints -/

section Constraints

variable (g : TailoredGameData) (x y : Fin (g.nV + 1))

/-- The coefficients of a constraint on the variables at `x`. -/
def coefX (c : List Bool) : Fin g.ansLen → Bool :=
  fun i => decide (i.val < g.lenAt x.val) && c.getD i.val false

/-- The coefficients of a constraint on the variables at `y`. -/
def coefY (c : List Bool) : Fin g.ansLen → Bool :=
  fun i => decide (i.val < g.lenAt y.val) && c.getD (g.lenAt x.val + i.val) false

/-- The coefficient of a constraint on `J`. -/
def coefJ (c : List Bool) : Bool := c.getD (g.lenAt x.val + g.lenAt y.val) false

/-- The bit `⟨c, a b 1⟩` over `F₂`, `true` for a constraint of the wrong length, which is
never satisfied. -/
def consBit (c : List Bool) (a b : Fin g.ansLen → Bool) : Bool :=
  if c.length = g.lenAt x.val + g.lenAt y.val + 1 then
    xor (xor (coefJ g x y c) (dotBit (coefX g x c) a)) (dotBit (coefY g x y c) b)
  else true

variable {g}

theorem bitSign_eq_one_iff (b : Bool) : bitSign b = 1 ↔ b = false := by
  cases b <;> norm_num [bitSign]

theorem bitSign_dotBit {k : ℕ} (α a : Fin k → Bool) :
    bitSign (dotBit α a) = ∏ i, bitSign (α i && a i) := by
  induction k with
  | zero => simp
  | succ k ih => rw [dotBit_succ, bitSign_xor, ih, Fin.prod_univ_succ]

theorem neg_one_pow_count_zipWith (c v : List Bool) (h : c.length = v.length) :
    (-1 : ℂ) ^ (List.zipWith (· && ·) c v).count true =
      ∏ i ∈ Finset.range c.length, bitSign (c.getD i false && v.getD i false) := by
  induction c generalizing v with
  | nil => simp
  | cons b c ih =>
    cases v with
    | nil => simp at h
    | cons u v =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zipWith_cons_cons, List.count_cons, pow_add, ih v h, List.length_cons,
        Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      congr 1
      cases b <;> cases u <;> simp [bitSign]

theorem bitSign_dotBit_coefX (c : List Bool) (a : Fin g.ansLen → Bool) :
    bitSign (dotBit (coefX g x c) a) =
      ∏ i ∈ Finset.range (g.lenAt x.val),
        bitSign (c.getD i false && TailoredGameData.bit a i) := by
  set F : ℕ → ℂ := fun i =>
    bitSign ((decide (i < g.lenAt x.val) && c.getD i false) && TailoredGameData.bit a i)
  have hF : ∀ i : Fin g.ansLen, bitSign (coefX g x c i && a i) = F i.val := fun i => by
    simp only [F, coefX, TailoredGameData.bit, dite_eq_left i.isLt]
  rw [bitSign_dotBit, Finset.prod_congr rfl fun i _ => hF i, Fin.prod_univ_eq_prod_range F]
  have hle := lenAt_le_ansLen_fin g x
  rw [← Finset.prod_subset (fun i hi => Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hle))
    (fun i _ hi => by simp [F, Finset.mem_range.not.mp hi])]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [F, decide_eq_true (Finset.mem_range.mp hi), Bool.true_and]

theorem bitSign_dotBit_coefY (c : List Bool) (b : Fin g.ansLen → Bool) :
    bitSign (dotBit (coefY g x y c) b) =
      ∏ i ∈ Finset.range (g.lenAt y.val),
        bitSign (c.getD (g.lenAt x.val + i) false && TailoredGameData.bit b i) := by
  set F : ℕ → ℂ := fun i => bitSign ((decide (i < g.lenAt y.val) &&
    c.getD (g.lenAt x.val + i) false) && TailoredGameData.bit b i)
  have hF : ∀ i : Fin g.ansLen, bitSign (coefY g x y c i && b i) = F i.val := fun i => by
    simp only [F, coefY, TailoredGameData.bit, dite_eq_left i.isLt]
  rw [bitSign_dotBit, Finset.prod_congr rfl fun i _ => hF i, Fin.prod_univ_eq_prod_range F]
  have hle := lenAt_le_ansLen_fin g y
  rw [← Finset.prod_subset (fun i hi => Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hle))
    (fun i _ hi => by simp [F, Finset.mem_range.not.mp hi])]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [F, decide_eq_true (Finset.mem_range.mp hi), Bool.true_and]

theorem length_full (z : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    (g.full z a).length = g.lenAt z.val := by
  simp [TailoredGameData.full]

theorem getD_full (z : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) {i : ℕ}
    (hi : i < g.lenAt z.val) : (g.full z a).getD i false = TailoredGameData.bit a i := by
  simp [TailoredGameData.full, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem getD_vec_left (a b : Fin g.ansLen → Bool) {i : ℕ} (hi : i < g.lenAt x.val) :
    (g.full x a ++ g.full y b ++ [true]).getD i false = TailoredGameData.bit a i := by
  rw [← getD_full x a hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.append_assoc, List.getElem?_append_left (by rw [length_full]; exact hi)]

theorem getD_vec_mid (a b : Fin g.ansLen → Bool) {i : ℕ} (hi : i < g.lenAt y.val) :
    (g.full x a ++ g.full y b ++ [true]).getD (g.lenAt x.val + i) false =
      TailoredGameData.bit b i := by
  rw [← getD_full y b hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.append_assoc, List.getElem?_append_right (by rw [length_full]; omega),
    length_full, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [length_full]; exact hi)]

theorem getD_vec_last (a b : Fin g.ansLen → Bool) :
    (g.full x a ++ g.full y b ++ [true]).getD (g.lenAt x.val + g.lenAt y.val) false = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [length_full])]
  simp [length_full]

/-- **A constraint is satisfied exactly when its bit vanishes.** -/
theorem satisfies_iff_consBit (c : List Bool) (a b : Fin g.ansLen → Bool) :
    TailoredGameData.Satisfies c (g.full x a ++ g.full y b ++ [true]) ↔
      consBit g x y c a b = false := by
  unfold TailoredGameData.Satisfies consBit
  have hv : (g.full x a ++ g.full y b ++ [true]).length = g.lenAt x.val + g.lenAt y.val + 1 := by
    simp [length_full, Nat.add_assoc]
  rw [hv]
  by_cases hc : c.length = g.lenAt x.val + g.lenAt y.val + 1
  · rw [ite_eq_left hc, ← neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1),
      neg_one_pow_count_zipWith _ _ (hc.trans hv.symm), hc, Finset.prod_range_succ,
      Finset.prod_range_add, ← bitSign_eq_one_iff, bitSign_xor, bitSign_xor,
      bitSign_dotBit_coefX, bitSign_dotBit_coefY]
    have e1 : ∀ i ∈ Finset.range (g.lenAt x.val),
        bitSign (c.getD i false && (g.full x a ++ g.full y b ++ [true]).getD i false) =
          bitSign (c.getD i false && TailoredGameData.bit a i) := fun i hi => by
      rw [getD_vec_left x y a b (Finset.mem_range.mp hi)]
    have e2 : ∀ i ∈ Finset.range (g.lenAt y.val),
        bitSign (c.getD (g.lenAt x.val + i) false &&
          (g.full x a ++ g.full y b ++ [true]).getD (g.lenAt x.val + i) false) =
          bitSign (c.getD (g.lenAt x.val + i) false && TailoredGameData.bit b i) := fun i hi => by
      rw [getD_vec_mid x y a b (Finset.mem_range.mp hi)]
    have e3 := getD_vec_last x y a b
    rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2, e3, Bool.and_true, coefJ]
    simp only [true_and]
    constructor <;> intro h <;> linear_combination h
  · rw [ite_eq_right hc]
    simp only [hc, false_and, Bool.true_eq_false]

end Constraints

namespace ZStrat

variable {g : TailoredGameData} (S : ZStrat g) (x y : Fin (g.nV + 1))

/-- The matrix `(-1)^{c_J} U^α V^β` of a constraint `c` at `(x, y)`, or `-1` for a constraint of
the wrong length. -/
noncomputable def consMat (c : List Bool) : Matrix (Fin S.m) (Fin S.m) ℂ :=
  if c.length = g.lenAt x.val + g.lenAt y.val + 1 then
    bitSign (coefJ g x y c) • (obsChar (S.U x) (coefX g x c) * obsChar (S.U y) (coefY g x y c))
  else -1

/-- `P_a` lies in the `(-1)^{⟨α, a⟩}`-eigenspace of `U^α`, on the right. -/
theorem proj_mul_obsChar (a : Fin g.ansLen → Bool) (α : Fin g.ansLen → Bool) :
    S.proj x a * obsChar (S.U x) α = bitSign (dotBit α a) • S.proj x a := by
  rw [(Commute.obsChar_right (fun i => (S.commute_U_proj x i a).symm) α).eq]
  exact obsChar_mul_fourierProj (S.invol x) (S.commute_U x) α a

/-- **`P_a consMat Q_b = (-1)^{⟨c, a b 1⟩} P_a Q_b`.** -/
theorem proj_mul_consMat_mul_proj (c : List Bool) (a b : Fin g.ansLen → Bool) :
    S.proj x a * S.consMat x y c * S.proj y b =
      bitSign (consBit g x y c a b) • (S.proj x a * S.proj y b) := by
  unfold consMat consBit
  split_ifs with hc
  · have hQ : obsChar (S.U y) (coefY g x y c) * S.proj y b =
        bitSign (dotBit (coefY g x y c) b) • S.proj y b :=
      obsChar_mul_fourierProj (S.invol y) (S.commute_U y) _ b
    calc S.proj x a * (bitSign (coefJ g x y c) • (obsChar (S.U x) (coefX g x c) *
          obsChar (S.U y) (coefY g x y c))) * S.proj y b
        = bitSign (coefJ g x y c) • ((S.proj x a * obsChar (S.U x) (coefX g x c)) *
          (obsChar (S.U y) (coefY g x y c) * S.proj y b)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [S.proj_mul_obsChar, hQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul,
            bitSign_xor, bitSign_xor]
  · simp [bitSign]

/-- **The violation of a constraint**: `[a b 1 violates c] P_a Q_b = P_a (1 - consMat)/2 Q_b`. -/
theorem ite_satisfies_smul (c : List Bool) (a b : Fin g.ansLen → Bool) :
    (if TailoredGameData.Satisfies c (g.full x a ++ g.full y b ++ [true]) then (0 : ℂ) else 1) •
        (S.proj x a * S.proj y b) =
      S.proj x a * ((1 / 2 : ℂ) • (1 - S.consMat x y c)) * S.proj y b := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    S.proj_mul_consMat_mul_proj]
  cases h : consBit g x y c a b
  · rw [ite_eq_left ((satisfies_iff_consBit x y c a b).mpr h)]
    simp
  · rw [ite_eq_right (fun h' => by rw [(satisfies_iff_consBit x y c a b).mp h'] at h; cases h)]
    simp only [bitSign_true, one_smul, neg_one_smul, sub_neg_eq_add]
    rw [← two_smul ℂ, smul_smul]
    norm_num

end ZStrat

end MIPRE.Tailored.Sofic

end
