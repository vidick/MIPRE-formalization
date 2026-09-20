/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.TM.CookLevin.DecoupledProg
import MIPRE.Foundations.SAT.Padding
import MIPRE.Foundations.SAT.Rename
import MIPRE.Foundations.SAT.PowerPadding

/-!
# The padded five-block clause describer

The construction in `prop:exciting-padding-prop` of `answer_reduction.tex`,
applied to the formula used by the existing decoupled describer. Five index
blocks acquire the common width `m`; the two answer tails are forced to be blank.
Formula renaming preserves the original tree, so the construction remains
polynomial in the old formula and the new width.
-/

namespace MIPRE.TM.CookLevin.Pad

open SAT Cost Cost.PolyTimeFun Fml Desc

/-- Where the original five blocks and signs lie in the padded input. -/
def layout (ℓ r m : ℕ) : List ℕ :=
  List.range' 0 ℓ ++ List.range' m ℓ ++ List.range' (2 * m) r ++
    List.range' (3 * m) r ++ List.range' (4 * m) r ++ List.range' (5 * m) 5

@[simp] theorem length_layout (ℓ r m : ℕ) : (layout ℓ r m).length = 2 * ℓ + 3 * r + 5 := by
  simp [layout]
  omega

/-- Test that the `m`-bit index at `base` is below `2^old`. The comparison uses
one extra zero bit, so it also works at `old = m`. -/
def low (base old m : ℕ) : Fml :=
  ltConst (padTo (m + 1) (field base m)) (nbits (m + 1) (2 ^ old))

theorem eval_low (base old m : ℕ) (hm : old ≤ m) (x : ℕ → Bool) :
    (low base old m).eval x = true ↔ val (field base m) x < 2 ^ old := by
  unfold low
  rw [eval_ltConst_iff _ _ (by simp [length_padTo]), val_padTo,
    bitsVal_nbits_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]

/-- The positive-at-even, negative-at-odd blank sign for one answer index. -/
def blankSign (base sign : ℕ) : Fml := xnor (inp sign) (not (inp base))

/-- The padded formula: old clauses on old indices, or either answer-tail clause. -/
def formula (ℓ r m : ℕ) (f : Fml) : Fml :=
  orList [and (andList [low 0 ℓ m, low m ℓ m, low (2 * m) r m,
      low (3 * m) r m, low (4 * m) r m])
      (Fml.rename (fun i => (layout ℓ r m).getD i 0) f),
    and (not (low 0 ℓ m)) (blankSign 0 (5 * m)),
    and (not (low m ℓ m)) (blankSign m (5 * m + 1))]

/-- The padded circuit, before padding its number of gates to the exact PCP count. -/
def circuit (ℓ r m : ℕ) (f : Fml) : Circuit := (formula ℓ r m f).toCircuit (5 * m + 5)

private theorem take_bitsOfNat (n m j : ℕ) (h : n ≤ m) :
    (bitsOfNat m j).take n = bitsOfNat n j := by
  apply List.ext_getElem (by simp [h])
  intro k hk hk'
  simp only [bitsOfNat, List.getElem_take, List.getElem_ofFn]

private theorem slice_index (pre post : BitStr) (m n j : ℕ) (hn : n ≤ m) :
    ibOf pre.length n (fun i => (pre ++ bitsOfNat m j ++ post).getD i false) = bitsOfNat n j := by
  rw [ibOf_getD _ _ _ (by simp; omega), List.append_assoc,
    List.drop_left' rfl, List.take_append]
  simp [length_bitsOfNat, Nat.sub_eq_zero_of_le hn, take_bitsOfNat _ _ _ hn]

/-- Reading the renaming table in a padded clause recovers the original input bits. -/
theorem map_layout_clause {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (layout ℓ r m).map (fun i => (clauseInput5 m m
      (c.map (Cnf5.blockInclusion hℓ) (Cnf5.blockInclusion hℓ)
        (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr))).getD i false) =
      clauseInput5 ℓ r c := by
  let a := bitsOfNat m c.l₁.var
  let b := bitsOfNat m c.l₂.var
  let u := bitsOfNat m c.l₃.var
  let v := bitsOfNat m c.l₄.var
  let w := bitsOfNat m c.l₅.var
  let signs := [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos]
  let input := a ++ b ++ u ++ v ++ w ++ signs
  have lengths : a.length = m ∧ b.length = m ∧ u.length = m ∧ v.length = m ∧ w.length = m := by
    simp [a, b, u, v, w]
  have h₁ : ibOf 0 ℓ (fun i => input.getD i false) = bitsOfNat ℓ c.l₁.var := by
    simpa only [List.length_nil, List.nil_append, input, a, List.append_assoc] using
      slice_index [] (b ++ u ++ v ++ w ++ signs) m ℓ c.l₁.var hℓ
  have h₂ : ibOf m ℓ (fun i => input.getD i false) = bitsOfNat ℓ c.l₂.var := by
    simpa only [lengths.1, input, b, List.append_assoc] using
      slice_index a (u ++ v ++ w ++ signs) m ℓ c.l₂.var hℓ
  have h₃ : ibOf (2 * m) r (fun i => input.getD i false) = bitsOfNat r c.l₃.var := by
    simpa only [List.length_append, lengths.1, lengths.2.1, two_mul, input, u, List.append_assoc] using
      slice_index (a ++ b) (v ++ w ++ signs) m r c.l₃.var hr
  have h₄ : ibOf (3 * m) r (fun i => input.getD i false) = bitsOfNat r c.l₄.var := by
    have he : (a ++ b ++ u).length = 3 * m := by simp [a, b, u]; omega
    have hh := slice_index (a ++ b ++ u) (w ++ signs) m r c.l₄.var hr
    rw [he] at hh
    simpa only [input, v, List.append_assoc] using hh
  have h₅ : ibOf (4 * m) r (fun i => input.getD i false) = bitsOfNat r c.l₅.var := by
    have he : (a ++ b ++ u ++ v).length = 4 * m := by simp [a, b, u, v]; omega
    have hh := slice_index (a ++ b ++ u ++ v) signs m r c.l₅.var hr
    rw [he] at hh
    simpa only [input, w, List.append_assoc] using hh
  have hs : ibOf (5 * m) 5 (fun i => input.getD i false) = signs := by
    have he : (a ++ b ++ u ++ v ++ w).length = 5 * m := by simp [a, b, u, v, w]; omega
    rw [← he, ibOf_getD _ _ _ (by simp only [input, List.length_append, he]; simp [signs])]
    change ((a ++ b ++ u ++ v ++ w ++ signs).drop _).take 5 = _
    rw [List.drop_left' rfl]
    exact List.take_of_length_le (by simp [signs])
  change (layout ℓ r m).map (fun i => input.getD i false) = _
  simp only [layout, List.map_append]
  change ibOf 0 ℓ _ ++ ibOf m ℓ _ ++ ibOf (2 * m) r _ ++
    ibOf (3 * m) r _ ++ ibOf (4 * m) r _ ++ ibOf (5 * m) 5 _ = _
  rw [h₁, h₂, h₃, h₄, h₅, hs]
  rfl

/-- On an embedded clause, the renamed old formula has exactly its old value. -/
theorem eval_renamed_clause {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5))
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (Fml.rename (fun i => (layout ℓ r m).getD i 0) f).eval
      (fun i => (clauseInput5 m m
        (c.map (Cnf5.blockInclusion hℓ) (Cnf5.blockInclusion hℓ)
          (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr))).getD i false) =
      f.eval (fun i => (clauseInput5 ℓ r c).getD i false) := by
  rw [Fml.eval_rename]
  apply Fml.eval_congr_of_inputsLt hf
  intro i hi
  have hlen : i < (layout ℓ r m).length := by simpa using hi
  have hh := congrArg (fun l : BitStr => l.getD i false) (map_layout_clause hℓ hr c)
  rw [List.getD_eq_getElem _ false (by simpa using hlen), List.getElem_map] at hh
  simpa only [Function.comp_apply, List.getD_eq_getElem _ 0 hlen] using hh

/-- The two answer-tail predicates have precisely the source's repaired parity. -/
theorem eval_blankSigns {m : ℕ} (hm : 1 ≤ m)
    (c : Clause5 (Fin (2 ^ m)) (Fin (2 ^ m))
      (Fin (2 ^ m)) (Fin (2 ^ m)) (Fin (2 ^ m))) :
    ((blankSign 0 (5 * m)).eval (fun i => (clauseInput5 m m c).getD i false) = true ↔
      c.l₁.pos = decide ((c.l₁.var : ℕ) % 2 = 0)) ∧
    ((blankSign m (5 * m + 1)).eval (fun i => (clauseInput5 m m c).getD i false) = true ↔
      c.l₂.pos = decide ((c.l₂.var : ℕ) % 2 = 0)) := by
  have hs0 := eval_sgF c 0
  have hs1 := eval_sgF c 1
  have hoff : sgOff m m = 5 * m := by unfold sgOff; omega
  simp only [hoff, Nat.add_zero, sgList, List.getD_cons_zero, List.getD_cons_succ] at hs0 hs1
  simp only [Fml.eval] at hs0 hs1
  have h0 : (clauseInput5 m m c).getD 0 false = (c.l₁.var : ℕ).testBit 0 := by
    rw [clauseInput5_eq, getD_append_left _ _ false (by simp; omega), getD_bitsOfNat _ (by omega)]
  have h1 : (clauseInput5 m m c).getD m false = (c.l₂.var : ℕ).testBit 0 := by
    change (clauseInput5 m m c).getD (m + 0) false = _
    rw [← getD_drop_eq, clauseInput5_eq,
      List.drop_left' (by simp), getD_append_left _ _ false (by simp; omega),
      getD_bitsOfNat _ (by omega)]
  have hp (j : ℕ) : (!(j.testBit 0)) = decide (j % 2 = 0) := by
    rw [Nat.testBit_zero]
    by_cases h : j % 2 = 0 <;> simp [h, show (j % 2 = 1) ↔ ¬ j % 2 = 0 by omega]
  simp only [blankSign, eval_xnor, beq_iff_eq, hs0, hs1, Fml.eval, h0, h1, hp]
  exact ⟨trivial, trivial⟩

/-- The constructed circuit describes exactly the padded clause set. -/
theorem formula5_circuit {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m) (hm : 1 ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5)) :
    (circuit ℓ r m f).formula5 m m =
      Cnf5.pad hℓ hr ((f.toCircuit (2 * ℓ + 3 * r + 5)).formula5 ℓ r) := by
  ext c
  let x := fun i => (clauseInput5 m m c).getD i false
  have h₁ : (low 0 ℓ m).eval x = true ↔ (c.l₁.var : ℕ) < 2 ^ ℓ := by
    rw [eval_low _ _ _ hℓ]
    have hv := val_j₁F c
    simpa only [j₁F, val_padTo] using iff_of_eq (congrArg (fun t => t < 2 ^ ℓ) hv)
  have h₂ : (low m ℓ m).eval x = true ↔ (c.l₂.var : ℕ) < 2 ^ ℓ := by
    rw [eval_low _ _ _ hℓ]
    have hv := val_j₂F c
    simpa only [j₂F, val_padTo] using iff_of_eq (congrArg (fun t => t < 2 ^ ℓ) hv)
  have h₃ : (low (2 * m) r m).eval x = true ↔ (c.l₃.var : ℕ) < 2 ^ r := by
    rw [eval_low _ _ _ hr]
    exact iff_of_eq (congrArg (fun t => t < 2 ^ r) (val_j₃F c))
  have h₄ : (low (3 * m) r m).eval x = true ↔ (c.l₄.var : ℕ) < 2 ^ r := by
    rw [eval_low _ _ _ hr]
    have hv := val_j₄F c
    have hoff : 2 * m + m = 3 * m := by omega
    simpa only [j₄F, hoff] using iff_of_eq (congrArg (fun t => t < 2 ^ r) hv)
  have h₅ : (low (4 * m) r m).eval x = true ↔ (c.l₅.var : ℕ) < 2 ^ r := by
    rw [eval_low _ _ _ hr]
    have hv := val_j₅F c
    have hoff : 2 * m + 2 * m = 4 * m := by omega
    simpa only [j₅F, hoff] using iff_of_eq (congrArg (fun t => t < 2 ^ r) hv)
  obtain ⟨hb₁, hb₂⟩ := eval_blankSigns hm c
  change ((blankSign 0 (5 * m)).eval x = true ↔ _) at hb₁
  change ((blankSign m (5 * m + 1)).eval x = true ↔ _) at hb₂
  change (circuit ℓ r m f).evalBits (clauseInput5 m m c) = true ↔ _
  rw [circuit, Fml.evalBits_toCircuit]
  change (formula ℓ r m f).eval x = true ↔ _
  simp only [formula, eval_orList, List.any_cons, List.any_nil, Fml.eval,
    eval_andList, List.all_cons, List.all_nil, Bool.and_true, Bool.or_false,
    Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', h₁, h₂, h₃, h₄, h₅, hb₁, hb₂]
  constructor
  · rintro (⟨⟨hi₁, hi₂, hi₃, hi₄, hi₅⟩, hval⟩ | ⟨hi, ho⟩ | ⟨hi, ho⟩)
    · let c₀ : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
          (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)) :=
        ⟨⟨⟨c.l₁.var, hi₁⟩, c.l₁.pos⟩, ⟨⟨c.l₂.var, hi₂⟩, c.l₂.pos⟩,
          ⟨⟨c.l₃.var, hi₃⟩, c.l₃.pos⟩, ⟨⟨c.l₄.var, hi₄⟩, c.l₄.pos⟩,
          ⟨⟨c.l₅.var, hi₅⟩, c.l₅.pos⟩⟩
      have hmap : c₀.map (Cnf5.blockInclusion hℓ) (Cnf5.blockInclusion hℓ)
          (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) = c := rfl
      refine Or.inl ⟨c₀, ?_, hmap⟩
      change (f.toCircuit _).evalBits (clauseInput5 ℓ r c₀) = true
      rw [Fml.evalBits_toCircuit]
      have he := eval_renamed_clause hℓ hr f hf c₀
      rw [hmap] at he
      exact he.symm.trans hval
    · exact Or.inr (Or.inl ⟨Nat.not_lt.mp (fun h => by rw [h₁.mpr h] at hi; contradiction), ho⟩)
    · exact Or.inr (Or.inr ⟨Nat.not_lt.mp (fun h => by rw [h₂.mpr h] at hi; contradiction), ho⟩)
  · rintro (⟨c₀, hc₀, rfl⟩ | ⟨hi, ho⟩ | ⟨hi, ho⟩)
    · refine Or.inl ⟨⟨c₀.l₁.var.isLt, c₀.l₂.var.isLt, c₀.l₃.var.isLt,
        c₀.l₄.var.isLt, c₀.l₅.var.isLt⟩, ?_⟩
      have he := eval_renamed_clause hℓ hr f hf c₀
      exact he.trans (by simpa only [Circuit.formula5, Set.mem_ofPred_eq,
        Fml.evalBits_toCircuit] using hc₀)
    · refine Or.inr (Or.inl ⟨?_, ho⟩)
      exact Bool.eq_false_iff.mpr (fun h => Nat.not_lt.mpr hi (h₁.mp h))
    · refine Or.inr (Or.inr ⟨?_, ho⟩)
      exact Bool.eq_false_iff.mpr (fun h => Nat.not_lt.mpr hi (h₂.mp h))

/-- Input-width padding preserves the full decider description. -/
theorem describes {ℓ r m n T : ℕ} {D : Decider} {x y : BitStr}
    (hℓ : ℓ ≤ m) (hr : r ≤ m) (hm : 1 ≤ m) (hT : 2 * T ≤ 2 ^ ℓ)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5))
    (hC : (f.toCircuit (2 * ℓ + 3 * r + 5)).DescribesDecider ℓ r D n x y T) :
    (circuit ℓ r m f).DescribesDecider m m D n x y T :=
  hC.of_pad hℓ hr hT (formula5_circuit hℓ hr hm f hf)

private theorem mem_layout_lt {ℓ r m j : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (hj : j ∈ layout ℓ r m) : j < 5 * m + 5 := by
  simp only [layout, List.mem_append, List.mem_range'_1] at hj
  omega

/-- Padding does not introduce references beyond the new input arity. -/
theorem formula_inputsLt {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5)) :
    (formula ℓ r m f).InputsLt (5 * m + 5) := by
  have hlo (b old : ℕ) (hb : b + m ≤ 5 * m + 5) :
      (low b old m).InputsLt (5 * m + 5) :=
    Fml.InputsLt.ltConst _ (Fml.InputsLt.padTo (Fml.InputsLt.field hb))
  have hblank (b sign : ℕ) (hb : b < 5 * m + 5) (hs : sign < 5 * m + 5) :
      (blankSign b sign).InputsLt (5 * m + 5) :=
    Fml.InputsLt.xnor hs hb
  have hren : (Fml.rename (fun i => (layout ℓ r m).getD i 0) f).InputsLt (5 * m + 5) := by
    apply hf.rename
    intro i hi
    have hlen : i < (layout ℓ r m).length := by simpa using hi
    rw [List.getD_eq_getElem _ 0 hlen]
    exact mem_layout_lt hℓ hr (List.getElem_mem hlen)
  apply Fml.InputsLt.orList
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · refine ⟨Fml.InputsLt.andList _ ?_, hren⟩
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact hlo _ _ (by omega)
  · exact ⟨hlo _ _ (by omega), hblank _ _ (by omega) (by omega)⟩
  · exact ⟨hlo _ _ (by omega), hblank _ _ (by omega) (by omega)⟩

/-- The constructed circuit is well formed in the existing circuit interface. -/
theorem circuit_wellFormed {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5)) :
    (circuit ℓ r m f).WellFormed :=
  Fml.toCircuit_wellFormed _ (formula_inputsLt hℓ hr f hf)

section Programs

variable {ι : Type*} [SizedEncoding ι]

private noncomputable def baseR (mu : PolyTimeFun ι Unary) (k : ℕ) : PolyTimeFun ι ℕ :=
  ap₁ unaryToBin (ap₁ (nsmulU k) mu)

private theorem baseR_apply (mu : PolyTimeFun ι Unary) (k : ℕ) (i : ι) :
    baseR mu k i = k * (mu i).length := by simp [baseR]

/-- The five-block offset table as an ambient program. -/
noncomputable def layoutR (lu ru mu : PolyTimeFun ι Unary) : PolyTimeFun ι (List ℕ) :=
  ap₂ append (ap₂ append (ap₂ append (ap₂ append (ap₂ append
    (ap₂ range'P (PolyTimeFun.const 0) lu) (ap₂ range'P (baseR mu 1) lu))
    (ap₂ range'P (baseR mu 2) ru)) (ap₂ range'P (baseR mu 3) ru))
    (ap₂ range'P (baseR mu 4) ru)) (ap₂ range'P (baseR mu 5) (PolyTimeFun.const (unary 5)))

theorem layoutR_apply (lu ru mu : PolyTimeFun ι Unary) (i : ι) :
    layoutR lu ru mu i = layout (lu i).length (ru i).length (mu i).length := by
  simp [layoutR, baseR_apply, layout]

/-- The original-width test, including the boundary case where both widths agree. -/
noncomputable def lowR (base : PolyTimeFun ι ℕ) (old mu : PolyTimeFun ι Unary) :
    PolyTimeFun ι Fml :=
  let wide := ap₂ addU mu (PolyTimeFun.const (unary 1))
  ap₂ ltConstP (ap₂ padToP wide (ap₂ fieldP base mu))
    (nbitsR wide (ap₁ natBits (ap₁ pow2P old)))

theorem lowR_apply (base : PolyTimeFun ι ℕ) (old mu : PolyTimeFun ι Unary) (i : ι) :
    lowR base old mu i = low (base i) (old i).length (mu i).length := by
  simp only [lowR, ap₂_apply, ltConstP_apply, padToP_apply, fieldP_apply]
  rw [nbitsR_apply (2 ^ (old i).length) (by
    intro j
    simp only [ap₁_apply, pow2P_apply, natBits_apply]
    exact getD_bits _ j)]
  simp [low]

private noncomputable def blankSignR (base sign : PolyTimeFun ι ℕ) : PolyTimeFun ι Fml :=
  xnorR (ap₁ Fml.inpF sign) (notR (ap₁ Fml.inpF base))

private theorem blankSignR_apply (base sign : PolyTimeFun ι ℕ) (i : ι) :
    blankSignR base sign i = blankSign (base i) (sign i) := rfl

/-- The padded clause formula, constructed uniformly in polynomial time. -/
noncomputable def formulaR (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) :
    PolyTimeFun ι Fml :=
  orR [andTwo (andR [lowR (PolyTimeFun.const 0) lu mu, lowR (baseR mu 1) lu mu,
      lowR (baseR mu 2) ru mu, lowR (baseR mu 3) ru mu, lowR (baseR mu 4) ru mu])
      (ap₂ Fml.renameBy (layoutR lu ru mu) f),
    andTwo (notR (lowR (PolyTimeFun.const 0) lu mu))
      (blankSignR (PolyTimeFun.const 0) (baseR mu 5)),
    andTwo (notR (lowR (baseR mu 1) lu mu))
      (blankSignR (baseR mu 1) (ap₁ inc (baseR mu 5)))]

theorem formulaR_apply (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) (i : ι) :
    formulaR lu ru mu f i = formula (lu i).length (ru i).length (mu i).length (f i) := by
  simp only [formulaR, orR_apply, andTwo_apply, andR_apply, List.map_cons, List.map_nil,
    lowR_apply, baseR_apply, PolyTimeFun.const_apply, one_mul, ap₂_apply,
    Fml.renameBy_apply, layoutR_apply, notR_apply, blankSignR_apply, ap₁_apply, inc_apply,
    formula]

/-- The padded circuit itself, with the correct input count, as an ambient program. -/
noncomputable def circuitR (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) :
    PolyTimeFun ι Circuit :=
  ap₂ Fml.toCircuitF (ap₁ (incN 5) (baseR mu 5)) (formulaR lu ru mu f)

theorem circuitR_apply (lu ru mu : PolyTimeFun ι Unary) (f : PolyTimeFun ι Fml) (i : ι) :
    circuitR lu ru mu f i = circuit (lu i).length (ru i).length (mu i).length (f i) := by
  simp [circuitR, baseR_apply, formulaR_apply, circuit]

end Programs

/-! ## Applying the construction to the existing decoupled describer -/

/-- The common power-of-two index width. The old auxiliary width dominates the
old answer width, so this pads all five blocks. -/
noncomputable def innerDim (T σ : ℕ) : ℕ := ceilPower (mParam T σ)

theorem innerDim_isPow (T σ : ℕ) : ∃ j, innerDim T σ = 2 ^ j := ⟨_, rfl⟩

theorem oldWidth_le_innerDim (T σ : ℕ) : mParam T σ ≤ innerDim T σ := le_ceilPower _

theorem answerWidth_le_innerDim (T σ : ℕ) : lOf T ≤ innerDim T σ :=
  (lOf_le_mOf T σ).trans (oldWidth_le_innerDim T σ)

theorem innerDim_pos (T σ : ℕ) : 1 ≤ innerDim T σ := by
  exact (one_le_mOf T σ).trans (oldWidth_le_innerDim T σ)

theorem two_mul_le_innerDim (T σ : ℕ) : 2 * T ≤ 2 ^ innerDim T σ := by
  have hl : 2 * T ≤ 2 ^ lOf T := by
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp
    · exact (lOf_spec T hT).1
  exact hl.trans (Nat.pow_le_pow_right (by decide) (answerWidth_le_innerDim T σ))

theorem innerDim_le : ∃ c, ∀ T σ,
    innerDim T σ ≤ c * (Nat.size T + Nat.size σ + 1) := by
  obtain ⟨c, hc⟩ := decoupledDescriber.r₀_le
  refine ⟨2 * c + 1, fun T σ => ?_⟩
  have h₁ : mParam T σ ≤ c * (Nat.size T + Nat.size σ + 1) := hc T σ
  have h₂ := ceilPower_le_twice (mParam T σ)
  change ceilPower (mParam T σ) ≤ _
  nlinarith

/-- The common width in unary, computed directly from the succinct parameters. -/
noncomputable def innerDimU : PolyTimeFun DescInput Unary :=
  ceilPowerProg.comp (mU dEu)

theorem innerDimU_length (p : DescInput) :
    (innerDimU p).length = innerDim p.1.2.2.1 p.1.2.2.2.2 := by
  simp [innerDimU, innerDim, mParam]

/-- The effective padded describer, before exact gate-count padding. -/
noncomputable def describe : PolyTimeFun DescInput Circuit :=
  circuitR dLu (mU dEu) innerDimU (descFml5R dEu dTR dLu dDR dnR dxR dyR)

theorem describe_apply (p : DescInput) : describe p =
    circuit (lOf p.1.2.2.1) (mParam p.1.2.2.1 p.1.2.2.2.2)
      (innerDim p.1.2.2.1 p.1.2.2.2.2)
      (descFml5 (lOf p.1.2.2.1) p.1.2.2.1 (eOf p.1.2.2.1 p.1.2.2.2.2)
        p.1.1 p.1.2.1 p.2.1 p.2.2) := by
  simp only [describe, circuitR_apply, length_dLu, length_mU, length_dEu, innerDimU_length,
    descFml5R_apply, dTR_apply, dDR_apply, dnR_apply, dxR_apply, dyR_apply, mParam]

theorem describe_wellFormed (p : DescInput) : (describe p).WellFormed := by
  rw [describe_apply]
  apply circuit_wellFormed (answerWidth_le_innerDim _ _) (oldWidth_le_innerDim _ _)
  exact descFml5_inputsLt _ _ _ _ _ _ _ (lOf_le_mOf _ _)

theorem describe_describes (D : Decider) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D.prog n T Q σ x y) :
    (describe ((D.prog, n, T, Q, σ), x, y)).DescribesDecider
      (innerDim T σ) (innerDim T σ) D n x y T := by
  rw [describe_apply]
  have hT' : 2 * T ≤ 2 ^ lOf T := by
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp
    · exact (lOf_spec T hT).1
  apply describes (answerWidth_le_innerDim T σ) (oldWidth_le_innerDim T σ)
    (innerDim_pos T σ) hT' _ (descFml5_inputsLt _ _ _ _ _ _ _ (lOf_le_mOf T σ))
  have h := decoupledDescriber.describes D n T Q σ x y hV
  change (describe5P _).DescribesDecider _ _ _ _ _ _ _ at h
  rw [describe5P_apply] at h
  exact h

/-- A polynomial bound for the padded circuit, derived from its verified program. -/
noncomputable def gatePoly : Polynomial ℕ :=
  describe.timeBound.comp (Polynomial.C 25 * Polynomial.X + Polynomial.C 12)

theorem describe_size_le (D : Prog) (n T Q σ : ℕ) (x y : BitStr)
    (hV : Valid D n T Q σ x y) :
    (describe ((D, n, T, Q, σ), x, y)).size ≤ roundUp gatePoly n T Q σ := by
  have h₁ := (size_le_esize _).trans (describe.esize_apply_le ((D, n, T, Q, σ), x, y))
  have h₂ := polynomial_eval_mono describe.timeBound (esize_descInput_le D n T Q σ x y hV)
  have he : describe.timeBound.eval (25 * LOf n T Q σ + 12) = gatePoly.eval (LOf n T Q σ) := by
    simp [gatePoly, Polynomial.eval_comp]
  exact ((h₁.trans h₂).trans (le_of_eq he)).trans (le_roundUp gatePoly n T Q σ)

end MIPRE.TM.CookLevin.Pad
