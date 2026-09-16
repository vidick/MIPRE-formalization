/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Repeat.RepDecider
import MIPRE.Foundations.Repeat.SamplerCost

/-!
# The running time of the repeated decider

`repDecider_timeBound`: when the input sampler and decider run within `R.S (|d| + 1)^{R.k}`
and `R.D (|d| + 1)^{R.k}` at index `n`, the repeated decider on `(λ, τ, β)` runs within
`c (W + 1)^m (|d| + 1)^{e (R.k + 1)}` for constants `c, m, e` independent of everything and
`W` any number dominating the parameters (`DecDom`). The cost is the explicit one of
`prepProg_runs` and `coordLoop_runs_bounded`, dominated piece by piece as in
`SamplerCost.lean`; the one point of care is that the sanitized inputs of the loop are no larger
than the raw ones (`size_encode_bitsOf_le`, `size_parse_bitsOf_le`), so that the input decider
is called on data of size below `|d|` and its bound needs no factor `c^{R.k}`.
-/

namespace MIPRE.Repeat

open Cost Cost.Data Cost.Prog CL

/-! ## Sizes of the sanitized inputs -/

theorem length_toList_le (d : Data) : (toList d).length + 1 ≤ d.size := by
  have := length_le_size_list' (toList d)
  rwa [list_toList] at this

theorem size_ofBool_bitOf_le (a : Data) : (ofBool (bitOf a)).size ≤ a.size := by
  cases a with
  | nil => simp [bitOf, ofBool, size]
  | cons a b => simp only [bitOf, ofBool, size]; have := size_pos a; have := size_pos b; omega

theorem size_list_map_ofBool_bitOf_le (l : List Data) :
    (list ((l.map bitOf).map ofBool)).size ≤ (list l).size := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, size_list_cons]
    have := size_ofBool_bitOf_le a
    omega

/-- Sanitizing a datum into a bit string does not increase its size. -/
theorem size_encode_bitsOf_le (d : Data) : (encode (bitsOf (toList d)) : Data).size ≤ d.size := by
  have := size_list_map_ofBool_bitOf_le (toList d)
  rw [list_toList] at this
  rw [encode_bitStr_eq_list]
  exact this

theorem size_parse_bitsOf_le (d : Data) : (parse (bitsOf (toList d))).size ≤ d.size := by
  have h1 := size_parse_le (bitsOf (toList d))
  have h2 := length_toList_le d
  simp only [bitsOf, List.length_map] at h1 ⊢
  have := size_pos d
  omega

theorem size_le_of_mem_list {a : Data} {l : List Data} (h : a ∈ l) : a.size ≤ (list l).size := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [size_list_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- Every query of the loop has the shape `(D̄, (n, xᵢ, yᵢ, aᵢ, bᵢ))` with each component no
larger than the list it is cut from. -/
theorem mem_decQueries {dD nD : Data} {s : ℕ} :
    ∀ (k : ℕ) (remX remY remA remB : List Data) (q : Data),
      q ∈ decQueries dD nD s k remX remY remA remB →
      ∃ xi yi ai bi, q = decQuery dD nD xi yi ai bi ∧ xi.size ≤ (list remX).size ∧
        yi.size ≤ (list remY).size ∧ ai.size ≤ (list remA).size ∧ bi.size ≤ (list remB).size := by
  intro k
  induction k with
  | zero => intro _ _ _ _ q h; simp [decQueries] at h
  | succ k ih =>
    intro remX remY remA remB q h
    rcases remA with _ | ⟨ai, remA'⟩
    · simp [decQueries] at h
    rcases remB with _ | ⟨bi, remB'⟩
    · simp [decQueries] at h
    simp only [decQueries, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨_, _, _, _, rfl, size_list_take_le _ _, size_list_take_le _ _, ?_, ?_⟩ <;>
        simp only [size_list_cons] <;> omega
    · obtain ⟨xi, yi, ai', bi', rfl, h1, h2, h3, h4⟩ := ih _ _ _ _ q h
      refine ⟨xi, yi, ai', bi', rfl, (h1.trans (size_list_drop_le _ _)),
        (h2.trans (size_list_drop_le _ _)), ?_, ?_⟩ <;> simp only [size_list_cons] <;> omega

/-! ## Domination of the primitives' costs -/

section Chain

variable {W X K : ℕ}

theorem dom_bitsCost : ∃ c m e, ∀ (W X K : ℕ) {L sz : ℕ}, 1 ≤ X → L ≤ X → sz ≤ X →
    Dom W X K c m e (bitsCost L sz) := by
  exact ⟨_, _, _, fun W X K {L sz} hX hL hsz => by
    unfold bitsCost
    have hL' : Dom W X K 1 0 1 L := Dom.ofLeX hX hL
    have hsz' : Dom W X K 1 0 1 sz := Dom.ofLeX hX hsz
    exact ((hL'.add hX (Dom.const 2)).mul ((hsz'.add hX ((Dom.const 2).mul hL')).add hX
      (Dom.const 15))).add hX ((hL'.add hX (Dom.const 2)).mul (((Dom.const 4).mul hL').add hX
      (Dom.const 20)))⟩

theorem dom_lenCost : ∃ c m e, ∀ (W X K : ℕ) {L sz : ℕ}, 1 ≤ X → L ≤ X → sz ≤ X →
    Dom W X K c m e (lenCost L sz) := by
  exact ⟨_, _, _, fun W X K {L sz} hX hL hsz => by
    unfold lenCost
    have hL' : Dom W X K 1 0 1 L := Dom.ofLeX hX hL
    have hsz' : Dom W X K 1 0 1 sz := Dom.ofLeX hX hsz
    exact ((hL'.add hX (Dom.const 1)).add hX (Dom.const 1)).mul
      ((((hsz'.add hX (Dom.const 1)).add hX ((Dom.const 2).mul hL')).add hX (Dom.const 13)))⟩

theorem dom_eqCost (c₁ m₁ e₁ c₂ m₂ e₂ : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {l₁ l₂ : Data}, 1 ≤ X →
    Dom W X K c₁ m₁ e₁ l₁.size → Dom W X K c₂ m₂ e₂ l₂.size → Dom W X K c m e (eqCost l₁ l₂) := by
  exact ⟨_, _, _, fun W X K {l₁ l₂} hX h₁ h₂ => by
    unfold eqCost
    exact ((h₁.of_le (spine_le_size l₁)).add hX (Dom.const 1)).mul ((h₁.add hX h₂).add hX
      (Dom.const 21))⟩

theorem dom_parseCost : ∃ c m e, ∀ (W X K : ℕ) {x : BitStr}, 1 ≤ X → x.length ≤ X →
    Dom W X K c m e (parseCost x) := by
  exact ⟨_, _, _, fun W X K {x} hX hx => by
    unfold parseCost
    have hL' : Dom W X K 1 0 1 x.length := Dom.ofLeX hX hx
    have he : Dom W X K (4 + 1) 0 1 (encode x : Data).size :=
      Dom.ofAffineX hX ((esize_bitStr_le x).trans (by omega))
    exact (hL'.add hX (Dom.const 2)).mul ((he.add hX ((Dom.const 2).mul hL')).add hX
      (Dom.const 25))⟩

theorem dom_serCost : ∃ c m e, ∀ (W X K : ℕ) {d : Data}, 1 ≤ X → d.size ≤ X →
    Dom W X K c m e (serCost d) := by
  exact ⟨_, _, _, fun W X K {d} hX hd => by
    unfold serCost
    have hd' : Dom W X K 1 0 1 d.size := Dom.ofLeX hX hd
    exact ((((Dom.const 3).mul hd').add hX (Dom.const 2)).mul (((Dom.const 16).mul hd').add hX
      (Dom.const 42))).add hX ((hd'.add hX (Dom.const 2)).mul (((Dom.const 5).mul hd').add hX
      (Dom.const 30)))⟩

theorem dom_dblCost : ∃ c m e, ∀ (W X K : ℕ) {mm a : ℕ}, 1 ≤ X → 2 ^ mm ≤ W → a ≤ W →
    Dom W X K c m e (dblCost mm a) := by
  exact ⟨_, _, _, fun W X K {m a} hX hm ha => by
    unfold dblCost
    have hm' : m ≤ W := (Nat.lt_two_pow_self).le.trans hm
    have h2 : Dom W X K 1 1 0 (2 ^ m) := Dom.ofLeW hm
    have ha' : Dom W X K 1 1 0 a := Dom.ofLeW ha
    exact ((Dom.ofLeW hm').add hX (Dom.const 1)).mul (((((h2.mul ha').add hX (Dom.const 1)).mul
      ((((Dom.const 4).mul h2).mul ha').add hX (Dom.const 14))).add hX
      (((Dom.const 10).mul h2).mul ha')).add hX ((Dom.const 2).mul (Dom.ofLeW hm')) |>.add hX
      (Dom.const 32))⟩

theorem dom_esize' {x : ℕ} (hx : x ≤ W) : Dom W X K (4 + 1) 1 0 (encode x : Data).size :=
  dom_esize hx

/-- The cost of the preparation, `prepCost`, dominated. -/
theorem dom_prepCost (cd md ed : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {sP dP : Data}
    {lam tau beta n s : ℕ} {xD yD aD bD : Data} {td : ℕ}, 1 ≤ X → 1 ≤ W →
    Dom W X K cd md ed td → sP.size ≤ W → dP.size ≤ W → lam ≤ W → tau ≤ W → beta ≤ W → n ≤ W →
    s ≤ W → 2 ^ (tau * (Nat.size lam + Nat.size n)) ≤ W →
    2 ^ (beta * (Nat.size lam + Nat.size n)) ≤ W → xD.size + yD.size + aD.size + bD.size + 3 ≤ X →
    Dom W X K c m e (prepCost sP dP lam tau beta n s xD yD aD bD td) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_toUnaryCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_powCost
  obtain ⟨c₃, m₃, e₃, h₃⟩ := dom_dblCost
  obtain ⟨c₄, m₄, e₄, h₄⟩ := dom_bitsCost
  obtain ⟨c₅, m₅, e₅, h₅⟩ := dom_lenCost
  obtain ⟨c₆, m₆, e₆, h₆⟩ := dom_eqCost 3 0 1 3 2 0
  obtain ⟨c₇, m₇, e₇, h₇⟩ := dom_eqCost 5 0 1 1 0 1
  obtain ⟨c₈, m₈, e₈, h₈⟩ := dom_parseCost
  obtain ⟨c₉, m₉, e₉, h₉⟩ := dom_serCost
  exact ⟨_, _, _, fun W X K {sP dP lam tau beta n s xD yD aD bD td} hX h1W htd hsP hdP hlam htau
      hbeta hn hs hreps hparse hd => by
    unfold prepCost prepPreCost
    have hxl := length_toList_le xD
    have hyl := length_toList_le yD
    have hal := length_toList_le aD
    have hbl := length_toList_le bD
    have hbx : (bitsOf (toList xD)).length = (toList xD).length := List.length_map ..
    have hby : (bitsOf (toList yD)).length = (toList yD).length := List.length_map ..
    have hba : (bitsOf (toList aD)).length = (toList aD).length := List.length_map ..
    have hbb : (bitsOf (toList bD)).length = (toList bD).length := List.length_map ..
    have hex := size_encode_bitsOf_le xD
    have hey := size_encode_bitsOf_le yD
    have hea := size_encode_bitsOf_le aD
    have heb := size_encode_bitsOf_le bD
    have hpa := size_parse_bitsOf_le aD
    have hpb := size_parse_bitsOf_le bD
    have hL : Nat.size lam + Nat.size n ≤ 2 * W := by
      have := nat_size_le_self lam; have := nat_size_le_self n; omega
    have hsz : (encode lam : Data).size + (encode n : Data).size + 1 ≤ 12 * W + 3 := by
      have := esize_nat_le' lam; have := esize_nat_le' n
      have e1 : (encode lam : Data).size = esize lam := rfl
      have e2 : (encode n : Data).size = esize n := rfl
      omega
    have dOfX : ∀ {v : ℕ}, v ≤ X → Dom W X K 1 0 1 v := fun h => Dom.ofLeX hX h
    have hs1x : Dom W X K 3 0 1 (ofNat (bitsOf (toList xD)).length).size := by
      rw [size_ofNat]
      exact (Dom.ofAffineX hX (a := 2) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs1y : Dom W X K 3 0 1 (ofNat (bitsOf (toList yD)).length).size := by
      rw [size_ofNat]
      exact (Dom.ofAffineX hX (a := 2) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs2 : Dom W X K 3 2 0 (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)).size := by
      rw [size_ofNat]
      exact ((((Dom.const 2).mul ((Dom.ofLeW hreps).mul (Dom.ofLeW hs))).add hX
        (Dom.const 1)).mono hX (by norm_num) (by norm_num) (by norm_num))
    have hs3a : Dom W X K 5 0 1 (encode (parse (bitsOf (toList aD))).toBitsPost : Data).size := by
      have := esize_bitStr_le (parse (bitsOf (toList aD))).toBitsPost
      have e : esize (parse (bitsOf (toList aD))).toBitsPost =
        (encode (parse (bitsOf (toList aD))).toBitsPost : Data).size := rfl
      simp only [length_toBitsPost] at this
      exact (Dom.ofAffineX hX (a := 4) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs3b : Dom W X K 5 0 1 (encode (parse (bitsOf (toList bD))).toBitsPost : Data).size := by
      have := esize_bitStr_le (parse (bitsOf (toList bD))).toBitsPost
      have e : esize (parse (bitsOf (toList bD))).toBitsPost =
        (encode (parse (bitsOf (toList bD))).toBitsPost : Data).size := rfl
      simp only [length_toBitsPost] at this
      exact (Dom.ofAffineX hX (a := 4) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs4a : Dom W X K 1 0 1 (encode (bitsOf (toList aD)) : Data).size := dOfX (by omega)
    have hs4b : Dom W X K 1 0 1 (encode (bitsOf (toList bD)) : Data).size := dOfX (by omega)
    have q1 := htd.add hX (h₁ W X K hX hs)
    have q2 := q1.add hX (h₁ W X K hX htau)
    have q3 := q2.add hX (h₁ W X K hX hbeta)
    have q4 := q3.add hX (h₂ W X K hX htau hL hsz)
    have q5 := q4.add hX (h₂ W X K hX hbeta hL hsz)
    have q6 := q5.add hX (h₃ W X K hX hreps hs)
    have q7 := q6.add hX (h₃ W X K hX hreps h1W)
    have q8 := q7.add hX (h₃ W X K hX hparse h1W)
    have q9 := q8.add hX (h₄ W X K (L := (toList xD).length) (sz := xD.size) hX (by omega) (by omega))
    have q10 := q9.add hX (h₄ W X K (L := (toList yD).length) (sz := yD.size) hX (by omega) (by omega))
    have q11 := q10.add hX (h₄ W X K (L := (toList aD).length) (sz := aD.size) hX (by omega) (by omega))
    have q12 := q11.add hX (h₄ W X K (L := (toList bD).length) (sz := bD.size) hX (by omega) (by omega))
    have q13 := q12.add hX (h₅ W X K (L := (bitsOf (toList xD)).length)
      (sz := (encode (bitsOf (toList xD)) : Data).size) hX (by omega) (by omega))
    have q14 := q13.add hX (h₅ W X K (L := (bitsOf (toList yD)).length)
      (sz := (encode (bitsOf (toList yD)) : Data).size) hX (by omega) (by omega))
    have q15 := q14.add hX (h₆ W X K hX hs1x hs2)
    have q16 := q15.add hX (h₆ W X K hX hs1y hs2)
    have q17 := q16.add hX (h₈ W X K (x := bitsOf (toList aD)) hX (by omega))
    have q18 := q17.add hX (h₉ W X K (d := parse (bitsOf (toList aD))) hX (by omega))
    have q19 := q18.add hX (h₇ W X K hX hs3a hs4a)
    have q20 := q19.add hX (h₈ W X K (x := bitsOf (toList bD)) hX (by omega))
    have q21 := q20.add hX (h₉ W X K (d := parse (bitsOf (toList bD))) hX (by omega))
    have q22 := q21.add hX (h₇ W X K hX hs3b hs4b)
    have r1 := (((((((((Dom.ofLeW hsP).add hX (Dom.ofLeW hdP)).add hX (dom_esize' hlam)).add hX
      (dom_esize' htau)).add hX (dom_esize' hbeta)).add hX (dom_esize' hn)).add hX
      (dOfX (v := xD.size) (by omega))).add hX (dOfX (v := yD.size) (by omega))).add hX
      (dOfX (v := aD.size) (by omega))).add hX (dOfX (v := bD.size) (by omega))
    have r2 := ((((((((Dom.ofLeW hdP).add hX (dom_esize' hn)).add hX
      ((Dom.const 2).mul (Dom.ofLeW hs))).add hX ((Dom.const 2).mul (Dom.ofLeW hparse))).add hX
      ((Dom.const 2).mul (Dom.ofLeW hreps))).add hX
      (dOfX (v := (encode (bitsOf (toList xD)) : Data).size) (by omega))).add hX
      (dOfX (v := (encode (bitsOf (toList yD)) : Data).size) (by omega))).add hX
      (dOfX (v := (parse (bitsOf (toList aD))).size) (by omega))).add hX
      (dOfX (v := (parse (bitsOf (toList bD))).size) (by omega))
    exact ((((Dom.const 6).mul q22).add hX ((Dom.const 8).mul r1)).add hX (Dom.const 500)).add hX
      ((Dom.const 8).mul r2) |>.add hX (Dom.const 100)⟩

/-- The argument of the bound on a call of the input decider from the loop, on data of size
at most `M`. -/
theorem dom_yM : ∃ c m e, ∀ (W X K : ℕ) {p n RD M : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → RD ≤ W →
    M + 1 ≤ X → Dom W X K c m e (p + (esize n + M + 1) + RD * (M + 1) ^ K) := by
  exact ⟨_, _, _, fun W X K {p n RD M} hX hp hn hRD hM =>
    ((Dom.ofLeW hp).add hX (((dom_esize hn).add hX (Dom.ofLeX hX (by omega))).add hX
      (Dom.const 1))).add hX ((Dom.ofLeW hRD).mul ((Dom.powK hX).of_le
        (Nat.pow_le_pow_left hM K)))⟩

end Chain

/-! ## The calls of the loop -/

/-- The calls of the coordinate loop to the input decider, through the universal machine,
within a uniform bound: `M` bounds the size of the data each is called on. -/
theorem loop_calls_time (D : Decider) (n : ℕ) (R : Budget) (hD : D.TimeBoundAt n R.D R.k)
    (s k : ℕ) (remX remY remA remB : List Data) :
    ∃ fq : Data → Data, ∀ q ∈ decQueries (encode D.prog) (encode n) s k remX remY remA remB,
      ∃ t ≤ selfUniversal.bound.eval (esize D.prog +
        (esize n + ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3)
          + 1) +
        R.D * ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3 + 1)
          ^ R.k),
        Eval [q] selfUniversal.univ (fq q) t := by
  classical
  have key : ∀ q ∈ decQueries (encode D.prog) (encode n) s k remX remY remA remB,
      ∃ r t, t ≤ selfUniversal.bound.eval (esize D.prog +
        (esize n + ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3)
          + 1) +
        R.D * ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3 + 1)
          ^ R.k) ∧ Eval [q] selfUniversal.univ r t := by
    intro q hq
    obtain ⟨xi, yi, ai, bi, rfl, h1, h2, h3, h4⟩ := mem_decQueries k remX remY remA remB q hq
    obtain ⟨r, t, ht, run⟩ := hD (.cons xi (.cons yi (.cons ai bi)))
    obtain ⟨t', ht', run'⟩ := selfUniversal.time_le _ _ _ _ run
    refine ⟨r, t', ht'.trans (polynomial_eval_mono _ ?_), run'⟩
    have hsz : (Data.cons xi (.cons yi (.cons ai bi))).size ≤
        (list remX).size + (list remY).size + (list remA).size + (list remB).size + 3 := by
      simp only [size_cons]; omega
    have hk := Nat.mul_le_mul_left R.D (Nat.pow_le_pow_left (Nat.add_le_add_right hsz 1) R.k)
    have he : (encode n : Data).size = esize n := rfl
    simp only [size_cons, he] at ht ⊢
    simp only [size_cons] at hsz hk
    omega
  refine ⟨fun q => if h : q ∈ decQueries (encode D.prog) (encode n) s k remX remY remA remB then
    (key q h).choose else .nil, fun q hq => ?_⟩
  simp only [dif_pos hq]
  obtain ⟨t, ht, run⟩ := (key q hq).choose_spec
  exact ⟨t, ht, run⟩

/-! ## The running time -/

/-- The hypotheses on the dominating number `W`. -/
structure DecDom {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider) (lam tau beta n : ℕ) (R : Budget)
    (W : ℕ) : Prop where
  S_le : R.S ≤ W
  D_le : R.D ≤ W
  lam_le : lam ≤ W
  tau_le : tau ≤ W
  beta_le : beta ≤ W
  n_le : n ≤ W
  sizeS_le : esize S.prog ≤ W
  sizeD_le : esize D.prog ≤ W
  pow_le : 10 ^ R.k ≤ W
  reps_le : Repetition.reps lam tau n ≤ W
  parse_le : Repetition.parseBound lam beta n ≤ W
  dim_le : S.dim n ≤ W

theorem DecDom.one_le {ℓ : ℕ} {S : CL.Sampler ℓ} {D : Decider} {lam tau beta n : ℕ} {R : Budget}
    {W : ℕ} (hW : DecDom S D lam tau beta n R W) : 1 ≤ W :=
  (Nat.one_le_pow _ _ (by norm_num)).trans hW.pow_le

/-- The size of the parameters datum. -/
theorem size_encode_decParams_le {ℓ : ℕ} {S : CL.Sampler ℓ} {D : Decider} {lam tau beta n : ℕ}
    {R : Budget} {W : ℕ} (hW : DecDom S D lam tau beta n R W) :
    (encode ((S.prog, D.prog), lam, tau, beta) : Data).size ≤ 14 * W + 7 := by
  have h1 := hW.sizeS_le
  have h2 := hW.sizeD_le
  have h3 := (esize_nat_le' lam).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.lam_le) 1)
  have h4 := (esize_nat_le' tau).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.tau_le) 1)
  have h5 := (esize_nat_le' beta).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.beta_le) 1)
  simp only [encode_prod, size_cons, esize] at *
  omega

/-- On a malformed input (fewer than three components), the repeated decider rejects at once. -/
theorem decMalformed_time : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
    (lam tau beta n : ℕ) (R : Budget) (W : ℕ) (d : Data), DecDom S D lam tau beta n R W →
    (d = .nil ∨ (∃ xD, d = .cons xD .nil) ∨ ∃ xD yD, d = .cons xD (.cons yD .nil)) →
    ∃ r t, t ≤ c * (W + 1) ^ m * (d.size + 1) ^ (e * (R.k + 1)) ∧
      (repDeciderProg S.prog D.prog lam tau beta).Runs (.cons (encode n) d) r t := by
  exact ⟨_, _, _, fun {ℓ} S D lam tau beta n R W d hW hd => by
    obtain ⟨t, ht, run⟩ := repDecCore_runs_malformed selfUniversal.univ (encode S.prog)
      (encode D.prog) (encode lam) (encode tau) (encode beta) (encode n) d hd
    refine ⟨.nil, _, ?_, hardcode_time (repDecCore_wellScoped selfUniversal.closed) run⟩
    have hX : 1 ≤ d.size + 1 := by omega
    have hpar := size_encode_decParams_le hW
    have hdsz : Dom W (d.size + 1) R.k 1 0 1 d.size := Dom.ofLeX hX (by omega)
    have chain := (((Dom.const 10).add hX (Dom.ofAffine (W := W) (X := d.size + 1) (K := R.k)
      (a := 14) (b := 7) hpar)).add hX (((dom_esize' hW.n_le).add hX hdsz).add hX
      (Dom.const 1))).add hX (Dom.const 3)
    rw [encode_decParams] at hpar chain ⊢
    refine (chain.of_le ?_).le
    simp only [size_cons]
    omega⟩

/-- On a well-formed input `(x, y, a, b)` (any four data), the repeated decider halts within
a dominated time. -/
theorem decWellformed_time : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
    (lam tau beta n : ℕ) (R : Budget) (W : ℕ) (xD yD aD bD : Data), DecDom S D lam tau beta n R W →
    S.TimeBoundAt n R.S R.k → D.TimeBoundAt n R.D R.k →
    ∃ r t, t ≤ c * (W + 1) ^ m *
        ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) ^ (e * (R.k + 1)) ∧
      (repDeciderProg S.prog D.prog lam tau beta).Runs
        (.cons (encode n) (.cons xD (.cons yD (.cons aD bD)))) r t := by
  obtain ⟨cd, md, ed, hd⟩ := dom_yd
  obtain ⟨cd', md', ed', hd'⟩ := dom_univ_bound cd md ed
  obtain ⟨cP, mP, eP, hP⟩ := dom_prepCost cd' md' ed'
  obtain ⟨cT, mT, eT, hT⟩ := dom_yM
  obtain ⟨cT', mT', eT', hT'⟩ := dom_univ_bound cT mT eT
  exact ⟨_, _, _, fun {ℓ} S D lam tau beta n R W xD yD aD bD hW hS hD => by
    have hX : 1 ≤ (Data.cons xD (.cons yD (.cons aD bD))).size + 1 := by omega
    have h1W : 1 ≤ W := hW.one_le
    have hreps : 2 ^ (tau * (Nat.size lam + Nat.size n)) ≤ W := hW.reps_le
    have hparse : 2 ^ (beta * (Nat.size lam + Nat.size n)) ≤ W := hW.parse_le
    have hdsz : (Data.cons xD (.cons yD (.cons aD bD))).size =
      xD.size + yD.size + aD.size + bD.size + 3 := by simp only [size_cons]; omega
    obtain ⟨td, htd, hdim⟩ := dim_call_time S n R hS
    obtain ⟨t₀, ht₀, hp⟩ := prepProg_runs selfUniversal.closed (encode S.prog) (encode D.prog)
      lam tau beta n (S.dim n) xD yD aD bD hdim
    have hdomtd := (hd' W _ R.k hX (by omega)
      (hd W _ R.k hX hW.sizeS_le hW.n_le hW.S_le hW.pow_le)).of_le htd
    have hdomP := hP W _ R.k (sP := encode S.prog) (dP := encode D.prog) (xD := xD) (yD := yD)
      (aD := aD) (bD := bD) hX h1W hdomtd
      hW.sizeS_le hW.sizeD_le hW.lam_le hW.tau_le hW.beta_le hW.n_le hW.dim_le hreps
      hparse (by omega)
    have hpar := size_encode_decParams_le hW
    have hdomPar : Dom W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k (14 + 7) 1 0
        (encode ((S.prog, D.prog), lam, tau, beta) : Data).size :=
      Dom.ofAffine hpar
    have hsX : Dom W _ R.k 1 0 1 xD.size := Dom.ofLeX hX (by omega)
    have hsY : Dom W _ R.k 1 0 1 yD.size := Dom.ofLeX hX (by omega)
    have hsA : Dom W _ R.k 1 0 1 aD.size := Dom.ofLeX hX (by omega)
    have hsB : Dom W _ R.k 1 0 1 bD.size := Dom.ofLeX hX (by omega)
    -- the sizes of the raw components of the input
    have hsum := (((((((((Dom.ofLeW (v := (encode S.prog : Data).size) hW.sizeS_le).add hX
      (Dom.ofLeW (v := (encode D.prog : Data).size) hW.sizeD_le)).add hX
      (dom_esize' hW.lam_le)).add hX (dom_esize' hW.tau_le)).add hX (dom_esize' hW.beta_le)).add hX
      (dom_esize' hW.n_le)).add hX hsX).add hX hsY).add hX hsA).add hX hsB
    have hin := ((dom_esize' hW.n_le).add hX ((((hsX.add hX hsY).add hX hsA).add hX hsB).add hX
      (Dom.const 3))).add hX (Dom.const 1)
    -- the lists of the loop's state
    have hlx : (list ((bitsOf (toList xD)).map ofBool)).size ≤ xD.size := by
      rw [← encode_bitStr_eq_list]; exact size_encode_bitsOf_le xD
    have hly : (list ((bitsOf (toList yD)).map ofBool)).size ≤ yD.size := by
      rw [← encode_bitStr_eq_list]; exact size_encode_bitsOf_le yD
    have hla : (list (toList (parse (bitsOf (toList aD))))).size ≤ aD.size := by
      rw [list_toList]; exact size_parse_bitsOf_le aD
    have hlb : (list (toList (parse (bitsOf (toList bD))))).size ≤ bD.size := by
      rw [list_toList]; exact size_parse_bitsOf_le bD
    -- domination of the loop's budget
    have hM : (list ((bitsOf (toList xD)).map ofBool)).size +
        (list ((bitsOf (toList yD)).map ofBool)).size +
        (list (toList (parse (bitsOf (toList aD))))).size +
        (list (toList (parse (bitsOf (toList bD))))).size + 3 + 1 ≤
        (Data.cons xD (.cons yD (.cons aD bD))).size + 1 := by rw [hdsz]; omega
    have hdomTu := hT' W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k hX (by omega)
      (hT W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k hX hW.sizeD_le hW.n_le hW.D_le hM)
    have hctx : Dom W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k
        ((1 + (4 + 1)) + (2 + 1) + (2 + 1) + 3) 1 0
        (decCtx (encode D.prog) (encode n) (S.dim n)
          (2 ^ (beta * (Nat.size lam + Nat.size n)))).size := by
      refine ((((Dom.ofLeW (v := (encode D.prog : Data).size) hW.sizeD_le).add hX
        (dom_esize' hW.n_le)).add hX
        (Dom.ofAffine (a := 2) (b := 1) (v := (ofNat (S.dim n)).size)
          (by rw [size_ofNat]; have := hW.dim_le; omega))).add hX
        (Dom.ofAffine (a := 2) (b := 1) (v := (ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))).size)
          (by rw [size_ofNat]; omega))).add hX
        (Dom.const 3) |>.of_le ?_ |>.mono hX ?_ ?_ ?_
      · simp only [decCtx, size_cons, size_ofNat]; omega
      · norm_num
      · norm_num
      · norm_num
    have hk : Dom W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k (2 + 1) 1 0
        (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))).size :=
      Dom.ofAffine (a := 2) (b := 1) (by rw [size_ofNat]; omega)
    have hZ := (((((((Dom.ofLeW hW.dim_le).add hX
      (Dom.ofLeW (v := 2 ^ (beta * (Nat.size lam + Nat.size n))) hparse)).add hX
      (hsX.of_le hlx)).add hX (hsY.of_le hly)).add hX (hsA.of_le hla)).add hX
      (hsB.of_le hlb)).add hX hctx).add hX hk |>.add hX (Dom.const 10)
    have hiter := ((Dom.const 40).mul ((hZ.add hX (Dom.const 30)).pow 2)).add hX hdomTu
    have hloop := ((Dom.ofLeW (v := 2 ^ (tau * (Nat.size lam + Nat.size n))) hreps).add hX
      (Dom.const 1)).mul hiter
    -- the size of the loop's state
    have hst := ((((((hk.add hX (hsX.of_le hlx)).add hX (hsY.of_le hly)).add hX
      (hsA.of_le hla)).add hX (hsB.of_le hlb)).add hX hctx).add hX (Dom.const 5))
    -- the whole budget, shared by both branches
    have chain := ((((((hdomP.add hX hloop).add hX hst).add hX (Dom.const 4)).add hX
      ((Dom.const 2).mul hsum)).add hX (Dom.const 40)).add hX hdomPar).add hX hin |>.add hX
      (Dom.const 3)
    by_cases hok : prepOk lam tau n (S.dim n) (bitsOf (toList xD)) (bitsOf (toList yD))
        (bitsOf (toList aD)) (bitsOf (toList bD)) = true
    · rw [prepResult, if_pos hok, prepState_eq] at hp
      obtain ⟨fq, hfq⟩ := loop_calls_time D n R hD (S.dim n)
        (2 ^ (tau * (Nat.size lam + Nat.size n))) ((bitsOf (toList xD)).map ofBool)
        ((bitsOf (toList yD)).map ofBool) (toList (parse (bitsOf (toList aD))))
        (toList (parse (bitsOf (toList bD))))
      obtain ⟨r, t₁, ht₁, hl⟩ := coordLoop_runs_bounded selfUniversal.closed (encode D.prog)
        (encode n) (S.dim n) (2 ^ (beta * (Nat.size lam + Nat.size n))) fq _ _
        (2 ^ (tau * (Nat.size lam + Nat.size n))) ((bitsOf (toList xD)).map ofBool)
        ((bitsOf (toList yD)).map ofBool) (toList (parse (bitsOf (toList aD))))
        (toList (parse (bitsOf (toList bD)))) [] hfq le_rfl
      have hmain := decMain_runs_state selfUniversal.closed _ _ _ hp hl
      have hcore := repDecCore_runs selfUniversal.closed (encode S.prog) (encode D.prog)
        (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD hmain
      refine ⟨r, _, ?_, hardcode_time (repDecCore_wellScoped selfUniversal.closed) hcore⟩
      unfold coordIter at ht₁
      refine (chain.of_le ?_).le
      simp only [size_cons, size_ofNat] at ht₀ ht₁ ⊢
      omega
    · rw [prepResult, if_neg hok] at hp
      have hmain := decMain_runs_nil _ hp
      have hcore := repDecCore_runs selfUniversal.closed (encode S.prog) (encode D.prog)
        (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD hmain
      refine ⟨.nil, _, ?_, hardcode_time (repDecCore_wellScoped selfUniversal.closed) hcore⟩
      refine (chain.of_le ?_).le
      simp only [size_cons, size_ofNat] at ht₀ ⊢
      omega⟩

/-- **The running time of the repeated decider**: constants `c, m, e` uniform in everything
such that, whenever `W` dominates the parameters at `n` and the input sampler and decider run
within `R.S (|d| + 1)^{R.k}` and `R.D (|d| + 1)^{R.k}` there, the repeated decider runs within
`c (W + 1)^m (|d| + 1)^{e (R.k + 1)}`. -/
theorem repDecider_timeBound : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
    (lam tau beta n : ℕ) (R : Budget) (W : ℕ), DecDom S D lam tau beta n R W →
    S.TimeBoundAt n R.S R.k → D.TimeBoundAt n R.D R.k →
    (repDecider S.prog D.prog lam tau beta).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1)) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := decMalformed_time
  obtain ⟨c₂, m₂, e₂, h₂⟩ := decWellformed_time
  refine ⟨c₁ + c₂, max m₁ m₂, max e₁ e₂, fun {ℓ} S D lam tau beta n R W hW hS hD d => ?_⟩
  have hX : 1 ≤ d.size + 1 := by omega
  rcases d with _ | ⟨xD, _ | ⟨yD, _ | ⟨aD, bD⟩⟩⟩
  · obtain ⟨r, t, ht, run⟩ := h₁ S D lam tau beta n R W .nil hW (Or.inl rfl)
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_left _ _) (le_max_left _ _)).le, run⟩
  · obtain ⟨r, t, ht, run⟩ := h₁ S D lam tau beta n R W _ hW (Or.inr (Or.inl ⟨xD, rfl⟩))
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_left _ _) (le_max_left _ _)).le, run⟩
  · obtain ⟨r, t, ht, run⟩ := h₁ S D lam tau beta n R W _ hW (Or.inr (Or.inr ⟨xD, yD, rfl⟩))
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_left _ _) (le_max_left _ _)).le, run⟩
  · obtain ⟨r, t, ht, run⟩ := h₂ S D lam tau beta n R W xD yD aD bD hW hS hD
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_right _ _) (le_max_right _ _)).le, run⟩

end MIPRE.Repeat
