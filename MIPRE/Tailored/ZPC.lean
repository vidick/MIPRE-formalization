/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Fourier
public import MIPRE.Foundations.GameDouble
public import MIPRE.Foundations.GameTransport
public import MIPRE.Tactics

@[expose] public section

/-!
# ZPC strategies are perfect commuting synchronous strategies

Paper II, §2.3–2.4. A Z-aligned permutation strategy commuting along edges (`PermStrategy`) is in
particular a synchronous quantum strategy — its measurements are the Fourier transforms of its
observables — which commutes on the support of the question distribution. This file proves it,
and collects the tools for showing that a permutation strategy is perfect.

* `PermStrategy.isPVMIn_proj`: the measurements are projective (`isPVMIn_fourierProj`, the
  observables being self-adjoint as involutive signed permutation matrices).
* `PermStrategy.value_eq_one_of`: a permutation strategy is perfect when every rejected answer
  pair of positive weight has `P^x_a P^y_b = 0`; `PermStrategy.dotBit_of_obsChar` says when that
  holds for a linear constraint, that is, when the constraint's observable `U^α V^β` acts as
  `(-1)^γ`; `satisfies_ofFn_iff` reads the canonical decider's `Satisfies` as
  `⟨α, a⟩ + ⟨β, b⟩ = γ`.
* `PermStrategy.toSync`, `isPCC_toSync`, `value_toSync` (blueprint `lem:zpc-pcc`): a permutation
  strategy for the doubled tailored game is a PCC synchronous strategy for the doubled bipartite
  game, with the same value; `TailoredGame.HasPerfectZPC.exists_pcc` and `valStar_eq_one`.
* `PermStrategy.double`, `value_double`: a permutation strategy for a game, played by both
  players, is one for the doubled game with the same value (the completeness half of Claim
  II:3127, in its bipartite case, Remark II:3159).
-/

namespace MIPRE.Tailored

open Cost Finset

/-! ## Answers of a fixed length -/

section Answers

/-- The first `L` bits of an answer, as a vector. -/
def bitVec {T : ℕ} (L : ℕ) (a : Verifier.Answers T) : Fin L → Bool := fun i => a.1.getD i false

/-- A vector of length at most `T`, as an answer. -/
def ofVec {T L : ℕ} (hL : L ≤ T) (v : Fin L → Bool) : Verifier.Answers T :=
  ⟨List.ofFn v, by simpa using hL⟩

theorem ofFn_bitVec {T L : ℕ} (a : Verifier.Answers T) (h : a.1.length = L) :
    List.ofFn (bitVec L a) = a.1 := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [bitVec, h2]

@[simp] theorem bitVec_ofVec {T L : ℕ} (hL : L ≤ T) (v : Fin L → Bool) :
    bitVec L (ofVec hL v) = v := by
  funext i
  simp [bitVec, ofVec]

theorem ofVec_injective {T L : ℕ} (hL : L ≤ T) : Function.Injective (ofVec (T := T) hL) :=
  fun _ _ h => List.ofFn_injective (congrArg Subtype.val h)

/-- **Summing over the answers of length `L`** is summing over the vectors of length `L`. -/
theorem sum_answers_ite {M : Type*} [AddCommMonoid M] {L T : ℕ} (hL : L ≤ T)
    (g : (Fin L → Bool) → M) :
    ∑ a : Verifier.Answers T, (if a.1.length = L then g (bitVec L a) else 0) = ∑ v, g v := by
  classical
  calc ∑ a : Verifier.Answers T, (if a.1.length = L then g (bitVec L a) else 0)
      = ∑ a ∈ univ.image (ofVec hL), (if a.1.length = L then g (bitVec L a) else 0) := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
        split_ifs with hlen
        · refine absurd (Finset.mem_image.2 ⟨bitVec L a, Finset.mem_univ _, ?_⟩) ha
          exact Subtype.ext (ofFn_bitVec a hlen)
        · rfl
    _ = ∑ v, (if (ofVec hL v).1.length = L then g (bitVec L (ofVec hL v)) else 0) :=
        Finset.sum_image fun _ _ _ _ h => ofVec_injective hL h
    _ = ∑ v, g v := Finset.sum_congr rfl fun v _ => by
        rw [ite_eq_left (by simp [ofVec]), bitVec_ofVec]

end Answers

/-! ## Linear constraints on vectors -/

/-- The parity of the number of common ones of two vectors is their inner product over `F₂`. -/
theorem even_count_zipWith_ofFn {k : ℕ} (α a : Fin k → Bool) :
    Even ((List.zipWith (· && ·) (List.ofFn α) (List.ofFn a)).count true) ↔
      dotBit α a = false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, List.count_cons, dotBit_succ]
    have := ih (fun i => α i.succ) fun i => a i.succ
    cases h : (α 0 && a 0) <;> simp [this, Nat.even_add_one]

/-- **The canonical decider's linear check on vectors** (II:1222): the constraint
`(α, β, γ)` is satisfied by the answers `(a, b)`, with `J = 1`, exactly when
`⟨α, a⟩ + ⟨β, b⟩ + γ = 0`. -/
theorem satisfies_ofFn_iff {k k' : ℕ} (α a : Fin k → Bool) (β b : Fin k' → Bool) (γ : Bool) :
    Satisfies (List.ofFn α ++ List.ofFn β ++ [γ]) (List.ofFn a ++ List.ofFn b ++ [true]) ↔
      xor (dotBit α a) (dotBit β b) = γ := by
  simp only [Satisfies, List.length_append, List.length_ofFn, List.length_singleton, true_and]
  rw [List.zipWith_append (l₁ := List.ofFn α ++ List.ofFn β) (l₂ := List.ofFn a ++ List.ofFn b)
      (by simp),
    List.zipWith_append (l₁ := List.ofFn α) (l₂ := List.ofFn a) (by simp), List.count_append,
    List.count_append, Nat.even_add, Nat.even_add, even_count_zipWith_ofFn,
    even_count_zipWith_ofFn]
  generalize dotBit α a = d₁
  generalize dotBit β b = d₂
  cases d₁ <;> cases d₂ <;> cases γ <;> simp

/-! ## Permutation strategies -/

variable {X : Type*} [Fintype X]

namespace TailoredGame

variable (G : TailoredGame X)

theorem len_le_maxLen (x : X) : G.len x ≤ G.maxLen := Finset.le_sup (Finset.mem_univ x)

@[simp] theorem doubled_μ (p q : Bool × X) :
    G.doubled.μ p q = if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0 := rfl

/-- An edge of the doubled game is an edge of the game. -/
theorem pos_of_doubled_pos {p q : Bool × X} (h : 0 < G.doubled.μ p q) : 0 < G.μ p.2 q.2 := by
  simp only [doubled] at h
  split_ifs at h
  · exact h
  · exact absurd h (lt_irrefl 0)

end TailoredGame

namespace PermStrategy

variable {G : TailoredGame X} (S : PermStrategy G)

/-- An involutive signed permutation matrix is self-adjoint. -/
theorem star_U (x : X) (i : Fin (G.len x)) : star (S.U x i) = S.U x i :=
  (S.signedPerm x i).isHermitian (S.invol x i)

theorem commute_U (x : X) (i j : Fin (G.len x)) : Commute (S.U x i) (S.U x j) := S.comm x i j

/-- **The measurements of a permutation strategy are projective.** -/
theorem isPVMIn_proj (x : X) : IsPVMIn (S.proj x) :=
  isPVMIn_fourierProj (S.invol x) (S.star_U x) (S.commute_U x)

/-- **Along an edge, the two measurements commute.** -/
theorem commute_proj {x y : X} (hxy : 0 < G.μ x y) (a : Fin (G.len x) → Bool)
    (b : Fin (G.len y) → Bool) : Commute (S.proj x a) (S.proj y b) :=
  Commute.fourierProj_fourierProj (fun i j => S.commEdges x y hxy i j) a b

theorem sum_proj (x : X) : ∑ a, S.proj x a = 1 := (S.isPVMIn_proj x).sum_eq_one

/-- The joint distribution at a question pair sums to one. -/
theorem sum_trace_proj_mul (x y : X) :
    ∑ a, ∑ b, (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) = 1 := by
  have h1 : ∑ a, ∑ b, S.proj x a * S.proj y b = 1 := by
    simp_rw [← Finset.mul_sum, S.sum_proj y, mul_one]
    exact S.sum_proj x
  have h2 := congrArg (fun M : Matrix (Fin S.m) (Fin S.m) ℂ => M.trace.re) h1
  simp only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_one, Fintype.card_fin,
    Complex.natCast_re] at h2
  simp_rw [← Finset.sum_div, h2]
  have : (S.m : ℝ) ≠ 0 := by exact_mod_cast S.m_pos.ne'
  exact div_self this

/-- **A permutation strategy is perfect when every rejected answer pair of positive weight has
`P^x_a P^y_b = 0`.** -/
theorem value_eq_one_of
    (h : ∀ x y, 0 < G.μ x y → ∀ a b, ¬G.Accepts x y (List.ofFn a) (List.ofFn b) →
      S.proj x a * S.proj y b = 0) :
    S.value = 1 := by
  unfold value
  have key : ∀ x y, (∑ a : Fin (G.len x) → Bool, ∑ b : Fin (G.len y) → Bool,
      G.μ x y * (if G.Accepts x y (List.ofFn a) (List.ofFn b) then 1 else 0) *
        ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ))) = G.μ x y := by
    intro x y
    rcases (G.μ_nonneg x y).lt_or_eq with hpos | hzero
    · have hab : ∀ a b, (if G.Accepts x y (List.ofFn a) (List.ofFn b) then (1 : ℝ) else 0) *
          ((S.proj x a * S.proj y b).trace.re / (S.m : ℝ)) =
            (S.proj x a * S.proj y b).trace.re / (S.m : ℝ) := by
        intro a b
        split_ifs with hacc
        · rw [one_mul]
        · rw [h x y hpos a b hacc, Matrix.trace_zero, Complex.zero_re, zero_div, mul_zero]
      simp_rw [mul_assoc, hab, ← Finset.mul_sum, S.sum_trace_proj_mul x y, mul_one]
    · simp [← hzero]
  simp only [key]
  exact G.μ_sum_one

/-- **The constraint lemma**: along an edge, if the observable `U^α V^β` of a linear constraint
acts as the scalar `(-1)^γ` on the range of `P^x_a P^y_b ≠ 0`, then `⟨α, a⟩ + ⟨β, b⟩ = γ` —
the constraint holds on every answer pair the strategy samples (Claim II:2870). -/
theorem dotBit_of_obsChar {x y : X} (hxy : 0 < G.μ x y) {a α : Fin (G.len x) → Bool}
    {b β : Fin (G.len y) → Bool} {γ : Bool}
    (h : obsChar (S.U x) α * obsChar (S.U y) β * (S.proj x a * S.proj y b) =
      bitSign γ • (S.proj x a * S.proj y b))
    (hne : S.proj x a * S.proj y b ≠ 0) :
    xor (dotBit α a) (dotBit β b) = γ := by
  have hV : Commute (obsChar (S.U y) β) (S.proj x a) :=
    (Commute.obsChar_right (fun j => (Commute.fourierProj_right
      (fun i => (show Commute (S.U x i) (S.U y j) from S.commEdges x y hxy i j).symm) a).symm)
      β).symm
  have hx := obsChar_mul_fourierProj (S.invol x) (S.commute_U x) α a
  have hy := obsChar_mul_fourierProj (S.invol y) (S.commute_U y) β b
  have hcalc : obsChar (S.U x) α * obsChar (S.U y) β * (S.proj x a * S.proj y b) =
      (bitSign (dotBit α a) * bitSign (dotBit β b)) • (S.proj x a * S.proj y b) := by
    rw [mul_assoc, ← mul_assoc (obsChar (S.U y) β), hV.eq, mul_assoc, ← mul_assoc]
    change obsChar (S.U x) α * fourierProj (S.U x) a *
      (obsChar (S.U y) β * fourierProj (S.U y) b) = _
    rw [hx, hy, smul_mul_smul_comm]
    rfl
  rw [hcalc, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h
  rcases h with h | h
  · rw [sub_eq_zero, ← bitSign_xor] at h
    exact bitSign_injective h
  · exact absurd h hne

/-! ## `lem:zpc-pcc`: a permutation strategy as a synchronous strategy -/

/-- The measurement at `x` on answer strings: the projection of the string's vector when it has
the length of the answers at `x`, and zero otherwise. -/
noncomputable def ansProj (T : ℕ) (x : X) (a : Verifier.Answers T) :
    Matrix (Fin S.m) (Fin S.m) ℂ :=
  if a.1.length = G.len x then S.proj x (bitVec (G.len x) a) else 0

theorem isPVMIn_ansProj {T : ℕ} (x : X) (hT : G.len x ≤ T) : IsPVMIn (S.ansProj T x) where
  star_eq a := by
    unfold ansProj
    split_ifs
    · exact (S.isPVMIn_proj x).star_eq _
    · exact star_zero _
  idem a := by
    unfold ansProj
    split_ifs
    · exact (S.isPVMIn_proj x).idem _
    · exact zero_mul _
  sum_eq_one := by
    unfold ansProj
    rw [sum_answers_ite hT (S.proj x)]
    exact S.sum_proj x
  orthogonal {a b} hab := by
    unfold ansProj
    split_ifs with ha hb
    · refine (S.isPVMIn_proj x).orthogonal fun hv => hab (Subtype.ext ?_)
      rw [← ofFn_bitVec a ha, ← ofFn_bitVec b hb, hv]
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _

/-- **`lem:zpc-pcc`**: the measurements of a permutation strategy for the doubled tailored game,
as a synchronous strategy for the doubled bipartite game. -/
noncomputable def toSync (S : PermStrategy G.doubled) : SyncStrategy G.toGame.doubled where
  d := S.m
  d_pos := S.m_pos
  P :=
    { M := S.ansProj G.maxLen
      selfAdjoint := fun p a => (S.isPVMIn_ansProj p (G.len_le_maxLen p.2)).star_eq a
      projective := fun p a => (S.isPVMIn_ansProj p (G.len_le_maxLen p.2)).idem a
      normalized := fun p => (S.isPVMIn_ansProj p (G.len_le_maxLen p.2)).sum_eq_one }

/-- **The synchronous strategy commutes on the support of the question distribution**, the
permutation strategy commuting along edges. -/
theorem isPCC_toSync (S : PermStrategy G.doubled) : S.toSync.IsPCC := by
  intro p q hpq a b
  have hc := S.commute_proj (x := p) (y := q) hpq
  change S.ansProj _ p a * S.ansProj _ q b = S.ansProj _ q b * S.ansProj _ p a
  unfold ansProj
  split_ifs
  · exact (hc _ _).eq
  · simp
  · simp
  · simp

/-- **The synchronous strategy has the value of the permutation strategy.** -/
theorem value_toSync (S : PermStrategy G.doubled) : S.toSync.value = S.value := by
  rw [SyncStrategy.value_eq]
  unfold PermStrategy.value
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  -- the summand of the permutation strategy's value, as a function of the two vectors
  set F : (Fin (G.doubled.len p) → Bool) → (Fin (G.doubled.len q) → Bool) → ℝ := fun v w =>
    G.doubled.μ p q * (if G.doubled.Accepts p q (List.ofFn v) (List.ofFn w) then 1 else 0) *
      ((S.proj p v * S.proj q w).trace.re / (S.m : ℝ)) with hF
  have hterm : ∀ (a b : Verifier.Answers G.maxLen),
      G.toGame.doubled.μ p q * (if G.toGame.doubled.D p q a b then 1 else 0) *
        ((S.toSync.P.M p a * S.toSync.P.M q b).trace.re / (S.toSync.d : ℝ)) =
      if a.1.length = G.doubled.len p then
        (if b.1.length = G.doubled.len q then F (bitVec _ a) (bitVec _ b) else 0) else 0 := by
    intro a b
    change G.toGame.doubled.μ p q * (if G.toGame.doubled.D p q a b then 1 else 0) *
        ((S.ansProj _ p a * S.ansProj _ q b).trace.re / (S.m : ℝ)) = _
    unfold ansProj
    by_cases ha : a.1.length = G.doubled.len p
    · by_cases hb : b.1.length = G.doubled.len q
      · simp only [ha, hb, ite_true]
        rw [hF]
        dsimp only
        rw [ofFn_bitVec a ha, ofFn_bitVec b hb]
        by_cases hpq : p.1 = false ∧ q.1 = true
        · have hD : G.toGame.doubled.D p q a b = decide (G.doubled.Accepts p q a.1 b.1) := by
            change (if p.1 = false ∧ q.1 = true then G.toGame.D p.2 q.2 a b else false) = _
            rw [ite_eq_left hpq]
            rfl
          rw [hD]
          by_cases hacc : G.doubled.Accepts p q a.1 b.1
          · simp only [hacc, decide_true, ite_true]
            rfl
          · simp only [hacc, decide_false, Bool.false_eq_true, ite_false, mul_zero, zero_mul]
        · have h0 : G.doubled.μ p q = 0 := by simp [TailoredGame.doubled, hpq]
          change G.doubled.μ p q * _ * _ = G.doubled.μ p q * _ * _
          simp only [h0, zero_mul]
      · simp only [ha, hb, ite_true, ite_false, mul_zero, Matrix.trace_zero, Complex.zero_re,
          zero_div]
    · simp only [ha, ite_false, zero_mul, Matrix.trace_zero, Complex.zero_re, zero_div, mul_zero]
  simp_rw [hterm]
  have hinner : ∀ a : Verifier.Answers G.maxLen,
      (∑ b : Verifier.Answers G.maxLen, if a.1.length = G.doubled.len p then
        (if b.1.length = G.doubled.len q then F (bitVec _ a) (bitVec _ b) else 0) else 0) =
      if a.1.length = G.doubled.len p then ∑ w, F (bitVec _ a) w else 0 := by
    intro a
    split_ifs with ha
    · exact sum_answers_ite (L := G.doubled.len q) (G.len_le_maxLen q.2) _
    · simp
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  exact sum_answers_ite (L := G.doubled.len p) (G.len_le_maxLen p.2) fun v => ∑ w, F v w

/-- **A permutation strategy, played by both players, for the doubled game.** -/
def double (S : PermStrategy G) : PermStrategy G.doubled where
  m := S.m
  m_pos := S.m_pos
  U p := S.U p.2
  signedPerm p := S.signedPerm p.2
  invol p := S.invol p.2
  comm p := S.comm p.2
  zAligned p := S.zAligned p.2
  commEdges p q h := S.commEdges p.2 q.2 (G.pos_of_doubled_pos h)

theorem proj_double (p : Bool × X) (a : Fin (G.len p.2) → Bool) :
    S.double.proj p a = S.proj p.2 a := rfl

/-- **Doubling a permutation strategy keeps its value** (Claim II:3127, completeness, in the
bipartite case of Remark II:3159). -/
theorem value_double : S.double.value = S.value := by
  unfold value
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, TailoredGame.doubled_μ]
  simp only [Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, ite_false, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, and_self, ite_true]
  rfl

end PermStrategy

namespace TailoredGame

variable {G : TailoredGame X}

/-- A game with a perfect ZPC strategy has one for its doubled game. -/
theorem HasPerfectZPC.doubled (h : G.HasPerfectZPC) : G.doubled.HasPerfectZPC := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S.double, by rw [S.value_double, hS]⟩

/-- **`lem:zpc-pcc`**: a perfect ZPC strategy for the doubled game gives a perfect PCC strategy
for the doubled bipartite game. -/
theorem HasPerfectZPC.exists_pcc (h : G.doubled.HasPerfectZPC) :
    ∃ S : SyncStrategy G.toGame.doubled, S.IsPCC ∧ S.value = 1 := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S.toSync, S.isPCC_toSync, by rw [S.value_toSync, hS]⟩

/-- A perfect ZPC strategy for the doubled game gives synchronous value `1`. -/
theorem HasPerfectZPC.syncValue_eq_one (h : G.doubled.HasPerfectZPC) :
    syncValue G.toGame.doubled = 1 := by
  obtain ⟨S, -, hS⟩ := h.exists_pcc
  refine le_antisymm (Real.iSup_le (fun S => S.value_le_one) zero_le_one) ?_
  rw [← hS]
  exact le_ciSup ⟨1, by rintro _ ⟨S', rfl⟩; exact S'.value_le_one⟩ S

/-- **A perfect ZPC strategy for the doubled game gives quantum value `1`.** -/
theorem HasPerfectZPC.valStar_eq_one (h : G.doubled.HasPerfectZPC) : G.valStar = 1 := by
  have h1 := syncValue_le_quantumValue G.toGame.doubled
  rw [h.syncValue_eq_one, quantumValue_doubled] at h1
  exact le_antisymm (quantumValue_le_one _) h1

end TailoredGame

end MIPRE.Tailored

end
