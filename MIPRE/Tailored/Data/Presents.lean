/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Data.Convert
public import MIPRE.Tailored.ZPC
public import MIPRE.Foundations.GameTransportByQuestion
public import MIPRE.Foundations.GameDouble
public import MIPRE.Tactics

@[expose] public section

/-!
# A tailored game description presenting a tailored game

A `TailoredGameValue.TailoredGameData` *presents* a tailored game `G` of the library
(`MIPRE.Tailored.TailoredGame`) along a bijection `e` of its vertices with `G`'s questions when it
has the same weights, the same numbers of readable and linear variables, and the same constraints
(`Presents`). The two read answers differently — the description reads bit vectors of the largest
length that vanish beyond a vertex's variables, the library bit strings of exactly that length —
and the description's canonical decider also rejects unequal answers at a loop. On a game with no
weight on its loops, such as a doubled game, neither difference costs anything:

* `Presents.quantumValue_eq`: the description has the quantum value of the game. Answers pass from
  vectors to strings by keeping a vertex's coordinates (`Presents.toStr`) and back by padding with
  zeros (`Presents.toVec`), question by question (`TensorProductStrategy.mergeAnswersByQuestion`).
* `Presents.hasPerfectZPC`: a perfect ZPC strategy of the game is one of the description, its
  observables padded with identities.

Two general facts are used: the quantum value depends on the decision predicate only where the
distribution has weight (`quantumValue_eq_of_equiv_support`), and a tailored game and its doubled
game have the same quantum value (`TailoredGame.quantumValue_doubled_eq_valStar`).
-/

namespace MIPRE

open Cost
open scoped ComplexOrder MatrixOrder

/-! ## The quantum value sees the predicate only where there is weight -/

section Support

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- Strategies have the same value on two games with the same distribution and predicates that
agree wherever the distribution has weight. -/
theorem TensorProductStrategy.value_copy_support {G : Game X Y A B} (S : TensorProductStrategy G)
    (G' : Game X Y A B) (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y, G.μ x y ≠ 0 → ∀ a b, G'.D x y a b = G.D x y a b) :
    (S.copy G').value = S.value := by
  unfold TensorProductStrategy.value
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  show G'.μ x y * (if G'.D x y a b then 1 else 0) * _ = G.μ x y * (if G.D x y a b then 1 else 0) * _
  rw [hμ]
  by_cases h : G.μ x y = 0
  · simp [h]
  · rw [hD x y h a b]
    rfl

/-- **The quantum value depends on the predicate only where the distribution has weight.** -/
theorem quantumValue_congr_support (G G' : Game X Y A B) (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y, G.μ x y ≠ 0 → ∀ a b, G'.D x y a b = G.D x y a b) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    have h := S'.value_copy_support G (fun x y => (hμ x y).symm) fun x y hxy a b =>
      (hD x y (by rwa [← hμ]) a b).symm
    rw [← h]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) _
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_copy_support G' hμ hD]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G') _

/-- **Relabeling, with the predicates agreeing only where there is weight.** -/
theorem quantumValue_eq_of_equiv_support {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y']
    [Fintype A'] [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X)
    (eY : Y' ≃ Y) (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y', G'.μ x' y' ≠ 0 →
      ∀ a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    quantumValue G' = quantumValue G := by
  let G'' : Game X' Y' A' B' :=
    { μ := G'.μ
      μ_nonneg := G'.μ_nonneg
      μ_sum_one := G'.μ_sum_one
      D := fun x' y' a' b' => G.D (eX x') (eY y') (eA a') (eB b') }
  have h1 : quantumValue G' = quantumValue G'' :=
    quantumValue_congr_support G'' G' (fun _ _ => rfl) fun x y h a b => hD x y h a b
  rw [h1]
  exact quantumValue_eq_of_equiv G G'' eX eY eA eB hμ fun _ _ _ _ => rfl

end Support

/-- **Question-dependent answer decoding can only raise the value** of a tensor-product strategy. -/
theorem TensorProductStrategy.value_le_mergeAnswersByQuestion' {X Y A B A' B' : Type*} [Fintype X]
    [Fintype Y] [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]
    {G' : Game X Y A' B'} (S' : TensorProductStrategy G') (G : Game X Y A B) (rA : X → A' → A)
    (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
    S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value := by
  rw [S'.value_mergeAnswersByQuestion, ← S'.value_toModel]
  exact S'.toModel.value_le_mergeAnswersByQuestion G rA rB hμ hD

namespace Tailored

open TailoredGameValue

namespace TailoredGame

variable {X : Type*} [Fintype X] (G : TailoredGame X)

theorem doubled_maxLen : G.doubled.maxLen = G.maxLen := by
  apply le_antisymm
  · exact Finset.sup_le fun p _ => G.len_le_maxLen p.2
  · exact Finset.sup_le fun x _ =>
      (Finset.le_sup (f := G.doubled.len) (Finset.mem_univ (false, x)) : G.len x ≤ _)

/-- **A tailored game and its doubled game have the same quantum value.** -/
theorem quantumValue_doubled_eq_valStar : quantumValue G.doubled.toGame = G.valStar := by
  have hA : ∀ a : BitStr, a.length ≤ G.doubled.maxLen ↔ a.length ≤ G.maxLen := fun a => by
    rw [doubled_maxLen]
  let eA : Verifier.Answers G.doubled.maxLen ≃ Verifier.Answers G.maxLen :=
    Equiv.subtypeEquivRight hA
  rw [TailoredGame.valStar, ← _root_.MIPRE.quantumValue_doubled G.toGame]
  refine quantumValue_eq_of_equiv_support G.toGame.doubled.toGame G.doubled.toGame (Equiv.refl _)
    (Equiv.refl _) eA eA (fun _ _ => rfl) fun p q hpq a b => ?_
  have htag : p.1 = false ∧ q.1 = true := by
    by_contra h
    exact hpq (by simp [TailoredGame.toGame, TailoredGame.doubled, h])
  show decide (G.doubled.Accepts p q a.1 b.1) =
    (if p.1 = false ∧ q.1 = true then decide (G.Accepts p.2 q.2 a.1 b.1) else false)
  rw [ite_eq_left htag]
  rfl

end TailoredGame

/-! ## Fourier transforms padded with identities -/

section Padding

variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem fourierFactor_one_false : fourierFactor (1 : R) false = 1 := by
  simp only [fourierFactor, bitSign_false]
  module

theorem fourierFactor_one_true : fourierFactor (1 : R) true = 0 := by
  simp only [fourierFactor, bitSign_true]
  module

/-- An observable equal to the identity annihilates the Fourier transform at an answer whose bit
there is `1`. -/
theorem fourierProj_eq_zero_of_one {n : ℕ} (U : Fin n → R) (a : Fin n → Bool) (k : Fin n)
    (hU : U k = 1) (ha : a k = true) : fourierProj U a = 0 := by
  unfold fourierProj
  apply List.prod_eq_zero
  rw [List.mem_map]
  exact ⟨k, List.mem_finRange k, by rw [hU, ha, fourierFactor_one_true]⟩

/-- **Padding with identities**: observables equal to the identity beyond `L` leave the Fourier
transform unchanged at an answer that vanishes beyond `L`. -/
theorem fourierProj_castLE {L n : ℕ} (hL : L ≤ n) (U : Fin n → R)
    (hU : ∀ k : Fin n, L ≤ k.val → U k = 1) (a : Fin n → Bool)
    (ha : ∀ k : Fin n, L ≤ k.val → a k = false) :
    fourierProj U a =
      fourierProj (fun k => U (Fin.castLE hL k)) fun k => a (Fin.castLE hL k) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hL
  unfold fourierProj
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, List.ofFn_add, List.prod_append]
  have h1 : (List.ofFn fun j : Fin r =>
      fourierFactor (U (Fin.natAdd L j)) (a (Fin.natAdd L j))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    rw [hU _ (by simp), ha _ (by simp), fourierFactor_one_false]
  rw [h1, mul_one]

end Padding

/-! ## Presentations -/

variable {X : Type*} [Fintype X] {g : TailoredGameData} {G : TailoredGame X}
  {e : Fin (g.nV + 1) ≃ X}

/-- **A tailored game description presents a tailored game** along a bijection of its vertices with
the game's questions: the same weights, the same numbers of readable and linear variables, and,
for every pair of vertices and every readable part of the right length, the same constraints. -/
structure Presents (g : TailoredGameData) (G : TailoredGame X) (e : Fin (g.nV + 1) ≃ X) : Prop where
  μ_eq : ∀ i j, g.toGame.μ i j = G.μ (e i) (e j)
  lenR_eq : ∀ i : Fin (g.nV + 1), g.lenRAt i = G.lenR (e i)
  lenL_eq : ∀ i : Fin (g.nV + 1), g.lenLAt i = G.lenL (e i)
  cons_iff : ∀ (i j : Fin (g.nV + 1)) (γ c : List Bool),
    γ.length = G.lenR (e i) + G.lenR (e j) →
      ((i.val, j.val, γ, c) ∈ g.cons ↔
        c ∈ G.cons (e i) (e j) (γ.take (G.lenR (e i))) (γ.drop (G.lenR (e i))))

namespace Presents

variable (hP : Presents g G e)
include hP

theorem lenAt_eq (i : Fin (g.nV + 1)) : g.lenAt i = G.len (e i) := by
  rw [TailoredGameData.lenAt, hP.lenR_eq, hP.lenL_eq]
  rfl

omit hP in
theorem length_full (i : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    (g.full i a).length = g.lenAt i := by
  simp [TailoredGameData.full]

omit hP in
theorem readable_eq_take (i : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) :
    g.readable i a = (g.full i a).take (g.lenRAt i) := by
  rw [TailoredGameData.readable, TailoredGameData.full, ← List.map_take, List.take_range,
    min_eq_left (show g.lenRAt i ≤ g.lenAt i from Nat.le_add_right _ _)]

/-- The answer at vertex `i`, as the bit string of its variables. -/
def toStr (i : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool) : Verifier.Answers G.maxLen :=
  ⟨g.full i a, by rw [length_full, hP.lenAt_eq]; exact G.len_le_maxLen (e i)⟩

omit hP in
/-- A bit string, as an answer vector: padded with zeros, truncated at the largest length. -/
def toVec (s : Verifier.Answers G.maxLen) : Fin g.ansLen → Bool := fun k => s.1.getD k false

omit hP in
theorem full_toVec (i : Fin (g.nV + 1)) (s : BitStr) (hs : s.length = g.lenAt i) :
    g.full i (fun k : Fin g.ansLen => s.getD k false) = s := by
  apply List.ext_getElem
  · rw [length_full, hs]
  · intro k h1 h2
    have hk : k < g.lenAt i := by rw [length_full] at h1; exact h1
    have hkA : k < g.ansLen := hk.trans_le (g.lenAt_le_ansLen i)
    simp only [TailoredGameData.full, List.getElem_map, List.getElem_range,
      TailoredGameData.bit, dite_eq_left hkA]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

omit hP in
theorem wellFormatted_toVec (i : Fin (g.nV + 1)) (s : BitStr) (hs : s.length = g.lenAt i) :
    g.WellFormatted i (fun k : Fin g.ansLen => s.getD k false) := by
  intro k hk
  show s.getD k false = false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]

/-- **The two deciders agree on well-formatted answers**: the description's accepts exactly when
the answers are equal at a loop and the game accepts their bit strings. -/
theorem accepts_iff (i j : Fin (g.nV + 1)) (a b : Fin g.ansLen → Bool)
    (ha : g.WellFormatted i a) (hb : g.WellFormatted j b) :
    g.Accepts i j a b ↔ (i = j → a = b) ∧ G.Accepts (e i) (e j) (g.full i a) (g.full j b) := by
  have hγ : (g.readable i a ++ g.readable j b).length = G.lenR (e i) + G.lenR (e j) := by
    simp [TailoredGameData.readable, hP.lenR_eq]
  have htake : (g.readable i a ++ g.readable j b).take (G.lenR (e i)) = g.readable i a := by
    rw [List.take_append_of_le_length (by simp [TailoredGameData.readable, hP.lenR_eq]),
      List.take_of_length_le (by simp [TailoredGameData.readable, hP.lenR_eq])]
  have hdrop : (g.readable i a ++ g.readable j b).drop (G.lenR (e i)) = g.readable j b := by
    rw [List.drop_append_of_le_length (by simp [TailoredGameData.readable, hP.lenR_eq]),
      List.drop_of_length_le (by simp [TailoredGameData.readable, hP.lenR_eq]), List.nil_append]
  have hrdi : (g.full i a).take (G.lenR (e i)) = g.readable i a := by
    rw [readable_eq_take, hP.lenR_eq]
  have hrdj : (g.full j b).take (G.lenR (e j)) = g.readable j b := by
    rw [readable_eq_take, hP.lenR_eq]
  have hli : (g.full i a).length = G.len (e i) := by rw [length_full, hP.lenAt_eq]
  have hlj : (g.full j b).length = G.len (e j) := by rw [length_full, hP.lenAt_eq]
  constructor
  · rintro ⟨hl, -, -, hcons⟩
    refine ⟨hl, hli, hlj, fun c hc => ?_⟩
    rw [hrdi, hrdj] at hc
    have hmem := (hP.cons_iff i j _ c hγ).2 (by rw [htake, hdrop]; exact hc)
    exact hcons _ hmem rfl rfl rfl
  · rintro ⟨hl, -, -, hcons⟩
    refine ⟨hl, ha, hb, ?_⟩
    rintro ⟨i', j', γ', c⟩ hmem h1 h2 h3
    obtain rfl : i' = i.val := h1
    obtain rfl : j' = j.val := h2
    obtain rfl : γ' = g.readable i a ++ g.readable j b := h3
    have := (hP.cons_iff i j _ c hγ).1 hmem
    rw [htake, hdrop] at this
    exact hcons c (by rw [hrdi, hrdj]; exact this)

/-! ## The quantum value -/

/-- The game on the description's vertices with the library's answers: the game read along `e`,
rejecting unequal answers at a loop. -/
noncomputable def midGame : Game (Fin (g.nV + 1)) (Fin (g.nV + 1)) (Verifier.Answers G.maxLen)
    (Verifier.Answers G.maxLen) where
  μ := g.toGame.μ
  μ_nonneg := g.toGame.μ_nonneg
  μ_sum_one := g.toGame.μ_sum_one
  D i j s t := G.toGame.D (e i) (e j) s t && (!decide (i = j) || decide (s = t))

omit hP in
theorem quantumValue_midGame (hP : Presents g G e) (hloop : ∀ x, G.μ x x = 0) :
    quantumValue (midGame (e := e) : Game _ _ (Verifier.Answers G.maxLen) _) =
      quantumValue G.toGame := by
  refine quantumValue_eq_of_equiv_support G.toGame midGame e e (Equiv.refl _) (Equiv.refl _)
    hP.μ_eq fun i j hij s t => ?_
  have hne : i ≠ j := by
    rintro rfl
    exact hij (by rw [show midGame.μ i i = g.toGame.μ i i from rfl, hP.μ_eq, hloop])
  show (G.toGame.D (e i) (e j) s t && (!decide (i = j) || decide (s = t))) = _
  simp [hne]

theorem quantumValue_le_midGame :
    quantumValue g.game ≤
      quantumValue (midGame (e := e) : Game _ _ (Verifier.Answers G.maxLen) _) := by
  refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
  refine (S'.value_le_mergeAnswersByQuestion' midGame (fun i a => hP.toStr i a)
    (fun j b => hP.toStr j b) (fun _ _ => rfl) fun i j a b h => ?_).trans
    (le_ciSup (TensorProductStrategy.bddAbove_range_value _) _)
  have hacc : g.Accepts i j a b := of_decide_eq_true h
  have ha := hacc.2.1
  have hb := hacc.2.2.1
  obtain ⟨hloop, hG⟩ := (hP.accepts_iff i j a b ha hb).1 hacc
  show (decide (G.Accepts (e i) (e j) (g.full i a) (g.full j b)) &&
    (!decide (i = j) || decide (hP.toStr i a = hP.toStr j b))) = true
  rw [Bool.and_eq_true, decide_eq_true_iff, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_iff]
  refine ⟨hG, ?_⟩
  by_cases hij : i = j
  · subst hij
    exact Or.inr (by rw [hloop rfl])
  · exact Or.inl hij

theorem midGame_le_quantumValue :
    quantumValue (midGame (e := e) : Game _ _ (Verifier.Answers G.maxLen) _) ≤
      quantumValue g.game := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  refine (S.value_le_mergeAnswersByQuestion' g.game (fun _ s => toVec s)
    (fun _ t => toVec t) (fun _ _ => rfl) fun i j s t h => ?_).trans
    (le_ciSup (TensorProductStrategy.bddAbove_range_value _) _)
  have h' : (G.toGame.D (e i) (e j) s t && (!decide (i = j) || decide (s = t))) = true := h
  rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_iff] at h'
  obtain ⟨hD, hst⟩ := h'
  have hG : G.Accepts (e i) (e j) s.1 t.1 := of_decide_eq_true hD
  have hs : s.1.length = g.lenAt i := by rw [hP.lenAt_eq]; exact hG.1
  have ht : t.1.length = g.lenAt j := by rw [hP.lenAt_eq]; exact hG.2.1
  have ha := wellFormatted_toVec i s.1 hs
  have hb := wellFormatted_toVec j t.1 ht
  refine decide_eq_true ((hP.accepts_iff i j _ _ ha hb).2 ⟨fun hij => ?_, ?_⟩)
  · rcases hst with hne | heq
    · exact absurd hij hne
    · rw [heq]
  · rw [full_toVec i s.1 hs, full_toVec j t.1 ht]
    exact hG

/-- **A presentation of a game with no weight on its loops has the game's quantum value.** -/
theorem quantumValue_eq (hloop : ∀ x, G.μ x x = 0) : quantumValue g.game = quantumValue G.toGame :=
  (le_antisymm hP.quantumValue_le_midGame hP.midGame_le_quantumValue).trans
    (quantumValue_midGame hP hloop)

/-! ## Perfect ZPC strategies -/

theorem len_le_ansLen (i : Fin (g.nV + 1)) : G.len (e i) ≤ g.ansLen := by
  rw [← hP.lenAt_eq]
  exact g.lenAt_le_ansLen i

omit hP in
/-- An answer to a question, as an answer vector at its vertex: padded with zeros. -/
def padVec (G : TailoredGame X) (e : Fin (g.nV + 1) ≃ X) (i : Fin (g.nV + 1))
    (a : Fin (G.len (e i)) → Bool) : Fin g.ansLen → Bool :=
  fun k => if h : k.val < G.len (e i) then a ⟨k.val, h⟩ else false

theorem padVec_injective (i : Fin (g.nV + 1)) : Function.Injective (padVec G e i) := by
  intro a b h
  funext k
  have := congrFun h ⟨k.val, k.isLt.trans_le (hP.len_le_ansLen i)⟩
  simpa [padVec, k.isLt] using this

/-- An answer vector that is not padded has a `1` beyond the question's variables. -/
theorem exists_of_not_mem_range (i : Fin (g.nV + 1)) (a : Fin g.ansLen → Bool)
    (ha : a ∉ Set.range (padVec G e i)) :
    ∃ k : Fin g.ansLen, G.len (e i) ≤ k.val ∧ a k = true := by
  by_contra hne
  push Not at hne
  apply ha
  refine ⟨fun k => a ⟨k.val, k.isLt.trans_le (hP.len_le_ansLen i)⟩, funext fun k => ?_⟩
  by_cases hk : k.val < G.len (e i)
  · simp [padVec, hk]
  · have h1 := hne k (not_lt.1 hk)
    simp only [padVec, dite_eq_right hk]
    cases h2 : a k
    · rfl
    · exact absurd h2 h1

theorem wellFormatted_padVec (i : Fin (g.nV + 1)) (a : Fin (G.len (e i)) → Bool) :
    g.WellFormatted i (padVec G e i a) := by
  intro k hk
  rw [hP.lenAt_eq] at hk
  simp only [padVec, dite_eq_right (not_lt.2 hk)]

theorem full_padVec (i : Fin (g.nV + 1)) (a : Fin (G.len (e i)) → Bool) :
    g.full i (padVec G e i a) = List.ofFn a := by
  apply List.ext_getElem
  · rw [length_full, hP.lenAt_eq, List.length_ofFn]
  · intro k h1 h2
    rw [List.length_ofFn] at h2
    have hkA : k < g.ansLen := h2.trans_le (hP.len_le_ansLen i)
    simp only [TailoredGameData.full, List.getElem_map, List.getElem_range,
      TailoredGameData.bit, dite_eq_left hkA, padVec, dite_eq_left h2, List.getElem_ofFn]

omit hP in
/-- **The padded strategy**: a permutation strategy of the game, read on the description, its
observables padded with identities beyond a question's variables. -/
noncomputable def padStrategy (hP : Presents g G e) (S : Tailored.PermStrategy G) :
    TailoredGameValue.PermStrategy g where
  m := S.m
  m_pos := S.m_pos
  U i k := if h : k.val < G.len (e i) then S.U (e i) ⟨k.val, h⟩ else 1
  signedPerm i k := by
    by_cases h : k.val < G.len (e i)
    · obtain ⟨σ, s, hσ⟩ := S.signedPerm (e i) ⟨k.val, h⟩
      exact ⟨σ, s, by rw [dite_eq_left h, hσ]; rfl⟩
    · exact ⟨1, fun _ => false, by
        rw [dite_eq_right h, TailoredGameValue.signedPermMatrix_eq, signedPermMatrix_one_one]⟩
  invol i k := by
    by_cases h : k.val < G.len (e i)
    · rw [dite_eq_left h]; exact S.invol _ _
    · rw [dite_eq_right h, one_mul]
  comm i k k' := by
    by_cases h : k.val < G.len (e i) <;> by_cases h' : k'.val < G.len (e i)
    · simp only [dite_eq_left h, dite_eq_left h']; exact S.comm _ _ _
    · simp only [dite_eq_left h, dite_eq_right h', one_mul, mul_one]
    · simp only [dite_eq_right h, dite_eq_left h', one_mul, mul_one]
    · simp only [dite_eq_right h, dite_eq_right h']
  pad i k hk := dite_eq_right (by rw [← hP.lenAt_eq]; omega)
  zAligned i k hk := by
    have hk' : k.val < G.len (e i) := by
      rw [← hP.lenAt_eq]; exact lt_of_lt_of_le hk (Nat.le_add_right _ _)
    rw [dite_eq_left hk']
    exact S.zAligned _ _ (by rw [← hP.lenR_eq]; exact hk)
  commEdges i j hij k k' := by
    have hμ : 0 < G.μ (e i) (e j) := by rw [← hP.μ_eq]; exact hij
    by_cases h : k.val < G.len (e i) <;> by_cases h' : k'.val < G.len (e j)
    · simp only [dite_eq_left h, dite_eq_left h']; exact S.commEdges _ _ hμ _ _
    · simp only [dite_eq_left h, dite_eq_right h', one_mul, mul_one]
    · simp only [dite_eq_right h, dite_eq_left h', one_mul, mul_one]
    · simp only [dite_eq_right h, dite_eq_right h']

/-- The padded strategy's measurement at an unpadded answer vector is `0`. -/
theorem proj_padStrategy_eq_zero (S : Tailored.PermStrategy G) (i : Fin (g.nV + 1))
    (a : Fin g.ansLen → Bool) (k : Fin g.ansLen) (hk : G.len (e i) ≤ k.val) (ha : a k = true) :
    (hP.padStrategy S).proj i a = 0 := by
  rw [TailoredGameValue.PermStrategy.proj_eq]
  exact fourierProj_eq_zero_of_one _ a k (dite_eq_right (not_lt.2 hk)) ha

/-- The padded strategy's measurement at a padded answer is the strategy's. -/
theorem proj_padStrategy (S : Tailored.PermStrategy G) (i : Fin (g.nV + 1))
    (a : Fin (G.len (e i)) → Bool) :
    (hP.padStrategy S).proj i (padVec G e i a) = S.proj (e i) a := by
  rw [TailoredGameValue.PermStrategy.proj_eq,
    fourierProj_castLE (hP.len_le_ansLen i) _ (fun k hk => dite_eq_right (not_lt.2 hk)) _
      (fun k hk => dite_eq_right (not_lt.2 hk))]
  have hU : (fun k : Fin (G.len (e i)) =>
      (hP.padStrategy S).U i (Fin.castLE (hP.len_le_ansLen i) k)) = S.U (e i) := by
    funext k
    show (if h : k.val < G.len (e i) then S.U (e i) ⟨k.val, h⟩ else 1) = S.U (e i) k
    rw [dite_eq_left k.isLt]
  have ha : (fun k : Fin (G.len (e i)) => padVec G e i a (Fin.castLE (hP.len_le_ansLen i) k)) =
      a := by
    funext k
    show (if h : k.val < G.len (e i) then a ⟨k.val, h⟩ else false) = a k
    rw [dite_eq_left k.isLt]
  rw [hU, ha]
  rfl

/-- **The padded strategy has the strategy's value**, on a game with no weight on its loops. -/
theorem value_padStrategy (hloop : ∀ x, G.μ x x = 0) (S : Tailored.PermStrategy G) :
    (hP.padStrategy S).value = S.value := by
  unfold TailoredGameValue.PermStrategy.value Tailored.PermStrategy.value
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  symm
  refine Fintype.sum_of_injective (padVec G e i) (hP.padVec_injective i) _ _ (fun a ha => ?_)
    fun a => ?_
  · obtain ⟨k, hk, hak⟩ := hP.exists_of_not_mem_range i a ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hP.proj_padStrategy_eq_zero S i a k hk hak, zero_mul, Matrix.trace_zero, Complex.zero_re,
      zero_div, mul_zero]
  refine Fintype.sum_of_injective (padVec G e j) (hP.padVec_injective j) _ _ (fun b hb => ?_)
    fun b => ?_
  · obtain ⟨k, hk, hbk⟩ := hP.exists_of_not_mem_range j b hb
    rw [hP.proj_padStrategy_eq_zero S j b k hk hbk, mul_zero, Matrix.trace_zero, Complex.zero_re,
      zero_div, mul_zero]
  rw [hP.proj_padStrategy, hP.proj_padStrategy, hP.μ_eq]
  by_cases hμ : G.μ (e i) (e j) = 0
  · simp [hμ]
  have hij : i ≠ j := by
    rintro rfl
    exact hμ (hloop _)
  have hacc : g.toGame.D i j (padVec G e i a) (padVec G e j b) = true ↔
      G.Accepts (e i) (e j) (List.ofFn a) (List.ofFn b) := by
    show decide _ = true ↔ _
    rw [decide_eq_true_iff, hP.accepts_iff i j _ _ (hP.wellFormatted_padVec i a)
      (hP.wellFormatted_padVec j b), hP.full_padVec, hP.full_padVec]
    exact ⟨fun h => h.2, fun h => ⟨fun h' => absurd h' hij, h⟩⟩
  by_cases hA : G.Accepts (e i) (e j) (List.ofFn a) (List.ofFn b)
  · rw [ite_eq_left hA, ite_eq_left (hacc.2 hA)]
    rfl
  · rw [ite_eq_right hA, ite_eq_right (mt hacc.1 hA)]
    rfl

/-- **A perfect ZPC strategy of a game with no weight on its loops is one of a presentation.** -/
theorem hasPerfectZPC (hloop : ∀ x, G.μ x x = 0) (h : G.HasPerfectZPC) : g.HasPerfectZPC := by
  obtain ⟨S, hS⟩ := h
  exact ⟨hP.padStrategy S, (hP.value_padStrategy hloop S).trans hS⟩

end Presents

end Tailored

end MIPRE

end
