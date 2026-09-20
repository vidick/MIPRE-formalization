/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-! # The two-level graph sampler

The graph may have loops. Its law is uniform on ordered adjacent pairs, so each
loop is counted once. This file supplies the semantic CL presentations; compiling
their finite graph table into an ambient sampler program is a separate obligation.
-/

noncomputable section

namespace MIPRE.CL.Graph

open Finset Classical

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Four binary blocks: player, vertex/neighbor indicator, vertex. -/
abbrev Coord (T : Type*) := Bool × (Bool × T)

/-- A vertex's one-hot indicator together with its neighbor indicator. -/
def encode (E : T → T → Prop) [DecidableRel E] (u : T) : Bool × T → ZMod 2 :=
  fun p => if p.1 then (if E u p.2 then 1 else 0) else (if p.2 = u then 1 else 0)

/-- The one-hot half makes the encoding injective, even for an isolated vertex. -/
theorem encode_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (encode E) := by
  intro u v h
  have hh := congrFun h (false, u)
  by_contra huv
  simpa [encode, huv] using hh

/-- Decode the finite graph table; malformed blocks have no decoded vertex. -/
def decode (E : T → T → Prop) [DecidableRel E] (x : Bool × T → ZMod 2) : Option T :=
  if h : ∃ u, x = encode E u then some h.choose else none

/-- Successful decoding means equality with the whole vertex-and-neighbor encoding. -/
theorem decode_eq_some_iff (E : T → T → Prop) [DecidableRel E]
    (x : Bool × T → ZMod 2) (u : T) : decode E x = some u ↔ x = encode E u := by
  unfold decode
  split_ifs with h
  · constructor
    · intro he
      have hc := Option.some.inj he
      exact h.choose_spec.trans (congrArg (encode E) hc)
    · intro hx
      congr 1
      exact encode_injective E (h.choose_spec.symm.trans hx)
  · constructor
    · intro he
      cases he
    · intro hx
      exact False.elim (h ⟨u, hx⟩)

/-- The first factor consists of the two blocks belonging to one player. -/
def own (w : Bool) : Finset (Coord T) := univ.filter fun p => p.1 = w

@[simp] theorem mem_own (w : Bool) (p : Coord T) : p ∈ own w ↔ p.1 = w := by
  simp [own]

/-- The second stage keeps just the relevant opposite neighbor bit when decoding succeeds. -/
def mask (E : T → T → Prop) [DecidableRel E] (w : Bool) (x : Coord T → ZMod 2) :
    Finset (Coord T) :=
  match decode E (fun p => x (w, p)) with
  | some u => {(!w, (true, u))}
  | none => ∅

/-- The second-stage mask is contained in the complement of the first factor. -/
theorem mask_subset (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (x : Coord T → ZMod 2) : mask E w x ⊆ (own w)ᶜ := by
  unfold mask
  split
  · intro p hp
    simp only [mem_singleton] at hp
    subst p
    simp
  · exact empty_subset _

/-- The graph sampler's second-stage linear map, on the entire remaining factor. -/
def second (E : T → T → Prop) [DecidableRel E] (w : Bool) (x : Coord T → ZMod 2) :
    RegLinear (ZMod 2) (own (T := T) w)ᶜ where
  toLinearMap := proj (mask E w x)
  proj_comp_proj' z := by
    rw [proj_proj_of_subset (mask_subset E w x), proj_proj_of_subset' (mask_subset E w x)]

/-- The actual two-level CL presentation: own blocks, then one opposite neighbor bit. -/
def presentation (E : T → T → Prop) [DecidableRel E] (w : Bool) :
    CLFun (ZMod 2) (Coord T) 2 :=
  .cons (own w) (RegLinear.id (own w)) fun x =>
    .cons (own w)ᶜ (second E w x) fun _ => .zero

/-- Its two factors partition all four blocks on every prefix, valid or otherwise. -/
theorem presentation_exactlyOn (E : T → T → Prop) [DecidableRel E] (w : Bool) :
    (presentation E w).ExactlyOn univ := by
  simp [presentation, CLFun.ExactlyOn, Finset.compl_eq_univ_sdiff]

/-- Projecting onto one's own first-stage block does not affect decoding. -/
theorem mask_proj_own (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) : mask E w (proj (own w) z) = mask E w z := by
  unfold mask
  have he : (fun p => proj (own w) z (w, p)) = fun p => z (w, p) := by
    funext p
    simp
  rw [he]

/-- The semantic output is the own block plus the selected opposite neighbor bit. -/
theorem presentation_eval (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) :
    (presentation E w).eval z = proj (own w) z + proj (mask E w z) z := by
  simp only [presentation, CLFun.eval_cons, CLFun.eval_zero, add_zero, RegLinear.id_apply]
  change _ + proj (mask E w (proj (own w) z)) (proj (own w)ᶜ z) = _
  rw [mask_proj_own, proj_proj_of_subset (mask_subset E w z)]

/-- A player sees its entire own block unchanged. -/
theorem presentation_eval_own (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) (p : Bool × T) :
    (presentation E w).eval z (w, p) = z (w, p) := by
  have hn : (w, p) ∉ mask E w z := by
    intro hh
    have := mask_subset E w z hh
    simpa using this
  rw [presentation_eval]
  simp [proj_apply, hn]

/-- On an encoded first-stage block, the selected opposite neighbor bit is visible unchanged. -/
theorem presentation_eval_bit (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) {u : T} (hu : (fun p => z (w, p)) = encode E u) :
    (presentation E w).eval z (!w, (true, u)) = z (!w, (true, u)) := by
  have hd := (decode_eq_some_iff E _ u).mpr hu
  rw [presentation_eval]
  simp [proj_apply, mask, hd]

/-- The local valid-view predicate, stated on the seed before applying the graph sampler. -/
def localValid (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) : Prop :=
  ∃ u, (fun p => z (w, p)) = encode E u ∧ z (!w, (true, u)) = 1

/-- Validity can be decided from the local sampled question, with no access to the seed. -/
theorem localValid_output_iff (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) :
    localValid E w ((presentation E w).eval z) ↔ localValid E w z := by
  have hown : (fun p => (presentation E w).eval z (w, p)) = fun p => z (w, p) := by
    funext p
    exact presentation_eval_own E w z p
  unfold localValid
  rw [hown]
  constructor <;> rintro ⟨u, hu, hbit⟩ <;> refine ⟨u, hu, ?_⟩
  · rwa [presentation_eval_bit E w z hu] at hbit
  · rwa [presentation_eval_bit E w z hu]

/-- The opposite part of the sampled question contains exactly the selected bit. -/
theorem opposite_output (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) :
    proj (own w)ᶜ ((presentation E w).eval z) = proj (mask E w z) z := by
  rw [presentation_eval, map_add, proj_proj_of_disjoint disjoint_compl_left, zero_add,
    proj_proj_of_subset' (mask_subset E w z)]

/-- An invalid local view has zero opposite-neighbor block, as required for PCC detyping. -/
theorem opposite_output_zero_of_invalid (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) (h : ¬localValid E w z) :
    proj (own w)ᶜ ((presentation E w).eval z) = 0 := by
  rw [opposite_output]
  cases hd : decode E (fun p => z (w, p)) with
  | none => simp [mask, hd, proj_empty]
  | some u =>
    have hu := (decode_eq_some_iff E _ u).mp hd
    have hb : z (!w, (true, u)) = 0 := by
      have hbit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
      exact (hbit _).resolve_right fun hb => h ⟨u, hu, hb⟩
    funext p
    by_cases hp : p = (!w, (true, u))
    · subst p
      simp [mask, hd, proj_apply, hb]
    · simp [mask, hd, proj_apply, hp]

/-- A seed encoding a pair of types. Each ordered pair has precisely this one seed. -/
def pairSeed (E : T → T → Prop) [DecidableRel E] (uv : T × T) : Coord T → ZMod 2 :=
  fun p => encode E (if p.1 then uv.2 else uv.1) p.2

/-- Encoding an ordered pair is injective. -/
theorem pairSeed_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (pairSeed E) := by
  intro uv uv' h
  apply Prod.ext
  · apply encode_injective E
    funext p
    exact congrFun h (false, p)
  · apply encode_injective E
    funext p
    exact congrFun h (true, p)

/-- Both local valid views are exactly the encodings of adjacent ordered pairs. -/
theorem localValid_both_iff (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (z : Coord T → ZMod 2) :
    localValid E false z ∧ localValid E true z ↔
      ∃ uv : T × T, E uv.1 uv.2 ∧ z = pairSeed E uv := by
  constructor
  · rintro ⟨⟨u, hu, hbit⟩, ⟨v, hv, _⟩⟩
    have hbits := congrFun hv (true, u)
    have hEvu : E v u := by
      by_contra hh
      simp [encode, hh] at hbits
      simp only [Bool.not_false] at hbit
      rw [hbit] at hbits
      exact one_ne_zero hbits
    refine ⟨(u, v), hE v u hEvu, ?_⟩
    funext p
    rcases p with ⟨w, p⟩
    cases w
    · exact congrFun hu p
    · exact congrFun hv p
  · rintro ⟨⟨u, v⟩, huv, rfl⟩
    constructor
    · exact ⟨u, rfl, by simp [pairSeed, encode, hE u v huv]⟩
    · exact ⟨v, rfl, by simp [pairSeed, encode, huv]⟩

/-- Ordered edges; a loop contributes once. -/
def edges (E : T → T → Prop) [DecidableRel E] : Finset (T × T) :=
  univ.filter fun p => E p.1 p.2

/-- The valid seeds, expressed as an image so their exact number is transparent. -/
def validSeeds (E : T → T → Prop) [DecidableRel E] : Finset (Coord T → ZMod 2) :=
  (edges E).image (pairSeed E)

/-- The rejection event has exactly one seed per ordered edge. -/
theorem card_validSeeds (E : T → T → Prop) [DecidableRel E] :
    (validSeeds E).card = (edges E).card :=
  Finset.card_image_of_injective _ (pairSeed_injective E)

/-- The rejection event is the event that both players have valid local views. -/
theorem mem_validSeeds_iff (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (z : Coord T → ZMod 2) :
    z ∈ validSeeds E ↔ localValid E false z ∧ localValid E true z := by
  rw [localValid_both_iff E hE]
  simp only [validSeeds, Finset.mem_image, edges, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor <;> rintro ⟨uv, hu, hz⟩ <;> exact ⟨uv, hu, hz.symm⟩

/-- On every rejected seed, at least one player recognizes an invalid local question. -/
theorem invalid_seed_locally_detected (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (z : Coord T → ZMod 2) :
    z ∉ validSeeds E ↔
      ¬localValid E false ((presentation E false).eval z) ∨
      ¬localValid E true ((presentation E true).eval z) := by
  rw [mem_validSeeds_iff E hE, localValid_output_iff, localValid_output_iff, not_and_or]

/-- The four binary blocks have `16 ^ |T|` seeds. -/
theorem card_seeds : Fintype.card (Coord T → ZMod 2) = 16 ^ Fintype.card T := by
  simp only [Fintype.card_fun, ZMod.card, Coord, Fintype.card_prod, Fintype.card_bool]
  rw [← mul_assoc, pow_mul]
  norm_num

/-- Uniform averaging on valid seeds is uniform averaging on ordered edges, without multiplicity. -/
theorem sum_validSeeds {M : Type*} [AddCommMonoid M]
    (E : T → T → Prop) [DecidableRel E] (f : (Coord T → ZMod 2) → M) :
    ∑ z ∈ validSeeds E, f z = ∑ uv ∈ edges E, f (pairSeed E uv) := by
  exact Finset.sum_image (fun _ _ _ _ h => pairSeed_injective E h)

/-- The probability of the valid-edge event under the uniform binary seed. -/
def validProbability (E : T → T → Prop) [DecidableRel E] : ℝ :=
  (validSeeds E).card / Fintype.card (Coord T → ZMod 2)

/-- Exact rejection probability, with loops counted once among the ordered edges. -/
theorem validProbability_eq (E : T → T → Prop) [DecidableRel E] :
    validProbability E = (edges E).card / (16 : ℝ) ^ Fintype.card T := by
  simp only [validProbability, card_validSeeds, card_seeds, Nat.cast_pow, Nat.cast_ofNat]

/-- A graph with an edge has acceptance probability at least `16 ^ (-|T|)`. -/
theorem inv_pow_le_validProbability (E : T → T → Prop) [DecidableRel E]
    (hne : (edges E).Nonempty) :
    ((16 : ℝ) ^ Fintype.card T)⁻¹ ≤ validProbability E := by
  rw [validProbability_eq, ← one_div]
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by norm_num) _)
  exact_mod_cast hne.card_pos

/-- Conditioning uniform seeds on acceptance gives the uniform ordered-edge law. -/
theorem conditional_average (E : T → T → Prop) [DecidableRel E]
    (f : (Coord T → ZMod 2) → ℝ) :
    (∑ z ∈ validSeeds E, f z) / (validSeeds E).card =
      (∑ uv ∈ edges E, f (pairSeed E uv)) / (edges E).card := by
  rw [sum_validSeeds, card_validSeeds]

end MIPRE.CL.Graph

end
