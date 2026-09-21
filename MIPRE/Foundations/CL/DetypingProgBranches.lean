/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgRoute
import MIPRE.Foundations.CL.TypedSampler

/-! # Correct query branches of the executable detyping router -/

noncomputable section

namespace MIPRE.CL.Detyping.Program

open Cost Cost.PolyTimeFun

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]

theorem route_query (n : ℕ) (q : Sampler.Query) :
    route E (encode (n, q)) =
      routeResult (graphDim T)
        (encode n, q.toTuple.1, q.toTuple.2.1.toBool, q.toTuple.2.2.1,
          q.toTuple.2.2.2.1, q.toTuple.2.2.2.2)
        (graphResult E (q.toTuple.2.1.toBool, decide (q.toTuple.2.2.1 = 1),
          ofBits (graphDim T) q.toTuple.2.2.2.1, ofBits (graphDim T) q.toTuple.2.2.2.2)) := by
  simp only [route, comp_apply, pair_apply, id_apply, parse_query, routeParsed_apply]
  rfl

theorem route_dimension (n : ℕ) :
    route E (encode (n, Sampler.Query.dimension)) =
      callResult (encode (n, (TypedSampler.Query.dimension : TypedSampler.Query T))) .nil := by
  rw [route_query]
  rfl

theorem route_marginal_early (n : ℕ) (w : Player) (j : ℕ) (z : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ 2) :
    route E (encode (n, Sampler.Query.marginal w j z)) =
      directResult (graphBits (((Graph.presentation E w.toBool).truncate j).eval (graphOfBits z)) ++
        pad false (content (graphDim T) z)) := by
  rw [route_query]
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> rfl

theorem route_linear_early (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ 2) :
    route E (encode (n, Sampler.Query.linear w j u y)) =
      directResult (graphBits ((Graph.presentation E w.toBool).mapOfPrefix (j - 1)
        (graphOfBits u) (graphOfBits y)) ++ pad false (content (graphDim T) y)) := by
  rw [route_query]
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> rfl

theorem route_factor_early (n : ℕ) (w : Player) (j : ℕ) (u : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ 2) :
    route E (encode (n, Sampler.Query.factor w j u)) =
      directResult (indicatorBits (((Graph.presentation E w.toBool).factorOfPrefix (j - 1)
        (graphOfBits u)).map graphEquiv.toEmbedding) ++ pad false (content (graphDim T) u)) := by
  rw [route_query]
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> rfl

theorem route_marginal_late (n : ℕ) (w : Player) (j : ℕ) (z : BitStr) (hj : 2 < j) :
    route E (encode (n, Sampler.Query.marginal w j z)) =
      match select E w.toBool (graphOfBits z) with
      | none => directResult (graphBits ((Graph.presentation E w.toBool).eval (graphOfBits z)) ++
          pad false (content (graphDim T) z))
      | some t => callResult
          (encode (n, TypedSampler.Query.atType t
            (Sampler.Query.marginal w (j - 2) (content (graphDim T) z))))
          (withPrefix (graphBits ((Graph.presentation E w.toBool).eval (graphOfBits z)))) := by
  rw [route_query]
  have hj1 : j ≠ 1 := by omega
  have hj2 : ¬j ≤ 2 := by omega
  simp only [routeResult, graphResult, Sampler.Query.toTuple, hj1, decide_false,
    Bool.false_eq_true, ↓reduceIte, hj2]
  change (if rawTruth (match select E w.toBool (graphOfBits z) with
      | none => Data.nil | some t => .cons (encode t) .nil) then _ else _) = _
  cases ht : select E w.toBool (graphOfBits z)
  all_goals simp only [graphOfBits] at ht
  all_goals simp only [ht, rawTruth, ↓reduceIte, Bool.false_eq_true,
    treeHead_cons]
  all_goals rfl

theorem route_linear_late (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr) (hj : 2 < j) :
    route E (encode (n, Sampler.Query.linear w j u y)) =
      match select E w.toBool (graphOfBits u) with
      | none => directResult (List.replicate (graphDim T) false ++ pad false (content (graphDim T) y))
      | some t => callResult
          (encode (n, TypedSampler.Query.atType t
            (Sampler.Query.linear w (j - 2) (content (graphDim T) u) (content (graphDim T) y))))
          (withPrefix (List.replicate (graphDim T) false)) := by
  rw [route_query]
  have hj1 : j ≠ 1 := by omega
  have hj2 : ¬j ≤ 2 := by omega
  simp only [routeResult, graphResult, Sampler.Query.toTuple, hj1, decide_false,
    Bool.false_eq_true, ↓reduceIte, hj2]
  change (if rawTruth (match select E w.toBool (graphOfBits u) with
      | none => Data.nil | some t => .cons (encode t) .nil) then _ else _) = _
  cases ht : select E w.toBool (graphOfBits u)
  all_goals simp only [graphOfBits] at ht
  all_goals simp only [ht, rawTruth, ↓reduceIte, Bool.false_eq_true, treeHead_cons]
  all_goals rfl

theorem route_factor_late (n : ℕ) (w : Player) (j : ℕ) (u : BitStr) (hj : 2 < j) :
    route E (encode (n, Sampler.Query.factor w j u)) =
      match select E w.toBool (graphOfBits u) with
      | none => directResult
          (List.replicate (graphDim T) false ++ pad (decide (j = 3)) (content (graphDim T) u))
      | some t => callResult
          (encode (n, TypedSampler.Query.atType t
            (Sampler.Query.factor w (j - 2) (content (graphDim T) u))))
          (withPrefix (List.replicate (graphDim T) false)) := by
  rw [route_query]
  have hj1 : j ≠ 1 := by omega
  have hj2 : ¬j ≤ 2 := by omega
  simp only [routeResult, graphResult, Sampler.Query.toTuple, hj1, decide_false,
    Bool.false_eq_true, ↓reduceIte, hj2]
  change (if rawTruth (match select E w.toBool (graphOfBits u) with
      | none => Data.nil | some t => .cons (encode t) .nil) then _ else _) = _
  cases ht : select E w.toBool (graphOfBits u)
  all_goals simp only [graphOfBits] at ht
  all_goals simp only [ht, rawTruth, ↓reduceIte, Bool.false_eq_true, treeHead_cons]
  all_goals rfl

theorem content_length {g s : ℕ} (z : BitStr) (hz : z.length = g + s) :
    (content g z).length = s := by simp [content, hz]

theorem pad_content {g s : ℕ} (b : Bool) (z : BitStr) (hz : z.length = g + s) :
    pad b (content g z) = List.replicate s b := by
  simp [pad, content_length z hz]

end MIPRE.CL.Detyping.Program
