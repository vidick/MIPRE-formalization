/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingProgBits

/-! # Bit-list query formulas for the numbered detyping sampler

These identities connect the semantic CL construction to the executable
router's graph-prefix and content-suffix operations. Prefix validity for
forwarded content queries is derived from the original numbered prefix.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Finset Classical

variable {T : Type*} [Fintype T] [DecidableEq T]

set_option linter.unusedSectionVars false

theorem toBits_zero (s : ℕ) : toBits (0 : Fin s → 𝔽₂) = List.replicate s false := by
  simp [toBits]

theorem graphBits_zero : graphBits (0 : Graph.Coord T → 𝔽₂) = List.replicate (graphDim T) false := by
  simp [graphBits, toBits_zero]

theorem graph_part_ofBits {s : ℕ} (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
    pull .inl (pull (registerEquiv s).toEmbedding (ofBits (graphDim T + s) z)) =
      graphOfBits (z.take (graphDim T)) := by
  rw [← graphOfBits_take s, toBits_ofBits hz]

theorem content_part_ofBits {s : ℕ} (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
    pull .inr (pull (registerEquiv s).toEmbedding (ofBits (graphDim T + s) z)) =
      ofBits s (z.drop (graphDim T)) := by
  rw [← ofBits_drop s, toBits_ofBits hz]

theorem toBits_register_graph (s : ℕ) (g : Graph.Coord T → 𝔽₂) :
    toBits (push (registerEquiv s).toEmbedding (push .inl g)) =
      graphBits g ++ List.replicate s false := by
  rw [toBits_register, pull_push]
  have h : pull (Function.Embedding.inr (α := Graph.Coord T)) (push .inl g) = (0 : Fin s → 𝔽₂) := by
    funext i; simp [pull]
  rw [h, toBits_zero]

theorem toBits_register_content (s : ℕ) (v : Fin s → 𝔽₂) :
    toBits (push (registerEquiv (T := T) s).toEmbedding (push .inr v)) =
      List.replicate (graphDim T) false ++ toBits v := by
  rw [toBits_register, pull_push]
  have h : pull (Function.Embedding.inl (β := Fin s)) (push .inr v) = (0 : Graph.Coord T → 𝔽₂) := by
    funext i; simp [pull]
  rw [h, graphBits_zero]

/-- Through the first two levels only graph bits are nonzero. -/
theorem numbered_marginal_graph {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (j : ℕ) (hj : j ≤ 2)
    (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
    toBits (((numbered E w P).truncate j).eval (ofBits (graphDim T + s) z)) =
      graphBits (((Graph.presentation E w.toBool).truncate j).eval
        (graphOfBits (z.take (graphDim T)))) ++ List.replicate s false := by
  rw [numbered, CLFun.eval_truncate_embed, marginal_graph E w.toBool P j hj,
    toBits_register_graph, graph_part_ofBits z hz]

/-- Later marginals append the selected typed marginal to the complete graph view. -/
theorem numbered_marginal_content {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (r : ℕ) (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
    toBits (((numbered E w P).truncate (r + 2)).eval (ofBits (graphDim T + s) z)) =
      graphBits ((Graph.presentation E w.toBool).eval (graphOfBits (z.take (graphDim T)))) ++
        toBits (((selected P (select E w.toBool (graphOfBits (z.take (graphDim T))))).truncate r).eval
          (ofBits s (z.drop (graphDim T)))) := by
  rw [numbered, CLFun.eval_truncate_embed, marginal_content E w.toBool P hP hℓ r,
    toBits_register]
  rw [graph_part_ofBits z hz, content_part_ofBits z hz]
  rfl

/-- Graph-level linear queries append a zero content block. -/
theorem numbered_linear_graph {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (k : ℕ) (hk : k < 2)
    (u y : Cost.BitStr) (hu : u.length = graphDim T + s) (hy : y.length = graphDim T + s) :
    toBits ((numbered E w P).mapOfPrefix k (ofBits (graphDim T + s) u) (ofBits (graphDim T + s) y)) =
      graphBits ((Graph.presentation E w.toBool).mapOfPrefix k
        (graphOfBits (u.take (graphDim T))) (graphOfBits (y.take (graphDim T)))) ++
        List.replicate s false := by
  have h : ∀ x z : Coord T (Fin s) → 𝔽₂,
      (presentation E w.toBool P).mapOfPrefix k x z =
        push .inl ((Graph.presentation E w.toBool).mapOfPrefix k (pull .inl x) (pull .inl z)) := by
    intro x z
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact linear_first E w.toBool P x z
    · exact linear_second E w.toBool P x z
  rw [numbered, CLFun.mapOfPrefix_embed, h, toBits_register_graph,
    graph_part_ofBits u hu, graph_part_ofBits y hy]

/-- Content-level linear queries prepend a zero graph block. -/
theorem numbered_linear_content {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (r : ℕ)
    (u y : Cost.BitStr) (hu : u.length = graphDim T + s) (hy : y.length = graphDim T + s) :
    toBits ((numbered E w P).mapOfPrefix (r + 2)
      (ofBits (graphDim T + s) u) (ofBits (graphDim T + s) y)) =
      List.replicate (graphDim T) false ++
        toBits ((selected P (select E w.toBool (graphOfBits (u.take (graphDim T))))).mapOfPrefix r
          (ofBits s (u.drop (graphDim T))) (ofBits s (y.drop (graphDim T)))) := by
  rw [numbered, CLFun.mapOfPrefix_embed, linear_content, toBits_register_content,
    graph_part_ofBits u hu, content_part_ofBits u hu, content_part_ofBits y hy]

private def indicatorVec {ι : Type*} [DecidableEq ι] (S : Finset ι) : ι → 𝔽₂ :=
  fun i => if i ∈ S then 1 else 0

private theorem toBits_indicator_equiv {ι : Type*} [DecidableEq ι] {s : ℕ}
    (e : ι ≃ Fin s) (S : Finset ι) :
    toBits (push e.toEmbedding (indicatorVec S)) = indicatorBits (S.map e.toEmbedding) := by
  unfold toBits indicatorBits
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  have hp := push_apply e.toEmbedding (indicatorVec S) j
  change push e.toEmbedding (indicatorVec S) (e j) = _ at hp
  rw [hp]
  simp [indicatorVec]

theorem indicatorBits_register_graph {s : ℕ} (S : Finset (Graph.Coord T)) :
    indicatorBits ((S.map (Function.Embedding.inl (β := Fin s))).map (registerEquiv s).toEmbedding) =
      indicatorBits (S.map graphEquiv.toEmbedding) ++ List.replicate s false := by
  rw [← toBits_indicator_equiv (registerEquiv s)]
  have h : indicatorVec (S.map (Function.Embedding.inl (β := Fin s))) =
      push .inl (indicatorVec S) := by
    funext q; cases q <;> simp [indicatorVec]
  rw [h, toBits_register_graph]
  congr 1
  exact toBits_indicator_equiv graphEquiv S

theorem indicatorBits_register_content {s : ℕ} (S : Finset (Fin s)) :
    indicatorBits ((S.map (Function.Embedding.inr (α := Graph.Coord T))).map (registerEquiv s).toEmbedding) =
      List.replicate (graphDim T) false ++ indicatorBits S := by
  rw [← toBits_indicator_equiv (registerEquiv s)]
  have h : indicatorVec (S.map (Function.Embedding.inr (α := Graph.Coord T))) =
      push .inr (indicatorVec S) := by
    funext q; cases q <;> simp [indicatorVec]
  rw [h, toBits_register_content]
  congr 1
  unfold toBits indicatorBits
  congr 1
  funext i
  simp [indicatorVec]

/-- Graph factors append zero membership bits for the content register. -/
theorem numbered_factor_graph {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (k : ℕ) (hk : k < 2)
    (u : Cost.BitStr) (hu : u.length = graphDim T + s) :
    indicatorBits ((numbered E w P).factorOfPrefix k (ofBits (graphDim T + s) u)) =
      indicatorBits (((Graph.presentation E w.toBool).factorOfPrefix k
        (graphOfBits (u.take (graphDim T)))).map graphEquiv.toEmbedding) ++ List.replicate s false := by
  have h : ∀ x : Coord T (Fin s) → 𝔽₂,
      (presentation E w.toBool P).factorOfPrefix k x =
        ((Graph.presentation E w.toBool).factorOfPrefix k (pull .inl x)).map Function.Embedding.inl := by
    intro x
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl
  rw [numbered, CLFun.factorOfPrefix_embed, h, indicatorBits_register_graph, graph_part_ofBits u hu]

/-- Content factors prepend zero membership bits for the graph register. -/
theorem numbered_factor_content {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (r : ℕ)
    (u : Cost.BitStr) (hu : u.length = graphDim T + s) :
    indicatorBits ((numbered E w P).factorOfPrefix (r + 2) (ofBits (graphDim T + s) u)) =
      List.replicate (graphDim T) false ++
        indicatorBits ((selected P (select E w.toBool (graphOfBits (u.take (graphDim T))))).factorOfPrefix r
          (ofBits s (u.drop (graphDim T)))) := by
  rw [numbered, CLFun.factorOfPrefix_embed, factor_content, indicatorBits_register_content,
    graph_part_ofBits u hu, content_part_ofBits u hu]

private theorem take_graph_append (g : Graph.Coord T → 𝔽₂) (v : Cost.BitStr) :
    (graphBits g ++ v).take (graphDim T) = graphBits g := by
  rw [← length_graphBits g, List.take_left]

private theorem drop_graph_append (g : Graph.Coord T → 𝔽₂) (v : Cost.BitStr) :
    (graphBits g ++ v).drop (graphDim T) = v := by
  rw [← length_graphBits g, List.drop_left]

/-- A selected type receives a prefix that is valid for the original typed sampler. -/
theorem numbered_selected_prefix {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (r : ℕ) (hr : 1 ≤ r) (u : Cost.BitStr)
    (hu : ∃ x, u = toBits (((numbered E w P).truncate (r + 1)).eval x))
    {t : T} (ht : select E w.toBool (graphOfBits (u.take (graphDim T))) = some t) :
    ∃ v, u.drop (graphDim T) = toBits (((P t).truncate (r - 1)).eval v) := by
  obtain ⟨x, rfl⟩ := hu
  have hi : r - 1 + 2 = r + 1 := by omega
  have hm := numbered_marginal_content E w P hP hℓ (r - 1) (toBits x) (length_toBits x)
  rw [ofBits_toBits, hi] at hm
  rw [hm] at ht ⊢
  simp only [take_graph_append, graphOfBits_graphBits, select_output] at ht
  refine ⟨ofBits s ((toBits x).drop (graphDim T)), ?_⟩
  rw [drop_graph_append, ht]
  rfl

end MIPRE.CL.Detyping
