/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Sofic.AssocValue

@[expose] public section

/-!
# Checks 1–3 fail only where a challenge fails

For a finite action `σ` and a question pair `(x, y)`, `npass σ x y` is the number of points whose
stabilizer fails the challenge at `(x, y)`. Each relation of Checks 1–3 among `J` and the
variables at `x` and at `y` (I:2086) fails at no more points than that: `J` fixes a point, `J²`
moves it, `J` and `X` do not commute at it, `X²` moves it, two variables at one vertex do not
commute at it, or a readable variable `X` moves it while `J X` moves it too.
-/

namespace MIPRE.Tailored.Sofic

open SubgroupTestValue TailoredGameValue Finset FiniteActionLemmas

variable {g : TailoredGameData} {n : ℕ} (σ : FiniteAction n)

/-- The number of points failing the challenge at `(x, y)`. -/
def npass (g : TailoredGameData) (x y : ℕ) : ℕ :=
  (univ.filter fun q => ¬σ.Passes (words g x y) (clauses g x y) q).card

private theorem card_le_npass {x y : ℕ} (P : Fin σ.N → Prop) [DecidablePred P]
    (h : ∀ q, σ.Passes (words g x y) (clauses g x y) q → P q) :
    (univ.filter fun q => ¬P q).card ≤ npass σ g x y := by
  unfold npass
  refine card_le_card ?_
  intro q
  simp only [mem_filter, mem_univ, true_and]
  exact fun hP hq => hP (h q hq)

private theorem inStab_of_fixed {x y : ℕ} {q : Fin σ.N}
    (h : σ.Passes (words g x y) (clauses g x y) q) {w : Word} (hw : (w, true) ∈ fixedLits g x y) :
    σ.wordPerm w q = q := by
  have := fixed_of_passes σ h hw
  simpa [FiniteAction.InStab] using this

private theorem mem_vars {x y z i : ℕ} (hz : z = x ∨ z = y) (hi : i < g.lenAt z) :
    wX g z i ∈ varsAt g x ++ varsAt g y := by
  have : wX g z i ∈ varsAt g z := List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  rcases hz with rfl | rfl
  · exact List.mem_append_left _ this
  · exact List.mem_append_right _ this

theorem card_J_fixed_le (g : TailoredGameData) (x y : ℕ) :
    (univ.filter fun q => genPerm σ genJ q = q).card ≤ npass σ g x y := by
  have := card_le_npass σ (g := g) (x := x) (y := y) (fun q => genPerm σ genJ q ≠ q) (by
    intro q hq
    have h := fixed_of_passes σ hq (wb := (wJ, false)) (by simp [fixedLits])
    simpa [FiniteAction.InStab, wJ, wordPerm_genW] using h)
  simpa using this

theorem card_J_sq_le (g : TailoredGameData) (x y : ℕ) :
    (univ.filter fun q => genPerm σ genJ (genPerm σ genJ q) ≠ q).card ≤ npass σ g x y :=
  card_le_npass σ (g := g) _ (by
    intro q hq
    have h := inStab_of_fixed σ hq (w := wJ ++ wJ) (by simp [fixedLits])
    simpa [wJ, wordPerm_append, wordPerm_genW] using h)

theorem card_JX_le {x y z i : ℕ} (hz : z = x ∨ z = y) (hi : i < g.lenAt z) :
    (univ.filter fun q => genPerm σ genJ (genPerm σ (genX g z i) q) ≠
      genPerm σ (genX g z i) (genPerm σ genJ q)).card ≤ npass σ g x y := by
  rw [← card_commutator_moves]
  refine card_le_npass σ _ (fun q hq => ?_)
  have hmem : (commW wJ (wX g z i), true) ∈ fixedLits g x y := by
    unfold fixedLits
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map_of_mem (f := fun X => (commW wJ X, true))
        (mem_vars hz hi)))))
  have h := inStab_of_fixed σ hq hmem
  rw [wordPerm_commW] at h
  simpa [wJ, wX, wordPerm_genW] using h

theorem card_X_sq_le {x y z i : ℕ} (hz : z = x ∨ z = y) (hi : i < g.lenAt z) :
    (univ.filter fun q => genPerm σ (genX g z i) (genPerm σ (genX g z i) q) ≠ q).card ≤
      npass σ g x y :=
  card_le_npass σ _ (by
    intro q hq
    have hmem : (wX g z i ++ wX g z i, true) ∈ fixedLits g x y := by
      unfold fixedLits
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map_of_mem (f := fun X => (X ++ X, true))
          (mem_vars hz hi))))
    have h := inStab_of_fixed σ hq hmem
    simpa [wX, wordPerm_append, wordPerm_genW] using h)

theorem card_XX_le {x y z i j : ℕ} (hz : z = x ∨ z = y) (hi : i < g.lenAt z)
    (hj : j < g.lenAt z) :
    (univ.filter fun q => genPerm σ (genX g z i) (genPerm σ (genX g z j) q) ≠
      genPerm σ (genX g z j) (genPerm σ (genX g z i) q)).card ≤ npass σ g x y := by
  rw [← card_commutator_moves]
  refine card_le_npass σ _ (fun q hq => ?_)
  have hi' : wX g z i ∈ varsAt g z := List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hj' : wX g z j ∈ varsAt g z := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have hmem : (commW (wX g z i) (wX g z j), true) ∈ fixedLits g x y := by
    have hz' : (commW (wX g z i) (wX g z j), true) ∈
        (varsAt g z).flatMap (fun X => (varsAt g z).map fun X' => (commW X X', true)) :=
      List.mem_flatMap.mpr ⟨_, hi', List.mem_map_of_mem (f := fun X' => (commW _ X', true)) hj'⟩
    unfold fixedLits
    rcases hz with rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_right _ hz')
    · exact List.mem_append_right _ hz'
  have h := inStab_of_fixed σ hq hmem
  rw [wordPerm_commW] at h
  simpa [wX, wordPerm_genW] using h

theorem card_read_le {x y z i : ℕ} (hz : z = x ∨ z = y) (hi : i < g.lenRAt z) :
    (univ.filter fun q => ¬(genPerm σ (genX g z i) q = q ∨
      genPerm σ genJ (genPerm σ (genX g z i) q) = q)).card ≤ npass σ g x y :=
  card_le_npass σ _ (by
    intro q hq
    have hmem : wX g z i ∈ readVars g x y := by
      have : wX g z i ∈ (List.range (g.lenRAt z)).map (wX g z) :=
        List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
      unfold readVars
      rcases hz with rfl | rfl
      · exact List.mem_append_left _ this
      · exact List.mem_append_right _ this
    have h := read_of_passes σ hq hmem
    simpa [FiniteAction.InStab, wJ, wX, wordPerm_append, wordPerm_genW] using h)

end MIPRE.Tailored.Sofic

end
