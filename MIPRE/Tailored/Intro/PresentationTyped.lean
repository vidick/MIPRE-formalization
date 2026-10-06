/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Presentation
public import MIPRE.Foundations.CL.DetypingComplete

@[expose] public section

/-!
# Completeness of a presentation from a typed strategy

`hasPerfectZPC_presented` takes a perfect PCC strategy of the detyped game. The detyped game of
this repository is `CL.Detyping.game`, and its perfect PCC strategies come from typed ones by
`CL.Detyping.complete`: the typed measurement at the question a view decodes to, and the
measurement concentrated on a fixed answer `a₀` off the decodable views. Its bit observables
along the encoding are those of the typed measurement at decodable views, and there are none
elsewhere (the detyped tailored game has no answer bits there). So the hypotheses of
`hasPerfectZPC_presented` reduce to typed ones (`hasPerfectZPC_presented_typed`).
-/

namespace MIPRE.Tailored

open Cost MIPRE.CL MIPRE.CL.Detyping Classical

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  (E : T → T → Prop) [DecidableRel E] {B ℓ : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem decodeQuestion_eq_some {x : Coord T ι → ZMod 2} {w : Bool} {q : Question T ι}
    (h : decodeQuestion E x = some (w, q)) : typeOf E x = some q.1 ∧ q.2 = pull .inr x := by
  unfold decodeQuestion at h
  unfold typeOf
  cases hd : decodeView E (pull .inl x) with
  | none => simp [hd] at h
  | some wu =>
    simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem decodeQuestion_eq_none {x : Coord T ι → ZMod 2} (h : decodeQuestion E x = none) :
    typeOf E x = none := by
  unfold decodeQuestion at h
  unfold typeOf
  cases hd : decodeView E (pull .inl x) with
  | none => rfl
  | some wu => simp [hd] at h

variable (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
  (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn Finset.univ) (hℓ : 0 < ℓ)
  (Dt : Question T ι → Question T ι → Verifier.Answers B → Verifier.Answers B → Bool)
  (D : TypedData T ι)

include hE hP hℓ in
/-- **Completeness of the presentation from a typed strategy.** -/
theorem hasPerfectZPC_presented_typed
    (encT : Question T ι → Verifier.Answers B → BitStr)
    (okT : Question T ι → Verifier.Answers B → Prop) (a₀ : Verifier.Answers B)
    (hlen : ∀ u a, okT u a → (encT u a).length = D.lenR u.1 + D.lenL u.1)
    (h : ∀ u v a b, E u.1 v.1 → okT u a → okT v b → Dt u v a b = true →
      D.Accepts u v (encT u a) (encT v b))
    (R : SyncStrategy (typedGame E hne P Dt).doubled) (hR : R.IsPCC) (hval : R.value = 1)
    (hsupp : ∀ q a, ¬okT q.2 a → R.P.M q a = 0)
    (hperm : ∀ q (i : ℕ), IsSignedPerm
      (pvmObs (R.P.M q) fun a => bitSign ((encT q.2 a).getD i false)))
    (hdiag : ∀ q (i : ℕ), i < D.lenR q.2.1 →
      (pvmObs (R.P.M q) fun a => bitSign ((encT q.2 a).getD i false)).IsDiag) :
    (presented E (game E P Dt) D).doubled.HasPerfectZPC := by
  refine hasPerfectZPC_presented E (game E P Dt) Dt (fun _ _ _ _ => rfl) D a₀ hlen h
    (complete E hne P Dt R a₀) (complete_isPCC E hE hne P hP hℓ Dt R hR a₀)
    (complete_value E hE hne P hP hℓ Dt R hval a₀) ?_ ?_ ?_
  · rintro ⟨w, x⟩ a ha
    change (match decodeQuestion E x with
      | some q => R.P.M q a
      | none => if a = a₀ then 1 else 0) = 0
    cases hd : decodeQuestion E x with
    | none =>
      have ht := decodeQuestion_eq_none E hd
      have : a ≠ a₀ := fun hh => ha ⟨fun t htt => by simp [ht] at htt, fun _ => hh⟩
      simp [this]
    | some wq =>
      obtain ⟨w', q⟩ := wq
      obtain ⟨ht, hq⟩ := decodeQuestion_eq_some E hd
      apply hsupp
      intro hok
      apply ha
      refine ⟨fun t htt => ?_, fun hn => by simp [ht] at hn⟩
      rw [ht] at htt
      cases htt
      rw [← hq]
      exact hok
  · rintro ⟨w, x⟩ i
    have hi := i.2
    change (i : ℕ) < (presented E (game E P Dt) D).len x at hi
    cases hd : decodeQuestion E x with
    | none =>
      exfalso
      have ht := decodeQuestion_eq_none E hd
      have hl : (presented E (game E P Dt) D).len x = 0 := by
        simp [TailoredGame.len, TypedData.detype, ht]
      omega
    | some wq =>
      obtain ⟨w', q⟩ := wq
      obtain ⟨ht, hq⟩ := decodeQuestion_eq_some E hd
      have hM : (complete E hne P Dt R a₀).P.M (w, x) = R.P.M (w', q) := by
        funext a
        change (match decodeQuestion E x with
          | some q => R.P.M q a
          | none => if a = a₀ then 1 else 0) = _
        rw [hd]
      have e : encObs (R.P.M (w', q)) (encV E (game E P Dt) D encT x) i =
          pvmObs (R.P.M (w', q)) fun a => bitSign ((encT q a).getD i false) := by
        simp only [encObs, encV, vecOf, TypedData.encD, ht, ← hq]
      change IsSignedPerm (encObs ((complete E hne P Dt R a₀).P.M (w, x))
        (encV E (game E P Dt) D encT x) i)
      simp only [complete, hd]
      have h1 := hperm (w', q) i
      rw [← e] at h1
      exact h1
  · rintro ⟨w, x⟩ i hi
    have hi' := i.2
    change (i : ℕ) < (presented E (game E P Dt) D).len x at hi'
    change (i : ℕ) < (presented E (game E P Dt) D).lenR x at hi
    cases hd : decodeQuestion E x with
    | none =>
      exfalso
      have ht := decodeQuestion_eq_none E hd
      have hl : (presented E (game E P Dt) D).len x = 0 := by
        simp [TailoredGame.len, TypedData.detype, ht]
      omega
    | some wq =>
      obtain ⟨w', q⟩ := wq
      obtain ⟨ht, hq⟩ := decodeQuestion_eq_some E hd
      have hM : (complete E hne P Dt R a₀).P.M (w, x) = R.P.M (w', q) := by
        funext a
        change (match decodeQuestion E x with
          | some q => R.P.M q a
          | none => if a = a₀ then 1 else 0) = _
        rw [hd]
      have e : encObs (R.P.M (w', q)) (encV E (game E P Dt) D encT x) i =
          pvmObs (R.P.M (w', q)) fun a => bitSign ((encT q a).getD i false) := by
        simp only [encObs, encV, vecOf, TypedData.encD, ht, ← hq]
      have hr : (presented E (game E P Dt) D).lenR x = D.lenR q.1 := by
        simp [TypedData.detype, ht]
      change (encObs ((complete E hne P Dt R a₀).P.M (w, x))
        (encV E (game E P Dt) D encT x) i).IsDiag
      simp only [complete, hd]
      have h1 := hdiag (w', q) i (hr ▸ hi)
      rw [← e] at h1
      exact h1

end MIPRE.Tailored

end
