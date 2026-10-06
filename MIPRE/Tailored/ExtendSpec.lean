/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Extend
public import MIPRE.Tailored.Verifier

@[expose] public section

/-!
# A tailored verifier extending a tailored game, from its programs

A tailored verifier `W` meets a tailored game `G` on `X` at an index `n` along an equivalence
`e : X ≃ 𝔽₂^{s(n)}` of the questions (`MeetsAt`) when its sampler's distribution is `G`'s weights
along `e`, and at every question `e x` its answer-length calculator outputs `G`'s lengths and its
linear-constraints processor `G`'s constraints. Then `W`'s `n`-th game extends `G` along `e`
(`MeetsAt.extends`), so it has `G`'s quantum value (`MeetsAt.valStar_eq`) and its perfect ZPC
strategies (`MeetsAt.hasPerfectZPC`).

This is the step from a game a stage presents to the output verifier of the stage, once the
output's programs are shown to compute the presented lengths and constraints: the introspection
stage proves it for its own presentation (`Intro.Output.extends_presented`), the answer
reduction through this generic form.
-/

namespace MIPRE.Tailored.TailoredVerifier

open Cost

variable {ℓ : ℕ} (W : TailoredVerifier ℓ) (n : ℕ) {X : Type*} [Fintype X]

theorem lenOf_eq_of_lenIs {x : BitStr} {κ : Bool} {k : ℕ} (h : LenIs W.len n x κ k) :
    W.lenOf n x κ = k := by
  have hex : ∃ m, LenIs W.len n x κ m := ⟨_, h⟩
  rw [TailoredVerifier.lenOf, dite_eq_left hex]
  exact hex.choose_spec.unique h

/-- **`W` meets `G` at `n` along `e`**: the sampler's distribution is `G`'s weights, and the two
programs output `G`'s lengths and constraints at the questions `e x`. -/
structure MeetsAt (G : TailoredGame X) (e : X ≃ W.Questions n) : Prop where
  dist_eq : ∀ x y, W.sampler.dist n (e x) (e y) = G.μ x y
  lenR_eq : ∀ x, LenIs W.len n (CL.toBits (e x)) false (G.lenR x)
  lenL_eq : ∀ x, LenIs W.len n (CL.toBits (e x)) true (G.lenL x)
  cons_eq : ∀ x y aR bR,
    LpIs W.lp n (CL.toBits (e x)) (CL.toBits (e y)) aR bR (G.cons x y aR bR)

namespace MeetsAt

variable {W n} {G : TailoredGame X} {e : X ≃ W.Questions n}

/-- **`W`'s `n`-th game extends `G` along `e`.** -/
theorem extends_ (h : W.MeetsAt n G e) : (W.tgame n).Extends G e.toEmbedding where
  μ_eq x y := h.dist_eq x y
  support x' y' _ := ⟨⟨_, e.apply_symm_apply x'⟩, ⟨_, e.apply_symm_apply y'⟩⟩
  lenR_eq x := W.lenOf_eq_of_lenIs n (h.lenR_eq x)
  lenL_eq x := W.lenOf_eq_of_lenIs n (h.lenL_eq x)
  cons_eq x y := by
    funext aR bR
    exact TailoredVerifier.consOf_eq_of _
      (fun κ => Bool.casesOn (motive := fun κ => ∃ k, LenIs W.len n _ κ k) κ
        ⟨_, h.lenR_eq x⟩ ⟨_, h.lenL_eq x⟩)
      (fun κ => Bool.casesOn (motive := fun κ => ∃ k, LenIs W.len n _ κ k) κ
        ⟨_, h.lenR_eq y⟩ ⟨_, h.lenL_eq y⟩) (h.cons_eq x y aR bR)

/-- **`W`'s `n`-th game has `G`'s quantum value.** -/
theorem valStar_eq (h : W.MeetsAt n G e) : W.valStar n = G.valStar :=
  h.extends_.valStar_eq

/-- **A perfect ZPC strategy of `G`'s doubled game gives one of `W`'s `n`-th game.** -/
theorem hasPerfectZPC (h : W.MeetsAt n G e) (hG : G.doubled.HasPerfectZPC) : W.HasPerfectZPC n :=
  h.extends_.doubled.hasPerfectZPC hG

end MeetsAt

end MIPRE.Tailored.TailoredVerifier

end
