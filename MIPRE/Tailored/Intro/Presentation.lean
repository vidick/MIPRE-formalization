/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Detyping
public import MIPRE.Tailored.Intro.Transport

@[expose] public section

/-!
# Presenting a detyped game by a detyped tailored game

The two transports of `MIPRE.Tailored.Intro.Transport` and the two reductions to the edges of
`MIPRE.Tailored.Detyping`, put together: for a game `H` on detyped questions whose predicate
calls a typed predicate `Dt` on the edges and accepts off them (the shape of every verifier this
repository detypes, `CL.Detyping.accepts`), and typed tailored data `D`,

* `valStar_presented_le`: if on every edge a pair the typed data accepts decodes to one `Dt`
  accepts, then `val*` of the detyped tailored game is at most that of `H`;
* `hasPerfectZPC_presented`: if on every edge an accepted pair of encodable answers encodes to
  one the typed data accepts, with the typed lengths, then a perfect PCC strategy of `H` charging
  only encodable answers, whose bit observables along the encoding are signed permutations
  diagonal at the readable bits, gives a perfect permutation strategy of the detyped tailored
  game.
-/

namespace MIPRE.Tailored

open Cost MIPRE.CL MIPRE.CL.Detyping Classical

/-- A list as a vector of a given length, padded with `false`. -/
def vecOf (n : ℕ) (l : BitStr) : Fin n → Bool := fun i => l.getD i false

theorem ofFn_vecOf {n : ℕ} {l : BitStr} (h : l.length = n) : List.ofFn (vecOf n l) = l := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [vecOf, h2]

variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  (E : T → T → Prop) [DecidableRel E] {B : ℕ}
  (H : Game (Coord T ι → ZMod 2) (Coord T ι → ZMod 2) (Verifier.Answers B) (Verifier.Answers B))
  (Dt : Question T ι → Question T ι → Verifier.Answers B → Verifier.Answers B → Bool)
  (hH : ∀ x y a b, H.D x y a b = Detyping.accepts E Dt x y a b)
  (D : TypedData T ι)

/-- The detyped tailored game, on the question distribution of `H`. -/
noncomputable abbrev presented : TailoredGame (Coord T ι → ZMod 2) :=
  D.detype E H.μ H.μ_nonneg H.μ_sum_one

include hH in
/-- **Soundness of the presentation.** -/
theorem valStar_presented_le (decT : Question T ι → BitStr → Verifier.Answers B)
    (a₀ : Verifier.Answers B)
    (h : ∀ u v a b, E u.1 v.1 → D.Accepts u v a b → Dt u v (decT u a) (decT v b) = true) :
    (presented E H D).valStar ≤ quantumValue H :=
  valStar_le_of_dec _ H (fun x a => TypedData.decD E decT a₀ x a.1) (fun _ _ => rfl)
    fun x y a b hab => by
      rw [hH]
      exact D.detype_accepts_dec E Dt decT a₀ h x y a.1 b.1 hab

variable (encT : Question T ι → Verifier.Answers B → BitStr)
  (okT : Question T ι → Verifier.Answers B → Prop) (a₀ : Verifier.Answers B)

/-- The encodable answers at a detyped question: the typed ones at a decodable view, and `a₀`
elsewhere. -/
def okD (x : Coord T ι → ZMod 2) (a : Verifier.Answers B) : Prop :=
  (∀ t, typeOf E x = some t → okT (t, pull .inr x) a) ∧ (typeOf E x = none → a = a₀)

/-- The encoding at a detyped question, as a vector of the question's length. -/
noncomputable def encV (x : Coord T ι → ZMod 2) (a : Verifier.Answers B) :
    Fin ((presented E H D).len x) → Bool :=
  vecOf _ (TypedData.encD E encT x a)

variable {encT okT}

theorem length_encD_of_okD (hlen : ∀ u a, okT u a → (encT u a).length = D.lenR u.1 + D.lenL u.1)
    {x : Coord T ι → ZMod 2} {a : Verifier.Answers B} (ha : okD E okT a₀ x a) :
    (TypedData.encD E encT x a).length = (presented E H D).len x := by
  unfold TypedData.encD TailoredGame.len
  cases hx : typeOf E x with
  | none => simp [TypedData.detype, hx]
  | some t => simp [TypedData.detype, hx, hlen _ _ (ha.1 t hx)]

include hH in
/-- **Completeness of the presentation.** -/
theorem hasPerfectZPC_presented
    (hlen : ∀ u a, okT u a → (encT u a).length = D.lenR u.1 + D.lenL u.1)
    (h : ∀ u v a b, E u.1 v.1 → okT u a → okT v b → Dt u v a b = true →
      D.Accepts u v (encT u a) (encT v b))
    (S : SyncStrategy H.doubled) (hS : S.IsPCC) (hval : S.value = 1)
    (hsupp : ∀ p a, ¬okD E okT a₀ p.2 a → S.P.M p a = 0)
    (hperm : ∀ p i, IsSignedPerm (encObs (S.P.M p) (encV E H D encT p.2) i))
    (hdiag : ∀ p (i : Fin ((presented E H D).len p.2)), i.val < (presented E H D).lenR p.2 →
      (encObs (S.P.M p) (encV E H D encT p.2) i).IsDiag) :
    (presented E H D).doubled.HasPerfectZPC := by
  refine hasPerfectZPC_of_sync (presented E H D) H (encV E H D encT) (okD E okT a₀) S hS hperm
    hdiag (fun _ _ => rfl) hval hsupp ?_
  intro x y a b ha hb hab
  rw [encV, encV, ofFn_vecOf (length_encD_of_okD E H D a₀ hlen ha),
    ofFn_vecOf (length_encD_of_okD E H D a₀ hlen hb)]
  rw [hH] at hab
  exact D.detype_accepts_enc E Dt encT okT hlen h x y a b ha.1 hb.1 hab

end MIPRE.Tailored

end
