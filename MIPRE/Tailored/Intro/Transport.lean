/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Intro.Encoded
public import MIPRE.Tailored.ZPC
public import MIPRE.Foundations.PerfectStrategy
public import MIPRE.Foundations.OracularModel

@[expose] public section

/-!
# Presenting a game as a tailored game

Phase 3 of `planning/aldous-lyons-track.md` (issue #281) presents the introspection verifier's
game `H` as a tailored game `G` on the same questions, whose answers are fixed-length bit
vectors. The two are tied by maps of answers in each direction:

* `dec x : (G-answers at x) → (H-answers)`, along which every answer pair `G` accepts is one `H`
  accepts: then `val*(G) ≤ val*(H)` (`valStar_le_of_dec`), the soundness direction;
* `enc x : (H-answers) → F₂^{len x}`, along which every answer pair `H` accepts *among the
  encodable ones* is one `G` accepts: then a perfect PCC strategy of `H` charging only encodable
  answers, whose bit observables along `enc` are signed permutations, diagonal at the readable
  bits, is a perfect permutation strategy of `G` (`hasPerfectZPC_of_sync`), the completeness
  direction.

The bit observables are those of `MIPRE.Tailored.encObs`; their Fourier transform is the
push-forward of the strategy along `enc` (`fourierProj_encObs`), which is why the value carries
over.
-/

namespace MIPRE.SyncStrategy

/-! ## Perfect PCC strategies have no rejected outcomes -/

section Sync

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

/-- The measurement at a question of a synchronous strategy is a projective measurement. -/
theorem isPVMIn (S : SyncStrategy G) (x : X) : IsPVMIn (S.P.M x) where
  star_eq a := S.P.selfAdjoint x a
  idem a := S.P.projective x a
  sum_eq_one := S.P.normalized x
  orthogonal h := S.orthogonal x h

/-- **A perfect PCC strategy has no rejected outcome**: at a question pair of positive weight,
the projections of a rejected answer pair multiply to zero. -/
theorem mul_eq_zero_of_value_eq_one (S : SyncStrategy G) (hS : S.IsPCC)
    (h : S.value = 1) {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    S.P.M x a * S.P.M y b = 0 := by
  have hc := hS x y hxy a b
  refine S.eq_zero_of_trace_re_eq_zero ?_ ?_ (S.re_eq_zero_of_value_eq_one h hxy hD)
  · rw [star_mul, S.P.selfAdjoint, S.P.selfAdjoint, hc]
  · rw [show S.P.M x a * S.P.M y b * (S.P.M x a * S.P.M y b) =
        S.P.M x a * (S.P.M y b * S.P.M x a) * S.P.M y b by noncomm_ring, ← hc,
      ← mul_assoc, S.P.projective, mul_assoc, S.P.projective]

end Sync

end MIPRE.SyncStrategy

namespace MIPRE.Tailored

open Finset

/-! ## The two transports -/

section Transport

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable (G : TailoredGame X) (H : Game X X A A)

/-- **Soundness**: if every answer pair the tailored game accepts decodes to one `H` accepts,
then `val*(G) ≤ val*(H)`. -/
theorem valStar_le_of_dec (dec : X → Verifier.Answers G.maxLen → A)
    (hμ : ∀ x y, H.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.Accepts x y a.1 b.1 → H.D x y (dec x a) (dec y b) = true) :
    G.valStar ≤ quantumValue H :=
  quantumValue_le_postprocess G.toGame H dec dec hμ fun x y a b h =>
    hD x y a b (of_decide_eq_true h)

variable (enc : (x : X) → A → Fin (G.len x) → Bool) (ok : X → A → Prop)
variable (S : SyncStrategy H.doubled) (hS : S.IsPCC)
  (hperm : ∀ p i, IsSignedPerm (encObs (S.P.M p) (enc p.2) i))
  (hdiag : ∀ p (i : Fin (G.len p.2)), i.val < G.lenR p.2 → (encObs (S.P.M p) (enc p.2) i).IsDiag)
  (hμ : ∀ x y, H.μ x y = G.μ x y)

/-- The permutation strategy of `G` read off a synchronous strategy of `H`: at `(t, x)`, the bit
observables of the measurement at `(t, x)` along `enc x`. -/
noncomputable def permOfSync : PermStrategy G.doubled where
  m := S.d
  m_pos := S.d_pos
  U p := encObs (S.P.M p) (enc p.2)
  signedPerm := hperm
  invol p := encObs_mul_self (S.isPVMIn p) (enc p.2)
  comm p := commute_encObs (S.isPVMIn p) (enc p.2)
  zAligned := hdiag
  commEdges p q hpq i j := by
    have hpq' : 0 < H.doubled.μ p q := by
      simp only [Game.doubled_μ, hμ]
      exact hpq
    exact commute_encObs_encObs (fun a b => hS p q hpq' a b) (enc p.2) (enc q.2) i j

theorem permOfSync_proj (p : Bool × X) (a : Fin (G.len p.2) → Bool) :
    (permOfSync G H enc S hS hperm hdiag hμ).proj p a =
      ∑ l ∈ univ.filter fun l => enc p.2 l = a, S.P.M p l :=
  fourierProj_encObs (S.isPVMIn p) (enc p.2) a

/-- **Completeness**: a perfect PCC strategy of `H` charging only answers in `ok`, along whose
encodings every accepted pair of such answers is accepted by `G`, and whose bit observables are
signed permutations, diagonal at the readable bits, gives a perfect permutation strategy of the
doubled tailored game. -/
theorem value_permOfSync (hval : S.value = 1)
    (hsupp : ∀ p a, ¬ok p.2 a → S.P.M p a = 0)
    (hacc : ∀ x y a b, ok x a → ok y b → H.D x y a b = true →
      G.Accepts x y (List.ofFn (enc x a)) (List.ofFn (enc y b))) :
    (permOfSync G H enc S hS hperm hdiag hμ).value = 1 := by
  apply PermStrategy.value_eq_one_of
  intro p q hpq
  suffices key : ∀ (a : Fin (G.len p.2) → Bool) (b : Fin (G.len q.2) → Bool),
      ¬G.Accepts p.2 q.2 (List.ofFn a) (List.ofFn b) →
        (permOfSync G H enc S hS hperm hdiag hμ).proj p a *
          (permOfSync G H enc S hS hperm hdiag hμ).proj q b = 0 from
    fun a b h => key a b h
  intro a b hrej
  have hpq' : 0 < H.doubled.μ p q := by
    simp only [Game.doubled_μ, hμ]
    exact hpq
  have htag : p.1 = false ∧ q.1 = true := by
    by_contra hn
    simp [TailoredGame.doubled, hn] at hpq
  rw [permOfSync_proj, permOfSync_proj]
  change (∑ l ∈ univ.filter fun l => enc p.2 l = a, S.P.M p l) *
    (∑ l ∈ univ.filter fun l => enc q.2 l = b, S.P.M q l) = (0 : Matrix (Fin S.d) (Fin S.d) ℂ)
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun l' hl' => ?_
  by_cases hl0 : ok p.2 l
  · by_cases hl0' : ok q.2 l'
    · refine S.mul_eq_zero_of_value_eq_one hS hval hpq' ?_
      simp only [Game.doubled, htag, and_self, ite_true]
      by_contra hacc'
      rw [Bool.not_eq_false] at hacc'
      apply hrej
      have := hacc p.2 q.2 l l' hl0 hl0' hacc'
      rw [(Finset.mem_filter.1 hl).2, (Finset.mem_filter.1 hl').2] at this
      exact this
    · rw [hsupp q l' hl0', mul_zero]
  · rw [hsupp p l hl0, zero_mul]

include hS hperm hdiag hμ in
theorem hasPerfectZPC_of_sync (hval : S.value = 1)
    (hsupp : ∀ p a, ¬ok p.2 a → S.P.M p a = 0)
    (hacc : ∀ x y a b, ok x a → ok y b → H.D x y a b = true →
      G.Accepts x y (List.ofFn (enc x a)) (List.ofFn (enc y b))) :
    G.doubled.HasPerfectZPC :=
  ⟨permOfSync G H enc S hS hperm hdiag hμ, value_permOfSync G H enc ok S hS hperm hdiag hμ hval
    hsupp hacc⟩

end Transport

end MIPRE.Tailored

end
