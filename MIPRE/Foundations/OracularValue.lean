/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.OracularTyped
public import MIPRE.Foundations.CL.DetypingModel
public import MIPRE.Foundations.CL.DetypingDeciderTransport

@[expose] public section

/-!
# Oracularization in a value model

The value transfers of oracularization at a normal form verifier —
`Verifier.valStar_ge_of_typed`, and through it `Oracularization.typed_soundness` and
`Oracularization.detyped_soundness` — use three facts about `val*` beyond the fields of
`ValueModel`: the game-level soundness of oracularization, the transfer from the typed game to
the oracularization by a question-dependent reading of the answers, and the detyping restriction.
`ValueModel.OracularSound` is those three facts, for a value model; the tensor-product and the
commuting-operator model have them (`ValueModel.tensor_oracularSound`,
`ValueModel.commuting_oracularSound`), both from the model-level statements
(`SeededGame.povmValue_sound_ge`, `BipartiteModel.povmValue_le_postprocess`,
`CL.Detyping.restrict_povmValue_ge`) read in the model of each strategy. The transfers are then
written once, in `Verifier.val ω` (`Verifier.val_ge_of_typed`,
`ValueModel.OracularSound.typedGame_ge_ambient`, and in `Pipeline/Oracularization.lean`
`Oracularization.typed_soundness_val` and `Oracularization.detyped_soundness_val`).
-/

namespace MIPRE

open Finset

namespace ValueModel

/-- **Oracularization is sound in the value model** (`def:oracular-sound-in`): the three facts the
value transfers of oracularization use.

* `le_postprocess`: reading the answers through maps that may depend on the question, on the
  same questions and distribution, raises the value when every accepted tuple stays accepted;
* `oracular`: the game-level soundness of oracularization, `ω(oracular) > 1 - ε` giving
  `ω ≥ 1 - 24√ε` for the input game;
* `detype`: the finite-game detyping restriction, the typed game's value at least
  `1 - 16^{|T|}(1 - ω)` of the detyped game's. -/
structure OracularSound (ω : ValueModel) : Prop where
  le_postprocess : ∀ {X Y A B A' B' : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] [DecidableEq A'] [DecidableEq B'] (G : Game X Y A B)
    (G' : Game X Y A' B') (rA : X → A → A') (rB : Y → B → B'), (∀ x y, G'.μ x y = G.μ x y) →
    (∀ x y a b, G.D x y a b = true → G'.D x y (rA x a) (rB y b) = true) → ω.val G ≤ ω.val G'
  oracular : ∀ {V A : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
    [Inhabited A] (S : SeededGame V A) {ε : ℝ}, 0 < ε → 1 - ε < ω.val S.oracular.toGame →
    1 - 24 * √ε ≤ ω.val S.toGame
  detype : ∀ {T ι A B : Type} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι] [Fintype A]
    [Fintype B] {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E], (∀ u v, E u v → E v u) →
    ∀ (hne : (CL.Graph.edges E).Nonempty) (P : Bool → T → CL.CLFun (ZMod 2) ι ℓ),
    (∀ w t, (P w t).ExactlyOn univ) → 0 < ℓ →
    ∀ D : CL.Detyping.Question T ι → CL.Detyping.Question T ι → A → B → Bool,
    1 - (16 : ℝ) ^ Fintype.card T * (1 - ω.val (CL.Detyping.game E P D))
      ≤ ω.val (CL.Detyping.typedGame E hne P D)

/-- **Oracularization is sound in the tensor-product model.** -/
theorem tensor_oracularSound : tensor.OracularSound where
  le_postprocess G G' rA rB hμ hD := quantumValue_le_postprocess G G' rA rB hμ hD
  oracular S _ hε h := S.quantumValue_ge_of_oracular hε h
  detype E _ hE hne P hP hℓ D := CL.Detyping.quantumValue_typedGame_ge E hE hne P hP hℓ D

/-- **Oracularization is sound in the commuting-operator model** (`lem:oracular-sound-co`). -/
theorem commuting_oracularSound : commuting.OracularSound where
  le_postprocess G G' rA rB hμ hD := commutingOperatorValue_le_postprocess G G' rA rB hμ hD
  oracular S _ hε h := S.commutingOperatorValue_ge_of_oracular hε h
  detype E _ hE hne P hP hℓ D :=
    CL.Detyping.commutingOperatorValue_typedGame_ge E hE hne P hP hℓ D

/-- **The detyping restriction at the compiled verifier**, in a value model: the typed game's
value is at least `1 - 16^{|T|}(1 - ω)` of the compiled verifier's game at the outer cut, which
is the finite detyped game up to the numbering of its coordinates (`ValueModel.eq_of_equiv`). -/
theorem OracularSound.typedGame_ge_ambient {ω : ValueModel} (hω : ω.OracularSound) {T : Type}
    [Fintype T] [DecidableEq T] [Cost.SizedEncoding T] {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (S : CL.TypedSampler ℓ T) (D : CL.Detyping.TypedDecider T) (C : CL.Detyping.CutoffProgram)
    (hE : ∀ u v, E u v → E v u) (hne : (CL.Graph.edges E).Nonempty) (hℓ : 0 < ℓ)
    (hD : D.Total) (n : ℕ) :
    1 - (16 : ℝ) ^ Fintype.card T *
        (1 - ω.val ((CL.Detyping.DeciderProgram.verifier E S D C hℓ hD).game n (C.outer n)))
      ≤ ω.val (CL.Detyping.typedGame E hne (CL.Detyping.DeciderProgram.sourceFamily S n)
          (CL.Detyping.DeciderProgram.typedPredicate S D C n)) := by
  have hfin := hω.detype E hE hne (CL.Detyping.DeciderProgram.sourceFamily S n)
    (fun w t => S.cl_exactlyOn n (Player.ofBool w) t) hℓ
    (CL.Detyping.DeciderProgram.typedPredicate S D C n)
  have heq : ω.val (CL.Detyping.game E (CL.Detyping.DeciderProgram.sourceFamily S n)
      (CL.Detyping.DeciderProgram.typedPredicate S D C n))
      = ω.val ((CL.Detyping.DeciderProgram.verifier E S D C hℓ hD).game n (C.outer n)) :=
    ω.eq_of_equiv _ _ (CL.Detyping.DeciderProgram.vectorEquiv (S.dim n))
      (CL.Detyping.DeciderProgram.vectorEquiv (S.dim n)) (.refl _) (.refl _)
      (fun x y => (CL.Detyping.DeciderProgram.verifier_game_mu E S D C hℓ hD n x y).symm)
      (fun x y a b => (CL.Detyping.DeciderProgram.verifier_game_D E S D C hℓ hD n x y a b).symm)
  rwa [heq] at hfin

end ValueModel

namespace SeededGame

/-- **The typed oracularized game has no larger value than the oracularization**, in a value model
where oracularization is sound: a typed predicate whose acceptance implies the oracularized
predicate after a question-dependent reading of the answers, on the same distribution
(`typedGame_mu`). `quantumValue_typedGame_le` is its tensor-product case. -/
theorem val_typedGame_le {ω : ValueModel} (hω : ω.OracularSound) {ι : Type} [Fintype ι]
    [DecidableEq ι] {ℓ : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1)) (D : (ι → CL.𝔽₂) → (ι → CL.𝔽₂) → A → A → Bool)
    {A' : Type} [Fintype A']
    (D' : CL.Detyping.Question Role ι → CL.Detyping.Question Role ι → A' → A' → Bool)
    (rA : CL.Detyping.Question Role ι → A' → OAns A)
    (hD : ∀ p q a b, D' p q a b = true → (ofCL L D).oaccepts p q (rA p a) (rA q b) = true) :
    ω.val (CL.Detyping.typedGame roleGraph roleGraph_nonempty (fun _ => roleFamily L) D')
      ≤ ω.val (ofCL L D).oracular.toGame :=
  hω.le_postprocess _ _ rA rA (fun p q => (typedGame_mu L D D' p q).symm) hD

end SeededGame

namespace Verifier

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

/-- **Soundness of the typed oracularized game, in a value model** where oracularization is
sound: for a typed predicate whose acceptance implies the oracularized predicate after a reading
of the answers, `ω` of the typed game above `1 - ε` puts `ω(𝒱_n)` at least `1 - 24√ε`.
`valStar_ge_of_typed` is its tensor-product case. -/
theorem val_ge_of_typed {ω : ValueModel} (hω : ω.OracularSound) (n B : ℕ) {A' : Type}
    [Fintype A']
    (D' : CL.Detyping.Question Role (Fin (V.sampler.dim n)) →
      CL.Detyping.Question Role (Fin (V.sampler.dim n)) → A' → A' → Bool)
    (rA : CL.Detyping.Question Role (Fin (V.sampler.dim n)) → A' → OAns (Answers B))
    (hD : ∀ p q a b, D' p q a b = true → (V.seeded n B).oaccepts p q (rA p a) (rA q b) = true)
    {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < ω.val (CL.Detyping.typedGame roleGraph roleGraph_nonempty
      (fun _ => roleFamily (V.sampler.cl n)) D')) :
    1 - 24 * √ε ≤ V.val ω n B :=
  hω.oracular (V.seeded n B) hε (lt_of_lt_of_le h (SeededGame.val_typedGame_le hω _ _ D' rA hD))

end Verifier

end MIPRE

end
