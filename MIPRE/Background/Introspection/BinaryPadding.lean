/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.BinaryGame
import MIPRE.Foundations.Introspection.SourcePadding
import Mathlib.Algebra.BigOperators.Fin

/-! # Full typed introspection completeness for arbitrary binary source lengths

The original `s` coordinates are placed in the first `s` positions of an
explicitly numbered `2^m*t`-qubit register. The original CL presentation is
extended by zero and its decider restricts to the original coordinates. No
field-linearity condition is imposed on the source CL functions.

The same-depth `depthPaddedGame` uses full-register auxiliary checks. Enlarging
the first factor can give dual Read/Hide labels with nonzero spectator bits,
even though the ordinary CL output is zero there. An executable verifier with
strict original-subspace answer guards therefore needs full-register checks
or a separate answer-format/coarsening bridge; that compiler identification
is not asserted by this finite-game theorem.
-/

noncomputable section
namespace MIPRE.Introspection.BinaryComplete
open Finset Classical
set_option linter.unusedSectionVars false

/-- Binary ordering of the Boolean hypercube, then the field-basis bit. -/
def coordNumbering (m t : ℕ) : Coord m t ≃ Fin (2^m*t) :=
  (Equiv.prodCongr
    ((Equiv.piCongrRight fun _ : Fin m => finTwoEquiv.symm).trans finFunctionFinEquiv)
    (Equiv.refl (Fin t))).trans finProdFinEquiv

/-- Pad in the initial numbered coordinates, with an explicit inverse label. -/
def paddingEmbedding {s m t : ℕ} (hs : s ≤ 2^m*t) : Fin s ↪ Coord m t :=
  (Fin.castLEEmb hs).trans (coordNumbering m t).symm.toEmbedding

theorem paddingEmbedding_number {s m t : ℕ} (hs : s ≤ 2^m*t) (i : Fin s) :
    (coordNumbering m t (paddingEmbedding hs i)).val = i.val := by
  simp [paddingEmbedding]

theorem card_seed (m t : ℕ) : Fintype.card (Seed m t) = 2^(2^m*t) := by
  simp [Seed, Coord]

variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t s : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Fin s) ℓ)
  (D : (Fin s → ZMod 2) → (Fin s → ZMod 2) → A → A → Bool)

/-- The actual full parsed game on the padded original CL maps. -/
def paddedGame (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hs : s ≤ 2^m*t) :=
  game (d := d) (SourcePadding.family (paddingEmbedding hs) L)
    (SourcePadding.decider (paddingEmbedding hs) D) hm b

/-- Any binary original CL game fits the honest construction after explicit
zero padding. The extra dimension is exactly the full qubit register and one
Magic Square qubit; the original strategy dimension is retained. -/
theorem exists_padded_perfectPCC
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (hd : 1 ≤ d) (hs : s ≤ 2^m*t)
    (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (paddedGame (d := d) L D hm b hs).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2^(2^m*t+1)*R.d := by
  let e := paddingEmbedding hs
  let R' := SourcePadding.strategy e L D R
  obtain ⟨Q,hQ,hvQ,hDim⟩ := exists_perfectPCC (SourcePadding.family e L)
    (SourcePadding.decider e D) R' hm b hb hd
    (SourcePadding.family_supported e L hL)
    (SourcePadding.strategy_isPCC e L D R hR)
    (SourcePadding.strategy_value e L D R hR hv)
  refine ⟨Q,hQ,hvQ,?_⟩
  rw [hDim, card_seed]
  change 2 * 2^(2^m*t) * R.d = 2^(2^m*t+1)*R.d
  rw [pow_succ, Nat.mul_comm 2]

/-- The same binary source with one final zero stage, so the factor registers
partition the entire padded register as required by soundness. -/
def exactPaddedGame (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hs : s ≤ 2^m*t) :=
  game (d := d) (SourcePadding.fullFamily (paddingEmbedding hs) L)
    (SourcePadding.decider (paddingEmbedding hs) D) hm b

/-- Exact-partition padding keeps the source game and dimension unchanged;
only the auxiliary hiding-chain level count increases by one. -/
theorem exists_exactPadded_perfectPCC
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (hd : 1 ≤ d) (hs : s ≤ 2^m*t)
    (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    (∀ w, (SourcePadding.fullFamily (paddingEmbedding hs) L w).ExactlyOn univ) ∧
    ∃ Q : SyncStrategy (exactPaddedGame (d := d) L D hm b hs).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2^(2^m*t+1)*R.d := by
  let e := paddingEmbedding hs
  have hfull := SourcePadding.fullFamily_exactlyOn e L hL
  refine ⟨hfull,?_⟩
  have hex : ∃ R' : SyncStrategy
      (Honest.sourceGame (SourcePadding.fullFamily e L) (SourcePadding.decider e D)).doubled,
      R'.IsPCC ∧ R'.value = 1 ∧ R'.d = R.d := by
    rw [SourcePadding.sourceGame_fullFamily]
    exact SourcePadding.exists_perfectPCC e L D R hR hv
  obtain ⟨R',hR',hv',hdim⟩ := hex
  obtain ⟨Q,hQ,hvQ,hDim⟩ := exists_perfectPCC (SourcePadding.fullFamily e L)
    (SourcePadding.decider e D) R' hm b hb hd (fun w => (hfull w).supportedOn) hR' hv'
  refine ⟨Q,hQ,hvQ,?_⟩
  rw [hDim, card_seed, hdim, pow_succ, Nat.mul_comm 2]

/-- The exact-partition construction at the original positive depth. -/
def depthPaddedGame (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hs : s ≤ 2^m*t) :=
  game (d := d) (SourcePadding.depthFamily (paddingEmbedding hs) L)
    (SourcePadding.decider (paddingEmbedding hs) D) hm b

/-- Arbitrary binary exact CL samplers extend to the complete typed
introspection game without changing their level count. -/
theorem exists_depthPadded_perfectPCC
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hb : LowDegree.IsSelfDualBasis b) (hd : 1 ≤ d) (hs : s ≤ 2^m*t) (hℓ : 0 < ℓ)
    (hL : ∀ w, (L w).ExactlyOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    (∀ w, (SourcePadding.depthFamily (paddingEmbedding hs) L w).ExactlyOn univ) ∧
    ∃ Q : SyncStrategy (depthPaddedGame (d := d) L D hm b hs).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2^(2^m*t+1)*R.d := by
  let e := paddingEmbedding hs
  have hfull := SourcePadding.depthFamily_exactlyOn e L hℓ hL
  refine ⟨hfull,?_⟩
  have hex : ∃ R' : SyncStrategy
      (Honest.sourceGame (SourcePadding.depthFamily e L) (SourcePadding.decider e D)).doubled,
      R'.IsPCC ∧ R'.value = 1 ∧ R'.d = R.d := by
    rw [SourcePadding.sourceGame_depthFamily e L D hℓ (fun w => (hL w).supportedOn)]
    exact SourcePadding.exists_perfectPCC e L D R hR hv
  obtain ⟨R',hR',hv',hdim⟩ := hex
  obtain ⟨Q,hQ,hvQ,hDim⟩ := exists_perfectPCC (SourcePadding.depthFamily e L)
    (SourcePadding.decider e D) R' hm b hb hd (fun w => (hfull w).supportedOn) hR' hv'
  refine ⟨Q,hQ,hvQ,?_⟩
  rw [hDim, card_seed, hdim, pow_succ, Nat.mul_comm 2]

end MIPRE.Introspection.BinaryComplete
end
