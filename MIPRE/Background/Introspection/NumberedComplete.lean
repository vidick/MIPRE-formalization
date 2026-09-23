/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.BinaryQuotientCompleteSupport
import MIPRE.Foundations.Introspection.SourceReindex
import MIPRE.Foundations.Introspection.TypedQuotientReindex
import MIPRE.Background.QLD.PauliFullAnswerPrograms

/-! # Honest guarded quotient completeness with the actual register numbering

The source CL family remains on its given coordinate type. Only its honest
construction is expressed temporarily in the binary Weyl coordinates. Quotient
transport then returns the strategy to the original coordinates, with exact
dimension and with support certificates for both kinds of executable guards.
-/

noncomputable section
namespace MIPRE.Introspection.NumberedComplete
open Finset CL Classical BinaryComplete
set_option linter.unusedSectionVars false
variable {F A I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
  {m t d ℓ : ℕ} [NeZero m]
  (e : I ≃ Coord m t) (L : Bool → CLFun (ZMod 2) I ℓ)
  (D : (I → ZMod 2) → (I → ZMod 2) → A → A → Bool)
  (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (χ : F → Fin m) (π : F ≃ F)

def project (a : QLD.Answer F m d) : I → ZMod 2 :=
  (reindexEquiv e).symm (BinaryComplete.project b a)

abbrev game := AuxiliaryQuotient.game QLD.adj (.pauli .X) (.pauli .Z)
  (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
  (ExplicitGame.pauliCheck hm π b)

abbrev guardedGame := PrefixGuard.game L Prod.fst (game (d := d) e L D hm b χ π)

/-- The temporary coordinate game has a perfect honest PCC strategy, including
the exact support facts needed after transporting back to the finite register. -/
theorem coordinate_exists_perfectPCC_with_format
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hb : LowDegree.IsSelfDualBasis b) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (AuxiliaryQuotient.reindexedGame e QLD.adj (.pauli .X) (.pauli .Z)
        (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
        (ExplicitGame.pauliCheck hm π b)).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (Seed m t) * R.d ∧
      (∀ q a, Q.P.M q a ≠ 0 →
        PrefixGuard.holds (SourceReindex.family e L) q.2.1 a) ∧
      (∀ side w payload y a,
        Q.P.M (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0 →
        ∃ x, (SourceReindex.family e L w).eval x = y) ∧
      (∀ side p payload a, Q.P.M (side,.inl p,payload) (.pauli a) ≠ 0 →
        (QLD.PauliCL.ExplicitSeed.binaryDecode π b p payload).fmtOk a = true) := by
  let Lc := SourceReindex.family e L
  let Dc := SourceReindex.decider e D
  let Rc := SourceReindex.strategy e L D R
  have hLc : ∀ w, (Lc w).SupportedOn univ := fun w => by
    simpa only [Lc, SourceReindex.family, map_univ_equiv] using (hL w).reindex e
  have hRc : Rc.IsPCC := SourceReindex.strategy_isPCC e L D R hR
  have hvRc : Rc.value = 1 := (SourceReindex.strategy_value e L D R).trans hv
  have hproj : (fun a : QLD.Answer F m d => reindexEquiv e (project e b a)) =
      BinaryComplete.project b := by
    funext a
    exact (reindexEquiv e).apply_symm_apply _
  let Gc := AuxiliaryQuotient.reindexedGame e QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
    (ExplicitGame.pauliCheck hm π b)
  have hgame : Gc = BinaryComplete.explicitQuotientGame Lc Dc hm b χ π := by
    change AuxiliaryQuotient.game _ _ _ _ _ _ _ _ = _
    rw [hproj]
    rfl
  let Q := BinaryComplete.quotientHonest (d := d) Lc Dc Rc hm b hLc χ π
  have hμ : ∀ x y, Gc.doubled.μ x y =
      (BinaryComplete.explicitQuotientGame Lc Dc hm b χ π).doubled.μ x y :=
    fun _ _ => by rw [hgame]
  refine ⟨Q.copy Gc.doubled,
    SyncStrategy.isPCC_copy
      (BinaryComplete.quotientHonest_isPCC Lc Dc Rc hm b hLc χ π hb hχ hRc) _ hμ,
    (Q.value_copy _ hμ (fun _ _ _ _ => by rw [hgame])).trans
      (BinaryComplete.quotientHonest_value Lc Dc Rc hm b hLc χ π hb hχ hd hRc hvRc),
    ?_, BinaryComplete.quotientHonest_prefixGuard Lc Dc Rc hm b hLc χ π,
    BinaryComplete.quotientHonest_introspect Lc Dc Rc hm b hLc χ π,
    BinaryComplete.quotientHonest_pauli_format Lc Dc Rc hm b hLc χ π⟩
  exact BinaryComplete.quotientHonest_dimension (d := d) Lc Dc Rc hm b hLc χ π

/-- Perfect PCC completeness after coordinate transport and executable prefix
guards. Introspect labels still lie in the actual original source-output range. -/
theorem exists_perfectPCC_with_format
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hb : LowDegree.IsSelfDualBasis b) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (guardedGame (d := d) e L D hm b χ π).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (Seed m t) * R.d ∧
      (∀ q a, Q.P.M q a ≠ 0 → PrefixGuard.holds L q.2.1 a) ∧
      (∀ side w payload y a,
        Q.P.M (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0 →
        ∃ x, (L w).eval x = y) ∧
      (∀ side p payload a, Q.P.M (side,.inl p,payload) (.pauli a) ≠ 0 →
        (QLD.PauliCL.ExplicitSeed.binaryDecode π b p payload).fmtOk a = true) := by
  obtain ⟨Q,hQ,hvQ,hdQ,hguard,hintro,hformat⟩ :=
    coordinate_exists_perfectPCC_with_format e L D hm b χ π R hb hχ hd hL hR hv
  let S := AuxiliaryQuotient.originalPCC e QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
    (ExplicitGame.pauliCheck hm π b) Q
  have hS : S.IsPCC := AuxiliaryQuotient.originalPCC_isPCC _ _ _ _ _ _ _ _ _ Q hQ
  have hvS : S.value = 1 := (AuxiliaryQuotient.originalPCC_value _ _ _ _ _ _ _ _ _ Q).trans hvQ
  have hdS : S.d = 2 * Fintype.card (Seed m t) * R.d :=
    (AuxiliaryQuotient.originalPCC_dimension _ _ _ _ _ _ _ _ _ Q).trans hdQ
  have hguardS : ∀ q a, S.P.M q a ≠ 0 → PrefixGuard.holds L q.2.1 a :=
    AuxiliaryQuotient.originalPCC_prefixGuard _ _ _ _ _ _ _ _ _ Q hguard
  refine ⟨S.copy (guardedGame e L D hm b χ π).doubled,
    PrefixGuard.copied_isPCC L Prod.fst _ S hS,
    PrefixGuard.copied_value_eq_one L Prod.fst _ S hguardS hvS,
    hdS, hguardS, ?_, hformat⟩
  intro side w payload y a ha
  obtain ⟨x,hx⟩ := hintro side w payload (reindexEquiv e y) a ha
  refine ⟨(reindexEquiv e).symm x, ?_⟩
  change ((L w).reindex e).eval x = reindexEquiv e y at hx
  rw [CLFun.eval_reindex'] at hx
  exact (reindexEquiv e).injective hx

/-- Compatibility statement retaining the original coordinate witness API. -/
theorem coordinate_exists_perfectPCC
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hb : LowDegree.IsSelfDualBasis b) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (AuxiliaryQuotient.reindexedGame e QLD.adj (.pauli .X) (.pauli .Z)
        (QLD.PauliCL.ExplicitSeed.binaryPresentation χ b) L (project (d := d) e b) D
        (ExplicitGame.pauliCheck hm π b)).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (Seed m t) * R.d ∧
      (∀ q a, Q.P.M q a ≠ 0 →
        PrefixGuard.holds (SourceReindex.family e L) q.2.1 a) ∧
      (∀ side w payload y a,
        Q.P.M (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0 →
        ∃ x, (SourceReindex.family e L w).eval x = y) := by
  obtain ⟨Q,hQ,hvQ,hdQ,hg,hi,_⟩ :=
    coordinate_exists_perfectPCC_with_format e L D hm b χ π R hb hχ hd hL hR hv
  exact ⟨Q,hQ,hvQ,hdQ,hg,hi⟩

/-- Compatibility statement retaining the original guarded witness API. -/
theorem exists_perfectPCC
    (R : SyncStrategy (Honest.sourceGame L D).doubled)
    (hb : LowDegree.IsSelfDualBasis b) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    ∃ Q : SyncStrategy (guardedGame (d := d) e L D hm b χ π).doubled,
      Q.IsPCC ∧ Q.value = 1 ∧ Q.d = 2 * Fintype.card (Seed m t) * R.d ∧
      (∀ q a, Q.P.M q a ≠ 0 → PrefixGuard.holds L q.2.1 a) ∧
      (∀ side w payload y a,
        Q.P.M (side, .inr (.introspect,w), payload) (.pair y a) ≠ 0 →
        ∃ x, (L w).eval x = y) := by
  obtain ⟨Q,hQ,hvQ,hdQ,hg,hi,_⟩ :=
    exists_perfectPCC_with_format e L D hm b χ π R hb hχ hd hL hR hv
  exact ⟨Q,hQ,hvQ,hdQ,hg,hi⟩

/-- The concrete executable numbering is the same projection, exactly. -/
theorem project_registerNumbering (a : QLD.Honest.Register F m) :
    project (QLD.PauliFullAnswerProgram.registerNumbering m t).symm b
      (.pauliAns (d := d) a) = QLD.PauliFullAnswerProgram.registerVector b a := rfl

end MIPRE.Introspection.NumberedComplete
end
