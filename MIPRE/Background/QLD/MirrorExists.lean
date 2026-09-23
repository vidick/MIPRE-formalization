/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.QLD.PaddedLIDT
import MIPRE.Background.QLD.Mirror

/-!
# `MirrorSimul`, discharged

`Mirror.lean` introduces `MirrorSimul`: the two cuts of `lem:qld-4-7`, on one state. Everything
`lem:qld-pauli-selfcons` and `lem:qld-swap` say is stated against it, and until now nothing
constructed one --- so that whole run of results was conditional on a structure no strategy had
been shown to have.

It has one. The two cuts are two runs of the same construction: `exists_globalPair` at the
strategy gives the first, and at the *swapped* strategy the second, whose padded state carries the
other pair. Nothing relates the two runs' measurements, and the structure does not ask that; the
one field that relates the two cuts is `hmirror`, and that is about the states alone.

## Why `hmirror` is not hard

Because both states are explicit. `padState` is the strategy tensored with one maximally entangled
pair and four padding registers pinned at basis vectors (`padState_reindex_apply`), so appending to
each cut the pair the *other* one carries gives, on both sides, the same product of the same six
factors. All that is left to check is that swapping a pair's two halves changes nothing, which is
`epr_symm`.

What this does **not** do is relate the two cuts' pair measurements. The paper does not either:
`lem:qld-4-7` gives one measurement per player's space, and the chain's endpoint is symmetric in
them for a reason of its own (`swap_mem_coupledIdx`), not because the two measurements are the
same object.
-/

noncomputable section
namespace MIPRE
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder

variable {dA dB Anc Bnc : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

/-- **The doubly padded state, pointwise**: the original amplitude where both ancillas sit at
their basis vectors, and zero elsewhere. -/
theorem extVec2_apply (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (p : (dA × Anc) × (dB × Bnc)) :
    extVec2 ψ a₀ b₀ p
      = (if p.1.2 = a₀ then (1 : ℂ) else 0) * (if p.2.2 = b₀ then (1 : ℂ) else 0)
        * ψ (p.1.1, p.2.1) := by
  classical
  obtain ⟨⟨x, anc⟩, ⟨y, bnc⟩⟩ := p
  show (∑ q : dA × dB, ((ancillaEmbed dA a₀) ⊗ₖ (ancillaEmbed dB b₀)) ((x, anc), (y, bnc)) q
      * ψ q) = _
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => Finset.sum_congr rfl fun k _ => show
      ((ancillaEmbed dA a₀) ⊗ₖ (ancillaEmbed dB b₀)) ((x, anc), (y, bnc)) (j, k) * ψ (j, k)
        = ((if (x, anc) = (j, a₀) then (1 : ℂ) else 0)
            * (if (y, bnc) = (k, b₀) then (1 : ℂ) else 0)) * ψ (j, k) from rfl]
  by_cases ha : anc = a₀
  · by_cases hb : bnc = b₀
    · subst ha; subst hb
      simp [Prod.ext_iff, ite_and, Finset.sum_ite_eq]
    · simp [Prod.ext_iff, hb]
  · simp [Prod.ext_iff, ha]

end MIPRE

namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.Adapter MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **A maximally entangled pair is symmetric.** This is the whole content of the two cuts reading
one state: the pair each cut is missing is the other's, and swapping its halves changes nothing. -/
theorem epr_symm (a b : Anc F m) :
    epr (F := F) (n := Fin m → Bool) (a, b) = epr (F := F) (n := Fin m → Bool) (b, a) := by
  rw [epr, epr]
  exact if_congr eq_comm rfl rfl

/-- The weight the two padding registers carry: one where both sit at their basis vectors. -/
def padWeight (e : (F × F) × CL.Answer F (4 * m) d 1) : ℂ :=
  (if e.1 = ((0 : F), (0 : F)) then (1 : ℂ) else 0) * (if e.2 = ansZero then (1 : ℂ) else 0)

set_option maxHeartbeats 1000000 in
/-- **The `SimulPair`'s state, pointwise.** It is the strategy's amplitude times the pair's, with
the padding registers pinned at their basis vectors --- an explicit product, which is what makes
the two cuts comparable. -/
theorem padState_reindex_apply (ψ : dA × dB → ℂ)
    (A : (dA × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1))
    (B : (dB × Anc F m) × ((F × F) × CL.Answer F (4 * m) d 1)) :
    reindexVec (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
        (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
        (padState (F := F) (m := m) (d := d) ψ) (A, B)
      = padWeight A.2 * padWeight B.2 * (ψ (A.1.1, B.1.1) * epr (A.1.2, B.1.2)) := by
  obtain ⟨⟨a, a'⟩, ⟨f, c⟩⟩ := A
  obtain ⟨⟨b, b'⟩, ⟨g, e⟩⟩ := B
  show padState (F := F) (m := m) (d := d) ψ ((((a, a'), f), c), (((b, b'), g), e)) = _
  rw [padState, extVec2_apply, extHat, extVec2_apply, hatVec]
  show _ = padWeight (f, c) * padWeight (g, e) * (ψ (a, b) * epr (a', b'))
  rw [padWeight, padWeight, expVec]
  ring

set_option maxHeartbeats 1000000 in
/-- **The two cuts read one state.** Appending to each cut the pair the *other* one carries gives
the same state on all six registers, up to the change of reading `mirrorVec`. Both sides are the
same explicit product --- the strategy, the two pairs, and the four padding registers pinned at
their basis vectors --- and all that has to be checked is that swapping a pair's two halves
changes nothing, which is `epr_symm`. -/
theorem hmirror_padState (ψ : dA × dB → ℂ) :
    expVec (reindexVec (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
          (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
          (padState (F := F) (m := m) (d := d) (ψ ∘ Prod.swap)))
        (epr (F := F) (n := Fin m → Bool))
      = mirrorVec (expVec (reindexVec
            (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
            (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
            (padState (F := F) (m := m) (d := d) ψ))
          (epr (F := F) (n := Fin m → Bool))) := by
  funext p
  obtain ⟨⟨⟨⟨b, b'⟩, eb⟩, t⟩, ⟨⟨a, b''⟩, ea⟩, s⟩ := p
  show reindexVec (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
          (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
          (padState (F := F) (m := m) (d := d) (ψ ∘ Prod.swap)) (((b, b'), eb), ((a, b''), ea))
        * epr (F := F) (n := Fin m → Bool) (t, s)
      = reindexVec (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
            (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
            (padState (F := F) (m := m) (d := d) ψ) (((a, s), ea), ((b, t), eb))
        * epr (F := F) (n := Fin m → Bool) (b'', b')
  rw [padState_reindex_apply, padState_reindex_apply]
  show padWeight eb * padWeight ea * ((ψ ∘ Prod.swap) (b, a) * epr (b', b''))
      * epr (F := F) (n := Fin m → Bool) (t, s)
    = padWeight ea * padWeight eb * (ψ (a, b) * epr (s, t))
      * epr (F := F) (n := Fin m → Bool) (b'', b')
  rw [epr_symm s t, epr_symm b'' b']
  show padWeight eb * padWeight ea * (ψ (a, b) * epr (b', b'')) * epr (t, s)
    = padWeight ea * padWeight eb * (ψ (a, b) * epr (t, s)) * epr (b', b'')
  ring

variable {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ψ : dA × dB → ℂ} {ε δ : ℝ} {hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)}
  {hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)} (hm : m ∣ Fintype.card F)

set_option synthInstance.maxSize 1000

include hm in
/-- **`MirrorSimul`, discharged.** The two cuts are two runs of the same construction: the first
at the strategy, the second at the swapped strategy, whose padded state carries the *other* pair.
Nothing relates their measurements --- the structure does not ask that --- and the one field that
does relate the two, `hmirror`, is about the states alone, which are explicit products. -/
noncomputable def mirrorOfGlobalPairs
    (P : GlobalPair ψ hprojA hprojB δ)
    (P' : GlobalPair (ψ ∘ Prod.swap) hprojB hprojA δ)
    (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    MirrorSimul ψ MA MB (deltaS (Fintype.card F) δ ε) where
  Ea := (F × F) × CL.Answer F (4 * m) d 1
  instFintypeEa := inferInstance
  instDecEqEa := inferInstance
  Eb := (F × F) × CL.Answer F (4 * m) d 1
  instFintypeEb := inferInstance
  instDecEqEb := inferInstance
  Φ := (P.toSimulPair hm hd hψ hfail hq).Φ
  Φ_unit := (P.toSimulPair hm hd hψ hfail hq).Φ_unit
  Φ_reduced := (P.toSimulPair hm hd hψ hfail hq).Φ_reduced
  SA := (P.toSimulPair hm hd hψ hfail hq).SA
  SA_proj := (P.toSimulPair hm hd hψ hfail hq).SA_proj
  SB := (P.toSimulPair hm hd hψ hfail hq).SB
  SB_proj := (P.toSimulPair hm hd hψ hfail hq).SB_proj
  consA := (P.toSimulPair hm hd hψ hfail hq).consA
  consB := (P.toSimulPair hm hd hψ hfail hq).consB
  Φ' := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).Φ
  Φ'_unit := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).Φ_unit
  Φ'_reduced := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).Φ_reduced
  SA' := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).SA
  SA'_proj := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).SA_proj
  SB' := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).SB
  SB'_proj := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).SB_proj
  consA' := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).consA
  consB' := (P'.toSimulPair hm hd (swapVec_unit hψ) (povmValue_swapped_le hfail) hq).consB
  hmirror := hmirror_padState ψ

include hm in
/-- **`MirrorSimul` exists**: a legal projective strategy of the Pauli basis test of value
`1 - eps` has both cuts' simultaneous pair measurements, on one state. Running
`lem:qld-simultaneous` twice --- once at the strategy and once at the swapped strategy --- gives
the two cuts, and the states they carry are the same six-register state read two ways. This is
what makes `lem:qld-pauli-selfcons` and everything below it unconditional. -/
theorem exists_mirrorSimul (hm4 : 4 * m ∣ Fintype.card F) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε)
    (hpA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hpB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (hε : 0 ≤ ε)
    (hlegA : LegalSupport MA) (hlegB : LegalSupport MB) (hd : 1 ≤ d)
    (hq : 48 * m * d ≤ Fintype.card F) :
    Nonempty (MirrorSimul ψ MA MB
      (deltaS (Fintype.card F) (deltaLD (Fintype.card F) m d ε) ε)) := by
  obtain ⟨P⟩ := exists_globalPair hm hm4 hψ hfail hpA hpB hε hlegA hlegB hd
  obtain ⟨P'⟩ := exists_globalPair hm hm4 (swapVec_unit hψ) (povmValue_swapped_le hfail)
    hpB hpA hε hlegB hlegA hd
  exact ⟨mirrorOfGlobalPairs hm P P' hd hψ hfail hq⟩

end MIPRE.QLD

end
