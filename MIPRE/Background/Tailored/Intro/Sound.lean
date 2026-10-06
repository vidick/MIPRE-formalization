/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Typed
public import MIPRE.Background.Introspection.CanonicalComplete
public import MIPRE.Background.Introspection.DecisionKernelComplete
public import MIPRE.Tailored.Intro.Presentation

@[expose] public section

/-!
# Soundness of the tailored presentation of the introspection verifier

The typed tailored data of the introspection verifier at its canonical parameters (`tdata`), and
the soundness half of the presentation: on every edge, a pair of answers it accepts decodes
(`decT`, through the kernel's parsed answers) to a pair the typed predicate of the reference
verifier accepts (`tdata_sound`). The constraints say that the readable conditions hold and the
kernel's semantic check accepts (`Typed.consL_iff`); the kernel's completeness
(`DecisionKernel.program_complete`) turns that into acceptance by the kernel program on the
re-encoded answers, which is the typed predicate (`raw_accepts_iff`). Then
`valStar_presented_le` bounds the value of the detyped tailored game by that of the reference
verifier's detyped game (`valStar_tpresented_le`).
-/

namespace MIPRE.Tailored.Intro.Sound

open Cost CL MIPRE.SAT MIPRE.Introspection MIPRE.QLD SourceCompiler PauliSamplerParameters
open DecisionCompiler Typed Classical

variable (c : ℕ) (hc : 1 ≤ c) (hc2 : 2 ≤ c) (he : Even c) (lam n : ℕ)
  (T : TailoredVerifier 7) (V : Verifier 7) (hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n)
  (kg : ∀ S : Finset (Fin (registerBits c lam n)), CL.RegLinear 𝔽₂ S →
    List (Fin (registerBits c lam n) → 𝔽₂))

/-- The typed tailored data of the introspection verifier at its canonical parameters. -/
noncomputable def tdata :
    TypedData DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)) where
  lenR t := Typed.lenR (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) t
  lenL t := Typed.len (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) t -
    Typed.lenR (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) t
  cons u v aR bR := consL (fieldBits c lam n) (fieldBits_pos c lam n) (fieldBits_odd he lam n)
    (selectorBits c lam n) (CanonicalGame.divides c hc lam n) ((2 ^ n) ^ lam) T V hs kg u.1 v.1
    (toBits u.2) (toBits v.2) aR bR

/-- The decoding of a typed tailored answer: the kernel's parsed answer read off the layout,
re-encoded as the kernel's bytes. -/
noncomputable def decT (q : CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n))) (tb : BitStr) :
    Verifier.Answers (outerBound c lam n) :=
  CanonicalComplete.encodeAnswer c hc2 lam n
    (parsedT (fieldBits c lam n) (fieldBits_pos c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam)
      T V hs q.1 tb)

theorem lenR_le_len (k j R : ℕ) (t : DecisionKernel.Label) :
    Typed.lenR k j R t ≤ Typed.len k j R t := by
  rcases t with p | ⟨t, w⟩
  · simp only [Typed.lenR, Typed.len, PauliCons.pauliLenR]
    split_ifs <;> omega
  · cases t <;> simp [Typed.lenR, Typed.len, auxLenR, auxLen] <;> omega

/-- The readable conditions give the kernel's prefix guard and source-output condition. -/
theorem guards_of_readOK {k : ℕ} {hk : 1 ≤ k} [NeZero k] {j R : ℕ} {T : TailoredVerifier 7}
    {V : Verifier 7} {hs : V.sampler.dim (2 ^ n) ≤ 2 ^ 2 ^ j * k} {u : DecisionKernel.Label}
    {a : BitStr} (ha : a.length = Typed.len k j R u) (h : readOK k j R T V hs u a) :
    PrefixGuard.holds (AuxiliaryDecision.padded V hs) u (parsedT k hk j R T V hs u a) ∧
      AuxiliaryDecision.sourceOutput (V.sampler.dim (2 ^ n)) u
        (DecisionKernel.Answer.toRaw (shoupBinField k hk) (parsedT k hk j R T V hs u a)) := by
  rcases u with p | ⟨t, w⟩
  · exact ⟨trivial, trivial⟩
  · obtain ⟨-, hp, hsrc⟩ := h
    have hQ : 0 + Q k j ≤ a.length := by
      rw [ha]; cases t <;> simp [Typed.len, auxLen] <;> omega
    cases t with
    | introspect =>
      refine ⟨trivial, ?_⟩
      change SourceCompiler.InSource _ (toBits (reg (Q k j) a 0))
      rw [toBits_reg hQ]
      exact hsrc rfl
    | sample => exact ⟨trivial, trivial⟩
    | read => exact ⟨hp, trivial⟩
    | hide i => exact ⟨hp, trivial⟩

/-- The Pauli answers read off the layout are formatted. -/
theorem pauliFormatted_parsedT {k : ℕ} {hk : 1 ≤ k} [NeZero k] {hodd : Odd k} {j R : ℕ}
    {T : TailoredVerifier 7} {V : Verifier 7} {hs : V.sampler.dim (2 ^ n) ≤ 2 ^ 2 ^ j * k}
    (u : DecisionKernel.Label) (x a : BitStr) :
    DecisionKernel.Answer.PauliFormatted k hk hodd j (2 ^ 2 ^ j * k) R u x
      (parsedT k hk j R T V hs u a) := by
  intro t c' hu hc
  subst hu
  simp only [parsedT, ParsedAnswer.pauli.injEq] at hc
  subst hc
  exact DecisionKernel.Answer.pauliDecode_format k hk hodd j t x a

set_option maxRecDepth 4096 in
variable {c hc hc2 he lam n T V hs kg} in
/-- **Soundness on the edges**: a pair of answers the typed tailored data accepts decodes to a
pair the reference verifier's typed predicate accepts. -/
theorem tdata_sound (hkg : KerGens (registerBits c lam n) kg) (hacc : AcceptsAsInput T V n)
    (U : ClockedUniversalMachine) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (u v : CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n))) (ta tb : BitStr)
    (h : (tdata c hc he lam n T V hs kg).Accepts u v ta tb) :
    rawPredicate c hc he U (V.sampler.prog, V.decider.prog) lam n u v
      (decT c hc2 lam n T V hs u ta) (decT c hc2 lam n T V hs v tb) = true := by
  obtain ⟨hla, hlb, hcons⟩ := h
  have hla' : ta.length = Typed.len (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) u.1 := by
    rw [hla]; exact Nat.add_sub_cancel' (lenR_le_len _ _ _ _)
  have hlb' : tb.length = Typed.len (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) v.1 := by
    rw [hlb]; exact Nat.add_sub_cancel' (lenR_le_len _ _ _ _)
  obtain ⟨hra, hrb, hchk⟩ := (consL_iff hkg hacc u.1 v.1 (toBits u.2) (toBits v.2) ta tb
    hla' hlb').1 hcons
  obtain ⟨hga, hsa⟩ := guards_of_readOK n (hk := fieldBits_pos c lam n) hla' hra
  obtain ⟨hgb, hsb⟩ := guards_of_readOK n (hk := fieldBits_pos c lam n) hlb' hrb
  change (rawGame c hc he U (V.sampler.prog, V.decider.prog) lam n).D u v _ _ = true
  rw [raw_accepts_iff c hc he U V hV]
  have hR := originalBound_three_le_registerBits hc2 lam n
  rw [originalBound_eq] at hR ⊢
  exact DecisionKernel.program_complete U V hV hn (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n) (selectorBits c lam n) (selectorBits_le_fieldBits hc lam n)
    (CanonicalGame.divides c hc lam n) hs (four_le_registerBits hc2 lam n) hR u.1 v.1
    (toBits u.2) (toBits v.2) (length_toBits _) (length_toBits _) _ _
    (pauliFormatted_parsedT n _ _ _) (pauliFormatted_parsedT n _ _ _) hga hgb hsa hsb hchk

/-- The reference verifier's detyped game at index `n`. -/
noncomputable abbrev H (U : ClockedUniversalMachine) (V : Verifier 7) :=
  CL.Detyping.game graph (CL.Detyping.DeciderProgram.sourceFamily (extendedSampler c hc he lam) n)
    (rawPredicate c hc he U (V.sampler.prog, V.decider.prog) lam n)

set_option maxRecDepth 4096 in
variable {c hc he lam n T V hs kg} in
include hc2 in
/-- **Soundness of the presentation**: the detyped tailored game has `val*` at most the quantum
value of the reference verifier's detyped game. -/
theorem valStar_tpresented_le (hkg : KerGens (registerBits c lam n) kg)
    (hacc : AcceptsAsInput T V n) (U : ClockedUniversalMachine) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) :
    (presented graph (H c hc he lam n U V) (tdata c hc he lam n T V hs kg)).valStar ≤
      quantumValue (H c hc he lam n U V) :=
  valStar_presented_le graph (H c hc he lam n U V)
    (rawPredicate c hc he U (V.sampler.prog, V.decider.prog) lam n) (fun _ _ _ _ => rfl)
    (tdata c hc he lam n T V hs kg) (decT c hc2 lam n T V hs) ⟨[], by simp⟩
    fun u v a b _ h => tdata_sound (hc2 := hc2) hkg hacc U hV hn u v a b h

end MIPRE.Tailored.Intro.Sound

end
