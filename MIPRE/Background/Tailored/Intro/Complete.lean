/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.Sound
public import MIPRE.Tailored.Intro.PresentationTyped

@[expose] public section

/-!
# Completeness of the tailored presentation of the introspection verifier, on the edges

The honest answers of the introspection verifier are byte strings in the canonical format of
their label (`Layout.OkLayout`). The tailored presentation encodes them by the padded layout
(`Layout.enc`), and the parsed answer the constraints read off the encoding is the kernel's
decoding of the bytes (`parsedT_enc`). So on every edge, when the kernel accepts two such byte
answers whose encodings satisfy the readable conditions, the typed tailored data accepts the two
encodings (`tdata_complete`): the kernel's soundness (`DecisionKernel.program_sound`) gives its
semantic check on the decoded answers, which are the parsed encodings, and `Typed.consL_iff`
turns that into the constraints.
-/

namespace MIPRE.Tailored.Intro.Complete

open Cost CL MIPRE.SAT MIPRE.Introspection MIPRE.QLD SourceCompiler PauliSamplerParameters
open DecisionCompiler Typed AnswerParser Classical

/-! ## The parsed encoding -/

theorem win_left {u v : BitStr} {m : ℕ} (h : u.length = m) : win (u ++ v) 0 m = u := by
  simp [win, ← h]

theorem win_right {u v : BitStr} {o m : ℕ} (h : u.length = o) : win (u ++ v) o m = v.take m := by
  simp [win, ← h]

theorem take_pad_le {R : ℕ} {l : BitStr} {m : ℕ} (hm : l.length = m) (rest : BitStr) :
    (pad R l ++ rest).take m = l := by
  rw [List.take_append_of_le_length (by simp [pad]; omega), pad, List.take_left' hm]

variable (k : ℕ) (hk : 1 ≤ k) [NeZero k] (j R : ℕ) {n : ℕ} (T : TailoredVerifier 7)
  (V : Verifier 7) (hs : V.sampler.dim (2 ^ n) ≤ 2 ^ 2 ^ j * k)

/-- The layout's encoding at the instance's parameters. -/
noncomputable abbrev encL (u : DecisionKernel.Label) (bs : BitStr) : BitStr :=
  enc (Q k j) R (sR k j T V hs) u bs

/-- The layout's well-formedness at the instance's parameters. -/
abbrev OkL (u : DecisionKernel.Label) (bs : BitStr) : Prop :=
  OkLayout (Q k j) R (pauliLen (2 ^ j) k) (sR k j T V hs) (sL k j T V hs) u bs

omit [NeZero k] in
variable {k hk j R T V hs} in
/-- **The parsed encoding is the kernel's decoding.** -/
theorem parsedT_enc {u : DecisionKernel.Label} {bs : BitStr} (h : OkL k j R T V hs u bs) :
    parsedT k hk j R T V hs u (encL k j R T V hs u bs) =
      DecisionKernel.Answer.decode (shoupBinField k hk) (2 ^ j) (Q k j) R u bs := by
  rcases u with p | ⟨t, w⟩
  · rfl
  · cases t with
    | introspect =>
      obtain ⟨y, α, rfl, hy, h1, h2, h3⟩ := h
      rw [encL, enc_pair (Or.inl rfl) hy]
      have hr : (α.take (sR k j T V hs (.introspect, w) y)).length =
          sR k j T V hs (.introspect, w) y := by simp; omega
      have hl : (α.drop (sR k j T V hs (.introspect, w) y)).length =
          sL k j T V hs (.introspect, w) y := by simp; omega
      have hpl : (pad R (α.take (sR k j T V hs (.introspect, w) y))).length = R :=
        length_pad (by omega)
      have hy0 : win (y ++ pad R (α.take (sR k j T V hs (.introspect, w) y)) ++
          pad R (α.drop (sR k j T V hs (.introspect, w) y))) 0 (Q k j) = y := by
        rw [List.append_assoc, win_left hy]
      simp only [parsedT, parsed, reg, srcAns, srcOffL, hy0]
      rw [List.append_assoc, win_right hy, take_pad_le hr,
        show Q k j + R = y.length + (pad R (α.take (sR k j T V hs (.introspect, w) y))).length by
          rw [hy, hpl], ← List.append_assoc, win_right (by simp), pad,
        List.take_left' hl, List.take_append_drop]
      simp [DecisionKernel.Answer.decode, AuxiliaryAnswer.decode, pairParts_pairBits _ y α hy,
        ParsedAnswer.mapAnswer, ParsedAnswer.mapPauli]
    | sample =>
      obtain ⟨y, α, rfl, hy, h1, h2, h3⟩ := h
      rw [encL, enc_pair (Or.inr rfl) hy]
      have hr : (α.take (sR k j T V hs (.sample, w) y)).length =
          sR k j T V hs (.sample, w) y := by simp; omega
      have hl : (α.drop (sR k j T V hs (.sample, w) y)).length =
          sL k j T V hs (.sample, w) y := by simp; omega
      have hpl : (pad R (α.take (sR k j T V hs (.sample, w) y))).length = R :=
        length_pad (by omega)
      have hy0 : win (y ++ pad R (α.take (sR k j T V hs (.sample, w) y)) ++
          pad R (α.drop (sR k j T V hs (.sample, w) y))) 0 (Q k j) = y := by
        rw [List.append_assoc, win_left hy]
      simp only [parsedT, parsed, reg, srcAns, srcOffL, hy0]
      rw [List.append_assoc, win_right hy, take_pad_le hr,
        show Q k j + R = y.length + (pad R (α.take (sR k j T V hs (.sample, w) y))).length by
          rw [hy, hpl], ← List.append_assoc, win_right (by simp), pad,
        List.take_left' hl, List.take_append_drop]
      simp [DecisionKernel.Answer.decode, AuxiliaryAnswer.decode, pairParts_pairBits _ y α hy,
        ParsedAnswer.mapAnswer, ParsedAnswer.mapPauli]
    | read =>
      obtain ⟨y, yp, α, rfl, hy, hyp, h1, h2, h3⟩ := h
      have he : encL k j R T V hs (.inr (.read, w)) (tripleBits y yp α) =
          y ++ (pad R (α.take (sR k j T V hs (.read, w) y)) ++
            (yp ++ pad R (α.drop (sR k j T V hs (.read, w) y)))) := by
        simp [encL, enc, tripleParts_tripleBits _ y yp α hy hyp]
      rw [he]
      have hr : (α.take (sR k j T V hs (.read, w) y)).length =
          sR k j T V hs (.read, w) y := by simp; omega
      have hl : (α.drop (sR k j T V hs (.read, w) y)).length =
          sL k j T V hs (.read, w) y := by simp; omega
      have hpl : (pad R (α.take (sR k j T V hs (.read, w) y))).length = R :=
        length_pad (by omega)
      have hy0 : win (y ++ (pad R (α.take (sR k j T V hs (.read, w) y)) ++
          (yp ++ pad R (α.drop (sR k j T V hs (.read, w) y))))) 0 (Q k j) = y := win_left hy
      simp only [parsedT, parsed, reg, srcAns, srcOffL, hy0]
      set p1 := pad R (α.take (sR k j T V hs (.read, w) y))
      set p2 := pad R (α.drop (sR k j T V hs (.read, w) y))
      have w1 : win (y ++ (p1 ++ (yp ++ p2))) (Q k j) (sR k j T V hs (.read, w) y) =
          α.take (sR k j T V hs (.read, w) y) := by
        rw [win_right hy, take_pad_le hr]
      have w2 : win (y ++ (p1 ++ (yp ++ p2))) (Q k j + R) (Q k j) = yp := by
        rw [show y ++ (p1 ++ (yp ++ p2)) = (y ++ p1) ++ (yp ++ p2) by simp,
          win_right (by simp [hy, hpl]), List.take_left' hyp]
      have w3 : win (y ++ (p1 ++ (yp ++ p2))) (2 * Q k j + R) (sL k j T V hs (.read, w) y) =
          α.drop (sR k j T V hs (.read, w) y) := by
        rw [show y ++ (p1 ++ (yp ++ p2)) = (y ++ p1 ++ yp) ++ p2 by simp,
          win_right (by simp [hy, hpl, hyp]; ring), ← List.append_nil p2, take_pad_le hl]
      rw [w1, w2, w3, List.take_append_drop]
      simp [DecisionKernel.Answer.decode, AuxiliaryAnswer.decode,
        tripleParts_tripleBits _ y yp α hy hyp, ParsedAnswer.mapAnswer, ParsedAnswer.mapPauli]
    | hide i =>
      obtain ⟨y, yp, x, rfl, hy, hyp, hx⟩ := h
      have he : encL k j R T V hs (.inr (.hide i, w)) (tripleBits y yp x) = y ++ (yp ++ x) := by
        simp [encL, enc, tripleParts_tripleBits _ y yp x hy hyp]
      rw [he]
      simp only [parsedT, parsed, reg]
      rw [win_left hy, win_right hy, List.take_left' hyp,
        show 2 * Q k j = (y ++ yp).length by simp [hy, hyp]; ring, ← List.append_assoc,
        win_right rfl, List.take_of_length_le hx.le]
      simp [DecisionKernel.Answer.decode, AuxiliaryAnswer.decode,
        tripleParts_tripleBits _ y yp x hy hyp, ParsedAnswer.mapAnswer, ParsedAnswer.mapPauli]

omit [NeZero k] in
variable {k j R T V hs} in
/-- Well-formed answers encode to the label's length. -/
theorem length_encL {u : DecisionKernel.Label} {bs : BitStr} (h : OkL k j R T V hs u bs) :
    (encL k j R T V hs u bs).length = Typed.len k j R u := by
  rw [encL, length_enc_of_ok (pread := pauliRead) h]
  rcases u with p | ⟨t, w⟩
  · simp only [Intro.lenR, Intro.lenL, Typed.len]
    split_ifs <;> simp
  · cases t <;> simp [Intro.lenR, Intro.lenL, Typed.len, auxLen] <;> ring

/-! ## The edges -/

variable (c : ℕ) (hc : 1 ≤ c) (hc2 : 2 ≤ c) (he : Even c) (lam : ℕ)
  (kg : ∀ S : Finset (Fin (registerBits c lam n)), CL.RegLinear 𝔽₂ S →
    List (Fin (registerBits c lam n) → 𝔽₂))

/-- The encoding of a byte answer at a typed question. -/
noncomputable def encT (hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n)
    (q : CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a : Verifier.Answers (outerBound c lam n)) : BitStr :=
  encL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) T V hs q.1 a.1

/-- The encodable byte answers at a typed question: well formed, with the readable conditions
at their encoding. -/
def okT (hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n)
    (q : CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a : Verifier.Answers (outerBound c lam n)) : Prop :=
  OkL (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) T V hs q.1 a.1 ∧
    readOK (fieldBits c lam n) (selectorBits c lam n) ((2 ^ n) ^ lam) T V hs q.1
      (encT T V c lam hs q a)

set_option maxRecDepth 4096 in
variable {T V c hc he lam kg} in
include hc2 in
/-- **Completeness on the edges**: when the reference verifier's typed predicate accepts two
encodable byte answers, the typed tailored data accepts their encodings. -/
theorem tdata_complete {hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n}
    (hkg : KerGens (registerBits c lam n) kg) (hacc : AcceptsAsInput T V n)
    (U : ClockedUniversalMachine) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (u v : CL.Detyping.Question DecisionKernel.Label (Fin (PauliSampler.dimension c lam n)))
    (a b : Verifier.Answers (outerBound c lam n)) (ha : okT T V c lam hs u a)
    (hb : okT T V c lam hs v b)
    (h : rawPredicate c hc he U (V.sampler.prog, V.decider.prog) lam n u v a b = true) :
    (Sound.tdata c hc he lam n T V hs kg).Accepts u v (encT T V c lam hs u a)
      (encT T V c lam hs v b) := by
  change (rawGame c hc he U (V.sampler.prog, V.decider.prog) lam n).D u v a b = true at h
  rw [raw_accepts_iff c hc he U V hV] at h
  have hR := originalBound_three_le_registerBits hc2 lam n
  rw [originalBound_eq] at hR h
  have hchk := DecisionKernel.program_sound U V hV hn (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n) (selectorBits c lam n) (selectorBits_le_fieldBits hc lam n)
    (CanonicalGame.divides c hc lam n) hs (four_le_registerBits hc2 lam n) hR u.1 v.1
    (toBits u.2) (toBits v.2) a.1 b.1 h
  rw [← parsedT_enc ha.1, ← parsedT_enc hb.1] at hchk
  have hla := length_encL ha.1
  have hlb := length_encL hb.1
  refine ⟨?_, ?_, (consL_iff hkg hacc u.1 v.1 (toBits u.2) (toBits v.2) _ _ hla hlb).2
    ⟨ha.2, hb.2, hchk⟩⟩
  · rw [encT, hla]; exact (Nat.add_sub_cancel' (Sound.lenR_le_len _ _ _ _)).symm
  · rw [encT, hlb]; exact (Nat.add_sub_cancel' (Sound.lenR_le_len _ _ _ _)).symm

set_option maxRecDepth 4096 in
variable {T V c hc he lam kg} in
include hc2 in
/-- **Completeness of the presentation**: a perfect PCC strategy of the reference verifier's
typed game that charges only encodable answers, whose bit observables along the encoding are
signed permutations, diagonal at the readable bits, gives a perfect ZPC strategy of the doubled
detyped tailored game. -/
theorem hasPerfectZPC_tpresented {hs : V.sampler.dim (2 ^ n) ≤ registerBits c lam n}
    (hkg : KerGens (registerBits c lam n) kg) (hacc : AcceptsAsInput T V n)
    (U : ClockedUniversalMachine) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (R : SyncStrategy (rawGame c hc he U (V.sampler.prog, V.decider.prog) lam n).doubled)
    (hR : R.IsPCC) (hval : R.value = 1)
    (hsupp : ∀ q a, ¬okT T V c lam hs q.2 a → R.P.M q a = 0)
    (hperm : ∀ q (i : ℕ), IsSignedPerm
      (pvmObs (R.P.M q) fun a => bitSign ((encT T V c lam hs q.2 a).getD i false)))
    (hdiag : ∀ q (i : ℕ), i < (Sound.tdata c hc he lam n T V hs kg).lenR q.2.1 →
      (pvmObs (R.P.M q) fun a => bitSign ((encT T V c lam hs q.2 a).getD i false)).IsDiag) :
    (presented graph (Sound.H c hc he lam n U V)
      (Sound.tdata c hc he lam n T V hs kg)).doubled.HasPerfectZPC :=
  hasPerfectZPC_presented_typed graph (TypeGraph.symmetric QLD.adj (.pauli .X) (.pauli .Z))
    (TypeGraph.edges_nonempty QLD.adj (.pauli .X) (.pauli .Z) 7)
    (CL.Detyping.DeciderProgram.sourceFamily (extendedSampler c hc he lam) n)
    (fun w t => (extendedSampler c hc he lam).cl_exactlyOn n (Player.ofBool w) t) (by decide)
    (rawPredicate c hc he U (V.sampler.prog, V.decider.prog) lam n)
    (Sound.tdata c hc he lam n T V hs kg) (encT T V c lam hs) (okT T V c lam hs) ⟨[], by simp⟩
    (fun u a ha => (length_encL ha.1).trans (Nat.add_sub_cancel' (Sound.lenR_le_len _ _ _ _)).symm)
    (fun u v a b _ ha hb h => tdata_complete hc2 hkg hacc U hV hn u v a b ha hb h)
    R hR hval hsupp hperm hdiag

end MIPRE.Tailored.Intro.Complete

end
