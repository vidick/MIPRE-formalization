/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.Family
import MIPRE.Background.AnswerReduction.AnswerFormat

/-!
# The typed answer-reduced game

Piece AR-3c of `planning/answer-reduction.md`, concluded: the game of the typed answer-reduced
verifier `V̂^ar` at one index, in the vocabulary the detyping compiler consumes
(`MIPRE.CL.Detyping.typedGame`), with bit-string answers.

* The types are `Role × PcpTy`, on the complete type graph with loops (`graph`), as for the
  oracularized verifier.
* The CL functions are the binary family `cl` of `MIPRE/Background/AnswerReduction/Family`, the
  same for both players.
* The predicate (`typedPred`) parses both answers by their types (`parse`), rejects a failed
  parse, and otherwise decides by the answer-reduced predicate `accepts` on the decoded questions
  (`decodeQ`: the type, the oracle half, and the PCP half read back over `F_q`).
* The game check (`gameCheck`) runs the PCP verifier of a `SAT.PcpDecider` on the input verifier's
  question pair, read off the oracle half by the input sampler's two CL functions, and the view
  `(z, α)` in the `k`-bit representation the PCP reads.

`accepts_of_typedPred` and `typedPred_enc` are the two directions AR-4 and AR-5 need: acceptance of
the bit-string predicate is acceptance of `accepts` after the parse, and `accepts` on answers of
the right format is acceptance of their honest encodings.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL SAT Pcp Cost

/-- The types of the answer-reduced verifier. -/
abbrev ArTy := Role × PcpTy

/-- The complete type graph on the answer-reduced types, loops included. -/
def graph : ArTy → ArTy → Prop := fun _ _ => True

instance : DecidableRel graph := fun _ _ => isTrue trivial

theorem mem_graph_edges (p : ArTy × ArTy) : p ∈ CL.Graph.edges graph := by
  simp only [CL.Graph.edges, Finset.mem_filter]
  exact ⟨by simp, trivial⟩

instance : Nonempty LIDT.CL.Ty := ⟨.point⟩

-- The kernel unfolds the `Finset.univ` of the 54 types while checking this; the default depth
-- does not suffice.
set_option maxRecDepth 10000 in
theorem graph_nonempty : (CL.Graph.edges graph).Nonempty :=
  ⟨Classical.arbitrary _, mem_graph_edges _⟩

variable {ℓ : ℕ} (V : Verifier (ℓ + 1)) (n : ℕ) (P : PcpParams) (hk : 1 ≤ P.k)

/-- The field of the PCP with its `k`-bit representation. -/
abbrev fld : BinField P.k := shoupBinField P.k hk

/-- A typed question of the answer-reduced verifier, decoded: the type, the oracle half and the
PCP half. -/
def decodeQ (p : Detyping.Question ArTy (Fin (dim V n P))) :
    Q P (Fq P hk) (Fin (V.sampler.dim n) → 𝔽₂) :=
  (p.1, oraclePart V n P p.2, pcpPart V n P hk p.2)

/-- **The game check**: the PCP verifier of `PD`, with the input decider `D` and the parameters
`(n, T, Q, σ)`, on the input question pair read off the oracle half and the view `(z, α)`. -/
def gameCheck (PD : PcpDecider) (D : Prog) (T Qn σ : ℕ) (x : Fin (V.sampler.dim n) → 𝔽₂)
    (z : Fin P.m' → Fq P hk) (α : Fin (P.m' + 6) → Fq P hk) : Bool :=
  PD.verify (pcpInput D n T Qn σ (toBits ((V.sampler.cl n .alice).eval x))
    (toBits ((V.sampler.cl n .bob).eval x)) ((fld P hk).vecBits z) ((fld P hk).vecBits α))

variable [NeZero P.m] {hm : P.m ∣ Fintype.card (Fq P hk)} {hm' : P.m' ∣ Fintype.card (Fq P hk)}
  (S : LIDT.CL.Sel (Fq P hk) P.m hm) (S' : LIDT.CL.Sel (Fq P hk) P.m' hm')
  (check : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) →
    Bool)

/-- **The typed answer-reduced predicate** on bit-string answers of length at most `B`. -/
def typedPred (B : ℕ) (p q : Detyping.Question ArTy (Fin (dim V n P)))
    (a b : Verifier.Answers B) : Bool :=
  match parse (fld P hk) p.1.2 a.1, parse (fld P hk) q.1.2 b.1 with
  | some u, some v => accepts S S' check (decodeQ V n P hk p) (decodeQ V n P hk q) u v
  | _, _ => false

/-- **The typed answer-reduced game** at index `n`, with answers of length at most `B`. -/
def typedGame (B : ℕ) :=
  Detyping.typedGame graph graph_nonempty (fun _ => cl V n P hk S S')
    (typedPred V n P hk S S' check B)

/-- Acceptance of the bit-string predicate is acceptance of `accepts` after the parse. -/
theorem accepts_of_typedPred {B : ℕ} {p q : Detyping.Question ArTy (Fin (dim V n P))}
    {a b : Verifier.Answers B} (h : typedPred V n P hk S S' check B p q a b = true) :
    ∃ u v, parse (fld P hk) p.1.2 a.1 = some u ∧ parse (fld P hk) q.1.2 b.1 = some v ∧
      accepts S S' check (decodeQ V n P hk p) (decodeQ V n P hk q) u v = true := by
  unfold typedPred at h
  split at h
  · rename_i u v hu hv
    exact ⟨u, v, hu, hv, h⟩
  · cases h

theorem ansFmt_of_accepts {X : Type*}
    {check' : X → (Fin P.m' → Fq P hk) → (Fin (P.m' + 6) → Fq P hk) → Bool}
    {p q : AnswerReduction.Q P (Fq P hk) X} {u v : Ans P (Fq P hk)}
    (h : accepts S S' check' p q u v = true) :
    ansFmt p.1.2 u = true ∧ ansFmt q.1.2 v = true := by
  simp only [accepts, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2⟩

/-- `accepts` on two answers is acceptance of their honest encodings. -/
theorem typedPred_enc {B : ℕ} {p q : Detyping.Question ArTy (Fin (dim V n P))}
    {u v : Ans P (Fq P hk)}
    (h : accepts S S' check (decodeQ V n P hk p) (decodeQ V n P hk q) u v = true)
    (hu : (enc (fld P hk) u).length ≤ B) (hv : (enc (fld P hk) v).length ≤ B) :
    typedPred V n P hk S S' check B p q ⟨enc (fld P hk) u, hu⟩ ⟨enc (fld P hk) v, hv⟩
      = true := by
  obtain ⟨hfu, hfv⟩ := ansFmt_of_accepts P hk S S' h
  have hfu' : ansFmt p.1.2 u = true := hfu
  have hfv' : ansFmt q.1.2 v = true := hfv
  simp only [typedPred]
  rw [parse_enc (fld P hk) hfu', parse_enc (fld P hk) hfv']
  exact h

end MIPRE.AnswerReduction

end
