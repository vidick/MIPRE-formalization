/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.HidingPrefix

/-! # Guarded coarse maps for the actual adjacent hiding test

The earlier fine label retains only its preceding prefix, current dual output,
and remaining tail. The next map uses the later prefix as a key. A separate
dummy outcome handles malformed answers and prefix mismatches, so each keyed
map is total on the entire answer alphabet and defines a complete measurement.
-/

noncomputable section

namespace MIPRE.Introspection.TypedEstimates

open Finset Matrix Classical

variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- The fine outcome retained at hiding level `k+1`. Off-format answers have
their own outcome; unused coordinates of a well-formed answer are discarded. -/
def hidingCoarse (P : CL.CLFun F ι ℓ) (k : ℕ) :
    ParsedAnswer (ι → F) A PauliAnswer → Option ((ι → F) × (ι → F) × (ι → F))
  | .hide y yp x => some (P.outputPrefix k y,
      CL.proj (P.factorOfPrefix k (P.outputPrefix k y)) yp,
      CL.proj (CLChecks.prefixRegister P (k + 1) y)ᶜ x)
  | _ => none

/-- Process a retained fine outcome using the later prefix. On a prefix
mismatch the output is the dummy label, rather than an incomplete family. -/
def hidingNextGuarded (P : CL.CLFun F ι ℓ) (k : ℕ) :
    Option (ι → F) → Option ((ι → F) × (ι → F) × (ι → F)) →
      Option ((ι → F) × (ι → F) × (ι → F))
  | some y, some (p, _, x) =>
      if p = P.outputPrefix k y then
        some (p, CLChecks.dualReadout P (k + 1) y x,
          CL.proj (CLChecks.prefixRegister P (k + 2) y)ᶜ x)
      else none
  | _, _ => none

/-- On matching prefixes, the new keyed map factors through exactly the
previous hiding label; no raw discarded tail coordinates are needed. -/
theorem hidingNextGuarded_factor {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y yp x z : ι → F)
    (hmatch : P.outputPrefix k y = P.outputPrefix k z) :
    hidingNextGuarded P k (some z) (hidingCoarse P k (.hide y yp x :
      ParsedAnswer (ι → F) A PauliAnswer)) =
        hidingNextEarlier P k (some z) (.hide y yp x :
          ParsedAnswer (ι → F) A PauliAnswer) := by
  have hreg := CLChecks.prefixRegister_congr hP k hmatch
  simp only [hidingNextGuarded, hidingCoarse, hreg, if_pos hmatch,
    CLChecks.dualReadout_proj_compl_prefix hP, hidingNextEarlier, Option.map_some,
    CLChecks.tail_proj_tail P z x (show k + 1 ≤ k + 2 by omega)]

/-- The actual parsed check implies equality of the guarded coarse outcomes.
No support or in-image hypothesis on the answers is used. -/
theorem hiding_next_accepts_guarded
    [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
    [Fintype F] [DecidableEq F] [Fintype A]
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
    hidingNextGuarded (L w) k.val (hidingNextLater (L w) k.val b).1
      (hidingCoarse (L w) k.val a) = (hidingNextLater (L w) k.val b).2 := by
  have hf := TypedPredicate.check_formats L X Z projectPauli D DP h
  cases a with
  | pauli a => simp [TypedPredicate.fits] at hf
  | pair y a => simp [TypedPredicate.fits] at hf
  | read y yp a => simp [TypedPredicate.fits] at hf
  | hide y yp x =>
    cases b with
    | pauli b => simp [TypedPredicate.fits] at hf
    | pair z b => simp [TypedPredicate.fits] at hf
    | read z zp b => simp [TypedPredicate.fits] at hf
    | hide z zp t =>
      have hc := TypedPredicate.check_hiding_next L X Z projectPauli D DP w k j hk h
      have hmatch : (L w).outputPrefix k.val y =
          (L w).outputPrefix k.val ((L w).outputPrefix (k.val + 1) z) := by
        rw [CLChecks.outputPrefix_outputPrefix hL z (by omega)]
        exact hc.1
      change hidingNextGuarded (L w) k.val (some ((L w).outputPrefix (k.val + 1) z))
        (hidingCoarse (L w) k.val _) = _
      rw [hidingNextGuarded_factor hL k.val y yp x _ hmatch]
      exact hiding_next_accepts_conditional L X Z projectPauli D DP w k j hk hL h

end MIPRE.Introspection.TypedEstimates

end
