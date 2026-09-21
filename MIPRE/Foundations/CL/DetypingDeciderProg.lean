/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingDeciderRoute
import MIPRE.Foundations.CL.DetypingProgSampler
import MIPRE.Foundations.Verifier

/-! # Executable detyping of the decision predicate

The compiler first queries the supplied typed sampler for its dimension, then
runs the supplied cutoff routine, and finally applies the graph router. Both
the original answers and the original index are retained. The cutoff routine
is an actual program: its bounds need not be polynomial in the binary index.
-/

noncomputable section

namespace MIPRE.CL.Detyping

set_option linter.unusedSectionVars false

open Cost Cost.PolyTimeFun Program

/-- A typed decider uses the source's seven-field input convention. -/
structure TypedDecider (T : Type*) [SizedEncoding T] where
  prog : Prog
  closed : prog.WellScoped 1

namespace TypedDecider

def Accepts {T : Type*} [SizedEncoding T] (D : TypedDecider T)
    (n : ℕ) (u : T) (x : BitStr) (v : T) (y a b : BitStr) : Prop :=
  ∃ time, D.prog.Runs (encode (n, u, x, v, y, a, b)) (encode true) time

def Total {T : Type*} [SizedEncoding T] (D : TypedDecider T) : Prop :=
  ∀ (n : ℕ) (d : Data), Halts D.prog (.cons (encode n) d)

end TypedDecider

/-- An executable pair of answer bounds. The inner bound is the source typed
game's cutoff for its entire answer; the outer bound applies even on nonedge views. -/
structure CutoffProgram where
  inner : ℕ → ℕ
  outer : ℕ → ℕ
  prog : Prog
  closed : prog.WellScoped 1
  runs : ∀ n, ∃ time, prog.Runs (encode n) (encode (inner n, outer n)) time

namespace DeciderProgram

variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

def pairPost : PolyTimeFun (Data × Data) Data := treePair

def dimensionRoute : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair
    (ap₂ treePair (encoded.comp (readNat.comp treeHead)) (const Data.nil)) (PolyTimeFun.id Data))

def cutoffRoute : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair
    (encoded.comp (readNat.comp (treeHead.comp treeHead))) (PolyTimeFun.id Data))

def dimensionStage : Prog := Prog.routeOneCall dimensionRoute S.prog pairPost
def cutoffStage : Prog := Prog.routeOneCall cutoffRoute C.prog pairPost
def decisionStage : Prog := Prog.routeOneCall (route E) D.prog post

theorem dimensionStage_closed : (dimensionStage S).WellScoped 1 :=
  Prog.routeOneCall_closed _ S.closed _
theorem cutoffStage_closed : (cutoffStage C).WellScoped 1 :=
  Prog.routeOneCall_closed _ C.closed _
theorem decisionStage_closed : (decisionStage E D).WellScoped 1 :=
  Prog.routeOneCall_closed _ D.closed _

def prog : Prog := .let_ (dimensionStage S) (.let_ (cutoffStage C) (decisionStage E D))

theorem prog_closed : (prog E S D C).WellScoped 1 :=
  ⟨dimensionStage_closed S, (cutoffStage_closed C).mono (by omega) _,
    (decisionStage_closed E D).mono (by omega) _⟩

theorem dimensionStage_runs (input : Data) :
    ∃ time, (dimensionStage S).Runs input
      (.cons input (encode (S.dim (readNat (treeHead input))))) time := by
  obtain ⟨time, hr⟩ := S.runs_dimension (readNat (treeHead input))
  exact Prog.routeOneCall_indirect dimensionRoute S.closed pairPost input _ input _ time rfl hr

theorem cutoffStage_runs (input : Data) (s : ℕ) :
    ∃ time, (cutoffStage C).Runs (.cons input (encode s))
      (context input s (C.inner (readNat (treeHead input)))
        (C.outer (readNat (treeHead input)))) time := by
  obtain ⟨time, hr⟩ := C.runs (readNat (treeHead input))
  exact Prog.routeOneCall_indirect cutoffRoute C.closed pairPost _ _ _ _ time rfl hr

theorem decisionStage_direct (c r : Data) (h : route E c = (false, r)) :
    ∃ time, (decisionStage E D).Runs c r time :=
  Prog.routeOneCall_direct _ _ _ _ _ h

theorem decisionStage_indirect (c arg ctx r : Data) (time : ℕ)
    (h : route E c = (true, .cons arg ctx)) (hr : D.prog.Runs arg r time) :
    ∃ time, (decisionStage E D).Runs c (post (ctx, r)) time :=
  Prog.routeOneCall_indirect _ D.closed _ _ _ _ _ time h hr

theorem decisionStage_halts (hD : D.Total) (c : Data) : Halts (decisionStage E D) c := by
  cases h : route E c with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨time, hr⟩ := decisionStage_direct E D c payload h
      exact ⟨_, time, hr⟩
    | true =>
      obtain ⟨d, ctx, rfl⟩ := route_preserves E c payload h
      obtain ⟨r, time, hr⟩ := hD (indexReader c) d
      obtain ⟨t, ht⟩ := decisionStage_indirect E D c _ ctx r time h hr
      exact ⟨_, t, ht⟩

/-- Prefixing the two executable index routines to any decision-stage run. -/
theorem prog_runs (input r : Data) (time : ℕ)
    (h : (decisionStage E D).Runs
      (context input (S.dim (readNat (treeHead input)))
        (C.inner (readNat (treeHead input))) (C.outer (readNat (treeHead input)))) r time) :
    ∃ t, (prog E S D C).Runs input r t := by
  obtain ⟨ts, hs⟩ := dimensionStage_runs S input
  obtain ⟨tc, hc⟩ := cutoffStage_runs C input (S.dim (readNat (treeHead input)))
  exact ⟨_, Eval.let_ hs (Eval.append_of_wellScoped
    (Eval.let_ hc (Eval.append_of_wellScoped h (decisionStage_closed E D) _))
      ⟨cutoffStage_closed C, (decisionStage_closed E D).mono (by omega) _⟩ _)⟩

/-- The compiled program halts on every raw data tree, including malformed indices. -/
theorem prog_halts (hD : D.Total) (input : Data) : Halts (prog E S D C) input := by
  obtain ⟨r, time, hr⟩ := decisionStage_halts E D hD
    (context input (S.dim (readNat (treeHead input)))
      (C.inner (readNat (treeHead input))) (C.outer (readNat (treeHead input))))
  obtain ⟨t, ht⟩ := prog_runs E S D C input r time hr
  exact ⟨r, t, ht⟩

/-- A genuine ambient decider, built from executable source programs. -/
def decider : MIPRE.Decider where
  prog := prog E S D C
  closed := prog_closed E S D C

end DeciderProgram
end MIPRE.CL.Detyping
