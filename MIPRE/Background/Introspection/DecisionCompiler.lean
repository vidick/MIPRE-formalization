/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Background.Introspection.DecisionCompilerRoute
import MIPRE.Background.Introspection.DecisionCompilerZero
import MIPRE.Foundations.Introspection.SourceDescriptionCompiler
import MIPRE.Foundations.Introspection.DecisionPreparationBound

/-! # The actual compiled introspection decider

Compilation clamps each source description, specializes the fixed prepared
kernel using binary metadata, and adds zero-parameter and zero-index branches.
The positive branch computes its clock and canonical resources exactly once.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionCompiler
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open DecisionPreparation (Metadata)

set_option maxRecDepth 4096

def positiveCompiler (c : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun Metadata Prog :=
  DecisionPreparation.compiler c (untypedKernel U)

def typedDecider (c : ℕ) (U : ClockedUniversalMachine) (M : Metadata) :
    CL.Detyping.TypedDecider DecisionKernel.Label :=
  ⟨DecisionPreparation.compiler c (DecisionKernel.program U) M,
    DecisionPreparation.compiler_closed c (DecisionKernel.program U) M⟩

theorem typedDecider_total (c : ℕ) (U : ClockedUniversalMachine) (M : Metadata) :
    (typedDecider c U M).Total := by
  intro n d
  obtain ⟨t,hr⟩ := DecisionPreparation.compiler_runs c (DecisionKernel.program U) M
    (.cons (encode n) d)
  exact ⟨_,t,hr⟩

theorem typedDecider_accepts (c : ℕ) (U : ClockedUniversalMachine) (M : Metadata)
    (n : ℕ) (T W : DecisionKernel.Label) (x y a b : BitStr) :
    (typedDecider c U M).Accepts n T x W y a b ↔
      DecisionKernel.program U (DecisionPreparation.kernelInput c M (encode (n,T,x,W,y,a,b))) = true := by
  obtain ⟨t,hr⟩ := DecisionPreparation.compiler_runs c (DecisionKernel.program U) M
    (encode (n,T,x,W,y,a,b))
  change (typedDecider c U M).prog.Runs (encode (n,T,x,W,y,a,b))
    (encode (DecisionKernel.program U
      (DecisionPreparation.kernelInput c M (encode (n,T,x,W,y,a,b))))) t at hr
  constructor
  · rintro ⟨t',hr'⟩
    exact encode_injective (hr.deterministic hr').1
  · intro h
    exact ⟨t,by rw [h] at hr; exact hr⟩

def selectedCompiler (c : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun Metadata Prog :=
  ite (AuxiliaryProgram.equal snd (const 0)) (const zeroProg)
    (zeroWrapCompiler.comp (positiveCompiler c U))

/-- Both the transformation and its source-description clamp are executable
polynomial-time functions on the binary compiler input. -/
def compute (c : ℕ) (U : ClockedUniversalMachine) : PolyTimeFun Metadata Prog :=
  SourceDescriptionCompiler.compiler (selectedCompiler c U)

@[simp] theorem selectedCompiler_apply (c : ℕ) (U : ClockedUniversalMachine) (M : Metadata) :
    selectedCompiler c U M = if M.2 = 0 then zeroProg else zeroWrap (positiveCompiler c U M) := by
  simp [selectedCompiler, PolyTimeFun.ite_apply, AuxiliaryProgram.equal_iff]

theorem compute_apply (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog) (lam : ℕ) :
    compute c U ((S,D),lam) = if lam = 0 then zeroProg else
      zeroWrap (positiveCompiler c U (SourceDescriptionCompiler.clamp ((S,D),lam))) := by
  simp only [compute, SourceDescriptionCompiler.compiler, comp_apply, selectedCompiler_apply]
  rfl

theorem compute_closed (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog) (lam : ℕ) :
    (compute c U ((S,D),lam)).WellScoped 1 := by
  rw [compute_apply]
  split_ifs
  · exact zeroProg_closed
  · exact zeroWrap_closed (DecisionPreparation.compiler_closed c (untypedKernel U) _)

def decider (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog) (lam : ℕ) : MIPRE.Decider :=
  ⟨compute c U ((S,D),lam),compute_closed c U S D lam⟩

theorem positive_runs (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (d : Data) :
    ∃ t, (decider c U S D lam).prog.Runs (.cons (encode n) d)
      (encode (untypedKernel U (DecisionPreparation.kernelInput c
        (SourceDescriptionCompiler.clamp ((S,D),lam)) (.cons (encode n) d)))) t := by
  obtain ⟨t,hr⟩ := DecisionPreparation.compiler_runs c (untypedKernel U)
    (SourceDescriptionCompiler.clamp ((S,D),lam)) (.cons (encode n) d)
  change (positiveCompiler c U _).Runs _ _ t at hr
  unfold decider
  simp only [compute_apply, if_neg (by omega : lam ≠ 0)]
  exact ⟨_,zeroWrap_runs_pos (DecisionPreparation.compiler_closed c (untypedKernel U) _) hn d _ t hr⟩

theorem zero_runs (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    (lam n : ℕ) (h : lam = 0 ∨ n = 0) (d : Data) :
    ∃ t, (decider c U S D lam).prog.Runs (.cons (encode n) d) (encode (zeroTest d)) t := by
  change ∃ t, (compute c U ((S,D),lam)).Runs _ _ t
  rw [compute_apply]
  by_cases hl : lam = 0
  · rw [if_pos hl]
    obtain ⟨t,_,hr⟩ := zeroProg_runs (encode n) d
    exact ⟨t,hr⟩
  · rw [if_neg hl]
    have hn : n = 0 := h.resolve_left hl
    subst n
    obtain ⟨t,_,hr⟩ := zeroWrap_runs_zero (positiveCompiler c U _) d
    exact ⟨t,hr⟩

theorem decider_total (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    (lam n : ℕ) (d : Data) : Halts (decider c U S D lam).prog (.cons (encode n) d) := by
  by_cases h : lam = 0 ∨ n = 0
  · obtain ⟨t,hr⟩ := zero_runs c U S D lam n h d
    exact ⟨_,t,hr⟩
  · push_neg at h
    obtain ⟨t,hr⟩ := positive_runs c U S D (by omega : 1 ≤ lam) (by omega : 1 ≤ n) d
    exact ⟨_,t,hr⟩

theorem accepts_positive (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (x y a b : BitStr) :
    (decider c U S D lam).Accepts n x y a b ↔
      untypedKernel U (DecisionPreparation.kernelInput c
        (SourceDescriptionCompiler.clamp ((S,D),lam)) (encode (n,x,y,a,b))) = true := by
  obtain ⟨t,hr⟩ := positive_runs c U S D hl hn (encode (x,y,a,b))
  have he : Data.cons (encode n) (encode (x,y,a,b)) = encode (n,x,y,a,b) := rfl
  rw [he] at hr
  constructor
  · rintro ⟨t',hr'⟩
    exact encode_injective (hr.deterministic hr').1
  · intro h
    exact ⟨t,by rw [h] at hr; exact hr⟩

theorem accepts_zero (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    (lam n : ℕ) (h : lam = 0 ∨ n = 0) (x y a b : BitStr) :
    (decider c U S D lam).Accepts n x y a b ↔
      x = [] ∧ y = [] ∧ a.length ≤ 2 ∧ b.length ≤ 2 := by
  obtain ⟨t,hr⟩ := zero_runs c U S D lam n h (encode (x,y,a,b))
  change (decider c U S D lam).prog.Runs (encode (n,x,y,a,b))
    (encode (zeroTest (encode (x,y,a,b)))) t at hr
  rw [← zeroTest_encode]
  constructor
  · rintro ⟨t',hr'⟩
    exact encode_injective (hr.deterministic hr').1
  · intro hz
    exact ⟨t,by rw [hz] at hr; exact hr⟩

def cutoffAt (c lam n : ℕ) : ℕ := if lam = 0 ∨ n = 0 then 2 else
  answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n)

theorem accepts_positive_bounds (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (x y a b : BitStr)
    (h : (decider c U S D lam).Accepts n x y a b) :
    x.length = CL.Detyping.graphDim DecisionKernel.Label +
      (3*SourceCompiler.registerPower c lam n+3)*SourceCompiler.fieldBits c lam n ∧
    y.length = CL.Detyping.graphDim DecisionKernel.Label +
      (3*SourceCompiler.registerPower c lam n+3)*SourceCompiler.fieldBits c lam n ∧
    a.length ≤ answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n) ∧
    b.length ≤ answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n) := by
  have hh := (accepts_positive c U S D hl hn x y a b).mp h
  have hi : ClockSimulation.indexReader (encode (n,x,y,a,b)) = n := readNat_encode n
  dsimp only [DecisionPreparation.kernelInput] at hh
  have hM : (SourceDescriptionCompiler.clamp ((S,D),lam)).2 = lam := rfl
  rw [hi,hM] at hh
  have he := (untypedKernel_iff U n x y a b _ _ _ _ _ _).mp hh
  simpa only [PauliSamplerParameters.parameters, length_unary] using
    (show _ ∧ _ ∧ _ ∧ _ from ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.1⟩)

theorem accepts_cutoff (c : ℕ) (U : ClockedUniversalMachine) (S D : Prog)
    (lam n : ℕ) (x y a b : BitStr) (h : (decider c U S D lam).Accepts n x y a b) :
    a.length ≤ cutoffAt c lam n ∧ b.length ≤ cutoffAt c lam n := by
  by_cases hz : lam = 0 ∨ n = 0
  · simpa only [cutoffAt, if_pos hz] using ((accepts_zero c U S D lam n hz x y a b).mp h).2.2
  · have hl : 1 ≤ lam := by omega
    have hn : 1 ≤ n := by omega
    simpa only [cutoffAt, if_neg hz] using (accepts_positive_bounds c U S D hl hn x y a b h).2.2

theorem cutoffAt_ansBound {c : ℕ} (hc : 1 ≤ c) :
    ∃ K, ∀ lam n, cutoffAt c lam n ≤ ansBound K lam n := by
  obtain ⟨K,hK⟩ := answerBound_ansBound hc
  refine ⟨K,fun lam n => ?_⟩
  by_cases hz : lam = 0 ∨ n = 0
  · rcases hz with rfl | rfl <;> simp [cutoffAt, ansBound]
  · simpa only [cutoffAt, if_neg hz] using hK lam n (by omega) (by omega)

theorem compute_size (c : ℕ) (U : ClockedUniversalMachine) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ S D lam,
      (decider c U S D lam).size ≤ C*(lam+1)^C :=
  SourceDescriptionCompiler.exists_compiler_size (selectedCompiler c U)

end MIPRE.Introspection.DecisionCompiler
