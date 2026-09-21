/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.DetypingDeciderProg
import MIPRE.Foundations.CL.DetypingProgCost
import MIPRE.Foundations.Cost.Universal

/-! # Total clocking of arbitrary typed decision programs

An executable index clock writes a unary cost budget. The clocked universal
machine simulates the arbitrary source program under that budget, and the
wrapper accepts exactly an in-budget return of `encode true`. No termination
or well-scopedness assumption is imposed on the source program.
-/

noncomputable section

namespace MIPRE.CL.Detyping

open Cost Cost.PolyTimeFun Program

/-- An actual index routine that supplies a unary simulation budget. -/
structure ClockProgram where
  budget : ℕ → ℕ
  prog : Prog
  closed : prog.WellScoped 1
  runs : ∀ n, ∃ time, prog.Runs (encode n) (.ofNat (budget n)) time

namespace ClockProgram

/-- Every valid index call to the clock terminates. -/
theorem halts (C : ClockProgram) (n : ℕ) : Halts C.prog (encode n) := by
  obtain ⟨time, hr⟩ := C.runs n
  exact ⟨_, time, hr⟩

/-- A concrete executable clock, useful independently of any index-growth routine. -/
def constant (k : ℕ) : ClockProgram where
  budget _ := k
  prog := .const (.ofNat k)
  closed := trivial
  runs _ := ⟨_, Eval.const _ _⟩

/-- Any polynomial-time unary index routine supplies an executable clock. -/
def ofPolyTimeFun (f : PolyTimeFun ℕ Unary) : ClockProgram where
  budget n := (f n).length
  prog := f.code
  closed := f.closed
  runs n := by
    obtain ⟨time, _, hr⟩ := f.computes n
    exact ⟨time, by simpa only [← encode_unary, unary_length] using hr⟩

theorem evalWithin_eq_some_iff (c : Prog) (x r : Data) (k : ℕ) :
    evalWithin c x k = some r ↔ ∃ time ≤ k, c.Runs x r time := by
  classical
  unfold evalWithin
  by_cases h : ∃ r time, time ≤ k ∧ c.Runs x r time
  · rw [dif_pos h]
    obtain ⟨time, ht, hr⟩ := h.choose_spec
    constructor
    · intro he
      have he' := Option.some.inj he
      exact ⟨time, ht, he' ▸ hr⟩
    · rintro ⟨t, ht', hr'⟩
      exact congrArg some (hr.deterministic hr').1
  · rw [dif_neg h]
    constructor
    · intro he; cases he
    · rintro ⟨time, ht, hr⟩
      exact False.elim (h ⟨r, time, ht, hr⟩)

/-- The success tag carries precisely the source result of an in-budget run. -/
theorem clockedResult_eq_iff (c : Prog) (x r : Data) (k : ℕ) :
    clockedResult c x k = .cons (encode true) r ↔ ∃ time ≤ k, c.Runs x r time := by
  have he : clockedResult c x k = .cons (encode true) r ↔ evalWithin c x k = some r := by
    cases h : evalWithin c x k <;> simp [clockedResult, h, encode, Data.ofBool]
  exact he.trans (evalWithin_eq_some_iff c x r k)

def clockRoute : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair
    (encoded.comp (readNat.comp treeHead)) (PolyTimeFun.id Data))

def clockPost (source : Prog) : PolyTimeFun (Data × Data) Data :=
  ap₂ treePair snd (ap₂ treePair (const (encode source)) fst)

def checkResult : PolyTimeFun Data Bool :=
  ap₂ treeEq (PolyTimeFun.id Data) (const (Data.cons (encode true) (encode true)))

theorem checkResult_apply (x : Data) :
    checkResult x = decide (x = .cons (encode true) (encode true)) := rfl

def clockStage (C : ClockProgram) (source : Prog) : Prog :=
  Prog.routeOneCall clockRoute C.prog (clockPost source)

theorem clockStage_closed (C : ClockProgram) (source : Prog) :
    (clockStage C source).WellScoped 1 := Prog.routeOneCall_closed _ C.closed _

theorem clockStage_runs (C : ClockProgram) (source : Prog) (x : Data) :
    ∃ time, (clockStage C source).Runs x
      (.cons (.ofNat (C.budget (readNat (treeHead x)))) (.cons (encode source) x)) time := by
  obtain ⟨time, hr⟩ := C.runs (readNat (treeHead x))
  exact Prog.routeOneCall_indirect clockRoute C.closed (clockPost source) x _ x _ time rfl hr

def wrapProg (C : ClockProgram) (U : ClockedUniversalMachine) (source : Prog) : Prog :=
  .let_ (clockStage C source) (.let_ U.univT checkResult.code)

theorem wrapProg_closed (C : ClockProgram) (U : ClockedUniversalMachine) (source : Prog) :
    (wrapProg C U source).WellScoped 1 :=
  ⟨clockStage_closed C source, U.closed.mono (by omega) _, checkResult.closed.mono (by omega) _⟩

/-- The exact Boolean returned by the executable clock wrapper on every raw input. -/
theorem wrapProg_runs (C : ClockProgram) (U : ClockedUniversalMachine) (source : Prog) (x : Data) :
    ∃ time, (wrapProg C U source).Runs x
      (encode (decide (clockedResult source x (C.budget (readNat (treeHead x))) =
        .cons (encode true) (encode true)))) time := by
  obtain ⟨tc, hc⟩ := clockStage_runs C source x
  obtain ⟨tu, _, hu⟩ := U.run source x (C.budget (readNat (treeHead x)))
  obtain ⟨tr, _, hr⟩ := checkResult.computes
    (clockedResult source x (C.budget (readNat (treeHead x))))
  exact ⟨_, Eval.let_ hc (Eval.append_of_wellScoped
    (Eval.let_ hu (Eval.append_of_wellScoped hr checkResult.closed _))
      ⟨U.closed, checkResult.closed.mono (by omega) _⟩ _)⟩

theorem wrapProg_halts (C : ClockProgram) (U : ClockedUniversalMachine) (source : Prog)
    (x : Data) : Halts (wrapProg C U source) x := by
  obtain ⟨time, hr⟩ := wrapProg_runs C U source x
  exact ⟨_, time, hr⟩

/-- The explicit wrapper cost, including clock generation and universal simulation. -/
def wrapCost (C : ClockProgram) (U : ClockedUniversalMachine) (source : Prog)
    (x : Data) (clockTime : ℕ) : ℕ :=
  let n := readNat (treeHead x)
  let k := C.budget n
  let G := U.bound.eval (k + esize source + x.size)
  clockRoute.timeBound.eval x.size + 3 * esize n + 3 * x.size + (2 * k + 1) + clockTime +
    (clockPost source).timeBound.eval (x.size + (2 * k + 1) + 1) + 18 +
    G + checkResult.timeBound.eval G + 2

/-- Runtime overhead is explicit once the executable clock's own runtime is bounded. -/
theorem wrapProg_haltsWithin (C : ClockProgram) (U : ClockedUniversalMachine) (source : Prog)
    (x : Data) (clockTime : ℕ)
    (hC : HaltsWithin C.prog (encode (readNat (treeHead x))) clockTime) :
    HaltsWithin (wrapProg C U source) x (wrapCost C U source x clockTime) := by
  let n := readNat (treeHead x)
  let k := C.budget n
  let G := U.bound.eval (k + esize source + x.size)
  obtain ⟨tc, hc⟩ := C.runs n
  obtain ⟨r, tr, htr, hrc⟩ := hC
  have htc : tc ≤ clockTime := by
    have he := (hc.deterministic hrc).2
    omega
  obtain ⟨ts, hts, hs⟩ := Prog.routeOneCall_indirect_cost clockRoute C.closed
    (clockPost source) x (encode n) x (.ofNat k) tc rfl hc
  obtain ⟨tu, htu, hu⟩ := U.run source x k
  obtain ⟨tp, htp, hp⟩ := checkResult.computes (clockedResult source x k)
  have hres : (clockedResult source x k).size ≤ G := hu.size_le.trans htu
  have htpG : tp ≤ checkResult.timeBound.eval G :=
    htp.trans (polynomial_eval_mono _ hres)
  refine ⟨_, _, ?_, Eval.let_ hs (Eval.append_of_wellScoped
    (Eval.let_ hu (Eval.append_of_wellScoped hp checkResult.closed _))
      ⟨U.closed, checkResult.closed.mono (by omega) _⟩ _)⟩
  change tu ≤ G at htu
  simp only [Data.size_ofNat] at hts
  change ts ≤ clockRoute.timeBound.eval x.size + 3 * esize n + 3 * x.size +
    (2 * k + 1) + tc + (clockPost source).timeBound.eval (x.size + (2 * k + 1) + 1) + 18 at hts
  change ts + (tu + tp + 1) + 1 ≤ clockRoute.timeBound.eval x.size +
    3 * esize n + 3 * x.size + (2 * k + 1) + clockTime +
      (clockPost source).timeBound.eval (x.size + (2 * k + 1) + 1) + 18 +
      G + checkResult.timeBound.eval G + 2
  omega

/-- Acceptance is exactly acceptance of the source within the computed cost budget. -/
theorem wrapProg_accepts_iff (C : ClockProgram) (U : ClockedUniversalMachine) (source : Prog)
    (x : Data) :
    (∃ time, (wrapProg C U source).Runs x (encode true) time) ↔
      ∃ time ≤ C.budget (readNat (treeHead x)), source.Runs x (encode true) time := by
  obtain ⟨time, hout⟩ := wrapProg_runs C U source x
  rw [← clockedResult_eq_iff]
  constructor
  · rintro ⟨t, hr⟩
    have hb := encode_injective (hout.deterministic hr).1
    exact of_decide_eq_true hb
  · intro h
    exact ⟨time, by simpa only [h, decide_true] using hout⟩

/-- The genuine typed decider obtained by clocking arbitrary source code. -/
def wrap {T : Type*} [SizedEncoding T] (C : ClockProgram) (U : ClockedUniversalMachine)
    (source : Prog) : TypedDecider T where
  prog := wrapProg C U source
  closed := wrapProg_closed C U source

theorem wrap_total {T : Type*} [SizedEncoding T] (C : ClockProgram)
    (U : ClockedUniversalMachine) (source : Prog) : (C.wrap (T := T) U source).Total :=
  fun n d => wrapProg_halts C U source (.cons (encode n) d)

theorem wrap_accepts_iff {T : Type*} [SizedEncoding T] (C : ClockProgram)
    (U : ClockedUniversalMachine) (source : Prog)
    (n : ℕ) (u : T) (x : BitStr) (v : T) (y a b : BitStr) :
    (C.wrap U source).Accepts n u x v y a b ↔
      ∃ time ≤ C.budget n, source.Runs (encode (n, u, x, v, y, a, b)) (encode true) time := by
  change (∃ time, (wrapProg C U source).Runs _ _ time) ↔ _
  rw [wrapProg_accepts_iff]
  simp only [encode_prod, treeHead_cons, readNat_encode]

/-- An in-budget source run is preserved, with nonaccepting results normalized to false. -/
theorem wrapProg_preserves_run (C : ClockProgram) (U : ClockedUniversalMachine)
    (source : Prog) (n : ℕ) (d r : Data) (time : ℕ)
    (hr : source.Runs (.cons (encode n) d) r time) (ht : time ≤ C.budget n) :
    ∃ t, (wrapProg C U source).Runs (.cons (encode n) d)
      (encode (decide (r = encode true))) t := by
  have hc := (clockedResult_eq_iff source (.cons (encode n) d) r (C.budget n)).mpr ⟨time, ht, hr⟩
  obtain ⟨t, hout⟩ := wrapProg_runs C U source (.cons (encode n) d)
  exact ⟨t, by simpa only [treeHead_cons, readNat_encode, hc, Data.cons.injEq,
    true_and] using hout⟩

/-- Whenever a source run is known to fit, clocking preserves its acceptance predicate. -/
theorem wrap_accepts_iff_of_bounded {T : Type*} [SizedEncoding T] (C : ClockProgram)
    (U : ClockedUniversalMachine) (D : TypedDecider T)
    (n : ℕ) (u : T) (x : BitStr) (v : T) (y a b : BitStr)
    (h : HaltsWithin D.prog (encode (n, u, x, v, y, a, b)) (C.budget n)) :
    (C.wrap U D.prog).Accepts n u x v y a b ↔ D.Accepts n u x v y a b := by
  rw [wrap_accepts_iff]
  constructor
  · rintro ⟨time, _, hr⟩; exact ⟨time, hr⟩
  · rintro ⟨time, hr⟩
    obtain ⟨r, t, ht, hout⟩ := h
    exact ⟨time, (hout.deterministic hr).2 ▸ ht, hr⟩

/-- The wrapper instantiated with the proved clocked self-interpreter. -/
def decider {T : Type*} [SizedEncoding T] (C : ClockProgram) (source : Prog) : TypedDecider T :=
  C.wrap selfClockedUniversal source

theorem decider_total {T : Type*} [SizedEncoding T] (C : ClockProgram) (source : Prog) :
    (C.decider (T := T) source).Total := wrap_total C selfClockedUniversal source

theorem decider_accepts_iff {T : Type*} [SizedEncoding T] (C : ClockProgram) (source : Prog)
    (n : ℕ) (u : T) (x : BitStr) (v : T) (y a b : BitStr) :
    (C.decider source).Accepts n u x v y a b ↔
      ∃ time ≤ C.budget n, source.Runs (encode (n, u, x, v, y, a, b)) (encode true) time :=
  wrap_accepts_iff C selfClockedUniversal source n u x v y a b

end ClockProgram
end MIPRE.CL.Detyping
