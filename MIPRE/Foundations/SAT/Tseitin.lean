/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Circuit
import MIPRE.Foundations.SAT.Cnf

/-!
# The circuit-to-3SAT reduction

`Circuit.tseitin C inp gv` is the 3SAT formula of a circuit `C` on variables `inp i` for its
inputs and `gv g` for its gates (`lem:circuit-to-sat-reduction`, `lem:tseitin` with the
output-wire conjunct of the F7.2 erratum): for every gate the clauses saying that its
variable is the gate's function of its arguments' variables, and the unit clause on the
output gate. `tseitin_sat_iff`: for a circuit reading only earlier gates, `C(x) = 1` iff some
assignment agreeing with `x` on the inputs satisfies the formula; `tseitin_values`: a
satisfying assignment carries the gate values. The tableau of the Cook–Levin theorem is
this reduction applied to the local check circuit at every window
(`planning/succinct-cook-levin.md`, S1).
-/

namespace MIPRE.SAT

variable {V : Type*}

/-- A clause from three literals. -/
def cl (a b c : Lit V) : Clause3 V := ⟨a, b, c⟩

/-- The consistency clauses of a gate whose variable is `y`, over the input variables `inp`
and the gate variables `gv`. -/
def gateClauses (inp gv : ℕ → V) (y : V) : Gate → List (Clause3 V)
  | .input i => [cl ⟨inp i, false⟩ ⟨y, true⟩ ⟨y, true⟩, cl ⟨inp i, true⟩ ⟨y, false⟩ ⟨y, false⟩]
  | .const b => [cl ⟨y, b⟩ ⟨y, b⟩ ⟨y, b⟩]
  | .and u v =>
    [cl ⟨gv u, false⟩ ⟨gv v, false⟩ ⟨y, true⟩, cl ⟨gv u, true⟩ ⟨gv v, true⟩ ⟨y, false⟩,
      cl ⟨gv u, true⟩ ⟨gv v, false⟩ ⟨y, false⟩, cl ⟨gv u, false⟩ ⟨gv v, true⟩ ⟨y, false⟩]
  | .or u v =>
    [cl ⟨gv u, true⟩ ⟨gv v, true⟩ ⟨y, false⟩, cl ⟨gv u, false⟩ ⟨gv v, false⟩ ⟨y, true⟩,
      cl ⟨gv u, false⟩ ⟨gv v, true⟩ ⟨y, true⟩, cl ⟨gv u, true⟩ ⟨gv v, false⟩ ⟨y, true⟩]
  | .not u => [cl ⟨gv u, true⟩ ⟨y, true⟩ ⟨y, true⟩, cl ⟨gv u, false⟩ ⟨y, false⟩ ⟨y, false⟩]

/-- The clauses of a gate hold iff its variable carries the gate's value, when the argument
variables carry the argument values. -/
theorem gateClauses_iff (inp gv : ℕ → V) (y : V) (g : Gate) (w : V → Bool) (vals : List Bool)
    (hv : ∀ u ∈ g.refs, vals.getD u false = w (gv u)) :
    (∀ c ∈ gateClauses inp gv y g, c.eval w = true) ↔ w y = g.eval (fun i => w (inp i)) vals := by
  cases g with
  | input i =>
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval]
    cases w y <;> cases w (inp i) <;> simp
  | const b =>
    simp only [gateClauses, List.mem_singleton, forall_eq, Clause3.eval, cl, Lit.eval, Gate.eval]
    cases w y <;> cases b <;> simp
  | and u v =>
    have hu := hv u (by simp [Gate.refs])
    have hv' := hv v (by simp [Gate.refs])
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval, hu, hv']
    cases w y <;> cases w (gv u) <;> cases w (gv v) <;> simp
  | or u v =>
    have hu := hv u (by simp [Gate.refs])
    have hv' := hv v (by simp [Gate.refs])
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval, hu, hv']
    cases w y <;> cases w (gv u) <;> cases w (gv v) <;> simp
  | not u =>
    have hu := hv u (by simp [Gate.refs])
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval, hu]
    cases w y <;> cases w (gv u) <;> simp

namespace Circuit

/-- The circuit-to-3SAT formula of `C`: the consistency clauses of every gate, and the unit
clause on the output gate. -/
def tseitin (C : Circuit) (inp gv : ℕ → V) : Cnf3 V :=
  {c | ∃ g : Fin C.gates.length, c ∈ gateClauses inp gv (gv g) C.gates[g]} ∪
    {cl ⟨gv (C.gates.length - 1), true⟩ ⟨gv (C.gates.length - 1), true⟩
      ⟨gv (C.gates.length - 1), true⟩}

/-- Every gate reads only earlier gates. -/
def RefsLt (C : Circuit) : Prop :=
  ∀ (k : ℕ) (h : k < C.gates.length), ∀ u ∈ C.gates[k].refs, u < k

theorem WellFormed.refsLt {C : Circuit} (h : C.WellFormed) : C.RefsLt := h.refs_lt

/-- A satisfying assignment of the gate clauses carries the gate values. -/
theorem tseitin_values (C : Circuit) (hC : C.RefsLt) (inp gv : ℕ → V) (w : V → Bool)
    (hSat : ∀ c ∈ C.tseitin inp gv, c.eval w = true) :
    ∀ g < C.gates.length, w (gv g) = C.valueAt (fun i => w (inp i)) g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    rw [valueAt_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]
    rw [← gateClauses_iff inp gv (gv g) C.gates[g] w _ ?_]
    · intro c hc
      exact hSat c (Or.inl ⟨⟨g, hg⟩, hc⟩)
    · intro u hu
      have hlt := hC g hg u hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some]
      simp only [List.getElem_ofFn]
      exact (ih u hlt (by omega)).symm

/-- Every input gate reads an existing input. -/
def InputsLt (C : Circuit) : Prop := ∀ i, Gate.input i ∈ C.gates → i < C.inputs

theorem WellFormed.inputsLt {C : Circuit} (h : C.WellFormed) : C.InputsLt := h.inputs_lt

/-- The gate values depend only on the inputs the circuit reads. -/
theorem valueAt_congr (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
    (hx : ∀ i < C.inputs, x i = x' i) : ∀ g, C.valueAt x g = C.valueAt x' g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    rw [valueAt_eq, valueAt_eq]
    have hl : (List.ofFn fun k : Fin g => C.valueAt x k) = List.ofFn fun k : Fin g => C.valueAt x' k := by
      congr 1
      funext k
      exact ih k k.isLt
    rw [hl]
    by_cases hg : g < C.gates.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]
      cases hgate : C.gates[g] with
      | input i =>
        simp only [Gate.eval]
        exact hx i (hin i (hgate ▸ List.getElem_mem hg))
      | const b => rfl
      | and u v => rfl
      | or u v => rfl
      | not u => rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl

theorem eval_congr (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
    (hx : ∀ i < C.inputs, x i = x' i) : C.eval x = C.eval x' := by
  unfold eval
  split_ifs
  · rfl
  · exact valueAt_congr C hin x x' hx _

/-- Soundness: a satisfying assignment of the formula agreeing with `x` on the inputs
witnesses `C(x) = 1`. -/
theorem eval_of_tseitin_sat (C : Circuit) (hC : C.RefsLt) (hin : C.InputsLt) (hne : C.gates ≠ [])
    (inp gv : ℕ → V) (x : ℕ → Bool) (w : V → Bool) (hx : ∀ i < C.inputs, w (inp i) = x i)
    (hSat : (C.tseitin inp gv).Sat w) : C.eval x = true := by
  have hout := hSat _ (Or.inr rfl)
  simp only [Clause3.eval, cl, Lit.eval, ite_true, Bool.or_self] at hout
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
  have := tseitin_values C hC inp gv w hSat (C.gates.length - 1) (by omega)
  rw [eval_congr C hin x (fun i => w (inp i)) (fun i hi => (hx i hi).symm)]
  simp only [eval, hne, ite_false]
  rw [← this, hout]

/-- Completeness, for a given assignment: one that carries the gate values on the gate
variables satisfies the formula when the circuit accepts the bits it reads on the inputs. -/
theorem tseitin_sat_of_values (C : Circuit) (hC : C.RefsLt) (inp gv : ℕ → V) (w : V → Bool)
    (hwg : ∀ g < C.gates.length, w (gv g) = C.valueAt (fun i => w (inp i)) g)
    (hx : C.eval (fun i => w (inp i)) = true) : (C.tseitin inp gv).Sat w := by
  intro c hc
  rcases hc with ⟨g, hg⟩ | rfl
  · refine (gateClauses_iff inp gv (gv g) C.gates[g] w
      (List.ofFn fun k : Fin g => C.valueAt (fun i => w (inp i)) k) ?_).mpr ?_ c hg
    · intro u hu
      have hlt := hC g g.isLt u hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hlt), Option.getD_some,
        List.getElem_ofFn, hwg u (by omega)]
    · rw [hwg g g.isLt, valueAt_eq, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem g.isLt, Option.getD_some]
      rfl
  · have hne : C.gates ≠ [] := by
      intro h
      simp [eval, h] at hx
    have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
    simp only [Clause3.eval, cl, Lit.eval, ite_true, Bool.or_self]
    rw [hwg (C.gates.length - 1) (by omega)]
    simpa [eval, hne] using hx

/-- Completeness: if `C(x) = 1`, the assignment reading `x` on the inputs and the gate values
on the gate variables satisfies the formula. -/
theorem tseitin_sat_of_eval (C : Circuit) (hC : C.RefsLt) (hin : C.InputsLt) (inp gv : ℕ → V)
    (hinp : ∀ i j, i < C.inputs → j < C.inputs → inp i = inp j → i = j)
    (hgv : ∀ g g', g < C.gates.length → g' < C.gates.length → gv g = gv g' → g = g')
    (hdisj : ∀ i g, i < C.inputs → inp i ≠ gv g)
    (x : ℕ → Bool) (hx : C.eval x = true) :
    ∃ w : V → Bool, (∀ i < C.inputs, w (inp i) = x i) ∧ (C.tseitin inp gv).Sat w := by
  classical
  let w : V → Bool := fun v =>
    if h : ∃ i, i < C.inputs ∧ v = inp i then x h.choose
    else if h' : ∃ g, g < C.gates.length ∧ v = gv g then C.valueAt x h'.choose else false
  have hwi : ∀ i < C.inputs, w (inp i) = x i := by
    intro i hi
    have h : ∃ i', i' < C.inputs ∧ inp i = inp i' := ⟨i, hi, rfl⟩
    simp only [w, dif_pos h]
    congr 1
    exact hinp _ _ h.choose_spec.1 hi h.choose_spec.2.symm
  have hwg : ∀ g < C.gates.length, w (gv g) = C.valueAt x g := by
    intro g hg
    have h : ¬ ∃ i, i < C.inputs ∧ gv g = inp i := fun ⟨i, hi, h⟩ => hdisj i g hi h.symm
    have h' : ∃ g', g' < C.gates.length ∧ gv g = gv g' := ⟨g, hg, rfl⟩
    simp only [w, dif_neg h, dif_pos h']
    congr 1
    exact hgv _ _ h'.choose_spec.1 hg h'.choose_spec.2.symm
  have hval : ∀ g, C.valueAt (fun i => w (inp i)) g = C.valueAt x g :=
    valueAt_congr C hin _ x hwi
  refine ⟨w, hwi, tseitin_sat_of_values C hC inp gv w (fun g hg => by rw [hwg g hg, hval]) ?_⟩
  rw [eval_congr C hin _ x hwi]
  exact hx

/-- **The circuit-to-3SAT reduction**: `C(x) = 1` iff some assignment agreeing with `x` on
the inputs satisfies the Tseitin formula. -/
theorem tseitin_sat_iff (C : Circuit) (hC : C.RefsLt) (hin : C.InputsLt) (hne : C.gates ≠ [])
    (inp gv : ℕ → V) (hinp : ∀ i j, i < C.inputs → j < C.inputs → inp i = inp j → i = j)
    (hgv : ∀ g g', g < C.gates.length → g' < C.gates.length → gv g = gv g' → g = g')
    (hdisj : ∀ i g, i < C.inputs → inp i ≠ gv g) (x : ℕ → Bool) :
    (∃ w : V → Bool, (∀ i < C.inputs, w (inp i) = x i) ∧ (C.tseitin inp gv).Sat w) ↔
      C.eval x = true :=
  ⟨fun ⟨w, hx, hSat⟩ => eval_of_tseitin_sat C hC hin hne inp gv x w hx hSat,
    tseitin_sat_of_eval C hC hin inp gv hinp hgv hdisj x⟩

end Circuit

end MIPRE.SAT
