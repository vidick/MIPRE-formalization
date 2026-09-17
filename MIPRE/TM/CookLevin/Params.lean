/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.CookLevin.FamilyFml
import MIPRE.TM.Interp.Run
import MIPRE.Foundations.SAT.Table

/-!
# The parameters of the describer: the check circuit and the tableau length

Two constants and one choice.

* `chk` is the check circuit of the interpreter machine: the truth-table circuit
  (`Fml.table`) of its local check predicate `checkPred U 1`, of `winCard 7 6 Sym Ctl` inputs
  and at most `7 · 2 ^ winCard` gates — an enormous constant, exactly as the paper's
  `lem:pack-check-size`, and formally harmless. `chk_isCheckCircuit` is the hypothesis of
  `lem:correct-tableau`; `Gc` is its gate count.
* `eOf T σ = 5 (⌈log T⌉ + ⌈log σ⌉) + 24` is the exponent of the tableau length: under the
  validity hypotheses and `|a|, |b| ≤ T`, the accepting run of `U` is shorter than
  `2 ^ eOf T σ` (`runBound_le_two_pow`), so the tableau of `Sof (eOf T σ)` steps is long
  enough. The bound comes from an explicit fifth-power majorant of `runBound`
  (`runBound_le`) (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.TM.CookLevin.Desc

open Interp SAT Cost

/-! ## The check circuit -/

open Classical in
/-- The local check predicate of the interpreter machine as a Boolean function of the window
bits, in the canonical order. -/
noncomputable def chkFun (x : Fin (winCard 7 6 Sym Ctl) → Bool) : Bool :=
  decide (checkPred U Sym.one fun wv => x (Fintype.equivFin _ wv))

/-- **The check circuit of the interpreter machine**: a truth-table circuit of `chkFun`,
taken from `Fml.exists_circuit`. It is never unfolded: its defining term mentions
`Fintype.card (WinVar 7 6 Sym Ctl)`, whose evaluation does not terminate in practice. -/
noncomputable def chk : Circuit := (Fml.exists_circuit (winCard 7 6 Sym Ctl) chkFun).choose

theorem chk_spec : chk.WellFormed ∧ chk.inputs = winCard 7 6 Sym Ctl ∧
    chk.size ≤ 7 * 2 ^ winCard 7 6 Sym Ctl ∧
    ∀ x : Fin (winCard 7 6 Sym Ctl) → Bool, chk.evalBits (List.ofFn x) = chkFun x :=
  (Fml.exists_circuit (winCard 7 6 Sym Ctl) chkFun).choose_spec

/-- The number of gates of the check circuit. -/
noncomputable def Gc : ℕ := chk.gates.length

theorem Gc_eq : Gc = chk.gates.length := rfl

theorem chk_wellFormed : chk.WellFormed := chk_spec.1

theorem chk_inputs : chk.inputs = winCard 7 6 Sym Ctl := chk_spec.2.1

theorem chk_refsLt : chk.RefsLt := chk_wellFormed.refsLt

theorem chk_inputsLt : chk.InputsLt := chk_wellFormed.inputsLt

theorem chk_gates_ne : chk.gates ≠ [] := chk_wellFormed.nonempty

theorem chk_size_le : chk.size ≤ 7 * 2 ^ winCard 7 6 Sym Ctl := chk_spec.2.2.1

theorem Gc_le : Gc ≤ 7 * 2 ^ winCard 7 6 Sym Ctl := chk_size_le

theorem Gc_pos : 0 < Gc := List.length_pos_iff.mpr chk_gates_ne

/-- The check circuit computes the local check predicate: the hypothesis of the correctness
of the tableau (`IsCheckCircuit`, `lem:correct-tableau`). -/
theorem chk_isCheckCircuit : IsCheckCircuit U Sym.one chk := by
  classical
  intro win
  have h := chk_spec.2.2.2 fun n => win ((Fintype.equivFin (WinVar 7 6 Sym Ctl)).symm n)
  rw [show (List.ofFn fun n => win ((Fintype.equivFin (WinVar 7 6 Sym Ctl)).symm n)) = winBits win
    from rfl] at h
  rw [h, chkFun, decide_eq_true_iff]
  have hfun : (fun wv : WinVar 7 6 Sym Ctl =>
      win ((Fintype.equivFin (WinVar 7 6 Sym Ctl)).symm
        ((Fintype.equivFin (WinVar 7 6 Sym Ctl)) wv))) = win := by
    funext wv
    rw [Equiv.symm_apply_apply]
  rw [hfun]

/-! ## The tableau length -/

/-- `a ≤ c · M ^ i` and `b ≤ d · M ^ j` give `a · b ≤ c d · M ^ (i + j)`. -/
theorem mul_le_mul_pow {a b c d i j M : ℕ} (ha : a ≤ c * M ^ i) (hb : b ≤ d * M ^ j) :
    a * b ≤ c * d * M ^ (i + j) := by
  calc a * b ≤ c * M ^ i * (d * M ^ j) := Nat.mul_le_mul ha hb
    _ = c * d * M ^ (i + j) := by ring

/-- Raising the exponent of a majorant. -/
theorem le_mul_pow_of_le {a c i j M : ℕ} (hM : 1 ≤ M) (h : a ≤ c * M ^ i) (hij : i ≤ j) :
    a ≤ c * M ^ j :=
  h.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right hM hij))

section RunBound

variable (D : Prog) (n T Q σ : ℕ) (x y a b : BitStr)

/-- **A fifth-power majorant of the run bound of the interpreter machine** under the validity
hypotheses and `|a|, |b| ≤ T`. -/
theorem runBound_le (hV : Valid D n T Q σ x y) (ha : a.length ≤ T) (hb : b.length ≤ T) :
    runBound D n x y a b T ≤ 400000 * (T + σ + 1) ^ 5 := by
  set M := T + σ + 1 with hM
  clear_value M
  have h1 : 1 ≤ M := by omega
  have hM1 : M ^ 1 = M := pow_one M
  have hTM : T ≤ 1 * M ^ 1 := by rw [hM1]; omega
  have hσM : σ ≤ 1 * M ^ 1 := by rw [hM1]; omega
  -- the sizes of the pieces of the input
  have hD : esize D ≤ 1 * M ^ 1 := by rw [hM1]; have := hV.size_le; omega
  have hn : esize n ≤ 3 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_nat_le n
    have h3 := hV.logn_le
    omega
  have hx : esize x ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le x
    have h3 := hV.x_le
    have h4 := hV.q_le
    omega
  have hy : esize y ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le y
    have h3 := hV.y_le
    have h4 := hV.q_le
    omega
  have hae : esize a ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le a
    omega
  have hbe : esize b ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le b
    omega
  -- the value bound
  have hV0 : V0 n x y a b T ≤ 27 * M ^ 1 := by
    rw [hM1] at hTM hn hx hy hae hbe ⊢
    show max (esize (n, x, y, a, b)) T ≤ 27 * M
    have he : esize (n, x, y, a, b) = esize n + esize x + esize y + esize a + esize b + 4 := by
      simp only [esize_prod]; omega
    omega
  have hL : 1 + 2 * T ≤ 3 * M ^ 1 := by rw [hM1]; omega
  -- the size bound along the run
  have hZ0 : Z0 D n x y a b T ≤ 231 * M ^ 3 := by
    show szBound (V0 n x y a b T) (1 + 2 * T) (esize D) T ≤ _
    have e1 : (1 + 2 * T) * V0 n x y a b T ≤ 81 * M ^ 2 := by
      have := mul_le_mul_pow hL hV0
      norm_num at this
      exact this
    have hin : V0 n x y a b T + esize D + (1 + 2 * T) * V0 n x y a b T + (1 + 2 * T) + 4
        ≤ 116 * M ^ 2 := by
      have h4 : (4 : ℕ) ≤ 4 * M ^ 2 := by
        have : (1 : ℕ) ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have hV0' : V0 n x y a b T ≤ 27 * M ^ 2 := le_mul_pow_of_le h1 hV0 (by omega)
      have hD' : esize D ≤ 1 * M ^ 2 := le_mul_pow_of_le h1 hD (by omega)
      have hL' : 1 + 2 * T ≤ 3 * M ^ 2 := le_mul_pow_of_le h1 hL (by omega)
      omega
    have e2 : T * (V0 n x y a b T + esize D + (1 + 2 * T) * V0 n x y a b T + (1 + 2 * T) + 4)
        ≤ 116 * M ^ 3 := by
      have h := mul_le_mul_pow hTM hin
      norm_num at h
      exact h
    have hV0' : V0 n x y a b T ≤ 27 * M ^ 3 := le_mul_pow_of_le h1 hV0 (by omega)
    have hD' : esize D ≤ 1 * M ^ 3 := le_mul_pow_of_le h1 hD (by omega)
    have hL' : 1 + 2 * T ≤ 3 * M ^ 3 := le_mul_pow_of_le h1 hL (by omega)
    have e1' : (1 + 2 * T) * V0 n x y a b T ≤ 81 * M ^ 3 := le_mul_pow_of_le h1 e1 (by omega)
    have h2 : (2 : ℕ) ≤ 2 * M ^ 3 := by
      have : (1 : ℕ) ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have h1' : (1 : ℕ) ≤ 1 * M ^ 3 := by
      have : (1 : ℕ) ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    show (V0 n x y a b T + esize D + 2) + ((1 + 2 * T) * V0 n x y a b T + (1 + 2 * T)) +
      T * (V0 n x y a b T + esize D + (1 + 2 * T) * V0 n x y a b T + (1 + 2 * T) + 4) + 1 ≤ _
    omega
  -- the per-step bound
  have hxl : 3 * T * Z0 D n x y a b T ≤ 693 * M ^ 4 := by
    have h3T : 3 * T ≤ 3 * M ^ 1 := by rw [hM1]; omega
    have := mul_le_mul_pow h3T hZ0
    norm_num at this
    exact this
  have hstep : stepB (Z0 D n x y a b T) (3 * T * Z0 D n x y a b T) ≤ 100000 * M ^ 4 := by
    show 100 * (Z0 D n x y a b T + 3 * T * Z0 D n x y a b T + 1) + Z0 D n x y a b T + 30 ≤ _
    have hZ0' : Z0 D n x y a b T ≤ 231 * M ^ 4 := le_mul_pow_of_le h1 hZ0 (by omega)
    have h30 : (31 : ℕ) ≤ 31 * M ^ 4 := by
      have : (1 : ℕ) ≤ M ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega
    omega
  have hmain : 3 * T * stepB (Z0 D n x y a b T) (3 * T * Z0 D n x y a b T) ≤ 300000 * M ^ 5 := by
    have h3T : 3 * T ≤ 3 * M ^ 1 := by rw [hM1]; omega
    have := mul_le_mul_pow h3T hstep
    norm_num at this
    exact this
  -- the initialization
  have hinit : initBound D n x y a b T ≤ 73 * M ^ 1 := by
    rw [hM1] at hTM hD hn hx hy ⊢
    show 3 * T + 8 * (a.length + b.length) + (S D.toData).length + (S (encode n)).length +
      (S (encode x)).length + (S (encode y)).length + 40 ≤ 73 * M
    rw [length_S, length_S, length_S, length_S]
    have e1 : D.toData.size = esize D := rfl
    have e2 : (encode n : Data).size = esize n := rfl
    have e3 : (encode x : Data).size = esize x := rfl
    have e4 : (encode y : Data).size = esize y := rfl
    omega
  -- putting it together
  have hinit' : initBound D n x y a b T ≤ 73 * M ^ 5 := le_mul_pow_of_le h1 hinit (by omega)
  have hV0'' : V0 n x y a b T ≤ 27 * M ^ 5 := le_mul_pow_of_le h1 hV0 (by omega)
  have h16 : (16 : ℕ) ≤ 16 * M ^ 5 := by
    have : (1 : ℕ) ≤ M ^ 5 := Nat.one_le_pow _ _ (by omega)
    omega
  show initBound D n x y a b T + 3 * T * stepB (Z0 D n x y a b T) (3 * T * Z0 D n x y a b T) +
    V0 n x y a b T + 16 ≤ _
  omega

end RunBound

/-- The exponent of the tableau length: `5 (⌈log T⌉ + ⌈log σ⌉) + 24`. -/
def eOf (T σ : ℕ) : ℕ := 5 * Nat.size T + 5 * Nat.size σ + 24

theorem sum_le_two_pow (T σ : ℕ) : T + σ + 1 ≤ 2 ^ (Nat.size T + Nat.size σ + 1) := by
  have hT := Nat.lt_size_self T
  have hσ := Nat.lt_size_self σ
  have h1 : (2 : ℕ) ^ Nat.size T ≤ 2 ^ (Nat.size T + Nat.size σ) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (2 : ℕ) ^ Nat.size σ ≤ 2 ^ (Nat.size T + Nat.size σ) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (2 : ℕ) ^ (Nat.size T + Nat.size σ + 1) = 2 ^ (Nat.size T + Nat.size σ) * 2 := by ring
  omega

/-- **The run of the interpreter machine fits in the tableau**: under the validity hypotheses
and `|a|, |b| ≤ T`, its accepting run is at most `Sof (eOf T σ)` steps. -/
theorem runBound_le_two_pow (D : Prog) (n T Q σ : ℕ) (x y a b : BitStr)
    (hV : Valid D n T Q σ x y) (ha : a.length ≤ T) (hb : b.length ≤ T) :
    runBound D n x y a b T ≤ Sof (eOf T σ) := by
  have h1 := runBound_le D n T Q σ x y a b hV ha hb
  have h2 := sum_le_two_pow T σ
  have h3 : (T + σ + 1) ^ 5 ≤ (2 ^ (Nat.size T + Nat.size σ + 1)) ^ 5 :=
    Nat.pow_le_pow_left h2 5
  have h4 : (2 ^ (Nat.size T + Nat.size σ + 1)) ^ 5 = 2 ^ (5 * Nat.size T + 5 * Nat.size σ + 5) := by
    rw [← pow_mul]
    ring_nf
  have h5 : (400000 : ℕ) ≤ 2 ^ 19 := by norm_num
  calc runBound D n x y a b T ≤ 400000 * (T + σ + 1) ^ 5 := h1
    _ ≤ 2 ^ 19 * 2 ^ (5 * Nat.size T + 5 * Nat.size σ + 5) := by
        rw [← h4]; exact Nat.mul_le_mul h5 h3
    _ = 2 ^ (5 * Nat.size T + 5 * Nat.size σ + 24) := by rw [← pow_add]; ring_nf
    _ = Sof (eOf T σ) := by rw [Sof, eOf]

end MIPRE.TM.CookLevin.Desc
