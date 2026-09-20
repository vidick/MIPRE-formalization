/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Pcp
import MIPRE.Foundations.SAT.ArrayProg
import MIPRE.Foundations.Cost.BinaryCompare
import MIPRE.Foundations.Cost.BinaryArithmetic
import MIPRE.Foundations.Cost.SizeProgram

/-! # Executable specification and view checks for the classical PCP -/

namespace MIPRE.SAT

open Cost Cost.PolyTimeFun Polynomial

private noncomputable def andProg : PolyTimeFun (Bool × Bool) Bool :=
  congr (ite fst snd (const false)) (fun p => p.1 && p.2)
    (by rintro ⟨a, b⟩; cases a <;> rfl)

private theorem fold_and (l : List Bool) (a : Bool) :
    l.foldl (fun b c => b && c) a = (a && l.all id) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons, ih, List.all_cons, id_eq, Bool.and_assoc]

private theorem esize_bool_le (b : Bool) : esize b ≤ 3 := by cases b <;> decide

/-- Test all supplied bits without interpreting their number as a binary magnitude. -/
noncomputable def allBoolProg : PolyTimeFun (List Bool) Bool :=
  let scan := foldlAdd andProg 3 (by
    intro s a
    have hb := esize_bool_le (andProg (s, a))
    simp only [Polynomial.eval_ofNat]
    omega)
  congr (scan.comp ((PolyTimeFun.id _).pair (const true))) (fun l => l.all id) (by
    intro l
    change l.foldl (fun a b => a && b) true = _
    rw [fold_and]
    rfl)

@[simp] theorem allBoolProg_apply (l : List Bool) : allBoolProg l = l.all id := rfl

/-- Check a list of coefficient widths against a binary-specified field degree. -/
noncomputable def widthsProg : PolyTimeFun (ℕ × List BitStr) Bool :=
  let item : PolyTimeFun (BitStr × ℕ) Bool :=
    ArrayProg.eqNat.comp ((unaryToBin.comp (length.comp fst)).pair snd)
  congr (allBoolProg.comp ((mapWith item).comp (snd.pair fst)))
    (fun p => p.2.all (fun b => decide (b.length = p.1))) (by intro p; simp [item])

@[simp] theorem widthsProg_apply (p : ℕ × List BitStr) :
    widthsProg p = p.2.all (fun b => decide (b.length = p.1)) := rfl

theorem widthsProg_true_iff (p : ℕ × List BitStr) :
    widthsProg p = true ↔ ∀ b ∈ p.2, b.length = p.1 := by simp

/-- The five finite conditions making a decider specification valid. -/
def validBool (p : DescInput) : Bool :=
  decide (p.1.2.2.2.1 ≤ p.1.2.2.1) &&
  decide (2 * Nat.size p.1.2.1 ≤ p.1.2.2.1) &&
  decide (esize p.1.1 ≤ p.1.2.2.2.2) &&
  decide (p.2.1.length ≤ p.1.2.2.2.1) && decide (p.2.2.length ≤ p.1.2.2.2.1)

/-- Uniform specification checking, including the actual encoded program size. -/
noncomputable def validProg : PolyTimeFun DescInput Bool :=
  let pars : PolyTimeFun DescInput (ℕ × ℕ × ℕ × ℕ) := snd.comp fst
  let n := fst.comp pars
  let T := fst.comp (snd.comp pars)
  let Q := fst.comp (snd.comp (snd.comp pars))
  let σ := snd.comp (snd.comp (snd.comp pars))
  let bits : PolyTimeFun ℕ BitStr := ofEncodeEq Nat.bits (fun _ => rfl)
  let logBits := length.comp (bits.comp n)
  let logn := unaryToBin.comp (append.comp (logBits.pair logBits))
  let progSize := unaryToBin.comp ((encodedSizeU Prog).comp (fst.comp fst))
  let lx := unaryToBin.comp (length.comp (fst.comp snd))
  let ly := unaryToBin.comp (length.comp (snd.comp snd))
  let c₁ := leNat.comp (Q.pair T)
  let c₂ := leNat.comp (logn.pair T)
  let c₃ := leNat.comp (progSize.pair σ)
  let c₄ := leNat.comp (lx.pair Q)
  let c₅ := leNat.comp (ly.pair Q)
  congr (ap₂ andProg (ap₂ andProg (ap₂ andProg (ap₂ andProg c₁ c₂) c₃) c₄) c₅)
    validBool (by intro p; simp [andProg, c₁, c₂, c₃, c₄, c₅, pars, n, T, Q, σ,
      logn, logBits, bits, progSize, lx, ly, validBool, two_mul, Nat.size_eq_bits_len])

@[simp] theorem validProg_apply (p : DescInput) : validProg p = validBool p := rfl

theorem validProg_true_iff (D : Prog) (n T Q σ : ℕ) (x y : BitStr) :
    validProg ((D, n, T, Q, σ), x, y) = true ↔ Valid D n T Q σ x y := by
  simp only [validProg_apply, validBool, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨hQ, hn⟩, hσ⟩, hx⟩, hy⟩
    exact ⟨hQ, hn, hσ, hx, hy⟩
  · intro h
    exact ⟨⟨⟨⟨h.q_le, h.logn_le⟩, h.size_le⟩, h.x_le⟩, h.y_le⟩

/-- Check both coordinate-list lengths and every field coefficient width.
The first input pair supplies the binary degree and outer dimension. -/
noncomputable def viewFormatProg :
    PolyTimeFun ((ℕ × ℕ) × List BitStr × List BitStr) Bool :=
  let k : PolyTimeFun ((ℕ × ℕ) × List BitStr × List BitStr) ℕ := fst.comp fst
  let m := snd.comp fst
  let z := fst.comp snd
  let ev := snd.comp snd
  let lz := unaryToBin.comp (length.comp z)
  let lev := unaryToBin.comp (length.comp ev)
  let expect := addUnary.comp (m.pair (const (unary 6)))
  let lengths := ap₂ andProg (ArrayProg.eqNat.comp (lz.pair m))
    (ArrayProg.eqNat.comp (lev.pair expect))
  ap₂ andProg (ap₂ andProg lengths (widthsProg.comp (k.pair z))) (widthsProg.comp (k.pair ev))

theorem viewFormatProg_true_iff (P : PcpParams) (z ev : List BitStr) :
    viewFormatProg ((P.k, P.m'), z, ev) = true ↔ ViewFormat P z ev := by
  simp only [viewFormatProg, ap₂_apply, andProg, congr_apply, comp_apply, pair_apply,
    ArrayProg.eqNat_apply, unaryToBin_apply, length_apply, length_unary, fst_apply,
    snd_apply, addUnary_apply, const_apply, Bool.and_eq_true, decide_eq_true_eq,
    widthsProg_true_iff]
  constructor
  · rintro ⟨⟨⟨hz, he⟩, hwz⟩, hwe⟩
    exact ⟨hz, by omega, hwz, hwe⟩
  · intro h
    exact ⟨⟨⟨h.length_z, by rw [h.length_ev]; omega⟩, h.width_z⟩, h.width_ev⟩

end MIPRE.SAT
