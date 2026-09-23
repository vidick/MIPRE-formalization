/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.Cost.While
import MIPRE.Foundations.CL.DetypingProgParse
import MIPRE.Foundations.LowDegree.UnaryDegreeArithmetic
import MIPRE.Foundations.CL.DetypingProgCall

/-!
# Unary arithmetic by loops

The routines the pipeline's parameter computations need, whose running time is polynomial in the
*value* of their input rather than its size: writing a binary number in unary (`toUnaryProg`)
and raising a unary number to a binary power (`powProg`). Both are `whileProg` loops
(`MIPRE/Foundations/Cost/While`) of polynomial-time steps.
-/

namespace MIPRE.Pipeline

open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic

/-- A unary numeral, read off its encoding. -/
noncomputable def readUnary : PolyTimeFun Data Unary :=
  (map (const ())).comp (ofEncodeEq rawList encode_rawList)

theorem rawList_encode {α : Type*} [SizedEncoding α] (l : List α) :
    rawList (encode l) = l.map encode := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [encode_list_cons]; simp only [rawList, ih, List.map_cons]

@[simp] theorem readUnary_encode (u : Unary) : readUnary (encode u) = u := by
  change (rawList (encode u)).map (fun _ => ()) = u
  rw [rawList_encode, List.map_map]
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.map_cons, ih]

/-! ## Binary to unary -/

/-- One step of the conversion, on `(x, acc)`: stop with `acc` at `x = 0`, else move one unit. -/
noncomputable def toUnaryStep : PolyTimeFun Data (Bool × Data) :=
  let x := readNat.comp treeHead
  let acc := readUnary.comp treeTail
  ite (ap₂ SAT.ArrayProg.eqNat x (const 0)) ((const false).pair (encoded.comp acc))
    ((const true).pair (encoded.comp ((predN.comp x).pair ((const ()).cons acc))))

theorem toUnaryStep_zero (acc : Unary) :
    toUnaryStep (encode ((0 : ℕ), acc)) = (false, encode acc) := by
  simp [toUnaryStep, encode_prod, readNat_encode]

theorem toUnaryStep_succ (x : ℕ) (acc : Unary) :
    toUnaryStep (encode (x + 1, acc)) = (true, encode (x, () :: acc)) := by
  simp [toUnaryStep, encode_prod, readNat_encode]

/-- **Binary to unary**: `encode x ↦ encode (unary x)`. -/
noncomputable def toUnaryProg : Prog :=
  seqProg (encoded.comp ((readNat).pair (const ([] : Unary)))).code (whileProg toUnaryStep)

theorem toUnaryProg_closed : toUnaryProg.WellScoped 1 :=
  seqProg_closed (PolyTimeFun.closed _) (whileProg_closed _)

theorem toUnaryProg_runs (x : ℕ) : ∃ t, toUnaryProg.Runs (encode x) (encode (unary x)) t := by
  obtain ⟨t₀, -, h₀⟩ := (encoded.comp ((readNat).pair (const ([] : Unary)))).computes (encode x)
  have hi : (encoded.comp ((readNat).pair (const ([] : Unary)))) (encode x) =
      encode (x, ([] : Unary)) := by simp [readNat_encode]
  rw [hi] at h₀
  obtain ⟨t, -, hrun⟩ := whileProg_runs toUnaryStep x (fun i => encode (x - i, unary i))
    (encode (unary x)) (fun i hi => by
      obtain ⟨y, hy⟩ : ∃ y, x - i = y + 1 := ⟨x - i - 1, by omega⟩
      rw [hy, toUnaryStep_succ, show x - (i + 1) = y by omega]
      simp [unary, List.replicate_succ])
    (by simp only [Nat.sub_self, toUnaryStep_zero])
  exact ⟨_, seqProg_runs (whileProg_closed _) h₀ (by simpa [unary] using hrun)⟩

/-! ## Powers -/

/-- One step of the power, on `(e, acc, b)`: stop with `acc` at `e = 0`, else multiply by `b`. -/
noncomputable def powStep : PolyTimeFun Data (Bool × Data) :=
  let e := readNat.comp treeHead
  let acc := readUnary.comp (treeHead.comp treeTail)
  let b := readUnary.comp (treeTail.comp treeTail)
  ite (ap₂ SAT.ArrayProg.eqNat e (const 0)) ((const false).pair (encoded.comp acc))
    ((const true).pair (encoded.comp ((predN.comp e).pair ((mulUnaryProg.comp (acc.pair b)).pair
      b))))

theorem powStep_zero (acc b : Unary) :
    powStep (encode ((0 : ℕ), acc, b)) = (false, encode acc) := by
  simp [powStep, encode_prod, readNat_encode]

theorem powStep_succ (e : ℕ) (acc b : Unary) :
    powStep (encode (e + 1, acc, b)) = (true, encode (e, unary (acc.length * b.length), b)) := by
  simp [powStep, encode_prod, readNat_encode]

/-- **The power**: `encode (b, e) ↦ encode (unary (|b|^e))`. -/
noncomputable def powProg : Prog :=
  seqProg (encoded.comp ((readNat.comp treeTail).pair ((const (unary 1)).pair
    (readUnary.comp treeHead)))).code (whileProg powStep)

theorem powProg_closed : powProg.WellScoped 1 :=
  seqProg_closed (PolyTimeFun.closed _) (whileProg_closed _)

theorem powProg_runs (b : Unary) (e : ℕ) :
    ∃ t, powProg.Runs (encode (b, e)) (encode (unary (b.length ^ e))) t := by
  obtain ⟨t₀, -, h₀⟩ := (encoded.comp ((readNat.comp treeTail).pair ((const (unary 1)).pair
    (readUnary.comp treeHead)))).computes (encode (b, e))
  have hi : (encoded.comp ((readNat.comp treeTail).pair ((const (unary 1)).pair
      (readUnary.comp treeHead)))) (encode (b, e)) = encode (e, unary 1, b) := by
    simp [encode_prod, readNat_encode]
  rw [hi] at h₀
  obtain ⟨t, -, hrun⟩ := whileProg_runs powStep e
    (fun i => encode (e - i, unary (b.length ^ i), b)) (encode (unary (b.length ^ e)))
    (fun i hi => by
      obtain ⟨y, hy⟩ : ∃ y, e - i = y + 1 := ⟨e - i - 1, by omega⟩
      rw [hy, powStep_succ, show e - (i + 1) = y by omega, length_unary, pow_succ])
    (by simp only [Nat.sub_self, powStep_zero])
  exact ⟨_, seqProg_runs (whileProg_closed _) h₀ (by simpa using hrun)⟩

/-! ## Stages -/

/-- A stage of a routine: split the input into an argument and a context, run `p` on the
argument, and combine the context with its answer. -/
noncomputable def stageProg (pre : PolyTimeFun Data Data) (p : Prog)
    (post : PolyTimeFun (Data × Data) Data) : Prog :=
  seqProg pre.code (Prog.callWithContext p post)

theorem stageProg_closed (pre : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) : (stageProg pre p post).WellScoped 1 :=
  seqProg_closed pre.closed (Prog.callWithContext_closed hp post)

theorem stageProg_runs (pre : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (X a ctx r : Data) (t : ℕ)
    (hpre : pre X = .cons a ctx) (hr : p.Runs a r t) :
    ∃ t', (stageProg pre p post).Runs X (post (ctx, r)) t' := by
  obtain ⟨t₀, -, h₀⟩ := pre.computes X
  rw [encode_data, hpre] at h₀
  obtain ⟨t₁, h₁⟩ := Prog.callWithContext_runs hp post a ctx r t hr
  exact ⟨_, seqProg_runs (Prog.callWithContext_closed hp post) h₀ h₁⟩

end MIPRE.Pipeline
