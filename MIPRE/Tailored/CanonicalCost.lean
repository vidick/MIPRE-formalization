/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Canonical
public import MIPRE.Foundations.CL.DetypingProgParse

@[expose] public section

/-!
# The running time of the canonical decider

P1b deferred the cost of the canonical decider `canonProg L LP` (`MIPRE.Tailored.Canonical`):
a bound on the running time of a decider in `MIPRE.Verifier.TimeBoundAt` quantifies over every
input `(n, d)`, malformed ones included, while the steps of `canonProg` are polynomial-time
functions, whose bounds hold on encodings only. This file puts a total parse in front
(`parseDIn`, the identity on encodings, `canonProgT L LP`) and bounds the running time.

* `pushProg_runs_le`: running a step and pushing its output costs the two runs and the sizes.
-/

namespace MIPRE.Cost.Prog

open Data

theorem pushProg_runs_le {F P : Prog} (hP : P.WellScoped 1) {s v r : Data} {t₁ t₂ : ℕ}
    (h₁ : F.Runs s v t₁) (h₂ : P.Runs v r t₂) :
    ∃ t ≤ t₁ + t₂ + v.size + r.size + s.size + 8, (pushProg F P).Runs s (.cons r s) t := by
  have hcall : Eval [v, s] (.let_ (.var 0) P) r ((v.size + 1) + t₂ + 1) :=
    Eval.let_ (Eval.var_of_get (env := [v, s]) (i := 0) rfl)
      (Eval.append_of_wellScoped (env := [v]) h₂ hP [v, s])
  have hcons : Eval [r, v, s] (.cons (.var 0) (.var 2)) (.cons r s)
      ((r.size + 1) + (s.size + 1) + 1) :=
    Eval.cons (Eval.var_of_get (env := [r, v, s]) (i := 0) rfl)
      (Eval.var_of_get (env := [r, v, s]) (i := 2) rfl)
  refine ⟨_, ?_, Eval.let_ h₁ (Eval.let_ hcall hcons)⟩
  omega

end MIPRE.Cost.Prog

namespace MIPRE.Tailored

open Cost Cost.PolyTimeFun Cost.Data CL.Detyping.Program

/-! ## The total parse -/

/-- Read a decider's input `(n, x, y, a, b)` off any data, the identity on encodings. -/
noncomputable def parseDIn : PolyTimeFun Data DIn :=
  (readNat.comp treeHead).pair ((readBits.comp (treeHead.comp treeTail)).pair
    ((readBits.comp (treeHead.comp (treeTail.comp treeTail))).pair
      ((readBits.comp (treeHead.comp (treeTail.comp (treeTail.comp treeTail)))).pair
        (readBits.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))))))

theorem parseDIn_encode (i : DIn) : parseDIn (encode i) = i := by
  obtain ⟨n, x, y, a, b⟩ := i
  simp only [parseDIn, pair_apply, comp_apply, encode_prod, treeHead_cons, treeTail_cons,
    readNat_encode, readBits_encode]

/-- **The canonical decider with a total parse in front.** -/
noncomputable def canonProgT (L P : Prog) : Prog := seqProg parseDIn.code (canonProg L P)

theorem canonProgT_wellScoped {L P : Prog} (hL : L.WellScoped 1) (hP : P.WellScoped 1) :
    (canonProgT L P).WellScoped 1 :=
  seqProg_closed parseDIn.closed (canonProg_wellScoped hL hP)

/-- **On encoded inputs the parse changes nothing.** -/
theorem canonProgT_runs_iff {L P : Prog} (hL : L.WellScoped 1) (hP : P.WellScoped 1) (i : DIn)
    (out : Data) :
    (∃ t, (canonProgT L P).Runs (encode i) out t) ↔ ∃ t, (canonProg L P).Runs (encode i) out t := by
  obtain ⟨tp, -, hp⟩ := parseDIn.computes (encode i : Data)
  rw [parseDIn_encode, encode_data] at hp
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨y, s, u, h₁, h₂⟩ := seqProg_inv (canonProg_wellScoped hL hP) h
    obtain ⟨rfl, -⟩ := Eval.deterministic h₁ hp
    exact ⟨u, h₂⟩
  · rintro ⟨t, h⟩
    exact ⟨_, seqProg_runs (canonProg_wellScoped hL hP) hp h⟩

/-! ## One step: a call of an input program, pushed onto the state -/

/-- **A step of the canonical decider, timed**: from the state `s`, build the input `F s` of a
program `Q` whose first component is the index `n`, run `Q` within its time bound, and push the
output. -/
theorem step_runs {σ β : Type*} [SizedEncoding σ] [SizedEncoding β] (F : PolyTimeFun σ (ℕ × β))
    {Q : Prog} (hQ : Q.WellScoped 1) {n T k : ℕ}
    (hQt : ∀ d : Data, HaltsWithin Q (.cons (encode n) d) (T * (d.size + 1) ^ k)) (s : σ)
    (hn : (F s).1 = n) :
    ∃ (r : Data) (t : ℕ), (Prog.pushProg F.code Q).Runs (encode s) (encode ((r, s) : Data × σ)) t ∧
      r.size ≤ T * esize (F s) ^ k ∧
      t ≤ 2 * F.timeBound.eval (esize s) + 2 * (T * esize (F s) ^ k) + esize s + 8 := by
  obtain ⟨t₁, ht₁, h₁⟩ := F.computes s
  have henc : (encode (F s) : Data) = .cons (encode n) (encode (F s).2) := by
    rw [← hn]; rfl
  obtain ⟨r, t₂, ht₂, h₂⟩ := hQt (encode (F s).2)
  have hsz : (encode (F s).2 : Data).size + 1 ≤ t₁ := by
    have := h₁.size_le
    rw [henc, Data.size_cons] at this
    omega
  have hsz' : (encode (F s).2 : Data).size + 1 ≤ esize (F s) := by
    unfold esize; rw [henc, Data.size_cons]; omega
  have ht₂' : t₂ ≤ T * esize (F s) ^ k :=
    ht₂.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz' _))
  rw [← henc] at h₂
  obtain ⟨t, ht, hrun⟩ := Prog.pushProg_runs_le hQ h₁ h₂
  have hv : (encode (F s) : Data).size ≤ t₁ := h₁.size_le
  have hr : r.size ≤ t₂ := Eval.size_le h₂
  refine ⟨r, t, ?_, hr.trans ht₂', ?_⟩
  · simpa [encode_prod, encode_data] using hrun
  · unfold esize at *
    omega

end MIPRE.Tailored

end
