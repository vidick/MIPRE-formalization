/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.CL.Sampler

/-! # Typed samplers with an ambient program

The typed version of the sampler interface in `types.tex`. There is a single
program and a common ambient dimension. A dimension query carries no type;
every other query carries the selected type together with the usual query.
-/

namespace MIPRE.CL

open Cost

inductive TypedSampler.Query (T : Type*)
  | dimension
  | atType (type : T) (query : Sampler.Query)

namespace TypedSampler.Query

variable {T : Type*} [SizedEncoding T]

def toData : Query T → Data
  | .dimension => .nil
  | .atType t q => .cons (encode t) (encode q)

def ofData : Data → Option (Query T)
  | .nil => some .dimension
  | .cons t q => (decode t : Option T).bind fun t' =>
      (decode q : Option Sampler.Query).map (Query.atType t')

@[simp] theorem ofData_toData (q : Query T) : ofData (toData q) = some q := by
  cases q <;> simp [toData, ofData, SizedEncoding.decode_encode]

instance : SizedEncoding (Query T) where
  encode := toData
  decode := ofData
  decode_encode := ofData_toData

end TypedSampler.Query

/-- A typed sampler has one executable query interface for all types, rather
than a nonuniform collection of independently chosen programs. -/
structure TypedSampler (ℓ : ℕ) (T : Type*) [SizedEncoding T] where
  prog : Prog
  closed : prog.WellScoped 1
  dim : ℕ → ℕ
  cl : (n : ℕ) → Player → T → CLFun 𝔽₂ (Fin (dim n)) ℓ
  cl_exactlyOn : ∀ n w t, (cl n w t).ExactlyOn Finset.univ
  runs_dimension : ∀ n, ∃ time,
    prog.Runs (encode (n, (TypedSampler.Query.dimension : TypedSampler.Query T)))
      (encode (dim n)) time
  runs_marginal : ∀ n w t j (z : BitStr), 1 ≤ j → j ≤ ℓ → z.length = dim n →
    ∃ time, prog.Runs (encode (n, TypedSampler.Query.atType t (.marginal w j z)))
      (encode (toBits (((cl n w t).truncate j).eval (ofBits (dim n) z)))) time
  runs_linear : ∀ n w t j (u y : BitStr), 1 ≤ j → j ≤ ℓ →
    (∃ x, u = toBits (((cl n w t).truncate (j - 1)).eval x)) → y.length = dim n →
    ∃ time, prog.Runs (encode (n, TypedSampler.Query.atType t (.linear w j u y)))
      (encode (toBits ((cl n w t).mapOfPrefix (j - 1)
        (ofBits (dim n) u) (ofBits (dim n) y)))) time
  runs_factor : ∀ n w t j (u : BitStr), 1 ≤ j → j ≤ ℓ →
    (∃ x, u = toBits (((cl n w t).truncate (j - 1)).eval x)) →
    ∃ time, prog.Runs (encode (n, TypedSampler.Query.atType t (.factor w j u)))
      (encode (indicatorBits ((cl n w t).factorOfPrefix (j - 1) (ofBits (dim n) u)))) time
  halts : ∀ (n : ℕ) (d : Data), Halts prog (.cons (encode n) d)

namespace TypedSampler

variable {ℓ : ℕ} {T : Type*} [SizedEncoding T]

def TimeBoundAt (S : TypedSampler ℓ T) (n B k : ℕ) : Prop :=
  ∀ d, HaltsWithin S.prog (.cons (encode n) d) (B * (d.size + 1) ^ k)

theorem TimeBoundAt.mono {S : TypedSampler ℓ T} {n B k B' k' : ℕ}
    (h : S.TimeBoundAt n B k) (hB : B ≤ B') (hk : k ≤ k') :
    S.TimeBoundAt n B' k' := by
  intro d
  obtain ⟨r, t, ht, hr⟩ := h d
  exact ⟨r, t, ht.trans (Nat.mul_le_mul hB (Nat.pow_le_pow_right (by omega) hk)), hr⟩

end TypedSampler
end MIPRE.CL
