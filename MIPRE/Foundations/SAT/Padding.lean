/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.SAT.Decoupled

/-!
# Padding decoupled descriptions

The semantic content of `prop:exciting-padding-prop` in `answer_reduction.tex`.
The original clauses are embedded in the larger five blocks. Additional clauses
force both answer tails to be blank tapes; the three auxiliary tails are free.
In particular, the conclusion preserves `Circuit.DescribesDecider`, which specifies
every answer bit, rather than merely preserving the accepted answer prefixes.
The circuit construction and its running time are separate obligations.
-/

namespace MIPRE.SAT

namespace Clause5

variable {A B C D E A' B' C' D' E' : Type*}

/-- Rename the variables in each of the five separate blocks. -/
def map (f₁ : A → A') (f₂ : B → B') (f₃ : C → C') (f₄ : D → D') (f₅ : E → E')
    (c : Clause5 A B C D E) : Clause5 A' B' C' D' E' :=
  ⟨⟨f₁ c.l₁.var, c.l₁.pos⟩, ⟨f₂ c.l₂.var, c.l₂.pos⟩,
    ⟨f₃ c.l₃.var, c.l₃.pos⟩, ⟨f₄ c.l₄.var, c.l₄.pos⟩, ⟨f₅ c.l₅.var, c.l₅.pos⟩⟩

@[simp] theorem eval_map (f₁ : A → A') (f₂ : B → B') (f₃ : C → C')
    (f₄ : D → D') (f₅ : E → E') (c : Clause5 A B C D E)
    (w₁ : A' → Bool) (w₂ : B' → Bool) (w₃ : C' → Bool)
    (w₄ : D' → Bool) (w₅ : E' → Bool) :
    (c.map f₁ f₂ f₃ f₄ f₅).eval w₁ w₂ w₃ w₄ w₅ =
      c.eval (w₁ ∘ f₁) (w₂ ∘ f₂) (w₃ ∘ f₃) (w₄ ∘ f₄) (w₅ ∘ f₅) := rfl

end Clause5

namespace Cnf5

/-- The inclusion of an old block into a larger one. -/
def blockInclusion {n m : ℕ} (h : n ≤ m) : Fin (2 ^ n) → Fin (2 ^ m) :=
  Fin.castLE (Nat.pow_le_pow_right (by decide) h)

/-- Extend a block arbitrarily by `false`; only the three auxiliary blocks use this. -/
def extendBlock {n m : ℕ} (w : Fin (2 ^ n) → Bool) : Fin (2 ^ m) → Bool :=
  fun i => if h : (i : ℕ) < 2 ^ n then w ⟨i, h⟩ else false

@[simp] theorem extendBlock_inclusion {n m : ℕ} (h : n ≤ m) (w : Fin (2 ^ n) → Bool) :
    extendBlock (m := m) w ∘ blockInclusion h = w := by
  funext i
  simp [extendBlock, blockInclusion, i.isLt]

/-- Embed the original clauses and force the two answer tails to contain blanks. -/
def pad {ℓ r ℓ' r' : ℕ} (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (φ : Cnf5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    Cnf5 (Fin (2 ^ ℓ')) (Fin (2 ^ ℓ')) (Fin (2 ^ r')) (Fin (2 ^ r')) (Fin (2 ^ r')) :=
  (Clause5.map (blockInclusion hℓ) (blockInclusion hℓ)
    (blockInclusion hr) (blockInclusion hr) (blockInclusion hr) '' φ) ∪
  {c | (2 ^ ℓ ≤ (c.l₁.var : ℕ) ∧ c.l₁.pos = decide ((c.l₁.var : ℕ) % 2 = 0)) ∨
    (2 ^ ℓ ≤ (c.l₂.var : ℕ) ∧ c.l₂.pos = decide ((c.l₂.var : ℕ) % 2 = 0))}

private def falseLit {n : ℕ} (w : Fin (2 ^ n) → Bool) : Lit (Fin (2 ^ n)) :=
  ⟨0, !(w 0)⟩

private theorem eval_falseLit {n : ℕ} (w : Fin (2 ^ n) → Bool) :
    (falseLit w).eval w = false := by
  cases h : w 0 <;> simp [falseLit, Lit.eval, h]

private theorem lit_true_iff {A : Type*} (w : A → Bool) (i : A) (o : Bool) :
    (⟨i, o⟩ : Lit A).eval w = true ↔ w i = o := by
  cases o <;> cases hw : w i <;> simp [Lit.eval, hw]

/-- Padding satisfaction is exactly original satisfaction and both complete blank tails. -/
theorem sat_pad_iff {ℓ r ℓ' r' : ℕ} (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (φ : Cnf5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
    (a b : Fin (2 ^ ℓ') → Bool) (w₁ w₂ w₃ : Fin (2 ^ r') → Bool) :
    (pad hℓ hr φ).Sat a b w₁ w₂ w₃ ↔
      φ.Sat (a ∘ blockInclusion hℓ) (b ∘ blockInclusion hℓ)
        (w₁ ∘ blockInclusion hr) (w₂ ∘ blockInclusion hr) (w₃ ∘ blockInclusion hr) ∧
      (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → a i = decide ((i : ℕ) % 2 = 0)) ∧
      (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → b i = decide ((i : ℕ) % 2 = 0)) := by
  constructor
  · intro h
    refine ⟨fun c hc => h _ (Or.inl ⟨c, hc, rfl⟩), ?_, ?_⟩
    · intro i hi
      have h' := h ⟨⟨i, decide ((i : ℕ) % 2 = 0)⟩,
        falseLit b, falseLit w₁, falseLit w₂, falseLit w₃⟩ (Or.inr (Or.inl ⟨hi, rfl⟩))
      exact (lit_true_iff a i _).mp (by simpa [Clause5.eval, eval_falseLit] using h')
    · intro i hi
      have h' := h ⟨falseLit a, ⟨i, decide ((i : ℕ) % 2 = 0)⟩,
        falseLit w₁, falseLit w₂, falseLit w₃⟩ (Or.inr (Or.inr ⟨hi, rfl⟩))
      exact (lit_true_iff b i _).mp (by simpa [Clause5.eval, eval_falseLit] using h')
  · rintro ⟨hφ, ha, hb⟩ c (⟨c₀, hc₀, rfl⟩ | ⟨hi, ho⟩ | ⟨hi, ho⟩)
    · exact hφ c₀ hc₀
    · have h : c.l₁.eval a = true := (lit_true_iff a c.l₁.var c.l₁.pos).mpr
        ((ha c.l₁.var hi).trans ho.symm)
      simp [Clause5.eval, h]
    · have h : c.l₂.eval b = true := (lit_true_iff b c.l₂.var c.l₂.pos).mpr
        ((hb c.l₂.var hi).trans ho.symm)
      simp [Clause5.eval, h]

end Cnf5

/-- Beyond twice the answer length the tape is `10`, starting at the even position. -/
theorem tapeBits_eq_blank {s : Cost.BitStr} {T p : ℕ} (hs : s.length ≤ T) (hp : 2 * T ≤ p) :
    tapeBits s p = decide (p % 2 = 0) := by
  have hnone : s[p / 2]? = none := List.getElem?_eq_none (by omega)
  simp only [tapeBits, hnone, cellBits]
  split_ifs with h <;> simp [h]

namespace Circuit

/-- A circuit implementing the padded clause set still describes the same decider,
including the entire answer tapes and their blank tails. -/
theorem DescribesDecider.of_pad {C C' : Circuit} {ℓ r ℓ' r' : ℕ}
    {D : Decider} {n T : ℕ} {x y : Cost.BitStr}
    (hC : C.DescribesDecider ℓ r D n x y T) (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (hT : 2 * T ≤ 2 ^ ℓ)
    (hpad : C'.formula5 ℓ' r' = Cnf5.pad hℓ hr (C.formula5 ℓ r)) :
    C'.DescribesDecider ℓ' r' D n x y T := by
  intro a b
  constructor
  · rintro ⟨w₁, w₂, w₃, hsat⟩
    rw [hpad, Cnf5.sat_pad_iff] at hsat
    obtain ⟨ap, bp, hap, hbp, ha, hb, hacc⟩ :=
      (hC (a ∘ Cnf5.blockInclusion hℓ) (b ∘ Cnf5.blockInclusion hℓ)).mp
        ⟨_, _, _, hsat.1⟩
    refine ⟨ap, bp, hap, hbp, ?_, ?_, hacc⟩
    · intro j
      by_cases hj : (j : ℕ) < 2 ^ ℓ
      · exact ha ⟨j, hj⟩
      · exact (hsat.2.1 j (by omega)).trans (tapeBits_eq_blank hap (by omega)).symm
    · intro j
      by_cases hj : (j : ℕ) < 2 ^ ℓ
      · exact hb ⟨j, hj⟩
      · exact (hsat.2.2 j (by omega)).trans (tapeBits_eq_blank hbp (by omega)).symm
  · rintro ⟨ap, bp, hap, hbp, ha, hb, hacc⟩
    obtain ⟨w₁, w₂, w₃, hsat⟩ :=
      (hC (a ∘ Cnf5.blockInclusion hℓ) (b ∘ Cnf5.blockInclusion hℓ)).mpr
        ⟨ap, bp, hap, hbp, (fun j => ha (Cnf5.blockInclusion hℓ j)),
          (fun j => hb (Cnf5.blockInclusion hℓ j)), hacc⟩
    refine ⟨Cnf5.extendBlock w₁, Cnf5.extendBlock w₂, Cnf5.extendBlock w₃, ?_⟩
    rw [hpad, Cnf5.sat_pad_iff]
    refine ⟨by simpa using hsat, ?_, ?_⟩
    · intro j hj
      exact (ha j).trans (tapeBits_eq_blank hap (by omega))
    · intro j hj
      exact (hb j).trans (tapeBits_eq_blank hbp (by omega))

end Circuit

end MIPRE.SAT
