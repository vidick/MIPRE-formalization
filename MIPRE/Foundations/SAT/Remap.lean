/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Foundations.SAT.Flatten
import MIPRE.Foundations.Cost.Reader

/-!
# Renaming the input variables of a formula

`Fml.remap ρ` renames every input variable of a formula, so that `eval x (remap ρ f)` is
`eval (x ∘ ρ) f`. It is what lets a describer already built on one input layout be reused
inside a larger one: the decoupled 5SAT describer of `lem:decoupled-5sat` embeds the 3SAT
describer of `thm:succinct-sat` by renaming its `3r₀ + 3` inputs into the five-block layout,
instead of composing the two *circuits*, which would mean concatenating gate lists with index
shifts and re-proving well-formedness through both.

On the post-order list a renaming is a `map` — only `Node.inp` changes — so `remapP` is
`mapWith` over the serialization and costs nothing beyond it
(`planning/decoupled-5sat.md`, A1a).
-/

namespace MIPRE.SAT

open Cost Cost.PolyTimeFun

namespace Fml

/-! ## On formulas -/

/-- Renaming the input variables of a formula. -/
def remap (ρ : ℕ → ℕ) : Fml → Fml
  | inp i => inp (ρ i)
  | const b => const b
  | and f g => and (remap ρ f) (remap ρ g)
  | or f g => or (remap ρ f) (remap ρ g)
  | not f => not (remap ρ f)

@[simp] theorem eval_remap (ρ : ℕ → ℕ) (x : ℕ → Bool) : ∀ f : Fml,
    (remap ρ f).eval x = f.eval (fun i => x (ρ i))
  | inp _ => rfl
  | const _ => rfl
  | and f g => by rw [remap, eval, eval, eval_remap ρ x f, eval_remap ρ x g]
  | or f g => by rw [remap, eval, eval, eval_remap ρ x f, eval_remap ρ x g]
  | not f => by rw [remap, eval, eval, eval_remap ρ x f]

@[simp] theorem size_remap (ρ : ℕ → ℕ) : ∀ f : Fml, (remap ρ f).size = f.size
  | inp _ => rfl
  | const _ => rfl
  | and f g => by rw [remap, size, size, size_remap ρ f, size_remap ρ g]
  | or f g => by rw [remap, size, size, size_remap ρ f, size_remap ρ g]
  | not f => by rw [remap, size, size, size_remap ρ f]

theorem InputsLt.remap {n m : ℕ} (ρ : ℕ → ℕ) (hρ : ∀ i, i < n → ρ i < m) : ∀ f : Fml,
    f.InputsLt n → (Fml.remap ρ f).InputsLt m
  | inp i, hf => hρ i hf
  | const _, _ => trivial
  | and a b, hf => ⟨InputsLt.remap ρ hρ a hf.1, InputsLt.remap ρ hρ b hf.2⟩
  | or a b, hf => ⟨InputsLt.remap ρ hρ a hf.1, InputsLt.remap ρ hρ b hf.2⟩
  | not a, hf => InputsLt.remap ρ hρ a hf

/-- **A formula reads only the inputs it names**: two assignments agreeing below `n` give it
the same value. -/
theorem eval_congr_of_lt {n : ℕ} {x y : ℕ → Bool} (h : ∀ i, i < n → x i = y i) :
    ∀ f : Fml, f.InputsLt n → f.eval x = f.eval y
  | inp i, hf => h i hf
  | const _, _ => rfl
  | and a b, hf => by rw [eval, eval, eval_congr_of_lt h a hf.1, eval_congr_of_lt h b hf.2]
  | or a b, hf => by rw [eval, eval, eval_congr_of_lt h a hf.1, eval_congr_of_lt h b hf.2]
  | not a, hf => by rw [eval, eval, eval_congr_of_lt h a hf]

/-! ## On the post-order list -/

/-- A renaming on nodes: only an input node changes. -/
def Node.remap (ρ : ℕ → ℕ) : Node → Node
  | .inp i => .inp (ρ i)
  | .const b => .const b
  | .and => .and
  | .or => .or
  | .not => .not

/-- **A renaming is a `map` on the serialization.** -/
theorem rpn_remap (ρ : ℕ → ℕ) : ∀ f : Fml,
    (Fml.remap ρ f).rpn = f.rpn.map (Node.remap ρ)
  | inp _ => rfl
  | const _ => rfl
  | and f g => by
    rw [Fml.remap, rpn, rpn, rpn_remap ρ f, rpn_remap ρ g, List.map_append, List.map_append]
    rfl
  | or f g => by
    rw [Fml.remap, rpn, rpn, rpn_remap ρ f, rpn_remap ρ g, List.map_append, List.map_append]
    rfl
  | not f => by
    rw [Fml.remap, rpn, rpn, rpn_remap ρ f, List.map_append]
    rfl

/-! ## As a program -/

section Prog

variable {γ : Type*} [SizedEncoding γ]

/-- A renaming of nodes, the renaming itself read off a parameter. -/
noncomputable def Node.remapP (R : PolyTimeFun (γ × ℕ) ℕ) :
    PolyTimeFun (Node × γ) Node :=
  (PolyTimeFun.casesNode ((PolyTimeFun.tagged 0 Node.inp Node.encode_inp).comp R)
      ((PolyTimeFun.tagged 1 Node.const Node.encode_const).comp snd)
      (PolyTimeFun.const Node.and) (PolyTimeFun.const Node.or)
      (PolyTimeFun.const Node.not)).comp (snd.pair fst)

@[simp] theorem Node.remapP_apply (R : PolyTimeFun (γ × ℕ) ℕ) (p : Node × γ) :
    Node.remapP R p = Node.remap (fun i => R (p.2, i)) p.1 := by
  obtain ⟨nd, g⟩ := p
  cases nd <;> rfl

/-- `Fml.remap`, the renaming read off a parameter. -/
noncomputable def remapP (R : PolyTimeFun (γ × ℕ) ℕ) : PolyTimeFun (Fml × γ) Fml :=
  PolyTimeFun.cast ((mapWith (Node.remapP R)).comp ((rpnF.comp fst).pair snd))
    (fun p => Fml.remap (fun i => R (p.2, i)) p.1) (by
      rintro ⟨f, g⟩
      show (encode (Fml.remap (fun i => R (g, i)) f) : Data) = encode _
      rw [encode_fml, rpn_remap]
      simp only [comp_apply, mapWith_apply, pair_apply, fst_apply, snd_apply, rpnF_apply,
        Node.remapP_apply])

@[simp] theorem remapP_apply (R : PolyTimeFun (γ × ℕ) ℕ) (p : Fml × γ) :
    remapP R p = Fml.remap (fun i => R (p.2, i)) p.1 := rfl

end Prog

end Fml

end MIPRE.SAT
