/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MIPRE.Foundations.Introspection.BasisProg

/-! # Executable binary field blocks

A bounded scan splits an explicitly supplied number of fixed-width blocks.
Short inputs produce short or empty final blocks and long suffixes are ignored;
the program is total on all inputs. Canonical-width inputs split and flatten
exactly. Combined conversion interprets the flat CL vector in the constructed
self-dual basis and returns the field arithmetic's canonical Shoup rows.
-/

noncomputable section
namespace MIPRE.Introspection.BinaryBlock
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram

def splitBlocks : ℕ → ℕ → BitStr → List BitStr
  | 0, _, _ => []
  | n + 1, k, v => v.take k :: splitBlocks n k (v.drop k)

theorem splitBlocks_length (n k : ℕ) (v : BitStr) : (splitBlocks n k v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [splitBlocks, ih]

private def splitStep : PolyTimeFun ((BitStr × List BitStr) × Unary) (BitStr × List BitStr) :=
  (drop.comp ((fst.comp fst).pair snd)).pair
    (cons (take.comp ((fst.comp fst).pair snd)) (snd.comp fst))

private theorem splitStep_apply (v : BitStr) (vs : List BitStr) (k : Unary) :
    splitStep ((v, vs), k) = (v.drop k.length, v.take k.length :: vs) := rfl

private theorem splitStep_fold (n : ℕ) (k : Unary) (v : BitStr) (vs : List BitStr) :
    ((List.replicate n k).foldl splitStep.step (v, vs)).2 =
      (splitBlocks n k.length v).reverse ++ vs := by
  induction n generalizing v vs with
  | zero => simp [splitBlocks]
  | succ n ih =>
    change ((List.replicate n k).foldl splitStep.step
      (v.drop k.length, v.take k.length :: vs)).2 = _
    rw [ih]
    simp [splitBlocks, List.append_assoc]

/-- Inputs are number of blocks, block width, and flat bits, in that order. -/
def splitBlocksProg : PolyTimeFun (Unary × Unary × BitStr) (List BitStr) :=
  let scan := foldlAdd splitStep 2 (by
    rintro ⟨v, vs⟩ k
    have he := esize_list_append (v.take k.length) (v.drop k.length)
    rw [List.take_append_drop] at he
    simp only [splitStep_apply, esize_prod, esize_list_cons, eval_ofNat]
    omega)
  congr ((PolyTimeFun.reverse.comp snd).comp (scan.comp
    ((replicate.comp (fst.pair (fst.comp snd))).pair ((snd.comp snd).pair (const [])))))
    (fun p => splitBlocks p.1.length p.2.1.length p.2.2) (by
      rintro ⟨n, k, v⟩
      change (((List.replicate n.length k).foldl splitStep.step (v, [])).2).reverse = _
      rw [splitStep_fold, List.append_nil, List.reverse_reverse])

theorem splitBlocksProg_apply (n k : Unary) (v : BitStr) :
    splitBlocksProg (n, k, v) = splitBlocks n.length k.length v := rfl

/-- Concatenation is an actual ambient program with a polynomial bound. -/
def flattenProg : PolyTimeFun (List BitStr) BitStr :=
  congr ((foldlAdd append X (by
    intro l r
    have h := esize_list_append l r
    simp only [append_apply, eval_X]
    omega)).comp ((PolyTimeFun.id _).pair (const []))) List.flatten (by
      intro l
      change l.foldl (fun a b => a ++ b) [] = l.flatten
      simpa using (List.foldl_append_eq_append (l := l) (l' := []) (f := fun b => b)))

theorem flattenProg_apply (vs : List BitStr) : flattenProg vs = vs.flatten := rfl

theorem splitBlocks_flatten (k : ℕ) (vs : List BitStr)
    (hv : ∀ v ∈ vs, v.length = k) : splitBlocks vs.length k vs.flatten = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hlen := hv v (by simp)
    have ht : (v ++ vs.flatten).take k = v := by rw [← hlen, List.take_left]
    have hd : (v ++ vs.flatten).drop k = vs.flatten := by rw [← hlen, List.drop_left]
    simp only [List.length_cons, splitBlocks, List.flatten_cons, ht, hd]
    rw [ih (fun w hw => hv w (by simp [hw]))]

theorem splitBlocksProg_flatten (k : ℕ) (vs : List BitStr)
    (hv : ∀ v ∈ vs, v.length = k) :
    splitBlocksProg (unary vs.length, unary k, flattenProg vs) = vs := by
  simp only [splitBlocksProg_apply, length_unary, flattenProg_apply]
  exact splitBlocks_flatten k vs hv

/-- Read a flat self-dual vector as canonical Shoup field rows. -/
def decodeBlocksProg : PolyTimeFun (Unary × Unary × BitStr) (List BitStr) :=
  fromSelfDualRowsProg.comp ((fst.comp snd).pair splitBlocksProg)

/-- Write canonical Shoup rows as the flat self-dual CL vector. -/
def encodeBlocksProg : PolyTimeFun (Unary × List BitStr) BitStr :=
  flattenProg.comp toSelfDualRowsProg

theorem decodeBlocksProg_apply (n k : Unary) (v : BitStr) :
    decodeBlocksProg (n, k, v) = fromSelfDualRowsProg (k, splitBlocks n.length k.length v) := rfl

theorem encodeBlocksProg_apply (k : Unary) (vs : List BitStr) :
    encodeBlocksProg (k, vs) = (toSelfDualRowsProg (k, vs)).flatten := rfl

theorem encodeBlocksProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    encodeBlocksProg (unary k, (shoupBinField k hk).vecBits u) =
      (List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))).flatten := by
  rw [encodeBlocksProg_apply, toSelfDualRowsProg_correct k hk hodd]

theorem decodeBlocksProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    decodeBlocksProg (unary n, unary k,
      (List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))).flatten) =
      (shoupBinField k hk).vecBits u := by
  rw [decodeBlocksProg_apply, length_unary, length_unary]
  have he := splitBlocks_flatten k
    (List.ofFn fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i))) (by
      intro v hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      simp [vectorBits])
  simp only [List.length_ofFn] at he
  rw [he, fromSelfDualRowsProg_correct k hk hodd]

theorem decodeBlocksProg_encodeBlocksProg (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    decodeBlocksProg (unary n, unary k,
      encodeBlocksProg (unary k, (shoupBinField k hk).vecBits u)) =
      (shoupBinField k hk).vecBits u := by
  rw [encodeBlocksProg_correct k hk hodd, decodeBlocksProg_correct k hk hodd]

theorem splitBlocksProg_runs (x : Unary × Unary × BitStr) :
    ∃ r ≤ splitBlocksProg.timeBound.eval (esize x),
      splitBlocksProg.code.Runs (encode x) (encode (splitBlocksProg x)) r :=
  splitBlocksProg.computes x

theorem decodeBlocksProg_runs (x : Unary × Unary × BitStr) :
    ∃ r ≤ decodeBlocksProg.timeBound.eval (esize x),
      decodeBlocksProg.code.Runs (encode x) (encode (decodeBlocksProg x)) r :=
  decodeBlocksProg.computes x

theorem encodeBlocksProg_runs (x : Unary × List BitStr) :
    ∃ r ≤ encodeBlocksProg.timeBound.eval (esize x),
      encodeBlocksProg.code.Runs (encode x) (encode (encodeBlocksProg x)) r :=
  encodeBlocksProg.computes x

end MIPRE.Introspection.BinaryBlock
end
