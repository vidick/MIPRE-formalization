/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import Mathlib.Data.List.Basic

/-!
# A self-delimiting binary code for natural numbers

The prefix-free code used by the machine-description format
(`planning/tm-infrastructure.md`, Milestone C, normative):

`encodeNat n = 1^L 0 d₀ … d_{L-1}`

where `d₀ … d_{L-1}` are the little-endian binary digits of `n` (`Turing.natToBits`;
canonical: the empty string for `0`, and the last digit of a nonzero number is `true`)
and `L` is their count. So `encodeNat 0 = [false]`, and in general
`(encodeNat n).length = 2·L + 1` with `L = ⌈log₂ (n+1)⌉`, characterized here without
`Nat.log2` by `lt_two_pow_natToBits` and `natToBits_length_le`.

The parser `parseNat` accepts *only* canonical digit strings (a digit block ending in
`false` is rejected), which gives genuine canonicality: `parseNat_sound` says every
accepted prefix *is* `encodeNat` of the parsed value. Together with the prefix property
`parseNat_encodeNat`, all downstream codec soundness proofs are compositional
(decision D11).

Everything is structurally recursive — `natToBits` runs on an explicit fuel, with a
fuel-irrelevance lemma — so the kernel can evaluate the whole codec and tests can be
`by decide` (decision D10).
-/

namespace Turing

/-! ## Little-endian binary digits -/

/-- Little-endian binary digits, structurally recursive in an explicit fuel (so that the
kernel can evaluate it); use `Turing.natToBits`, which instantiates the fuel. -/
def natToBitsAux : ℕ → ℕ → List Bool
  | _, 0 => []
  | 0, _ + 1 => []
  | fuel + 1, n + 1 => ((n + 1) % 2 == 1) :: natToBitsAux fuel ((n + 1) / 2)

/-- The little-endian binary digits of a natural number: `[]` for `0`; the last digit of
a nonzero number is `true`. -/
def natToBits (n : ℕ) : List Bool := natToBitsAux n n

/-- The value of a little-endian digit string. -/
def bitsToNat (l : List Bool) : ℕ :=
  l.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0

/-- The digits do not depend on the fuel, as long as there is enough of it. -/
theorem natToBitsAux_congr {f₁ f₂ n : ℕ} (h₁ : n ≤ f₁) (h₂ : n ≤ f₂) :
    natToBitsAux f₁ n = natToBitsAux f₂ n := by
  induction f₁ generalizing f₂ n with
  | zero =>
    obtain rfl : n = 0 := Nat.le_zero.mp h₁
    cases f₂ <;> rfl
  | succ f₁ ih =>
    cases n with
    | zero => cases f₂ <;> rfl
    | succ n =>
      cases f₂ with
      | zero => omega
      | succ f₂ =>
        simp only [natToBitsAux, List.cons.injEq, true_and]
        exact ih (by omega) (by omega)

@[simp]
theorem natToBits_zero : natToBits 0 = [] := rfl

theorem natToBits_succ (n : ℕ) :
    natToBits (n + 1) = ((n + 1) % 2 == 1) :: natToBits ((n + 1) / 2) := by
  show natToBitsAux (n + 1) (n + 1) = _
  simp only [natToBitsAux, List.cons.injEq, true_and]
  exact natToBitsAux_congr (by omega) (Nat.le_refl _)

@[simp]
theorem bitsToNat_nil : bitsToNat [] = 0 := rfl

@[simp]
theorem bitsToNat_cons (b : Bool) (l : List Bool) :
    bitsToNat (b :: l) = 2 * bitsToNat l + (if b then 1 else 0) := rfl

/-- The digits of `2·m` (for `m > 0`): a `false` in front of the digits of `m`. -/
theorem natToBits_two_mul {m : ℕ} (hm : 0 < m) :
    natToBits (2 * m) = false :: natToBits m := by
  cases m with
  | zero => omega
  | succ k =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, natToBits_succ]
    congr 1
    · have h2 : (2 * k + 1 + 1) % 2 = 0 := by omega
      simp [h2]
    · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]

/-- The digits of `2·m + 1`: a `true` in front of the digits of `m`. -/
theorem natToBits_two_mul_add_one (m : ℕ) :
    natToBits (2 * m + 1) = true :: natToBits m := by
  rw [natToBits_succ]
  congr 1
  · have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp [h2]
  · rw [show (2 * m + 1) / 2 = m by omega]

/-- Digits round-trip: the value of the digits of `n` is `n`. -/
@[simp]
theorem bitsToNat_natToBits (n : ℕ) : bitsToNat (natToBits n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [natToBits_succ, bitsToNat_cons, ih ((n + 1) / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> simp [h] <;> omega

/-- Canonicality: no digit string produced by `natToBits` ends in `false`. -/
theorem natToBits_getLast?_ne_false (n : ℕ) : (natToBits n).getLast? ≠ some false := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [natToBits_succ]
      cases hrest : natToBits ((n + 1) / 2) with
      | nil =>
        -- the tail digits are empty, so `(n+1)/2 = 0`, i.e. `n + 1 = 1`
        have hval : (n + 1) / 2 = 0 := by
          have h := bitsToNat_natToBits ((n + 1) / 2)
          rw [hrest] at h
          simpa using h.symm
        have hn : n + 1 = 1 := by omega
        simp [hn]
      | cons b' l' =>
        rw [List.getLast?_cons_cons]
        exact hrest ▸ ih ((n + 1) / 2) (by omega)

/-- A canonical nonempty digit string has positive value. -/
theorem bitsToNat_pos {l : List Bool} (h : l.getLast? = some true) : 0 < bitsToNat l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    cases hl : l with
    | nil =>
      subst hl
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      simp
    | cons b' l' =>
      subst hl
      rw [List.getLast?_cons_cons] at h
      have hpos := ih h
      rw [bitsToNat_cons]
      omega

/-- Digits round-trip the other way: on canonical strings, `natToBits ∘ bitsToNat` is
the identity. -/
theorem natToBits_bitsToNat : ∀ (l : List Bool), l.getLast? ≠ some false →
    natToBits (bitsToNat l) = l
  | [], _ => by simp
  | true :: rest, h => by
    have htail : rest.getLast? ≠ some false := by
      cases rest with
      | nil => simp
      | cons b' l' => rwa [List.getLast?_cons_cons] at h
    have hv : bitsToNat (true :: rest) = 2 * bitsToNat rest + 1 := by simp
    rw [hv, natToBits_two_mul_add_one, natToBits_bitsToNat rest htail]
  | false :: rest, h => by
    have hne : rest ≠ [] := by
      rintro rfl
      simp at h
    have htail : rest.getLast? ≠ some false := by
      cases rest with
      | nil => simp
      | cons b' l' => rwa [List.getLast?_cons_cons] at h
    have hlast : rest.getLast? = some true := by
      cases hgl : rest.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hgl) hne
      | some bb =>
        cases bb with
        | false => exact absurd hgl htail
        | true => rfl
    have hpos := bitsToNat_pos hlast
    have hv : bitsToNat (false :: rest) = 2 * bitsToNat rest := by simp
    rw [hv, natToBits_two_mul hpos, natToBits_bitsToNat rest htail]

/-! ## The length of the digit string -/

/-- `natToBits n` has enough digits for `n`. -/
theorem lt_two_pow_natToBits (n : ℕ) : n < 2 ^ (natToBits n).length := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [natToBits_succ]
      have h := ih ((n + 1) / 2) (by omega)
      simp only [List.length_cons, Nat.pow_succ]
      omega

/-- `natToBits n` has no more digits than any binary bound on `n`. -/
theorem natToBits_length_le : ∀ {n k : ℕ}, n < 2 ^ k → (natToBits n).length ≤ k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => intro k _; simp
    | n + 1 =>
      intro k h
      cases k with
      | zero =>
        rw [Nat.pow_zero] at h
        omega
      | succ k =>
        rw [natToBits_succ]
        simp only [List.length_cons]
        have hdiv : (n + 1) / 2 < 2 ^ k := by
          rw [Nat.pow_succ] at h
          omega
        have := ih ((n + 1) / 2) (by omega) hdiv
        omega

/-- The digit count is monotone. -/
theorem natToBits_length_mono {m n : ℕ} (h : m ≤ n) :
    (natToBits m).length ≤ (natToBits n).length :=
  natToBits_length_le (Nat.lt_of_le_of_lt h (lt_two_pow_natToBits n))

/-! ## The self-delimiting code -/

/-- The self-delimiting code of a natural number: the digit count in unary, a `false`
separator, then the digits. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate (natToBits n).length true ++ false :: natToBits n

/-- Split a maximal run of leading `true`s. -/
def parseUnary : List Bool → ℕ × List Bool
  | true :: s =>
    match parseUnary s with
    | (k, r) => (k + 1, r)
  | s => (0, s)

/-- Parse one self-delimiting natural number; rejects non-canonical digit strings. -/
def parseNat (s : List Bool) : Option (ℕ × List Bool) :=
  let p := parseUnary s
  match p.2 with
  | false :: rest =>
    if p.1 ≤ rest.length then
      if (rest.take p.1).getLast? = some false then none
      else some (bitsToNat (rest.take p.1), rest.drop p.1)
    else none
  | _ => none

theorem parseUnary_replicate (k : ℕ) (r : List Bool) :
    parseUnary (List.replicate k true ++ false :: r) = (k, false :: r) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, parseUnary, ih]

theorem parseUnary_sound : ∀ s : List Bool,
    s = List.replicate (parseUnary s).1 true ++ (parseUnary s).2
  | [] => rfl
  | false :: s => rfl
  | true :: s => by
    have ih := parseUnary_sound s
    simp only [parseUnary]
    rcases h : parseUnary s with ⟨k, r⟩
    rw [h] at ih
    simpa [List.replicate_succ] using ih

/-- Prefix property: `parseNat` consumes exactly `encodeNat n` and returns the rest. -/
@[simp]
theorem parseNat_encodeNat (n : ℕ) (rest : List Bool) :
    parseNat (encodeNat n ++ rest) = some (n, rest) := by
  have hshape : encodeNat n ++ rest
      = List.replicate (natToBits n).length true ++ false :: (natToBits n ++ rest) := by
    simp [encodeNat]
  rw [hshape]
  simp only [parseNat, parseUnary_replicate]
  rw [if_pos (by simp)]
  rw [List.take_left, List.drop_left]
  rw [if_neg (natToBits_getLast?_ne_false n), bitsToNat_natToBits]

/-- Soundness: every accepted prefix is the canonical encoding of the parsed value. -/
theorem parseNat_sound {s rest : List Bool} {n : ℕ} (h : parseNat s = some (n, rest)) :
    s = encodeNat n ++ rest := by
  rcases hu : parseUnary s with ⟨L, r⟩
  cases r with
  | nil => simp [parseNat, hu] at h
  | cons b rest0 =>
    cases b with
    | true => simp [parseNat, hu] at h
    | false =>
      simp only [parseNat, hu] at h
      by_cases hle : L ≤ rest0.length
      · rw [if_pos hle] at h
        by_cases hcan : (rest0.take L).getLast? = some false
        · rw [if_pos hcan] at h
          exact absurd h (by simp)
        · rw [if_neg hcan] at h
          have hpair : bitsToNat (rest0.take L) = n ∧ rest0.drop L = rest := by
            simpa using h
          obtain ⟨hn, hrest⟩ := hpair
          have hs := parseUnary_sound s
          simp only [hu] at hs
          have hbits : natToBits n = rest0.take L := by
            rw [← hn]
            exact natToBits_bitsToNat _ hcan
          have hlen : (natToBits n).length = L := by
            rw [hbits, List.length_take]
            omega
          rw [hs, ← hrest]
          unfold encodeNat
          rw [hlen, hbits]
          simp [List.take_append_drop]
      · rw [if_neg hle] at h
        exact absurd h (by simp)

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro a b hab
  have h1 : (some (a, ([] : List Bool)) : Option (ℕ × List Bool)) = some (b, []) := by
    calc (some (a, ([] : List Bool)) : Option (ℕ × List Bool))
        = parseNat (encodeNat a ++ []) := (parseNat_encodeNat a []).symm
      _ = parseNat (encodeNat b ++ []) := by rw [hab]
      _ = some (b, []) := parseNat_encodeNat b []
  simpa using h1

theorem encodeNat_length (n : ℕ) :
    (encodeNat n).length = 2 * (natToBits n).length + 1 := by
  simp [encodeNat]
  omega

/-- The code of `n < 2^k` takes at most `2k + 1` bits. -/
theorem encodeNat_length_le {n k : ℕ} (h : n < 2 ^ k) :
    (encodeNat n).length ≤ 2 * k + 1 := by
  have := natToBits_length_le h
  rw [encodeNat_length]
  omega

/-- The code length is monotone. -/
theorem encodeNat_length_mono {m n : ℕ} (h : m ≤ n) :
    (encodeNat m).length ≤ (encodeNat n).length := by
  rw [encodeNat_length, encodeNat_length]
  have := natToBits_length_mono h
  omega

end Turing
