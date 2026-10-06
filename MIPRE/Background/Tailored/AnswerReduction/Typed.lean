/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.LIDT.Presentation
public import MIPRE.Tailored.AnsRed.Slots
public import MIPRE.Tailored.Intro.LinearCheck
public import MIPRE.Tailored.Intro.Forms
public import MIPRE.Tailored.Detyping
public import MIPRE.Foundations.CL.ProductSampler
public import MIPRE.Foundations.CL.Downsize
public import Mathlib.Data.List.GetD
public import MIPRE.Tactics

@[expose] public section

/-!
# The typed tailored data of the answer-reduced game

Paper II's combinatorial answer reduction `𝔄𝔫𝔰ℜ𝔢𝔡` (`defn:combi_ans_red`, II:10285), as typed
tailored data (`MIPRE.Tailored.TypedData`) on the nine types `{A, B, O} × {Point, ALine, DLine}`
(`Role × LIDT.CL.Ty`), at one index of the input verifier. A question carries the oracularized
input question (the seed `z` of the input sampler for the oracle, the original player's question
for an isolated player) and, over `F₂` through the Shoup basis, a question of the seeded
low-degree test on `M = 2^j` variables.

**Answers** (Table tab:Answer_Lengths_combinatorial_ans_red). A role answers a codeword for each of
its slots (`slotsOf`, readable first): the oracle a whole PCP, Alice the two polynomials of the
first answer, Bob those of the second. Each codeword is one field element at a `Point`, the
`d + 1` coefficients of a polynomial at an `ALine`, the `Md + 1` at a `DLine`, each element as its
`t` canonical bits, codeword after codeword. So the readable part of an answer is its first
codewords, as a tailored game requires; `decAns` reads an answer as one of the low-degree test.

**The four checks** (II:10457–10502), each a list of `F₂`-linear constraints on the two answers
with coefficients read off the questions and the readable answers (`cons`):

1. *low degree*: at two questions of the same role, the seeded low-degree test of
   `LIDT.CL.accepts` on the role's codewords (`ldCons`);
2. *consistency*: at two questions of the same low-degree type, one isolated and one oracle, the
   isolated player's codewords are the oracle's in the same slots (`consCons`);
3. *indifference*: at an axis-parallel line in the direction `i`, every codeword whose slot's
   block misses `i` is constant along it (`indCons`);
4. *proof*: at the oracle's point question, the thirteen checks of the PCP at the point
   (`proofCons`) — the formula check and the readable assignment checks as a readable guard, the
   system check as linear equations in the linear values with coefficients read off `g_O`, the
   linear assignment checks as linear equations because `g ↦ g (1 - g)` is `F₂`-linear in
   characteristic `2`.

The *reading* (`cons_iff`): for answers of the types' lengths, the constraints hold exactly when
the four checks hold of the field elements the answers carry (`ArPred`) — the predicate the
completeness and soundness of the game are proved against.

The one departure from the paper is its type graph: complete with loops here, as the repository's
typed games are (§5 of `planning/aldous-lyons-track.md`, "Phase 4 slices"). The low-degree test
then runs at every pair of questions of one role, and only the constants of the soundness proof
change.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Cost MIPRE.CL MIPRE.SAT MIPRE.LowDegree MIPRE.LowDegree.BinaryLinear MIPRE.Tailored.Intro

/-! ## The registers of the low-degree test -/

section Registers

variable (j : ℕ)

/-- The number of coordinates of the low-degree test's registers: the point, the direction, the
seed. -/
abbrev D : ℕ := 2 * 2 ^ j + 1

/-- The registers of the low-degree test on `F_q^{D}`: the point, then the direction, then the
seed. -/
def regs : LIDT.CL.Regs (Fin (D j)) (2 ^ j) where
  pt i := ⟨i, by have := i.2; simp only [D]; omega⟩
  dir i := ⟨2 ^ j + i, by have := i.2; simp only [D]; omega⟩
  coord := ⟨2 * 2 ^ j, by simp only [D]; omega⟩
  pt_injective a b h := Fin.ext (by have h' := congrArg Fin.val h; dsimp only at h'; omega)
  dir_injective a b h := Fin.ext (by have h' := congrArg Fin.val h; dsimp only at h'; omega)
  pt_ne_dir a b h := by
    have := a.2
    have h' := congrArg Fin.val h
    dsimp only at h'
    omega
  pt_ne_coord a h := by
    have := a.2
    have h' := congrArg Fin.val h
    dsimp only at h'
    omega
  dir_ne_coord a h := by
    have := a.2
    have h' := congrArg Fin.val h
    dsimp only at h'
    omega

end Registers

/-! ## Field elements in bit strings -/

variable (t : ℕ) (ht : 1 ≤ t)

/-- The field `F_q`, `q = 2^t`, in its Shoup representation. -/
abbrev Fq : Type := (shoupBinField t ht).carrier

/-- **The field element whose canonical bits start at position `o`** of a bit string, bits beyond
the string read as `0`. -/
def elt (a : BitStr) (o : ℕ) : Fq t ht :=
  (shoupCoordinateEquiv t ht).symm fun i => ofBool (a.getD (o + i) false)

variable {t ht}

theorem fldAt_bitVec {N : ℕ} (z : BitStr) (hz : z.length ≤ N) (o : ℕ) :
    fldAt t ht N o (Intro.bitVec N z) = elt t ht z o := by
  simp only [fldAt, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, elt]
  congr 1
  funext i
  simp [LinearMap.pi_apply, getv_bitVec z hz]

theorem elt_append_left {a b : BitStr} {o : ℕ} (h : o + t ≤ a.length) :
    elt t ht (a ++ b) o = elt t ht a o := by
  simp only [elt]
  congr 1
  funext i
  rw [List.getD_append _ _ _ _ (by omega)]

theorem elt_append_right (a b : BitStr) (o : ℕ) :
    elt t ht (a ++ b) (a.length + o) = elt t ht b o := by
  simp only [elt]
  congr 1
  funext i
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 2
  omega

theorem elt_take {a : BitStr} {n o : ℕ} (h : o + t ≤ n) : elt t ht (a.take n) o = elt t ht a o := by
  simp only [elt]
  congr 1
  funext i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  rw [ite_eq_left (by omega)]

/-! ## Field equations as constraints -/

variable (t ht) in
/-- **Field equations `E(z) = κ` on `N` answer bits, as constraints**: the coordinate checks of
each equation (`fieldChecks`). -/
def eqsCons {N : ℕ} (es : List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht)) :
    List BitStr :=
  (es.flatMap fun e => fieldChecks t ht e.1 e.2).map LinCheck.toCon

/-- **The constraints of field equations hold exactly when the equations do.** -/
theorem eqsCons_iff {N : ℕ} (es : List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht))
    (z : BitStr) (hz : z.length = N) :
    (∀ c ∈ eqsCons t ht es, Satisfies c (z ++ [true])) ↔
      ∀ e ∈ es, e.1 (Intro.bitVec N z) = e.2 := by
  constructor
  · intro h e he
    refine (forall_fieldChecks_iff e.1 e.2 _).1 fun χ hχ => ?_
    exact (satisfies_toCon_iff χ z hz).1
      (h χ.toCon (List.mem_map.2 ⟨χ, List.mem_flatMap.2 ⟨e, he, hχ⟩, rfl⟩))
  · intro h c hc
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 hc
    obtain ⟨e, he, hχe⟩ := List.mem_flatMap.1 hχ
    exact (satisfies_toCon_iff χ z hz).2 ((forall_fieldChecks_iff e.1 e.2 _).2 (h e he) χ hχe)

/-- `g ↦ g (1 - g)`, which is `F₂`-linear in characteristic `2`: the left side of an assignment
check (eq:PCP_check_1_ansred). -/
def certLin : Fq t ht →ₗ[ZMod 2] Fq t ht where
  toFun g := g * (1 - g)
  map_add' g h := by
    have h2 : (2 : Fq t ht) = 0 := CharTwo.two_eq_zero
    linear_combination (-(g * h)) * h2
  map_smul' c g := by
    rcases binary_eq_zero_or_one c with rfl | rfl <;> simp

@[simp] theorem certLin_apply (g : Fq t ht) : certLin g = g * (1 - g) := rfl

/-- Multiplication by a field element, as an `F₂`-linear map. -/
abbrev mulL (α : Fq t ht) : Fq t ht →ₗ[ZMod 2] Fq t ht := LinearMap.mulLeft (ZMod 2) α

/-! ## The layout of the answers -/

variable (t ht) (j d : ℕ) (L : PcpDims)

/-- The number of field elements of a codeword at a question of the low-degree type `S`: one
value, or the coefficients of a polynomial of degree at most `d` or `M d`. -/
def ncoef : LIDT.CL.Ty → ℕ
  | .point => 1
  | .aline => d + 1
  | .dline => 2 ^ j * d + 1

theorem ncoef_pos (S : LIDT.CL.Ty) : 0 < ncoef j d S := by
  cases S <;> simp [ncoef]

/-- The number of readable bits of an answer at a type. -/
def lenR (u : Role × LIDT.CL.Ty) : ℕ := (rOf L u.1).length * ncoef j d u.2 * t

/-- The number of linear bits of an answer at a type. -/
def lenL (u : Role × LIDT.CL.Ty) : ℕ := (lOf L u.1).length * ncoef j d u.2 * t

/-- The number of bits of an answer at a type. -/
def len (u : Role × LIDT.CL.Ty) : ℕ := lenR t j d L u + lenL t j d L u

theorem len_eq (u : Role × LIDT.CL.Ty) :
    len t j d L u = (slotsOf L u.1).length * ncoef j d u.2 * t := by
  simp only [len, lenR, lenL, slotsOf, List.length_append]
  ring

theorem lenR_le_len (u : Role × LIDT.CL.Ty) : lenR t j d L u ≤ len t j d L u :=
  Nat.le_add_right _ _

/-- **The `e`-th field element of the `c`-th codeword** of an answer at the low-degree type
`S`. -/
def cw (S : LIDT.CL.Ty) (a : BitStr) (c e : ℕ) : Fq t ht :=
  elt t ht a ((c * ncoef j d S + e) * t)

/-- **An answer read as an answer of the low-degree test**, with the role's codewords. -/
def decAns (r : Role) : (S : LIDT.CL.Ty) → BitStr →
    LIDT.CL.Answer (Fq t ht) (2 ^ j) d (slotsOf L r).length
  | .point, a => .values fun c => cw t ht j d .point a c 0
  | .aline, a => .apolys fun c e => cw t ht j d .aline a c e
  | .dline, a => .dpolys fun c e => cw t ht j d .dline a c e

/-- **The values of the oracle's slots** in a point answer. -/
def vals (a : BitStr) (s : Slot L) : Fq t ht := cw t ht j d .point a (idxO s) 0

/-! ## The questions -/

variable (rV : ℕ)

/-- The oracularized input question a typed question carries, `F₂^{r}`. -/
def rolePart (y : Fin (rV + D j * t) → 𝔽₂) : Fin rV → 𝔽₂ := leftPart y

/-- The low-degree vector a typed question carries, read back over `F_q`. -/
def ldPart (y : Fin (rV + D j * t) → 𝔽₂) : Fin (D j) → Fq t ht :=
  (downsizeEquiv (shoupPowerBasis t ht)).symm ((reindexEquiv finProdFinEquiv).symm (rightPart y))

variable {hM : 2 ^ j ∣ Fintype.card (Fq t ht)} (sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM)

/-- **The question of the low-degree test** a typed question of the low-degree type `S`
carries. -/
def ldQ (S : LIDT.CL.Ty) (y : Fin (rV + D j * t) → 𝔽₂) : LIDT.CL.Question (Fq t ht) (2 ^ j) :=
  (regs j).questionOf sel S (ldPart t ht j rV y)

/-! ## The four checks -/

section Checks

variable {t ht j d L}

/-- The equations that two answers at offsets `0` and `Na` agree on `k` codewords of `nc`
elements. -/
def ldEq (N Na k nc : ℕ) : List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht) :=
  (List.range k).flatMap fun c => (List.range nc).map fun e =>
    (fldAt t ht N ((c * nc + e) * t) - fldAt t ht N (Na + (c * nc + e) * t), 0)

/-- The equations that the `k` line polynomials of `nc` coefficients at offset `oL`, evaluated at
`α`, are the `k` values at offset `oP`. -/
def ldLine (N k nc oL oP : ℕ) (α : Fq t ht) :
    List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht) :=
  (List.range k).map fun c =>
    (∑ e ∈ Finset.range nc, mulL (α ^ e) ∘ₗ fldAt t ht N (oL + (c * nc + e) * t) -
      fldAt t ht N (oP + c * t), 0)

variable (j d hM) in
/-- **The low-degree checks** at two questions of one role with `k` codewords, the first answer
of `Na` bits: the subtests of `LIDT.CL.subtests` — equal answers at equal types, the line
polynomials against the point values when a point lies on a line, and nothing at an axis-parallel
line against a diagonal one. -/
def ldCons (k Na N : ℕ) : LIDT.CL.Question (Fq t ht) (2 ^ j) →
    LIDT.CL.Question (Fq t ht) (2 ^ j) → List BitStr
  | .point _, .point _ => eqsCons t ht (ldEq N Na k 1)
  | .aline _ _, .aline _ _ => eqsCons t ht (ldEq N Na k (d + 1))
  | .dline _ _ _, .dline _ _ _ => eqsCons t ht (ldEq N Na k (2 ^ j * d + 1))
  | .aline u₀ s, .point x =>
      guardCons (decide (∃ τ : Fq t ht, x = u₀ + τ • Pi.single (LIDT.CL.chi hM s) 1)) N ++
        eqsCons t ht (ldLine N k (d + 1) 0 Na
          (LIDT.CL.lineParam u₀ (Pi.single (LIDT.CL.chi hM s) 1) x))
  | .point x, .aline u₀ s =>
      guardCons (decide (∃ τ : Fq t ht, x = u₀ + τ • Pi.single (LIDT.CL.chi hM s) 1)) N ++
        eqsCons t ht (ldLine N k (d + 1) Na 0
          (LIDT.CL.lineParam u₀ (Pi.single (LIDT.CL.chi hM s) 1) x))
  | .dline u₀ _ v, .point x =>
      guardCons (decide (∃ τ : Fq t ht, x = u₀ + τ • v)) N ++
        eqsCons t ht (ldLine N k (2 ^ j * d + 1) 0 Na (LIDT.CL.lineParam u₀ v x))
  | .point x, .dline u₀ _ v =>
      guardCons (decide (∃ τ : Fq t ht, x = u₀ + τ • v)) N ++
        eqsCons t ht (ldLine N k (2 ^ j * d + 1) Na 0 (LIDT.CL.lineParam u₀ v x))
  | _, _ => []

variable (L) in
/-- The equations that an isolated role's codewords of `nc` elements at offset `oI` are the
oracle's in the same slots, at offset `oO`. -/
def consEqs (N oI oO nc : ℕ) (r : Role) :
    List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht) :=
  (List.finRange (slotsOf L r).length).flatMap fun (c : Fin (slotsOf L r).length) =>
    (List.range nc).map fun e =>
      (fldAt t ht N (oI + ((c : ℕ) * nc + e) * t) -
        fldAt t ht N (oO + (idxO ((slotsOf L r).get c) * nc + e) * t), 0)

variable (t ht j d L) in
/-- **The consistency checks** at two questions of the low-degree type `S`, the first answer of
`Na` bits: at an isolated role and the oracle, in either order, the isolated player's codewords
are the oracle's in the same slots. -/
def consCons (Na N : ℕ) (S : LIDT.CL.Ty) : Role → Role → List BitStr
  | .alice, .oracle => eqsCons t ht (consEqs L N 0 Na (ncoef j d S) .alice)
  | .bob, .oracle => eqsCons t ht (consEqs L N 0 Na (ncoef j d S) .bob)
  | .oracle, .alice => eqsCons t ht (consEqs L N Na 0 (ncoef j d S) .alice)
  | .oracle, .bob => eqsCons t ht (consEqs L N Na 0 (ncoef j d S) .bob)
  | _, _ => []

variable (j) in
/-- **The block of a slot** among the low-degree test's `M` variables. -/
def blockM (hLM : L.m ≤ 2 ^ j) (s : Slot L) : Finset (Fin (2 ^ j)) :=
  Finset.univ.image (Fin.castLE hLM ∘ s.emb)

variable (hLM : L.m ≤ 2 ^ j)

variable (d L) in
/-- The equations that the codewords of a role at offset `o` whose blocks miss the direction `i`
have their coefficients `1, …, d` zero. -/
def indEqs (N o : ℕ) (r : Role) (i : Fin (2 ^ j)) :
    List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht) :=
  (List.finRange (slotsOf L r).length).flatMap fun (c : Fin (slotsOf L r).length) =>
    if i ∈ blockM j hLM ((slotsOf L r).get c) then [] else
      (List.range d).map fun e => (fldAt t ht N (o + ((c : ℕ) * (d + 1) + (e + 1)) * t), 0)

variable (j d L hM) in
/-- **The indifference checks** of one answer, of a role, at offset `o`: at an axis-parallel line,
the codewords whose blocks miss its direction are constant along it. -/
def indCons (N o : ℕ) (r : Role) : LIDT.CL.Question (Fq t ht) (2 ^ j) → List BitStr
  | .aline _ s => eqsCons t ht (indEqs d L hLM N o r (LIDT.CL.chi hM s))
  | _ => []

variable (L) in
/-- The point of the PCP's variables a point of the test's carries: its first `m`
coordinates. -/
def ptm (p : Fin (2 ^ j) → Fq t ht) : Fin L.m → Fq t ht := p ∘ Fin.castLE hLM

variable (L) in
/-- The equations the linear values of an oracle's point answer at offset `o` must satisfy, given
the readable value `wO` of `g_O`, at the point `p` of the PCP's variables: the system check and
the three linear assignment checks. -/
def proofEqs (N o : ℕ) (wO : Fq t ht) (p : Fin L.m → Fq t ht) :
    List (((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht) :=
  let v : Slot L → (Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht := fun s => fldAt t ht N (o + idxO s * t)
  let x := p ∘ L.vO
  let asg : (k : ℕ) → (Fin k → Fin L.m) → Slot L → (Fin k → Slot L) →
      ((Fin N → ZMod 2) →ₗ[ZMod 2] Fq t ht) × Fq t ht := fun _ e g β =>
    (certLin ∘ₗ v g - ∑ i, mulL ((p ∘ e) i * (1 - (p ∘ e) i)) ∘ₗ v (β i), 0)
  [(mulL (wO * x (L.oSgn 0)) ∘ₗ v .gLa + mulL (wO * x (L.oSgn 1)) ∘ₗ v .gLb +
      ∑ k : Fin 3, mulL (wO * x (L.oSgn (2 + k.castLE (by decide)))) ∘ₗ v (.gL k) -
      ∑ X, mulL (x X * (1 - x X)) ∘ₗ v (.αL X), wO * x (L.oSgn 5)),
    asg L.ℓ (L.vO ∘ L.oA) .gLa Slot.βLa, asg L.ℓ (L.vO ∘ L.oB) .gLb Slot.βLb] ++
    (List.finRange 3).map fun k => asg L.dm (L.vO ∘ L.oL k) (.gL k) (Slot.βL k)

variable (j d L) in
/-- **The proof check** of an oracle's point answer at offset `o`, read through its readable part
`aR`, against the circuit polynomial `T` at the point `p` of the test's variables: the readable
checks as a guard, then the equations the linear values enter. -/
def proofCons (N o : ℕ) (T : MvPolynomial (Fin L.m) (Fq t ht)) (p : Fin (2 ^ j) → Fq t ht)
    (aR : BitStr) : List BitStr :=
  guardCons (decide (PassesR T (vals t ht j d L aR) (ptm L hLM p))) N ++
    eqsCons t ht (proofEqs L N o (vals t ht j d L aR .gO) (ptm L hLM p))

end Checks

/-! ## The typed tailored data -/

variable (hLM : L.m ≤ 2 ^ j) (circ : (Fin rV → 𝔽₂) → MvPolynomial (Fin L.m) (Fq t ht))

/-- **The constraints at a pair of typed questions**, from the readable answers: the low-degree
checks at one role, the consistency checks at one low-degree type, the indifference checks of each
answer, and the proof check of each oracle point answer. None unless the readable answers have
their types' readable lengths, as they always do in the game. -/
def cons (u v : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (rV + D j * t))) (aR bR : BitStr) :
    List BitStr :=
  if aR.length = lenR t j d L u.1 ∧ bR.length = lenR t j d L v.1 then
    (if u.1.1 = v.1.1 then
      ldCons j d hM (slotsOf L u.1.1).length (len t j d L u.1) (len t j d L u.1 + len t j d L v.1)
        (ldQ t ht j rV sel u.1.2 u.2) (ldQ t ht j rV sel v.1.2 v.2) else []) ++
    (if u.1.2 = v.1.2 then
      consCons t ht j d L (len t j d L u.1) (len t j d L u.1 + len t j d L v.1) u.1.2 u.1.1 v.1.1
      else []) ++
    indCons j d L hM hLM (len t j d L u.1 + len t j d L v.1) 0 u.1.1
      (ldQ t ht j rV sel u.1.2 u.2) ++
    indCons j d L hM hLM (len t j d L u.1 + len t j d L v.1) (len t j d L u.1) v.1.1
      (ldQ t ht j rV sel v.1.2 v.2) ++
    (if u.1 = (.oracle, .point) then
      proofCons j d L hLM (len t j d L u.1 + len t j d L v.1) 0 (circ (rolePart t j rV u.2))
        (ldQ t ht j rV sel u.1.2 u.2).base aR else []) ++
    (if v.1 = (.oracle, .point) then
      proofCons j d L hLM (len t j d L u.1 + len t j d L v.1) (len t j d L u.1)
        (circ (rolePart t j rV v.2)) (ldQ t ht j rV sel v.1.2 v.2).base bR else [])
  else []

/-- **The typed tailored data of the answer-reduced game.** -/
def tdata : TypedData (Role × LIDT.CL.Ty) (Fin (rV + D j * t)) where
  lenR := lenR t j d L
  lenL := lenL t j d L
  cons := cons t ht j d L rV sel hLM circ

/-! ## The four checks, on field elements -/

/-- An isolated role's answer `a` agrees with the oracle's `b` in the role's slots, at the
low-degree type `S`. -/
def IsoAgrees (r : Role) (S : LIDT.CL.Ty) (a b : BitStr) : Prop :=
  ∀ c : Fin (slotsOf L r).length, ∀ e < ncoef j d S,
    cw t ht j d S a c e = cw t ht j d S b (idxO ((slotsOf L r).get c)) e

/-- **The consistency check** at two roles, at one low-degree type. -/
def ConsOK (S : LIDT.CL.Ty) (a b : BitStr) : Role → Role → Prop
  | .alice, .oracle => IsoAgrees t ht j d L .alice S a b
  | .bob, .oracle => IsoAgrees t ht j d L .bob S a b
  | .oracle, .alice => IsoAgrees t ht j d L .alice S b a
  | .oracle, .bob => IsoAgrees t ht j d L .bob S b a
  | _, _ => True

variable (hM) in
/-- **The indifference check** of an answer of a role: at an axis-parallel line, the codewords
whose blocks miss its direction have their coefficients `1, …, d` zero. -/
def IndOK (r : Role) (a : BitStr) : LIDT.CL.Question (Fq t ht) (2 ^ j) → Prop
  | .aline _ s => ∀ c : Fin (slotsOf L r).length,
      LIDT.CL.chi hM s ∉ blockM j hLM ((slotsOf L r).get c) →
        ∀ e < d, cw t ht j d .aline a c (e + 1) = 0
  | _ => True

/-- **The answer-reduced predicate on field elements**: the four checks at a pair of typed
questions. -/
def ArPred (u v : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (rV + D j * t)))
    (a b : BitStr) : Prop :=
  (∀ r, u.1.1 = r → v.1.1 = r →
    LIDT.CL.accepts hM (ldQ t ht j rV sel u.1.2 u.2) (ldQ t ht j rV sel v.1.2 v.2)
      (decAns t ht j d L r u.1.2 a) (decAns t ht j d L r v.1.2 b) = true) ∧
  (u.1.2 = v.1.2 → ConsOK t ht j d L u.1.2 a b u.1.1 v.1.1) ∧
  IndOK t ht j d L hM hLM u.1.1 a (ldQ t ht j rV sel u.1.2 u.2) ∧
  IndOK t ht j d L hM hLM v.1.1 b (ldQ t ht j rV sel v.1.2 v.2) ∧
  (u.1 = (.oracle, .point) → PassesV (circ (rolePart t j rV u.2)) (vals t ht j d L a)
    (ptm L hLM (ldQ t ht j rV sel u.1.2 u.2).base)) ∧
  (v.1 = (.oracle, .point) → PassesV (circ (rolePart t j rV v.2)) (vals t ht j d L b)
    (ptm L hLM (ldQ t ht j rV sel v.1.2 v.2).base))

/-! ## Reading the constraints -/

section Read

variable {t ht j d L}

theorem fldAt_left {a b : BitStr} {N o : ℕ} (hN : a.length + b.length = N)
    (h : o + t ≤ a.length) : fldAt t ht N o (Intro.bitVec N (a ++ b)) = elt t ht a o := by
  rw [fldAt_bitVec _ (by rw [List.length_append]; omega), elt_append_left h]

theorem fldAt_right {a b : BitStr} {N Na : ℕ} (ha : a.length = Na) (hN : Na + b.length = N)
    (o : ℕ) : fldAt t ht N (Na + o) (Intro.bitVec N (a ++ b)) = elt t ht b o := by
  subst ha
  rw [fldAt_bitVec _ (by rw [List.length_append]; omega), elt_append_right]

theorem off_add_le {k nc c e : ℕ} (hc : c < k) (he : e < nc) :
    (c * nc + e) * t + t ≤ k * nc * t := by
  have h1 : c * nc + e + 1 ≤ k * nc := by
    have : (c + 1) * nc ≤ k * nc := Nat.mul_le_mul_right _ hc
    nlinarith
  calc (c * nc + e) * t + t = (c * nc + e + 1) * t := by ring
    _ ≤ k * nc * t := Nat.mul_le_mul_right _ h1

/-- **The equality equations**, read. -/
theorem ldEq_iff {a b : BitStr} {N Na k nc : ℕ} (ha : a.length = Na) (hN : Na + b.length = N)
    (hk : Na = k * nc * t) :
    (∀ e ∈ ldEq (t := t) (ht := ht) N Na k nc, e.1 (Intro.bitVec N (a ++ b)) = e.2) ↔
      ∀ c < k, ∀ e < nc, elt t ht a ((c * nc + e) * t) = elt t ht b ((c * nc + e) * t) := by
  simp only [ldEq, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · intro h c hc e he
    have := h _ ⟨c, hc, e, he, rfl⟩
    dsimp only at this
    rw [LinearMap.sub_apply, fldAt_left (by omega) (by rw [ha, hk]; exact off_add_le hc he),
      fldAt_right ha hN] at this
    exact sub_eq_zero.1 this
  · rintro h _ ⟨c, hc, e, he, rfl⟩
    dsimp only
    rw [LinearMap.sub_apply, fldAt_left (by omega) (by rw [ha, hk]; exact off_add_le hc he),
      fldAt_right ha hN, h c hc e he, sub_self]

theorem ldLine_apply {N nc oL oP : ℕ} (α : Fq t ht) (c : ℕ) (v : Fin N → ZMod 2) :
    (∑ e ∈ Finset.range nc, mulL (α ^ e) ∘ₗ fldAt t ht N (oL + (c * nc + e) * t) -
      fldAt t ht N (oP + c * t)) v =
      ∑ e ∈ Finset.range nc, α ^ e * fldAt t ht N (oL + (c * nc + e) * t) v -
        fldAt t ht N (oP + c * t) v := by
  rw [LinearMap.sub_apply, LinearMap.sum_apply]
  rfl

/-- **The line equations, the line answer first**, read. -/
theorem ldLine_iff_ab {a b : BitStr} {N Na k nc : ℕ} (α : Fq t ht) (ha : a.length = Na)
    (hN : Na + b.length = N) (hk : Na = k * nc * t) :
    (∀ e ∈ ldLine (t := t) (ht := ht) N k nc 0 Na α, e.1 (Intro.bitVec N (a ++ b)) = e.2) ↔
      ∀ c < k, ∑ e ∈ Finset.range nc, α ^ e * elt t ht a ((c * nc + e) * t) =
        elt t ht b (c * t) := by
  have key : ∀ c < k, (∑ e ∈ Finset.range nc, α ^ e * fldAt t ht N (0 + (c * nc + e) * t)
      (Intro.bitVec N (a ++ b)) - fldAt t ht N (Na + c * t) (Intro.bitVec N (a ++ b))) =
      ∑ e ∈ Finset.range nc, α ^ e * elt t ht a ((c * nc + e) * t) - elt t ht b (c * t) := by
    intro c hc
    rw [fldAt_right ha hN]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [zero_add, fldAt_left (by omega)
      (by rw [ha, hk]; exact off_add_le hc (Finset.mem_range.1 he))]
  simp only [ldLine, List.mem_map, List.mem_range]
  constructor
  · intro h c hc
    have := h _ ⟨c, hc, rfl⟩
    dsimp only at this
    rw [ldLine_apply, key c hc] at this
    exact sub_eq_zero.1 this
  · rintro h _ ⟨c, hc, rfl⟩
    dsimp only
    rw [ldLine_apply, key c hc, h c hc, sub_self]

/-- **The line equations, the point answer first**, read. -/
theorem ldLine_iff_ba {a b : BitStr} {N Na k nc : ℕ} (α : Fq t ht) (ha : a.length = Na)
    (hN : Na + b.length = N) (hk : Na = k * 1 * t) :
    (∀ e ∈ ldLine (t := t) (ht := ht) N k nc Na 0 α, e.1 (Intro.bitVec N (a ++ b)) = e.2) ↔
      ∀ c < k, ∑ e ∈ Finset.range nc, α ^ e * elt t ht b ((c * nc + e) * t) =
        elt t ht a (c * t) := by
  have key : ∀ c < k, (∑ e ∈ Finset.range nc, α ^ e * fldAt t ht N (Na + (c * nc + e) * t)
      (Intro.bitVec N (a ++ b)) - fldAt t ht N (0 + c * t) (Intro.bitVec N (a ++ b))) =
      ∑ e ∈ Finset.range nc, α ^ e * elt t ht b ((c * nc + e) * t) - elt t ht a (c * t) := by
    intro c hc
    have hle : c * t + t ≤ a.length := by
      have := off_add_le (t := t) (nc := 1) (e := 0) hc Nat.one_pos
      rw [ha, hk]; simpa using this
    rw [zero_add, fldAt_left (by omega) hle]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [fldAt_right ha hN]
  simp only [ldLine, List.mem_map, List.mem_range]
  constructor
  · intro h c hc
    have := h _ ⟨c, hc, rfl⟩
    dsimp only at this
    rw [ldLine_apply, key c hc] at this
    exact sub_eq_zero.1 this
  · rintro h _ ⟨c, hc, rfl⟩
    dsimp only
    rw [ldLine_apply, key c hc, h c hc, sub_self]

end Read

section ReadLD

variable {t ht j d L}

theorem cw_point (a : BitStr) (c : ℕ) : cw t ht j d .point a c 0 = elt t ht a (c * t) := by
  simp [cw, ncoef]

theorem eval_cw (S : LIDT.CL.Ty) (a : BitStr) (c n : ℕ) (hn : ncoef j d S = n + 1)
    (α : Fq t ht) :
    LIDT.LinePoly.eval (fun e : Fin (n + 1) => cw t ht j d S a c e) α =
      ∑ e ∈ Finset.range (n + 1), α ^ e * elt t ht a ((c * (n + 1) + e) * t) := by
  rw [LIDT.LinePoly.eval,
    ← Fin.sum_univ_eq_sum_range (fun e => α ^ e * elt t ht a ((c * (n + 1) + e) * t))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [cw, hn, mul_comm]

/-- **The low-degree checks**, read: for answers of their types' lengths, at two questions of
one role, they hold exactly when the seeded low-degree test accepts the answers read as answers of
the test. -/
theorem ldCons_iff (r : Role) (S1 S2 : LIDT.CL.Ty) (x y : Fin (D j) → Fq t ht) {a b : BitStr}
    (ha : a.length = len t j d L (r, S1)) (hb : b.length = len t j d L (r, S2)) :
    (∀ c ∈ ldCons j d hM (slotsOf L r).length (len t j d L (r, S1))
        (len t j d L (r, S1) + len t j d L (r, S2))
        ((regs j).questionOf sel S1 x) ((regs j).questionOf sel S2 y),
        Satisfies c (a ++ b ++ [true])) ↔
      LIDT.CL.accepts hM ((regs j).questionOf sel S1 x) ((regs j).questionOf sel S2 y)
        (decAns t ht j d L r S1 a) (decAns t ht j d L r S2 b) = true := by
  have hz : (a ++ b).length = len t j d L (r, S1) + len t j d L (r, S2) := by
    rw [List.length_append, ha, hb]
  have hN : len t j d L (r, S1) + b.length = len t j d L (r, S1) + len t j d L (r, S2) := by
    rw [hb]
  have hNa := len_eq t j d L (r, S1)
  cases S1 <;> cases S2 <;>
    simp only [LIDT.CL.Regs.questionOf, ldCons, decAns, LIDT.CL.accepts,
      LIDT.CL.Question.fmtOk, LIDT.CL.subtests, LIDT.CL.lineVsPoint, Bool.true_and,
      decide_eq_true_eq] at hNa ⊢
  · -- two points
    rw [eqsCons_iff _ _ hz, ldEq_iff ha hN (by rw [hNa]; rfl)]
    constructor
    · intro h
      funext c
      exact h c c.2 0 Nat.one_pos
    · intro h c hc e he
      obtain rfl : e = 0 := by omega
      exact congrFun h ⟨c, hc⟩
  · -- a point, then an axis-parallel line
    rw [List.forall_mem_append, guardCons_iff, decide_eq_true_eq, eqsCons_iff _ _ hz,
      ldLine_iff_ba _ ha hN (by rw [hNa]; rfl)]
    refine and_congr_right fun _ => ⟨fun h c => ?_, fun h c hc => ?_⟩
    · rw [eval_cw (t := t) (ht := ht) (j := j) (d := d) .aline b c d rfl, h c c.2, cw_point]
    · have := h ⟨c, hc⟩
      rwa [eval_cw (t := t) (ht := ht) (j := j) (d := d) .aline b c d rfl, cw_point] at this
  · -- a point, then a diagonal line
    rw [List.forall_mem_append, guardCons_iff, decide_eq_true_eq, eqsCons_iff _ _ hz,
      ldLine_iff_ba _ ha hN (by rw [hNa]; rfl)]
    refine and_congr_right fun _ => ⟨fun h c => ?_, fun h c hc => ?_⟩
    · rw [eval_cw (t := t) (ht := ht) (j := j) (d := d) .dline b c (2 ^ j * d) rfl, h c c.2,
        cw_point]
    · have := h ⟨c, hc⟩
      rwa [eval_cw (t := t) (ht := ht) (j := j) (d := d) .dline b c (2 ^ j * d) rfl,
        cw_point] at this
  · -- an axis-parallel line, then a point
    rw [List.forall_mem_append, guardCons_iff, decide_eq_true_eq, eqsCons_iff _ _ hz,
      ldLine_iff_ab _ ha hN (by rw [hNa]; rfl)]
    refine and_congr_right fun _ => ⟨fun h c => ?_, fun h c hc => ?_⟩
    · rw [eval_cw (t := t) (ht := ht) (j := j) (d := d) .aline a c d rfl, h c c.2, cw_point]
    · have := h ⟨c, hc⟩
      rwa [eval_cw (t := t) (ht := ht) (j := j) (d := d) .aline a c d rfl, cw_point] at this
  · -- two axis-parallel lines
    rw [eqsCons_iff _ _ hz, ldEq_iff ha hN (by rw [hNa]; rfl)]
    constructor
    · intro h
      funext c e
      exact h c c.2 e e.2
    · intro h c hc e he
      exact congrFun (congrFun h ⟨c, hc⟩) ⟨e, he⟩
  · -- an axis-parallel line, then a diagonal one
    simp
  · -- a diagonal line, then a point
    rw [List.forall_mem_append, guardCons_iff, decide_eq_true_eq, eqsCons_iff _ _ hz,
      ldLine_iff_ab _ ha hN (by rw [hNa]; rfl)]
    refine and_congr_right fun _ => ⟨fun h c => ?_, fun h c hc => ?_⟩
    · rw [eval_cw (t := t) (ht := ht) (j := j) (d := d) .dline a c (2 ^ j * d) rfl, h c c.2,
        cw_point]
    · have := h ⟨c, hc⟩
      rwa [eval_cw (t := t) (ht := ht) (j := j) (d := d) .dline a c (2 ^ j * d) rfl,
        cw_point] at this
  · -- a diagonal line, then an axis-parallel one
    simp
  · -- two diagonal lines
    rw [eqsCons_iff _ _ hz, ldEq_iff ha hN (by rw [hNa]; rfl)]
    constructor
    · intro h
      funext c e
      exact h c c.2 e e.2
    · intro h c hc e he
      exact congrFun (congrFun h ⟨c, hc⟩) ⟨e, he⟩


end ReadLD

/-! ### Consistency -/

section ReadCons

variable {t ht j d L}

/-- The consistency equations, the isolated answer first, read. -/
theorem consEqs_iff_io (r : Role) {a b : BitStr} {N Na nc : ℕ} (ha : a.length = Na)
    (hN : Na + b.length = N) (hk : Na = (slotsOf L r).length * nc * t) :
    (∀ e ∈ consEqs (t := t) (ht := ht) L N 0 Na nc r, e.1 (Intro.bitVec N (a ++ b)) = e.2) ↔
      ∀ c : Fin (slotsOf L r).length, ∀ e < nc, elt t ht a ((c * nc + e) * t) =
        elt t ht b ((idxO ((slotsOf L r).get c) * nc + e) * t) := by
  simp only [consEqs, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_finRange,
    true_and]
  constructor
  · intro h c e he
    have := h _ ⟨c, e, he, rfl⟩
    dsimp only at this
    rw [LinearMap.sub_apply, zero_add,
      fldAt_left (by omega) (by rw [ha, hk]; exact off_add_le c.2 he), fldAt_right ha hN] at this
    exact sub_eq_zero.1 this
  · rintro h _ ⟨c, e, he, rfl⟩
    dsimp only
    rw [LinearMap.sub_apply, zero_add,
      fldAt_left (by omega) (by rw [ha, hk]; exact off_add_le c.2 he), fldAt_right ha hN,
      h c e he, sub_self]

/-- The consistency equations, the oracle's answer first, read. -/
theorem consEqs_iff_oi (r : Role) {a b : BitStr} {N Na nc : ℕ} (ha : a.length = Na)
    (hN : Na + b.length = N) (hk : Na = (slotsOf L .oracle).length * nc * t) :
    (∀ e ∈ consEqs (t := t) (ht := ht) L N Na 0 nc r, e.1 (Intro.bitVec N (a ++ b)) = e.2) ↔
      ∀ c : Fin (slotsOf L r).length, ∀ e < nc, elt t ht b ((c * nc + e) * t) =
        elt t ht a ((idxO ((slotsOf L r).get c) * nc + e) * t) := by
  simp only [consEqs, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_finRange,
    true_and]
  constructor
  · intro h c e he
    have := h _ ⟨c, e, he, rfl⟩
    dsimp only at this
    rw [LinearMap.sub_apply, zero_add, fldAt_right ha hN,
      fldAt_left (by omega) (by rw [ha, hk]; exact off_add_le (idxO_lt _) he)] at this
    exact sub_eq_zero.1 this
  · rintro h _ ⟨c, e, he, rfl⟩
    dsimp only
    rw [LinearMap.sub_apply, zero_add, fldAt_right ha hN,
      fldAt_left (by omega) (by rw [ha, hk]; exact off_add_le (idxO_lt _) he), h c e he,
      sub_self]

/-- **The consistency checks**, read. -/
theorem consCons_iff (S : LIDT.CL.Ty) (r1 r2 : Role) {a b : BitStr}
    (ha : a.length = len t j d L (r1, S)) (hb : b.length = len t j d L (r2, S)) :
    (∀ c ∈ consCons t ht j d L (len t j d L (r1, S)) (len t j d L (r1, S) + len t j d L (r2, S))
        S r1 r2, Satisfies c (a ++ b ++ [true])) ↔ ConsOK t ht j d L S a b r1 r2 := by
  have hz : (a ++ b).length = len t j d L (r1, S) + len t j d L (r2, S) := by
    rw [List.length_append, ha, hb]
  have hN : len t j d L (r1, S) + b.length = len t j d L (r1, S) + len t j d L (r2, S) := by
    rw [hb]
  have hNa := len_eq t j d L (r1, S)
  cases r1 <;> cases r2 <;> simp only [consCons, ConsOK, IsoAgrees] at hNa ⊢ <;>
    first
    | (rw [eqsCons_iff _ _ hz, consEqs_iff_io _ ha hN hNa]; rfl)
    | (rw [eqsCons_iff _ _ hz, consEqs_iff_oi _ ha hN hNa]; rfl)
    | simp

end ReadCons

/-! ### Indifference -/

section ReadInd

variable {t ht j d L}

/-- The indifference equations of an answer at offset `o`, read, through the answer's reading
`X` there. -/
theorem indEqs_iff (r : Role) (i : Fin (2 ^ j)) {N o : ℕ} (v : Fin N → ZMod 2) (X : BitStr)
    (hX : ∀ c : Fin (slotsOf L r).length, ∀ e < d,
      fldAt t ht N (o + (c * (d + 1) + (e + 1)) * t) v = elt t ht X ((c * (d + 1) + (e + 1)) * t)) :
    (∀ e ∈ indEqs (t := t) (ht := ht) d L hLM N o r i, e.1 v = e.2) ↔
      ∀ c : Fin (slotsOf L r).length, i ∉ blockM j hLM ((slotsOf L r).get c) →
        ∀ e < d, elt t ht X ((c * (d + 1) + (e + 1)) * t) = 0 := by
  simp only [indEqs, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · intro h c hc e he
    have := h _ ⟨c, by
      rw [ite_eq_right_iff.mpr (fun h' => absurd h' hc)]
      exact List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩⟩
    dsimp only at this
    rwa [hX c e he] at this
  · rintro h _ ⟨c, hmem⟩
    by_cases hc : i ∈ blockM j hLM ((slotsOf L r).get c)
    · rw [ite_eq_left hc] at hmem
      simp at hmem
    · rw [ite_eq_right hc] at hmem
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
      dsimp only
      rw [hX c e (List.mem_range.1 he)]
      exact h c hc e (List.mem_range.1 he)

/-- **The indifference checks of the first answer**, read. -/
theorem indCons_iff_a (r : Role) (S : LIDT.CL.Ty) (x : Fin (D j) → Fq t ht) {a b : BitStr} {N : ℕ}
    (ha : a.length = len t j d L (r, S)) (hN : a.length + b.length = N) :
    (∀ c ∈ indCons j d L hM hLM N 0 r ((regs j).questionOf sel S x),
        Satisfies c (a ++ b ++ [true])) ↔
      IndOK t ht j d L hM hLM r a ((regs j).questionOf sel S x) := by
  have hz : (a ++ b).length = N := by rw [List.length_append, hN]
  have hNa := len_eq t j d L (r, S)
  cases S <;> simp only [LIDT.CL.Regs.questionOf, indCons, IndOK] at hNa ⊢
  · simp
  · rw [eqsCons_iff _ _ hz]
    refine indEqs_iff hLM r _ _ a fun c e he => ?_
    rw [zero_add, fldAt_left hN (by
      rw [ha, hNa]
      exact off_add_le (nc := ncoef j d .aline) c.2 (show e + 1 < d + 1 by omega))]
  · simp

/-- **The indifference checks of the second answer**, read. -/
theorem indCons_iff_b (r : Role) (S : LIDT.CL.Ty) (x : Fin (D j) → Fq t ht) {a b : BitStr}
    {N Na : ℕ} (ha : a.length = Na) (hN : Na + b.length = N) :
    (∀ c ∈ indCons j d L hM hLM N Na r ((regs j).questionOf sel S x),
        Satisfies c (a ++ b ++ [true])) ↔
      IndOK t ht j d L hM hLM r b ((regs j).questionOf sel S x) := by
  have hz : (a ++ b).length = N := by rw [List.length_append, ha, hN]
  cases S <;> simp only [LIDT.CL.Regs.questionOf, indCons, IndOK]
  · simp
  · rw [eqsCons_iff _ _ hz]
    exact indEqs_iff hLM r _ _ b fun c e he => fldAt_right ha hN _
  · simp

end ReadInd

/-! ### The proof check -/

section ReadProof

variable {t ht j d L}

/-- **The equations the linear values enter**, read through the values `w` a point answer
carries. -/
theorem proofEqs_iff {N o : ℕ} (v : Fin N → ZMod 2) (w : Slot L → Fq t ht) (p : Fin L.m → Fq t ht)
    (hw : ∀ s, fldAt t ht N (o + idxO s * t) v = w s) :
    (∀ e ∈ proofEqs (t := t) (ht := ht) L N o (w .gO) p, e.1 v = e.2) ↔ PassesL w p := by
  simp only [proofEqs, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    List.mem_finRange, forall_const, List.not_mem_nil, IsEmpty.forall_iff,
    and_true, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, certLin_apply, hw, sub_eq_zero,
    Function.comp_apply]
  unfold PassesL SystemCheckV AssignCheckV
  simp only [Function.comp_apply, mul_sub, mul_add, Finset.mul_sum, mul_assoc]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨by linear_combination h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linear_combination h1, h2, h3⟩, h4⟩

theorem vals_take_of_readable {a : BitStr} {s : Slot L} (hs : s.readable = true) :
    vals t ht j d L (a.take (lenR t j d L (.oracle, .point))) s = vals t ht j d L a s := by
  simp only [vals, cw]
  exact elt_take (off_add_le (k := (rOf L .oracle).length) (idxO_lt_of_readable hs)
    (ncoef_pos j d .point))

theorem fldAt_vals_a {a b : BitStr} {N : ℕ} (ha : a.length = len t j d L (.oracle, .point))
    (hN : a.length + b.length = N) (s : Slot L) :
    fldAt t ht N (0 + idxO s * t) (Intro.bitVec N (a ++ b)) = vals t ht j d L a s := by
  have hle : idxO s * t + t ≤ a.length := by
    have := off_add_le (t := t) (k := (slotsOf L .oracle).length) (nc := 1) (e := 0)
      (idxO_lt s) Nat.one_pos
    rw [ha, len_eq]
    simpa [ncoef] using this
  rw [zero_add, fldAt_left hN hle]
  simp [vals, cw, ncoef]

theorem fldAt_vals_b {a b : BitStr} {N Na : ℕ} (ha : a.length = Na) (hN : Na + b.length = N)
    (s : Slot L) :
    fldAt t ht N (Na + idxO s * t) (Intro.bitVec N (a ++ b)) = vals t ht j d L b s := by
  rw [fldAt_right ha hN]
  simp [vals, cw, ncoef]

/-- **The proof check of the first answer**, read. -/
theorem proofCons_iff_a (T : MvPolynomial (Fin L.m) (Fq t ht)) (p : Fin (2 ^ j) → Fq t ht)
    {a b : BitStr} {N : ℕ} (ha : a.length = len t j d L (.oracle, .point))
    (hN : a.length + b.length = N) :
    (∀ c ∈ proofCons j d L hLM N 0 T p (a.take (lenR t j d L (.oracle, .point))),
        Satisfies c (a ++ b ++ [true])) ↔ PassesV T (vals t ht j d L a) (ptm L hLM p) := by
  have hz : (a ++ b).length = N := by rw [List.length_append, hN]
  rw [proofCons, List.forall_mem_append, guardCons_iff, decide_eq_true_eq, eqsCons_iff _ _ hz,
    passesV_iff, passesR_congr _ _ fun s hs => vals_take_of_readable hs,
    vals_take_of_readable rfl]
  exact and_congr_right fun _ => proofEqs_iff _ _ _ (fldAt_vals_a ha hN)

/-- **The proof check of the second answer**, read. -/
theorem proofCons_iff_b (T : MvPolynomial (Fin L.m) (Fq t ht)) (p : Fin (2 ^ j) → Fq t ht)
    {a b : BitStr} {N Na : ℕ} (ha : a.length = Na) (hN : Na + b.length = N) :
    (∀ c ∈ proofCons j d L hLM N Na T p (b.take (lenR t j d L (.oracle, .point))),
        Satisfies c (a ++ b ++ [true])) ↔ PassesV T (vals t ht j d L b) (ptm L hLM p) := by
  have hz : (a ++ b).length = N := by rw [List.length_append, ha, hN]
  rw [proofCons, List.forall_mem_append, guardCons_iff, decide_eq_true_eq, eqsCons_iff _ _ hz,
    passesV_iff, passesR_congr _ _ fun s hs => vals_take_of_readable hs,
    vals_take_of_readable rfl]
  exact and_congr_right fun _ => proofEqs_iff _ _ _ (fldAt_vals_b ha hN)

end ReadProof

/-! ### All the constraints -/

/-- **The constraints at a pair of typed questions, read**: for answers of their types' lengths,
they hold exactly when the four checks hold of the field elements the answers carry. -/
theorem cons_iff (u v : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (rV + D j * t)))
    {a b : BitStr} (ha : a.length = len t j d L u.1) (hb : b.length = len t j d L v.1) :
    (∀ c ∈ cons t ht j d L rV sel hLM circ u v (a.take (lenR t j d L u.1))
        (b.take (lenR t j d L v.1)), Satisfies c (a ++ b ++ [true])) ↔
      ArPred t ht j d L rV sel hLM circ u v a b := by
  obtain ⟨⟨r1, S1⟩, y1⟩ := u
  obtain ⟨⟨r2, S2⟩, y2⟩ := v
  have hla : (a.take (lenR t j d L (r1, S1))).length = lenR t j d L (r1, S1) := by
    rw [List.length_take, ha]
    exact min_eq_left (lenR_le_len t j d L _)
  have hlb : (b.take (lenR t j d L (r2, S2))).length = lenR t j d L (r2, S2) := by
    rw [List.length_take, hb]
    exact min_eq_left (lenR_le_len t j d L _)
  have hN : a.length + b.length = len t j d L (r1, S1) + len t j d L (r2, S2) := by rw [ha, hb]
  have hN' : len t j d L (r1, S1) + b.length = len t j d L (r1, S1) + len t j d L (r2, S2) := by
    rw [hb]
  rw [cons, ite_eq_left ⟨hla, hlb⟩]
  simp only [List.forall_mem_append, and_assoc, ArPred, ldQ]
  refine Iff.and ?_ (Iff.and ?_ (Iff.and ?_ (Iff.and ?_ (Iff.and ?_ ?_))))
  · -- the low-degree checks
    by_cases h : r1 = r2
    · subst h
      rw [ite_eq_left rfl, ldCons_iff sel r1 S1 S2 _ _ ha hb]
      exact ⟨fun h r h1 _ => h1 ▸ h, fun h => h r1 rfl rfl⟩
    · rw [ite_eq_right h]
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, true_iff]
      intro r h1 h2
      exact absurd (h1.trans h2.symm) h
  · -- the consistency checks
    by_cases h : S1 = S2
    · subst h
      rw [ite_eq_left rfl, consCons_iff S1 r1 r2 ha hb]
      exact ⟨fun h _ => h, fun h => h rfl⟩
    · rw [ite_eq_right h]
      simp [h]
  · exact indCons_iff_a sel hLM r1 S1 _ ha hN
  · exact indCons_iff_b sel hLM r2 S2 _ ha hN'
  · -- the proof check of the first answer
    by_cases h : (r1, S1) = (Role.oracle, LIDT.CL.Ty.point)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [ite_eq_left rfl]
      exact ⟨fun h' _ => (proofCons_iff_a hLM _ _ ha hN).1 h',
        fun h' => (proofCons_iff_a hLM _ _ ha hN).2 (h' rfl)⟩
    · rw [ite_eq_right h]
      simp [h]
  · -- the proof check of the second answer
    by_cases h : (r2, S2) = (Role.oracle, LIDT.CL.Ty.point)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [ite_eq_left rfl]
      exact ⟨fun h' _ => (proofCons_iff_b hLM _ _ ha hN').1 h',
        fun h' => (proofCons_iff_b hLM _ _ ha hN').2 (h' rfl)⟩
    · rw [ite_eq_right h]
      simp [h]

/-- **Typed acceptance, read**: the typed tailored data accepts two answers exactly when they have
their types' lengths and the four checks hold of the field elements they carry. -/
theorem accepts_iff (u v : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (rV + D j * t)))
    (a b : BitStr) :
    (tdata t ht j d L rV sel hLM circ).Accepts u v a b ↔
      a.length = len t j d L u.1 ∧ b.length = len t j d L v.1 ∧
        ArPred t ht j d L rV sel hLM circ u v a b := by
  unfold TypedData.Accepts
  change (a.length = len t j d L u.1 ∧ b.length = len t j d L v.1 ∧ _) ↔ _
  constructor
  · rintro ⟨ha, hb, h⟩
    exact ⟨ha, hb, (cons_iff t ht j d L rV sel hLM circ u v ha hb).1 h⟩
  · rintro ⟨ha, hb, h⟩
    exact ⟨ha, hb, (cons_iff t ht j d L rV sel hLM circ u v ha hb).2 h⟩

end MIPRE.Tailored.AnsRed.Typed

end
