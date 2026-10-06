/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.Pcp
public import MIPRE.Foundations.OracularGame

@[expose] public section

/-!
# The polynomials of a PCP, slot by slot

The answer-reduced game (`defn:combi_ans_red`, II:10285) asks the oracle for a PCP evaluated at a
point or restricted to a line, and the isolated players for two of its polynomials: Alice for the
two assignments `g_A, g_{La}` of the first answer, Bob for those of the second (Table
tab:Answer_Lengths_combinatorial_ans_red). This file names the polynomials of a PCP (`Pcp`), so
that the game can list them as codewords and compare them across players.

* `Slot L`: one slot for each polynomial of a PCP of layout `L`, with its readability
  (`Slot.readable`), the number of its variables (`Slot.size`) and their place among the PCP's
  (`Slot.emb`, the blocks of Definition defn:blocks_of_vars_circuit).
* The codewords of a role (`slotsOf`), readable first: the oracle's are all the slots
  (`oSlots`, `heartsuit = ♥^R + ♥^L` of eq:def_heartsuit), an isolated player's the two of its
  answer.
* A PCP's polynomial in a slot (`Pcp.slot`), its value at a point (`Pcp.slotEval`), and the
  thirteen checks on slot values (`PassesV`), which are the checks of `Pcp.Passes`
  (`passes_iff_passesV`), split into the part on readable values (`PassesR`) and the part the
  linear values enter (`PassesL`).
* From polynomials on more variables that each depend only on their slot's block — what the
  game's indifference check guarantees — the PCP they are (`Pcp.ofPolys`): its slots, renamed
  back, are the given polynomials (`rename_ofPolys_slot`), so its values are theirs.
-/

namespace MIPRE.Tailored.AnsRed

open MvPolynomial

variable {L : PcpDims}

/-- **The slots of a PCP** (Definition defn:PCP_of_V_n_satisfied): one for each polynomial, the
readable ones first. -/
inductive Slot (L : PcpDims)
  | gA
  | gB
  | gO
  | gW (k : Fin 3)
  | αR (X : Fin L.m)
  | βA (i : Fin L.ℓ)
  | βB (i : Fin L.ℓ)
  | βO (i : Fin L.oW)
  | βW (k : Fin 3) (i : Fin L.r)
  | gLa
  | gLb
  | gL (k : Fin 3)
  | αL (X : Fin L.oW)
  | βLa (i : Fin L.ℓ)
  | βLb (i : Fin L.ℓ)
  | βL (k : Fin 3) (i : Fin L.dm)
  deriving DecidableEq

namespace Slot

/-- Whether a slot is readable: the paper's `Π^R`. -/
def readable : Slot L → Bool
  | gA | gB | gO | gW _ | αR _ | βA _ | βB _ | βO _ | βW _ _ => true
  | gLa | gLb | gL _ | αL _ | βLa _ | βLb _ | βL _ _ => false

/-- The number of variables of a slot's polynomial. -/
def size : Slot L → ℕ
  | gA | βA _ | gB | βB _ | gLa | βLa _ | gLb | βLb _ => L.ℓ
  | gO | βO _ | αL _ => L.oW
  | gW _ | βW _ _ => L.r
  | αR _ => L.m
  | gL _ | βL _ _ => L.dm

/-- **The block of a slot**: where its variables sit among the PCP's. -/
def emb : (s : Slot L) → Fin s.size → Fin L.m
  | gA | βA _ => L.vA
  | gB | βB _ => L.vB
  | gO | βO _ | αL _ => L.vO
  | gW k | βW k _ => L.vW k
  | αR _ => id
  | gLa | βLa _ => L.vO ∘ L.oA
  | gLb | βLb _ => L.vO ∘ L.oB
  | gL k | βL k _ => L.vO ∘ L.oL k

theorem emb_injective : ∀ s : Slot L, Function.Injective s.emb
  | gA | βA _ => L.vA_injective
  | gB | βB _ => L.vB_injective
  | gO | βO _ | αL _ => L.vO_injective
  | gW k | βW k _ => L.vW_injective k
  | αR _ => Function.injective_id
  | gLa | βLa _ => L.vO_injective.comp L.oA_injective
  | gLb | βLb _ => L.vO_injective.comp L.oB_injective
  | gL k | βL k _ => L.vO_injective.comp (L.oL_injective k)

end Slot

/-! ## The codewords of the roles -/

variable (L) in
/-- The readable slots, in the order of the oracle's codewords. -/
def rSlots : List (Slot L) :=
  [.gA, .gB, .gO] ++ List.ofFn Slot.gW ++ List.ofFn Slot.αR ++ List.ofFn Slot.βA ++
    List.ofFn Slot.βB ++ List.ofFn Slot.βO ++
      (List.finRange 3).flatMap fun k => List.ofFn (Slot.βW k)

variable (L) in
/-- The linear slots, in the order of the oracle's codewords. -/
def lSlots : List (Slot L) :=
  [.gLa, .gLb] ++ List.ofFn Slot.gL ++ List.ofFn Slot.αL ++ List.ofFn Slot.βLa ++
    List.ofFn Slot.βLb ++ (List.finRange 3).flatMap fun k => List.ofFn (Slot.βL k)

variable (L) in
/-- **The readable codewords of a role**: all the readable slots for the oracle, `g_A` for Alice
and `g_B` for Bob. -/
def rOf : Role → List (Slot L)
  | .oracle => rSlots L
  | .alice => [.gA]
  | .bob => [.gB]

variable (L) in
/-- **The linear codewords of a role**: all the linear slots for the oracle, `g_{La}` for Alice
and `g_{Lb}` for Bob. -/
def lOf : Role → List (Slot L)
  | .oracle => lSlots L
  | .alice => [.gLa]
  | .bob => [.gLb]

variable (L) in
/-- **The codewords of a role**, readable first. -/
def slotsOf (r : Role) : List (Slot L) := rOf L r ++ lOf L r

theorem readable_of_mem_rSlots {s : Slot L} (h : s ∈ rSlots L) : s.readable = true := by
  simp only [rSlots, List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
    List.mem_ofFn', Set.mem_range, List.mem_flatMap, List.mem_finRange, true_and] at h
  rcases h with rfl | rfl | rfl |
    (((((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, _, rfl⟩) <;> rfl

theorem not_readable_of_mem_lSlots {s : Slot L} (h : s ∈ lSlots L) : s.readable = false := by
  simp only [lSlots, List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
    List.mem_ofFn', Set.mem_range, List.mem_flatMap, List.mem_finRange, true_and] at h
  rcases h with rfl | rfl | ((((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, _, rfl⟩) <;> rfl

theorem readable_of_mem_rOf {r : Role} {s : Slot L} (h : s ∈ rOf L r) : s.readable = true := by
  cases r
  · exact readable_of_mem_rSlots h
  · simp only [rOf, List.mem_singleton] at h; subst h; rfl
  · simp only [rOf, List.mem_singleton] at h; subst h; rfl

theorem not_readable_of_mem_lOf {r : Role} {s : Slot L} (h : s ∈ lOf L r) :
    s.readable = false := by
  cases r
  · exact not_readable_of_mem_lSlots h
  · simp only [lOf, List.mem_singleton] at h; subst h; rfl
  · simp only [lOf, List.mem_singleton] at h; subst h; rfl

/-- **Every slot is a codeword of the oracle.** -/
theorem mem_slotsOf_oracle (s : Slot L) : s ∈ slotsOf L .oracle := by
  simp only [slotsOf, rOf, lOf, rSlots, lSlots, List.cons_append, List.nil_append,
    List.mem_cons, List.mem_append, List.mem_ofFn', Set.mem_range, List.mem_flatMap,
    List.mem_finRange, true_and]
  cases s <;> simp

theorem mem_rSlots_of_readable {s : Slot L} (h : s.readable = true) : s ∈ rSlots L := by
  have hm := mem_slotsOf_oracle s
  simp only [slotsOf, rOf, lOf, List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · rw [not_readable_of_mem_lSlots hm] at h
    exact absurd h (by simp)

/-! ## Positions among the oracle's codewords -/

/-- **The position of a slot among the oracle's codewords.** -/
def idxO (s : Slot L) : ℕ := (slotsOf L .oracle).idxOf s

theorem idxO_lt (s : Slot L) : idxO s < (slotsOf L .oracle).length :=
  List.idxOf_lt_length_of_mem (mem_slotsOf_oracle s)

theorem getElem_idxO (s : Slot L) : (slotsOf L .oracle)[idxO s]'(idxO_lt s) = s :=
  List.getElem_idxOf (idxO_lt s)

/-- **A readable slot sits among the oracle's readable codewords.** -/
theorem idxO_lt_of_readable {s : Slot L} (h : s.readable = true) :
    idxO s < (rSlots L).length := by
  have hm := mem_rSlots_of_readable h
  rw [idxO, slotsOf, rOf, List.idxOf_append_of_mem hm]
  exact List.idxOf_lt_length_of_mem hm

/-- A codeword of a role is readable exactly when it is among the role's readable ones. -/
theorem readable_getElem_slotsOf (r : Role) {c : ℕ} (hc : c < (slotsOf L r).length) :
    ((slotsOf L r)[c]).readable = true ↔ c < (rOf L r).length := by
  simp only [slotsOf] at hc ⊢
  by_cases h : c < (rOf L r).length
  · rw [List.getElem_append_left h]
    exact iff_of_true (readable_of_mem_rOf (List.getElem_mem _)) h
  · rw [List.getElem_append_right (by omega)]
    rw [not_readable_of_mem_lOf (List.getElem_mem _)]
    exact iff_of_false (by simp) h

theorem length_rSlots : (rSlots L).length = 6 + L.m + L.ℓ + L.ℓ + L.oW + 3 * L.r := by
  simp only [rSlots, List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
    List.length_flatMap, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]

theorem length_lSlots : (lSlots L).length = 5 + L.oW + L.ℓ + L.ℓ + 3 * L.dm := by
  simp only [lSlots, List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
    List.length_flatMap, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]

/-! ## A PCP's slots -/

section Values

variable {F : Type*} [CommRing F]

/-- **A PCP's polynomial in a slot**, on the slot's variables. -/
def Pcp.slot (P : Pcp L F) : (s : Slot L) → MvPolynomial (Fin s.size) F
  | .gA => P.gA
  | .gB => P.gB
  | .gO => P.gO
  | .gW k => P.gW k
  | .αR X => P.αR X
  | .βA i => P.βA i
  | .βB i => P.βB i
  | .βO i => P.βO i
  | .βW k i => P.βW k i
  | .gLa => P.gLa
  | .gLb => P.gLb
  | .gL k => P.gL k
  | .αL X => P.αL X
  | .βLa i => P.βLa i
  | .βLb i => P.βLb i
  | .βL k i => P.βL k i

/-- **A PCP's value in a slot** at a point of the PCP's variables. -/
def Pcp.slotEval (P : Pcp L F) (p : Fin L.m → F) (s : Slot L) : F := eval (p ∘ s.emb) (P.slot s)

/-- A PCP's polynomial in a slot, on all the PCP's variables. -/
noncomputable def Pcp.slotPoly (P : Pcp L F) (s : Slot L) : MvPolynomial (Fin L.m) F :=
  rename s.emb (P.slot s)

theorem Pcp.eval_slotPoly (P : Pcp L F) (p : Fin L.m → F) (s : Slot L) :
    eval p (P.slotPoly s) = P.slotEval p s := by
  rw [slotPoly, eval_rename, slotEval]

/-- The formula check on the values of the slots at a point. -/
def FormulaCheckV (T : MvPolynomial (Fin L.m) F) (w : Slot L → F) (p : Fin L.m → F) : Prop :=
  eval p T * (p L.πA * w .gA - p (L.sgn 0)) * (p L.πB * w .gB - p (L.sgn 1)) *
      (p L.πC * w .gO - p (L.sgn 2)) *
      ∏ k : Fin 3, (w (.gW k) - p (L.sgn (3 + k.castLE (by omega)))) =
    ∑ X, p X * (1 - p X) * w (.αR X)

/-- The system check on the values of the slots at a point of the index space of `O`. -/
def SystemCheckV (w : Slot L → F) (x : Fin L.oW → F) : Prop :=
  w .gO * (x (L.oSgn 0) * w .gLa + x (L.oSgn 1) * w .gLb +
      ∑ k : Fin 3, x (L.oSgn (2 + k.castLE (by omega))) * w (.gL k) - x (L.oSgn 5)) =
    ∑ X, x X * (1 - x X) * w (.αL X)

/-- An assignment check on values: `g (1 - g)` is the certificate sum at `x`. -/
def AssignCheckV {k : ℕ} (g : F) (β : Fin k → F) (x : Fin k → F) : Prop :=
  g * (1 - g) = ∑ i, x i * (1 - x i) * β i

/-- **The thirteen checks on the values of the slots** at a point, in the order of
`Pcp.Passes`. -/
def PassesV (T : MvPolynomial (Fin L.m) F) (w : Slot L → F) (p : Fin L.m → F) : Prop :=
  FormulaCheckV T w p ∧ SystemCheckV w (p ∘ L.vO) ∧
    AssignCheckV (w .gA) (fun i => w (.βA i)) (p ∘ L.vA) ∧
    AssignCheckV (w .gB) (fun i => w (.βB i)) (p ∘ L.vB) ∧
    AssignCheckV (w .gO) (fun i => w (.βO i)) (p ∘ L.vO) ∧
    (∀ k, AssignCheckV (w (.gW k)) (fun i => w (.βW k i)) (p ∘ L.vW k)) ∧
    AssignCheckV (w .gLa) (fun i => w (.βLa i)) (p ∘ L.vO ∘ L.oA) ∧
    AssignCheckV (w .gLb) (fun i => w (.βLb i)) (p ∘ L.vO ∘ L.oB) ∧
    ∀ k, AssignCheckV (w (.gL k)) (fun i => w (.βL k i)) (p ∘ L.vO ∘ L.oL k)

/-- **The checks of a PCP at a point are the checks on its values there.** -/
theorem passes_iff_passesV (T : MvPolynomial (Fin L.m) F) (P : Pcp L F) (p : Fin L.m → F) :
    P.Passes T p ↔ PassesV T (P.slotEval p) p := Iff.rfl

/-- The checks on the readable values: the formula check and the readable assignment checks. -/
def PassesR (T : MvPolynomial (Fin L.m) F) (w : Slot L → F) (p : Fin L.m → F) : Prop :=
  FormulaCheckV T w p ∧
    AssignCheckV (w .gA) (fun i => w (.βA i)) (p ∘ L.vA) ∧
    AssignCheckV (w .gB) (fun i => w (.βB i)) (p ∘ L.vB) ∧
    AssignCheckV (w .gO) (fun i => w (.βO i)) (p ∘ L.vO) ∧
    ∀ k, AssignCheckV (w (.gW k)) (fun i => w (.βW k i)) (p ∘ L.vW k)

/-- The checks the linear values enter: the system check and the linear assignment checks. -/
def PassesL (w : Slot L → F) (p : Fin L.m → F) : Prop :=
  SystemCheckV w (p ∘ L.vO) ∧
    AssignCheckV (w .gLa) (fun i => w (.βLa i)) (p ∘ L.vO ∘ L.oA) ∧
    AssignCheckV (w .gLb) (fun i => w (.βLb i)) (p ∘ L.vO ∘ L.oB) ∧
    ∀ k, AssignCheckV (w (.gL k)) (fun i => w (.βL k i)) (p ∘ L.vO ∘ L.oL k)

instance [DecidableEq F] (T : MvPolynomial (Fin L.m) F) (w : Slot L → F) (p : Fin L.m → F) :
    Decidable (PassesR T w p) := by
  unfold PassesR FormulaCheckV AssignCheckV
  infer_instance

theorem passesV_iff (T : MvPolynomial (Fin L.m) F) (w : Slot L → F) (p : Fin L.m → F) :
    PassesV T w p ↔ PassesR T w p ∧ PassesL w p := by
  unfold PassesV PassesR PassesL
  tauto

/-- **The readable checks read only readable values.** -/
theorem passesR_congr (T : MvPolynomial (Fin L.m) F) {w w' : Slot L → F} (p : Fin L.m → F)
    (h : ∀ s, s.readable = true → w s = w' s) : PassesR T w p ↔ PassesR T w' p := by
  have e : ∀ s, s.readable = true → w s = w' s := h
  unfold PassesR FormulaCheckV AssignCheckV
  rw [e .gA rfl, e .gB rfl, e .gO rfl]
  simp only [e (.gW _) rfl, e (.αR _) rfl, e (.βA _) rfl, e (.βB _) rfl, e (.βO _) rfl,
    e (.βW _ _) rfl]

end Values

/-! ## The PCP of block-local polynomials -/

section OfPolys

variable {F : Type*} [CommRing F] {N : ℕ} (ι : Fin L.m → Fin N) (hι : Function.Injective ι)

/-- The polynomial on a slot's variables that a polynomial on `N` variables is, when it depends
only on the slot's block (placed among the `N` variables by `ι`). -/
noncomputable def slotOf (s : Slot L) (g : MvPolynomial (Fin N) F) : MvPolynomial (Fin s.size) F :=
  killCompl (hι.comp s.emb_injective) g

/-- **The PCP of a family of polynomials on `N` variables**, one per slot, each read on its
slot's block. -/
noncomputable def Pcp.ofPolys (f : Slot L → MvPolynomial (Fin N) F) : Pcp L F where
  gA := slotOf ι hι .gA (f .gA)
  gB := slotOf ι hι .gB (f .gB)
  gO := slotOf ι hι .gO (f .gO)
  gW k := slotOf ι hι (.gW k) (f (.gW k))
  gLa := slotOf ι hι .gLa (f .gLa)
  gLb := slotOf ι hι .gLb (f .gLb)
  gL k := slotOf ι hι (.gL k) (f (.gL k))
  αR X := slotOf ι hι (.αR X) (f (.αR X))
  αL X := slotOf ι hι (.αL X) (f (.αL X))
  βA i := slotOf ι hι (.βA i) (f (.βA i))
  βB i := slotOf ι hι (.βB i) (f (.βB i))
  βO i := slotOf ι hι (.βO i) (f (.βO i))
  βW k i := slotOf ι hι (.βW k i) (f (.βW k i))
  βLa i := slotOf ι hι (.βLa i) (f (.βLa i))
  βLb i := slotOf ι hι (.βLb i) (f (.βLb i))
  βL k i := slotOf ι hι (.βL k i) (f (.βL k i))

theorem Pcp.slot_ofPolys (f : Slot L → MvPolynomial (Fin N) F) (s : Slot L) :
    (Pcp.ofPolys ι hι f).slot s = slotOf ι hι s (f s) := by
  cases s <;> rfl

/-- A polynomial that depends only on a slot's block is the renaming of its reading there. -/
theorem rename_slotOf {s : Slot L} {g : MvPolynomial (Fin N) F}
    (hg : ↑g.vars ⊆ Set.range (ι ∘ s.emb)) : rename (ι ∘ s.emb) (slotOf ι hι s g) = g := by
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range g _ (hι.comp s.emb_injective) hg
  rw [slotOf, killCompl_rename_app]

/-- **The slots of the PCP of block-local polynomials, renamed back, are the polynomials.** -/
theorem rename_ofPolys_slot {f : Slot L → MvPolynomial (Fin N) F}
    (hf : ∀ s, ↑(f s).vars ⊆ Set.range (ι ∘ s.emb)) (s : Slot L) :
    rename (ι ∘ s.emb) ((Pcp.ofPolys ι hι f).slot s) = f s := by
  rw [Pcp.slot_ofPolys, rename_slotOf ι hι (hf s)]

/-- **The values of the PCP of block-local polynomials are theirs.** -/
theorem slotEval_ofPolys {f : Slot L → MvPolynomial (Fin N) F}
    (hf : ∀ s, ↑(f s).vars ⊆ Set.range (ι ∘ s.emb)) (u : Fin N → F) (s : Slot L) :
    (Pcp.ofPolys ι hι f).slotEval (u ∘ ι) s = eval u (f s) := by
  conv_rhs => rw [← rename_ofPolys_slot ι hι hf s]
  rw [eval_rename, Pcp.slotEval]
  rfl

/-- **The PCP of block-local polynomials of individual degree at most `d` has degree at most
`d`.** -/
theorem indDeg_ofPolys {f : Slot L → MvPolynomial (Fin N) F}
    (hf : ∀ s, ↑(f s).vars ⊆ Set.range (ι ∘ s.emb)) {d : ℕ}
    (hd : ∀ s i, (f s).degreeOf i ≤ d) : (Pcp.ofPolys ι hι f).IndDeg d := by
  have key : ∀ s (i : Fin s.size), ((Pcp.ofPolys ι hι f).slot s).degreeOf i ≤ d := by
    intro s i
    have h := hd s ((ι ∘ s.emb) i)
    rw [← rename_ofPolys_slot ι hι hf s,
      degreeOf_rename_of_injective (hι.comp s.emb_injective)] at h
    exact h
  exact ⟨key .gA, key .gB, key .gO, fun k => key (.gW k), key .gLa, key .gLb,
    fun k => key (.gL k), fun X => key (.αR X), fun X => key (.αL X), fun i => key (.βA i),
    fun i => key (.βB i), fun i => key (.βO i), fun k i => key (.βW k i), fun i => key (.βLa i),
    fun i => key (.βLb i), fun k i => key (.βL k i)⟩

end OfPolys

end MIPRE.Tailored.AnsRed

end
