/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.AnsRed.Slots

@[expose] public section

/-!
# The positions of the slots among the oracle's codewords

The oracle's answer in the answer-reduced game lists a codeword for every slot of the PCP, the
readable ones first (`slotsOf`), and a slot's codeword sits at its position `idxO`. The
linear-constraints processor reads the codewords at these positions, so they are computed here
in closed form: the readable slots in the order of `rSlots`, then the linear ones in the order of
`lSlots`, after the `6 + m + 2ℓ + ◇' + 3r` readable ones (`idxO_gA`, …, `idxO_βL`). The isolated
players' codewords are `g_A, g_{La}` and `g_B, g_{Lb}` (`slotsOf_alice`, `slotsOf_bob`).
-/

namespace MIPRE.Tailored.AnsRed

variable {L : PcpDims}

theorem idxOf_ofFn {α : Type*} [DecidableEq α] {n : ℕ} {f : Fin n → α}
    (hf : Function.Injective f) (i : Fin n) : (List.ofFn f).idxOf (f i) = i := by
  have h := List.get_idxOf (List.nodup_ofFn.2 hf) ⟨i, by simp⟩
  simpa using h

theorem finRange3_flatMap {α : Type*} (g : Fin 3 → List α) :
    (List.finRange 3).flatMap g = g 0 ++ (g 1 ++ g 2) := by
  simp [List.finRange_succ, List.flatMap_cons]

section Ofn

variable (L)

theorem idxOf_gW (k : Fin 3) : (List.ofFn (Slot.gW (L := L))).idxOf (.gW k) = k :=
  idxOf_ofFn (fun _ _ h => Slot.gW.inj h) k
theorem idxOf_αR (X : Fin L.m) : (List.ofFn (Slot.αR (L := L))).idxOf (.αR X) = X :=
  idxOf_ofFn (fun _ _ h => Slot.αR.inj h) X
theorem idxOf_βA (i : Fin L.ℓ) : (List.ofFn (Slot.βA (L := L))).idxOf (.βA i) = i :=
  idxOf_ofFn (fun _ _ h => Slot.βA.inj h) i
theorem idxOf_βB (i : Fin L.ℓ) : (List.ofFn (Slot.βB (L := L))).idxOf (.βB i) = i :=
  idxOf_ofFn (fun _ _ h => Slot.βB.inj h) i
theorem idxOf_βO (i : Fin L.oW) : (List.ofFn (Slot.βO (L := L))).idxOf (.βO i) = i :=
  idxOf_ofFn (fun _ _ h => Slot.βO.inj h) i
theorem idxOf_βW (k : Fin 3) (i : Fin L.r) :
    (List.ofFn (Slot.βW (L := L) k)).idxOf (.βW k i) = i :=
  idxOf_ofFn (fun _ _ h => (Slot.βW.inj h).2) i
theorem idxOf_gL (k : Fin 3) : (List.ofFn (Slot.gL (L := L))).idxOf (.gL k) = k :=
  idxOf_ofFn (fun _ _ h => Slot.gL.inj h) k
theorem idxOf_αL (X : Fin L.oW) : (List.ofFn (Slot.αL (L := L))).idxOf (.αL X) = X :=
  idxOf_ofFn (fun _ _ h => Slot.αL.inj h) X
theorem idxOf_βLa (i : Fin L.ℓ) : (List.ofFn (Slot.βLa (L := L))).idxOf (.βLa i) = i :=
  idxOf_ofFn (fun _ _ h => Slot.βLa.inj h) i
theorem idxOf_βLb (i : Fin L.ℓ) : (List.ofFn (Slot.βLb (L := L))).idxOf (.βLb i) = i :=
  idxOf_ofFn (fun _ _ h => Slot.βLb.inj h) i
theorem idxOf_βL (k : Fin 3) (i : Fin L.dm) :
    (List.ofFn (Slot.βL (L := L) k)).idxOf (.βL k i) = i :=
  idxOf_ofFn (fun _ _ h => (Slot.βL.inj h).2) i

end Ofn

/-- The simp set that computes positions of slots in the oracle's codewords. -/
macro "slot_idx" : tactic => `(tactic|
  (simp [idxO, slotsOf, rOf, lOf, rSlots, lSlots, finRange3_flatMap, List.idxOf_append_of_notMem,
    List.idxOf_append_of_mem, List.mem_ofFn, idxOf_gW, idxOf_αR, idxOf_βA, idxOf_βB, idxOf_βO,
    idxOf_βW, idxOf_gL, idxOf_αL, idxOf_βLa, idxOf_βLb, idxOf_βL] <;> omega))

/-! ## The readable slots -/

@[simp] theorem idxO_gA : idxO (L := L) .gA = 0 := by slot_idx
@[simp] theorem idxO_gB : idxO (L := L) .gB = 1 := by slot_idx
@[simp] theorem idxO_gO : idxO (L := L) .gO = 2 := by slot_idx
theorem idxO_gW (k : Fin 3) : idxO (L := L) (.gW k) = 3 + k := by
  fin_cases k <;> slot_idx
theorem idxO_αR (X : Fin L.m) : idxO (L := L) (.αR X) = 6 + X := by slot_idx
theorem idxO_βA (i : Fin L.ℓ) : idxO (L := L) (.βA i) = 6 + L.m + i := by slot_idx
theorem idxO_βB (i : Fin L.ℓ) : idxO (L := L) (.βB i) = 6 + L.m + L.ℓ + i := by slot_idx
theorem idxO_βO (i : Fin L.oW) : idxO (L := L) (.βO i) = 6 + L.m + L.ℓ + L.ℓ + i := by slot_idx
theorem idxO_βW (k : Fin 3) (i : Fin L.r) :
    idxO (L := L) (.βW k i) = 6 + L.m + L.ℓ + L.ℓ + L.oW + k * L.r + i := by
  fin_cases k <;> slot_idx

/-! ## The linear slots -/

theorem idxO_gLa : idxO (L := L) .gLa = (rSlots L).length := by slot_idx
theorem idxO_gLb : idxO (L := L) .gLb = (rSlots L).length + 1 := by slot_idx
theorem idxO_gL (k : Fin 3) : idxO (L := L) (.gL k) = (rSlots L).length + 2 + k := by
  fin_cases k <;> slot_idx
theorem idxO_αL (X : Fin L.oW) : idxO (L := L) (.αL X) = (rSlots L).length + 5 + X := by
  slot_idx
theorem idxO_βLa (i : Fin L.ℓ) :
    idxO (L := L) (.βLa i) = (rSlots L).length + 5 + L.oW + i := by slot_idx
theorem idxO_βLb (i : Fin L.ℓ) :
    idxO (L := L) (.βLb i) = (rSlots L).length + 5 + L.oW + L.ℓ + i := by slot_idx
theorem idxO_βL (k : Fin 3) (i : Fin L.dm) :
    idxO (L := L) (.βL k i) = (rSlots L).length + 5 + L.oW + L.ℓ + L.ℓ + k * L.dm + i := by
  fin_cases k <;> slot_idx

/-! ## The isolated players' codewords -/

theorem slotsOf_alice : slotsOf L .alice = [.gA, .gLa] := rfl
theorem slotsOf_bob : slotsOf L .bob = [.gB, .gLb] := rfl

/-! ## The blocks of the slots -/

/-- **The first wire of a slot's block**: each block is the interval of `size` wires from it. -/
def Slot.lo : Slot L → ℕ
  | .gA | .βA _ => 1
  | .gB | .βB _ => L.ℓ + 2
  | .gO | .βO _ | .αL _ => L.ℓ + L.ℓ + 3
  | .gW k | .βW k _ => L.ℓ + L.ℓ + 3 + L.oW + k * L.r
  | .αR _ => 0
  | .gLa | .βLa _ => L.ℓ + L.ℓ + 3
  | .gLb | .βLb _ => L.ℓ + L.ℓ + 3 + L.ℓ
  | .gL k | .βL k _ => L.ℓ + L.ℓ + 3 + L.ℓ + L.ℓ + k * L.dm

/-- **A slot's block is the interval of `size` wires from `lo`.** -/
theorem Slot.val_emb : (s : Slot L) → (x : Fin s.size) → (s.emb x : ℕ) = s.lo + x
  | .gA, x | .βA _, x => show 1 + (x : ℕ) = 1 + x from rfl
  | .gB, x | .βB _, x => show L.ℓ + 1 + 1 + (x : ℕ) = L.ℓ + 2 + x by omega
  | .gO, x | .βO _, x | .αL _, x =>
    show L.ℓ + 1 + (L.ℓ + 1) + 1 + (x : ℕ) = L.ℓ + L.ℓ + 3 + x by omega
  | .gW k, x | .βW k _, x =>
    show L.ℓ + 1 + (L.ℓ + 1) + (L.oW + 1) + k * L.r + (x : ℕ) =
      L.ℓ + L.ℓ + 3 + L.oW + k * L.r + x by omega
  | .αR _, x => show (x : ℕ) = 0 + x by omega
  | .gLa, x | .βLa _, x => show L.ℓ + 1 + (L.ℓ + 1) + 1 + (x : ℕ) = L.ℓ + L.ℓ + 3 + x by omega
  | .gLb, x | .βLb _, x =>
    show L.ℓ + 1 + (L.ℓ + 1) + 1 + (L.ℓ + (x : ℕ)) = L.ℓ + L.ℓ + 3 + L.ℓ + x by omega
  | .gL k, x | .βL k _, x =>
    show L.ℓ + 1 + (L.ℓ + 1) + 1 + (L.ℓ + L.ℓ + k * L.dm + (x : ℕ)) =
      L.ℓ + L.ℓ + 3 + L.ℓ + L.ℓ + k * L.dm + x by omega

/-- A wire lies in a slot's block exactly when it lies in its interval. -/
theorem Slot.exists_emb_iff (s : Slot L) (w : ℕ) :
    (∃ x, (s.emb x : ℕ) = w) ↔ s.lo ≤ w ∧ w < s.lo + s.size := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [s.val_emb x]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left x.2 _⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨w - s.lo, by omega⟩, by rw [s.val_emb]; simp only; omega⟩

end MIPRE.Tailored.AnsRed

end
