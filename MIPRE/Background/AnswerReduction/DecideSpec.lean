/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.Background.AnswerReduction.TypedGame
import MIPRE.Background.AnswerReduction.PcpSampler
import MIPRE.Foundations.Introspection.FieldLineCheckProg
import MIPRE.Foundations.Introspection.FieldQuestionProg

/-!
# The answer-reduced decision, on blocks of bits

Piece AR-3e of `planning/answer-reduction.md`: the decision predicate `accepts` of
`MIPRE/Background/AnswerReduction/Predicate`, rewritten as a function of the `k`-bit blocks a
program reads (`verdictB`), with the field arithmetic done by the introspection stage programs:
the line-versus-point check (`FieldLineCheck.lineCheckProg`), the seed selector, and the line
representatives the sampler's third stage already uses.

* **The low-degree subtests** (`ldB`): of the seeded test's decision, only a point question
  against a line question of the same copy is ever checked, and there it is the line-versus-point
  check on the line the question describes (`ldB_aline`, `ldB_dline`).
* **The five steps** (`sideB`) are organised by what each type pair asks for: at most one
  comparison of two answer blocks (`eqPlan`), one low-degree subtest (`ldPlan`) and one game check
  (`chkPlan`), which are functions of the types alone. `sideB_eq` is `side`.
* **The predicate** (`verdictB_eq`) is the typed predicate `typedPred`, the answers parsed into
  blocks (`parseB`) and the questions' PCP halves split into their three runs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck
  Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL

/-! ## Lists of blocks -/

/-- A list cut into `n` consecutive runs of `w` elements. -/
def chunks {α : Type*} (w : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | n + 1, l => l.take w :: chunks w n (l.drop w)

theorem chunks_eq {α : Type*} (w : ℕ) : ∀ (n : ℕ) (l : List α),
    chunks w n l = List.ofFn fun c : Fin n => (l.drop (c * w)).take w
  | 0, _ => rfl
  | n + 1, l => by
    rw [chunks, chunks_eq w n, List.ofFn_succ]
    congr 1
    · simp
    · congr 1
      funext c
      simp only [Fin.val_succ, List.drop_drop, Nat.succ_mul]
      rw [Nat.add_comm w]

theorem chunks_ofFn {α : Type*} (w n : ℕ) (g : Fin n → Fin w → α) :
    chunks w n (List.ofFn fun r : Fin (n * w) => g (finProdFinEquiv.symm r).1
      (finProdFinEquiv.symm r).2) = List.ofFn fun c => List.ofFn (g c) := by
  rw [chunks_eq]
  apply congrArg List.ofFn
  funext c
  have hc : (c : ℕ) * w + w ≤ n * w := by
    have := c.isLt
    nlinarith
  apply List.ext_getElem
  · simp; omega
  · intro j h₁ h₂
    simp only [List.length_ofFn] at h₂
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    have hw : 0 < w := by omega
    congr 1
    · apply Fin.ext
      simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt h₂, zero_add]
    · apply Fin.ext
      simp only [finProdFinEquiv_symm_apply, Fin.coe_modNat]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂]

/-! ## The line-versus-point check -/

section Line

variable {k : ℕ} (hk : 1 ≤ k)

local notation "E" => shoupBinField k hk

/-- **The line-versus-point check on blocks**: every codeword's polynomial, evaluated at the
point's parameter on the line, gives the point's value. -/
def lvpB (kU : Unary) (base dir pt : List BitStr) (polys : List (List BitStr))
    (vals : List BitStr) : Bool :=
  (polys.zip vals).all fun fa => lineCheckProg ((kU, base, dir, pt), fa.1, fa.2)

theorem lineParam_eq {m : ℕ} (u₀ w x : Point (E).carrier m) :
    lineParam u₀ w x = parameter u₀ w x := by
  rw [parameter_eq]; rfl

theorem lvpB_eq {m ldc d : ℕ} [NeZero ldc] (u₀ w x : Point (E).carrier m)
    (f : Fin ldc → LinePoly (E).carrier d) (a : Fin ldc → (E).carrier) :
    lvpB (unary k) ((E).vecBits u₀) ((E).vecBits w) ((E).vecBits x)
      (List.ofFn fun j => (E).vecBits (f j)) ((E).vecBits a) = lineVsPoint u₀ w x f a := by
  have hz : (List.ofFn fun j => (E).vecBits (f j)).zip ((E).vecBits a) =
      List.ofFn fun j => ((E).vecBits (f j), (E).toBits (a j)) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  rw [lvpB, hz, lineVsPoint]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    lineCheckProg_correct k hk, decide_eq_true_eq, LinePoly.eval, lineParam_eq]
  constructor
  · intro h
    exact ⟨(h 0).1, fun j => (h j).2⟩
  · rintro ⟨h₁, h₂⟩ j
    exact ⟨h₁, h₂ j⟩

end Line

/-! ## The low-degree subtests of a copy -/

/-- The direction of the line a question of test type `τ` describes, from its seed and its
blocks: the selected axis, or the selected diagonal direction. -/
def dirB (kU : Unary) (d : Desc) (τ : ℕ) (s : BitStr) (Y : Blocks) : List BitStr :=
  if τ = 1 then axisDirectionProg ((kU, d.2.2.1, d.2.1), s)
  else selDirL kU d s (sliceL d.1.length d.2.1.length Y.2.1)

/-- **The low-degree subtest of a copy** `d`: the point the question with blocks `X` carries,
against the line of test type `τ` the question with blocks `Y` carries. -/
def ldB (kU : Unary) (d : Desc) (τ : ℕ) (X Y : Blocks) (polys : List (List BitStr))
    (vals : List BitStr) : Bool :=
  let s := seedOf d Y.2.2
  let dir := dirB kU d τ s Y
  lvpB kU (ptMapL kU d τ s dir (sliceL d.1.length d.2.1.length Y.1)) dir
    (sliceL d.1.length d.2.1.length X.1) polys vals

section Copy

variable {k : ℕ} (hk : 1 ≤ k)

local notation "E" => shoupBinField k hk

variable (P : PcpParams)

/-- The three runs of blocks of a vector of `V^pcp`. -/
def blocksV (x : Coord P → (E).carrier) : Blocks :=
  ((E).vecBits (ptOf6 P x), (E).vecBits (dirOf6 P x), (E).vecBits (seedsOf P x))

variable (o sz jw : ℕ) (c : Fin 6) (h : o + sz ≤ P.m') (hjw : jw ≤ k) (hsz2 : sz = 2 ^ jw)
  [NeZero sz] {hsz : sz ∣ Fintype.card (shoupBinField k hk).carrier}
  (S : Sel (shoupBinField k hk).carrier sz hsz)
  (hχ : ∀ a, (S.χ a : ℕ) = (selector (shoupBinField k hk) jw hjw a : ℕ))

local notation "D" => ((unary o, unary sz, unary jw, unary c) : Desc)
local notation "R" => regsAt P o sz c h

omit [NeZero sz] in
theorem seedOf_blocksV (y : Coord P → (E).carrier) :
    seedOf D (blocksV hk P y).2.2 = (E).toBits (y (R).coord) :=
  seedOf_vecBits hk o sz jw c _

omit [NeZero sz] in
theorem pt_blocksV (y : Coord P → (E).carrier) :
    sliceL (unary o).length (unary sz).length (blocksV hk P y).1 = (E).vecBits ((R).ptOf y) := by
  rw [length_unary, length_unary, blocksV, ← vecBits_sliceV hk o sz h]
  rfl

omit [NeZero sz] in
theorem dir_blocksV (y : Coord P → (E).carrier) :
    sliceL (unary o).length (unary sz).length (blocksV hk P y).2.1 =
      (E).vecBits ((R).dirOf y) := by
  rw [length_unary, length_unary, blocksV, ← vecBits_sliceV hk o sz h]
  rfl

include hχ hsz2 in
/-- **The axis-parallel subtest**. -/
theorem ldB_aline {ldc d : ℕ} [NeZero ldc] (xp xq : Coord P → (E).carrier)
    (av : Fin ldc → (E).carrier) (f : Fin ldc → LinePoly (E).carrier d) :
    ldB (unary k) D 1 (blocksV hk P xp) (blocksV hk P xq) (List.ofFn fun j => (E).vecBits (f j))
      ((E).vecBits av) =
    LIDT.CL.accepts hsz (((R).sampleOf S .point xp).question hsz .point)
      (((R).sampleOf S .aline xq).question hsz .aline) (.values av) (.apolys f) := by
  subst hsz2
  simp only [ldB, dirB, if_true, seedOf_blocksV hk P o (2 ^ jw) jw c h]
  rw [axisDirectionProg_correct k hk jw hjw, pt_blocksV hk P o (2 ^ jw) c h,
    pt_blocksV hk P o (2 ^ jw) c h]
  have hs : ∀ a, (Pi.single (selector (E) jw hjw a) 1 : Fin (2 ^ jw) → (E).carrier) =
      Pi.single (S.χ a) 1 := fun a => congrArg (Pi.single · 1) (Fin.ext (hχ a).symm)
  rw [hs]
  have hmap := ptMapL_vecBits hk o (2 ^ jw) jw c S hjw hχ .aline
  simp only [tyNat] at hmap
  rw [hmap, lvpB_eq hk]
  simp only [LIDT.CL.accepts, Sample.question, Regs.sampleOf, Question.fmtOk, subtests,
    Bool.true_and, S.chi_π]
  rfl

include hχ in
/-- **The diagonal subtest**. -/
theorem ldB_dline {ldc d : ℕ} [NeZero ldc] (xp xq : Coord P → (E).carrier)
    (av : Fin ldc → (E).carrier) (f : Fin ldc → LinePoly (E).carrier (sz * d)) :
    ldB (unary k) D 2 (blocksV hk P xp) (blocksV hk P xq) (List.ofFn fun j => (E).vecBits (f j))
      ((E).vecBits av) =
    LIDT.CL.accepts hsz (((R).sampleOf S .point xp).question hsz .point)
      (((R).sampleOf S .dline xq).question hsz .dline) (.values av) (.dpolys f) := by
  simp only [ldB, dirB, show (2 : ℕ) ≠ 1 by decide, if_false, seedOf_blocksV hk P o sz jw c h]
  rw [dir_blocksV hk P o sz c h, pt_blocksV hk P o sz c h, pt_blocksV hk P o sz c h,
    selDirL_vecBits hk o sz jw c S hjw hχ]
  have hmap := ptMapL_vecBits hk o sz jw c S hjw hχ .dline
  simp only [tyNat] at hmap
  rw [hmap, lvpB_eq hk]
  simp only [LIDT.CL.accepts, Sample.question, Regs.sampleOf, Question.fmtOk, subtests,
    Bool.true_and, S.chi_π]
  rfl

end Copy

/-! ## Answers as blocks -/

section Answers

variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}

local notation "E" => shoupBinField k hk

/-- The blocks of an answer: its elements' bits. -/
def ansB (u : Ans P (shoupBinField k hk).carrier) : List BitStr := (elems (E) u).map (E).toBits

theorem ofFn_getD (l : List (E).carrier) {N : ℕ} (hN : l.length = N) :
    List.ofFn (fun r : Fin N => l.getD r 0) = l := by
  subst hN
  apply List.ext_getElem
  · simp
  · intro j _ h
    simp [List.getD_eq_getElem?_getD]

theorem elems_ofElems (t : PcpTy) (l : List (E).carrier) (hl : l.length = cnt P t) :
    elems (E) (ofElems (P := P) (E) t l) = l := by
  obtain ⟨i, τ⟩ := t
  unfold cnt at hl
  unfold ofElems
  split_ifs at hl ⊢ with hi
  · cases τ
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      rfl
    · exact ofFn_getD hk l hl
    · exact ofFn_getD hk l hl
  · cases τ
    · exact ofFn_getD hk l hl
    · change List.ofFn (fun r => l.getD (finProdFinEquiv (finProdFinEquiv.symm r)) 0) = l
      simp only [Equiv.apply_symm_apply]
      exact ofFn_getD hk l hl
    · change List.ofFn (fun r => l.getD (finProdFinEquiv (finProdFinEquiv.symm r)) 0) = l
      simp only [Equiv.apply_symm_apply]
      exact ofFn_getD hk l hl

theorem ansB_injective {t : PcpTy} {u v : Ans P (E).carrier} (hu : ansFmt t u = true)
    (hv : ansFmt t v = true) (h : ansB hk u = ansB hk v) : u = v := by
  rw [← ofElems_elems (E) hu, ← ofElems_elems (E) hv]
  congr 1
  have := congrArg (List.map (E).ofBits) h
  simpa only [ansB, List.map_map, Function.comp_def, (E).ofBits_toBits, List.map_id'] using this

theorem ansB_ofElems (t : PcpTy) (bs : List BitStr) (hl : bs.length = cnt P t)
    (hw : ∀ b ∈ bs, b.length = k) :
    ansB hk (ofElems (P := P) (E) t (bs.map (E).ofBits)) = bs := by
  rw [ansB, elems_ofElems hk t _ (by simp [hl]), List.map_map]
  conv_rhs => rw [← List.map_id bs]
  apply List.map_congr_left
  intro b hb
  exact shoupBinField_toBits_ofBits k hk b (hw b hb)

/-- A point answer of the first five copies is one block. -/
theorem ansB_val1 {i : Fin 6} (hi : (i : ℕ) < 5) {u : Ans P (E).carrier}
    (hu : ansFmt (i, .point) u = true) :
    ∃ av : Fin 1 → (E).carrier, u = .inl (.values av) ∧ ansB hk u = (E).vecBits av ∧
      val1 u = av 0 := by
  rcases u with (av | f | f) | (av | f | f) <;>
    simp [ansFmt, tyFmt, hi] at hu <;> try omega
  refine ⟨av, rfl, ?_, rfl⟩
  simp [ansB, elems, BinField.vecBits]

/-- A point answer of the sixth copy is its `m' + 6` blocks. -/
theorem ansB_val6 {i : Fin 6} (hi : (i : ℕ) = 5) {u : Ans P (E).carrier}
    (hu : ansFmt (i, .point) u = true) :
    ∃ av : Fin (P.m' + 6) → (E).carrier, u = .inr (.values av) ∧ ansB hk u = (E).vecBits av ∧
      vals6 u = av ∧ ∀ j, val6 j u = av j := by
  rcases u with (av | f | f) | (av | f | f) <;>
    simp [ansFmt, tyFmt, hi] at hu
  refine ⟨av, rfl, ?_, rfl, fun _ => rfl⟩
  simp [ansB, elems, BinField.vecBits]

theorem getD_vecBits {N : ℕ} (v : Fin N → (E).carrier) (j : Fin N) :
    ((E).vecBits v).getD j [] = (E).toBits (v j) := by
  simp [BinField.vecBits, List.getD_eq_getElem?_getD]

theorem getD_vecBits' {N : ℕ} (v : Fin N → (E).carrier) (j : ℕ) (hj : j < N) :
    ((E).vecBits v).getD j [] = (E).toBits (v ⟨j, hj⟩) :=
  getD_vecBits hk v ⟨j, hj⟩

theorem toBits_injective : Function.Injective (E).toBits := fun a b h => by
  simpa only [(E).ofBits_toBits] using congrArg (E).ofBits h

end Answers

/-! ## The atoms of the five steps, for a family -/

section Atoms

variable (F : PcpFamily) (n : ℕ)


/-- The number of coefficients of a polynomial of the sixth copy's line answers. -/
def width (m' : ℕ) (τ : LIDT.CL.Ty) : ℕ := if τ = .aline then dPcp + 1 else m' * dPcp + 1

theorem atom_val6_val1 {i i' : Fin 6} (hi : (i : ℕ) = 5) (hi' : (i' : ℕ) < 5)
    {u v : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier} (hu : ansFmt (i, .point) u = true)
    (hv : ansFmt (i', .point) v = true) (j : Fin ((F.par n).m' + 6)) :
    decide (val6 j u = val1 v) = decide ((ansB (F.hk n) u).getD j [] = (ansB (F.hk n) v).getD 0 []) := by
  obtain ⟨av, -, hua, -, hv6⟩ := ansB_val6 (F.hk n) hi hu
  obtain ⟨bv, -, hvb, hv1⟩ := ansB_val1 (F.hk n) hi' hv
  rw [hua, hvb, hv6, hv1, getD_vecBits (F.hk n) av j, getD_vecBits' (F.hk n) bv 0 one_pos]
  simp only [(toBits_injective (F.hk n)).eq_iff]
  rfl

theorem atom_val1_val6 {i i' : Fin 6} (hi : (i : ℕ) < 5) (hi' : (i' : ℕ) = 5)
    {u v : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier} (hu : ansFmt (i, .point) u = true)
    (hv : ansFmt (i', .point) v = true) (j : Fin ((F.par n).m' + 6)) :
    decide (val1 u = val6 j v) = decide ((ansB (F.hk n) u).getD 0 [] = (ansB (F.hk n) v).getD j []) := by
  obtain ⟨av, -, hua, hu1⟩ := ansB_val1 (F.hk n) hi hu
  obtain ⟨bv, -, hvb, -, hv6⟩ := ansB_val6 (F.hk n) hi' hv
  rw [hua, hvb, hv6, hu1, getD_vecBits' (F.hk n) av 0 one_pos, getD_vecBits (F.hk n) bv j]
  simp only [(toBits_injective (F.hk n)).eq_iff]
  rfl

theorem ofFn_one_vecBits {N : ℕ} (g : Fin 1 → Fin N → (fld (F.par n) (F.hk n)).carrier) :
    [(fld (F.par n) (F.hk n)).vecBits (g 0)] = List.ofFn fun j => (fld (F.par n) (F.hk n)).vecBits (g j) := by
  simp [List.ofFn_succ]

/-- **The low-degree subtest of a copy `c ≤ 5`**, on blocks. -/
theorem atom_ld1 (c : Fin 5) {τ' : LIDT.CL.Ty} (hτ' : τ' ≠ .point) {u v : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier}
    (hu : ansFmt (c.castSucc, .point) u = true) (hv : ansFmt (c.castSucc, τ') v = true)
    (x y : Coord (F.par n) → (fld (F.par n) (F.hk n)).carrier) :
    LIDT.CL.accepts (pow_dvd_card _ _ _ _ (F.m_eq n) (F.jm_le n))
      (q1 (F.sel n) c .point x) (q1 (F.sel n) c τ' y) (ans1 u) (ans1 v) =
      ldB (unary (F.par n).k) (F.desc n c.castSucc) (tyNat τ') (blocksV (F.hk n) (F.par n) x) (blocksV (F.hk n) (F.par n) y)
        [ansB (F.hk n) v] (ansB (F.hk n) u) := by
  have hc : ((c.castSucc : Fin 6) : ℕ) < 5 := c.isLt
  obtain ⟨av, rfl, hua, -⟩ := ansB_val1 (F.hk n) hc hu
  rw [hua, F.desc_lt n _ hc]
  simp only [q1, regs_eq, Fin.val_castSucc, ans1]
  cases τ' with
  | point => exact absurd rfl hτ'
  | aline =>
    rcases v with (bv | f | f) | (bv | f | f) <;> simp [ansFmt, tyFmt] at hv <;>
      (try (have := c.isLt; omega))
    have hvb : ansB (F.hk n) (.inl (.apolys f) : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier) = (fld (F.par n) (F.hk n)).vecBits (f 0) := by
      simp [ansB, elems, BinField.vecBits]
    rw [hvb, ofFn_one_vecBits]
    exact (ldB_aline (F.hk n) (F.par n) _ _ _ _ _ (F.jm_le n) (F.m_eq n) (F.sel n)
      (powSel_χ _ _ _ _ _ _) x y av f).symm
  | dline =>
    rcases v with (bv | f | f) | (bv | f | f) <;> simp [ansFmt, tyFmt] at hv <;>
      (try (have := c.isLt; omega))
    have hvb : ansB (F.hk n) (.inl (.dpolys f) : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier) = (fld (F.par n) (F.hk n)).vecBits (f 0) := by
      simp [ansB, elems, BinField.vecBits]
    rw [hvb, ofFn_one_vecBits]
    exact (ldB_dline (F.hk n) (F.par n) _ _ _ _ _ (F.jm_le n) (F.sel n)
      (powSel_χ _ _ _ _ _ _) x y av f).symm

/-- **The low-degree subtest of the sixth copy**, on blocks. -/
theorem atom_ld6 {i : Fin 6} (hi : (i : ℕ) = 5) {τ' : LIDT.CL.Ty} (hτ' : τ' ≠ .point)
    {u v : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier} (hu : ansFmt (i, .point) u = true)
    (hv : ansFmt (i, τ') v = true) (x y : Coord (F.par n) → (fld (F.par n) (F.hk n)).carrier) :
    LIDT.CL.accepts (pow_dvd_card _ _ _ _ (F.m'_eq n) (F.jm'_le n))
      (q6 (F.sel' n) .point x) (q6 (F.sel' n) τ' y) (ans6 u) (ans6 v) =
      ldB (unary (F.par n).k) (F.desc n 5) (tyNat τ') (blocksV (F.hk n) (F.par n) x) (blocksV (F.hk n) (F.par n) y)
        (chunks (width (F.par n).m' τ') ((F.par n).m' + 6) (ansB (F.hk n) v)) (ansB (F.hk n) u) := by
  obtain ⟨av, rfl, hua, -, -⟩ := ansB_val6 (F.hk n) hi hu
  rw [hua, F.desc_ge n 5 (by decide)]
  simp only [q6, regs6_eq, ans6]
  cases τ' with
  | point => exact absurd rfl hτ'
  | aline =>
    rcases v with (bv | f | f) | (bv | f | f) <;> simp [ansFmt, tyFmt, hi] at hv
    have hvb : chunks (width (F.par n).m' .aline) ((F.par n).m' + 6) (ansB (F.hk n) (.inr (.apolys f) :
        Ans (F.par n) (fld (F.par n) (F.hk n)).carrier)) = List.ofFn fun c => (fld (F.par n) (F.hk n)).vecBits (f c) := by
      simp only [ansB, elems, List.map_ofFn, width, if_true, Function.comp_def]
      simpa only [BinField.vecBits, List.map_ofFn, Function.comp_def] using
        chunks_ofFn _ _ fun c j => (fld (F.par n) (F.hk n)).toBits (f c j)
    rw [hvb]
    exact (ldB_aline (F.hk n) (F.par n) _ _ _ _ _ (F.jm'_le n) (F.m'_eq n) (F.sel' n)
      (powSel_χ _ _ _ _ _ _) x y av f).symm
  | dline =>
    rcases v with (bv | f | f) | (bv | f | f) <;> simp [ansFmt, tyFmt, hi] at hv
    have hvb : chunks (width (F.par n).m' .dline) ((F.par n).m' + 6) (ansB (F.hk n) (.inr (.dpolys f) :
        Ans (F.par n) (fld (F.par n) (F.hk n)).carrier)) = List.ofFn fun c => (fld (F.par n) (F.hk n)).vecBits (f c) := by
      simp only [ansB, elems, List.map_ofFn, width, reduceCtorEq, if_false, Function.comp_def]
      simpa only [BinField.vecBits, List.map_ofFn, Function.comp_def] using
        chunks_ofFn _ _ fun c j => (fld (F.par n) (F.hk n)).toBits (f c j)
    rw [hvb]
    exact (ldB_dline (F.hk n) (F.par n) _ _ _ _ _ (F.jm'_le n) (F.sel' n)
      (powSel_χ _ _ _ _ _ _) x y av f).symm

end Atoms

/-! ## The five steps, planned by the types -/

/-- The comparison of two answer blocks a type pair asks for: step 2, an oracle's `Point_6`
component against an isolated player's `Point_v`, or step 4, a copy's point against the
oracle's `Point_6` component. -/
def eqPlan (p q : ArTy) : Option (ℕ × ℕ) :=
  match p.1, q.1 with
  | .oracle, .alice =>
    if (p.2.1 : ℕ) = 5 ∧ p.2.2 = .point ∧ (q.2.1 : ℕ) = 0 ∧ q.2.2 = .point then some (0, 0)
    else none
  | .oracle, .bob =>
    if (p.2.1 : ℕ) = 5 ∧ p.2.2 = .point ∧ (q.2.1 : ℕ) = 1 ∧ q.2.2 = .point then some (1, 0)
    else none
  | .oracle, .oracle =>
    if 2 ≤ (p.2.1 : ℕ) ∧ (p.2.1 : ℕ) < 5 ∧ p.2.2 = .point ∧ (q.2.1 : ℕ) = 5 ∧ q.2.2 = .point then
      some (0, p.2.1)
    else none
  | _, _ => none

/-- The low-degree subtest a type pair asks for: the copy, and whether the line answers carry
`m' + 6` codewords (the sixth copy). -/
def ldPlan (p q : ArTy) : Option (ℕ × Bool) :=
  match p.1, q.1 with
  | .alice, .alice =>
    if (p.2.1 : ℕ) = 0 ∧ (q.2.1 : ℕ) = 0 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then some (0, false)
    else none
  | .bob, .bob =>
    if (p.2.1 : ℕ) = 1 ∧ (q.2.1 : ℕ) = 1 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then some (1, false)
    else none
  | .oracle, .oracle =>
    if 2 ≤ (p.2.1 : ℕ) ∧ (p.2.1 : ℕ) < 5 ∧ q.2.1 = p.2.1 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then
      some (p.2.1, false)
    else if (p.2.1 : ℕ) = 5 ∧ (q.2.1 : ℕ) = 5 ∧ p.2.2 = .point ∧ q.2.2 ≠ .point then
      some (5, true)
    else none
  | _, _ => none

/-- Whether a type asks for the game check: an oracle's `Point_6`. -/
def chkPlan (p : ArTy) : Bool := decide (p.1 = .oracle ∧ (p.2.1 : ℕ) = 5 ∧ p.2.2 = .point)

/-- **One side of the five steps, on blocks**, as its type pair plans it. `chk` is the game
check's verdict. -/
def sideB (kU m'U : Unary) (descs : List Desc) (chk : Bool) (p q : ArTy) (X Y : Blocks)
    (A B : List BitStr) : Bool :=
  (match eqPlan p q with
    | some (α, β) => decide (A.getD α [] = B.getD β [])
    | none => true) &&
  (match ldPlan p q with
    | some (c, ch) => ldB kU (descs.getD c default) (tyNat q.2.2) X Y
        (if ch then chunks (width m'U.length q.2.2) (m'U.length + 6) B else [B]) A
    | none => true) &&
  (!chkPlan p || chk)

section SideEq

theorem chk_eq {C : Prop} [Decidable C] {chk c : Bool} (h : C → chk = c) :
    (!decide C || chk) = (if C then c else true) := by
  by_cases hC : C <;> simp [hC, h]

variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)

theorem getD_desc (c : Fin 6) : (List.ofFn (F.desc n)).getD c default = F.desc n c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem sideB_eq (p q : Q (F.par n) (Fq (F.par n) (F.hk n)) X)
    (u v : Ans (F.par n) (Fq (F.par n) (F.hk n)))
    (hu : ansFmt p.1.2 u = true) (hv : ansFmt q.1.2 v = true) (chk : Bool)
    (hchk : chkPlan p.1 = true → chk = check p.2.1 ((regs6 (F.par n)).ptOf p.2.2) (vals6 u)) :
    sideB (unary (F.par n).k) (unary (F.par n).m') (List.ofFn (F.desc n)) chk p.1 q.1
        (blocksV (F.hk n) (F.par n) p.2.2) (blocksV (F.hk n) (F.par n) q.2.2)
        (ansB (F.hk n) u) (ansB (F.hk n) v) =
      side (F.sel n) (F.sel' n) check p q u v := by
  obtain ⟨⟨r, i, τ⟩, x, xv⟩ := p
  obtain ⟨⟨r', i', τ'⟩, y, yv⟩ := q
  simp only at hu hv hchk ⊢
  have hchk' := fun h => hchk (by simpa [chkPlan] using h)
  cases r <;> cases r' <;> simp only [sideB, side, eqPlan, ldPlan, chkPlan, roleIdx] at hchk' ⊢ <;>
    simp only [reduceCtorEq, and_false, false_and, if_false, true_and, and_true, if_true,
      Bool.true_and, Bool.and_true, Fin.val_zero, Fin.val_one, Fin.isValue,
      decide_false, Bool.not_false, Bool.true_or, zero_ne_one, one_ne_zero, and_self,
      IsEmpty.forall_iff] at hchk' ⊢
  · -- two oracles
    rw [chk_eq hchk']
    have hassoc : ∀ a b c d : Bool, (a && b && c && d) = (a && (b && c) && d) := by decide
    conv_rhs => rw [hassoc]
    congr 2
    · split_ifs with hC
      · obtain ⟨-, hi5, rfl, hi', rfl⟩ := hC
        exact (atom_val1_val6 F n hi5 hi' hu hv ⟨i, by omega⟩).symm
      · rfl
    · split_ifs with hB hC hC
      · exact absurd hC.1 (by omega)
      · obtain ⟨-, hi5, hii, rfl, hτ'⟩ := hB
        rw [hii] at hv
        have hi : i = (⟨i, hi5⟩ : Fin 5).castSucc := Fin.ext rfl
        rw [hi] at hu hv
        have := atom_ld1 F n ⟨i, hi5⟩ hτ' hu hv xv yv
        simp only [Bool.and_true, if_false, Bool.false_eq_true]
        rw [this, ← hi, getD_desc]
      · obtain ⟨hi5, hi5', rfl, hτ'⟩ := hC
        have hii : i' = i := Fin.ext (by omega)
        subst hii
        have := atom_ld6 F n hi5 hτ' hu hv xv yv
        simp only [Bool.true_and, if_true]
        rw [this, length_unary]
        exact congrArg (fun d => ldB _ d _ _ _ _ _) (getD_desc F n 5)
      · rfl
  · -- the oracle against Alice
    rw [chk_eq hchk']
    congr 1
    split_ifs with hC
    · obtain ⟨hi5, rfl, hi', rfl⟩ := hC
      exact (atom_val6_val1 F n hi5 (by omega) hu hv ⟨0, by omega⟩).symm
    · rfl
  · -- the oracle against Bob
    rw [chk_eq hchk']
    congr 1
    split_ifs with hC
    · obtain ⟨hi5, rfl, hi', rfl⟩ := hC
      exact (atom_val6_val1 F n hi5 (by omega) hu hv ⟨1, by omega⟩).symm
    · rfl
  · -- Alice against Alice
    split_ifs with hC
    · obtain ⟨hi, hi', rfl, hτ'⟩ := hC
      have e : i = (0 : Fin 5).castSucc := Fin.ext hi
      have e' : i' = (0 : Fin 5).castSucc := Fin.ext hi'
      subst e e'
      rw [atom_ld1 F n 0 hτ' hu hv xv yv]
      simp [List.getD_eq_getElem?_getD]
    · rfl
  · -- Bob against Bob
    split_ifs with hC
    · obtain ⟨hi, hi', rfl, hτ'⟩ := hC
      have e : i = (1 : Fin 5).castSucc := Fin.ext hi
      have e' : i' = (1 : Fin 5).castSucc := Fin.ext hi'
      subst e e'
      rw [atom_ld1 F n 1 hτ' hu hv xv yv]
      simp [List.getD_eq_getElem?_getD]
    · rfl

end SideEq

/-! ## Parsing, and the predicate -/

/-- The number of field elements of an answer of the type `t`, from `m` and `m'` (`cnt`). -/
def cntB (m m' : ℕ) (t : PcpTy) : ℕ :=
  if (t.1 : ℕ) < 5 then
    match t.2 with
    | .point => 1
    | .aline => dPcp + 1
    | .dline => m * dPcp + 1
  else
    match t.2 with
    | .point => m' + 6
    | .aline => (m' + 6) * (dPcp + 1)
    | .dline => (m' + 6) * (m' * dPcp + 1)

theorem cnt_eq (P : PcpParams) (t : PcpTy) : cnt P t = cntB P.m P.m' t := rfl

/-- **The bounded parse into blocks**: a serialized list of `c` blocks of `k` bits. -/
def parseB (k c : ℕ) (s : BitStr) : Option (List BitStr) :=
  match (decode (Data.parse s) : Option (List BitStr)) with
  | some bs => if bs.length = c ∧ ∀ b ∈ bs, b.length = k then some bs else none
  | none => none

theorem parse_eq {k : ℕ} (E : BinField k) {P : PcpParams} (t : PcpTy) (s : BitStr) :
    parse (P := P) E t s = (parseB k (cnt P t) s).map fun bs => ofElems E t (bs.map E.ofBits) := by
  unfold parse parseB
  rcases (decode (Data.parse s) : Option (List BitStr)) with _ | bs
  · rfl
  · dsimp only
    split_ifs <;> rfl

theorem parseB_spec {k c : ℕ} {s : BitStr} {bs : List BitStr} (h : parseB k c s = some bs) :
    bs.length = c ∧ ∀ b ∈ bs, b.length = k := by
  unfold parseB at h
  split at h
  · split_ifs at h with hc
    cases h
    exact hc
  · cases h

/-- **The answer-reduced predicate on blocks**: the equal-type check and both sides. -/
def acceptsB (kU m'U : Unary) (descs : List Desc) (chkP chkQ : Bool) (p q : ArTy)
    (X Y : Blocks) (A B : List BitStr) : Bool :=
  (if p = q then decide (A = B) else true) &&
  sideB kU m'U descs chkP p q X Y A B && sideB kU m'U descs chkQ q p Y X B A

/-- **The typed predicate on bits**: parse both answers into blocks, then decide. -/
def verdictB (kU m'U : Unary) (descs : List Desc) (chkP chkQ : Bool) (p q : ArTy)
    (X Y : Blocks) (a b : BitStr) : Bool :=
  match parseB kU.length (cntB (descs.getD 0 default).2.1.length m'U.length p.2) a,
      parseB kU.length (cntB (descs.getD 0 default).2.1.length m'U.length q.2) b with
  | some A, some B => acceptsB kU m'U descs chkP chkQ p q X Y A B
  | _, _ => false

section VerdictEq

variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)

theorem desc_zero_sz : ((List.ofFn (F.desc n)).getD 0 default).2.1.length = (F.par n).m := by
  rw [show (0 : ℕ) = ((0 : Fin 6) : ℕ) from rfl, getD_desc, F.desc_lt n 0 (by decide)]
  exact length_unary _

/-- **The typed predicate is the predicate on bits**: for questions whose PCP halves have the
blocks `blocksV`, and game-check verdicts `chkP`, `chkQ` that are the game check wherever a type
asks for it. -/
theorem verdictB_eq (p q : Q (F.par n) (Fq (F.par n) (F.hk n)) X) (a b : BitStr)
    (chkP chkQ : Bool)
    (hP : ∀ u, parse (fld (F.par n) (F.hk n)) p.1.2 a = some u → chkPlan p.1 = true →
      chkP = check p.2.1 ((regs6 (F.par n)).ptOf p.2.2) (vals6 u))
    (hQ : ∀ v, parse (fld (F.par n) (F.hk n)) q.1.2 b = some v → chkPlan q.1 = true →
      chkQ = check q.2.1 ((regs6 (F.par n)).ptOf q.2.2) (vals6 v)) :
    verdictB (unary (F.par n).k) (unary (F.par n).m') (List.ofFn (F.desc n)) chkP chkQ p.1 q.1
        (blocksV (F.hk n) (F.par n) p.2.2) (blocksV (F.hk n) (F.par n) q.2.2) a b =
      match parse (fld (F.par n) (F.hk n)) p.1.2 a, parse (fld (F.par n) (F.hk n)) q.1.2 b with
      | some u, some v => accepts (F.sel n) (F.sel' n) check p q u v
      | _, _ => false := by
  simp only [verdictB, desc_zero_sz, length_unary, ← cnt_eq, parse_eq]
  rcases hA : parseB (F.par n).k (cnt (F.par n) p.1.2) a with _ | A <;>
    rcases hB : parseB (F.par n).k (cnt (F.par n) q.1.2) b with _ | B <;>
    simp only [Option.map_none, Option.map_some]
  obtain ⟨hAl, hAw⟩ := parseB_spec hA
  obtain ⟨hBl, hBw⟩ := parseB_spec hB
  set u := ofElems (P := F.par n) (fld (F.par n) (F.hk n)) p.1.2
    (A.map (fld (F.par n) (F.hk n)).ofBits)
  set v := ofElems (P := F.par n) (fld (F.par n) (F.hk n)) q.1.2
    (B.map (fld (F.par n) (F.hk n)).ofBits)
  have hpu : parse (fld (F.par n) (F.hk n)) p.1.2 a = some u := by rw [parse_eq, hA]; rfl
  have hqv : parse (fld (F.par n) (F.hk n)) q.1.2 b = some v := by rw [parse_eq, hB]; rfl
  have hu := ansFmt_of_parse _ hpu
  have hv := ansFmt_of_parse _ hqv
  have hAu : ansB (F.hk n) u = A := ansB_ofElems (F.hk n) _ A hAl hAw
  have hBv : ansB (F.hk n) v = B := ansB_ofElems (F.hk n) _ B hBl hBw
  rw [← hAu, ← hBv, acceptsB, accepts, hu, hv, Bool.true_and, Bool.true_and,
    sideB_eq F n check p q u v hu hv chkP (hP u hpu),
    sideB_eq F n check q p v u hv hu chkQ (hQ v hqv)]
  congr 2
  split_ifs with he
  · have he' : p.1.2 = q.1.2 := congrArg Prod.snd he
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      exact ansB_injective (F.hk n) hu (he' ▸ hv) h
    · intro h
      rw [h]
  · rfl

end VerdictEq

end MIPRE.AnswerReduction

end
