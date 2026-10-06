/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.Intro.PauliHide
public import MIPRE.Foundations.Introspection.AuxiliaryMaskProgram
public import MIPRE.Foundations.Introspection.BasisProg
public import MIPRE.Foundations.Introspection.BinaryBlockProg
public import MIPRE.Foundations.Introspection.FieldAnswerParserProg
public import MIPRE.Foundations.LowDegree.BinaryComponentsProg
public import MIPRE.Foundations.LowDegree.BinaryMatrixSolve

@[expose] public section

/-!
# The first hiding edge's constraints as polynomial-time programs

`PauliHide.pauliHideCons` and `pauliHideConsRev` are lists of register forms
`∑ wᵣ ((Π a)ᵣ + xᵣ) = 0`, for `w` the masked generators `proj S z` and the unit vectors off `S`,
with `Π a` the kernel's register of the Pauli answer and `x` a register of the Hide answer. This
file computes them by programs (`Cost.PolyTimeFun`), from the kernel's parameter triple, the mask
of `S = P.factorOfPrefix 0 0` and the generators' bits; the mask and the generators are inputs,
computed elsewhere from the sampler.

The coefficient of a Hide bit is a coordinate of `w`. The coefficient of the Pauli bit `i` of
block `bb` is `∑_s C i s · w (bb, s)`, with `C i s` the `s`-th self-dual coordinate of the `i`-th
canonical (Shoup) basis element `bsh i` (`dot_pauliXProj_unitV`): `Π` expands each field element
of the answer in the self-dual basis. So with the rows `C i ·` computed once (`ctxProg`, by the
kernel's basis conversion `BasisProgram.toSelfDualRowsProg` on the identity rows), the Pauli
coefficients are those rows applied to each block of `w` (`coefProg`, `coefProg_eq`).

* `toCon_hideCon`, `toCon_hideCon_seg`: the constraint vector of a register form, position by
  position, and by segments of `Q` bits when the two registers sit at multiples of `Q`;
* `hideChecks_toCon`: `hideChecks` as such register forms;
* `pauliHideProg_eq`, `pauliHideRevProg_eq`: **the programs compute the constraint lists**,
  exactly, for every `P` and every list of generators.
-/

noncomputable section

namespace MIPRE.Tailored.Intro.PauliHideProg

open Cost MIPRE.SAT MIPRE.LowDegree MIPRE.QLD MIPRE.Introspection
open MIPRE.Introspection.FieldTableProgram MIPRE.Tailored.Intro.PauliCons
open MIPRE.Tailored.Intro.PauliHide

/-! ## Unit vectors -/

/-- The unit vector at `l`, in the form `LinCheck.toCon` evaluates. -/
abbrev unitV {N : ℕ} (l : Fin N) : Fin N → ZMod 2 := fun i => if l = i then 1 else 0

theorem getv_unitV {N : ℕ} (l : Fin N) (p : ℕ) :
    getv N p (unitV l) = if p = l then 1 else 0 := by
  unfold getv
  by_cases h : p < N
  · rw [dite_eq_left h]
    change (if l = ⟨p, h⟩ then (1 : ZMod 2) else 0) = _
    by_cases hp : p = l
    · rw [ite_eq_left (Fin.ext hp.symm), ite_eq_left hp]
    · rw [ite_eq_right (fun he => hp (by rw [he])), ite_eq_right hp]
  · rw [dite_eq_right h, ite_eq_right (by omega)]
    rfl

/-- The block reading of `i·k` bits: `bb·k ≤ i₀ + k·bb₀ < bb·k + k` exactly when `bb = bb₀`. -/
theorem block_iff {k i₀ bb bb₀ : ℕ} (hi : i₀ < k) :
    (bb * k ≤ i₀ + k * bb₀ ∧ i₀ + k * bb₀ < bb * k + k) ↔ bb = bb₀ := by
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (bb + 1) * k ≤ bb₀ * k := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at this
      rw [Nat.mul_comm k] at h2
      omega
    · have : (bb₀ + 1) * k ≤ bb * k := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at this
      rw [Nat.mul_comm k] at h1
      omega
  · rintro rfl
    rw [Nat.mul_comm k]
    omega

/-- The register coefficients of a register form. -/
theorem dot_regAt_unitV {N s : ℕ} (o : ℕ) (w : Fin s → ZMod 2) (l : Fin N) :
    ∑ r, w r * regAt N o s (unitV l) r =
      if h : o ≤ l ∧ (l : ℕ) < o + s then w ⟨l - o, by omega⟩ else 0 := by
  simp only [regAt, LinearMap.pi_apply, getv_unitV, mul_ite, mul_one, mul_zero]
  by_cases h : o ≤ (l : ℕ) ∧ (l : ℕ) < o + s
  · rw [dite_eq_left h, Finset.sum_eq_single ⟨l - o, by omega⟩]
    · rw [ite_eq_left (by simp only; omega)]
    · intro r _ hr
      rw [ite_eq_right]
      intro he
      exact hr (Fin.ext (by simp only; omega))
    · simp
  · rw [dite_eq_right h]
    exact Finset.sum_eq_zero fun r _ => ite_eq_right (by omega)

/-- A window at `a·Q` read at the position `t + Q·σ` of the `σ`-th segment. -/
theorem seg_dite {Q : ℕ} (p σ a : ℕ) (t : Fin Q) (f : Fin Q → ZMod 2) (hp : p = t + Q * σ) :
    (if h : a * Q ≤ p ∧ p < a * Q + Q then
        f ⟨p - a * Q, by omega⟩ else 0) = if σ = a then f t else 0 := by
  subst hp
  by_cases hσ : σ = a
  · subst hσ
    have h : σ * Q ≤ (t : ℕ) + Q * σ ∧ (t : ℕ) + Q * σ < σ * Q + Q := by
      rw [Nat.mul_comm Q]; omega
    rw [dite_eq_left h, ite_eq_left rfl]
    congr 1
    ext
    simp only
    rw [Nat.mul_comm Q]; omega
  · rw [ite_eq_right hσ, dite_eq_right]
    intro h
    exact hσ ((block_iff t.2).1 h).symm

variable (k : ℕ) (hk : 1 ≤ k)

/-- The `i`-th element of the canonical (Shoup polynomial) basis. -/
def bsh (i : Fin k) : (shoupBinField k hk).carrier :=
  (shoupCoordinateEquiv k hk).symm (Pi.single i 1)

theorem fldAt_unitV {N : ℕ} (o : ℕ) (l : Fin N) :
    fldAt k hk N o (unitV l) =
      if h : o ≤ l ∧ (l : ℕ) < o + k then bsh k hk ⟨l - o, by omega⟩ else 0 := by
  apply (shoupCoordinateEquiv k hk).injective
  funext i
  simp only [fldAt, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, LinearMap.pi_apply, getv_unitV]
  by_cases h : o ≤ (l : ℕ) ∧ (l : ℕ) < o + k
  · rw [dite_eq_left h]
    simp only [bsh, LinearEquiv.apply_symm_apply, Pi.single_apply, Fin.ext_iff]
    by_cases hi : (i : ℕ) = l - o
    · rw [ite_eq_left hi, ite_eq_left (by omega)]
    · rw [ite_eq_right hi, ite_eq_right (by omega)]
  · rw [dite_eq_right h, map_zero, Pi.zero_apply, ite_eq_right (by omega)]

variable [NeZero k] (hodd : Odd k) (j : ℕ)

/-- The self-dual coordinates of the canonical basis: `C i s`. -/
def cm (i s : Fin k) : ZMod 2 := (shoupSelfDualNormalBasis k hk hodd).equivFun (bsh k hk i) s

/-- The coefficients of the Pauli bits in `∑ wᵣ (Π a)ᵣ`: at block `bb`, bit `i`,
`∑_s C i s · w (bb, s)`. -/
def coef (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) : Fin (2 ^ 2 ^ j * k) → ZMod 2 := fun r =>
  ∑ s : Fin k, cm k hk hodd (finProdFinEquiv.symm r).2 s *
    w (finProdFinEquiv ((finProdFinEquiv.symm r).1, s))

/-- **The Pauli coefficients of a register form.** -/
theorem dot_pauliXProj_unitV {N : ℕ} (o : ℕ) (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) (l : Fin N) :
    ∑ r, w r * pauliXProj k hk hodd j N o (unitV l) r =
      if h : o ≤ l ∧ (l : ℕ) < o + 2 ^ 2 ^ j * k then coef k hk hodd j w ⟨l - o, by omega⟩
      else 0 := by
  rw [← (PauliFullAnswerProgram.registerNumbering (2 ^ j) k).sum_comp, Fintype.sum_prod_type]
  simp only [pauliXProj, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.coe_proj, Function.eval, Equiv.symm_apply_apply]
  rw [← (cubeEnumeration (2 ^ j)).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, PauliFullAnswerProgram.registerNumbering, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map, Equiv.apply_symm_apply, Equiv.refl_apply, fldAt_unitV]
  split_ifs with hl
  · set r : Fin (2 ^ 2 ^ j * k) := ⟨l - o, by omega⟩
    obtain ⟨⟨bb₀, i₀⟩, hr⟩ : ∃ p, finProdFinEquiv p = r := ⟨_, finProdFinEquiv.apply_symm_apply r⟩
    have hrv : (l : ℕ) - o = i₀ + k * bb₀ := by
      have := congrArg Fin.val hr
      simp only [finProdFinEquiv, Equiv.coe_fn_mk] at this
      simp only [r] at this
      omega
    rw [Finset.sum_eq_single bb₀]
    · have hsymm : finProdFinEquiv.symm r = (bb₀, i₀) := by rw [← hr]; simp
      simp only [coef, hsymm]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hc : o + (bb₀ : ℕ) * k ≤ l ∧ (l : ℕ) < o + bb₀ * k + k := by
        have := (block_iff (bb := bb₀) (bb₀ := bb₀) i₀.2).2 rfl
        omega
      rw [dite_eq_left hc, mul_comm]
      congr 1
      unfold cm
      have hi : ∀ hlt : (l : ℕ) - (o + bb₀ * k) < k,
          (⟨(l : ℕ) - (o + bb₀ * k), hlt⟩ : Fin k) = i₀ :=
        fun _ => Fin.ext (by simp only; rw [Nat.mul_comm k] at hrv; omega)
      rw [hi]
    · intro bb _ hbb
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [dite_eq_right]
      · simp
      · intro hc
        apply hbb
        exact Fin.ext ((block_iff i₀.2).1 ⟨by omega, by omega⟩)
    · simp
  · refine Finset.sum_eq_zero fun bb _ => Finset.sum_eq_zero fun s _ => ?_
    rw [dite_eq_right]
    · simp
    · intro hc
      have : (bb : ℕ) * k + k ≤ 2 ^ 2 ^ j * k := by
        have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt bb.2)
        rwa [Nat.succ_mul] at this
      omega

/-- The register form `∑ wᵣ ((Π a)ᵣ + xᵣ)`, the Pauli register at `oP`, the other at `oR`. -/
def hideCon (N oP oR : ℕ) (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) : LinCheck N :=
  ⟨dotForm w ∘ₗ (pauliXProj k hk hodd j N oP + regAt N oR (2 ^ 2 ^ j * k)), 0⟩

/-- **The constraint vector of a register form**, position by position. -/
theorem toCon_hideCon (N oP oR : ℕ) (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) :
    (hideCon k hk hodd j N oP oR w).toCon =
      List.ofFn (fun l : Fin N => BinaryLinear.bit
        ((if h : oP ≤ l ∧ (l : ℕ) < oP + 2 ^ 2 ^ j * k then
            coef k hk hodd j w ⟨l - oP, by omega⟩ else 0) +
          (if h : oR ≤ l ∧ (l : ℕ) < oR + 2 ^ 2 ^ j * k then w ⟨l - oR, by omega⟩ else 0))) ++
        [false] := by
  unfold LinCheck.toCon
  congr 1
  apply congrArg List.ofFn
  funext l
  change BinaryLinear.bit (∑ i, w i * ((pauliXProj k hk hodd j N oP (unitV l) +
    regAt N oR (2 ^ 2 ^ j * k) (unitV l) : Fin (2 ^ 2 ^ j * k) → ZMod 2) i)) = _
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, dot_pauliXProj_unitV]
  rw [dot_regAt_unitV (N := N) (s := 2 ^ 2 ^ j * k) oR w l]

/-- **The constraint vector of a register form, by segments of `Q` bits**: the Pauli register
in segment `a`, the other in segment `b`. -/
theorem toCon_hideCon_seg (a b : ℕ) (hab : a ≠ b) (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) :
    (hideCon k hk hodd j (4 * (2 ^ 2 ^ j * k)) (a * (2 ^ 2 ^ j * k)) (b * (2 ^ 2 ^ j * k))
        w).toCon =
      (List.ofFn fun σ : Fin 4 =>
        if (σ : ℕ) = a then CL.toBits (coef k hk hodd j w)
        else if (σ : ℕ) = b then CL.toBits w
        else List.replicate (2 ^ 2 ^ j * k) false).flatten ++ [false] := by
  rw [toCon_hideCon, CL.ofFn_eq_flatten_blocks]
  congr 2
  apply congrArg List.ofFn
  funext σ
  have hv : ∀ t : Fin (2 ^ 2 ^ j * k),
      ((finProdFinEquiv (σ, t) : Fin (4 * (2 ^ 2 ^ j * k))) : ℕ) = t + 2 ^ 2 ^ j * k * σ :=
    fun t => rfl
  have hr : (if (σ : ℕ) = a then CL.toBits (coef k hk hodd j w)
      else if (σ : ℕ) = b then CL.toBits w else List.replicate (2 ^ 2 ^ j * k) false) =
      List.ofFn fun t : Fin (2 ^ 2 ^ j * k) => BinaryLinear.bit
        ((if (σ : ℕ) = a then coef k hk hodd j w t else 0) + if (σ : ℕ) = b then w t else 0) := by
    by_cases ha : (σ : ℕ) = a
    · have hb : (σ : ℕ) ≠ b := by omega
      simp [ha, hab, CL.toBits, BinaryLinear.bit]
    · by_cases hb : (σ : ℕ) = b
      · simp [hb, Ne.symm hab, CL.toBits, BinaryLinear.bit]
      · simp [ha, hb, BinaryLinear.bit, List.ofFn_const]
  rw [hr]
  apply congrArg List.ofFn
  funext t
  rw [seg_dite _ (σ : ℕ) a t (coef k hk hodd j w) (hv t), seg_dite _ (σ : ℕ) b t w (hv t)]

/-! ## The constraints of `hideChecks` as register forms -/

theorem proj_eq_dotForm {s : ℕ} (i : Fin s) :
    (LinearMap.proj i : (Fin s → ZMod 2) →ₗ[ZMod 2] ZMod 2) = dotForm (Pi.single i 1) := by
  ext x
  simp [dotForm_apply, Pi.single_apply, @eq_comm _ i]

theorem flatten_map_ite {α β : Type*} (l : List α) (p : α → Bool) (g : α → β) :
    (l.map fun x => if p x then [] else [g x]).flatten = (l.filter fun x => !p x).map g := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : p x <;> simp [h, ih]

/-- **`hideChecks` by segments**: the register forms of `hideChecks` at offsets that are
multiples of `Q`. -/
theorem hideChecks_toCon {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) (oP oH a b c : ℕ)
    (hoP : oP = a * (2 ^ 2 ^ j * k)) (hb' : oH + 2 ^ 2 ^ j * k = b * (2 ^ 2 ^ j * k))
    (hc' : oH + 2 * (2 ^ 2 ^ j * k) = c * (2 ^ 2 ^ j * k)) :
    (hideChecks k hk hodd j (4 * (2 ^ 2 ^ j * k)) oP oH P gens).map LinCheck.toCon =
      (gens.map fun z => (hideCon k hk hodd j (4 * (2 ^ 2 ^ j * k)) (a * (2 ^ 2 ^ j * k))
          (b * (2 ^ 2 ^ j * k)) (CL.proj (P.factorOfPrefix 0 0) z)).toCon) ++
        (((List.finRange (2 ^ 2 ^ j * k)).filter fun i => decide (i ∉ P.factorOfPrefix 0 0)).map
          fun i => (hideCon k hk hodd j (4 * (2 ^ 2 ^ j * k)) (a * (2 ^ 2 ^ j * k))
            (c * (2 ^ 2 ^ j * k)) (Pi.single i 1)).toCon) := by
  subst hoP
  simp only [hideChecks, List.map_append, List.map_map, hb', hc']
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, hideCon, proj_eq_dotForm]

/-! ## The programs -/

/-- The data the coefficient programs share: the self-dual coordinate rows of the canonical
basis, `k` and `2^j` in unary. -/
abbrev Ctx : Type := List BitStr × Unary × Unary

/-- The shared data, from the kernel's parameter triple. -/
def ctxProg : PolyTimeFun PauliSamplerParameters.Parameters Ctx :=
  (BasisProgram.toSelfDualRowsProg.comp
      (PolyTimeFun.fst.pair (BinaryLinear.identityBitsProg.comp PolyTimeFun.fst))).pair
    (PolyTimeFun.fst.pair (PolyTimeFun.snd.comp PolyTimeFun.snd))

/-- The coefficients of the Pauli bits of a register form `w`: block by block, the coordinate
rows applied to the block of `w`. -/
def coefProg : PolyTimeFun (BitStr × Ctx) BitStr :=
  BinaryBlock.flattenProg.comp ((PolyTimeFun.mapWith (BinaryLinear.applyBitsProg.comp
      (PolyTimeFun.snd.pair PolyTimeFun.fst))).comp
    ((FieldAnswerParser.rowsProg.comp
      ((FieldAnswerParser.scalePowerOfTwoProg.comp ((PolyTimeFun.const 1).pair
          (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))).pair
        ((PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)).pair
          PolyTimeFun.fst))).pair (PolyTimeFun.fst.comp PolyTimeFun.snd)))

/-- `Q` zeros, `Q` the length of the register form. -/
def zerosProg : PolyTimeFun (BitStr × Ctx) BitStr :=
  PolyTimeFun.replicate.comp ((PolyTimeFun.length.comp PolyTimeFun.fst).pair
    (PolyTimeFun.const false))

/-- The constraint of a register form: four segments of `Q` bits, the Pauli coefficients in
segment `a`, the form in segment `b`, zeros elsewhere, then `J`'s coefficient `0`. -/
def segProg (a b : ℕ) : PolyTimeFun (BitStr × Ctx) BitStr :=
  PolyTimeFun.append.comp ((BinaryBlock.flattenProg.comp (PolyTimeFun.listOf (List.ofFn
    fun σ : Fin 4 => if (σ : ℕ) = a then coefProg else if (σ : ℕ) = b then PolyTimeFun.fst
      else zerosProg))).pair (PolyTimeFun.const [false]))

/-- The input of the hiding programs: parameters, the mask of `S`, the generators. -/
abbrev HideInput : Type := PauliSamplerParameters.Parameters × BitStr × List BitStr

/-- The constraints of the generators. -/
def genFamily (a b : ℕ) : PolyTimeFun HideInput (List BitStr) :=
  (PolyTimeFun.mapWith ((segProg a b).comp ((AuxiliaryBits.mask.comp
      ((PolyTimeFun.fst.comp PolyTimeFun.snd).pair PolyTimeFun.fst)).pair
      (PolyTimeFun.snd.comp PolyTimeFun.snd)))).comp
    ((PolyTimeFun.snd.comp PolyTimeFun.snd).pair
      ((PolyTimeFun.fst.comp PolyTimeFun.snd).pair (ctxProg.comp PolyTimeFun.fst)))

/-- The constraints of the coordinates off the mask. -/
def offFamily (a c : ℕ) : PolyTimeFun HideInput (List BitStr) :=
  BinaryLinear.flattenBitsProg.comp ((PolyTimeFun.mapWith (PolyTimeFun.ite
      (PolyTimeFun.fst.comp PolyTimeFun.fst) (PolyTimeFun.const [])
      (PolyTimeFun.cons ((segProg a c).comp
        ((PolyTimeFun.snd.comp PolyTimeFun.fst).pair PolyTimeFun.snd))
        (PolyTimeFun.const [])))).comp
    ((PolyTimeFun.zip.comp ((PolyTimeFun.fst.comp PolyTimeFun.snd).pair
      (BinaryLinear.identityBitsProg.comp
        (PolyTimeFun.length.comp (PolyTimeFun.fst.comp PolyTimeFun.snd))))).pair
      (ctxProg.comp PolyTimeFun.fst)))

/-- **The first hiding edge's constraints, Pauli answer first, as a program.** -/
def pauliHideProg : PolyTimeFun HideInput (List BitStr) :=
  PolyTimeFun.append.comp ((genFamily 0 2).pair (offFamily 0 3))

/-- **The first hiding edge's constraints, Hide answer first, as a program.** -/
def pauliHideRevProg : PolyTimeFun HideInput (List BitStr) :=
  PolyTimeFun.append.comp ((genFamily 3 1).pair (offFamily 3 2))

/-! ## Correctness of the programs -/

omit [NeZero k] in
/-- The canonical bits of a field element are its coordinate vector. -/
theorem toBits_eq_vectorBits (x : (shoupBinField k hk).carrier) :
    (shoupBinField k hk).toBits x = BinaryLinear.vectorBits (shoupCoordinateEquiv k hk x) := by
  rw [shoupCoordinateEquiv_apply,
    BinaryLinear.vectorBits_vectorValue k _ ((shoupBinField k hk).length_toBits x)]

omit [NeZero k] in
theorem identityBits_eq :
    BinaryLinear.identityBits k = (shoupBinField k hk).vecBits (bsh k hk) := by
  apply List.ext_getElem (by simp [BinaryLinear.identityBits])
  intro i h1 h2
  simp only [BinaryLinear.identityBits, List.getElem_map, List.getElem_range, BinField.vecBits,
    List.getElem_ofFn]
  have hi : i < k := by simpa [BinaryLinear.identityBits] using h1
  rw [toBits_eq_vectorBits, bsh, LinearEquiv.apply_symm_apply]
  exact BinaryLinear.unitBits_eq_vectorBits (n := k) ⟨i, hi⟩

/-- The coordinate rows: row `i` is `C i ·`. -/
def cRows : List BitStr := List.ofFn fun i : Fin k => CL.toBits fun s => cm k hk hodd i s

theorem ctxProg_eq :
    ctxProg (unary k, unary j, unary (2 ^ j)) = (cRows k hk hodd, unary k, unary (2 ^ j)) := by
  simp only [ctxProg, PolyTimeFun.pair_apply, PolyTimeFun.comp_apply, PolyTimeFun.fst_apply,
    PolyTimeFun.snd_apply, BinaryLinear.identityBitsProg, PolyTimeFun.congr_apply, length_unary]
  rw [identityBits_eq k hk, BasisProgram.toSelfDualRowsProg_correct k hk hodd]
  rfl

omit [NeZero k] in
theorem toBits_blocks (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) :
    CL.toBits w = (List.ofFn fun bb : Fin (2 ^ 2 ^ j) =>
      CL.toBits fun s : Fin k => w (finProdFinEquiv (bb, s))).flatten := by
  rw [CL.toBits, CL.ofFn_eq_flatten_blocks]
  rfl

theorem coefProg_eq (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) :
    coefProg (CL.toBits w, cRows k hk hodd, unary k, unary (2 ^ j)) =
      CL.toBits (coef k hk hodd j w) := by
  have hmin : min (1 * 2 ^ 2 ^ j) (CL.toBits w).length = 2 ^ 2 ^ j := by
    rw [CL.length_toBits, one_mul]
    exact Nat.min_eq_left (Nat.le_mul_of_pos_right _ (by omega))
  simp only [coefProg, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.fst_apply,
    PolyTimeFun.snd_apply, PolyTimeFun.const_apply, FieldAnswerParser.rowsProg_apply,
    FieldAnswerParser.scalePowerOfTwoProg_apply, length_unary, hmin,
    PolyTimeFun.mapWith_apply, BinaryLinear.applyBitsProg_apply, BinaryBlock.flattenProg_apply]
  rw [toBits_blocks k j w, toBits_blocks k j (coef k hk hodd j w)]
  have hlen := List.length_ofFn (f := fun bb : Fin (2 ^ 2 ^ j) =>
    CL.toBits fun s : Fin k => w (finProdFinEquiv (bb, s)))
  have hs := BinaryBlock.splitBlocks_flatten k (List.ofFn fun bb : Fin (2 ^ 2 ^ j) =>
    CL.toBits fun s : Fin k => w (finProdFinEquiv (bb, s))) (by
      intro v hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      simp)
  rw [hlen] at hs
  rw [hs]
  rw [List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext bb
  simp only [Function.comp_apply, BinaryLinear.applyBits, cRows, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  change BinaryLinear.dotBits (BinaryLinear.vectorBits _) (BinaryLinear.vectorBits _) = _
  rw [BinaryLinear.dotBits_vectorBits]
  simp only [coef, Equiv.symm_apply_apply]
  rfl

theorem segProg_eq (a b : ℕ) (w : Fin (2 ^ 2 ^ j * k) → ZMod 2) :
    segProg a b (CL.toBits w, cRows k hk hodd, unary k, unary (2 ^ j)) =
      (List.ofFn fun σ : Fin 4 =>
        if (σ : ℕ) = a then CL.toBits (coef k hk hodd j w)
        else if (σ : ℕ) = b then CL.toBits w
        else List.replicate (2 ^ 2 ^ j * k) false).flatten ++ [false] := by
  simp only [segProg, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.append_apply,
    PolyTimeFun.const_apply, BinaryBlock.flattenProg_apply, PolyTimeFun.listOf_apply,
    List.map_ofFn]
  congr 2
  apply congrArg List.ofFn
  funext σ
  simp only [Function.comp_apply]
  split_ifs
  · exact coefProg_eq k hk hodd j w
  · rfl
  · simp [zerosProg]

omit [NeZero k] in
theorem zip_indicator_identity (S : Finset (Fin (2 ^ 2 ^ j * k))) :
    (CL.indicatorBits S).zip (BinaryLinear.identityBits (2 ^ 2 ^ j * k)) =
      (List.finRange (2 ^ 2 ^ j * k)).map fun i =>
        (decide (i ∈ S), CL.toBits (Pi.single i 1 : Fin (2 ^ 2 ^ j * k) → ZMod 2)) := by
  apply List.ext_getElem (by simp [CL.indicatorBits, BinaryLinear.identityBits])
  intro i h1 h2
  have hi : i < 2 ^ 2 ^ j * k := by simpa using h2
  simp only [List.getElem_zip, CL.indicatorBits, List.getElem_ofFn, BinaryLinear.identityBits,
    List.getElem_map, List.getElem_range, List.getElem_finRange]
  congr 1
  exact BinaryLinear.unitBits_eq_vectorBits (n := 2 ^ 2 ^ j * k) ⟨i, hi⟩

theorem families_eq {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) :
    PolyTimeFun.append ((genFamily a b) ((unary k, unary j, unary (2 ^ j)),
        CL.indicatorBits (P.factorOfPrefix 0 0), gens.map CL.toBits),
      (offFamily a c) ((unary k, unary j, unary (2 ^ j)),
        CL.indicatorBits (P.factorOfPrefix 0 0), gens.map CL.toBits)) =
      (gens.map fun z => (hideCon k hk hodd j (4 * (2 ^ 2 ^ j * k)) (a * (2 ^ 2 ^ j * k))
          (b * (2 ^ 2 ^ j * k)) (CL.proj (P.factorOfPrefix 0 0) z)).toCon) ++
        (((List.finRange (2 ^ 2 ^ j * k)).filter fun i => decide (i ∉ P.factorOfPrefix 0 0)).map
          fun i => (hideCon k hk hodd j (4 * (2 ^ 2 ^ j * k)) (a * (2 ^ 2 ^ j * k))
            (c * (2 ^ 2 ^ j * k)) (Pi.single i 1)).toCon) := by
  rw [PolyTimeFun.append_apply]
  congr 1
  · simp only [genFamily, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.fst_apply,
      PolyTimeFun.snd_apply, PolyTimeFun.mapWith_apply, List.map_map, ctxProg_eq k hk hodd j]
    apply List.map_congr_left
    intro z _
    simp only [Function.comp_apply, AuxiliaryBits.mask_correct, segProg_eq k hk hodd j,
      toCon_hideCon_seg k hk hodd j a b hab]
  · simp only [offFamily, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.fst_apply,
      PolyTimeFun.snd_apply, PolyTimeFun.mapWith_apply, ctxProg_eq k hk hodd j,
      PolyTimeFun.zip_apply,
      PolyTimeFun.length_apply, length_unary, BinaryLinear.identityBitsProg,
      BinaryLinear.flattenBitsProg, PolyTimeFun.congr_apply]
    have hlen : (CL.indicatorBits (P.factorOfPrefix 0 0)).length = 2 ^ 2 ^ j * k := by
      simp [CL.indicatorBits]
    rw [hlen, zip_indicator_identity, List.map_map]
    have hstep : ∀ i : Fin (2 ^ 2 ^ j * k),
        ((PolyTimeFun.fst.comp PolyTimeFun.fst).ite (PolyTimeFun.const [])
            (((segProg a c).comp ((PolyTimeFun.snd.comp PolyTimeFun.fst).pair
              PolyTimeFun.snd)).cons (PolyTimeFun.const [])) :
            PolyTimeFun ((Bool × BitStr) × Ctx) (List BitStr))
          ((decide (i ∈ P.factorOfPrefix 0 0),
            CL.toBits (Pi.single i 1 : Fin (2 ^ 2 ^ j * k) → ZMod 2)),
            cRows k hk hodd, unary k, unary (2 ^ j)) =
        if decide (i ∈ P.factorOfPrefix 0 0) then []
        else [(hideCon k hk hodd j (4 * (2 ^ 2 ^ j * k)) (a * (2 ^ 2 ^ j * k))
          (c * (2 ^ 2 ^ j * k)) (Pi.single i 1)).toCon] := by
      intro i
      simp only [PolyTimeFun.ite_apply, PolyTimeFun.comp_apply, PolyTimeFun.fst_apply,
        PolyTimeFun.const_apply, PolyTimeFun.cons_apply, PolyTimeFun.pair_apply,
        PolyTimeFun.snd_apply, segProg_eq k hk hodd j, toCon_hideCon_seg k hk hodd j a c hac]
    simp only [Function.comp_def]
    rw [List.map_congr_left (l := List.finRange (2 ^ 2 ^ j * k))
      (g := fun i => if decide (i ∈ P.factorOfPrefix 0 0) then []
        else [(hideCon k hk hodd j (4 * (2 ^ 2 ^ j * k)) (a * (2 ^ 2 ^ j * k))
          (c * (2 ^ 2 ^ j * k)) (Pi.single i 1)).toCon]) (fun i _ => hstep i)]
    rw [flatten_map_ite]
    congr 1

/-- **`pauliHideProg` computes `pauliHideCons`**, from the kernel's parameter triple, the mask of
the first factor `S = P.factorOfPrefix 0 0` and the generators' bits. -/
theorem pauliHideProg_eq {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) :
    pauliHideProg ((unary k, unary j, unary (2 ^ j)), CL.indicatorBits (P.factorOfPrefix 0 0),
        gens.map CL.toBits) = pauliHideCons k hk hodd j P gens := by
  rw [pauliHideCons, hideChecks_toCon k hk hodd j P gens 0 _ 0 2 3 (by simp) (by ring) (by ring),
    ← families_eq k hk hodd j P gens 0 2 3 (by decide) (by decide)]
  rfl

/-- **`pauliHideRevProg` computes `pauliHideConsRev`.** -/
theorem pauliHideRevProg_eq {ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin (2 ^ 2 ^ j * k)) ℓ)
    (gens : List (Fin (2 ^ 2 ^ j * k) → CL.𝔽₂)) :
    pauliHideRevProg ((unary k, unary j, unary (2 ^ j)),
        CL.indicatorBits (P.factorOfPrefix 0 0), gens.map CL.toBits) =
      pauliHideConsRev k hk hodd j P gens := by
  rw [pauliHideConsRev, hideChecks_toCon k hk hodd j P gens _ 0 3 1 2 rfl (by ring) (by ring),
    ← families_eq k hk hodd j P gens 3 1 2 (by decide) (by decide)]
  rfl

end MIPRE.Tailored.Intro.PauliHideProg

end

end
