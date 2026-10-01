/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import MIPRE.Background.Repetition.CommutingRepetition.Tracial.Interface
public import MIPRE.Foundations.MatUnits
public import MIPRE.Tactics

@[expose] public section

/-!
# The twisted Pauli algebra: a standard tracial algebra with unital dyadic matrix units

Work package T4 of C6b (`planning/c6b-plan.md`; `reports/c6b-paper-proofs.md`, §3.8). The value
lemma's amplification (Theorems A and T of the report, §3) tensors a finite pair with a standard
tracial algebra `B` whose `⋆`-algebra `B.A` has unital `2ⁿ × 2ⁿ` matrix units for every `n`
(`HasDyadicUnits`, `MIPRE/Foundations/MatUnits.lean`). This file constructs one, the **twisted
Pauli algebra** (`pauliStd`, `pauliStd_hasDyadicUnits`), in the interface
`CommutingRepetition.StdTracialAlgebra` of the vendored commuting-repetition development.

* **Labels and phase.** The Pauli labels are `Label = ℕ →₀ ZMod 2 × ZMod 2`, a pair of bits
  `(x, z)` at each site. The phase is `ω(g, h) = (-1)^{β(g, h)}` with `β(g, h) = ∑ᵢ z(g)ᵢ x(h)ᵢ`,
  a bilinear, hence `2`-cocycle, twist (`phase_cocycle`).
* **The operators.** On `ℓ²(Label)` the unitary `W g` sends `δ_h` to `ω(g, h) δ_{g+h}`, so that
  `W g W h = ω(g, h) W (g + h)` and `(W g)⋆ = ω(g, g) W g`.
* **The algebra.** `pauliA` is the linear span of the `W g` in `B(ℓ²(Label))`, a `⋆`-subalgebra;
  it is not closed, which the interface does not ask for. The trace is the vector state at
  `δ₀`, tracial because `τ(W g) = [g = 0]`; the GNS map is `a ↦ a δ₀`, with dense range since its
  image contains every `δ_g`; the left action is the inclusion, and the right action is
  `op a ↦ J a⋆ J` for the antiunitary `(J ξ)ₖ = ω(k, k) conj(ξₖ)`, which satisfies Tomita's
  identity `J (a δ₀) = a⋆ δ₀` (`J_pauliEmbed`). That the two actions commute is checked on the
  dense range.
* **The units.** `X_k = W (single k (1, 0))` and `Z_k = W (single k (0, 1))` are Pauli sites in
  the sense of `MIPRE.PauliSites` (`pauliSites`), whose units `Π_k X_kᵃ (1 + Z_k)/2 X_kᵇ` are
  unital in `pauliA` itself, not only after the representation.

Names that would shadow the fields of `StdTracialAlgebra` are spelled out: the algebra is
`pauliA`, its trace `pauliTrace`, the Hilbert space `PauliSpace`, the GNS map `pauliEmbed` and the
right action `pauliRight`.

The interface imports all of Mathlib, but the file names the two Mathlib modules it needs, and
compiles with only those: `ℓ²`, and the C⋆-algebra of operators on a Hilbert space. The second is
there for instance search rather than for a lemma: without it, `Algebra ℂ B(ℓ²(Label))` and its
scalar-tower instances are searched through the metric structure of the carrier of `lp` and run
out of budget.
-/

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace MIPRE.Repetition.Pauli

open ContinuousLinearMap

/-! ### Pauli labels and the phase cocycle -/

/-- **Pauli labels**: finitely supported sequences of pairs `(x-bit, z-bit)`. -/
abbrev Label := ℕ →₀ ZMod 2 × ZMod 2

/-- **The twist** `β(g, h) = ∑ᵢ z(g)ᵢ x(h)ᵢ`, the half of the symplectic form that defines the
phase. -/
def twist (g h : Label) : ZMod 2 := g.sum fun i a => a.2 * (h i).1

/-- The twist is additive in its first argument. -/
theorem twist_add_left (g g' h : Label) : twist (g + g') h = twist g h + twist g' h := by
  unfold twist
  rw [Finsupp.sum_add_index'] <;> intros <;> simp [add_mul]

/-- The twist is additive in its second argument. -/
theorem twist_add_right (g h h' : Label) : twist g (h + h') = twist g h + twist g h' := by
  unfold twist
  rw [← Finsupp.sum_add]
  simp [mul_add]

/-- `β(0, h) = 0`. -/
@[simp] theorem twist_zero_left (h : Label) : twist 0 h = 0 := by simp [twist]

/-- `β(g, 0) = 0`. -/
@[simp] theorem twist_zero_right (g : Label) : twist g 0 = 0 := by simp [twist]

/-- The twist of two single-site labels. -/
theorem twist_single (k l : ℕ) (u v : ZMod 2 × ZMod 2) :
    twist (Finsupp.single k u) (Finsupp.single l v) = u.2 * (if l = k then v.1 else 0) := by
  unfold twist
  rw [Finsupp.sum_single_index (by simp), Finsupp.single_apply]
  split_ifs <;> simp

/-- Every label is its own inverse. -/
theorem label_add_self (g : Label) : g + g = 0 := by
  ext i <;> simp [CharTwo.add_self_eq_zero]

/-- **The sign character** `ZMod 2 → {±1}`. -/
def signChar (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

private theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

/-- `(-1)⁰ = 1`. -/
@[simp] theorem signChar_zero : signChar 0 = 1 := by simp [signChar]

/-- `(-1)¹ = -1`. -/
@[simp] theorem signChar_one : signChar 1 = -1 := by simp [signChar]

/-- The sign character is a character. -/
theorem signChar_add (a b : ZMod 2) : signChar (a + b) = signChar a * signChar b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

/-- The sign character squares to `1`. -/
theorem signChar_mul_self (a : ZMod 2) : signChar a * signChar a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp

/-- The sign character is unimodular. -/
theorem norm_signChar (a : ZMod 2) : ‖signChar a‖ = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp

/-- The sign character is real. -/
theorem conj_signChar (a : ZMod 2) : conj (signChar a) = signChar a := by
  rcases zmod2_cases a with rfl | rfl <;> simp

/-- **The phase** `ω(g, h) = (-1)^{β(g, h)}`. -/
def phase (g h : Label) : ℂ := signChar (twist g h)

/-- **The cocycle identity** of the phase, in the form `W g W h = ω(g, h) W (g + h)` needs at the
coordinate `k`. -/
theorem phase_cocycle (g h k : Label) :
    phase g (k + g) * phase h (k + (g + h)) = phase g h * phase (g + h) (k + (g + h)) := by
  unfold phase
  rw [← signChar_add, ← signChar_add]
  congr 1
  simp only [twist_add_left, twist_add_right]
  generalize twist g h = a, twist g k = b, twist g g = c, twist h k = d, twist h g = e,
    twist h h = f
  revert a b c d e f
  decide

/-- The phase is unimodular. -/
theorem norm_phase (g h : Label) : ‖phase g h‖ = 1 := norm_signChar _

/-- The phase squares to `1`. -/
theorem phase_mul_self (g h : Label) : phase g h * phase g h = 1 := signChar_mul_self _

/-- The phase is real. -/
theorem conj_phase (g h : Label) : conj (phase g h) = phase g h := conj_signChar _

/-- The phase of two single-site labels. -/
theorem phase_single (k l : ℕ) (u v : ZMod 2 × ZMod 2) :
    phase (Finsupp.single k u) (Finsupp.single l v) =
      signChar (u.2 * (if l = k then v.1 else 0)) := by
  rw [phase, twist_single]

/-! ### `ℓ²(Label)` and weighted permutations -/

/-- **The Hilbert space** `ℓ²(Label)`. -/
abbrev PauliSpace := ↥(lp (fun _ : Label => ℂ) 2)

/-- The exponent `2` of `ℓ²` is positive, in the form the `lp` API asks for. -/
private theorem two_toReal_pos : 0 < (2 : ENNReal).toReal := by norm_num

/-- The squared coordinates of a vector of `ℓ²(Label)` are summable. -/
private theorem summable_sq (ξ : PauliSpace) :
    Summable fun k => ‖ξ k‖ ^ (2 : ENNReal).toReal :=
  (memℓp_gen_iff two_toReal_pos).1 (lp.memℓp ξ)

/-- The vector `k ↦ φ k * ξ (e k)`, for a unimodular weight `φ` and a permutation `e`. -/
def weightedPermFun (e : Label ≃ Label) (φ : Label → ℂ) (hφ : ∀ k, ‖φ k‖ = 1)
    (ξ : PauliSpace) : PauliSpace :=
  ⟨fun k => φ k * ξ (e k), (memℓp_gen_iff (by norm_num)).2 <| by
    have := (e.summable_iff (f := fun k => ‖ξ k‖ ^ (2:ENNReal).toReal)).2 (summable_sq ξ)
    simpa [norm_mul, hφ, Function.comp_def] using this⟩

/-- The coordinates of a weighted permutation of a vector. -/
@[simp] theorem weightedPermFun_apply (e : Label ≃ Label) (φ : Label → ℂ) (hφ : ∀ k, ‖φ k‖ = 1)
    (ξ : PauliSpace) (k : Label) : weightedPermFun e φ hφ ξ k = φ k * ξ (e k) := rfl

/-- A weighted permutation preserves the norm. -/
theorem norm_weightedPermFun (e : Label ≃ Label) (φ : Label → ℂ) (hφ : ∀ k, ‖φ k‖ = 1)
    (ξ : PauliSpace) : ‖weightedPermFun e φ hφ ξ‖ = ‖ξ‖ := by
  rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
  congr 1
  simp only [weightedPermFun_apply, norm_mul, hφ, one_mul]
  exact e.tsum_eq (fun k => ‖ξ k‖ ^ (2:ENNReal).toReal)

/-- **A weighted permutation** `ξ ↦ (k ↦ φ k * ξ (e k))`, as a bounded operator (an isometry). -/
def weightedPerm (e : Label ≃ Label) (φ : Label → ℂ) (hφ : ∀ k, ‖φ k‖ = 1) :
    PauliSpace →L[ℂ] PauliSpace :=
  LinearMap.mkContinuous
    { toFun := weightedPermFun e φ hφ
      map_add' := fun ξ η => by ext k; simp [mul_add]
      map_smul' := fun c ξ => by ext k; simp; ring }
    1 (fun ξ => by simp [norm_weightedPermFun])

/-- The coordinates of the image under a weighted permutation. -/
@[simp] theorem weightedPerm_apply (e : Label ≃ Label) (φ : Label → ℂ) (hφ : ∀ k, ‖φ k‖ = 1)
    (ξ : PauliSpace) (k : Label) : weightedPerm e φ hφ ξ k = φ k * ξ (e k) := rfl

/-- A weighted permutation is an isometry. -/
theorem norm_weightedPerm (e : Label ≃ Label) (φ : Label → ℂ) (hφ : ∀ k, ‖φ k‖ = 1)
    (ξ : PauliSpace) : ‖weightedPerm e φ hφ ξ‖ = ‖ξ‖ := norm_weightedPermFun e φ hφ ξ

/-! ### The twisted Pauli unitaries `W g` -/

/-- **The twisted Pauli unitary** `W g`, with `W g δ_h = ω(g, h) δ_{g+h}`. -/
def W (g : Label) : PauliSpace →L[ℂ] PauliSpace :=
  weightedPerm (Equiv.addRight g) (fun k => phase g (k + g)) (fun _ => norm_phase _ _)

/-- The coordinates of `W g ξ`: `(W g ξ)ₖ = ω(g, k + g) ξ_{k+g}`. -/
@[simp] theorem W_apply (g : Label) (ξ : PauliSpace) (k : Label) :
    W g ξ k = phase g (k + g) * ξ (k + g) := rfl

/-- `W g` is an isometry. -/
theorem norm_W (g : Label) (ξ : PauliSpace) : ‖W g ξ‖ = ‖ξ‖ := norm_weightedPerm _ _ _ ξ

/-- `W g W h = ω(g, h) W (g + h)`. -/
theorem W_mul (g h : Label) : W g * W h = phase g h • W (g + h) := by
  ext ξ k
  simp only [mul_apply_eq_comp, W_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc, ← mul_assoc, phase_cocycle, mul_assoc]

/-- `W 0 = 1`. -/
theorem W_zero : W 0 = 1 := by
  ext ξ k
  simp [phase]

/-- `(W g)² = ω(g, g)`. -/
theorem W_mul_self (g : Label) : W g * W g = phase g g • (1 : PauliSpace →L[ℂ] PauliSpace) := by
  rw [W_mul, label_add_self, W_zero]

/-- `(W g)⋆ = ω(g, g) W g`. -/
theorem star_W (g : Label) : star (W g) = phase g g • W g := by
  have iso : star (W g) * W g = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (W g)).1 (norm_W g)
  calc star (W g) = star (W g) * (phase g g • (W g * W g)) := by
        rw [W_mul_self, smul_smul, phase_mul_self, one_smul, mul_one]
    _ = phase g g • W g := by rw [mul_smul_comm, ← mul_assoc, iso, one_mul]

/-! ### Basis vectors -/

/-- **The basis vector** `δ_h`. -/
def basisVec (h : Label) : PauliSpace := lp.single 2 h (1 : ℂ)

/-- The coordinates of `δ_h`. -/
theorem basisVec_apply (h k : Label) : basisVec h k = if k = h then 1 else 0 := by
  simp [basisVec, Pi.single_apply]

private theorem add_eq_iff_eq_add (k g h : Label) : k + g = h ↔ k = g + h := by
  constructor
  · rintro rfl; rw [add_comm k g, ← add_assoc, label_add_self, zero_add]
  · rintro rfl; rw [add_comm g h, add_assoc, label_add_self, add_zero]

/-- `W g δ_h = ω(g, h) δ_{g+h}`. -/
theorem W_basisVec (g h : Label) : W g (basisVec h) = phase g h • basisVec (g + h) := by
  ext k
  simp only [W_apply, basisVec_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    add_eq_iff_eq_add]
  split_ifs with hk
  · subst hk; rw [add_comm g h, add_assoc, label_add_self, add_zero]
  · simp

/-- **The trace vector** `δ₀`. -/
def traceVec : PauliSpace := basisVec 0

/-- `W g δ₀ = δ_g`. -/
theorem W_traceVec (g : Label) : W g traceVec = basisVec g := by
  rw [traceVec, W_basisVec]; simp [phase]

/-- `⟪δ₀, δ_h⟫ = [h = 0]`. -/
theorem inner_traceVec_basisVec (h : Label) :
    ⟪traceVec, basisVec h⟫_ℂ = if h = 0 then 1 else 0 := by
  rw [traceVec, basisVec, lp.inner_single_left, basisVec_apply]
  simp [eq_comm]

/-! ### The algebra -/

/-- The linear span of the `W g`. -/
def pauliSpan : Submodule ℂ (PauliSpace →L[ℂ] PauliSpace) := Submodule.span ℂ (Set.range W)

/-- Each `W g` lies in the span. -/
theorem W_mem_pauliSpan (g : Label) : W g ∈ pauliSpan := Submodule.subset_span ⟨g, rfl⟩

/-- The span is closed under multiplication. -/
theorem mul_mem_pauliSpan {a b : PauliSpace →L[ℂ] PauliSpace} (ha : a ∈ pauliSpan)
    (hb : b ∈ pauliSpan) : a * b ∈ pauliSpan := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hx; obtain ⟨h, rfl⟩ := hy
      rw [W_mul]; exact Submodule.smul_mem _ _ (W_mem_pauliSpan _)
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

/-- The span is closed under the adjoint. -/
theorem star_mem_pauliSpan {a : PauliSpace →L[ℂ] PauliSpace} (ha : a ∈ pauliSpan) :
    star a ∈ pauliSpan := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx; rw [star_W]; exact Submodule.smul_mem _ _ (W_mem_pauliSpan _)
  | zero => rw [star_zero (PauliSpace →L[ℂ] PauliSpace)]; exact zero_mem _
  | add x y _ _ hx hy =>
    rw [show star (x + y) = star x + star y from star_add x y]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [show star (c • x) = star c • star x from star_smul c x]; exact Submodule.smul_mem _ _ hx

/-- **The twisted Pauli `⋆`-algebra** (`lem:pauli-algebra`): the linear span of the `W g` inside
`B(ℓ²(Label))`. -/
def pauliA : StarSubalgebra ℂ (PauliSpace →L[ℂ] PauliSpace) where
  carrier := pauliSpan
  mul_mem' := mul_mem_pauliSpan
  add_mem' := add_mem
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one, ← W_zero]; exact Submodule.smul_mem _ _ (W_mem_pauliSpan _)
  star_mem' := star_mem_pauliSpan

/-- Membership in `pauliA` is membership in the span. -/
theorem mem_pauliA {a : PauliSpace →L[ℂ] PauliSpace} : a ∈ pauliA ↔ a ∈ pauliSpan := Iff.rfl

/-- `W g` as an element of `pauliA`. -/
def w (g : Label) : pauliA := ⟨W g, W_mem_pauliSpan g⟩

/-- `w g w h = ω(g, h) w (g + h)`. -/
theorem w_mul (g h : Label) : w g * w h = phase g h • w (g + h) := Subtype.ext (W_mul g h)

/-- `w 0 = 1`. -/
theorem w_zero : w 0 = 1 := Subtype.ext W_zero

/-- `(w g)⋆ = ω(g, g) w g`. -/
theorem star_w (g : Label) : star (w g) = phase g g • w g := Subtype.ext (star_W g)

/-- **Induction over the span**, for elements of `pauliA`. -/
theorem pauliA_induction {p : pauliA → Prop} (hw : ∀ g, p (w g)) (h0 : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ (c : ℂ) a, p a → p (c • a)) (a : pauliA) :
    p a := by
  obtain ⟨a, ha⟩ := a
  induction (mem_pauliA.1 ha) using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hw g
  | zero => exact h0
  | add x y hx hy px py => exact hadd _ _ (px hx) (py hy)
  | smul c x hx px => exact hsmul c _ (px hx)

/-! ### The trace and the GNS data -/

/-- **The trace** of `pauliA`: the vector state at `δ₀`. -/
def pauliTrace : pauliA →ₗ[ℂ] ℂ where
  toFun a := ⟪traceVec, (a : PauliSpace →L[ℂ] PauliSpace) traceVec⟫_ℂ
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

/-- The trace is the vector state at `δ₀`. -/
theorem pauliTrace_apply (a : pauliA) :
    pauliTrace a = ⟪traceVec, (a : PauliSpace →L[ℂ] PauliSpace) traceVec⟫_ℂ := rfl

/-- The trace is normalized. -/
theorem pauliTrace_one : pauliTrace 1 = 1 := by
  rw [pauliTrace_apply]; simp [traceVec, basisVec]

/-- The trace commutes with the adjoint. -/
theorem pauliTrace_star (a : pauliA) : pauliTrace (star a) = star (pauliTrace a) := by
  rw [pauliTrace_apply, pauliTrace_apply,
    show ((star a : pauliA) : PauliSpace →L[ℂ] PauliSpace) =
      star (a : PauliSpace →L[ℂ] PauliSpace) from rfl,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm]
  rfl

private theorem pauliTrace_w_mul_w_of_ne {g h : Label} (hne : g ≠ h) :
    pauliTrace (w g * w h) = 0 := by
  rw [pauliTrace_apply]
  change ⟪traceVec, (W g * W h) traceVec⟫_ℂ = 0
  have hne' : g + h ≠ 0 := by
    intro h0
    apply hne
    have := congrArg (· + h) h0
    simpa [add_assoc, label_add_self] using this
  rw [W_mul, smul_apply, W_traceVec, inner_smul_right, inner_traceVec_basisVec]
  simp [hne']

/-- The trace is tracial on the unitaries `W g`. -/
theorem pauliTrace_w_mul_comm (g h : Label) : pauliTrace (w g * w h) = pauliTrace (w h * w g) := by
  by_cases hgh : g = h
  · rw [hgh]
  · rw [pauliTrace_w_mul_w_of_ne hgh, pauliTrace_w_mul_w_of_ne (Ne.symm hgh)]

/-- **The trace is tracial.** -/
theorem pauliTrace_mul_comm (a b : pauliA) : pauliTrace (a * b) = pauliTrace (b * a) := by
  induction a using pauliA_induction with
  | hw g =>
    induction b using pauliA_induction with
    | hw h => exact pauliTrace_w_mul_comm g h
    | h0 => simp
    | hadd x y hx hy => rw [mul_add, add_mul, map_add, map_add, hx, hy]
    | hsmul c x hx => rw [mul_smul_comm, smul_mul_assoc, map_smul, map_smul, hx]
  | h0 => simp
  | hadd x y hx hy => rw [mul_add, add_mul, map_add, map_add, hx, hy]
  | hsmul c x hx => rw [mul_smul_comm, smul_mul_assoc, map_smul, map_smul, hx]

/-- **The GNS map** `a ↦ a δ₀`. -/
def pauliEmbed : pauliA →ₗ[ℂ] PauliSpace where
  toFun a := (a : PauliSpace →L[ℂ] PauliSpace) traceVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The GNS map is evaluation at `δ₀`. -/
theorem pauliEmbed_apply (a : pauliA) :
    pauliEmbed a = (a : PauliSpace →L[ℂ] PauliSpace) traceVec := rfl

/-- The GNS map sends `w g` to `δ_g`. -/
theorem pauliEmbed_w (g : Label) : pauliEmbed (w g) = basisVec g := W_traceVec g

/-- The GNS map realizes the trace: `⟪a δ₀, b δ₀⟫ = τ(a⋆ b)`. -/
theorem inner_pauliEmbed (a b : pauliA) :
    ⟪pauliEmbed a, pauliEmbed b⟫_ℂ = pauliTrace (star a * b) := by
  rw [pauliEmbed_apply, pauliEmbed_apply, pauliTrace_apply,
    show ((star a * b : pauliA) : PauliSpace →L[ℂ] PauliSpace) =
      star (a : PauliSpace →L[ℂ] PauliSpace) * b from rfl,
    mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- **The GNS map has dense range**: its image contains every `δ_g`. -/
theorem pauliEmbed_dense : DenseRange pauliEmbed := by
  intro f
  have hs := lp.hasSum_single (E := fun _ : Label => ℂ) (p := 2) ENNReal.ofNat_ne_top f
  refine mem_closure_of_tendsto hs (Filter.Eventually.of_forall fun s => ?_)
  change _ ∈ (LinearMap.range pauliEmbed : Set PauliSpace)
  refine Submodule.sum_mem _ fun i _ => ?_
  have : lp.single 2 i (f i) = f i • basisVec i := by
    ext k; simp [basisVec, Pi.single_apply]
  rw [this]
  exact Submodule.smul_mem _ _ ⟨w i, pauliEmbed_w i⟩

/-- The GNS map intertwines left multiplication with the operator. -/
theorem pauliEmbed_mul (a b : pauliA) :
    pauliEmbed (a * b) = (a : PauliSpace →L[ℂ] PauliSpace) (pauliEmbed b) := rfl

/-! ### The modular conjugation `J` and the right action -/

/-- **The modular conjugation** `(J ξ)ₖ = ω(k, k) conj(ξₖ)`: the antiunitary with
`J (a δ₀) = a⋆ δ₀`. -/
def J (ξ : PauliSpace) : PauliSpace :=
  ⟨fun k => phase k k * conj (ξ k), (memℓp_gen_iff (by norm_num)).2 <| by
    simpa [norm_phase] using summable_sq ξ⟩

/-- The coordinates of `J ξ`. -/
@[simp] theorem J_apply (ξ : PauliSpace) (k : Label) : J ξ k = phase k k * conj (ξ k) := rfl

/-- `J` is additive. -/
theorem J_add (ξ η : PauliSpace) : J (ξ + η) = J ξ + J η := by ext k; simp [mul_add]

/-- `J` is conjugate-linear. -/
theorem J_smul (c : ℂ) (ξ : PauliSpace) : J (c • ξ) = conj c • J ξ := by ext k; simp; ring

/-- `J` is an involution. -/
theorem J_J (ξ : PauliSpace) : J (J ξ) = ξ := by
  ext k
  simp only [J_apply, map_mul, conj_phase, Complex.conj_conj]
  rw [← mul_assoc, phase_mul_self, one_mul]

/-- `J` is isometric. -/
theorem norm_J (ξ : PauliSpace) : ‖J ξ‖ = ‖ξ‖ := by
  rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
  simp [norm_phase]

/-- `J` is antiunitary: `⟪J ξ, J η⟫ = ⟪η, ξ⟫`. -/
theorem inner_J_J (ξ η : PauliSpace) : ⟪J ξ, J η⟫_ℂ = ⟪η, ξ⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  ext k
  simp only [J_apply, RCLike.inner_apply', map_mul, conj_phase, RCLike.conj_conj]
  linear_combination (ξ k * conj (η k)) * phase_mul_self k k

/-- `⟪J u, v⟫ = ⟪J v, u⟫`. -/
theorem inner_J_left (u v : PauliSpace) : ⟪J u, v⟫_ℂ = ⟪J v, u⟫_ℂ := by
  conv_lhs => rw [← J_J v]
  rw [inner_J_J]

/-- **Conjugation by `J`**: `T ↦ J T J`, a complex-antilinear `⋆`-preserving ring map. -/
def conjJ (T : PauliSpace →L[ℂ] PauliSpace) : PauliSpace →L[ℂ] PauliSpace :=
  LinearMap.mkContinuous
    { toFun := fun ξ => J (T (J ξ))
      map_add' := fun ξ η => by simp [J_add]
      map_smul' := fun c ξ => by simp [J_smul] }
    ‖T‖ (fun ξ => by simpa [norm_J] using T.le_opNorm (J ξ))

/-- `(J T J) ξ = J (T (J ξ))`. -/
@[simp] theorem conjJ_apply (T : PauliSpace →L[ℂ] PauliSpace) (ξ : PauliSpace) :
    conjJ T ξ = J (T (J ξ)) := rfl

/-- Conjugation by `J` is multiplicative. -/
theorem conjJ_mul (S T : PauliSpace →L[ℂ] PauliSpace) : conjJ (S * T) = conjJ S * conjJ T := by
  ext1 ξ; simp [mul_apply_eq_comp, J_J]

/-- Conjugation by `J` is unital. -/
theorem conjJ_one : conjJ 1 = 1 := by ext1 ξ; simp [J_J]

/-- Conjugation by `J` is additive. -/
theorem conjJ_add (S T : PauliSpace →L[ℂ] PauliSpace) : conjJ (S + T) = conjJ S + conjJ T := by
  ext1 ξ; simp [J_add]

/-- Conjugation by `J` is conjugate-linear. -/
theorem conjJ_smul (c : ℂ) (T : PauliSpace →L[ℂ] PauliSpace) :
    conjJ (c • T) = conj c • conjJ T := by
  ext1 ξ; simp [J_smul]

/-- Conjugation by `J` sends `0` to `0`. -/
theorem conjJ_zero : conjJ 0 = 0 := by
  ext1 ξ; rw [conjJ_apply]; ext k; simp

/-- Conjugation by `J` commutes with the adjoint. -/
theorem conjJ_star (T : PauliSpace →L[ℂ] PauliSpace) : conjJ (star T) = star (conjJ T) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  rw [conjJ_apply, conjJ_apply, inner_J_left, ContinuousLinearMap.adjoint_inner_right,
    ← inner_J_J (J x) (T (J y)), J_J]

/-- `J δ_g = ω(g, g) δ_g`. -/
theorem J_basisVec (g : Label) : J (basisVec g) = phase g g • basisVec g := by
  ext k
  simp only [J_apply, basisVec_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs with hk
  · subst hk; simp
  · simp

/-- **Tomita's identity** on `pauliA`: `J (a δ₀) = a⋆ δ₀`. -/
theorem J_pauliEmbed (a : pauliA) : J (pauliEmbed a) = pauliEmbed (star a) := by
  induction a using pauliA_induction with
  | hw g =>
    rw [pauliEmbed_w, J_basisVec, pauliEmbed_apply,
      show ((star (w g) : pauliA) : PauliSpace →L[ℂ] PauliSpace) = star (W g) from rfl, star_W,
      smul_apply, W_traceVec]
  | h0 => rw [star_zero (↥pauliA), map_zero]; ext k; simp
  | hadd x y hx hy => rw [map_add, J_add, hx, hy, star_add, map_add]
  | hsmul c x hx => rw [map_smul, J_smul, hx, star_smul, map_smul]; rfl

/-- **The right action** of `pauliA`: `op a ↦ J a⋆ J`. -/
def pauliRight : (↥pauliA)ᵐᵒᵖ →⋆ₐ[ℂ] (PauliSpace →L[ℂ] PauliSpace) where
  toFun a := conjJ (star ((MulOpposite.unop a : pauliA) : PauliSpace →L[ℂ] PauliSpace))
  map_one' := by
    change conjJ (star (1 : PauliSpace →L[ℂ] PauliSpace)) = 1
    rw [star_one (PauliSpace →L[ℂ] PauliSpace), conjJ_one]
  map_mul' a b := by
    change conjJ (star (((MulOpposite.unop b : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace) *
      ((MulOpposite.unop a : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace))) = _
    rw [star_mul ((MulOpposite.unop b : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace), conjJ_mul]
  map_zero' := by
    change conjJ (star (0 : PauliSpace →L[ℂ] PauliSpace)) = 0
    rw [star_zero (PauliSpace →L[ℂ] PauliSpace), conjJ_zero]
  map_add' a b := by
    change conjJ (star (((MulOpposite.unop a : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace) +
      ((MulOpposite.unop b : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace))) = _
    rw [star_add ((MulOpposite.unop a : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace), conjJ_add]
  commutes' c := by
    change conjJ (star (algebraMap ℂ (PauliSpace →L[ℂ] PauliSpace) c)) =
      algebraMap ℂ (PauliSpace →L[ℂ] PauliSpace) c
    rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one (PauliSpace →L[ℂ] PauliSpace),
      conjJ_smul, conjJ_one]
    simp
  map_star' a := by
    change conjJ (star (star ((MulOpposite.unop a : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace))) =
      star (conjJ (star ((MulOpposite.unop a : ↥pauliA) : PauliSpace →L[ℂ] PauliSpace)))
    rw [← conjJ_star]

/-- The right action of `op a` is `J a⋆ J`. -/
theorem pauliRight_op (a : pauliA) :
    pauliRight (MulOpposite.op a) = conjJ (star (a : PauliSpace →L[ℂ] PauliSpace)) := rfl

/-- The right action multiplies on the right: `R(op a) (b δ₀) = (b a) δ₀`. -/
theorem pauliRight_pauliEmbed (a b : pauliA) :
    pauliRight (MulOpposite.op a) (pauliEmbed b) = pauliEmbed (b * a) := by
  rw [pauliRight_op, conjJ_apply, J_pauliEmbed,
    ← show ((star a : pauliA) : PauliSpace →L[ℂ] PauliSpace) =
      star (a : PauliSpace →L[ℂ] PauliSpace) from rfl,
    ← pauliEmbed_mul, ← star_mul b a, J_pauliEmbed, star_star]

/-- **The left and right actions commute**, checked on the dense range of the GNS map. -/
theorem pauliA_commute_pauliRight (a b : pauliA) :
    Commute (pauliA.subtype a) (pauliRight (MulOpposite.op b)) := by
  change (a : PauliSpace →L[ℂ] PauliSpace) * pauliRight (MulOpposite.op b) =
    pauliRight (MulOpposite.op b) * (a : PauliSpace →L[ℂ] PauliSpace)
  refine DFunLike.coe_injective ?_
  refine DenseRange.equalizer pauliEmbed_dense (map_continuous _) (map_continuous _)
    (funext fun c => ?_)
  simp only [Function.comp_apply, mul_apply_eq_comp]
  rw [pauliRight_pauliEmbed, ← pauliEmbed_mul, ← pauliEmbed_mul, pauliRight_pauliEmbed, mul_assoc]

/-- **The twisted Pauli algebra as a standard tracial algebra** (`lem:pauli-algebra`): `pauliA` with
the vector trace at `δ₀`, on `ℓ²(Label)`, acting on the left by inclusion and on the right through
`J`. -/
def pauliStd : CommutingRepetition.StdTracialAlgebra.{0} where
  A := ↥pauliA
  τ := pauliTrace
  τ_one := pauliTrace_one
  τ_mul_comm := pauliTrace_mul_comm
  τ_star := pauliTrace_star
  H := PauliSpace
  ι := pauliEmbed
  ι_dense := pauliEmbed_dense
  ι_inner := inner_pauliEmbed
  L := pauliA.subtype
  R := pauliRight
  L_apply _ _ := rfl
  R_apply := pauliRight_pauliEmbed
  LR_commute := pauliA_commute_pauliRight

/-! ### The Pauli sites and the dyadic units -/

/-- The label of `X` at site `k`. -/
def xLabel (k : ℕ) : Label := Finsupp.single k (1, 0)

/-- The label of `Z` at site `k`. -/
def zLabel (k : ℕ) : Label := Finsupp.single k (0, 1)

/-- The `X` labels carry no `z`-bits, so their phase on the left is trivial. -/
theorem phase_xLabel_left (k : ℕ) (h : Label) : phase (xLabel k) h = 1 := by
  simp [phase, twist, xLabel]

/-- The `Z` labels carry no `x`-bits, so their phase on the right is trivial. -/
theorem phase_zLabel_right (g : Label) (l : ℕ) : phase g (zLabel l) = 1 := by
  have : ∀ i, (zLabel l i).1 = 0 := fun i => by
    rw [zLabel, Finsupp.single_apply]; split_ifs <;> rfl
  simp [phase, twist, this]

/-- `Z_k` and `X_l` anticommute exactly when `k = l`. -/
theorem phase_zLabel_xLabel (k l : ℕ) :
    phase (zLabel k) (xLabel l) = if l = k then -1 else 1 := by
  rw [zLabel, xLabel, phase_single]; split_ifs <;> simp

/-- `w g w h = w (g + h)` when the phase is trivial. The three `w`-lemmas below are proved in the
operators, where the scalar actions are found much faster than on the subalgebra. -/
theorem w_mul_of_phase_eq_one {g h : Label} (hgh : phase g h = 1) : w g * w h = w (g + h) :=
  Subtype.ext (show W g * W h = W (g + h) by rw [W_mul, hgh, one_smul])

/-- `w g w h = -w (g + h)` when the phase is `-1`. -/
theorem w_mul_of_phase_eq_neg_one {g h : Label} (hgh : phase g h = -1) :
    w g * w h = -w (g + h) :=
  Subtype.ext (show W g * W h = -W (g + h) by rw [W_mul, hgh]; exact neg_one_smul ℂ (W (g + h)))

/-- `w g` is self-adjoint when `ω(g, g) = 1`. -/
theorem star_w_of_phase_eq_one {g : Label} (hg : phase g g = 1) : star (w g) = w g :=
  Subtype.ext (show star (W g) = W g by rw [star_W, hg, one_smul])

/-- **The Pauli sites of `pauliA`**: `x k = W (X_k)`, `z k = W (Z_k)`. -/
def pauliSites : PauliSites ↥pauliA where
  x k := w (xLabel k)
  z k := w (zLabel k)
  x_mul_self k := by
    rw [w_mul_of_phase_eq_one (phase_xLabel_left k _), label_add_self, w_zero]
  z_mul_self k := by
    rw [w_mul_of_phase_eq_one (phase_zLabel_right _ k), label_add_self, w_zero]
  z_mul_x k := by
    rw [w_mul_of_phase_eq_neg_one ((phase_zLabel_xLabel k k).trans (ite_eq_left rfl)),
      w_mul_of_phase_eq_one (phase_xLabel_left k _), add_comm]
  star_x k := star_w_of_phase_eq_one (phase_xLabel_left k _)
  star_z k := star_w_of_phase_eq_one (phase_zLabel_right _ k)
  commute_x_x k l _ := by
    change w _ * w _ = w _ * w _
    rw [w_mul_of_phase_eq_one (phase_xLabel_left k _),
      w_mul_of_phase_eq_one (phase_xLabel_left l _), add_comm]
  commute_x_z k l h := by
    change w _ * w _ = w _ * w _
    rw [w_mul_of_phase_eq_one (phase_xLabel_left k _),
      w_mul_of_phase_eq_one ((phase_zLabel_xLabel l k).trans (ite_eq_right h)), add_comm]
  commute_z_z k l _ := by
    change w _ * w _ = w _ * w _
    rw [w_mul_of_phase_eq_one (phase_zLabel_right _ l),
      w_mul_of_phase_eq_one (phase_zLabel_right _ k), add_comm]

/-- **The twisted Pauli algebra has unital dyadic matrix units** (`lem:pauli-algebra`), in
`pauliStd.A` itself: the units of its Pauli sites (`MIPRE.PauliSites.hasDyadicUnits`). -/
theorem pauliStd_hasDyadicUnits : HasDyadicUnits pauliStd.A := pauliSites.hasDyadicUnits

end MIPRE.Repetition.Pauli

end

end
