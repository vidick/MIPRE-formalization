/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Weyl
public import MIPRE.Foundations.PVM
public import MIPRE.Foundations.AncillaModel

@[expose] public section

/-!
# Exact Pauli observables from a simultaneous pair measurement

Blueprint `lem:qld-exact-paulis`, the part of it that is **exact**: given a projective measurement
`S` whose outcomes are *pairs* `(g_X, g_Z)` and a map `cd` sending an outcome to a vector of
`F_q^n`, the appendix builds binary observables on the enlarged space `dA (x) (C^q)^{(x) n}` which
satisfy the generalized Pauli relations with no error term at all. This file is that construction
and those relations.

Nothing here is approximate, and nothing here mentions the game: every statement is an identity
in the algebra, with `IsPVMIn S` and `IsWeylFamily w` the only hypotheses. That is the point ---
the blueprint's proof paragraph says exactness comes "from projectivity of the simultaneous
measurement together with the group law of the Pauli basis", and this file is the
formalization of exactly that sentence. `thm:linearity` is not used.

## Over a `⋆`-algebra

Stated in a bipartite model (Phase 5 of `planning/mipco-track.md`): the pair measurement is a
projective measurement `S : G × G → R` in any `⋆`-algebra `R` --- in use, a player's algebra of a
model, where `IsPVMIn` is what the strategy's projectivity supplies --- and the operators the
appendix writes on `dA (x) (C^q)^{(x) n}` are the `F_q^n × F_q^n` matrices over `R`, the register
the new outer index: an element `X` of `R` tensored with a matrix `P` of scalars on the register is
`smulKron X P` (`MIPRE/Foundations/AncillaModel.lean`), the adjoint is `star`, and a product of two
such tensors is taken factorwise by `smulKron_mul`. The matrix statements of the earlier version
are the instances `R = Matrix dA dA ℂ`, up to the register-outer layout of `smulKron`. Every
statement is still an exact identity, and nothing needs the algebra to be finite-dimensional.

## The construction

Write `pi` for one of the two projections `(g_X, g_Z) |→ g_W`. Then

* `sCoarse S pi g` is the `W`-marginal `S^W_g`, a projective measurement by `IsPVMIn.coarse`;
* `mTilde` is the appendix's `eq:tilde_M`,
  `M~^{W,u}_a = sum_g S^W_g (x) tau^W_{cd(g) . u + a}(u)`,
  where `tau^W_c(u)` is the syndrome projector `MIPRE.Weyl.syn w u c` --- the level set of the
  pairing with `u` --- so that `mTilde` is a projective measurement with outcomes in `F_q`;
* `wTilde` is `eq:def-tildewj`, the binary observable
  `W~^e(u) = sum_a (-1)^{tr(e a)} M~^{W,u}_a`, at a field element `e` (the appendix takes `e` in a
  self-dual basis of `F_q` over `F_2`, which this file does not need).

## The one identity everything follows from

`wTilde_eq`: the observable **factorizes**,

`W~^e(u) = pvmObs S (p |→ (-1)^{tr(e (cd (pi p) . u))})  (x)  w (e . u)`,

a signed sum of the *pair* measurement tensor a genuine Weyl operator. The `F_q`-valued syndrome
label is what makes this work: summing the syndrome projectors against the character of `a`
reassembles the Weyl operator on the line `r |→ r . u` (`MIPRE.Weyl.eq_sum_proj`), and the
`cd(g) . u` shift becomes the sign the first factor carries.

Self-adjointness (`wTilde_conjTranspose`) and involutivity (`wTilde_mul_self`) are then the
`pvmObs` calculus of `MIPRE/Foundations/Measurement.lean` on the left factor and the group law on
the right. The twisted commutation (`wTilde_mul_wTilde`) is the same: the two left factors are
weightings of *one* projective measurement, so they commute exactly (`IsPVMIn.pvmObs_comm`), and
the whole phase comes from the right factors' `MIPRE.Weyl.wX_mul_wZ`.

## A repair carried over from the paper

The pinned paper's display for the commutation relation used to split into `e != e'` (claiming
exact commutation) and `e = e'` (a phase). That is false: self-duality gives `tr(e_j e_{j'}) =
delta_{j j'}`, but `tr(e_j e_{j'} c)` need not vanish for `c` outside `F_2`, and the quantity in
the exponent is `e_j e_{j'} (u . v)` with `u . v` an arbitrary field element. The paper now states
the general phase, and `wTilde_mul_wTilde` below is that general phase --- with no case split, and
with no reference to a basis, since the relation holds for every pair of field elements.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

set_option linter.unusedSectionVars false

/-! ## Two small bilinearity facts

`trDot_smul` of `MIPRE/Foundations/Weyl.lean` pulls a scalar out of the *left* argument of the
form. Both of the following pull one out of the right, which is what the two observables'
arguments need. -/

/-- Scaling the right argument of the `F_q`-valued pairing pulls the scalar out. -/
theorem dotF_smul_right (r : F) (u v : n → F) : dotF u (r • v) = r * dotF u v := by
  rw [dotF, dotF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by
    show u l * (r * v l) = r * (u l * v l)
    ring

/-- **The form of two scaled vectors.** This is the exponent of the phase in
`wTilde_mul_wTilde`, and the reason it is symmetric in the two scalars. -/
theorem trDot_smul_smul (r r' : F) (u v : n → F) :
    trDot (r • u) (r' • v) = Algebra.trace (ZMod 2) F (r * r' * dotF u v) := by
  rw [trDot_smul, dotF_smul_right, mul_assoc]

/-- The form against a scaled vector, in the shape the phase function below is written in. -/
theorem trDot_smul_right (r : F) (u v : n → F) :
    trDot u (r • v) = Algebra.trace (ZMod 2) F (r * dotF u v) := by
  rw [trDot_comm, trDot_smul, dotF_comm]

/-! ## Bilinearity of the tensor sign over finite sums

The tensor sign is `smulKron`, and every displayed calculation below moves a sum across it, on
either side. These are `smulKron_sum_left` and `smulKron_sum_right` of
`MIPRE/Foundations/AncillaModel.lean` at the register of the construction; a scalar moves across
it in the same way (`smulKron_smul_left`, and `smulKron_smul_right` there). -/

/-- `(sum_x A x) (x) B = sum_x (A x (x) B)`. -/
theorem sum_kron {iota : Type*} (s : Finset iota) (A : iota → R)
    (B : Matrix (n → F) (n → F) ℂ) :
    smulKron (∑ x ∈ s, A x) B = ∑ x ∈ s, smulKron (A x) B :=
  smulKron_sum_left s A B

/-- `A (x) (sum_x B x) = sum_x (A (x) B x)`. -/
theorem kron_sum {iota : Type*} (s : Finset iota) (A : R)
    (B : iota → Matrix (n → F) (n → F) ℂ) :
    smulKron A (∑ x ∈ s, B x) = ∑ x ∈ s, smulKron A (B x) :=
  smulKron_sum_right A s B

/-- `(c X) (x) P = c (X (x) P)`. -/
theorem smulKron_smul_left {α : Type*} (c : ℂ) (X : R) (P : Matrix α α ℂ) :
    smulKron (c • X) P = c • smulKron X P := by
  ext a b
  rw [smulKron_apply, Matrix.smul_apply, smulKron_apply, smul_comm]

/-! ## The marginals of a pair measurement -/

/-- **A coarse-graining of a measurement along a map on its outcomes.** The two marginals of the
simultaneous pair measurement are this at `Prod.fst` and `Prod.snd`; `IsPVMIn.coarse` is what
makes each of them projective. -/
def sCoarse (S : G × G → R) (pi : G × G → G) (g : G) : R :=
  ∑ p ∈ univ.filter fun p => pi p = g, S p

theorem isPVM_sCoarse {S : G × G → R} (hS : IsPVMIn S) (pi : G × G → G) :
    IsPVMIn (sCoarse S pi) :=
  hS.coarse pi

/-- **Summing a family against the marginals is summing it against the measurement**, the label
read off through the projection. The fibrewise sum, stated once because both the definition of
`mTilde` and its factorization use it. -/
theorem sum_sCoarse_kron {S : G × G → R} (pi : G × G → G)
    (T : G → Matrix (n → F) (n → F) ℂ) :
    ∑ g, smulKron (sCoarse S pi g) (T g) = ∑ p, smulKron (S p) (T (pi p)) := by
  classical
  rw [show ∑ p, smulKron (S p) (T (pi p))
      = ∑ g, ∑ p ∈ univ.filter fun p => pi p = g, smulKron (S p) (T (pi p)) from
    (Finset.sum_fiberwise (univ : Finset (G × G)) pi fun p => smulKron (S p) (T (pi p))).symm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [sCoarse, sum_kron]
  exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]

/-! ## The measurement and the observable -/

variable (S : G × G → R) (pi : G × G → G) (cd : G → (n → F))
  (w : (n → F) → Matrix (n → F) (n → F) ℂ)

/-- **The appendix's `eq:tilde_M`.** `M~^{W,u}_a = sum_g S^W_g (x) tau^W_{cd(g) . u - a}(u)`; in
characteristic two the subtraction is the addition. -/
def mTilde (u : n → F) (a : F) : Matrix (n → F) (n → F) R :=
  ∑ g, smulKron (sCoarse S pi g) (syn w u (dotF (cd g) u + a))

/-- The same sum indexed by the *pair* outcomes, which is the form the factorization starts
from. -/
theorem mTilde_eq_sum (u : n → F) (a : F) :
    mTilde S pi cd w u a = ∑ p, smulKron (S p) (syn w u (dotF (cd (pi p)) u + a)) :=
  sum_sCoarse_kron pi _

/-- **The phase the first tensor factor carries**, `tr(e (cd(pi p) . u))`. -/
def cdPhase (e : F) (u : n → F) : G × G → ZMod 2 :=
  fun p => Algebra.trace (ZMod 2) F (e * dotF (cd (pi p)) u)

/-- **The appendix's `eq:def-tildewj`.** The binary observable obtained from `mTilde` by the
character of the field element `e`. -/
def wTilde (e : F) (u : n → F) : Matrix (n → F) (n → F) R :=
  ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a)) • mTilde S pi cd w u a

/-! ## The factorization

The whole content of the exactness claim. -/

/-- **The observable factorizes** as a signed sum of the pair measurement tensor a Weyl operator:
`W~^e(u) = pvmObs S ((-1)^{cdPhase}) (x) w (e . u)`.

The proof runs the appendix's displayed calculation backwards. Expanding `w (e . u)` in its own
spectral projectors (`eq_sum_proj`, which needs no group law) and grouping the eigenvalue patterns
by their pairing with `u` turns the right-hand side into a double sum over outcomes `p` and
syndromes `a`; the left-hand side is the same double sum after the substitution
`a |→ cd(pi p) . u + a`, which for each fixed `p` is a bijection of `F_q`. -/
theorem wTilde_eq (e : F) (u : n → F) :
    wTilde S pi cd w e u
      = smulKron (pvmObs S (fun p => sgn (cdPhase pi cd e u p))) (w (e • u)) := by
  -- the syndrome projector is the fibre of the spectral family over the pairing, by definition
  have hsyn : ∀ a : F, (∑ c ∈ univ.filter fun c => dotF c u = a, proj w c) = syn w u a :=
    fun _ => rfl
  -- expand the Weyl operator in its spectral projectors and group them by syndrome
  have hw : w (e • u) = ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a)) • syn w u a := by
    rw [eq_sum_proj (w := w) (e • u),
      ← Finset.sum_fiberwise (univ : Finset (n → F)) (fun c => dotF c u)
        fun c => sgn (trDot (e • u) c) • proj w c]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hsyn a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c hc => by
      rw [trDot_smul, dotF_comm, (Finset.mem_filter.mp hc).2]
  -- the right-hand side, as a double sum over outcomes and syndromes
  have hR : smulKron (pvmObs S (fun p => sgn (cdPhase pi cd e u p))) (w (e • u))
      = ∑ p, ∑ a : F, (sgn (cdPhase pi cd e u p)
          * sgn (Algebra.trace (ZMod 2) F (e * a))) • smulKron (S p) (syn w u a) := by
    rw [pvmObs, hw, sum_kron]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smulKron_smul_left, kron_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [smulKron_smul_right, smul_smul]
  -- the left-hand side, as the same double sum with the outcome-dependent shift
  have hL : wTilde S pi cd w e u
      = ∑ p, ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a))
          • smulKron (S p) (syn w u (dotF (cd (pi p)) u + a)) := by
    rw [wTilde, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mTilde_eq_sum, Finset.smul_sum]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- for each fixed outcome, translating the syndrome by `cd (pi p) . u` is a bijection of `F_q`
  refine Fintype.sum_bijective (fun a => dotF (cd (pi p)) u + a)
    (Equiv.addLeft (dotF (cd (pi p)) u)).bijective _ _ fun a => ?_
  congr 1
  simp only [cdPhase]
  rw [← sgn_add, ← map_add, ← mul_add, ← add_assoc, add_self, zero_add]

/-! ## The Pauli relations, exactly -/

variable {S pi cd w}

/-- **The observable is self-adjoint.** -/
theorem wTilde_conjTranspose [StarModule ℂ R] (hS : IsPVMIn S) (hw : IsWeylFamily w) (e : F)
    (u : n → F) :
    star (wTilde S pi cd w e u) = wTilde S pi cd w e u := by
  rw [wTilde_eq, star_smulKron, hw.selfAdjoint, hS.pvmObs_star_eq fun p => star_sgn _]

/-- **The observable squares to the identity**, so it is a genuine `+-1`-valued observable. The
left factor squares to one because the signs do and the measurement is projective; the right
factor because `w (e . u) w (e . u) = w (e . u + e . u) = w 0 = 1`. -/
theorem wTilde_mul_self (hS : IsPVMIn S) (hw : IsWeylFamily w) (e : F) (u : n → F) :
    wTilde S pi cd w e u * wTilde S pi cd w e u = 1 := by
  rw [wTilde_eq, smulKron_mul, hS.pvmObs_mul_self fun p => sgn_mul_self _,
    ← hw.map_add, add_self_vec, hw.map_zero, smulKron_one_one]

/-- **The exact twisted commutation relation.**
`X~^e(u) Z~^{e'}(v) = (-1)^{tr(e e' (u . v))} Z~^{e'}(v) X~^e(u)`,
for every pair of field elements and every pair of vectors, with no case split.

Both sides factorize by `wTilde_eq`. The left factors are weightings of the *same* projective
measurement `S`, so they commute exactly whatever the two projections `pi` and `pi'` are
(`IsPVMIn.pvmObs_comm`) --- this is where projectivity of the simultaneous measurement is used,
and it is the only place. The entire phase is then the Weyl families' own
`(-1)^{tr((e . u) . (e' . v))}`, which `trDot_smul_smul` rewrites as the displayed exponent. -/
theorem wTilde_mul_wTilde (hS : IsPVMIn S) {pi pi' : G × G → G} (e e' : F) (u v : n → F) :
    wTilde S pi cd wX e u * wTilde S pi' cd wZ e' v
      = sgn (Algebra.trace (ZMod 2) F (e * e' * dotF u v))
        • (wTilde S pi' cd wZ e' v * wTilde S pi cd wX e u) := by
  rw [wTilde_eq, wTilde_eq, smulKron_mul, smulKron_mul, wX_mul_wZ, trDot_smul_smul,
    hS.pvmObs_comm (fun p => sgn (cdPhase pi cd e u p))
      (fun p => sgn (cdPhase pi' cd e' v p)), smulKron_smul_right]

end MIPRE.QLD

end

end
