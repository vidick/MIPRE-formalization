/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Background.Tailored.AnswerReduction.SoundExtract

@[expose] public section

/-!
# Soundness of the answer-reduced game: the point relations

The relations between the measurements of the strategy `T` and the polynomial measurements of
`SoundExtract`, on the common index `(z, w)` of a seed of the input sampler and a vector of the
low-degree test's registers, both uniform. Every relation is a disagreement
(`BipartiteModel.dis`) between a family of Alice's measurements and a family of Bob's.

* **From the typed game** (`sum_dis_edge_le`): at one type pair, a check forcing two readings of
  the answers to agree bounds their disagreement by the failure there, `81` times the typed
  failure after summing. The consistency check (II:10449, check 2) at two point questions, one
  of an isolated role and one of the oracle, forces the role's point values to be the oracle's
  at the role's slots (`pvR_eq_pvO_of_arDt`).
* **From the extraction** (`sum_dis_MA_GB_le`, `sum_dis_GA_MB_le`, `sum_dis_GA_GB_le`): the three
  conclusions of the seeded test's soundness, the uniform point of the test read off the
  registers of a uniform vector (`LIDT.CL.Regs.sum_ptOf_le`), averaged over the seeds.

They chain across the two players (`BipartiteModel.sum_dis_triangle`): an isolated role's
polynomials evaluated at the point against the oracle's at the role's slots, both ways
(`sum_dis_GAr_GBO_le`, `sum_dis_GAO_GBr_le`). This is the paper's comparison of `ℋ^{(A,x)}` with
`ℋ^{(O,z)}_{[Restrict_1]}` (II:10703), before Schwartz–Zippel.
-/

noncomputable section

namespace MIPRE.Tailored.AnsRed.Typed

open Finset MIPRE.CL MIPRE.SAT MIPRE.LIDT

/-! ## Readings -/

section Readings

variable {t : ℕ} {ht : 1 ≤ t} {j d : ℕ} {L : PcpDims}

variable (t ht j d) in
/-- The value of the `c`-th codeword of a point answer. -/
def pv {B : ℕ} (c : ℕ) (a : Verifier.Answers B) : Fq t ht := cw t ht j d .point a.1 c 0

variable (t ht j d L) in
/-- The values of a role's codewords in a point answer. -/
def pvR {B : ℕ} (r : Role) (a : Verifier.Answers B) : Fin (slotsOf L r).length → Fq t ht :=
  fun c => pv t ht j d c a

variable (L) in
/-- The oracle's codeword in the slot of a role's codeword. -/
def oc (r : Role) (c : Fin (slotsOf L r).length) : Fin (slotsOf L .oracle).length :=
  ⟨idxO ((slotsOf L r).get c), idxO_lt _⟩

variable (t ht j d L) in
/-- The values of an oracle point answer in a role's slots. -/
def pvO {B : ℕ} (r : Role) (a : Verifier.Answers B) : Fin (slotsOf L r).length → Fq t ht :=
  fun c => pvR t ht j d L .oracle a (oc L r c)

/-- The evaluations at a point of a tuple of polynomials. -/
def evalR {k : ℕ} (u : Fin (2 ^ j) → Fq t ht)
    (g : Fin k → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)) : Fin k → Fq t ht :=
  fun c => (g c).eval u

variable (L) in
/-- An oracle's polynomials in a role's slots. -/
def restr (r : Role) (f : PolyR t ht j d L .oracle) : PolyR t ht j d L r := fun c => f (oc L r c)

/-- The reading of a tuple at a role's slots. -/
def selR {X : Type*} (r : Role) (v : Fin (slotsOf L .oracle).length → X) :
    Fin (slotsOf L r).length → X :=
  fun c => v (oc L r c)

theorem evalR_restr (r : Role) (u : Fin (2 ^ j) → Fq t ht) (f : PolyR t ht j d L .oracle) :
    evalR u (restr L r f) = selR r (evalR u f) := rfl

theorem pvO_eq {B : ℕ} (r : Role) (a : Verifier.Answers B) :
    pvO t ht j d L r a = selR r (pvR t ht j d L .oracle a) := rfl

end Readings

/-! ## The relations -/

variable {𝒞 𝒜 ℬ : Type*} [Ring 𝒞] [StarRing 𝒞] [Algebra ℂ 𝒞] [Ring 𝒜] [StarRing 𝒜]
  [Algebra ℂ 𝒜] [Ring ℬ] [StarRing ℬ] [Algebra ℂ ℬ] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [PartialOrder ℬ] [StarOrderedRing ℬ] {M : BipartiteModel 𝒞 𝒜 ℬ}
variable {t : ℕ} {ht : 1 ≤ t} {j : ℕ} {d : ℕ} {hM : 2 ^ j ∣ Fintype.card (Fq t ht)}
  {sel : LIDT.CL.Sel (Fq t ht) (2 ^ j) hM} {L : PcpDims} {hLM : L.m ≤ 2 ^ j}
  {ℓV : ℕ} {V : TailoredVerifier ℓV} {n : ℕ} {Cc : V.Questions n → Circuit}
  {hm : ∀ z, (Cc z).inputs + (Cc z).size = L.m} {ℓ : ℕ}
  {P : Bool → Role × LIDT.CL.Ty → CLFun (ZMod 2) (Fin (V.sampler.dim n + D j * t)) ℓ} {B : ℕ}

open Classical in
/-- **What acceptance by the typed data says**: the four checks on the field elements. -/
theorem arPred_of_arDt
    {u v : CL.Detyping.Question (Role × LIDT.CL.Ty) (Fin (V.sampler.dim n + D j * t))}
    {a b : Verifier.Answers B} (h : arDt d hM sel L hLM V n Cc hm B u v a b = true) :
    ArPred t ht j d L (V.sampler.dim n) sel hLM (circOf L V n Cc hm) u v a.1 b.1 :=
  ((accepts_iff t ht j d L _ sel hLM _ u v a.1 b.1).1 (of_decide_eq_true h)).2.2

/-- **The consistency check**, an isolated role's point against the oracle's: the role's point
values are the oracle's in the role's slots. -/
theorem pvR_eq_pvO_of_arDt {r : Role} (hr : r ≠ .oracle) {z : V.Questions n}
    {w : Fin (D j) → Fq t ht} {a b : Verifier.Answers B}
    (h : arDt d hM sel L hLM V n Cc hm B (arQr sel _ r (oq V n r z) (ldq sel .point w))
      (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w)) a b = true) :
    pvR t ht j d L r a = pvO t ht j d L r b := by
  have h2 := (arPred_of_arDt h).2.1 rfl
  funext c
  cases r with
  | oracle => exact absurd rfl hr
  | alice => exact h2 c 0 Nat.one_pos
  | bob => exact h2 c 0 Nat.one_pos

/-- **The consistency check**, the oracle's point against an isolated role's. -/
theorem pvO_eq_pvR_of_arDt {r : Role} (hr : r ≠ .oracle) {z : V.Questions n}
    {w : Fin (D j) → Fq t ht} {a b : Verifier.Answers B}
    (h : arDt d hM sel L hLM V n Cc hm B (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))
      (arQr sel _ r (oq V n r z) (ldq sel .point w)) a b = true) :
    pvO t ht j d L r a = pvR t ht j d L r b := by
  have h2 := (arPred_of_arDt h).2.1 rfl
  funext c
  cases r with
  | oracle => exact absurd rfl hr
  | alice => exact (h2 c 0 Nat.one_pos).symm
  | bob => exact (h2 c 0 Nat.one_pos).symm

variable (T : M.ProjStrat (arGame d hM sel L hLM V n Cc hm P B)) (hL : LIDT.Simul.SoundIn M)
  (hd : 1 ≤ d) (hP : ArSampler hM sel V n P)

include hP in
/-- **One type pair bounds a summed disagreement**: at most `81` times the typed failure, per
seed. -/
theorem sum_dis_edge_le (uv : (Role × LIDT.CL.Ty) × (Role × LIDT.CL.Ty)) {C : Type*} [Fintype C]
    [DecidableEq C] (f g : V.Questions n → (Fin (D j) → Fq t ht) → Verifier.Answers B → C)
    (hD : ∀ z w a b, arDt d hM sel L hLM V n Cc hm B
      (arQr sel _ uv.1.1 (oq V n uv.1.1 z) (ldq sel uv.1.2 w))
      (arQr sel _ uv.2.1 (oq V n uv.2.1 z) (ldq sel uv.2.2 w)) a b = true → f z w a = g z w b) :
    ∑ z, ∑ w, M.dis ((T.PA (arQr sel _ uv.1.1 (oq V n uv.1.1 z) (ldq sel uv.1.2 w))).map (f z w))
        ((T.PB (arQr sel _ uv.2.1 (oq V n uv.2.1 z) (ldq sel uv.2.2 w))).map (g z w))
      ≤ 81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht)) *
        (1 - T.value) :=
  le_trans (Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun w _ =>
    M.dis_map_le_condFail (f z w) (g z w) (hD z w)) (sum_edge_le T hP uv)

theorem tuplePOVMA_roleStrat (r : Role) (y : V.Questions n) (u : Fin (2 ^ j) → Fq t ht) :
    Simul.tuplePOVMAIn hM (roleStrat T r y) u =
      (T.PA (arQr sel _ r y (.point u))).map (pvR t ht j d L r) := by
  unfold Simul.tuplePOVMAIn roleStrat BipartiteModel.ProjStrat.adapt
  rw [POVMIn.map_map]
  rfl

theorem tuplePOVMB_roleStrat (r : Role) (y : V.Questions n) (u : Fin (2 ^ j) → Fq t ht) :
    Simul.tuplePOVMBIn hM (roleStrat T r y) u =
      (T.PB (arQr sel _ r y (.point u))).map (pvR t ht j d L r) := by
  unfold Simul.tuplePOVMBIn roleStrat BipartiteModel.ProjStrat.adapt
  rw [POVMIn.map_map]
  rfl

theorem evalTuplePOVMIn_eq {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    {k : ℕ} (G : POVMIn (Fin k → LowIndDegPoly (F := Fq t ht) (m := 2 ^ j) (d := d)) R)
    (u : Fin (2 ^ j) → Fq t ht) : Simul.evalTuplePOVMIn G u = G.map (evalR u) := rfl

include hP in
/-- **Averaging over the seeds**: a per-seed bound by the error at the seed's oracularized
question becomes a bound by the error at `9` times the typed failure. -/
theorem sum_le_of_dS (r : Role) (F : V.Questions n → (Fin (D j) → Fq t ht) → ℝ)
    (hF : ∀ z, ∑ w, F z w ≤ Fintype.card (Fin (D j) → Fq t ht) *
      dS t ht j d L r (epsR T r (oq V n r z))) :
    ∑ z, ∑ w, F z w ≤ Fintype.card (V.Questions n) *
      (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L r (9 * (1 - T.value))) := by
  calc ∑ z, ∑ w, F z w
      ≤ ∑ z, (Fintype.card (Fin (D j) → Fq t ht) : ℝ) *
          dS t ht j d L r (epsR T r (oq V n r z)) := Finset.sum_le_sum fun z _ => hF z
    _ = (Fintype.card (Fin (D j) → Fq t ht) : ℝ) *
          ∑ z, dS t ht j d L r (epsR T r (oq V n r z)) := by rw [Finset.mul_sum]
    _ ≤ (Fintype.card (Fin (D j) → Fq t ht) : ℝ) *
          (Fintype.card (V.Questions n) * dS t ht j d L r (9 * (1 - T.value))) :=
        mul_le_mul_of_nonneg_left (sum_deltaSimR_le T hP r) (by positivity)
    _ = _ := by ring

include hP in
/-- **Alice's point against Bob's polynomials**, from the extraction. -/
theorem sum_dis_MA_GB_le (r : Role) :
    ∑ z, ∑ w, M.dis ((T.PA (arQr sel _ r (oq V n r z) (ldq sel .point w))).map
        (pvR t ht j d L r)) ((GB T hL hd r (oq V n r z)).map (evalR ((regs j).ptOf w)))
      ≤ Fintype.card (V.Questions n) *
        (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L r (9 * (1 - T.value))) := by
  refine sum_le_of_dS T hP r _ fun z => ?_
  have h2 := M.sum_dis_le_of_inconsistency T.ψ_unit _ _ (extR_spec T hL hd r (oq V n r z)).1
  refine LIDT.CL.Regs.sum_ptOf_le (regs j) (fun u => M.dis ((T.PA (arQr sel _ r (oq V n r z)
    (.point u))).map (pvR t ht j d L r)) ((GB T hL hd r (oq V n r z)).map (evalR u))) ?_
  simpa only [tuplePOVMA_roleStrat, evalTuplePOVMIn_eq] using h2

include hP in
/-- **Alice's polynomials against Bob's point**, from the extraction. -/
theorem sum_dis_GA_MB_le (r : Role) :
    ∑ z, ∑ w, M.dis ((GA T hL hd r (oq V n r z)).map (evalR ((regs j).ptOf w)))
        ((T.PB (arQr sel _ r (oq V n r z) (ldq sel .point w))).map (pvR t ht j d L r))
      ≤ Fintype.card (V.Questions n) *
        (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L r (9 * (1 - T.value))) := by
  refine sum_le_of_dS T hP r _ fun z => ?_
  have h2 := M.sum_dis_le_of_inconsistency T.ψ_unit _ _ (extR_spec T hL hd r (oq V n r z)).2.1
  refine LIDT.CL.Regs.sum_ptOf_le (regs j) (fun u => M.dis
    ((GA T hL hd r (oq V n r z)).map (evalR u))
    ((T.PB (arQr sel _ r (oq V n r z) (.point u))).map (pvR t ht j d L r))) ?_
  simpa only [tuplePOVMB_roleStrat, evalTuplePOVMIn_eq] using h2

include hP in
/-- **The two polynomial measurements against each other**, from the extraction. -/
theorem sum_dis_GA_GB_le (r : Role) :
    ∑ z, M.dis (GA T hL hd r (oq V n r z)) (GB T hL hd r (oq V n r z))
      ≤ Fintype.card (V.Questions n) * dS t ht j d L r (9 * (1 - T.value)) := by
  refine le_trans (Finset.sum_le_sum fun z _ => ?_) (sum_deltaSimR_le T hP r)
  have h3 := (extR_spec T hL hd r (oq V n r z)).2.2
  rwa [M.inconsistency_uniform_unit T.ψ_unit] at h3

/-! ## The isolated roles against the oracle -/

include hP in
/-- **An isolated role's polynomials against the oracle's in its slots**, evaluated at the point:
through Bob's point at the role, Alice's point at the oracle, and the consistency check. -/
theorem sum_dis_GAr_GBO_le {r : Role} (hr : r ≠ .oracle) :
    ∑ z, ∑ w, M.dis ((GA T hL hd r (oq V n r z)).map (evalR ((regs j).ptOf w)))
        ((GB T hL hd .oracle (oq V n .oracle z)).map
          fun f => evalR ((regs j).ptOf w) (restr L r f))
      ≤ 11 * (Fintype.card (V.Questions n) *
          (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L r (9 * (1 - T.value)))
        + 81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht)) *
          (1 - T.value)
        + Fintype.card (V.Questions n) *
          (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L .oracle (9 * (1 - T.value)))) := by
  have hAB := sum_dis_GA_MB_le T hL hd hP r
  have hCB := sum_dis_edge_le T hP ((.oracle, .point), (r, .point))
    (fun _ _ => pvO t ht j d L r) (fun _ _ => pvR t ht j d L r)
    fun _ _ _ _ h => pvO_eq_pvR_of_arDt hr h
  have hCD : ∑ z, ∑ w, M.dis ((T.PA (arQr sel _ .oracle (oq V n .oracle z)
        (ldq sel .point w))).map (pvO t ht j d L r))
        ((GB T hL hd .oracle (oq V n .oracle z)).map
          fun f => evalR ((regs j).ptOf w) (restr L r f))
      ≤ Fintype.card (V.Questions n) *
        (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L .oracle (9 * (1 - T.value))) := by
    refine le_trans (Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun w _ => ?_)
      (sum_dis_MA_GB_le T hL hd hP .oracle)
    have e1 : (T.PA (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
        (pvO t ht j d L r) = ((T.PA (arQr sel _ .oracle (oq V n .oracle z)
          (ldq sel .point w))).map (pvR t ht j d L .oracle)).map (selR r) := by
      rw [POVMIn.map_map]; rfl
    have e2 : (GB T hL hd .oracle (oq V n .oracle z)).map
        (fun f => evalR ((regs j).ptOf w) (restr L r f)) =
        ((GB T hL hd .oracle (oq V n .oracle z)).map (evalR ((regs j).ptOf w))).map
          (selR r) := by
      rw [POVMIn.map_map]; rfl
    rw [e1, e2]
    exact M.dis_map_le _ _ _
  have h := M.sum_dis_triangle T.ψ_unit
    (fun x : V.Questions n × (Fin (D j) → Fq t ht) =>
      (GA T hL hd r (oq V n r x.1)).map (evalR ((regs j).ptOf x.2)))
    (fun x => (T.PA (arQr sel _ .oracle (oq V n .oracle x.1)
      (ldq sel .point x.2))).map (pvO t ht j d L r))
    (fun x => (T.PB (arQr sel _ r (oq V n r x.1) (ldq sel .point x.2))).map (pvR t ht j d L r))
    (fun x => (GB T hL hd .oracle (oq V n .oracle x.1)).map
      fun f => evalR ((regs j).ptOf x.2) (restr L r f))
  simp only [Fintype.sum_prod_type] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  exact add_le_add (add_le_add hAB hCB) hCD

include hP in
/-- **The oracle's polynomials in an isolated role's slots against the role's**, evaluated at the
point: through Bob's point at the oracle, Alice's point at the role, and the consistency check. -/
theorem sum_dis_GAO_GBr_le {r : Role} (hr : r ≠ .oracle) :
    ∑ z, ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
          fun f => evalR ((regs j).ptOf w) (restr L r f))
        ((GB T hL hd r (oq V n r z)).map (evalR ((regs j).ptOf w)))
      ≤ 11 * (Fintype.card (V.Questions n) *
          (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L .oracle (9 * (1 - T.value)))
        + 81 * (Fintype.card (V.Questions n) * Fintype.card (Fin (D j) → Fq t ht)) *
          (1 - T.value)
        + Fintype.card (V.Questions n) *
          (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L r (9 * (1 - T.value)))) := by
  have hAB : ∑ z, ∑ w, M.dis ((GA T hL hd .oracle (oq V n .oracle z)).map
        fun f => evalR ((regs j).ptOf w) (restr L r f))
        ((T.PB (arQr sel _ .oracle (oq V n .oracle z)
          (ldq sel .point w))).map (pvO t ht j d L r))
      ≤ Fintype.card (V.Questions n) *
        (Fintype.card (Fin (D j) → Fq t ht) * dS t ht j d L .oracle (9 * (1 - T.value))) := by
    refine le_trans (Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun w _ => ?_)
      (sum_dis_GA_MB_le T hL hd hP .oracle)
    have e1 : (T.PB (arQr sel _ .oracle (oq V n .oracle z) (ldq sel .point w))).map
        (pvO t ht j d L r) = ((T.PB (arQr sel _ .oracle (oq V n .oracle z)
          (ldq sel .point w))).map (pvR t ht j d L .oracle)).map (selR r) := by
      rw [POVMIn.map_map]; rfl
    have e2 : (GA T hL hd .oracle (oq V n .oracle z)).map
        (fun f => evalR ((regs j).ptOf w) (restr L r f)) =
        ((GA T hL hd .oracle (oq V n .oracle z)).map (evalR ((regs j).ptOf w))).map
          (selR r) := by
      rw [POVMIn.map_map]; rfl
    rw [e1, e2]
    exact M.dis_map_le _ _ _
  have hCB := sum_dis_edge_le T hP ((r, .point), (.oracle, .point))
    (fun _ _ => pvR t ht j d L r) (fun _ _ => pvO t ht j d L r)
    fun _ _ _ _ h => pvR_eq_pvO_of_arDt hr h
  have hCD := sum_dis_MA_GB_le T hL hd hP r
  have h := M.sum_dis_triangle T.ψ_unit
    (fun x : V.Questions n × (Fin (D j) → Fq t ht) =>
      (GA T hL hd .oracle (oq V n .oracle x.1)).map
        fun f => evalR ((regs j).ptOf x.2) (restr L r f))
    (fun x => (T.PA (arQr sel _ r (oq V n r x.1) (ldq sel .point x.2))).map (pvR t ht j d L r))
    (fun x => (T.PB (arQr sel _ .oracle (oq V n .oracle x.1)
      (ldq sel .point x.2))).map (pvO t ht j d L r))
    (fun x => (GB T hL hd r (oq V n r x.1)).map (evalR ((regs j).ptOf x.2)))
  simp only [Fintype.sum_prod_type] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  exact add_le_add (add_le_add hAB hCB) hCD

end MIPRE.Tailored.AnsRed.Typed

end
