/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.LenProg
public import MIPRE.Tailored.Repeat.DomTools

@[expose] public section

/-!
# The running time of the repeated answer-length calculator

`repLen_timeBound`: with the input sampler and calculator within `R` at index `n`, the repeated
calculator halts on every input `(n, d)` within `c (W + 1)^m (|d| + 1)^{e (R.k + 1)}`, for a
bound `W` on the parameters (`LenDom`) and constants `c, m, e` independent of everything. The
proof follows the stages of `lenCore_runsLe`: the calls to the input programs are bounded by
their time bounds through the universal machine, every query to the calculator being of size
linear in `|d|` (`size_lenQs_le`), and the polynomial-time stages by `dom_poly`.
-/

namespace MIPRE.Tailored.RepProg

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL Calls Repeat

/-! ## Sizes -/

theorem length_rawList_le : ∀ d : Data, (Detyping.Program.rawList d).length ≤ d.size
  | .nil => by simp [Detyping.Program.rawList]
  | .cons a b => by
    have := length_rawList_le b
    simp only [Detyping.Program.rawList, List.length_cons, size_cons]
    omega

theorem size_treeHead_le (d : Data) : (treeHead d).size ≤ d.size := by
  cases d with
  | nil => exact le_rfl
  | cons a b => simp only [treeHead_cons, size_cons]; omega

theorem length_readQ_le (d : Data) : (readQ d).length ≤ d.size := by
  unfold readQ Detyping.Program.readBits
  simp only [comp_apply, map_apply, ofEncodeEq_apply, List.length_map]
  exact (length_rawList_le _).trans (size_treeHead_le d)

/-- Every query to the input calculator is `(n, xᵢ, κ)` with `xᵢ` a block of the question, of
size linear in the input. -/
theorem mem_lenQs {n : ℕ} {d : Data} {s k : ℕ} {q : Data} (hq : q ∈ lenQs n d s k) :
    ∃ (xi : BitStr) (b : Bool), q = encode (n, xi, b) ∧ esize xi ≤ 4 * d.size + 1 := by
  unfold lenQs lenQueries at hq
  rw [List.mem_append, List.mem_map, List.mem_map] at hq
  have key : ∀ xi ∈ blocks (readQ d) s k, esize xi ≤ 4 * d.size + 1 := by
    intro xi hxi
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hxi
    refine (esize_bitStr_le _).trans ?_
    have h1 : (Cost.Data.chunk s i (readQ d)).length ≤ (readQ d).length := by
      simp only [Cost.Data.chunk, List.length_take, List.length_drop]; omega
    have := length_readQ_le d
    omega
  rcases hq with ⟨xi, hxi, rfl⟩ | ⟨xi, hxi, rfl⟩
  · exact ⟨xi, false, rfl, key xi hxi⟩
  · exact ⟨xi, true, rfl, key xi hxi⟩

theorem length_lenQs (n : ℕ) (d : Data) (s k : ℕ) : (lenQs n d s k).length = 2 * k := by
  simp [lenQs, lenQueries]; omega

theorem esize_bool_le (b : Bool) : esize b ≤ 3 := by cases b <;> simp

theorem esize_dimension : esize CL.Sampler.Query.dimension ≤ 20 := by decide

/-! ## The cost of the core, dominated -/

/-- **The cost of the core is dominated**, given dominations of the dimension query's cost `Td`,
the calls' cost `T`, and the bound `Z` on the last loop. -/
theorem dom_lenCoreCost (cd md ed cT mT eT cZ mZ eZ : ℕ) : ∃ c m e, ∀ (W X K : ℕ)
    {sp lp : Prog} {lam tau n : ℕ} {d : Data} {s k Td T Z : ℕ} {rs : List Data},
    1 ≤ X → 1 ≤ W → d.size + 1 ≤ X → esize sp ≤ W → esize lp ≤ W → lam ≤ W → tau ≤ W → n ≤ W →
    s ≤ W → k ≤ W → Dom W X K cd md ed Td → Dom W X K cT mT eT T → Dom W X K cZ mZ eZ Z →
    (list (lenQs n d s k)).size ≤ Z → (list rs).size ≤ Z →
    Dom W X K c m e (lenCoreCost sp lp lam tau n d s k Td T Z rs) := by
  obtain ⟨cA, mA, eA, hA⟩ := dom_poly lenA.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cB, mB, eB, hB⟩ := dom_poly lenB.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cC, mC, eC, hC⟩ := dom_poly lenC.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cD, mD, eD, hD⟩ := dom_poly lenD.timeBound (30 + 10 + 30) 1 1
  obtain ⟨cE, mE, eE, hE⟩ := dom_poly lenE.timeBound (30 + 10 + 30 + cZ) (max 1 mZ) (max 1 eZ)
  obtain ⟨cu, mu, eu, hu⟩ := dom_toUnaryCost
  obtain ⟨cdm, mdm, edm, hdm⟩ := dom_dimCost
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_mapCallCost 1 0 0 cd md ed (30 + 10 + 30) 1 1 (30 + 10 + 30) 1 1
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_mapCallCost (30 + 10 + 30) 1 1 cT mT eT (30 + 10 + 30) 1 1 cZ mZ eZ
  exact ⟨_, _, _, fun W X K {sp lp lam tau n d s k Td T Z rs} hX hW1 hd hsp hlp hlam htau hn hs hk
      hTd hT hZ hqs hrs => by
    have small : ∀ {y : ℕ}, y ≤ 30 * W + 10 * X + 30 → Dom W X K (30 + 10 + 30) 1 1 y :=
      fun hy => Dom.ofLin hX hy
    have elam := esize_nat_le' lam
    have etau := esize_nat_le' tau
    have en := esize_nat_le' n
    have es := esize_nat_le' s
    have ek := esize_nat_le' k
    have e1 : esize (1 : ℕ) ≤ 5 := by decide
    have edim := esize_dimension
    have hκ := esize_bool_le (readK d)
    have hlen := length_lenQs n d s k
    have ea : esize ((((sp, lp, lam, tau) : LenPar), n, d) : LenIn) ≤ 14 * W + X + 8 := by
      simp only [esize_prod, esize_data]; omega
    have eqd : (encode (n, CL.Sampler.Query.dimension) : Data).size ≤ 4 * W + 22 := by
      change esize (n, CL.Sampler.Query.dimension) ≤ _
      simp only [esize_prod]; omega
    have es' : (encode s : Data).size ≤ 4 * W + 1 := by change esize s ≤ _; omega
    have ek' : (encode k : Data).size ≤ 4 * W + 1 := by change esize k ≤ _; omega
    have hsp' : (encode sp : Data).size ≤ W := hsp
    have hlp' : (encode lp : Data).size ≤ W := hlp
    have eus : esize (((((sp, lp, lam, tau) : LenPar), n, d) : LenIn), unary s) ≤ 16 * W + X + 10 := by
      rw [esize_prod, esize_unary]; omega
    have hrs' : esize rs ≤ Z := hrs
    -- the ten terms
    have t1 := hA W X K hX (small (y := esize ((((sp, lp, lam, tau) : LenPar), n, d) : LenIn))
      (by omega))
    have t2a := small (y := (encode ((((sp, lp, lam, tau) : LenPar), n, d) : LenIn) : Data).size)
      (by change esize _ ≤ _; omega)
    have t2b := small (y := (Data.cons (encode sp)
      (list [(encode (n, CL.Sampler.Query.dimension) : Data)])).size)
      (by simp only [size_cons, size_list_cons, list_nil, size_nil]; omega)
    have t2c := h₁ W X K (M := 1) (T := Td) (C := (encode sp : Data).size)
      (Z := (list [(encode (n, CL.Sampler.Query.dimension) : Data)]).size +
        (list [(encode s : Data)]).size + 1) hX (Dom.const 1) hTd
      (small (by omega))
      (small (by simp only [size_list_cons, list_nil, size_nil]; omega))
    have t3 := hB W X K hX (small (y := esize ((((((sp, lp, lam, tau) : LenPar), n, d) : LenIn)),
      [(encode s : Data)])) (by
        simp only [esize_prod, esize_data]
        change _ + (list [(encode s : Data)]).size + 1 ≤ _
        simp only [size_list_cons, list_nil, size_nil]; omega))
    have t4a := small (y := (encode s : Data).size) (by omega)
    have t4b := hu W X K hX hs
    have t5 := hC W X K hX (small (y := esize (((((sp, lp, lam, tau) : LenPar), n, d) : LenIn),
      unary s)) (by omega))
    have t6a := small (y := (encode (((((sp, lp, lam, tau) : LenPar), n, d) : LenIn), unary s) :
      Data).size) (by change esize _ ≤ _; omega)
    have t6b := small (y := (encode ((1 : ℕ), lam, n, tau) : Data).size)
      (by change esize _ ≤ _; simp only [esize_prod]; omega)
    have t6c := hdm W X K hX htau (L := Nat.size lam + Nat.size n) (Λ := esize lam) (N := esize n)
      (Ssz := esize (1 : ℕ)) (by have := nat_size_le_self lam; have := nat_size_le_self n; omega)
      (by omega) (by omega) (by omega)
    have t7a := small (y := (encode k : Data).size) (by omega)
    have t7b := hu W X K hX hk
    have t8 := hD W X K hX (small (y := esize ((((((sp, lp, lam, tau) : LenPar), n, d) : LenIn),
      unary s), unary k)) (by rw [esize_prod, esize_unary]; omega))
    have t9a := small (y := (encode (readK d, unary k) : Data).size)
      (by change esize _ ≤ _; simp only [esize_prod, esize_unary]; omega)
    have t9b : Dom W X K _ _ _ (Data.cons (encode lp) (list (lenQs n d s k))).size :=
      ((small (y := esize lp + 1) (by omega)).add hX hZ).of_le
        (by simp only [size_cons]; have : (encode lp : Data).size = esize lp := rfl; omega)
    have t9c := h₂ W X K (M := (lenQs n d s k).length) (T := T) (C := (encode lp : Data).size)
      (Z := Z) hX (small (by omega)) hT (small (by omega)) hZ
    have t10 := hE W X K hX (y := esize ((readK d, unary k), rs))
      (((small (y := esize (readK d) + (2 * k + 1) + 2) (by omega)).add hX hZ).of_le
        (by simp only [esize_prod, esize_unary]; omega))
    have u2 := ((t2a.add hX t2b).add hX t2c).add hX (Dom.const 5)
    have u4 := ((t2a.add hX t4a).add hX t4b).add hX (Dom.const 5)
    have u6 := ((t6a.add hX t6b).add hX (t6c.add hX (Dom.const 3))).add hX (Dom.const 5)
    have u7 := ((t6a.add hX t7a).add hX t7b).add hX (Dom.const 5)
    have u9 := ((t9a.add hX t9b).add hX t9c).add hX (Dom.const 5)
    have v1 := (((t1.add hX u2).add hX t3).add hX u4).add hX t5
    have v2 := (((v1.add hX u6).add hX u7).add hX t8).add hX u9
    refine ((v2.add hX t10).add hX (Dom.const 9)).of_le ?_
    dsimp only [lenCoreCost]
    omega⟩

/-! ## The time bound -/

/-- The parameters of the repeated calculator at index `n`, bounded by `W`. -/
structure LenDom {ℓ : ℕ} (S : CL.Sampler ℓ) (L : Decider) (lam tau n : ℕ) (R : Budget)
    (W : ℕ) : Prop where
  S_le : R.S ≤ W
  D_le : R.D ≤ W
  lam_le : lam ≤ W
  tau_le : tau ≤ W
  n_le : n ≤ W
  sizeS_le : esize S.prog ≤ W
  sizeL_le : esize L.prog ≤ W
  pow_le : 10 ^ R.k ≤ W
  reps_le : Repetition.reps lam tau n ≤ W
  dim_le : S.dim n ≤ W

theorem size_encode_dimension : (encode CL.Sampler.Query.dimension : Data).size = 9 := by decide

/-- The dimension query through the universal machine, within its bound. -/
theorem dim_univ_le {ℓ : ℕ} (S : CL.Sampler ℓ) (n : ℕ) (R : Budget) (hS : S.TimeBoundAt n R.S R.k) :
    RunsLe selfUniversal.univ (.cons (encode S.prog) (encode (n, CL.Sampler.Query.dimension)))
      (encode (S.dim n))
      (selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k)) := by
  obtain ⟨r, t, ht, hrun⟩ := hS (encode CL.Sampler.Query.dimension)
  obtain ⟨t₀, h₀⟩ := S.runs_dimension n
  obtain ⟨rfl, -⟩ := Eval.deterministic hrun h₀
  obtain ⟨t', ht', hu⟩ := selfUniversal.time_le _ _ _ _ h₀
  refine ⟨t', ht'.trans (polynomial_eval_mono _ ?_), hu⟩
  rw [size_encode_dimension, show (9 : ℕ) + 1 = 10 from rfl] at ht
  have : (encode (n, CL.Sampler.Query.dimension) : Data).size = esize n + 10 := by
    change esize n + (encode CL.Sampler.Query.dimension : Data).size + 1 = _
    rw [size_encode_dimension]
  rw [this]
  have := (Eval.deterministic hrun h₀).2
  omega

/-- The calls to the input calculator through the universal machine, within a common bound. -/
theorem len_calls_le (L : Decider) (n : ℕ) (R : Budget) (hL : L.TimeBoundAt n R.D R.k)
    (d : Data) (s k : ℕ) : ∀ q ∈ lenQs n d s k, ∃ r, RunsLe selfUniversal.univ
      (.cons (encode L.prog) q) r (selfUniversal.bound.eval (esize L.prog +
        (esize n + 4 * d.size + 6) + R.D * (4 * d.size + 6) ^ R.k)) := by
  intro q hq
  obtain ⟨xi, b, rfl, hxi⟩ := mem_lenQs hq
  obtain ⟨r, t, ht, hrun⟩ := hL (encode (xi, b))
  obtain ⟨t', ht', hu⟩ := selfUniversal.time_le _ _ _ _ hrun
  refine ⟨r, t', ht'.trans (polynomial_eval_mono _ ?_), hu⟩
  have hb := esize_bool_le b
  have h1 : (encode (xi, b) : Data).size + 1 ≤ 4 * d.size + 6 := by
    change esize xi + esize b + 1 + 1 ≤ _; omega
  have h2 : t ≤ R.D * (4 * d.size + 6) ^ R.k :=
    ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _))
  have h3 : (Data.cons (encode n) (encode (xi, b))).size ≤ esize n + 4 * d.size + 6 := by
    simp only [size_cons]; change esize n + _ + 1 ≤ _; omega
  omega

/-- The argument of the calls' bound, dominated. -/
theorem dom_yCall : ∃ c m e, ∀ (W X K : ℕ) {p n D : ℕ} {d : Data}, 1 ≤ X → 10 ^ K ≤ W →
    p ≤ W → n ≤ W → D ≤ W → d.size + 1 ≤ X →
    Dom W X K c m e (p + (esize n + 4 * d.size + 6) + D * (4 * d.size + 6) ^ K) := by
  exact ⟨_, _, _, fun W X K {p n D d} hX hW hp hn hD hd => by
    have en := esize_nat_le' n
    exact ((Dom.ofLin hX (a := 5) (b := 4) (c := 7) (by omega)).add hX
      ((Dom.ofLeW hD).mul (dom_powK hX hW (a := 6) (j := 1) (by norm_num) (by omega))))⟩

/-- The bound on the queries and results of the loop of calls. -/
def lenZ (W n : ℕ) (d : Data) (T : ℕ) : ℕ :=
  2 * W * (esize n + 4 * d.size + 6) + 2 * W + 1 + (2 * W * T + 2 * W + 1) + 1

theorem dom_lenZ (cT mT eT : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {n T : ℕ} {d : Data}, 1 ≤ X → n ≤ W →
    d.size + 1 ≤ X → Dom W X K cT mT eT T → Dom W X K c m e (lenZ W n d T) := by
  exact ⟨_, _, _, fun W X K {n T d} hX hn hd hT => by
    unfold lenZ
    have en := esize_nat_le' n
    have hW2 : Dom W X K (2 + 0) 1 0 (2 * W) := Dom.ofAffine (by omega)
    exact ((((hW2.mul (Dom.ofLin hX (a := 4) (b := 4) (c := 7) (by omega))).add hX hW2).add hX
      (Dom.const 1)).add hX (((hW2.mul hT).add hX hW2).add hX (Dom.const 1))).add hX
      (Dom.const 1)⟩

/-- **The running time of the repeated calculator.** -/
theorem repLen_timeBound : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (L : Decider) (lam tau n : ℕ)
    (R : Budget) (W : ℕ), LenDom S L lam tau n R W → S.TimeBoundAt n R.S R.k →
    L.TimeBoundAt n R.D R.k →
    (repLen S L lam tau).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1)) := by
  obtain ⟨cy, my, ey, hy⟩ := dom_yd
  obtain ⟨cd, md, ed, hd⟩ := dom_univ_bound cy my ey
  obtain ⟨cc, mc, ec, hc⟩ := dom_yCall
  obtain ⟨cT, mT, eT, hT⟩ := dom_univ_bound cc mc ec
  obtain ⟨cZ, mZ, eZ, hZ⟩ := dom_lenZ cT mT eT
  obtain ⟨cL, mL, eL, hLc⟩ := dom_lenCoreCost cd md ed cT mT eT cZ mZ eZ
  exact ⟨_, _, _, fun {ℓ} S L lam tau n R W hW hS hL d => by
    classical
    have hX : 1 ≤ d.size + 1 := by omega
    have hW1 : 1 ≤ W := le_trans (Nat.one_le_pow _ _ (by norm_num)) hW.pow_le
    have en := esize_nat_le' n
    have elam := esize_nat_le' lam
    have etau := esize_nat_le' tau
    have hcalls := len_calls_le L n R hL d (S.dim n) (Repetition.reps lam tau n)
    set T := selfUniversal.bound.eval (esize L.prog + (esize n + 4 * d.size + 6) +
      R.D * (4 * d.size + 6) ^ R.k) with hTdef
    let f : Data → Data := fun q =>
      if h : ∃ r, RunsLe selfUniversal.univ (.cons (encode L.prog) q) r T then h.choose else .nil
    have hf : ∀ q ∈ (lenQs n d (S.dim n) (Repetition.reps lam tau n)), RunsLe selfUniversal.univ (.cons (encode L.prog) q) (f q) T := by
      intro q hq
      simp only [f, dite_eq_left (hcalls q hq)]
      exact (hcalls q hq).choose_spec
    have hlen : (lenQs n d (S.dim n) (Repetition.reps lam tau n)).length ≤ 2 * W := by
      rw [length_lenQs]; have := hW.reps_le; omega
    have hq1 : (list (lenQs n d (S.dim n) (Repetition.reps lam tau n))).size ≤ 2 * W * (esize n + 4 * d.size + 6) + 2 * W + 1 := by
      refine Machine.size_list_le_of_forall (lenQs n d (S.dim n) (Repetition.reps lam tau n)) hlen fun q hq => ?_
      obtain ⟨xi, b, rfl, hxi⟩ := mem_lenQs hq
      have hb := esize_bool_le b
      change esize n + (esize xi + esize b + 1) + 1 ≤ _
      omega
    have hq2 : (list ((lenQs n d (S.dim n) (Repetition.reps lam tau n)).map f)).size ≤ 2 * W * T + 2 * W + 1 := by
      refine Machine.size_list_le_of_forall _ (by rw [List.length_map]; exact hlen) fun r hr => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      exact (hf q hq).size_le
    have hsize : (list (lenQs n d (S.dim n) (Repetition.reps lam tau n))).size + (list ((lenQs n d (S.dim n) (Repetition.reps lam tau n)).map f)).size + 1 ≤ lenZ W n d T := by
      unfold lenZ; omega
    obtain ⟨t, ht, hr⟩ := lenCore_runsLe selfUniversal.closed S.prog L.prog lam tau n d (S.dim n)
      (dim_univ_le S n R hS) f T (lenZ W n d T) hf hsize
    have hr' : (lenCore selfUniversal.univ).Runs (.cons (encode ((S.prog, L.prog, lam, tau) : LenPar))
        (.cons (encode n) d)) _ t := hr
    have hh := hardcode_time (lenCore_wellScoped selfUniversal.closed) hr'
    refine ⟨_, _, ?_, hh⟩
    have dTd := hd W (d.size + 1) R.k hX (by omega)
      (hy W (d.size + 1) R.k hX hW.sizeS_le hW.n_le hW.S_le hW.pow_le)
    have dT : Dom W (d.size + 1) R.k cT mT eT T := hT W (d.size + 1) R.k hX (by omega)
      (hc W (d.size + 1) R.k hX hW.pow_le hW.sizeL_le hW.n_le hW.D_le le_rfl)
    have dZ := hZ W (d.size + 1) R.k hX hW.n_le le_rfl dT
    have dL := hLc W (d.size + 1) R.k (sp := S.prog) (lp := L.prog) (d := d) (s := S.dim n)
      (k := Repetition.reps lam tau n) (rs := (lenQs n d (S.dim n) (Repetition.reps lam tau n)).map f) hX hW1 le_rfl hW.sizeS_le hW.sizeL_le hW.lam_le hW.tau_le
      hW.n_le hW.dim_le hW.reps_le dTd dT dZ (by omega) (by omega)
    have dP := Dom.ofLin (W := W) (K := R.k) hX (a := 10) (b := 0) (c := 5)
      (v := (encode ((S.prog, L.prog, lam, tau) : LenPar) : Data).size) (by
        change esize S.prog + (esize L.prog + (esize lam + esize tau + 1) + 1) + 1 ≤ _
        have := hW.sizeS_le; have := hW.sizeL_le; have := hW.lam_le; have := hW.tau_le
        omega)
    have dI := Dom.ofLin (W := W) (K := R.k) hX (a := 4) (b := 1) (c := 1)
      (v := (Data.cons (encode n) d).size) (by
        simp only [size_cons]; change esize n + _ + 1 ≤ _; have := hW.n_le; omega)
    exact (((dL.add hX dP).add hX dI).add hX (Dom.const 3)).le.trans' (by omega)⟩

end MIPRE.Tailored.RepProg

end
