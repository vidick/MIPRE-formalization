/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.Repeat.LpProg

@[expose] public section

/-!
# The repeated linear-constraints processor meets its specification

`RepSpec.lp_iff` for `repLp` (issue #280, P2b): at good questions and readable answers of the
right lengths, the processor halts exactly when every coordinate's processor does, and then
outputs the product's constraints. The lengths the program reads off the calculator's outputs are
the coordinates' (`lensOf_quarter`), so its twelve lengths at a coordinate are those of
`TailoredGame.padCons` (`lens_lpPads`), its queries to the input processor are the
coordinates' (`lpPQs_eq`), and its output is the product's constraints (`lpOut_eq`).
-/

namespace MIPRE.Tailored.RepProg

open Cost Cost.Data Cost.Prog Cost.PolyTimeFun CL Calls Finset

/-! ## Lengths of the scans -/

theorem length_flatten_unary (L : List Unary) : L.flatten.length = (L.map List.length).sum :=
  List.length_flatten

/-- The lengths of the triple at a position: the sum before, the length at, the sum after. -/
theorem lens_triples (L : List Unary) (i : ℕ) (hi : i < L.length) :
    ((triples L)[i]'(by simpa [triples] using hi)).map List.length =
      [((L.map List.length).take i).sum, (L.map List.length)[i]'(by simpa using hi),
        ((L.map List.length).drop (i + 1)).sum] := by
  simp [triples, length_flatten_unary, List.map_take, List.map_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]

@[simp] theorem length_triples (L : List Unary) : (triples L).length = L.length := by
  simp [triples]

@[simp] theorem length_padData (A B C D : List Unary) :
    (padData A B C D).length = min (min A.length B.length) (min C.length D.length) := by
  simp [padData]

theorem getElem_padData (A B C D : List Unary) (i : ℕ) (h : i < (padData A B C D).length) :
    (padData A B C D)[i] =
      (triples A)[i]'(by simp at h; simp; omega) ++ (triples B)[i]'(by simp at h; simp; omega) ++
        ((triples C)[i]'(by simp at h; simp; omega) ++ (triples D)[i]'(by simp at h; simp; omega)) := by
  simp [padData]

/-! ## Sums over the coordinates -/

theorem sum_take_ofFn_eq {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    ((List.ofFn f).take i).sum = ∑ j ∈ univ.filter (· < i), f j := by
  rw [List.sum_take_ofFn]
  rfl

theorem sum_drop_ofFn_eq {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    ((List.ofFn f).drop (i + 1)).sum = (∑ j, f j) - ((∑ j ∈ univ.filter (· < i), f j) + f i) := by
  have h1 := List.sum_take_add_sum_drop (List.ofFn f) (i + 1)
  have h2 : ((List.ofFn f).take (i + 1)).sum = (∑ j ∈ univ.filter (· < i), f j) + f i := by
    rw [List.sum_take_succ _ _ (by simpa using i.isLt), sum_take_ofFn_eq]
    simp
  rw [List.sum_ofFn] at h1
  omega

/-! ## Quarters -/

theorem quarter_append (A B C D : List Data) {k : ℕ} (hA : A.length = k)
    (hB : B.length = k) (hC : C.length = k) (hD : D.length = k) :
    quarter (A ++ B ++ (C ++ D)) k 0 = A ∧ quarter (A ++ B ++ (C ++ D)) k 1 = B ∧
      quarter (A ++ B ++ (C ++ D)) k 2 = C ∧ quarter (A ++ B ++ (C ++ D)) k 3 = D := by
  subst hA
  have e1 : A.drop (A.length + A.length + A.length) = [] := List.drop_of_length_le (by omega)
  have e2 : B.drop (A.length + A.length) = [] := List.drop_of_length_le (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [quarter, List.drop_append, List.take_append, hB, hC, hD, two_mul, e1, e2,
      show 3 * A.length = A.length + A.length + A.length by ring]

theorem forall₂_quarter {R : Data → Data → Prop} {l₁ l₂ : List Data}
    (h : List.Forall₂ R l₁ l₂) (k j : ℕ) : List.Forall₂ R (quarter l₁ k j) (quarter l₂ k j) :=
  List.forall₂_take _ (List.forall₂_drop _ h)

section Spec

variable {ℓ : ℕ} (V : TailoredVerifier ℓ) (lam tau : ℕ)

open TailoredVerifier

/-- The calls to the input calculator answered, the lengths read off the results are the
coordinates'. -/
theorem lens_lensOf (n : ℕ) (b : Bool) :
    ∀ (bl : List BitStr) (rs : List Data), (∀ xi ∈ bl, ∃ k, LenIs V.len n xi b k) →
      List.Forall₂ (fun q r => ∃ t, selfUniversal.univ.Runs (.cons (encode V.len.prog) q) r t)
        (bl.map fun xi => encode (n, xi, b)) rs →
      (lensOf rs).map List.length = bl.map fun xi => V.lenOf n xi b
  | [], _, _, h => by cases h; rfl
  | xi :: bl, _, hb, .cons ⟨t, hr⟩ hrest => by
    rename_i r rs
    have ih := lens_lensOf n b bl rs (fun x hx => hb x (by simp [hx])) hrest
    obtain ⟨t', h'⟩ := selfUniversal.halts_of _ _ _ _ hr
    have hL : LenIs V.len n xi b (spineList r).length := ⟨t', r, h', rfl⟩
    have hdef := hb xi (by simp)
    have hlen : V.lenOf n xi b = (spineList r).length := by
      unfold lenOf; rw [dif_pos hdef]; exact hdef.choose_spec.unique hL
    simp only [lensOf, List.map_cons, List.map_map] at ih ⊢
    rw [← ih, hlen]
    simp [Function.comp_def, length_unary, rawList_eq_spineList]

/-- The padding by twelve lengths is the padding of the product. -/
theorem padWithL_eq {X : Type*} [Fintype X] (G : TailoredGame X) {k : ℕ} (x y : Fin k → X) (i : Fin k)
    (p : List Unary) (hp : p.map List.length = [G.preR x i, G.lenR (x i), G.sufR x i,
      G.preL x i, G.lenL (x i), G.sufL x i, G.preR y i, G.lenR (y i), G.sufR y i, G.preL y i,
      G.lenL (y i), G.sufL y i]) (c : BitStr) :
    padWithL p c = G.padCons x y i c := by
  have h : ∀ j, (p.getD j []).length = (p.map List.length).getD j 0 := by
    clear hp
    induction p with
    | nil => intro j; simp
    | cons u p ih =>
      intro j
      cases j with
      | zero => simp
      | succ j => simp only [List.getD_cons_succ, List.map_cons]; exact ih j
  simp only [padWithL, h, hp, TailoredGame.padCons, TailoredGame.len, List.getD_cons_succ,
    List.getD_cons_zero, TailoredGame.zeros, List.append_assoc, Nat.add_assoc]

variable (n : ℕ) (x y : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) (aR bR : BitStr)

/-- The state of the processor at `(n, x, y, a^R, b^R)`. -/
noncomputable abbrev specSt : LpSt :=
  lpSt V.sampler.prog V.len.prog V.lp.prog lam tau n (encode (toBits x, toBits y, aR, bR))
    (V.sampler.dim n)

theorem blocksX_specSt :
    blocksX (specSt V lam tau n x y aR bR) = List.ofFn fun i => toBits (qc V lam tau n x i) := by
  simp only [blocksX, (read_encode _ _ _ _).1, length_unary, blocks_toBits]

theorem blocksY_specSt :
    blocksY (specSt V lam tau n x y aR bR) = List.ofFn fun i => toBits (qc V lam tau n y i) := by
  simp only [blocksY, (read_encode _ _ _ _).2.1, length_unary, blocks_toBits]

/-- The calls to `L̄` answered by `rs₁`, the four quarters of lengths. -/
theorem lens_quarters (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i)))
    (hy : ∀ i, V.LenDefined n (toBits (qc V lam tau n y i))) (rs₁ : List Data)
    (hrs : List.Forall₂ (fun q r => ∃ t, selfUniversal.univ.Runs (.cons (encode V.len.prog) q) r t)
      (lpLenQs (specSt V lam tau n x y aR bR)) rs₁) :
    (lensOf (quarter rs₁ (K lam tau n) 0)).map List.length =
        List.ofFn (fun i => (V.tgame n).lenR (qEquiv V lam tau n x i)) ∧
      (lensOf (quarter rs₁ (K lam tau n) 1)).map List.length =
        List.ofFn (fun i => (V.tgame n).lenL (qEquiv V lam tau n x i)) ∧
      (lensOf (quarter rs₁ (K lam tau n) 2)).map List.length =
        List.ofFn (fun i => (V.tgame n).lenR (qEquiv V lam tau n y i)) ∧
      (lensOf (quarter rs₁ (K lam tau n) 3)).map List.length =
        List.ofFn (fun i => (V.tgame n).lenL (qEquiv V lam tau n y i)) := by
  have hq : lpLenQs (specSt V lam tau n x y aR bR) =
      ((List.ofFn fun i => toBits (qc V lam tau n x i)).map (fun xi => encode (n, xi, false)) ++
        (List.ofFn fun i => toBits (qc V lam tau n x i)).map (fun xi => encode (n, xi, true))) ++
      ((List.ofFn fun i => toBits (qc V lam tau n y i)).map (fun xi => encode (n, xi, false)) ++
        (List.ofFn fun i => toBits (qc V lam tau n y i)).map (fun xi => encode (n, xi, true))) := by
    simp only [lpLenQs, lenQueries, blocksX_specSt, blocksY_specSt]
  obtain ⟨q0, q1, q2, q3⟩ := quarter_append
    ((List.ofFn fun i => toBits (qc V lam tau n x i)).map (fun xi => encode (n, xi, false)))
    ((List.ofFn fun i => toBits (qc V lam tau n x i)).map (fun xi => encode (n, xi, true)))
    ((List.ofFn fun i => toBits (qc V lam tau n y i)).map (fun xi => encode (n, xi, false)))
    ((List.ofFn fun i => toBits (qc V lam tau n y i)).map (fun xi => encode (n, xi, true)))
    (k := K lam tau n) (by simp) (by simp) (by simp) (by simp)
  rw [hq] at hrs
  have hgx : ∀ b, ∀ xi ∈ List.ofFn (fun i => toBits (qc V lam tau n x i)),
      ∃ k, LenIs V.len n xi b k := by
    intro b xi h; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 h; exact hx i b
  have hgy : ∀ b, ∀ xi ∈ List.ofFn (fun i => toBits (qc V lam tau n y i)),
      ∃ k, LenIs V.len n xi b k := by
    intro b xi h; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 h; exact hy i b
  have r0 := forall₂_quarter hrs (K lam tau n) 0
  have r1 := forall₂_quarter hrs (K lam tau n) 1
  have r2 := forall₂_quarter hrs (K lam tau n) 2
  have r3 := forall₂_quarter hrs (K lam tau n) 3
  rw [q0] at r0; rw [q1] at r1; rw [q2] at r2; rw [q3] at r3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lens_lensOf V n false _ _ (hgx false) r0, List.map_ofFn]; rfl
  · rw [lens_lensOf V n true _ _ (hgx true) r1, List.map_ofFn]; rfl
  · rw [lens_lensOf V n false _ _ (hgy false) r2, List.map_ofFn]; rfl
  · rw [lens_lensOf V n true _ _ (hgy true) r3, List.map_ofFn]; rfl

/-- **The twelve lengths of every coordinate** are those of the product's padding. -/
theorem lens_lpPads (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i)))
    (hy : ∀ i, V.LenDefined n (toBits (qc V lam tau n y i))) (rs₁ : List Data)
    (hrs : List.Forall₂ (fun q r => ∃ t, selfUniversal.univ.Runs (.cons (encode V.len.prog) q) r t)
      (lpLenQs (specSt V lam tau n x y aR bR)) rs₁) :
    (lpPads rs₁ (K lam tau n)).length = K lam tau n ∧ ∀ i : Fin (K lam tau n),
      ((lpPads rs₁ (K lam tau n)).getD i []).map List.length =
        [(V.tgame n).preR (qEquiv V lam tau n x) i, (V.tgame n).lenR (qEquiv V lam tau n x i),
          (V.tgame n).sufR (qEquiv V lam tau n x) i, (V.tgame n).preL (qEquiv V lam tau n x) i,
          (V.tgame n).lenL (qEquiv V lam tau n x i), (V.tgame n).sufL (qEquiv V lam tau n x) i,
          (V.tgame n).preR (qEquiv V lam tau n y) i, (V.tgame n).lenR (qEquiv V lam tau n y i),
          (V.tgame n).sufR (qEquiv V lam tau n y) i, (V.tgame n).preL (qEquiv V lam tau n y) i,
          (V.tgame n).lenL (qEquiv V lam tau n y i), (V.tgame n).sufL (qEquiv V lam tau n y) i] := by
  obtain ⟨h0, h1, h2, h3⟩ := lens_quarters V lam tau n x y aR bR hx hy rs₁ hrs
  have l0 := congrArg List.length h0
  have l1 := congrArg List.length h1
  have l2 := congrArg List.length h2
  have l3 := congrArg List.length h3
  simp only [List.length_map, List.length_ofFn] at l0 l1 l2 l3
  have hlen : (lpPads rs₁ (K lam tau n)).length = K lam tau n := by
    simp [lpPads, l0, l1, l2, l3]
  refine ⟨hlen, fun i => ?_⟩
  have hi : (i : ℕ) < (lpPads rs₁ (K lam tau n)).length := by rw [hlen]; exact i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  simp only [lpPads] at hi ⊢
  rw [getElem_padData, List.map_append, List.map_append, List.map_append,
    lens_triples (lensOf (quarter rs₁ (K lam tau n) 0)) i (by omega),
    lens_triples (lensOf (quarter rs₁ (K lam tau n) 1)) i (by omega),
    lens_triples (lensOf (quarter rs₁ (K lam tau n) 2)) i (by omega),
    lens_triples (lensOf (quarter rs₁ (K lam tau n) 3)) i (by omega)]
  simp only [h0, h1, h2, h3, sum_take_ofFn_eq, sum_drop_ofFn_eq, List.getElem_ofFn,
    List.cons_append, List.nil_append]
  rfl

theorem length_getD_of_lens {p : List Unary} {l : List ℕ} (hp : p.map List.length = l) (j : ℕ) :
    (p.getD j []).length = l.getD j 0 := by
  subst hp
  induction p generalizing j with
  | nil => simp
  | cons u p ih =>
    cases j with
    | zero => simp
    | succ j => simp only [List.getD_cons_succ, List.map_cons]; exact ih j

/-- **The queries to the input processor** are the coordinates'. -/
theorem lpPQs_eq (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i)))
    (hy : ∀ i, V.LenDefined n (toBits (qc V lam tau n y i))) (rs₁ : List Data)
    (hrs : List.Forall₂ (fun q r => ∃ t, selfUniversal.univ.Runs (.cons (encode V.len.prog) q) r t)
      (lpLenQs (specSt V lam tau n x y aR bR)) rs₁) :
    lpPQs (specSt V lam tau n x y aR bR) rs₁ = List.ofFn fun i =>
      encode (n, toBits (qc V lam tau n x i), toBits (qc V lam tau n y i),
        (V.tgame n).coordR (qEquiv V lam tau n x) aR i,
        (V.tgame n).coordR (qEquiv V lam tau n y) bR i) := by
  obtain ⟨hlen, hpad⟩ := lens_lpPads V lam tau n x y aR bR hx hy rs₁ hrs
  obtain ⟨-, -, hA, hB⟩ := read_encode (toBits x) (toBits y) aR bR
  apply List.ext_getElem
  · simp [lpPQs, lpQueries, blocksX_specSt, blocksY_specSt, hlen]
  intro i h₁ h₂
  have hi : i < K lam tau n := by simpa using h₂
  have hp := hpad ⟨i, hi⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at hp
  simp only [lpPQs, lpQueries, List.getElem_map, List.getElem_zip, blocksX_specSt,
    blocksY_specSt, List.getElem_ofFn, lpQuery, hA, hB, length_unary]
  have hp' : ((lpPads rs₁ (K lam tau n))[i]).map List.length = _ := hp
  rw [length_getD_of_lens hp' 0, length_getD_of_lens hp' 1, length_getD_of_lens hp' 6,
    length_getD_of_lens hp' 7]
  rfl

/-- **The output** is the padded constraints of the coordinates. -/
theorem lpOut_eq (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i)))
    (hy : ∀ i, V.LenDefined n (toBits (qc V lam tau n y i))) (rs₁ : List Data)
    (hrs : List.Forall₂ (fun q r => ∃ t, selfUniversal.univ.Runs (.cons (encode V.len.prog) q) r t)
      (lpLenQs (specSt V lam tau n x y aR bR)) rs₁) (rs₂ : List Data)
    (h₂ : rs₂.length = K lam tau n) :
    lpOut (lpPads rs₁ (K lam tau n)) rs₂ = (List.finRange (K lam tau n)).flatMap
      fun (i : Fin (K lam tau n)) => (bitsListD (rs₂.getD (i : ℕ) .nil)).map
        ((V.tgame n).padCons (qEquiv V lam tau n x) (qEquiv V lam tau n y) i) := by
  obtain ⟨hlen, hpad⟩ := lens_lpPads V lam tau n x y aR bR hx hy rs₁ hrs
  rw [lpOut, List.flatMap_def]
  congr 1
  apply List.ext_getElem
  · simp [hlen, h₂]
  intro i h₁ h₃
  have hi : i < K lam tau n := by simpa using h₃
  have hp := hpad ⟨i, hi⟩
  simp only [List.getElem_map, List.getElem_zip, List.getElem_finRange]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at hp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact List.map_congr_left fun c _ => padWithL_eq _ _ _ _ _ hp c

end Spec

/-! ## The processor -/

/-- The program of the repeated processor: the core with `(S̄, L̄, P̄, λ, τ)` stored. -/
noncomputable def repLpProg (sp lp pp : Prog) (lam tau : ℕ) : Prog :=
  hardcode (lpCore selfUniversal.univ) (encode ((sp, lp, pp, lam, tau) : LpPar))

/-- **The repeated linear-constraints processor.** -/
noncomputable def repLp {ℓ : ℕ} (S : CL.Sampler ℓ) (L P : Decider) (lam tau : ℕ) : Decider :=
  ⟨repLpProg S.prog L.prog P.prog lam tau,
    hardcode_wellScoped (lpCore_wellScoped selfUniversal.closed) _⟩

/-! ## The specification -/

open Classical in
/-- A result of `univ` on `(c, q)`, when there is one. -/
noncomputable def chooseRun (c q : Data) : Data :=
  if h : ∃ r t, selfUniversal.univ.Runs (.cons c q) r t then h.choose else .nil

theorem chooseRun_spec {c q : Data} (h : ∃ r t, selfUniversal.univ.Runs (.cons c q) r t) :
    ∃ t, selfUniversal.univ.Runs (.cons c q) (chooseRun c q) t := by
  unfold chooseRun
  rw [dif_pos h]
  exact h.choose_spec

theorem forall₂_map_self {α β : Type*} {R : α → β → Prop} (f : α → β) :
    ∀ {l : List α}, (∀ a ∈ l, R a (f a)) → List.Forall₂ R l (l.map f)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_map_self f fun b hb => h b (by simp [hb]))

theorem mem_lenQueries {n : ℕ} {bl : List BitStr} {q : Data} (h : q ∈ lenQueries n bl) :
    ∃ xi ∈ bl, ∃ b : Bool, q = encode (n, xi, b) := by
  unfold lenQueries at h
  rw [List.mem_append, List.mem_map, List.mem_map] at h
  rcases h with ⟨xi, hxi, rfl⟩ | ⟨xi, hxi, rfl⟩
  · exact ⟨xi, hxi, false, rfl⟩
  · exact ⟨xi, hxi, true, rfl⟩

section Spec

variable {ℓ : ℕ} (V : TailoredVerifier ℓ) (lam tau : ℕ)

open TailoredVerifier

/-- **`RepSpec.lp_iff`** for the repeated processor. -/
theorem repLp_lpIs_iff (n : ℕ) (x y : Fin (K lam tau n * V.sampler.dim n) → 𝔽₂) (aR bR : BitStr)
    (hx : ∀ i, V.LenDefined n (toBits (qc V lam tau n x i)))
    (hy : ∀ i, V.LenDefined n (toBits (qc V lam tau n y i))) (cs : List BitStr) :
    LpIs (repLp V.sampler V.len V.lp lam tau) n (toBits x) (toBits y) aR bR cs ↔
      (∀ i, ∃ c, LpIs V.lp n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
        ((V.tgame n).coordR (qEquiv V lam tau n x) aR i)
        ((V.tgame n).coordR (qEquiv V lam tau n y) bR i) c) ∧
      cs = ((V.tgame n).repeat (K lam tau n)).cons (qEquiv V lam tau n x)
        (qEquiv V lam tau n y) aR bR := by
  obtain ⟨td, hd⟩ := dim_univ V n
  -- the queries of a coordinate, and what its processor's output is
  set qP : Fin (K lam tau n) → Data := fun i =>
    encode (n, toBits (qc V lam tau n x i), toBits (qc V lam tau n y i),
      (V.tgame n).coordR (qEquiv V lam tau n x) aR i,
      (V.tgame n).coordR (qEquiv V lam tau n y) bR i) with hqP
  have hprod : ((V.tgame n).repeat (K lam tau n)).cons (qEquiv V lam tau n x)
      (qEquiv V lam tau n y) aR bR = (List.finRange (K lam tau n)).flatMap fun i =>
        (V.consOf n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
          ((V.tgame n).coordR (qEquiv V lam tau n x) aR i)
          ((V.tgame n).coordR (qEquiv V lam tau n y) bR i)).map
        ((V.tgame n).padCons (qEquiv V lam tau n x) (qEquiv V lam tau n y) i) := rfl
  -- a run of `P̄` on a coordinate's query gives its constraints
  have hcoord : ∀ i r, (∃ t, selfUniversal.univ.Runs (.cons (encode V.lp.prog) (qP i)) r t) →
      V.consOf n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
          ((V.tgame n).coordR (qEquiv V lam tau n x) aR i)
          ((V.tgame n).coordR (qEquiv V lam tau n y) bR i) = bitsListD r ∧
        LpIs V.lp n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
          ((V.tgame n).coordR (qEquiv V lam tau n x) aR i)
          ((V.tgame n).coordR (qEquiv V lam tau n y) bR i) (bitsListD r) := by
    intro i r ⟨t, hr⟩
    obtain ⟨t', h'⟩ := selfUniversal.halts_of _ _ _ _ hr
    have hl : LpIs V.lp n (toBits (qc V lam tau n x i)) (toBits (qc V lam tau n y i))
        ((V.tgame n).coordR (qEquiv V lam tau n x) aR i)
        ((V.tgame n).coordR (qEquiv V lam tau n y) bR i) (bitsListD r) := ⟨t', r, h', rfl⟩
    exact ⟨consOf_eq_of V (hx i) (hy i) hl, hl⟩
  constructor
  · rintro ⟨t, r, hr, rfl⟩
    obtain ⟨t', -, hc⟩ := hardcode_time_rev (lpCore_wellScoped selfUniversal.closed) hr
    obtain ⟨rs₁, rs₂, hrs₁, hrs₂, rfl⟩ := lpCore_inv selfUniversal.closed V.sampler.prog
      V.len.prog V.lp.prog lam tau n (encode (toBits x, toBits y, aR, bR)) (V.sampler.dim n) hd
      (r := r) (t := t') hc
    rw [lpPQs_eq V lam tau n x y aR bR hx hy rs₁ hrs₁] at hrs₂
    have hl₂ : rs₂.length = K lam tau n := by simpa using hrs₂.length_eq.symm
    have hget : ∀ i : Fin (K lam tau n), ∃ t, selfUniversal.univ.Runs
        (.cons (encode V.lp.prog) (qP i)) (rs₂.getD i .nil) t := by
      intro i
      obtain ⟨-, hall⟩ := List.forall₂_iff_get.1 hrs₂
      have := hall i (by simp) (by rw [hl₂]; exact i.isLt)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl₂]; exact i.isLt),
        Option.getD_some]
      simpa [qP] using this
    refine ⟨fun i => ⟨_, (hcoord i _ (hget i)).2⟩, ?_⟩
    rw [bitsListD_encode, lpOut_eq V lam tau n x y aR bR hx hy rs₁ hrs₁ rs₂ hl₂, hprod]
    refine List.flatMap_congr fun i _ => ?_
    rw [(hcoord i _ (hget i)).1]
  · rintro ⟨hc, rfl⟩
    have hf₁ : ∀ q ∈ lpLenQs (specSt V lam tau n x y aR bR), ∃ t, selfUniversal.univ.Runs
        (.cons (encode V.len.prog) q) (chooseRun (encode V.len.prog) q) t := by
      intro q hq
      apply chooseRun_spec
      have hq' : q ∈ lenQueries n (List.ofFn fun i => toBits (qc V lam tau n x i)) ∨
          q ∈ lenQueries n (List.ofFn fun i => toBits (qc V lam tau n y i)) := by
        simpa only [lpLenQs, blocksX_specSt, blocksY_specSt, List.mem_append] using hq
      rcases hq' with h | h <;>
      · obtain ⟨xi, hxi, b, rfl⟩ := mem_lenQueries h
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hxi
        first
          | obtain ⟨k, t, dd, hrun, -⟩ := hx i b
            obtain ⟨t', -, hu⟩ := selfUniversal.time_le _ _ _ _ hrun
            exact ⟨_, _, hu⟩
          | obtain ⟨k, t, dd, hrun, -⟩ := hy i b
            obtain ⟨t', -, hu⟩ := selfUniversal.time_le _ _ _ _ hrun
            exact ⟨_, _, hu⟩
    have hrs₁ := forall₂_map_self (R := fun q r => ∃ t, selfUniversal.univ.Runs
      (.cons (encode V.len.prog) q) r t) _ hf₁
    have hPQ := lpPQs_eq V lam tau n x y aR bR hx hy _ hrs₁
    have hf₂ : ∀ q ∈ lpPQs (specSt V lam tau n x y aR bR)
        ((lpLenQs (specSt V lam tau n x y aR bR)).map (chooseRun (encode V.len.prog))),
        ∃ t, selfUniversal.univ.Runs (.cons (encode V.lp.prog) q)
          (chooseRun (encode V.lp.prog) q) t := by
      intro q hq
      rw [hPQ] at hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
      apply chooseRun_spec
      obtain ⟨c, t, dd, hrun, -⟩ := hc i
      obtain ⟨t', -, hu⟩ := selfUniversal.time_le _ _ _ _ hrun
      exact ⟨_, _, hu⟩
    obtain ⟨T₁, hT₁⟩ := Repeat.exists_uniform_bound _ (fun q t => selfUniversal.univ.Runs
      (.cons (encode V.len.prog) q) (chooseRun (encode V.len.prog) q) t) hf₁
    obtain ⟨T₂, hT₂⟩ := Repeat.exists_uniform_bound _ (fun q t => selfUniversal.univ.Runs
      (.cons (encode V.lp.prog) q) (chooseRun (encode V.lp.prog) q) t) hf₂
    obtain ⟨t₀, -, h₀⟩ := lpCore_runsLe selfUniversal.closed V.sampler.prog V.len.prog V.lp.prog
      lam tau n (encode (toBits x, toBits y, aR, bR)) (V.sampler.dim n) ⟨td, le_rfl, hd⟩
      (chooseRun (encode V.len.prog)) (chooseRun (encode V.lp.prog)) T₁ _ T₂ _ hT₁ le_rfl hT₂
      le_rfl
    refine ⟨_, _, hardcode_time (lpCore_wellScoped selfUniversal.closed) h₀, ?_⟩
    rw [bitsListD_encode, lpOut_eq V lam tau n x y aR bR hx hy _ hrs₁ _ (by simp [hPQ]), hprod]
    refine List.flatMap_congr fun i _ => ?_
    have hgi : ((lpPQs (specSt V lam tau n x y aR bR) ((lpLenQs (specSt V lam tau n x y aR bR)).map
        (chooseRun (encode V.len.prog)))).map (chooseRun (encode V.lp.prog))).getD i .nil =
        chooseRun (encode V.lp.prog) (qP i) := by
      rw [hPQ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), Option.getD_some]
      simp [qP]
    rw [hgi, (hcoord i _ (chooseRun_spec ?_)).1]
    obtain ⟨c, t, dd, hrun, -⟩ := hc i
    obtain ⟨t', -, hu⟩ := selfUniversal.time_le _ _ _ _ hrun
    exact ⟨_, _, hu⟩

/-- **The repeated programs meet their specification at every index.** -/
theorem repSpec (n : ℕ) :
    RepSpec V lam tau (repLen V.sampler V.len lam tau) (repLp V.sampler V.len V.lp lam tau) n where
  len_eq x hx κ := repLen_lenIs V lam tau n x hx κ
  good_of_len x κ m h i := good_of_repLen V lam tau n x κ m h i
  lp_iff x y aR bR hx hy _ _ cs := repLp_lpIs_iff V lam tau n x y aR bR hx hy cs

end Spec

end MIPRE.Tailored.RepProg

end
