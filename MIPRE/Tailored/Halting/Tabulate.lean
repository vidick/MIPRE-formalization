/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Foundations.Halting.Instantiation
public import MIPRE.Tailored.Compression
public import MIPRE.Tailored.Data.Presents

@[expose] public section

/-!
# The tabulation of a tailored verifier

The tailored counterpart of `MIPRE/Foundations/Halting/Tabulate.lean` and
`Halting/Paper/TabulateL.lean`: the `n`-th game of a `λ`-bounded tailored verifier, written down
as a `TailoredGameValue.TailoredGameData`, by running its three programs under the budgets
`λ`-boundedness supplies.

`tabOfT ℓ sd ld pd s T k n` is the description that the three encoded programs and four numbers
determine. The vertices are the doubled questions, `Bool × 𝔽₂^s` packed into `Fin (2 ^ (s + 1))`
as in the existing tabulation (`Verifier.tagEquiv`), so that the description presents the
doubled game `(V.tgame n).doubled`, which has no weight on its loops:

* the weights are `Verifier.weightList` at the two tagged marginals, as in `Halting.tabOf`, the
  marginals queried at the sampler's own level `ℓ` (`margAt`) and normalized to length `s`
  (`margN`), which only matters at level `0`, where the questions are empty;
* the lengths at a vertex are what the answer-length calculator outputs on its question
  (`lenRun`), read in unary;
* the constraints at a pair of vertices and a readable part of the right length are what the
  linear-constraints processor outputs there (`lpRun`), read by `Data.bitsListD`.

Each run defaults when its budget is missed, which a time bound rules out.

* `primrec_tabOfT`: the description is primitive recursive in its parameters.
* `presents_tabOfT`: for a tailored verifier whose three programs run within `T · (|d| + 1)^k`
  at index `n`, the description presents `(V.tgame n).doubled` (`MIPRE.Tailored.Presents`).
* `tabT TG x n`, `tabT_computable`, `presents_tabT`: the tabulation of the verifier a
  description string `descOf λ P` denotes, `(S^λ, L^λ, P)`, with the budget `n^λ · (|d| + 1)^λ`,
  computable in `(x, n)` and correct when that verifier is `λ`-bounded and `n ≥ 2`.
-/

namespace MIPRE.Tailored

open Cost TailoredGameValue

/-! ## Total readings of data, primitive recursively -/

theorem unaryToNat_eq_length (d : Data) : Data.unaryToNat d = (Data.spineList d).length := by
  induction d with
  | nil => rfl
  | cons a d _ ih => rw [Data.unaryToNat_cons, Data.spineList_cons, List.length_cons, ih]

theorem primrec_bitD : Primrec Data.bitD :=
  (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const Data.nil))
    (Primrec.const false) (Primrec.const true)).of_eq fun d => by cases d <;> rfl

theorem bitsD_eq_recD (d : Data) :
    Data.bitsD d = Data.recD [] (fun a _ _ rb => Data.bitD a :: rb) d := by
  induction d with
  | nil => rfl
  | cons a d _ ih => rw [Data.recD_cons, ← ih]; rfl

theorem primrec_bitsD : Primrec Data.bitsD :=
  (Data.primrec_recD [] _ (Primrec.list_cons.comp (primrec_bitD.comp
    (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))).of_eq
    fun d => (bitsD_eq_recD d).symm

theorem bitsListD_eq_recD (d : Data) :
    Data.bitsListD d = Data.recD [] (fun a _ _ rb => Data.bitsD a :: rb) d := by
  induction d with
  | nil => rfl
  | cons a d _ ih => rw [Data.recD_cons, ← ih]; rfl

theorem primrec_bitsListD : Primrec Data.bitsListD :=
  (Data.primrec_recD [] _ (Primrec.list_cons.comp (primrec_bitsD.comp
    (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))).of_eq
    fun d => (bitsListD_eq_recD d).symm

/-! ## Budgeted runs -/

/-- Player `w`'s marginal at the level `ℓ`: one sampler query under the budget
`T · (|q| + 1) ^ k`, `[]` when the budget is missed. `Halting.margOf` is the level `7`. -/
def margAt (ℓ : ℕ) (sd : Data) (T k n : ℕ) (w : Player) (z : BitStr) : BitStr :=
  ((Machine.runForD sd (encode (n, CL.Sampler.Query.marginal w ℓ z))
      (T * ((encode (CL.Sampler.Query.marginal w ℓ z) : Data).size + 1) ^ k)).bind
    fun d => (SizedEncoding.decode d : Option BitStr)).getD []

/-- The marginal, normalized to length `s`: an answer of another length, which a sampler of
level at least `1` never gives under its time bound, is replaced by zeros. At level `0` the
questions are empty, and so is every normalized marginal. -/
def margN (ℓ : ℕ) (sd : Data) (T k n s : ℕ) (w : Player) (z : BitStr) : BitStr :=
  if (margAt ℓ sd T k n w z).length = s then margAt ℓ sd T k n w z
  else (List.range s).map fun _ => false

/-- The length the answer-length calculator outputs on `(n, x, κ)` under the budget
`T · (|(x, κ)| + 1) ^ k`, read in unary; `0` when the budget is missed. -/
def lenRun (ld : Data) (T k n : ℕ) (x : BitStr) (κ : Bool) : ℕ :=
  ((Machine.runForD ld (encode (n, x, κ)) (T * ((encode (x, κ) : Data).size + 1) ^ k)).map
    Data.unaryToNat).getD 0

/-- The constraints the linear-constraints processor outputs on `(n, x, y, a^R, b^R)` under the
budget `T · (|(x, y, a^R, b^R)| + 1) ^ k`, read by `Data.bitsListD`; `[]` when the budget is
missed. -/
def lpRun (pd : Data) (T k n : ℕ) (x y aR bR : BitStr) : List BitStr :=
  ((Machine.runForD pd (encode (n, x, y, aR, bR))
      (T * ((encode (x, y, aR, bR) : Data).size + 1) ^ k)).map Data.bitsListD).getD []

/-! ## The description -/

/-- The question at the vertex `v` of the doubled question set: the bits `1, …, s` of `v`, bit
`0` being the tag. -/
def zOf (s v : ℕ) : BitStr := (List.range s).map fun i => v.testBit (i + 1)

/-- The lengths at the vertices, of the readable variables (`κ = false`) or of the linear ones. -/
def lenList (ld : Data) (T k n s : ℕ) (κ : Bool) : List ℕ :=
  (List.range (2 ^ (s + 1))).map fun v => lenRun ld T k n (zOf s v) κ

/-- The constraint entries at a pair of vertices and a readable part. -/
def consAt (pd : Data) (T k n s : ℕ) (lR : List ℕ) (v v' : ℕ) (γ : BitStr) :
    List (ℕ × ℕ × BitStr × BitStr) :=
  (lpRun pd T k n (zOf s v) (zOf s v') (γ.take (lR.getD v 0)) (γ.drop (lR.getD v 0))).map
    fun c => (v, v', γ, c)

/-- The constraint entries: at every pair of vertices and every readable part of the right
length, the constraints the processor outputs there. -/
def consT (pd : Data) (T k n s : ℕ) (lR : List ℕ) : List (ℕ × ℕ × BitStr × BitStr) :=
  (List.range (2 ^ (s + 1))).flatMap fun v => (List.range (2 ^ (s + 1))).flatMap fun v' =>
    (Data.bitStrsOfLen (lR.getD v 0 + lR.getD v' 0)).flatMap fun γ => consAt pd T k n s lR v v' γ

/-- **The tabulation of a tailored verifier, on parameters alone**: the sampler, answer-length
calculator and linear-constraints processor `sd`, `ld`, `pd` (encoded programs), the dimension
`s`, the budget `T · (|d| + 1) ^ k` and the index `n`. The vertices are the doubled questions. -/
def tabOfT (ℓ : ℕ) (sd ld pd : Data) (s T k n : ℕ) : TailoredGameData where
  nV := 2 ^ (s + 1) - 1
  lenR := lenList ld T k n s false
  lenL := lenList ld T k n s true
  w := Verifier.weightList s
        (fun z => Verifier.bitsToIdx (false :: margN ℓ sd T k n s .alice z))
        (fun z => Verifier.bitsToIdx (true :: margN ℓ sd T k n s .bob z))
  cons := consT pd T k n s (lenList ld T k n s false)

/-! ## Primitive recursion -/

section Primrec

variable {α : Type*} [Primcodable α]

set_option maxHeartbeats 1000000 in
theorem primrec_margAt (ℓ : ℕ) {sd : α → Data} {T k n : α → ℕ} (hsd : Primrec sd)
    (hT : Primrec T) (hk : Primrec k) (hn : Primrec n) (w : Player) :
    Primrec fun q : α × BitStr => margAt ℓ (sd q.1) (T q.1) (k q.1) (n q.1) w q.2 := by
  have hq : Primrec fun q : α × BitStr =>
      (encode (CL.Sampler.Query.marginal w ℓ q.2) : Data) :=
    (CL.Sampler.primrec_encode_marginal w ℓ).comp Primrec.snd
  have hinput : Primrec fun q : α × BitStr =>
      (encode (n q.1, CL.Sampler.Query.marginal w ℓ q.2) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp (hn.comp Primrec.fst)) hq
  have hbudget : Primrec fun q : α × BitStr =>
      T q.1 * ((encode (CL.Sampler.Query.marginal w ℓ q.2) : Data).size + 1) ^ k q.1 :=
    Primrec.nat_mul.comp (hT.comp Primrec.fst)
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp hq))
        (hk.comp Primrec.fst))
  exact Primrec.option_getD.comp
    (Primrec.option_bind
      (Machine.primrec_runForD.comp (((hsd.comp Primrec.fst).pair hinput).pair hbudget))
      (Data.primrec_decode_bitStr.comp Primrec.snd).to₂)
    (Primrec.const [])

theorem primrec_margN (ℓ : ℕ) {sd : α → Data} {T k n s : α → ℕ} (hsd : Primrec sd)
    (hT : Primrec T) (hk : Primrec k) (hn : Primrec n) (hs : Primrec s) (w : Player) :
    Primrec fun q : α × BitStr => margN ℓ (sd q.1) (T q.1) (k q.1) (n q.1) (s q.1) w q.2 := by
  have hm := primrec_margAt ℓ hsd hT hk hn w
  have hz : Primrec fun q : α × BitStr => (List.range (s q.1)).map fun _ => false :=
    Primrec.list_map (Primrec.list_range.comp (hs.comp Primrec.fst)) (Primrec.const false).to₂
  exact Primrec.ite (PrimrecRel.comp Primrec.eq (Primrec.list_length.comp hm)
    (hs.comp Primrec.fst)) hm hz

set_option maxHeartbeats 1000000 in
theorem primrec_dimOf {sd : α → Data} {T k n : α → ℕ} (hsd : Primrec sd) (hT : Primrec T)
    (hk : Primrec k) (hn : Primrec n) :
    Primrec fun a : α => Halting.dimOf (sd a) (T a) (k a) (n a) := by
  have hbudget : Primrec fun a : α =>
      T a * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ k a :=
    Primrec.nat_mul.comp hT (primrec_nat_pow.comp (Primrec.const _) hk)
  have hinput : Primrec fun a : α => (encode (n a, CL.Sampler.Query.dimension) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hn)
      (Primrec.const (encode CL.Sampler.Query.dimension : Data))
  exact Primrec.option_getD.comp
    (Primrec.option_bind (Machine.primrec_runForD.comp ((hsd.pair hinput).pair hbudget))
      (Data.primrec_decode_nat.comp Primrec.snd).to₂)
    (Primrec.const 0)

set_option maxHeartbeats 1000000 in
theorem primrec_lenRun {ld : α → Data} {T k n : α → ℕ} {x : α → BitStr} {κ : α → Bool}
    (hld : Primrec ld) (hT : Primrec T) (hk : Primrec k) (hn : Primrec n) (hx : Primrec x)
    (hκ : Primrec κ) :
    Primrec fun a => lenRun (ld a) (T a) (k a) (n a) (x a) (κ a) := by
  have hxk : Primrec fun a => (encode (x a, κ a) : Data) :=
    Data.primrec_cons.comp (primrec_encode_bitStr.comp hx) (Data.primrec_ofBool.comp hκ)
  have hinput : Primrec fun a => (encode (n a, x a, κ a) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hn) hxk
  have hbudget : Primrec fun a => T a * ((encode (x a, κ a) : Data).size + 1) ^ k a :=
    Primrec.nat_mul.comp hT
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp hxk)) hk)
  exact Primrec.option_getD.comp
    (Primrec.option_map (Machine.primrec_runForD.comp ((hld.pair hinput).pair hbudget))
      (Data.primrec_unaryToNat.comp Primrec.snd).to₂)
    (Primrec.const 0)

set_option maxHeartbeats 1000000 in
theorem primrec_lpRun {pd : α → Data} {T k n : α → ℕ} {x y aR bR : α → BitStr}
    (hpd : Primrec pd) (hT : Primrec T) (hk : Primrec k) (hn : Primrec n) (hx : Primrec x)
    (hy : Primrec y) (haR : Primrec aR) (hbR : Primrec bR) :
    Primrec fun a => lpRun (pd a) (T a) (k a) (n a) (x a) (y a) (aR a) (bR a) := by
  have hebs : Primrec fun l : BitStr => (encode l : Data) := primrec_encode_bitStr
  have htup : Primrec fun a => (encode (x a, y a, aR a, bR a) : Data) :=
    Data.primrec_cons.comp (hebs.comp hx) (Data.primrec_cons.comp (hebs.comp hy)
      (Data.primrec_cons.comp (hebs.comp haR) (hebs.comp hbR)))
  have hinput : Primrec fun a => (encode (n a, x a, y a, aR a, bR a) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hn) htup
  have hbudget : Primrec fun a =>
      T a * ((encode (x a, y a, aR a, bR a) : Data).size + 1) ^ k a :=
    Primrec.nat_mul.comp hT
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp htup)) hk)
  exact Primrec.option_getD.comp
    (Primrec.option_map (Machine.primrec_runForD.comp ((hpd.pair hinput).pair hbudget))
      (primrec_bitsListD.comp Primrec.snd).to₂)
    (Primrec.const [])

theorem primrec_zOf : Primrec₂ zOf :=
  (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (TailoredGameData.primrec_testBit.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.succ.comp Primrec.snd)).to₂).to₂

theorem primrec_lenList {ld : α → Data} {T k n s : α → ℕ} (hld : Primrec ld) (hT : Primrec T)
    (hk : Primrec k) (hn : Primrec n) (hs : Primrec s) (κ : Bool) :
    Primrec fun a => lenList (ld a) (T a) (k a) (n a) (s a) κ :=
  Primrec.list_map
    (Primrec.list_range.comp (primrec_nat_pow.comp (Primrec.const 2) (Primrec.succ.comp hs)))
    (primrec_lenRun (hld.comp Primrec.fst) (hT.comp Primrec.fst) (hk.comp Primrec.fst)
      (hn.comp Primrec.fst) (primrec_zOf.comp (hs.comp Primrec.fst) Primrec.snd)
      (Primrec.const κ)).to₂

/-- The parameters of the constraint entries, as one tuple. -/
abbrev ConsParams : Type := Data × ℕ × ℕ × ℕ × ℕ × List ℕ

set_option maxHeartbeats 1000000 in
theorem primrec_consAt :
    Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr =>
      consAt q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2.1 q.1.1.2.2.2.2.1 q.1.1.2.2.2.2.2
        q.1.2.1 q.1.2.2 q.2 := by
  have hP : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hpd : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1.1 := Primrec.fst.comp hP
  have hT : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp hP)
  have hk : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hP))
  have hn : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hP)))
  have hs : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp hP))))
  have hlR : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp hP))))
  have hv : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hv' : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hγ : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.2 := Primrec.snd
  have hlv : Primrec fun q : (ConsParams × ℕ × ℕ) × BitStr => q.1.1.2.2.2.2.2.getD q.1.2.1 0 :=
    (Primrec.list_getD 0).comp hlR hv
  have hrun := primrec_lpRun hpd hT hk hn (primrec_zOf.comp hs hv) (primrec_zOf.comp hs hv')
    (Primrec.list_take.comp hlv hγ) (Primrec.list_drop.comp hlv hγ)
  exact Primrec.list_map hrun
    ((hv.comp Primrec.fst).pair ((hv'.comp Primrec.fst).pair
      ((hγ.comp Primrec.fst).pair Primrec.snd))).to₂

set_option maxHeartbeats 1000000 in
theorem primrec_consT_params :
    Primrec fun q : ConsParams =>
      consT q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 := by
  have hγ : Primrec₂ fun (q : ConsParams × ℕ × ℕ) (γ : BitStr) =>
      consAt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2.1 q.1.2.2.2.2.2 q.2.1 q.2.2 γ :=
    primrec_consAt.to₂
  have hlen : Primrec fun q : ConsParams × ℕ × ℕ =>
      Data.bitStrsOfLen (q.1.2.2.2.2.2.getD q.2.1 0 + q.1.2.2.2.2.2.getD q.2.2 0) :=
    Data.primrec_bitStrsOfLen.comp (Primrec.nat_add.comp
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))) (Primrec.fst.comp Primrec.snd))
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))) (Primrec.snd.comp Primrec.snd)))
  have hV' : Primrec₂ fun (q : ConsParams × ℕ) (v' : ℕ) =>
      (Data.bitStrsOfLen (q.1.2.2.2.2.2.getD q.2 0 + q.1.2.2.2.2.2.getD v' 0)).flatMap
        fun γ => consAt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2.1 q.1.2.2.2.2.2 q.2 v' γ :=
    (Primrec.list_flatMap (hlen.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
      (hγ.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)))
        Primrec.snd).to₂).to₂
  have hrange : Primrec fun q : ConsParams => List.range (2 ^ (q.2.2.2.2.1 + 1)) :=
    Primrec.list_range.comp (primrec_nat_pow.comp (Primrec.const 2) (Primrec.succ.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        Primrec.snd))))))
  have hV : Primrec₂ fun (q : ConsParams) (v : ℕ) =>
      (List.range (2 ^ (q.2.2.2.2.1 + 1))).flatMap fun v' =>
        (Data.bitStrsOfLen (q.2.2.2.2.2.getD v 0 + q.2.2.2.2.2.getD v' 0)).flatMap
          fun γ => consAt q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 v v' γ :=
    (Primrec.list_flatMap (hrange.comp Primrec.fst) (hV'.comp Primrec.fst Primrec.snd).to₂).to₂
  exact (Primrec.list_flatMap hrange hV).of_eq fun q => rfl

/-- **The tabulation is primitive recursive** in its parameters. -/
theorem primrec_tabOfT (ℓ : ℕ) {sd ld pd : α → Data} {s T k n : α → ℕ} (hsd : Primrec sd)
    (hld : Primrec ld) (hpd : Primrec pd) (hs : Primrec s) (hT : Primrec T) (hk : Primrec k)
    (hn : Primrec n) :
    Primrec fun a => tabOfT ℓ (sd a) (ld a) (pd a) (s a) (T a) (k a) (n a) := by
  have hnV : Primrec fun a => 2 ^ (s a + 1) - 1 :=
    Primrec.nat_sub.comp (primrec_nat_pow.comp (Primrec.const 2) (Primrec.succ.comp hs))
      (Primrec.const 1)
  have hlR := primrec_lenList hld hT hk hn hs false
  have hlL := primrec_lenList hld hT hk hn hs true
  have hw : Primrec fun a => Verifier.weightList (s a)
      (fun z => Verifier.bitsToIdx (false :: margN ℓ (sd a) (T a) (k a) (n a) (s a) .alice z))
      (fun z => Verifier.bitsToIdx (true :: margN ℓ (sd a) (T a) (k a) (n a) (s a) .bob z)) := by
    refine Primrec.list_map (Data.primrec_bitStrsOfLen.comp hs) ?_
    exact (((Verifier.primrec_tagIdxOf false).comp (primrec_margN ℓ hsd hT hk hn hs .alice)).pair
      (((Verifier.primrec_tagIdxOf true).comp (primrec_margN ℓ hsd hT hk hn hs .bob)).pair
        (Primrec.const 1))).to₂
  -- Composing with the expected type stated times out; stating it afterwards does not.
  have hcons0 := primrec_consT_params.comp (hpd.pair (hT.pair (hk.pair (hn.pair (hs.pair hlR)))))
  have hcons : Primrec fun a => consT (pd a) (T a) (k a) (n a) (s a) (lenList (ld a) (T a)
      (k a) (n a) (s a) false) := hcons0.of_eq fun a => rfl
  have htup := hnV.pair (hlR.pair (hlL.pair (hw.pair hcons)))
  have h2 := (Primrec.of_equiv_symm (e := TailoredGameData.equivTuple)).comp htup
  exact h2.of_eq fun a => rfl

end Primrec

/-! ## The runs, under a time bound -/

section Correct

variable {ℓ : ℕ}

/-- The dimension query, under a time bound. -/
theorem dimOf_eq_of (S : CL.Sampler ℓ) {n T k : ℕ} (hb : S.TimeBoundAt n T k) :
    Halting.dimOf (encode S.prog) T k n = S.dim n := by
  rw [Halting.dimOf, show Machine.runForD (encode S.prog)
      (encode (n, CL.Sampler.Query.dimension))
      (T * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ k)
      = S.queryUnder T k n CL.Sampler.Query.dimension from rfl, S.queryUnder_dimension hb]
  simp [SizedEncoding.decode_encode]

/-- A marginal query, under a time bound, at a level at least `1`. -/
theorem margAt_eq_of (S : CL.Sampler ℓ) {n T k : ℕ} (hb : S.TimeBoundAt n T k) (hℓ : 1 ≤ ℓ)
    (w : Player) (z : BitStr) (hz : z.length = S.dim n) :
    margAt ℓ (encode S.prog) T k n w z = CL.toBits ((S.cl n w).eval (CL.ofBits (S.dim n) z)) := by
  rw [margAt, show Machine.runForD (encode S.prog)
      (encode (n, CL.Sampler.Query.marginal w ℓ z))
      (T * ((encode (CL.Sampler.Query.marginal w ℓ z) : Data).size + 1) ^ k)
      = S.queryUnder T k n (CL.Sampler.Query.marginal w ℓ z) from rfl,
    S.queryUnder_marginal hb hℓ w z hz]
  simp [SizedEncoding.decode_encode]

/-- At level `0` the questions are empty: the CL function of level `0` is the zero map, which is
exactly on the empty set only. -/
theorem dim_eq_zero_of_level_zero (S : CL.Sampler 0) (n : ℕ) : S.dim n = 0 := by
  have h := S.cl_exactlyOn n .alice
  rw [CL.CLFun.eq_zero (S.cl n .alice), CL.CLFun.exactlyOn_zero, Finset.univ_eq_empty_iff]
    at h
  simpa using h

/-- **The normalized marginal is the sampler's**, at every level. -/
theorem margN_eq_of (S : CL.Sampler ℓ) {n T k : ℕ} (hb : S.TimeBoundAt n T k) (w : Player)
    (z : BitStr) (hz : z.length = S.dim n) :
    margN ℓ (encode S.prog) T k n (S.dim n) w z =
      CL.toBits ((S.cl n w).eval (CL.ofBits (S.dim n) z)) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have h0 := dim_eq_zero_of_level_zero S n
    have hl : (margN 0 (encode S.prog) T k n (S.dim n) w z).length = 0 := by
      unfold margN
      split_ifs with h
      · rw [h, h0]
      · simp [h0]
    rw [List.eq_nil_of_length_eq_zero hl, eq_comm, ← List.length_eq_zero_iff, CL.length_toBits,
      h0]
  · unfold margN
    rw [margAt_eq_of S hb hℓ w z hz, ite_eq_left (CL.length_toBits _)]

/-- Under a time bound, the budgeted run of the answer-length calculator is its output. -/
theorem lenIs_lenRun (L : Decider) {n T k : ℕ} (hb : L.TimeBoundAt n T k) (x : BitStr)
    (κ : Bool) : LenIs L n x κ (lenRun (encode L.prog) T k n x κ) := by
  obtain ⟨r, t, ht, h⟩ := hb (encode (x, κ))
  refine ⟨t, r, h, ?_⟩
  rw [lenRun, show Machine.runForD (encode L.prog) (encode (n, x, κ))
    (T * ((encode (x, κ) : Data).size + 1) ^ k) = some r from Machine.runForD_eq_some h ht]
  simp [unaryToNat_eq_length]

/-- Under a time bound, the budgeted run of the linear-constraints processor is its output. -/
theorem lpIs_lpRun (P : Decider) {n T k : ℕ} (hb : P.TimeBoundAt n T k) (x y aR bR : BitStr) :
    LpIs P n x y aR bR (lpRun (encode P.prog) T k n x y aR bR) := by
  obtain ⟨r, t, ht, h⟩ := hb (encode (x, y, aR, bR))
  refine ⟨t, r, h, ?_⟩
  rw [lpRun, show Machine.runForD (encode P.prog) (encode (n, x, y, aR, bR))
    (T * ((encode (x, y, aR, bR) : Data).size + 1) ^ k) = some r
    from Machine.runForD_eq_some h ht]
  rfl

theorem lenOf_eq_lenRun (V : TailoredVerifier ℓ) {n T k : ℕ} (hb : V.len.TimeBoundAt n T k)
    (x : BitStr) (κ : Bool) : V.lenOf n x κ = lenRun (encode V.len.prog) T k n x κ := by
  have h := lenIs_lenRun V.len hb x κ
  have hex : ∃ m, LenIs V.len n x κ m := ⟨_, h⟩
  unfold TailoredVerifier.lenOf
  rw [dite_eq_left hex]
  exact hex.choose_spec.unique h

theorem consOf_eq_lpRun (V : TailoredVerifier ℓ) {n T k : ℕ} (hL : V.len.TimeBoundAt n T k)
    (hP : V.lp.TimeBoundAt n T k) (x y aR bR : BitStr) :
    V.consOf n x y aR bR = lpRun (encode V.lp.prog) T k n x y aR bR :=
  V.consOf_eq_of (fun κ => ⟨_, lenIs_lenRun V.len hL x κ⟩)
    (fun κ => ⟨_, lenIs_lenRun V.len hL y κ⟩) (lpIs_lpRun V.lp hP x y aR bR)

/-! ## The vertices -/

theorem testBit_bitsToIdx (l : BitStr) (j : ℕ) :
    (Verifier.bitsToIdx l).testBit j = l.getD j false := by
  induction l generalizing j with
  | nil => simp
  | cons b l ih =>
    have h : Verifier.bitsToIdx (b :: l) = Nat.bit b (Verifier.bitsToIdx l) := by
      rw [Verifier.bitsToIdx_cons]
      cases b
      · simp [Nat.bit]
      · simp [Nat.bit]; omega
    rw [h]
    cases j with
    | zero => rw [Nat.testBit_bit_zero, List.getD_cons_zero]
    | succ j => rw [Nat.testBit_bit_succ, ih, List.getD_cons_succ]

theorem zOf_bitsToIdx {s : ℕ} (b : Bool) (z : BitStr) (hz : z.length = s) :
    zOf s (Verifier.bitsToIdx (b :: z)) = z := by
  apply List.ext_getElem
  · simp [zOf, hz]
  · intro i _ h2
    simp only [zOf, List.getElem_map, List.getElem_range, testBit_bitsToIdx]
    rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]

theorem tabOfT_nV (ℓ : ℕ) (sd ld pd : Data) (s T k n : ℕ) :
    (tabOfT ℓ sd ld pd s T k n).nV + 1 = 2 ^ (s + 1) :=
  Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)

/-- The vertices of the tabulation are the doubled questions: a tag and a point of `𝔽₂^s`. -/
noncomputable def vtxEquiv (ℓ : ℕ) (sd ld pd : Data) (s T k n : ℕ) :
    Fin ((tabOfT ℓ sd ld pd s T k n).nV + 1) ≃ Bool × (Fin s → CL.𝔽₂) :=
  (finCongr (tabOfT_nV ℓ sd ld pd s T k n)).trans (Verifier.tagEquiv s).symm

theorem vtxEquiv_apply (ℓ : ℕ) (sd ld pd : Data) (s T k n : ℕ)
    (i : Fin ((tabOfT ℓ sd ld pd s T k n).nV + 1)) :
    Verifier.bitsToIdx ((vtxEquiv ℓ sd ld pd s T k n i).1 ::
      CL.toBits (vtxEquiv ℓ sd ld pd s T k n i).2) = i := by
  rw [vtxEquiv, Equiv.trans_apply, Verifier.bitsToIdx_tagEquiv_symm]
  simp

theorem zOf_vtxEquiv (ℓ : ℕ) (sd ld pd : Data) (s T k n : ℕ)
    (i : Fin ((tabOfT ℓ sd ld pd s T k n).nV + 1)) :
    zOf s i = CL.toBits (vtxEquiv ℓ sd ld pd s T k n i).2 := by
  conv_lhs => rw [← vtxEquiv_apply ℓ sd ld pd s T k n i]
  exact zOf_bitsToIdx _ _ (CL.length_toBits _)

theorem lenList_getD (ℓ : ℕ) (sd ld pd : Data) (s T k n : ℕ) (κ : Bool)
    (i : Fin ((tabOfT ℓ sd ld pd s T k n).nV + 1)) :
    (lenList ld T k n s κ).getD i 0 = lenRun ld T k n (zOf s i) κ :=
  Data.getD_range_map (fun v => lenRun ld T k n (zOf s v) κ)
    (tabOfT_nV ℓ sd ld pd s T k n ▸ i.isLt)

theorem mem_consT (pd : Data) (T k n s : ℕ) (lR : List ℕ) (v v' : ℕ) (γ c : BitStr) :
    (v, v', γ, c) ∈ consT pd T k n s lR ↔ v < 2 ^ (s + 1) ∧ v' < 2 ^ (s + 1) ∧
      γ.length = lR.getD v 0 + lR.getD v' 0 ∧
      c ∈ lpRun pd T k n (zOf s v) (zOf s v') (γ.take (lR.getD v 0)) (γ.drop (lR.getD v 0)) := by
  simp only [consT, consAt, List.mem_flatMap, List.mem_map, List.mem_range,
    Data.mem_bitStrsOfLen, Prod.mk.injEq]
  constructor
  · rintro ⟨v₀, hv₀, v₀', hv₀', γ₀, hγ₀, c₀, hc₀, rfl, rfl, rfl, rfl⟩
    exact ⟨hv₀, hv₀', hγ₀, hc₀⟩
  · rintro ⟨hv, hv', hγ, hc⟩
    exact ⟨v, hv, v', hv', γ, hγ, c, hc, rfl, rfl, rfl, rfl⟩

/-! ## The question distribution -/

/-- **The `μ` clause**: the tabulated weight of a pair of vertices is the doubled distribution
of the sampler — the weight list enumerates `𝔽₂^s` once, each point at the pair its two tagged
marginals land on (`MIPRE.Halting.mu_clauseL`, for a sampler of any level). -/
theorem mu_tabOfT (S : CL.Sampler ℓ) {n T k : ℕ} (hS : S.TimeBoundAt n T k) (ld pd : Data)
    (i j : Fin ((tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).nV + 1)) :
    (tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).toGame.μ i j =
      if (vtxEquiv ℓ (encode S.prog) ld pd (S.dim n) T k n i).1 = false ∧
          (vtxEquiv ℓ (encode S.prog) ld pd (S.dim n) T k n j).1 = true then
        S.dist n (vtxEquiv ℓ (encode S.prog) ld pd (S.dim n) T k n i).2
          (vtxEquiv ℓ (encode S.prog) ld pd (S.dim n) T k n j).2
      else 0 := by
  classical
  set e := vtxEquiv ℓ (encode S.prog) ld pd (S.dim n) T k n with he
  have hlen : ∀ (w : Player) (z : BitStr), z.length = S.dim n →
      (margN ℓ (encode S.prog) T k n (S.dim n) w z).length = S.dim n := by
    intro w z hz
    rw [margN_eq_of S hS w z hz, CL.length_toBits]
  have hrange : ∀ (tg : Bool) (w : Player), ∀ z ∈ Data.bitStrsOfLen (S.dim n),
      Verifier.bitsToIdx (tg :: margN ℓ (encode S.prog) T k n (S.dim n) w z)
        < (tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).nV + 1 := by
    intro tg w z hz
    have hlt := Verifier.bitsToIdx_lt (tg :: margN ℓ (encode S.prog) T k n (S.dim n) w z)
    rw [List.length_cons, hlen w z ((Data.mem_bitStrsOfLen _ _).1 hz)] at hlt
    rw [tabOfT_nV]
    exact hlt
  have htot : (tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).weights.totalWeight =
      2 ^ S.dim n :=
    Verifier.totalWeight_weightList _ _ _ _ _ _ (hrange false .alice) (hrange true .bob)
  have hqw : ∀ a b : ℕ, (tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).weights.questionWeight
      a b = ((Data.bitStrsOfLen (S.dim n)).filter fun z =>
          decide (Verifier.bitsToIdx (false :: margN ℓ (encode S.prog) T k n (S.dim n) .alice z)
              = a ∧
            Verifier.bitsToIdx (true :: margN ℓ (encode S.prog) T k n (S.dim n) .bob z)
              = b)).length :=
    fun a b => Verifier.questionWeight_weightList _ _ _ _ _ _ a b
  have hidx : ∀ (w : Player) (tg : Bool) (z : BitStr), z.length = S.dim n →
      ∀ m : Fin ((tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).nV + 1),
      Verifier.bitsToIdx (tg :: margN ℓ (encode S.prog) T k n (S.dim n) w z) = (m : ℕ) ↔
        (tg = (e m).1 ∧ (S.cl n w).eval (CL.ofBits (S.dim n) z) = (e m).2) := by
    intro w tg z hz m
    rw [margN_eq_of S hS w z hz, ← vtxEquiv_apply ℓ (encode S.prog) ld pd (S.dim n) T k n m,
      Verifier.bitsToIdx_cons_toBits_eq_iff]
  show (if (tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).weights.totalWeight = 0 then
      (if i = 0 ∧ j = 0 then 1 else 0)
    else ((tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).weights.questionWeight i j : ℝ) /
      ((tabOfT ℓ (encode S.prog) ld pd (S.dim n) T k n).weights.totalWeight : ℝ)) = _
  rw [htot, ite_eq_right (Nat.two_pow_pos _).ne', hqw]
  by_cases htag : (e i).1 = false ∧ (e j).1 = true
  · rw [ite_eq_left htag]
    have hnum : ((Data.bitStrsOfLen (S.dim n)).filter fun z =>
          decide (Verifier.bitsToIdx (false :: margN ℓ (encode S.prog) T k n (S.dim n) .alice z)
              = (i : ℕ) ∧
            Verifier.bitsToIdx (true :: margN ℓ (encode S.prog) T k n (S.dim n) .bob z)
              = (j : ℕ))).length
        = (Finset.univ.filter fun v : Fin (S.dim n) → CL.𝔽₂ =>
            (S.cl n .alice).eval v = (e i).2 ∧ (S.cl n .bob).eval v = (e j).2).card := by
      rw [show ((Data.bitStrsOfLen (S.dim n)).filter fun z =>
          decide (Verifier.bitsToIdx (false :: margN ℓ (encode S.prog) T k n (S.dim n) .alice z)
              = (i : ℕ) ∧
            Verifier.bitsToIdx (true :: margN ℓ (encode S.prog) T k n (S.dim n) .bob z)
              = (j : ℕ)))
          = ((Data.bitStrsOfLen (S.dim n)).filter fun z =>
            (fun v : Fin (S.dim n) → CL.𝔽₂ =>
              decide ((S.cl n .alice).eval v = (e i).2 ∧ (S.cl n .bob).eval v = (e j).2))
              (CL.ofBits (S.dim n) z)) from ?_]
      · rw [Verifier.length_filter_bitStrsOfLen (s := S.dim n)
          (fun v => decide ((S.cl n .alice).eval v = (e i).2 ∧
            (S.cl n .bob).eval v = (e j).2))]
        congr 1
      · refine List.filter_congr fun z hz => ?_
        have hz' : z.length = S.dim n := (Data.mem_bitStrsOfLen _ _).1 hz
        simp only [decide_eq_decide]
        rw [hidx .alice false z hz' i, hidx .bob true z hz' j, htag.1, htag.2]
        simp
    rw [hnum, show S.dist n (e i).2 (e j).2
        = ((Finset.univ.filter fun v : Fin (S.dim n) → CL.𝔽₂ =>
            (S.cl n .alice).eval v = (e i).2 ∧ (S.cl n .bob).eval v = (e j).2).card : ℝ)
          / (Fintype.card (Fin (S.dim n) → CL.𝔽₂) : ℝ) from rfl]
    congr 1
    simp
  · rw [ite_eq_right htag]
    have hnil : ((Data.bitStrsOfLen (S.dim n)).filter fun z =>
        decide (Verifier.bitsToIdx (false :: margN ℓ (encode S.prog) T k n (S.dim n) .alice z)
            = (i : ℕ) ∧
          Verifier.bitsToIdx (true :: margN ℓ (encode S.prog) T k n (S.dim n) .bob z)
            = (j : ℕ))) = [] := by
      refine List.filter_eq_nil_iff.2 fun z hz => ?_
      have hz' : z.length = S.dim n := (Data.mem_bitStrsOfLen _ _).1 hz
      simp only [decide_eq_true_eq, not_and]
      intro h1 h2
      exact htag ⟨((hidx .alice false z hz' i).1 h1).1.symm,
        ((hidx .bob true z hz' j).1 h2).1.symm⟩
    rw [hnil]
    simp

/-! ## The presentation -/

/-- **The tabulation presents the doubled game** of a tailored verifier whose three programs run
within the budget `T · (|d| + 1) ^ k` at index `n`. -/
theorem presents_tabOfT (V : TailoredVerifier ℓ) {n T k : ℕ} (hS : V.sampler.TimeBoundAt n T k)
    (hL : V.len.TimeBoundAt n T k) (hP : V.lp.TimeBoundAt n T k) :
    Presents (tabOfT ℓ (encode V.sampler.prog) (encode V.len.prog) (encode V.lp.prog)
        (V.sampler.dim n) T k n) (V.tgame n).doubled
      (vtxEquiv ℓ (encode V.sampler.prog) (encode V.len.prog) (encode V.lp.prog)
        (V.sampler.dim n) T k n) := by
  set sd := encode V.sampler.prog
  set ld := encode V.len.prog
  set pd := encode V.lp.prog
  have hR : ∀ (κ : Bool) (i : Fin ((tabOfT ℓ sd ld pd (V.sampler.dim n) T k n).nV + 1)),
      (lenList ld T k n (V.sampler.dim n) κ).getD i 0 =
        V.lenOf n (CL.toBits (vtxEquiv ℓ sd ld pd (V.sampler.dim n) T k n i).2) κ := by
    intro κ i
    rw [lenList_getD, zOf_vtxEquiv, lenOf_eq_lenRun V hL]
  refine ⟨fun i j => mu_tabOfT V.sampler hS ld pd i j, fun i => hR false i, fun i => hR true i,
    fun i j γ c hγ => ?_⟩
  have hi : (i : ℕ) < 2 ^ (V.sampler.dim n + 1) := tabOfT_nV ℓ sd ld pd _ T k n ▸ i.isLt
  have hj : (j : ℕ) < 2 ^ (V.sampler.dim n + 1) := tabOfT_nV ℓ sd ld pd _ T k n ▸ j.isLt
  show (↑i, ↑j, γ, c) ∈ consT pd T k n (V.sampler.dim n) (lenList ld T k n (V.sampler.dim n) false)
    ↔ c ∈ V.consOf n (CL.toBits (vtxEquiv ℓ sd ld pd (V.sampler.dim n) T k n i).2)
      (CL.toBits (vtxEquiv ℓ sd ld pd (V.sampler.dim n) T k n j).2)
      (γ.take (V.lenOf n (CL.toBits (vtxEquiv ℓ sd ld pd (V.sampler.dim n) T k n i).2) false))
      (γ.drop (V.lenOf n (CL.toBits (vtxEquiv ℓ sd ld pd (V.sampler.dim n) T k n i).2) false))
  rw [mem_consT, hR false i, hR false j, consOf_eq_lpRun V hL hP, ← zOf_vtxEquiv,
    ← zOf_vtxEquiv]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hi, hj, by rw [zOf_vtxEquiv, zOf_vtxEquiv]; exact hγ, h⟩⟩

end Correct

/-! ## The tabulation of a description string -/

section Strings

variable {ℓ : ℕ} (TG : TailoredGapCompression ℓ)

/-- **The tabulation of the verifier a description string denotes**, at index `n`: the compressed
sampler and answer-length calculator at the string's parameter `λ`, the string's processor, and
the budget `n^λ · (|d| + 1)^λ` that `λ`-boundedness supplies. -/
noncomputable def tabT (x : BitStr) (n : ℕ) : TailoredGameData :=
  tabOfT ℓ (encode (TG.samplerProg (Halting.descLam x)))
    (encode (TG.lenProg (Halting.descLam x))) (Halting.descDecD x)
    (Halting.dimOf (encode (TG.samplerProg (Halting.descLam x))) (n ^ Halting.descLam x)
      (Halting.descLam x) n)
    (n ^ Halting.descLam x) (Halting.descLam x) n

theorem primrec_tabOfT_tuple (ℓ : ℕ) :
    Primrec fun q : (Data × Data × Data) × ℕ × ℕ × ℕ × ℕ =>
      tabOfT ℓ q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 :=
  primrec_tabOfT ℓ (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem primrec_dimOf_tuple :
    Primrec fun q : Data × ℕ × ℕ × ℕ => Halting.dimOf q.1 q.2.1 q.2.2.1 q.2.2.2 :=
  primrec_dimOf Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem computable_samplerData : Computable fun p : BitStr × ℕ =>
    (encode (TG.samplerProg (Halting.descLam p.1)) : Data) :=
  PolyTimeFun.computable_encode_comp TG.samplerProg (fun p : BitStr × ℕ => Halting.descLam p.1)
    (Data.primrec_encode_nat.comp (Halting.primrec_descLam.comp Primrec.fst)).to_comp

theorem computable_lenData : Computable fun p : BitStr × ℕ =>
    (encode (TG.lenProg (Halting.descLam p.1)) : Data) :=
  PolyTimeFun.computable_encode_comp TG.lenProg (fun p : BitStr × ℕ => Halting.descLam p.1)
    (Data.primrec_encode_nat.comp (Halting.primrec_descLam.comp Primrec.fst)).to_comp

theorem computable_dimT : Computable fun p : BitStr × ℕ =>
    Halting.dimOf (encode (TG.samplerProg (Halting.descLam p.1))) (p.2 ^ Halting.descLam p.1)
      (Halting.descLam p.1) p.2 := by
  have hlam : Primrec fun p : BitStr × ℕ => Halting.descLam p.1 :=
    Halting.primrec_descLam.comp Primrec.fst
  have h := primrec_dimOf_tuple.to_comp.comp ((computable_samplerData TG).pair
    ((primrec_nat_pow.comp Primrec.snd hlam).to_comp.pair (hlam.to_comp.pair Computable.snd)))
  exact h.of_eq fun _ => rfl

/-- **The tabulation of a description string is computable** in the string and the index. -/
theorem computable_tabT : Computable fun p : BitStr × ℕ => tabT TG p.1 p.2 := by
  have hlam : Primrec fun p : BitStr × ℕ => Halting.descLam p.1 :=
    Halting.primrec_descLam.comp Primrec.fst
  have hpd : Primrec fun p : BitStr × ℕ => Halting.descDecD p.1 :=
    Data.primrec_right.comp (Data.primrec_parse.comp Primrec.fst)
  have h := (primrec_tabOfT_tuple ℓ).to_comp.comp
    (((computable_samplerData TG).pair ((computable_lenData TG).pair hpd.to_comp)).pair
      ((computable_dimT TG).pair ((primrec_nat_pow.comp Primrec.snd hlam).to_comp.pair
        (hlam.to_comp.pair Computable.snd))))
  exact h.of_eq fun _ => rfl

/-- **The tabulation of a description is correct**: on the description of a `λ`-bounded tailored
verifier `(S^λ, L^λ, P)`, at every index `n ≥ 2`, it presents the doubled `n`-th game. -/
theorem presents_tabT (lam : ℕ) (P : Decider)
    (hb : (⟨TG.sampler lam, TG.len lam, P⟩ : TailoredVerifier ℓ).IsBounded lam) {n : ℕ}
    (hn : 2 ≤ n) :
    ∃ e, Presents (tabT TG (Halting.descOf lam P.prog) n)
      ((⟨TG.sampler lam, TG.len lam, P⟩ : TailoredVerifier ℓ).tgame n).doubled e := by
  obtain ⟨-, hS, hL, hP, -⟩ := hb.1 n hn
  have htab : tabT TG (Halting.descOf lam P.prog) n = tabOfT ℓ (encode (TG.sampler lam).prog)
      (encode (TG.len lam).prog) (encode P.prog) ((TG.sampler lam).dim n) (n ^ lam) lam n := by
    rw [tabT, Halting.descLam_descOf, Halting.descDecD_descOf, TG.samplerProg_eq,
      TG.lenProg_eq, dimOf_eq_of _ hS]
  rw [htab]
  exact ⟨_, presents_tabOfT (V := ⟨TG.sampler lam, TG.len lam, P⟩) hS hL hP⟩

end Strings

end MIPRE.Tailored

end
