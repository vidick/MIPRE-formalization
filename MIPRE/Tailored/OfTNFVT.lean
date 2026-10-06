/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
module
public import MIPRE.Tailored.OfTNFV
public import MIPRE.Tailored.CanonicalCost
public import MIPRE.Foundations.Halting.WrapperCostAt
public import MIPRE.Foundations.GapCompression

@[expose] public section

/-!
# A tailored verifier as a bounded normal form verifier

`TailoredVerifier.ofTNFV U V` (`MIPRE.Tailored.OfTNFV`) presents a tailored verifier as a
normal form verifier, its decider the canonical decider `canonProg` in the wrapper of
`Verifier.ofSamplerDecider`; `canonProg` is bounded on encodings only. `ofTNFVT U V` is the same
with the total parse in front, `canonProgT` (`MIPRE.Tailored.CanonicalCost`), which accepts the
same inputs and is bounded on every input. So it denotes the same games, and it is
`λ'`-bounded for a `λ'` linear in `λ`:

* `ofTNFVT_accepts_iff`, `ofTNFVT_game`: the decider accepts what that of `ofTNFV` accepts, so
  the games are equal, and `valStar_ofTNFVT`, `hasPerfectPCC_ofTNFVT` transport
  `valStar_ofTNFV`, `hasPerfectPCC_ofTNFV`;
* `dom_wrapCoreCost`: the wrapper's explicit cost `Prog.wrapCoreCost`, at the sampler's bound
  `Cs` and degree `K`, is dominated by `c (W + 1)^m X^{e (K + 1)}` (`MIPRE.Repeat.Dom`) once `W`
  is above `10^K`, `Cs`, the dimension and the sizes of the index and of the two programs;
* `ofTNFVT_isBounded`: **for a fixed universal machine `U` there is a constant `C` such that
  every `λ`-bounded tailored verifier `V` gives a `(C λ)`-bounded normal form verifier
  `ofTNFVT U V`.** The decider's clause is the wrapper's cost at the index in question
  (`Prog.wrapCore_cost_at`, which needs the sampler's bound at that index only, `n ≥ 2` being
  all `λ`-boundedness supplies) on the canonical decider's (`canonProgT_timeBound`), dominated
  with `W = n^{A λ}`; the size clause is `esize_wrapCore` and `esize_canonProgT`.
-/

namespace MIPRE.Tailored

open Cost Cost.Data Cost.Prog

/-! ## Arithmetic at `n ≥ 2` -/

theorem le_pow_self_of_two_le {n : ℕ} (hn : 2 ≤ n) (x : ℕ) : x ≤ n ^ x :=
  (Nat.lt_two_pow_self (n := x)).le.trans (Nat.pow_le_pow_left hn x)

theorem pow_le_pow_mul {n a b lam : ℕ} (hn : 2 ≤ n) (hab : a ≤ b) :
    n ^ (a * lam) ≤ n ^ (b * lam) :=
  Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right lam hab)

/-- `10^λ ≤ n^{4 λ}` for `n ≥ 2`. -/
theorem ten_pow_le {n : ℕ} (hn : 2 ≤ n) (lam : ℕ) : 10 ^ lam ≤ n ^ (4 * lam) := by
  calc 10 ^ lam ≤ (2 ^ 4) ^ lam := Nat.pow_le_pow_left (by norm_num) lam
    _ ≤ (n ^ 4) ^ lam := Nat.pow_le_pow_left (Nat.pow_le_pow_left hn 4) lam
    _ = n ^ (4 * lam) := by rw [← pow_mul]

/-- `esize n ≤ n^4` for `n ≥ 2`: the binary numeral has at most `n` digits. -/
theorem esize_nat_le_pow_four {n : ℕ} (hn : 2 ≤ n) : esize n ≤ n ^ 4 := by
  have h1 : esize n ≤ 4 * n + 1 :=
    (esize_nat_le n).trans (by have := Nat.size_le.2 (Nat.lt_two_pow_self (n := n)); omega)
  have h2 : n ^ 4 = n * n ^ 3 := by ring
  have h3 : 8 ≤ n ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  nlinarith

namespace TailoredVerifier

variable {ℓ : ℕ} (V : TailoredVerifier ℓ)

/-! ## The verifier, and its games -/

/-- **A tailored verifier as a normal form verifier, with a total parse**: its sampler, and the
canonical decider with the parse in front (`canonProgT`), wrapped in the question-length
check. -/
noncomputable def ofTNFVT (U : UniversalMachine) : Verifier ℓ :=
  Verifier.ofSamplerDecider U V.sampler (canonProgT V.len.prog V.lp.prog)

@[simp] theorem ofTNFVT_sampler (U : UniversalMachine) : (V.ofTNFVT U).sampler = V.sampler :=
  rfl

/-- The decider accepts exactly what that of `ofTNFV` accepts, on every input. -/
theorem ofTNFVT_accepts_iff_ofTNFV (U : UniversalMachine) (n : ℕ) (x y a b : BitStr) :
    (V.ofTNFVT U).decider.Accepts n x y a b ↔ (V.ofTNFV U).decider.Accepts n x y a b := by
  rw [ofTNFVT, ofTNFV, Verifier.ofSamplerDecider_accepts, Verifier.ofSamplerDecider_accepts]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact canonProgT_runs_iff V.len.closed V.lp.closed ((n, x, y, a, b) : DIn) (encode true)

/-- **The normal form verifier's decider accepts exactly what the tailored game accepts.** -/
theorem ofTNFVT_accepts_iff (U : UniversalMachine) (n : ℕ) (x y : V.Questions n)
    (a b : BitStr) :
    (V.ofTNFVT U).decider.Accepts n (CL.toBits x) (CL.toBits y) a b ↔
      (V.tgame n).Accepts x y a b :=
  (V.ofTNFVT_accepts_iff_ofTNFV U _ _ _ _ _).trans (V.ofTNFV_accepts_iff U n x y a b)

/-- **The games are those of `ofTNFV`.** -/
theorem ofTNFVT_game (U : UniversalMachine) (n T : ℕ) :
    (V.ofTNFVT U).game n T = (V.ofTNFV U).game n T := by
  unfold Verifier.game
  congr 1
  funext x y a b
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact V.ofTNFVT_accepts_iff_ofTNFV U n _ _ _ _

/-- **The decision predicates agree** on the answers the tailored game has, embedded in the
answers of length at most `T`. -/
theorem ofTNFVT_game_D (U : UniversalMachine) {n T : ℕ} (hT : (V.tgame n).maxLen ≤ T)
    (x y : V.Questions n) (a b : Verifier.Answers (V.tgame n).maxLen) :
    ((V.ofTNFVT U).game n T).D x y (Verifier.Answers.castLE hT a)
        (Verifier.Answers.castLE hT b) =
      (V.tgame n).toGame.D x y a b := by
  rw [V.ofTNFVT_game U n T]
  exact V.ofTNFV_game_D U hT x y a b

/-- **The values agree**, for an answer bound above the tailored game's answer lengths. -/
theorem valStar_ofTNFVT (U : UniversalMachine) (n T : ℕ) (hT : (V.tgame n).maxLen ≤ T) :
    (V.ofTNFVT U).valStar n T = V.valStar n := by
  rw [← V.valStar_ofTNFV U n T hT]
  unfold Verifier.valStar
  rw [V.ofTNFVT_game U n T]
  rfl

/-- **A perfect ZPC strategy gives a perfect PCC strategy of `ofTNFVT`** (`lem:zpc-pcc`), for an
answer bound above the tailored game's answer lengths. -/
theorem hasPerfectPCC_ofTNFVT (U : UniversalMachine) {n T : ℕ} (hT : (V.tgame n).maxLen ≤ T)
    (h : V.HasPerfectZPC n) : (V.ofTNFVT U).HasPerfectPCC n T := by
  have h' := V.hasPerfectPCC_ofTNFV U hT h
  unfold Verifier.HasPerfectPCC Verifier.doubledGame at h' ⊢
  rw [V.ofTNFVT_game U n T]
  exact h'

end TailoredVerifier

/-! ## The wrapper's cost, dominated -/

open Repeat

theorem _root_.MIPRE.Repeat.Dom.powX {W X K : ℕ} (e : ℕ) : Dom W X K 1 0 e (X ^ (e * (K + 1))) := by
  simp [Dom]

/-- **The wrapper's explicit cost is dominated**: for every domination `(cT, mT, eT)` of the
string's decider's time `T`, there are `c, m, e` with `wrapCoreCost ≤ c (W + 1)^m X^{e (K + 1)}`
— the sampler's bound `Cs` at degree `K` — once `W` is above `10^K`, `Cs`, the dimension and the
sizes of the index and of the two programs, and `X` above the input's size. The constants depend
on the universal machine alone. -/
theorem dom_wrapCoreCost (U : UniversalMachine) (cT mT eT : ℕ) : ∃ c m e,
    ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (dec : Prog) (W X K n Cs T s : ℕ), 1 ≤ X → 10 ^ K ≤ W →
      s + 1 ≤ X → esize S.prog ≤ W → esize dec ≤ W → esize n ≤ W → S.dim n ≤ W → Cs ≤ W →
      Dom W X K cT mT eT T → Dom W X K c m e (wrapCoreCost U S dec (fun _ => Cs) K n T s) := by
  set q : ℕ := (encode CL.Sampler.Query.dimension : Data).size with hq
  have hq10 : q + 1 ≤ 10 ^ (q + 1) := (Nat.lt_pow_self (by norm_num)).le
  have dP : ∀ {W X K : ℕ}, 1 ≤ X → 10 ^ K ≤ W → Dom W X K 1 (q + 1) 1 ((q + 1) ^ K) :=
    fun hX hW => dom_powK hX hW hq10 (Nat.le_mul_of_pos_right _ hX)
  -- the argument of the universal machine on the dimension query
  obtain ⟨cA, mA, eA, hA⟩ : ∃ cA mA eA, ∀ (W X K a b Cs : ℕ), 1 ≤ X → 10 ^ K ≤ W → a ≤ W →
      b ≤ W → Cs ≤ W → Dom W X K cA mA eA (a + (b + q + 1) + Cs * (q + 1) ^ K) :=
    ⟨_, _, _, fun W X K a b Cs hX hW ha hb hC =>
      ((Dom.ofLeW ha).add hX (Dom.ofAffine (a := 1) (b := q + 1) (v := b + q + 1)
        (by omega))).add hX ((Dom.ofLeW hC).mul (dP hX hW))⟩
  obtain ⟨cU, mU, eU, hU⟩ := dom_poly U.bound cA mA eA
  -- the argument of the universal machine on the string's decider
  obtain ⟨cB, mB, eB, hB⟩ : ∃ cB mB eB, ∀ (W X K a b s T : ℕ), 1 ≤ X → a ≤ W → b ≤ W →
      s + 1 ≤ X → Dom W X K cT mT eT T → Dom W X K cB mB eB (a + (b + s + 1) + T) :=
    ⟨_, _, _, fun W X K a b s T hX ha hb hs hT =>
      ((Dom.ofLeW ha).add hX ((Dom.ofLeW hb).add hX (Dom.ofLeX hX (v := s + 1) hs))).add hX hT⟩
  obtain ⟨cV, mV, eV, hV⟩ := dom_poly U.bound cB mB eB
  exact ⟨_, _, _, fun S dec W X K n Cs T s hX hW hs hS hd hn hdim hC hT =>
    have hsz : Nat.size (S.dim n) ≤ W :=
      (Nat.size_le.2 (Nat.lt_two_pow_self (n := S.dim n))).trans hdim
    have hes : esize (S.dim n) ≤ 4 * W + 1 :=
      (esize_nat_le (S.dim n)).trans (by omega)
    have dE := Dom.ofAffine (X := X) (K := K) hes
    have d1 := (((Dom.ofLeW hS).add hX (Dom.ofLeW hn)).add hX (Dom.const q)).add hX dE
    have d2 := (d1.add hX ((Dom.ofLeW hC).mul (dP hX hW))).add hX
      (hU W X K hX (hA W X K _ _ Cs hX hW hS hn hC))
    have d3 := (((Dom.ofLeW hdim).add hX (Dom.const 1)).mul
      (Dom.ofAffine (X := X) (K := K) (a := 4) (b := 14) (v := 4 * S.dim n + 14)
        (by omega))).add hX ((Dom.const 7).mul dE)
    have d4 := (d3.add hX ((Dom.const 8).mul (Dom.ofLeW hdim))).add hX (Dom.const 90)
    have dZ := (d2.add hX (((Dom.ofLeW hsz).add hX (Dom.const 2)).mul d4)).add hX
      (Dom.const 10)
    have dChk := (Dom.const 60).mul
      ((((Dom.ofLeX hX (v := s) (by omega)).add hX (Dom.ofLeW hdim)).add hX
        (Dom.const 30)).pow 2)
    have dR := ((((Dom.ofLeW hd).add hX (Dom.ofLeW hn)).add hX
      (Dom.ofLeX hX (v := s) (by omega))).add hX (Dom.const 2))
    ((((((Dom.const 60).mul (dZ.pow 2)).add hX (Dom.const 4)).add hX
      ((Dom.const 2).mul dChk)).add hX
      (((Dom.const 2).mul dR).add hX (hV W X K hX (hB W X K _ _ s T hX hd hn hs hT)))).add hX
      (Dom.const 20))⟩

/-! ## The bound, at `n ≥ 2` -/

/-- The domination at `W = n^{A λ}`, read as a bound of the shape `TimeBoundAt` asks for. -/
theorem dom_le_pow {n X c m e A lam C : ℕ} (hn : 2 ≤ n) (hlam : 1 ≤ lam) (hX : 1 ≤ X)
    (hC1 : c + (A + 1) * m ≤ C) (hC2 : 2 * e ≤ C) :
    c * (n ^ (A * lam) + 1) ^ m * X ^ (e * (lam + 1)) ≤ n ^ (C * lam) * X ^ (C * lam) := by
  have hpos : 0 < n := by omega
  have h1 : c ≤ n ^ (c * lam) := (le_pow_self_of_two_le hn c).trans
    (Nat.pow_le_pow_right hpos (Nat.le_mul_of_pos_right c hlam))
  have h2 : n ^ (A * lam) + 1 ≤ n ^ ((A + 1) * lam) := by
    have hW : 1 ≤ n ^ (A * lam) := Nat.one_le_pow _ _ hpos
    calc n ^ (A * lam) + 1 ≤ n ^ (A * lam) * n := by nlinarith
      _ = n ^ (A * lam + 1) := (pow_succ _ _).symm
      _ ≤ n ^ ((A + 1) * lam) := Nat.pow_le_pow_right hpos (by nlinarith)
  have h3 : (n ^ (A * lam) + 1) ^ m ≤ n ^ ((A + 1) * lam * m) :=
    (Nat.pow_le_pow_left h2 m).trans_eq (by rw [← pow_mul])
  have h4 : X ^ (e * (lam + 1)) ≤ X ^ (C * lam) := Nat.pow_le_pow_right hX (by nlinarith)
  have h5 : n ^ (c * lam) * n ^ ((A + 1) * lam * m) ≤ n ^ (C * lam) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right hpos (by nlinarith)
  calc c * (n ^ (A * lam) + 1) ^ m * X ^ (e * (lam + 1))
      ≤ n ^ (c * lam) * n ^ ((A + 1) * lam * m) * X ^ (C * lam) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4
    _ ≤ n ^ (C * lam) * X ^ (C * lam) := Nat.mul_le_mul_right _ h5

namespace TailoredVerifier

/-- **A `λ`-bounded tailored verifier is a `(C λ)`-bounded normal form verifier**, for a
constant `C` depending on the universal machine `U` alone. -/
theorem ofTNFVT_isBounded (U : UniversalMachine) :
    ∃ C : ℕ, ∀ {ℓ : ℕ} (V : TailoredVerifier ℓ) (lam : ℕ), V.IsBounded lam →
      (V.ofTNFVT U).IsBounded (C * lam) := by
  obtain ⟨c0, m0, e0, hcanon⟩ := canonProgT_timeBound
  obtain ⟨cT, mT, eT, hTd⟩ : ∃ cT mT eT, ∀ (W K a b n' s : ℕ), a ≤ W → b ≤ W → n' ≤ W →
      Dom W (s + 1) K cT mT eT (c0 * (a + b + n' + 1) ^ m0 * (s + 1) ^ (e0 * (K + 1))) :=
    ⟨_, _, _, fun W K a b n' s ha hb hn =>
      ((Dom.const c0).mul ((Dom.ofAffine (a := 3) (b := 1) (v := a + b + n' + 1)
        (by omega)).pow m0)).mul (Dom.powX e0)⟩
  obtain ⟨c, m, e, hW⟩ := dom_wrapCoreCost U cT mT eT
  refine ⟨c + (esize (canonProgT Prog.nil Prog.nil) + 9 + 1) * m + 2 * e +
    esize (wrapCore U.univ Prog.nil Data.nil) + esize (canonProgT Prog.nil Prog.nil) + 7,
    fun {ℓ} V lam hV => ?_⟩
  have hdec0 := esize_canonProgT V.len.prog V.lp.prog
  have hwr := esize_wrapCore U.univ V.sampler.prog (encode (canonProgT V.len.prog V.lp.prog))
  have hencd : (encode (canonProgT V.len.prog V.lp.prog) : Data).size =
      esize (canonProgT V.len.prog V.lp.prog) := rfl
  set Kw := esize (wrapCore U.univ Prog.nil Data.nil) with hKw
  set Kc := esize (canonProgT Prog.nil Prog.nil) with hKc
  set A := Kc + 9 with hA
  set C := c + (A + 1) * m + 2 * e + Kw + Kc + 7 with hC
  set dec := canonProgT V.len.prog V.lp.prog with hdecdef
  obtain ⟨hVn, hVs⟩ := hV
  have hVs' : max (esize V.sampler.prog) (max (esize V.len.prog) (esize V.lp.prog)) ≤ lam := hVs
  have hS : esize V.sampler.prog ≤ lam := (le_max_left _ _).trans hVs'
  have hL : esize V.len.prog ≤ lam := ((le_max_left _ _).trans (le_max_right _ _)).trans hVs'
  have hP : esize V.lp.prog ≤ lam := ((le_max_right _ _).trans (le_max_right _ _)).trans hVs'
  have hlam : 1 ≤ lam := le_trans (by have := two_le_esize V.len.prog; omega) hL
  have hlamC : lam ≤ C * lam := Nat.le_mul_of_pos_left lam (by omega)
  have hdec : esize dec ≤ Kc + 5 * lam := by omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨hdim, hSt, hLt, hPt, -⟩ := hVn n hn
    have hpos : 0 < n := by omega
    have hpow : n ^ lam ≤ n ^ (C * lam) := Nat.pow_le_pow_right hpos hlamC
    refine ⟨hdim.trans hpow, hSt.mono hpow hlamC, fun d => ?_⟩
    have hW1 : n ^ lam ≤ n ^ (A * lam) := by
      simpa using pow_le_pow_mul (lam := lam) (a := 1) (b := A) hn (by omega)
    have hW10 : 10 ^ lam ≤ n ^ (A * lam) :=
      (ten_pow_le hn lam).trans (pow_le_pow_mul hn (by omega))
    have hWn : esize n ≤ n ^ (A * lam) :=
      (esize_nat_le_pow_four hn).trans (Nat.pow_le_pow_right hpos (by nlinarith))
    have hWS : esize V.sampler.prog ≤ n ^ (A * lam) :=
      (hS.trans (le_pow_self_of_two_le hn lam)).trans hW1
    have hWd : esize dec ≤ n ^ (A * lam) :=
      (hdec.trans (by nlinarith : Kc + 5 * lam ≤ (Kc + 5) * lam)).trans
        ((le_pow_self_of_two_le hn _).trans (pow_le_pow_mul hn (by omega)))
    obtain ⟨r, t, ht, hr⟩ := wrapCore_cost_at U V.sampler dec hSt
      (fun s => c0 * (n ^ lam + 10 ^ lam + esize n + 1) ^ m0 * (s + 1) ^ (e0 * (lam + 1)))
      (fun d' => hcanon V.len.closed V.lp.closed hLt hPt d') d
    have hdom := hW V.sampler dec (n ^ (A * lam)) (d.size + 1) lam n (n ^ lam) _ d.size
      (by omega) hW10 le_rfl hWS hWd hWn (hdim.trans hW1) hW1
      (hTd (n ^ (A * lam)) lam _ _ _ d.size hW1 hW10 hWn)
    exact ⟨r, t, ht.trans (hdom.le.trans (dom_le_pow hn hlam (by omega) (by omega) (by omega))),
      hr⟩
  · have h4 : Kw + 6 * lam + Kc ≤ C * lam :=
      calc Kw + 6 * lam + Kc ≤ (Kw + Kc + 6) * lam := by nlinarith
        _ ≤ C * lam := Nat.mul_le_mul_right _ (by omega)
    refine max_le (hS.trans hlamC) ?_
    change esize (wrapCore U.univ V.sampler.prog (encode dec)) ≤ C * lam
    omega

end TailoredVerifier

end MIPRE.Tailored

end
