/-
Vendored from `lukasliehr/MIPRE` (https://github.com/lukasliehr/MIPRE), a Lean 4 formalization of
Tsirelson's problem, by scripts/vendor-liehr.py; do not edit by hand. Upstream path:
Tsirelson/Core/Entanglement.lean, from a snapshot of the `main` branch supplied on 2026-09-25
(archive, no commit recorded). The import prefix `Tsirelson.` is rewritten to
`MIPRE.Background.LiehrTsirelson.Upstream.`; the Lean namespace `Tsirelson` is unchanged, and
nothing outside `MIPRE/Background/LiehrTsirelson/` may name it. Upstream carries no license file;
see README.md.
-/
import MIPRE.Background.LiehrTsirelson.Upstream.Core.Value

/-!
# Schmidt rank and the entanglement requirement `Ent`

Source: `Blueprint/Nodes/B23-Games/Parts/01-GamesAndStrategies.tex`, the Schmidt
rank paragraph preceding `def:ent`, and `def:ent` itself.

`Ent G ν` is the minimum Schmidt-rank bound of an **actual** tensor strategy
attaining value at least `ν`, and `∞` when no such strategy exists.  The TeX's
own boundary conventions (`Ent = 1` for `ν ≤ 0`, `Ent = ∞` for `ν > 1`) are
proved, not assumed.

The Schmidt rank of a bipartite state `ψ = ∑_{ij} ψ(i,j) |i⟩|j⟩` is the rank of
its coefficient matrix; it is therefore *derived from the actual state* and is
never a free field.
-/

namespace Tsirelson

noncomputable section

universe u v w z

variable {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-! ## Rank positivity for nonzero matrices -/

theorem rank_pos_of_ne_zero {m n : ℕ} {M : Matrix (Fin m) (Fin n) ℂ} (h : M ≠ 0) :
    0 < M.rank := by
  rw [Matrix.rank, Nat.pos_iff_ne_zero]
  intro hz
  rw [Submodule.finrank_eq_zero] at hz
  apply h
  have hlin : ∀ v, M.mulVecLin v = 0 := by
    intro v
    have hv : M.mulVecLin v ∈ LinearMap.range M.mulVecLin := LinearMap.mem_range_self _ v
    rw [hz, Submodule.mem_bot] at hv
    exact hv
  ext i j
  have h1 := congrFun (hlin (Pi.single j (1 : ℂ))) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using h1

/-! ## Schmidt rank -/

namespace TensorStrategy

/-- The coefficient matrix of the bipartite state, `ψ(i,j)`. -/
def coeffMatrix (S : TensorStrategy X Y A B) : Matrix (Fin S.dA) (Fin S.dB) ℂ :=
  Matrix.of fun i j => WithLp.ofLp S.ψ (i, j)

@[simp] theorem coeffMatrix_apply (S : TensorStrategy X Y A B) (i : Fin S.dA) (j : Fin S.dB) :
    S.coeffMatrix i j = WithLp.ofLp S.ψ (i, j) := rfl

theorem coeffMatrix_ne_zero (S : TensorStrategy X Y A B) : S.coeffMatrix ≠ 0 := by
  intro hz
  have hcoord : WithLp.ofLp S.ψ = (0 : Fin S.dA × Fin S.dB → ℂ) := by
    funext p
    obtain ⟨i, j⟩ := p
    have : S.coeffMatrix i j = 0 := by rw [hz]; rfl
    simpa using this
  have hψ : S.ψ = 0 := by
    have := congrArg (WithLp.toLp 2) hcoord
    simpa using this
  have h1 : ‖S.ψ‖ = 1 := S.unit_ψ
  rw [hψ] at h1
  simp at h1

/-- The **Schmidt rank** of the strategy's state: the rank of its coefficient
matrix.  Derived from the actual state; not a field. -/
def schmidtRank (S : TensorStrategy X Y A B) : ℕ := S.coeffMatrix.rank

theorem schmidtRank_eq_rank (S : TensorStrategy X Y A B) :
    S.schmidtRank = S.coeffMatrix.rank := rfl

/-- A unit bipartite state has Schmidt rank at least one. -/
theorem schmidtRank_pos (S : TensorStrategy X Y A B) : 0 < S.schmidtRank :=
  rank_pos_of_ne_zero S.coeffMatrix_ne_zero

theorem one_le_schmidtRank (S : TensorStrategy X Y A B) : 1 ≤ S.schmidtRank :=
  S.schmidtRank_pos

theorem schmidtRank_le_dB (S : TensorStrategy X Y A B) : S.schmidtRank ≤ S.dB := by
  rw [schmidtRank_eq_rank]
  simpa using Matrix.rank_le_card_width S.coeffMatrix

theorem schmidtRank_le_dA (S : TensorStrategy X Y A B) : S.schmidtRank ≤ S.dA := by
  rw [schmidtRank_eq_rank]
  simpa using Matrix.rank_le_card_height S.coeffMatrix

end TensorStrategy

/-! ## The entanglement requirement -/

/-- `Ent G ν`: the least Schmidt rank of an actual finite-dimensional tensor
strategy achieving value at least `ν`, and `⊤` when none exists.

This is `def:ent`. -/
def Ent (G : NonlocalGame X Y A B) (ν : ℝ) : ℕ∞ :=
  ⨅ S : {S : TensorStrategy X Y A B // ν ≤ S.value G}, (S.1.schmidtRank : ℕ∞)

/-- The family whose infimum defines `Ent`, named so that `iInf_le`/`le_iInf`
applications elaborate without an unresolved metavariable. -/
def entFamily (G : NonlocalGame X Y A B) (ν : ℝ) :
    {S : TensorStrategy X Y A B // ν ≤ S.value G} → ℕ∞ :=
  fun S => (S.1.schmidtRank : ℕ∞)

theorem Ent_eq_iInf_entFamily (G : NonlocalGame X Y A B) (ν : ℝ) :
    Ent G ν = ⨅ S, entFamily G ν S := rfl

/-- Any qualifying strategy bounds `Ent` above. -/
theorem Ent_le_schmidtRank {G : NonlocalGame X Y A B} {ν : ℝ}
    (S : TensorStrategy X Y A B) (hS : ν ≤ S.value G) :
    Ent G ν ≤ (S.schmidtRank : ℕ∞) :=
  iInf_le (entFamily G ν) ⟨S, hS⟩

/-- `Ent` is `⊤` exactly when the threshold is unattainable. -/
theorem Ent_eq_top_iff (G : NonlocalGame X Y A B) (ν : ℝ) :
    Ent G ν = ⊤ ↔ ¬ ∃ S : TensorStrategy X Y A B, ν ≤ S.value G := by
  constructor
  · rintro h ⟨S, hS⟩
    have hle : Ent G ν ≤ (S.schmidtRank : ℕ∞) := Ent_le_schmidtRank S hS
    rw [h] at hle
    exact absurd (ENat.coe_lt_top S.schmidtRank) (not_lt.2 hle)
  · intro h
    have : IsEmpty {S : TensorStrategy X Y A B // ν ≤ S.value G} :=
      ⟨fun S => h ⟨S.1, S.2⟩⟩
    exact iInf_of_empty _

/-- The threshold-existence characterization. -/
theorem Ent_le_iff_exists_strategy (G : NonlocalGame X Y A B) (ν : ℝ) (d : ℕ) :
    Ent G ν ≤ (d : ℕ∞) ↔
      ∃ S : TensorStrategy X Y A B, ν ≤ S.value G ∧ S.schmidtRank ≤ d := by
  constructor
  · intro h
    by_contra hcon
    have hlt : ∀ S : {S : TensorStrategy X Y A B // ν ≤ S.value G},
        (d : ℕ∞) < entFamily G ν S := by
      intro S
      have hnle : ¬ (S.1.schmidtRank ≤ d) := fun hle => hcon ⟨S.1, S.2, hle⟩
      show (d : ℕ∞) < (S.1.schmidtRank : ℕ∞)
      exact_mod_cast not_le.mp hnle
    have hge : (d : ℕ∞) + 1 ≤ Ent G ν :=
      le_iInf fun S => Order.add_one_le_of_lt (hlt S)
    have hfinal : (d : ℕ∞) + 1 ≤ (d : ℕ∞) := le_trans hge h
    have hcast : ((d + 1 : ℕ) : ℕ∞) ≤ ((d : ℕ) : ℕ∞) := by exact_mod_cast hfinal
    have hd : d + 1 ≤ d := by exact_mod_cast hcast
    omega
  · rintro ⟨S, hS, hrank⟩
    calc Ent G ν ≤ (S.schmidtRank : ℕ∞) := Ent_le_schmidtRank S hS
      _ ≤ (d : ℕ∞) := by exact_mod_cast hrank

/-- `Ent` is monotone in the threshold. -/
theorem Ent_mono_threshold (G : NonlocalGame X Y A B) {ν₁ ν₂ : ℝ} (h : ν₁ ≤ ν₂) :
    Ent G ν₁ ≤ Ent G ν₂ := by
  refine le_iInf fun S => ?_
  exact Ent_le_schmidtRank S.1 (le_trans h S.2)

/-- Below the trivial threshold, `Ent` is `1`: the one-dimensional deterministic
strategy attains it, and every state has Schmidt rank at least one. -/
theorem Ent_eq_one_of_nonpos (G : NonlocalGame X Y A B) {ν : ℝ} (hν : ν ≤ 0) :
    Ent G ν = 1 := by
  refine le_antisymm ?_ ?_
  · have hval : ν ≤ (trivialTensorStrategy (X := X) (Y := Y)
        G.nonemptyA.some G.nonemptyB.some).value G :=
      le_trans hν (tensorStrategy_value_mem_Icc _ G).1
    have hrank : (trivialTensorStrategy (X := X) (Y := Y)
        G.nonemptyA.some G.nonemptyB.some).schmidtRank ≤ 1 :=
      (trivialTensorStrategy (X := X) (Y := Y)
        G.nonemptyA.some G.nonemptyB.some).schmidtRank_le_dB
    calc Ent G ν ≤ _ := Ent_le_schmidtRank _ hval
      _ ≤ (1 : ℕ∞) := by exact_mod_cast hrank
  · refine le_iInf fun S => ?_
    have : (1 : ℕ) ≤ S.1.schmidtRank := S.1.one_le_schmidtRank
    exact_mod_cast this

/-- Above value one, `Ent` is `⊤`: no strategy can exceed payoff one. -/
theorem Ent_eq_top_of_one_lt (G : NonlocalGame X Y A B) {ν : ℝ} (hν : 1 < ν) :
    Ent G ν = ⊤ := by
  rw [Ent_eq_top_iff]
  rintro ⟨S, hS⟩
  exact absurd (le_trans hS (tensorStrategy_value_mem_Icc S G).2) (not_le.2 hν)

end

end Tsirelson
