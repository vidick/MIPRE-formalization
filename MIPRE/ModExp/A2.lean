module
public import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.NormNum
public import MIPRE.Tactics
@[expose] public section
theorem a2 : (2:ℕ) + 2 = 4 := by norm_num
end
