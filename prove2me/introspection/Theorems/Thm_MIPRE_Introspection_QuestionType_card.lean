/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/Types.lean (statement stub of MIPRE.Introspection.QuestionType.card);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Introspection_Types

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.QuestionType
variable {PauliType : Type*} {ℓ : ℕ}

theorem MIPRE.Introspection.QuestionType.card [Fintype PauliType] (ℓ : ℕ) :
    Fintype.card (QuestionType PauliType ℓ) = Fintype.card PauliType + 2 * ℓ + 6 := by sorry
