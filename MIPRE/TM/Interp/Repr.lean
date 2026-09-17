/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import MIPRE.TM.Interp.Tape
import MIPRE.Foundations.Cost.MachineBound

/-!
# The tape representation of configurations

Values as their preorder bits (`S`), the control (`ctrlRepr`), the environment
(`envRepr`, innermost value at the right end, `#`-separated), the frames (`frameRepr`) and
the stack (`kontRepr`), as lists of symbols; and their lengths in terms of the sizes.
-/

namespace MIPRE.TM.Interp

open MIPRE.Cost MIPRE.Cost.Machine

/-- A value: its preorder bits. -/
def S (v : Data) : List Sym := bits v.toBits

@[simp] theorem S_nil : S .nil = [.zero] := rfl

theorem S_cons (a b : Data) : S (.cons a b) = .one :: (S a ++ S b) := by
  simp [S, Data.toBits]

@[simp] theorem length_S (v : Data) : (S v).length = v.size := by simp [S]

theorem S_ne_nil (v : Data) : S v ≠ [] := by
  cases v <;> simp [S_cons]

/-- The symbols of a value are bits. -/
theorem mem_S (v : Data) : ∀ s ∈ S v, s = .zero ∨ s = .one := by
  intro s hs
  simp only [S, bits, List.mem_map] at hs
  obtain ⟨b, -, rfl⟩ := hs
  cases b <;> simp

/-- The control: `0 · S(p.toData)` for `ev p`, `1 · S(v)` for `ret v`. -/
def ctrlRepr : Ctrl → List Sym
  | .ev p => .zero :: S p.toData
  | .ret v => .one :: S v

/-- The environment `[v₁, …, vₙ]` (`v₁` innermost): `S(vₙ) # … # S(v₁) #`. -/
def envRepr : Env → List Sym
  | [] => []
  | v :: env => envRepr env ++ S v ++ [.sep]

@[simp] theorem envRepr_nil : envRepr [] = [] := rfl

@[simp] theorem envRepr_cons (v : Data) (env : Env) :
    envRepr (v :: env) = envRepr env ++ S v ++ [.sep] := rfl

theorem length_envRepr (env : Env) :
    (envRepr env).length = (env.map Data.size).sum + env.length := by
  induction env with
  | nil => simp
  | cons v env ih => simp [ih]; omega

/-- No `$` and no `¶` in an environment. -/
theorem mem_envRepr (env : Env) : ∀ s ∈ envRepr env, s ≠ .fr ∧ s ≠ .en := by
  induction env with
  | nil => simp
  | cons v env ih =>
    intro s hs
    simp only [envRepr_cons, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | hs) | rfl
    · exact ih s hs
    · rcases mem_S v s hs with rfl | rfl <;> simp
    · simp

/-- The two tag bits of a frame. -/
def frameTag : Frame → List Sym
  | .cons1 _ _ => [.zero, .zero]
  | .cons2 _ => [.zero, .one]
  | .let1 _ _ => [.one, .zero]
  | .loop1 _ _ => [.one, .one]

/-- A frame: its tag, its payload, `$`; a closure carries its environment after `¶`. -/
def frameRepr : Frame → List Sym
  | .cons1 t env => [.zero, .zero] ++ S t.toData ++ [.en] ++ envRepr env ++ [.fr]
  | .cons2 a => [.zero, .one] ++ S a ++ [.fr]
  | .let1 b env => [.one, .zero] ++ S b.toData ++ [.en] ++ envRepr env ++ [.fr]
  | .loop1 b env => [.one, .one] ++ S b.toData ++ [.en] ++ envRepr env ++ [.fr]

/-- The body of a frame: the frame without its final `$`. -/
def frameBody : Frame → List Sym
  | .cons1 t env => [.zero, .zero] ++ S t.toData ++ [.en] ++ envRepr env
  | .cons2 a => [.zero, .one] ++ S a
  | .let1 b env => [.one, .zero] ++ S b.toData ++ [.en] ++ envRepr env
  | .loop1 b env => [.one, .one] ++ S b.toData ++ [.en] ++ envRepr env

theorem frameRepr_eq (f : Frame) : frameRepr f = frameBody f ++ [.fr] := by
  cases f <;> simp [frameRepr, frameBody]

/-- No `$` in the body of a frame. -/
theorem mem_frameBody (f : Frame) : ∀ s ∈ frameBody f, s ≠ .fr := by
  intro s hs
  have hS : ∀ v : Data, s ∈ S v → s ≠ .fr := fun v h =>
    (mem_S v s h).elim (fun e => e ▸ by simp) (fun e => e ▸ by simp)
  cases f with
  | cons1 t env =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (((rfl | rfl) | h) | rfl) | h
    · simp
    · simp
    · exact hS _ h
    · simp
    · exact (mem_envRepr env s h).1
  | cons2 a =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (rfl | rfl) | h
    · simp
    · simp
    · exact hS _ h
  | let1 b env =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (((rfl | rfl) | h) | rfl) | h
    · simp
    · simp
    · exact hS _ h
    · simp
    · exact (mem_envRepr env s h).1
  | loop1 b env =>
    simp only [frameBody, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hs
    rcases hs with (((rfl | rfl) | h) | rfl) | h
    · simp
    · simp
    · exact hS _ h
    · simp
    · exact (mem_envRepr env s h).1

/-- The stack `[f₁, …, fₘ]` (`f₁` the top): `frameRepr fₘ ++ … ++ frameRepr f₁`. -/
def kontRepr : List Frame → List Sym
  | [] => []
  | f :: k => kontRepr k ++ frameRepr f

@[simp] theorem kontRepr_nil : kontRepr [] = [] := rfl

@[simp] theorem kontRepr_cons (f : Frame) (k : List Frame) :
    kontRepr (f :: k) = kontRepr k ++ frameRepr f := rfl

theorem length_frameRepr_le {V L P : ℕ} {f : Frame} (h : FrameBound V L P f) :
    (frameRepr f).length ≤ V + P + L * V + L + 4 := by
  cases f with
  | cons2 a => simp only [FrameBound] at h; simp [frameRepr]; omega
  | cons1 t env =>
    obtain ⟨h1, h2, h3⟩ := h
    rw [Prog.esize_eq_size_toData] at h1
    have := length_envRepr env
    have hsum : (env.map Data.size).sum ≤ L * V := by
      calc (env.map Data.size).sum ≤ (env.map fun _ => V).sum :=
            List.sum_le_sum (fun v hv => h3 v hv)
        _ = env.length * V := by simp [List.map_const', List.sum_replicate]
        _ ≤ L * V := Nat.mul_le_mul_right V h2
    simp only [frameRepr, List.length_append, List.length_cons, List.length_nil, length_S,
      List.length_singleton]
    omega
  | let1 b env =>
    obtain ⟨h1, h2, h3⟩ := h
    rw [Prog.esize_eq_size_toData] at h1
    have := length_envRepr env
    have hsum : (env.map Data.size).sum ≤ L * V := by
      calc (env.map Data.size).sum ≤ (env.map fun _ => V).sum :=
            List.sum_le_sum (fun v hv => h3 v hv)
        _ = env.length * V := by simp [List.map_const', List.sum_replicate]
        _ ≤ L * V := Nat.mul_le_mul_right V h2
    simp only [frameRepr, List.length_append, List.length_cons, List.length_nil, length_S,
      List.length_singleton]
    omega
  | loop1 b env =>
    obtain ⟨h1, h2, h3⟩ := h
    rw [Prog.esize_eq_size_toData] at h1
    have := length_envRepr env
    have hsum : (env.map Data.size).sum ≤ L * V := by
      calc (env.map Data.size).sum ≤ (env.map fun _ => V).sum :=
            List.sum_le_sum (fun v hv => h3 v hv)
        _ = env.length * V := by simp [List.map_const', List.sum_replicate]
        _ ≤ L * V := Nat.mul_le_mul_right V h2
    simp only [frameRepr, List.length_append, List.length_cons, List.length_nil, length_S,
      List.length_singleton]
    omega

end MIPRE.TM.Interp
