/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases

/-!
# Colouring a cycle so that every vertex sees a prescribed colour

A cycle `v₀ v₁ … v_{k−1}` with edges `eᵢ = vᵢ v_{i+1}` (indices mod `k`) and a prescribed colour
`F i ∈ {0, 1, 2}` at every vertex. We look for a proper `3`-edge-colouring `c` of the cycle such
that every vertex `vᵢ` sees its colour `F i` on one of its two edges (equivalently, the colour
missing at `vᵢ` is not `F i`). This is possible whenever `F` is not constant
(`exists_cycle_colouring`; when `F` is constant and `k` is odd it is impossible).

The proof walks along the path `e₀, e₁, …, e_{k−1}` starting with `c e₀ = F 0`: after each vertex
either the prescribed colour of that vertex, or both other colours, can end the path
(`path_reach`). Starting at a vertex `v₀` with `F (k−1) ≠ F 0` closes the cycle.
-/

@[expose] public section

namespace CoreDeg2Lib

/-- The third colour. -/
def third (a b : Fin 3) : Fin 3 := -(a + b)

theorem third_ne_left : ∀ a b : Fin 3, a ≠ b → third a b ≠ a := by decide

theorem third_ne_right : ∀ a b : Fin 3, a ≠ b → third a b ≠ b := by decide

theorem eq_third : ∀ a b x : Fin 3, a ≠ b → x ≠ a → x ≠ b → x = third a b := by decide

theorem third_comm (a b : Fin 3) : third a b = third b a := by
  unfold third; rw [add_comm]

/-- If `a ≠ b`, a colour `F` lies on one of the two edges iff it is not the missing colour. -/
theorem third_ne_iff : ∀ a b f : Fin 3, a ≠ b → (third a b ≠ f ↔ f = a ∨ f = b) := by decide

theorem exists_ne_ne : ∀ a b : Fin 3, ∃ z, z ≠ a ∧ z ≠ b := by decide

/-- A colouring `c` of the edges `e₀ … e_n` of a path is valid for the prescribed colours `f` at
the inner vertices `1 … n`. -/
def PathOK (f : ℕ → Fin 3) (c : ℕ → Fin 3) (n : ℕ) : Prop :=
  ∀ t < n, c t ≠ c (t + 1) ∧ (f (t + 1) = c t ∨ f (t + 1) = c (t + 1))

/-- The colours that can end a valid path colouring with first colour `s`. -/
def Reach (f : ℕ → Fin 3) (s : Fin 3) (n : ℕ) (z : Fin 3) : Prop :=
  ∃ c : ℕ → Fin 3, c 0 = s ∧ PathOK f c n ∧ c n = z

theorem reach_extend {f : ℕ → Fin 3} {s : Fin 3} {n : ℕ} {x z : Fin 3} (hx : Reach f s n x)
    (hxz : x ≠ z) (hf : f (n + 1) = x ∨ f (n + 1) = z) : Reach f s (n + 1) z := by
  obtain ⟨c, h0, hok, hn⟩ := hx
  refine ⟨Function.update c (n + 1) z, ?_, ?_, by simp⟩
  · rw [Function.update_of_ne (show (0 : ℕ) ≠ n + 1 by omega)]; exact h0
  · intro t ht
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · rw [Function.update_of_ne (show t ≠ n + 1 by omega),
        Function.update_of_ne (show t + 1 ≠ n + 1 by omega)]
      exact hok t ht
    · subst ht
      rw [Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self, hn]
      exact ⟨hxz, hf⟩

/-- After `n ≥ 1` steps, either the prescribed colour `f n` of the last inner vertex can end the
path, or every other colour can. -/
theorem path_reach (f : ℕ → Fin 3) (s : Fin 3) :
    ∀ n, 1 ≤ n → Reach f s n (f n) ∨ ∀ z, z ≠ f n → Reach f s n z := by
  -- some colour is always reachable
  have step : ∀ n x, Reach f s n x →
      Reach f s (n + 1) (f (n + 1)) ∨ ∀ z, z ≠ f (n + 1) → Reach f s (n + 1) z := by
    intro n x hx
    by_cases hy : Reach f s n (f (n + 1))
    · exact Or.inr fun z hz => reach_extend hy hz.symm (Or.inl rfl)
    · have hxne : x ≠ f (n + 1) := fun h => hy (h ▸ hx)
      exact Or.inl (reach_extend hx hxne (Or.inr rfl))
  have nonempty : ∀ n, ∃ x, Reach f s n x := by
    intro n
    induction n with
    | zero => exact ⟨s, fun _ => s, rfl, fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      rcases step n x hx with h | h
      · exact ⟨_, h⟩
      · obtain ⟨z, hz, -⟩ := exists_ne_ne (f (n + 1)) (f (n + 1))
        exact ⟨z, h z hz⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x, hx⟩ := nonempty m
  exact step m x hx

/-- **Cycle colouring.** If `F (k − 1) ≠ F 0`, the cycle of length `k ≥ 2` has a proper
`3`-edge-colouring `c` (edge `i` joins vertices `i` and `i + 1 mod k`) such that every vertex sees
its prescribed colour. -/
theorem exists_cycle_colouring (k : ℕ) (hk : 2 ≤ k) (F : ℕ → Fin 3) (hF : F (k - 1) ≠ F 0) :
    ∃ c : ℕ → Fin 3, (∀ i, 0 < i → i < k → c (i - 1) ≠ c i) ∧ c (k - 1) ≠ c 0 ∧
      (∀ i, 0 < i → i < k → F i = c (i - 1) ∨ F i = c i) ∧ (F 0 = c (k - 1) ∨ F 0 = c 0) := by
  have hend : ∃ z, z ≠ F 0 ∧ Reach F (F 0) (k - 1) z := by
    rcases path_reach F (F 0) (k - 1) (by omega) with h | h
    · exact ⟨_, hF, h⟩
    · obtain ⟨z, hz1, hz2⟩ := exists_ne_ne (F 0) (F (k - 1))
      exact ⟨z, hz1, h z hz2⟩
  obtain ⟨z, hz, c, h0, hok, hn⟩ := hend
  refine ⟨c, fun i hi hik => ?_, by rw [hn, h0]; exact hz, fun i hi hik => ?_, Or.inr h0.symm⟩
  · have := (hok (i - 1) (by omega)).1
    rwa [show i - 1 + 1 = i by omega] at this
  · have := (hok (i - 1) (by omega)).2
    rwa [show i - 1 + 1 = i by omega] at this

end CoreDeg2Lib
