/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Indexing the vertices of a cycle

For a cycle `p : K.Walk v₀ v₀` of length `k`, the vertices `p.getVert i` (`i < k`) are pairwise
distinct, consecutive ones (indices mod `k`) are adjacent, and every edge of the cycle joins two
consecutive ones. `cycIdx p v` is the index of a vertex `v` of the cycle.
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph

variable {V : Type*} {K : SimpleGraph V} {v₀ : V}

namespace CycleWalk

variable {p : K.Walk v₀ v₀} (hp : p.IsCycle)
include hp

theorem three_le : 3 ≤ p.length := hp.three_le_length

theorem getVert_inj {i j : ℕ} (hi : i < p.length) (hj : j < p.length)
    (h : p.getVert i = p.getVert j) : i = j :=
  hp.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) h

theorem getVert_mod (i : ℕ) (hi : i ≤ p.length) : p.getVert (i % p.length) = p.getVert i := by
  rcases Nat.lt_or_ge i p.length with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have : i = p.length := by omega
    subst this
    rw [Nat.mod_self, Walk.getVert_zero, Walk.getVert_length]

theorem adj_succ {i : ℕ} (hi : i < p.length) :
    K.Adj (p.getVert i) (p.getVert ((i + 1) % p.length)) := by
  rw [getVert_mod hp (i + 1) (by omega)]
  exact p.adj_getVert_succ hi

theorem exists_getVert {v : V} (hv : v ∈ p.support) : ∃ i < p.length, p.getVert i = v := by
  obtain ⟨n, rfl, hn⟩ := Walk.mem_support_iff_exists_getVert.1 hv
  have := three_le hp
  rcases Nat.lt_or_ge n p.length with h | h
  · exact ⟨n, h, rfl⟩
  · refine ⟨0, by omega, ?_⟩
    rw [show n = p.length by omega, Walk.getVert_zero, Walk.getVert_length]

theorem getVert_mem_support (i : ℕ) : p.getVert i ∈ p.support := p.getVert_mem_support i

/-- An edge of the cycle joins two consecutive vertices. -/
theorem exists_of_toSubgraph_adj {u v : V} (h : p.toSubgraph.Adj u v) :
    ∃ i < p.length, (u = p.getVert i ∧ v = p.getVert ((i + 1) % p.length)) ∨
      (v = p.getVert i ∧ u = p.getVert ((i + 1) % p.length)) := by
  obtain ⟨i, he, hi⟩ := (Walk.toSubgraph_adj_iff p).1 h
  refine ⟨i, hi, ?_⟩
  rw [getVert_mod hp (i + 1) (by omega)]
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

open Classical in
/-- The index of a vertex of the cycle. -/
noncomputable def idx (p : K.Walk v₀ v₀) (v : V) : ℕ :=
  if h : ∃ i, i < p.length ∧ p.getVert i = v then Nat.find h else 0

omit hp in
theorem idx_spec {v : V} (h : ∃ i, i < p.length ∧ p.getVert i = v) :
    idx p v < p.length ∧ p.getVert (idx p v) = v := by
  classical
  unfold idx
  rw [dif_pos h]
  exact Nat.find_spec h

theorem idx_lt {v : V} (hv : v ∈ p.support) : idx p v < p.length :=
  (idx_spec (exists_getVert hp hv)).1

theorem getVert_idx {v : V} (hv : v ∈ p.support) : p.getVert (idx p v) = v :=
  (idx_spec (exists_getVert hp hv)).2

theorem idx_getVert {i : ℕ} (hi : i < p.length) : idx p (p.getVert i) = i :=
  getVert_inj hp (idx_lt hp (getVert_mem_support hp i)) hi
    (getVert_idx hp (getVert_mem_support hp i))

theorem idx_inj {u v : V} (hu : u ∈ p.support) (hv : v ∈ p.support) (h : idx p u = idx p v) :
    u = v := by
  rw [← getVert_idx hp hu, ← getVert_idx hp hv, h]

/-- An edge of the cycle joins consecutive indices. -/
theorem idx_of_toSubgraph_adj {u v : V} (h : p.toSubgraph.Adj u v) :
    idx p v = (idx p u + 1) % p.length ∨ idx p u = (idx p v + 1) % p.length := by
  obtain ⟨i, hi, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := exists_of_toSubgraph_adj hp h
  · left
    rw [idx_getVert hp hi, idx_getVert hp (Nat.mod_lt _ (by omega))]
  · right
    rw [idx_getVert hp hi, idx_getVert hp (Nat.mod_lt _ (by omega))]

end CycleWalk

end CoreDeg2Lib
