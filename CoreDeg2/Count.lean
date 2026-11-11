/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Class-two graphs with `Δ = 3` and core of maximum degree two: petal structure and counting

If `G` is connected, `Δ(G) = 3`, its core has maximum degree at most two and `G` is of class two,
then (Hilton–Zhao; Cariolaro–Cariolaro, Lemma 3) `G` is a *petal graph*: every vertex has degree
`2` or `3`, the vertices of degree `3` induce a `2`-regular graph, and both neighbours of every
vertex of degree `2` have degree `3` (`petal_structure`). Counting the edges between the two
degree classes gives `|V(G)| = 3t` and `|E(G)| = 4t` where `t` is the number of vertices of
degree two, hence `3 |E(G)| = 4 |V(G)|` (`three_mul_card_edgeFinset`).
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Petal

variable (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (hcore : CoreLeTwo G)
  (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (hΔ : G.maxDegree = 3)
include hconn hcore hcl hΔ

/-- **Petal structure (Cariolaro–Cariolaro, Lemma 3).** -/
theorem petal_structure :
    (∀ v, G.degree v = 2 ∨ G.degree v = 3) ∧
    (∀ v, G.degree v = 3 → #(coreNbrs G v) = 2) ∧
    (∀ v w, G.degree v = 2 → G.Adj v w → G.degree w = 3) := by
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 := fun v => by
    have h1 := le_degree_add_one G hconn hcore hcl v
    have h2 := G.degree_le_maxDegree v
    omega
  refine ⟨hdeg, fun v hv => card_coreNbrs_eq_two G hconn hcore hcl (hv.trans hΔ.symm),
    fun v w hv hvw => ?_⟩
  -- both neighbours of a vertex of degree two have degree three
  have h2 := two_le_card_coreNbrs G hconn hcore hcl v
  have hsub : coreNbrs G v ⊆ G.neighborFinset v := filter_subset _ _
  have heq : coreNbrs G v = G.neighborFinset v :=
    eq_of_subset_of_card_le hsub (by rw [card_neighborFinset_eq_degree, hv]; exact h2)
  have hw : w ∈ coreNbrs G v := by rw [heq, mem_neighborFinset]; exact hvw
  rw [mem_coreNbrs, hΔ] at hw
  exact hw.2

/-- **Counting.** `3 |E(G)| = 4 |V(G)|`. -/
theorem three_mul_card_edgeFinset : 3 * #G.edgeFinset = 4 * Fintype.card V := by
  obtain ⟨hdeg, hcn, hnb⟩ := petal_structure G hconn hcore hcl hΔ
  set S := (univ : Finset V).filter fun v => G.degree v = 3 with hS
  set T := (univ : Finset V).filter fun v => ¬ G.degree v = 3 with hT
  -- each vertex of degree three has exactly one neighbour of degree two
  have habove : ∀ a ∈ S, #(T.bipartiteAbove G.Adj a) = 1 := by
    intro a ha
    rw [hS, mem_filter] at ha
    have h1 := card_filter_add_card_filter_not (s := G.neighborFinset a) (fun u => G.degree u = 3)
    have h2 : (G.neighborFinset a).filter (fun u => G.degree u = 3) = coreNbrs G a := by
      unfold coreNbrs; rw [hΔ]
    have h3 : T.bipartiteAbove G.Adj a =
        (G.neighborFinset a).filter (fun u => ¬ G.degree u = 3) := by
      ext u; simp [bipartiteAbove, hT, mem_neighborFinset, and_comm]
    rw [h3]
    rw [h2, hcn a ha.2, card_neighborFinset_eq_degree, ha.2] at h1
    omega
  -- each vertex of degree two has exactly two neighbours of degree three
  have hbelow : ∀ b ∈ T, #(S.bipartiteBelow G.Adj b) = 2 := by
    intro b hb
    rw [hT, mem_filter] at hb
    have hb2 : G.degree b = 2 := by rcases hdeg b with h | h <;> [exact h; exact absurd h hb.2]
    have h3 : S.bipartiteBelow G.Adj b = G.neighborFinset b := by
      ext u
      simp only [bipartiteBelow, hS, mem_filter, mem_univ, true_and, mem_neighborFinset]
      exact ⟨fun h => h.2.symm, fun h => ⟨hnb b u hb2 h, h.symm⟩⟩
    rw [h3, card_neighborFinset_eq_degree, hb2]
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := S) (t := T) (r := G.Adj)
  rw [sum_congr rfl habove, sum_congr rfl hbelow] at hdc
  simp only [sum_const, smul_eq_mul, mul_one] at hdc
  -- the handshake lemma
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [← sum_filter_add_sum_filter_not univ (fun v => G.degree v = 3)] at hsum
  have hS3 : ∑ v ∈ S, G.degree v = 3 * #S := by
    rw [sum_const_nat fun v hv => (mem_filter.1 hv).2, mul_comm]
  have hT2 : ∑ v ∈ T, G.degree v = 2 * #T := by
    rw [sum_const_nat fun v hv => show G.degree v = 2 by
      rcases hdeg v with h | h
      · exact h
      · exact absurd h (mem_filter.1 hv).2, mul_comm]
  rw [← hS, ← hT, hS3, hT2] at hsum
  have hcard := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun v => G.degree v = 3)
  rw [← hS, ← hT, card_univ] at hcard
  omega

end Petal

end CoreDeg2Lib
