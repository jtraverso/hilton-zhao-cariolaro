/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Degree
public import LeanPool.Vizing.Main

/-!
# Graphs whose core has maximum degree at most two (Hilton–Zhao)

The *core* of `G` is the subgraph induced by the vertices of maximum degree `Δ = Δ(G)`. Its
maximum degree is at most two when every vertex of degree `Δ` has at most two neighbours of
degree `Δ` (`CoreLeTwo G`).

**Hilton–Zhao (1992).** If `G` is connected, of class two, and its core has maximum degree at most
two, then
1. `G` is critical: `G − e` is `Δ`-edge-colourable for every edge `e` (`isDeltaCritical`);
2. every vertex has at least two neighbours of degree `Δ`, so the core is `2`-regular
   (`two_le_card_coreNbrs`, `card_coreNbrs_eq_two`);
3. every vertex has degree at least `Δ − 1` (`le_degree_add_one`), and if `Δ ≥ 3` some vertex
   has degree `Δ − 1` (`exists_degree_add_one_eq`).

Proof (as in Cranston–Rabern, *The Hilton–Zhao conjecture is true for graphs with maximum
degree 4*, Lemma 1): take an edge-minimal subgraph `H ≤ G` that is not `Δ`-edge-colourable; by
Vizing `Δ(H) = Δ`, and Vizing's adjacency lemma in `H` (registered `Overfull.val`) shows that the
non-isolated vertices of `H` have degree `≥ Δ − 1` in `H` and that no edge of `G` leaves them, so
`H = G` by connectivity. The remaining items are Vizing's adjacency lemma in the critical graph
`G` (`Overfull.val_crit`).
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph Finset Overfull

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The neighbours of `v` of maximum degree. -/
def coreNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (G.neighborFinset v).filter fun u => G.degree u = G.maxDegree

/-- The core of `G` (vertices of maximum degree) has maximum degree at most two. -/
def CoreLeTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = G.maxDegree → #(coreNbrs G v) ≤ 2

omit [DecidableEq V] in
theorem mem_coreNbrs {G : SimpleGraph V} [DecidableRel G.Adj] {v u : V} :
    u ∈ coreNbrs G v ↔ G.Adj v u ∧ G.degree u = G.maxDegree := by
  simp [coreNbrs]

/-- The set counted by Vizing's adjacency lemma is contained in `coreNbrs G x` minus `y`. -/
theorem valSet_subset (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    ((G.neighborFinset x).filter fun z => z ≠ y ∧ G.degree z = G.maxDegree) ⊆
      (coreNbrs G x).erase y := by
  intro z hz
  simp only [mem_filter, mem_neighborFinset] at hz
  exact mem_erase.2 ⟨hz.2.1, mem_coreNbrs.2 ⟨hz.1, hz.2.2⟩⟩

omit [Fintype V] [DecidableEq V] in
theorem exists_adj_of_not_colorable (G : SimpleGraph V) {k : ℕ}
    (h : ¬ G.lineGraph.Colorable k) : ∃ u v, G.Adj u v := by
  by_contra hne
  push Not at hne
  apply h
  have : IsEmpty G.edgeSet := ⟨fun ⟨e, he⟩ => by
    induction e using Sym2.ind with
    | h x y => exact hne x y he⟩
  exact Colorable.of_isEmpty k

omit [Fintype V] [DecidableEq V] in
/-- In a connected graph with an edge, every vertex has a neighbour. -/
theorem exists_adj_of_connected {G : SimpleGraph V} (hconn : G.Connected) {u w : V}
    (huw : G.Adj u w) (v : V) : ∃ x, G.Adj v x := by
  by_cases hvu : v = u
  · exact ⟨w, hvu ▸ huw⟩
  · obtain ⟨p⟩ := hconn.preconnected v u
    cases p with
    | nil => exact absurd rfl hvu
    | cons h _ => exact ⟨_, h⟩

omit [DecidableEq V] in
theorem ncard_deleteEdges_lt (H : SimpleGraph V) {x y : V} (hxy : H.Adj x y) :
    (H.deleteEdges {s(x, y)}).edgeSet.ncard < H.edgeSet.ncard := by
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  rw [edgeSet_deleteEdges]
  exact Set.sdiff_ssubset_left_iff.mpr ⟨s(x, y), hxy, rfl⟩

/-- **Hilton–Zhao, criticality.** A connected class-two graph whose core has maximum degree at
most two is `Δ`-critical. -/
theorem isDeltaCritical (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : CoreLeTwo G) (hcl : ¬ G.lineGraph.Colorable G.maxDegree) : IsDeltaCritical G := by
  classical
  set Δ := G.maxDegree with hΔ
  -- an edge-minimal subgraph that is not `Δ`-edge-colourable
  obtain ⟨H, hHmem, hHmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun H : SimpleGraph V => H ≤ G ∧ ¬ H.lineGraph.Colorable Δ)
    (fun H => H.edgeSet.ncard) ⟨G, by simp [hcl]⟩
  rw [mem_filter] at hHmem
  obtain ⟨-, hHG, hHcol⟩ := hHmem
  have hdegH : ∀ v, H.degree v ≤ G.degree v := fun v => degree_le_of_le hHG
  have hdegG : ∀ v, G.degree v ≤ Δ := fun v => G.degree_le_maxDegree v
  have hHΔ : H.maxDegree = Δ := by
    have hle : H.maxDegree ≤ Δ :=
      maxDegree_le_of_forall_degree_le _ _ fun v => (hdegH v).trans (hdegG v)
    by_contra hne
    exact hHcol ((LeanPool.Vizing.lineGraph_colorable H).mono (by omega))
  have hclass : IsClassTwo H := by
    unfold IsClassTwo; rw [hHΔ]; exact hHcol
  -- Vizing's adjacency lemma in `H`
  have hval : ∀ x y, H.Adj x y → Δ + 1 ≤ H.degree y +
      #((H.neighborFinset x).filter fun z => z ≠ y ∧ H.degree z = Δ) := by
    intro x y hxy
    have hdel : (H.deleteEdges {s(x, y)}).lineGraph.Colorable H.maxDegree := by
      by_contra hn
      have := hHmin (H.deleteEdges {s(x, y)})
        (by rw [mem_filter]; exact ⟨mem_univ _, (deleteEdges_le _).trans hHG, by rwa [hHΔ] at hn⟩)
      have := ncard_deleteEdges_lt H hxy
      omega
    obtain ⟨c, hc⟩ := exists_colMinus_of_colorable hxy hdel
    have := val hclass hc
    rw [hHΔ] at this
    exact this
  -- vertices of degree `Δ` in `H` have degree `Δ` in `G`
  have hcoreH : ∀ z, H.degree z = Δ → G.degree z = Δ := fun z hz =>
    le_antisymm (hdegG z) (hz ▸ hdegH z)
  -- the set counted by VAL in `H` sits inside `coreNbrs G x` minus `y`
  have hsub : ∀ x y, ((H.neighborFinset x).filter fun z => z ≠ y ∧ H.degree z = Δ) ⊆
      (coreNbrs G x).erase y := by
    intro x y z hz
    simp only [mem_filter, mem_neighborFinset] at hz
    exact mem_erase.2 ⟨hz.2.1, mem_coreNbrs.2 ⟨hHG hz.1, hcoreH z hz.2.2⟩⟩
  -- every vertex with an `H`-neighbour `y` has an `H`-neighbour of `H`-degree `Δ` other than `y`
  have hcoreNbr : ∀ x y, H.Adj x y → ∃ z, H.Adj x z ∧ z ≠ y ∧ H.degree z = Δ := by
    intro x y hxy
    have h1 := hval x y hxy
    have h2 : H.degree y ≤ Δ := (hdegH y).trans (hdegG y)
    obtain ⟨z, hz⟩ : ((H.neighborFinset x).filter fun z => z ≠ y ∧ H.degree z = Δ).Nonempty :=
      card_pos.mp (by omega)
    simp only [mem_filter, mem_neighborFinset] at hz
    exact ⟨z, hz.1, hz.2.1, hz.2.2⟩
  -- non-isolated vertices of `H` have `H`-degree at least `Δ − 1`
  have hlow : ∀ y w, H.Adj y w → Δ ≤ H.degree y + 1 := by
    intro y w hyw
    obtain ⟨z, hyz, -, hz⟩ := hcoreNbr y w hyw
    have h1 := hval z y hyz.symm
    have h2 := card_le_card (hsub z y)
    have h3 := card_erase_le (s := coreNbrs G z) (a := y)
    have h4 := hcore z (hcoreH z hz)
    omega
  -- no edge of `G` leaves the non-isolated vertices of `H`
  have hclosed : ∀ u w v, H.Adj u w → G.Adj u v → H.Adj u v := by
    intro u w v huw huv
    by_contra hnot
    have hl := hlow u w huw
    -- `G.degree u ≥ H.degree u + 1`
    have hGu : H.degree u + 1 ≤ G.degree u := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      have : insert v (H.neighborFinset u) ⊆ G.neighborFinset u := by
        intro z hz
        rcases mem_insert.1 hz with rfl | hz
        · exact (mem_neighborFinset _ _ _).2 huv
        · exact (mem_neighborFinset _ _ _).2 (hHG ((mem_neighborFinset _ _ _).1 hz))
      have h := card_le_card this
      rwa [card_insert_of_notMem (by rwa [mem_neighborFinset])] at h
    have hGuΔ : G.degree u = Δ := le_antisymm (hdegG u) (by omega)
    obtain ⟨x, hux, -, hx⟩ := hcoreNbr u w huw
    have h1 := hval x u hux.symm
    have h2 := card_le_card (hsub x u)
    have hu_mem : u ∈ coreNbrs G x := mem_coreNbrs.2 ⟨hHG hux.symm, hGuΔ⟩
    have h3 := card_erase_of_mem hu_mem
    have h4 := hcore x (hcoreH x hx)
    have h5 : H.degree u + 1 ≤ Δ := by omega
    omega
  -- `H` has an edge
  obtain ⟨u₀, w₀, hu₀⟩ := exists_adj_of_not_colorable H hHcol
  -- every vertex is non-isolated in `H`
  have hall : ∀ v, ∃ w, H.Adj v w := by
    intro v
    obtain ⟨p⟩ := hconn.preconnected u₀ v
    suffices ∀ a b (q : G.Walk a b), (∃ w, H.Adj a w) → ∃ w, H.Adj b w from
      this _ _ p ⟨w₀, hu₀⟩
    intro a b q
    induction q with
    | nil => exact id
    | cons h _ ih =>
      intro ⟨w, hw⟩
      exact ih ⟨_, (hclosed _ w _ hw h).symm⟩
  have hGH : G ≤ H := by
    intro u v huv
    obtain ⟨w, hw⟩ := hall u
    exact hclosed u w v hw huv
  have hHeq : H = G := le_antisymm hHG hGH
  subst hHeq
  refine ⟨hconn, hcl, fun e he => ?_⟩
  induction e using Sym2.ind with
  | h x y =>
    by_contra hn
    have := hHmin (H.deleteEdges {s(x, y)})
      (by rw [mem_filter]; exact ⟨mem_univ _, deleteEdges_le _, hn⟩)
    have h2 : (H.deleteEdges {s(x, y)}).edgeSet.ncard < H.edgeSet.ncard :=
      ncard_deleteEdges_lt H (x := x) (y := y) he
    omega

/-- In a `Δ`-critical graph, every vertex with a neighbour has at least two neighbours of degree
`Δ` (Vizing). -/
theorem two_le_card_coreNbrs_of_critical {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsDeltaCritical G) {x y : V} (hxy : G.Adj x y) : 2 ≤ #(coreNbrs G x) := by
  have h1 := val_crit hG hxy
  have h2 := card_le_card (valSet_subset G x y)
  have h3 := G.degree_le_maxDegree y
  by_cases hy : G.degree y = G.maxDegree
  · have := card_erase_of_mem (mem_coreNbrs.2 ⟨hxy, hy⟩)
    omega
  · have := card_erase_le (s := coreNbrs G x) (a := y)
    omega

/-- In a `Δ`-critical graph with core of maximum degree at most two, every neighbour of a vertex
of degree `Δ` has degree at least `Δ − 1`. -/
theorem le_degree_add_one_of_critical {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsDeltaCritical G) (hcore : CoreLeTwo G) {x y : V} (hxy : G.Adj x y)
    (hx : G.degree x = G.maxDegree) : G.maxDegree ≤ G.degree y + 1 := by
  have h1 := val_crit hG hxy
  have h2 := card_le_card (valSet_subset G x y)
  have h3 := card_erase_le (s := coreNbrs G x) (a := y)
  have h4 := hcore x hx
  omega

section HiltonZhao

variable (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (hcore : CoreLeTwo G)
  (hcl : ¬ G.lineGraph.Colorable G.maxDegree)
include hconn hcore hcl

/-- **Hilton–Zhao.** Every vertex has at least two neighbours of maximum degree. -/
theorem two_le_card_coreNbrs (v : V) : 2 ≤ #(coreNbrs G v) := by
  have hG := isDeltaCritical G hconn hcore hcl
  obtain ⟨u, w, huw⟩ := exists_adj_of_not_colorable G hcl
  obtain ⟨x, hx⟩ := exists_adj_of_connected hconn huw v
  exact two_le_card_coreNbrs_of_critical hG hx

/-- **Hilton–Zhao.** The core is `2`-regular. -/
theorem card_coreNbrs_eq_two {v : V} (hv : G.degree v = G.maxDegree) :
    #(coreNbrs G v) = 2 :=
  le_antisymm (hcore v hv) (two_le_card_coreNbrs G hconn hcore hcl v)

/-- **Hilton–Zhao.** Every vertex has degree at least `Δ − 1`. -/
theorem le_degree_add_one (v : V) : G.maxDegree ≤ G.degree v + 1 := by
  have hG := isDeltaCritical G hconn hcore hcl
  obtain ⟨x, hx⟩ : (coreNbrs G v).Nonempty :=
    card_pos.mp (by have := two_le_card_coreNbrs G hconn hcore hcl v; omega)
  rw [mem_coreNbrs] at hx
  exact le_degree_add_one_of_critical hG hcore hx.1.symm hx.2

/-- **Hilton–Zhao.** If `Δ ≥ 3`, the minimum degree is exactly `Δ − 1`. -/
theorem exists_degree_add_one_eq (hΔ : 3 ≤ G.maxDegree) : ∃ v, G.degree v + 1 = G.maxDegree := by
  by_contra hne
  push Not at hne
  have hreg : ∀ v, G.degree v = G.maxDegree := fun v => by
    have h1 := le_degree_add_one G hconn hcore hcl v
    have h2 := G.degree_le_maxDegree v
    have h3 := hne v
    omega
  obtain ⟨u, w, huw⟩ := exists_adj_of_not_colorable G hcl
  have hcn : coreNbrs G u = G.neighborFinset u := by
    unfold coreNbrs
    exact filter_true_of_mem fun z _ => hreg z
  have := hcore u (hreg u)
  rw [hcn, card_neighborFinset_eq_degree, hreg u] at this
  omega

end HiltonZhao

end CoreDeg2Lib
