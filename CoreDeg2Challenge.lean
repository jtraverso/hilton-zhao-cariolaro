/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Graphs whose core has maximum degree at most two

The core of a finite simple graph `G` is the subgraph induced by its vertices of maximum degree
`Δ = G.maxDegree`; it has maximum degree at most two when every vertex of degree `Δ` has at most
two neighbours of degree `Δ`. Class one means `G.lineGraph.Colorable G.maxDegree`.

* Hilton–Zhao (1992): a connected class-two graph whose core has maximum degree at most two is
  critical, every vertex has at least two neighbours of degree `Δ` (so the core is `2`-regular),
  and the minimum degree is `Δ − 1` (when `Δ ≥ 3`). Consequences: class one when some vertex of
  degree `Δ` has at most one neighbour of degree `Δ`, or when some vertex has degree `≤ Δ − 2`.
* `Δ = 3` (Cariolaro–Cariolaro 2003, Lemma 3): a connected class-two graph is a petal graph, and
  `3 |E| = 4 |V|`.
* `Δ = 3` (Cariolaro–Cariolaro 2003, Lemma 7, for one core cycle): if some component of the core
  carries no internal petal (no vertex of degree `< 3` adjacent to two of its vertices), then `G`
  is of class one.
* The Petersen graph minus a vertex, `P*`, satisfies the hypotheses, is connected, of class two,
  and not overfull.
-/

@[expose] public section

namespace CoreDeg2

open SimpleGraph Finset

/-! ### Hilton–Zhao -/

/-- **Hilton–Zhao: criticality.** -/
theorem hiltonZhao_critical {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) :
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).lineGraph.Colorable G.maxDegree := by
  sorry

/-- **Hilton–Zhao: every vertex has two neighbours of maximum degree.** -/
theorem hiltonZhao_two_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (v : V) :
    2 ≤ #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) := by
  sorry

/-- **Hilton–Zhao: the core is `2`-regular.** -/
theorem hiltonZhao_core_regular {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (v : V) (hv : G.degree v = G.maxDegree) :
    #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) = 2 := by
  sorry

/-- **Hilton–Zhao: minimum degree at least `Δ − 1`.** -/
theorem hiltonZhao_min_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (v : V) :
    G.maxDegree ≤ G.degree v + 1 := by
  sorry

/-- **Hilton–Zhao: minimum degree exactly `Δ − 1` when `Δ ≥ 3`.** -/
theorem hiltonZhao_min_degree_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (hΔ : 3 ≤ G.maxDegree) :
    ∃ v, G.degree v + 1 = G.maxDegree := by
  sorry

/-- **Class one** when some vertex of maximum degree has at most one neighbour of maximum
degree. -/
theorem colorable_of_core_deg_le_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (v : V) (hv : G.degree v = G.maxDegree)
    (hv1 : #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 1) :
    G.lineGraph.Colorable G.maxDegree := by
  sorry

/-- **Class one** when some vertex has degree at most `Δ − 2`. -/
theorem colorable_of_low_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (v : V) (hv : G.degree v + 2 ≤ G.maxDegree) :
    G.lineGraph.Colorable G.maxDegree := by
  sorry

/-! ### Maximum degree three -/

/-- **Cariolaro–Cariolaro, Lemma 3: petal structure.** -/
theorem petal_structure {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable 3) :
    (∀ v, G.degree v = 2 ∨ G.degree v = 3) ∧
    (∀ v, G.degree v = 3 → #((G.neighborFinset v).filter fun u => G.degree u = 3) = 2) ∧
    (∀ v w, G.degree v = 2 → G.Adj v w → G.degree w = 3) := by
  sorry

/-- **Counting:** a connected class-two graph with `Δ = 3` and core of maximum degree at most
two has `3 |E| = 4 |V|`. -/
theorem three_mul_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable 3) :
    3 * #G.edgeFinset = 4 * Fintype.card V := by
  sorry

/-- **Class one** (`Δ = 3`) when `3 |E| ≠ 4 |V|`. -/
theorem colorable_of_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcard : 3 * #G.edgeFinset ≠ 4 * Fintype.card V) :
    G.lineGraph.Colorable 3 := by
  sorry

/-- **Cariolaro–Cariolaro, Lemma 7 (one core cycle without internal petals).** If the core
component of a vertex `r` of degree three carries no internal petal, then `G` is of class one.
The core is the graph on `V` whose edges are the edges of `G` between vertices of degree `Δ`. -/
theorem colorable_of_noInternalPetal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (r : V) (hr : G.degree r = 3)
    (hR : ∀ w x y, G.Adj w x → G.Adj w y → x ≠ y → G.degree w ≠ 3 →
      (SimpleGraph.fromRel fun u v => G.Adj u v ∧ G.degree u = G.maxDegree ∧
        G.degree v = G.maxDegree).Reachable r x →
      ¬ (SimpleGraph.fromRel fun u v => G.Adj u v ∧ G.degree u = G.maxDegree ∧
        G.degree v = G.maxDegree).Reachable r y) :
    G.lineGraph.Colorable 3 := by
  sorry

/-! ### The Petersen graph minus a vertex -/

/-- The edges of `P*`: the hexagon `0-1-2-3-4-5` and the vertices `6, 7, 8` joined to the
antipodal pairs `{0, 3}, {1, 4}, {2, 5}`. -/
def pStarEdges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (6, 0), (6, 3), (7, 1), (7, 4), (8, 2), (8, 5)]

/-- `P*`, the Petersen graph minus a vertex. -/
def pStar : SimpleGraph (Fin 9) := SimpleGraph.fromRel fun i j => (i, j) ∈ pStarEdges

instance pStarDecAdj : DecidableRel pStar.Adj := fun a b =>
  decidable_of_iff' _ (SimpleGraph.fromRel_adj _ a b)

/-- The edges of the Petersen graph: outer pentagon, spokes, inner pentagram. -/
def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

/-- The Petersen graph. -/
def petersen : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun i j => (i, j) ∈ petersenEdges

/-- `P*` is the Petersen graph with the vertex `0` deleted. -/
theorem pStar_iso : Nonempty (pStar ≃g petersen.induce {v | v ≠ 0}) := by
  sorry

theorem pStar_maxDegree : pStar.maxDegree = 3 := by
  sorry

/-- The core of `P*` (the hexagon) has maximum degree two. -/
theorem pStar_core : ∀ v, pStar.degree v = pStar.maxDegree →
    #((pStar.neighborFinset v).filter fun u => pStar.degree u = pStar.maxDegree) ≤ 2 := by
  sorry

theorem pStar_connected : pStar.Connected := by
  sorry

/-- **`P*` is of class two.** -/
theorem pStar_not_colorable : ¬ pStar.lineGraph.Colorable pStar.maxDegree := by
  sorry

/-- `P*` is not overfull. -/
theorem pStar_not_overfull :
    ¬ pStar.maxDegree * (Fintype.card (Fin 9) / 2) < #pStar.edgeFinset := by
  sorry

/-! ### The theorem of Cariolaro and Cariolaro -/

/-- **Cariolaro–Cariolaro (2003).** A connected graph with maximum degree three whose core has
maximum degree at most two is of class two if and only if it is isomorphic to `P*`. -/
theorem cariolaro_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2) :
    ¬ G.lineGraph.Colorable 3 ↔ Nonempty (G ≃g pStar) := by
  sorry

/-- **Cariolaro–Cariolaro (2003), Theorem 1.** A connected graph with maximum degree three whose
core has maximum degree at most two, other than `P*`, is of class one. -/
theorem cariolaro {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hP : ¬ Nonempty (G ≃g pStar)) : G.lineGraph.Colorable 3 := by
  sorry

end CoreDeg2
