/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.NoInternal
public import Mathlib.Data.Fin.VecNotation

/-!
# Graphs whose core has maximum degree at most two (solution)

The statements and definitions are those of `CoreDeg2Challenge.lean`; the proofs are in the
library `CoreDeg2/` (namespace `CoreDeg2Lib`) and, for `P*`, below (finite checks by `decide`).

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
  exact (CoreDeg2Lib.isDeltaCritical G hconn hcore hcl).2.2

/-- **Hilton–Zhao: every vertex has two neighbours of maximum degree.** -/
theorem hiltonZhao_two_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (v : V) :
    2 ≤ #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) := by
  exact CoreDeg2Lib.two_le_card_coreNbrs G hconn hcore hcl v

/-- **Hilton–Zhao: the core is `2`-regular.** -/
theorem hiltonZhao_core_regular {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (v : V) (hv : G.degree v = G.maxDegree) :
    #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) = 2 := by
  exact CoreDeg2Lib.card_coreNbrs_eq_two G hconn hcore hcl hv

/-- **Hilton–Zhao: minimum degree at least `Δ − 1`.** -/
theorem hiltonZhao_min_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (v : V) :
    G.maxDegree ≤ G.degree v + 1 := by
  exact CoreDeg2Lib.le_degree_add_one G hconn hcore hcl v

/-- **Hilton–Zhao: minimum degree exactly `Δ − 1` when `Δ ≥ 3`.** -/
theorem hiltonZhao_min_degree_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable G.maxDegree) (hΔ : 3 ≤ G.maxDegree) :
    ∃ v, G.degree v + 1 = G.maxDegree := by
  exact CoreDeg2Lib.exists_degree_add_one_eq G hconn hcore hcl hΔ

/-- **Class one** when some vertex of maximum degree has at most one neighbour of maximum
degree. -/
theorem colorable_of_core_deg_le_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (v : V) (hv : G.degree v = G.maxDegree)
    (hv1 : #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 1) :
    G.lineGraph.Colorable G.maxDegree := by
  by_contra hcl
  have := hiltonZhao_two_le G hconn hcore hcl v
  omega

/-- **Class one** when some vertex has degree at most `Δ − 2`. -/
theorem colorable_of_low_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (v : V) (hv : G.degree v + 2 ≤ G.maxDegree) :
    G.lineGraph.Colorable G.maxDegree := by
  by_contra hcl
  have := hiltonZhao_min_degree G hconn hcore hcl v
  omega

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
  have hcl' : ¬ G.lineGraph.Colorable G.maxDegree := by rwa [hΔ]
  obtain ⟨h1, h2, h3⟩ := CoreDeg2Lib.petal_structure G hconn hcore hcl' hΔ
  refine ⟨h1, fun v hv => ?_, h3⟩
  have := h2 v hv
  unfold CoreDeg2Lib.coreNbrs at this
  rwa [hΔ] at this

/-- **Counting:** a connected class-two graph with `Δ = 3` and core of maximum degree at most
two has `3 |E| = 4 |V|`. -/
theorem three_mul_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcl : ¬ G.lineGraph.Colorable 3) :
    3 * #G.edgeFinset = 4 * Fintype.card V := by
  exact CoreDeg2Lib.three_mul_card_edgeFinset G hconn hcore (by rwa [hΔ]) hΔ

/-- **Class one** (`Δ = 3`) when `3 |E| ≠ 4 |V|`. -/
theorem colorable_of_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hΔ : G.maxDegree = 3)
    (hcore : ∀ v, G.degree v = G.maxDegree →
      #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2)
    (hcard : 3 * #G.edgeFinset ≠ 4 * Fintype.card V) :
    G.lineGraph.Colorable 3 := by
  by_contra hcl
  exact hcard (three_mul_card_edgeFinset G hconn hΔ hcore hcl)

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
  exact CoreDeg2Lib.colorable_of_noInternalPetal G hconn hcore hΔ hr hR

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

instance petersenDecAdj : DecidableRel petersen.Adj := fun a b =>
  decidable_of_iff' _ (SimpleGraph.fromRel_adj _ a b)

/-- The vertices of `P*` as vertices of the Petersen graph other than `0`. -/
def pStarEmb : Fin 9 → Fin 10 := ![2, 3, 8, 6, 9, 7, 1, 4, 5]

/-- The inverse labelling. -/
def pStarInv : Fin 10 → Fin 9 := ![0, 6, 0, 1, 7, 8, 3, 5, 2, 4]

theorem pStarEmb_ne_zero (i : Fin 9) : pStarEmb i ≠ 0 := by
  revert i; decide

theorem pStarInv_emb (i : Fin 9) : pStarInv (pStarEmb i) = i := by
  revert i; decide

theorem pStarEmb_inv (v : Fin 10) (hv : v ≠ 0) : pStarEmb (pStarInv v) = v := by
  revert v; decide

theorem pStarEmb_adj (i j : Fin 9) : petersen.Adj (pStarEmb i) (pStarEmb j) ↔ pStar.Adj i j := by
  revert i j; decide

/-- **`P*` is the Petersen graph minus a vertex.** -/
def pStarIso : pStar ≃g petersen.induce {v | v ≠ 0} where
  toFun i := ⟨pStarEmb i, pStarEmb_ne_zero i⟩
  invFun v := pStarInv v.1
  left_inv i := pStarInv_emb i
  right_inv v := Subtype.ext (pStarEmb_inv v.1 v.2)
  map_rel_iff' {i j} := by
    simp only [Equiv.coe_fn_mk, comap_adj, Function.Embedding.coe_subtype]
    exact pStarEmb_adj i j

theorem pStar_degree (i : Fin 9) : pStar.degree i = if i.val < 6 then 3 else 2 := by
  revert i; decide

theorem pStar_maxDegree' : pStar.maxDegree = 3 := by
  apply le_antisymm
  · exact maxDegree_le_of_forall_degree_le _ _ fun i => by
      rw [pStar_degree]; split_ifs <;> omega
  · have := pStar.degree_le_maxDegree 0
    rwa [pStar_degree] at this

theorem pStar_coreNbrs (i : Fin 9) :
    #((pStar.neighborFinset i).filter fun u => pStar.degree u = 3) ≤ 2 := by
  revert i; decide

theorem pStar_connected' : pStar.Connected := by
  have h : ∀ v, pStar.Reachable 0 v := by
    have a01 : pStar.Adj 0 1 := by decide
    have a12 : pStar.Adj 1 2 := by decide
    have a23 : pStar.Adj 2 3 := by decide
    have a34 : pStar.Adj 3 4 := by decide
    have a45 : pStar.Adj 4 5 := by decide
    have a06 : pStar.Adj 0 6 := by decide
    have a17 : pStar.Adj 1 7 := by decide
    have a28 : pStar.Adj 2 8 := by decide
    have r1 := a01.reachable
    have r2 := r1.trans a12.reachable
    have r3 := r2.trans a23.reachable
    have r4 := r3.trans a34.reachable
    have r5 := r4.trans a45.reachable
    have r6 := a06.reachable
    have r7 := r1.trans a17.reachable
    have r8 := r2.trans a28.reachable
    intro v
    fin_cases v
    exacts [Reachable.refl _, r1, r2, r3, r4, r5, r6, r7, r8]
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

theorem pStar_card_edgeFinset : #pStar.edgeFinset = 12 := by
  decide

/-- `P*` is not overfull: `|E| = 12 = Δ ⌊|V|/2⌋`. -/
theorem pStar_not_overfull' : ¬ pStar.maxDegree * (Fintype.card (Fin 9) / 2) < #pStar.edgeFinset := by
  rw [pStar_maxDegree', pStar_card_edgeFinset]
  decide

/-- The finite core of the class-two check: the hexagon edges `a b c d e g` (`01, 12, 23, 34,
45, 50`) and the petal edges `p₀ … p₅` (at vertex `i`) admit no proper colouring with three
colours. -/
theorem pStar_key : ∀ a b : Fin 3, a ≠ b → ∀ p1 : Fin 3, p1 ≠ a → p1 ≠ b →
    ∀ c : Fin 3, c ≠ b → ∀ p2 : Fin 3, p2 ≠ b → p2 ≠ c →
    ∀ d : Fin 3, d ≠ c → ∀ p3 : Fin 3, p3 ≠ c → p3 ≠ d →
    ∀ e : Fin 3, e ≠ d → ∀ p4 : Fin 3, p4 ≠ d → p4 ≠ e → p4 ≠ p1 →
    ∀ g : Fin 3, g ≠ e → g ≠ a → ∀ p5 : Fin 3, p5 ≠ e → p5 ≠ g → p5 ≠ p2 →
    ∀ p0 : Fin 3, p0 ≠ a → p0 ≠ g → p0 ≠ p3 → False := by
  decide

/-- **`P*` is of class two.** -/
theorem not_colorable_pStar : ¬ pStar.lineGraph.Colorable 3 := by
  rintro ⟨C⟩
  let f : Fin 9 → Fin 9 → Fin 3 := fun i j =>
    if h : pStar.Adj i j then C ⟨s(i, j), h⟩ else 0
  -- two distinct edges sharing a vertex get different colours
  have hgen : ∀ i j k l, pStar.Adj i j → pStar.Adj k l → (i = k ∨ i = l ∨ j = k ∨ j = l) →
      s(i, j) ≠ s(k, l) → f i j ≠ f k l := by
    intro i j k l hij hkl hsh hne
    simp only [f, dif_pos hij, dif_pos hkl]
    refine C.valid ?_
    rw [lineGraph_adj_iff_exists]
    refine ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
    rcases hsh with rfl | rfl | rfl | rfl
    · exact ⟨i, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    · exact ⟨i, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩
    · exact ⟨j, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    · exact ⟨j, Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩
  exact pStar_key (f 0 1) (f 1 2) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 1 7) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 2 3) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 2 8) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 3 4) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 3 6) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 4 5) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 4 7) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 5 0) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 5 8) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (f 0 6) (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (hgen _ _ _ _ (by decide) (by decide) (by decide) (by decide))

/-- `P*` is the Petersen graph with the vertex `0` deleted. -/
theorem pStar_iso : Nonempty (pStar ≃g petersen.induce {v | v ≠ 0}) := by
  exact ⟨pStarIso⟩

theorem pStar_maxDegree : pStar.maxDegree = 3 := by
  exact pStar_maxDegree'

/-- The core of `P*` (the hexagon) has maximum degree two. -/
theorem pStar_core : ∀ v, pStar.degree v = pStar.maxDegree →
    #((pStar.neighborFinset v).filter fun u => pStar.degree u = pStar.maxDegree) ≤ 2 := by
  intro v _
  rw [pStar_maxDegree']
  exact pStar_coreNbrs v

theorem pStar_connected : pStar.Connected := by
  exact pStar_connected'

/-- **`P*` is of class two.** -/
theorem pStar_not_colorable : ¬ pStar.lineGraph.Colorable pStar.maxDegree := by
  rw [pStar_maxDegree']
  exact not_colorable_pStar

/-- `P*` is not overfull. -/
theorem pStar_not_overfull :
    ¬ pStar.maxDegree * (Fintype.card (Fin 9) / 2) < #pStar.edgeFinset := by
  exact pStar_not_overfull'

end CoreDeg2
