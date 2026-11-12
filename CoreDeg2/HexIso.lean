/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Recognising `P*`

`pStarL` is the Petersen graph minus a vertex on `Fin 9` (hexagon `0 … 5`, vertices `6, 7, 8`
joined to `{0, 3}, {1, 4}, {2, 5}`). A graph whose vertices are a hexagon `x 0 … x 5` and three
vertices `w 0, w 1, w 2` with `w c` adjacent exactly to `x c` and `x (c + 3)` is isomorphic to it
(`iso_of_hex`).
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph

/-- The edges of `P*`. -/
def pStarEdgesL : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (6, 0), (6, 3), (7, 1), (7, 4), (8, 2), (8, 5)]

/-- `P*`, the Petersen graph minus a vertex. -/
def pStarL : SimpleGraph (Fin 9) := SimpleGraph.fromRel fun i j => (i, j) ∈ pStarEdgesL

instance : DecidableRel pStarL.Adj := fun a b =>
  decidable_of_iff' _ (SimpleGraph.fromRel_adj _ a b)

/-- Adjacency in `P*`, arithmetically. -/
def PR (i j : ℕ) : Prop :=
  (i < 6 ∧ j < 6 ∧ (j = (i + 1) % 6 ∨ i = (j + 1) % 6)) ∨ (i < 6 ∧ 6 ≤ j ∧ i % 3 = j - 6) ∨
    (6 ≤ i ∧ j < 6 ∧ j % 3 = i - 6)

instance (i j : ℕ) : Decidable (PR i j) := by unfold PR; infer_instance

theorem pStarL_adj_iff : ∀ a b : Fin 9, pStarL.Adj a b ↔ PR a.val b.val := by decide

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Recognition of `P*`.** -/
theorem iso_of_hex (x w : ℕ → V)
    (hxinj : ∀ a b, a < 6 → b < 6 → x a = x b → a = b)
    (hxadj : ∀ a b, a < 6 → b < 6 → (G.Adj (x a) (x b) ↔ (b = (a + 1) % 6 ∨ a = (b + 1) % 6)))
    (hwx : ∀ a c, a < 6 → c < 3 → (G.Adj (x a) (w c) ↔ a % 3 = c))
    (hww : ∀ c c', c < 3 → c' < 3 → ¬ G.Adj (w c) (w c'))
    (hwne : ∀ c a, c < 3 → a < 6 → w c ≠ x a)
    (hwinj : ∀ c c', c < 3 → c' < 3 → w c = w c' → c = c')
    (hall : ∀ v, (∃ a, a < 6 ∧ v = x a) ∨ (∃ c, c < 3 ∧ v = w c)) :
    Nonempty (pStarL ≃g G) := by
  classical
  let f : Fin 9 → V := fun i => if i.val < 6 then x i.val else w (i.val - 6)
  have hinj : Function.Injective f := by
    intro i j h
    simp only [f] at h
    apply Fin.ext
    split_ifs at h with hi hj hj
    · exact hxinj _ _ hi hj h
    · exact absurd h.symm (hwne _ _ (by omega) hi)
    · exact absurd h (hwne _ _ (by omega) hj)
    · have := hwinj _ _ (by omega) (by omega) h; omega
  have hsurj : Function.Surjective f := by
    intro v
    rcases hall v with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
    · exact ⟨⟨a, by omega⟩, by simp [f, ha]⟩
    · exact ⟨⟨c + 6, by omega⟩, by simp [f, show ¬ (c + 6 < 6) by omega]⟩
  refine ⟨⟨Equiv.ofBijective f (show Function.Bijective f from ⟨hinj, hsurj⟩), fun {a b} => ?_⟩⟩
  show G.Adj (f a) (f b) ↔ _
  rw [pStarL_adj_iff a b]
  have ha := a.2
  have hb := b.2
  unfold PR
  by_cases h1 : a.val < 6 <;> by_cases h2 : b.val < 6
  · simp only [f, if_pos h1, if_pos h2]
    rw [hxadj _ _ h1 h2]
    constructor
    · intro h; exact Or.inl ⟨h1, h2, h⟩
    · rintro (⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨h, -⟩)
      · exact h
      · omega
      · omega
  · simp only [f, if_pos h1, if_neg h2]
    rw [hwx _ _ h1 (by omega)]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨h1, by omega, h⟩)
    · rintro (⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩)
      · omega
      · exact h
      · omega
  · simp only [f, if_neg h1, if_pos h2]
    rw [G.adj_comm, hwx _ _ h2 (by omega)]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨by omega, h2, h⟩)
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩)
      · omega
      · omega
      · exact h
  · simp only [f, if_neg h1, if_neg h2]
    constructor
    · intro h; exact absurd h (hww _ _ (by omega) (by omega))
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩) <;> omega

/-- Line graphs of isomorphic graphs are equally colourable. -/
theorem lineGraph_colorable_of_iso {W : Type*} {H : SimpleGraph W} (e : H ≃g G) {n : ℕ}
    (h : G.lineGraph.Colorable n) : H.lineGraph.Colorable n := by
  obtain ⟨C⟩ := h
  let f : H.lineGraph →g G.lineGraph :=
    { toFun := fun x => ⟨Sym2.map e x.1, by
        obtain ⟨y, hy⟩ := x
        induction y using Sym2.ind with
        | h u v => simpa [mem_edgeSet] using e.map_adj_iff.2 hy⟩
      map_rel' := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        rw [lineGraph_adj_iff_exists] at hxy ⊢
        obtain ⟨hne, v, hv1, hv2⟩ := hxy
        refine ⟨fun h => hne ?_, e v, Sym2.mem_map.2 ⟨v, hv1, rfl⟩,
          Sym2.mem_map.2 ⟨v, hv2, rfl⟩⟩
        apply Subtype.ext
        exact Sym2.map.injective e.injective (congrArg Subtype.val h) }
  exact ⟨C.comp f⟩

end CoreDeg2Lib
