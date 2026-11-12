/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.CycleColour
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Count

/-!
# Cyclic instances of the chorded-cycle problem

A cyclic list of vertex types: `ext a` (the colour missing at the vertex must differ from `a`) or
`lab l` (vertices carrying the same label must miss different colours; a label carried once is a
free vertex). A solution assigns to each vertex the pair `(in, out)` of the colours of its two
cycle edges: `in ≠ out`, and the `out` colour of a vertex is the `in` colour of the next one,
cyclically. The colour missing at a vertex is `mv (in, out) = third in out`.
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

/-- Vertex types. -/
inductive VT where
  | ext (a : Fin 3)
  | lab (l : ℕ)
  deriving DecidableEq

/-- Edge colours at a vertex: `(in, out)`. -/
abbrev Pair := Fin 3 × Fin 3

/-- The colour missing at a vertex. -/
def mv (p : Pair) : Fin 3 := third p.1 p.2

/-- Two vertices carrying the same label miss different colours. -/
def Compat (x y : VT × Pair) : Prop := ∀ l, x.1 = .lab l → y.1 = .lab l → mv x.2 ≠ mv y.2

/-- Consecutive vertices share their edge. -/
def Link (x y : VT × Pair) : Prop := x.2.2 = y.2.1

/-- A valid cyclic list of typed, coloured vertices. -/
structure Valid (L : List (VT × Pair)) : Prop where
  proper : ∀ x ∈ L, x.2.1 ≠ x.2.2
  ext : ∀ x ∈ L, ∀ a, x.1 = .ext a → mv x.2 ≠ a
  pair : L.Pairwise Compat
  chain : L.IsChain Link
  close : ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, Link x y

/-- An instance is solvable. -/
def Solvable (I : List VT) : Prop := ∃ L : List (VT × Pair), L.map Prod.fst = I ∧ Valid L

theorem Compat.symm {x y : VT × Pair} (h : Compat x y) : Compat y x :=
  fun l hy hx => (h l hx hy).symm

/-- Rotating by one step preserves validity. -/
theorem Valid.rotate_one {a : VT × Pair} {t : List (VT × Pair)} (h : Valid (a :: t)) :
    Valid (t ++ [a]) := by
  obtain ⟨hp, he, hpa, hc, hcl⟩ := h
  refine ⟨fun x hx => hp x (by simp at hx ⊢; tauto), fun x hx => he x (by simp at hx ⊢; tauto),
    ?_, ?_, ?_⟩
  · rw [List.pairwise_cons] at hpa
    rw [List.pairwise_append]
    exact ⟨hpa.2, by simp, fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy; exact (hpa.1 x hx).symm⟩
  · rw [List.isChain_append]
    refine ⟨hc.tail, by simp, fun x hx y hy => ?_⟩
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    cases t with
    | nil => simp at hx
    | cons b t =>
      apply hcl x _ a (by simp)
      rw [List.getLast?_cons_cons]; exact hx
  · intro x hx y hy
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
      Option.some.injEq] at hx
    subst hx
    cases t with
    | nil => simp at hy; subst hy; exact hcl _ (by simp) _ (by simp)
    | cons b t =>
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact (List.isChain_cons_cons.1 hc).1

theorem Valid.rotate {L : List (VT × Pair)} (h : Valid L) (n : ℕ) : Valid (L.rotate n) := by
  induction n generalizing L with
  | zero => simpa using h
  | succ n ih =>
    cases L with
    | nil => simpa using h
    | cons a t =>
      rw [List.rotate_cons_succ]
      exact ih h.rotate_one

theorem Solvable.rotate {I : List VT} (h : Solvable I) (n : ℕ) : Solvable (I.rotate n) := by
  obtain ⟨L, hL, hv⟩ := h
  exact ⟨L.rotate n, by rw [List.map_rotate, hL], hv.rotate n⟩

theorem solvable_of_rotate {I : List VT} {n : ℕ} (hn : n ≤ I.length)
    (h : Solvable (I.rotate n)) : Solvable I := by
  have := h.rotate (I.length - n)
  rwa [List.rotate_rotate, Nat.add_sub_cancel' hn, List.rotate_length] at this

/-! ### Well-formed instances -/

/-- Every label is carried at most twice. -/
def WF (I : List VT) : Prop := ∀ l, I.count (.lab l) ≤ 2

theorem WF.rotate {I : List VT} (h : WF I) (n : ℕ) : WF (I.rotate n) := fun l => by
  rw [(List.rotate_perm I n).count_eq]; exact h l

/-- Some label is carried twice. -/
def HasChord (I : List VT) : Prop := ∃ l, 2 ≤ I.count (.lab l)

end CoreDeg2Lib.Chord
