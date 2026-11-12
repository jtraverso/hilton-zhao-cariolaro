/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Chord.Defs
public import CoreDeg2.Assemble
public import Mathlib.Data.List.OfFn

/-!
# Index-based descriptions of solutions

`ofFun k ty c` is the valued list whose vertex `i < k` has type `ty i` and edge colours
`c (prevI k i)`, `c i` (edge `i` joins vertices `i` and `i + 1 mod k`). It is valid as soon as the
colouring is proper and the restrictions hold (`valid_ofFun`); conversely every solution of an
instance `ofFn ty` has this form (`exists_fun_of_solvable`).
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

/-- The valued list of an edge colouring `c` of a cycle of length `k`. -/
def ofFun (k : ℕ) (ty : ℕ → VT) (c : ℕ → Fin 3) : List (VT × Pair) :=
  List.ofFn fun i : Fin k => (ty i, (c (prevI k i), c i))

theorem prevI_succ {k i : ℕ} : prevI k (i + 1) = i := by unfold prevI; simp

theorem close_of {L : List (VT × Pair)} (h0 : 0 < L.length)
    (hlink : Link (L[L.length - 1]'(by omega)) (L[0]'h0)) :
    ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, Link x y := by
  intro x hx y hy
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hx
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at hy
  simp only [Option.mem_def, Option.some.injEq] at hx hy
  subst hx; subst hy
  exact hlink

theorem valid_ofFun {k : ℕ} (hk : 1 ≤ k) {ty : ℕ → VT} {c : ℕ → Fin 3}
    (hprop : ∀ i < k, c (prevI k i) ≠ c i)
    (hext : ∀ i < k, ∀ a, ty i = .ext a → third (c (prevI k i)) (c i) ≠ a)
    (hpair : ∀ i j, i < j → j < k → ∀ l, ty i = .lab l → ty j = .lab l →
      third (c (prevI k i)) (c i) ≠ third (c (prevI k j)) (c j)) :
    Valid (ofFun k ty c) := by
  refine ⟨fun x hx => ?_, fun x hx a ha => ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact hprop i i.2
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx; exact hext i i.2 a ha
  · rw [ofFun, List.pairwise_ofFn]
    intro i j hij l hi hj
    exact hpair i j hij j.2 l hi hj
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [ofFun, List.length_ofFn] at hi
    simp only [ofFun, List.getElem_ofFn, Link, prevI_succ]
  · apply close_of (by simp [ofFun]; omega)
    simp only [ofFun, List.getElem_ofFn, List.length_ofFn, Link]
    simp [prevI]

/-- Every solution of `ofFn ty` comes from an edge colouring. -/
theorem exists_fun_of_solvable {k : ℕ} (hk : 1 ≤ k) {ty : ℕ → VT}
    (h : Solvable (List.ofFn fun i : Fin k => ty i)) :
    ∃ c : ℕ → Fin 3, (∀ i < k, c (prevI k i) ≠ c i) ∧
      (∀ i < k, ∀ a, ty i = .ext a → third (c (prevI k i)) (c i) ≠ a) ∧
      (∀ i j, i < j → j < k → ∀ l, ty i = .lab l → ty j = .lab l →
        third (c (prevI k i)) (c i) ≠ third (c (prevI k j)) (c j)) := by
  obtain ⟨L, hL, hv⟩ := h
  have hlen : L.length = k := by rw [← List.length_map (f := Prod.fst), hL, List.length_ofFn]
  have hty : ∀ i (hi : i < L.length), L[i].1 = ty i := by
    intro i hi
    have := List.getElem_of_eq hL (i := i) (by simp; omega)
    simpa using this
  let dflt : VT × Pair := (.ext 0, (0, 0))
  let c : ℕ → Fin 3 := fun i => (L.getD i dflt).2.2
  have hout : ∀ i (hi : i < L.length), c i = L[i].2.2 := fun i hi => by
    simp [c, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hin : ∀ i (hi : i < L.length), L[i].2.1 = c (prevI k i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have h1 : (L[L.length - 1]'(by omega)) ∈ L.getLast? := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
      have h2 : (L[0]'hi) ∈ L.head? := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi]; rfl
      have h3 : (L[L.length - 1]'(by omega)).2.2 = (L[0]'hi).2.1 := hv.close _ h1 _ h2
      rw [show prevI k 0 = L.length - 1 by simp [prevI, hlen], hout _ (by omega)]
      exact h3.symm
    · have h3 : (L[i - 1]'(by omega)).2.2 = (L[i - 1 + 1]'(by omega)).2.1 :=
        hv.chain.getElem (i - 1) (by omega)
      simp only [Nat.sub_add_cancel hpos] at h3
      rw [show prevI k i = i - 1 by simp [prevI, show i ≠ 0 by omega], hout _ (by omega)]
      exact h3.symm
  refine ⟨c, fun i hi => ?_, fun i hi a ha => ?_, fun i j hij hj l hi hj' => ?_⟩
  · have := hv.proper L[i] (List.getElem_mem (by omega))
    rwa [hin i (by omega), ← hout i (by omega)] at this
  · have := hv.ext L[i] (List.getElem_mem (by omega)) a (by rw [hty i (by omega)]; exact ha)
    rwa [mv, hin i (by omega), ← hout i (by omega)] at this
  · have := List.pairwise_iff_getElem.1 hv.pair i j (by omega) (by omega) hij l
      (by rw [hty i (by omega)]; exact hi) (by rw [hty j (by omega)]; exact hj')
    rwa [mv, mv, hin i (by omega), ← hout i (by omega), hin j (by omega),
      ← hout j (by omega)] at this

end CoreDeg2Lib.Chord
