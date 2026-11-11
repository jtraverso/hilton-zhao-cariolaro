/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.CycleColour
public import CoreDeg2.CycleWalk
public import LeanPool.Vizing.Main

/-!
# Recolouring a core cycle together with its petal edges

Let `R` be the vertex set of a cycle `p` (in some graph `K`) inside `G`, such that every vertex
`x ∈ R` has exactly one neighbour `pw x` outside `R` (its *petal centre*), the petal centres of
distinct vertices of `R` are distinct, and the other neighbours of `pw x` lie outside `R`. Given
a partial colouring `d` of `G` that colours every edge with both ends outside `R`, and a proper
colouring `c` of the edges of the cycle such that for every `x ∈ R` the colour missing at `x` on
the cycle differs from the colour of the far edge of its petal, we obtain a proper
`3`-edge-colouring of `G` (`colorable_of_cycle_colouring`): the cycle edges get `c`, the edge
`x – pw x` gets the colour missing at `x`, and every other edge keeps its colour from `d`.
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph LeanPool.Vizing LeanPool.Vizing.PEC CycleWalk

/-- The previous index on a cycle of length `k`. -/
def prevI (k i : ℕ) : ℕ := if i = 0 then k - 1 else i - 1

theorem prevI_lt {k i : ℕ} (hi : i < k) : prevI k i < k := by
  unfold prevI; split_ifs <;> omega

theorem succ_mod_eq {k i : ℕ} (hi : i < k) : (i + 1) % k = if i + 1 = k then 0 else i + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- If `i` is the successor of `j` (mod `k`), then `j` is the predecessor of `i`. -/
theorem eq_prevI_of_succ {k i j : ℕ} (hj : j < k) (h : i = (j + 1) % k) : j = prevI k i := by
  rw [succ_mod_eq hj] at h
  unfold prevI
  split_ifs at h with h1 <;> split_ifs with h2 <;> omega

theorem succ_succ_ne {k i : ℕ} (hk : 3 ≤ k) (hi : i < k) : ((i + 1) % k + 1) % k ≠ i := by
  rw [succ_mod_eq hi]
  split_ifs with h
  · rw [succ_mod_eq (by omega)]; split_ifs <;> omega
  · rw [succ_mod_eq (by omega)]; split_ifs <;> omega

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {K : SimpleGraph V} {v₀ : V} {p : K.Walk v₀ v₀}

section Assemble

variable (hp : p.IsCycle) (R : Set V) (hR : ∀ v, v ∈ R ↔ v ∈ p.support) (pw py : V → V)
  (hRR : ∀ u v, u ∈ R → v ∈ R → G.Adj u v → p.toSubgraph.Adj u v)
  (hRout : ∀ u v, u ∈ R → v ∉ R → G.Adj u v → v = pw u)
  (hpw_inj : ∀ x x', x ∈ R → x' ∈ R → pw x = pw x' → x = x')
  (hpy : ∀ x, x ∈ R → ∀ z, G.Adj (pw x) z → z ∉ R → z = py x)
  (d : PEC G (Fin 3)) (hd : ∀ u v, G.Adj u v → u ∉ R → v ∉ R → d.col u v ≠ none)
  (c : ℕ → Fin 3) (hc1 : ∀ i < p.length, c (prevI p.length i) ≠ c i)
  (hc2 : ∀ x, x ∈ R → d.col (pw x) (py x) ≠
    some (third (c (prevI p.length (idx p x))) (c (idx p x))))

/-- The colour of a cycle edge `uv`. -/
noncomputable def edgeC (p : K.Walk v₀ v₀) (c : ℕ → Fin 3) (u v : V) : Fin 3 :=
  if idx p v = (idx p u + 1) % p.length then c (idx p u) else c (idx p v)

/-- The colour missing at `u` on the cycle. -/
noncomputable def misC (p : K.Walk v₀ v₀) (c : ℕ → Fin 3) (u : V) : Fin 3 :=
  third (c (prevI p.length (idx p u))) (c (idx p u))

open Classical in
/-- The assembled colour function. -/
noncomputable def asmCol (G : SimpleGraph V) [DecidableRel G.Adj] (p : K.Walk v₀ v₀) (R : Set V)
    (d : PEC G (Fin 3)) (c : ℕ → Fin 3) (u v : V) : Option (Fin 3) :=
  if G.Adj u v then
    if u ∈ R then (if v ∈ R then some (edgeC p c u v) else some (misC p c u))
    else (if v ∈ R then some (misC p c v) else d.col u v)
  else none

include hp hR hRR in
/-- Adjacent vertices of `R` have consecutive indices, in exactly one order. -/
theorem idx_cases {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) :
    (idx p v = (idx p u + 1) % p.length ∧ ¬ idx p u = (idx p v + 1) % p.length) ∨
    (idx p u = (idx p v + 1) % p.length ∧ ¬ idx p v = (idx p u + 1) % p.length) := by
  have hk := three_le hp
  have hu' := idx_lt hp ((hR u).1 hu)
  have hv' := idx_lt hp ((hR v).1 hv)
  rcases idx_of_toSubgraph_adj hp (hRR u v hu hv huv) with h | h
  · refine Or.inl ⟨h, fun h' => succ_succ_ne hk hu' ?_⟩
    rw [← h, ← h']
  · refine Or.inr ⟨h, fun h' => succ_succ_ne hk hv' ?_⟩
    rw [← h, ← h']

include hp hR hRR in
theorem edgeC_symm {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) :
    edgeC p c u v = edgeC p c v u := by
  unfold edgeC
  rcases idx_cases hp R hR hRR hu hv huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2]
  · rw [if_neg h2, if_pos h1]

include hp hR hRR in
/-- The colour of a cycle edge at `u`: `c (idx u)` towards the successor, `c (prev (idx u))`
towards the predecessor. -/
theorem edgeC_cases {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) :
    (idx p v = (idx p u + 1) % p.length ∧ edgeC p c u v = c (idx p u)) ∨
    (idx p v = prevI p.length (idx p u) ∧ edgeC p c u v = c (prevI p.length (idx p u))) := by
  unfold edgeC
  rcases idx_cases hp R hR hRR hu hv huv with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, if_pos h1⟩
  · have := eq_prevI_of_succ (idx_lt hp ((hR v).1 hv)) h1
    exact Or.inr ⟨this, by rw [if_neg h2, this]⟩

include hp hR hRR hRout hpw_inj hpy hc1 hc2 in
theorem asmCol_proper {u v w : V} {γ : Fin 3} (hv : asmCol G p R d c u v = some γ)
    (hw : asmCol G p R d c u w = some γ) : v = w := by
  classical
  have hk := three_le hp
  unfold asmCol at hv hw
  by_cases huv : G.Adj u v
  swap
  · rw [if_neg huv] at hv; exact absurd hv (by simp)
  by_cases huw : G.Adj u w
  swap
  · rw [if_neg huw] at hw; exact absurd hw (by simp)
  rw [if_pos huv] at hv
  rw [if_pos huw] at hw
  by_cases hu : u ∈ R
  · rw [if_pos hu] at hv hw
    have hiu := idx_lt hp ((hR u).1 hu)
    have hne := hc1 _ hiu
    have hm1 := third_ne_left _ _ hne
    have hm2 := third_ne_right _ _ hne
    by_cases hvR : v ∈ R <;> by_cases hwR : w ∈ R
    · rw [if_pos hvR] at hv; rw [if_pos hwR] at hw
      apply idx_inj hp ((hR v).1 hvR) ((hR w).1 hwR)
      rcases edgeC_cases hp R hR hRR c hu hvR huv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩ <;>
      rcases edgeC_cases hp R hR hRR c hu hwR huw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      · rw [hv1, hw1]
      · rw [hv2] at hv; rw [hw2] at hw
        exact absurd (Option.some_injective _ (hw.trans hv.symm)) hne
      · rw [hv2] at hv; rw [hw2] at hw
        exact absurd (Option.some_injective _ (hv.trans hw.symm)) hne
      · rw [hv1, hw1]
    · rw [if_pos hvR] at hv; rw [if_neg hwR] at hw
      have hmis : misC p c u = γ := Option.some_injective _ hw
      rcases edgeC_cases hp R hR hRR c hu hvR huv with ⟨-, hv2⟩ | ⟨-, hv2⟩ <;>
        rw [hv2] at hv <;> have := Option.some_injective _ hv <;> unfold misC at hmis
      · exact absurd (hmis.trans this.symm) hm2
      · exact absurd (hmis.trans this.symm) hm1
    · rw [if_neg hvR] at hv; rw [if_pos hwR] at hw
      have hmis : misC p c u = γ := Option.some_injective _ hv
      rcases edgeC_cases hp R hR hRR c hu hwR huw with ⟨-, hw2⟩ | ⟨-, hw2⟩ <;>
        rw [hw2] at hw <;> have := Option.some_injective _ hw <;> unfold misC at hmis
      · exact absurd (hmis.trans this.symm) hm2
      · exact absurd (hmis.trans this.symm) hm1
    · rw [hRout u v hu hvR huv, hRout u w hu hwR huw]
  · rw [if_neg hu] at hv hw
    by_cases hvR : v ∈ R <;> by_cases hwR : w ∈ R
    · -- `u` is the petal centre of both `v` and `w`
      have h1 := hRout v u hvR hu huv.symm
      have h2 := hRout w u hwR hu huw.symm
      exact hpw_inj v w hvR hwR (h1.symm.trans h2)
    · rw [if_pos hvR] at hv; rw [if_neg hwR] at hw
      have h1 := hRout v u hvR hu huv.symm
      subst h1
      have h2 := hpy v hvR w huw hwR
      subst h2
      exact absurd (hw.trans hv.symm) (hc2 v hvR)
    · rw [if_neg hvR] at hv; rw [if_pos hwR] at hw
      have h1 := hRout w u hwR hu huw.symm
      subst h1
      have h2 := hpy w hwR v huv hvR
      subst h2
      exact absurd (hv.trans hw.symm) (hc2 w hwR)
    · rw [if_neg hvR] at hv; rw [if_neg hwR] at hw
      exact d.col_proper hv hw

include hp hR hRR hRout hpw_inj hpy hc1 hc2 hd in
/-- **Assembly.** -/
theorem colorable_of_cycle_colouring : G.lineGraph.Colorable 3 := by
  classical
  let e : PEC G (Fin 3) :=
    { col := asmCol G p R d c
      col_symm := by
        intro u v
        unfold asmCol
        by_cases huv : G.Adj u v
        · rw [if_pos huv, if_pos huv.symm]
          by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> simp only [hu, hv, ↓reduceIte]
          · rw [edgeC_symm hp R hR hRR c hu hv huv]
          · exact d.col_symm u v
        · rw [if_neg huv, if_neg (fun h => huv h.symm)]
      col_adj := by
        intro u v γ h
        unfold asmCol at h
        by_contra huv
        rw [if_neg huv] at h
        exact absurd h (by simp)
      col_proper := fun hv hw =>
        asmCol_proper hp R hR pw py hRR hRout hpw_inj hpy d c hc1 hc2 hv hw }
  refine ⟨e.lineGraphColoring fun u v huv => ?_⟩
  show asmCol G p R d c u v ≠ none
  unfold asmCol
  rw [if_pos huv]
  by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> simp only [hu, hv, ↓reduceIte]
  all_goals first
    | exact Option.some_ne_none _
    | exact hd u v huv hu hv

end Assemble

end CoreDeg2Lib
