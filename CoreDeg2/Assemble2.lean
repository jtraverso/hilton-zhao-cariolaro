/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Assemble

/-!
# Recolouring a core cycle with internal petals

Same as `colorable_of_cycle_colouring`, but petal centres may be adjacent to two vertices of the
cycle `R` (internal petals). The conditions: a vertex outside `R` sees different missing colours
at its neighbours in `R` (`hmid`), and the missing colour at its neighbour in `R` differs from the
colours of its other edges (`hfar`).
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph LeanPool.Vizing LeanPool.Vizing.PEC CycleWalk

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {K : SimpleGraph V} {v₀ : V} {p : K.Walk v₀ v₀}

section Assemble2

variable (hp : p.IsCycle) (R : Set V) (hR : ∀ v, v ∈ R ↔ v ∈ p.support) (pw : V → V)
  (hRR : ∀ u v, u ∈ R → v ∈ R → G.Adj u v → p.toSubgraph.Adj u v)
  (hRout : ∀ u v, u ∈ R → v ∉ R → G.Adj u v → v = pw u)
  (d : PEC G (Fin 3)) (hd : ∀ u v, G.Adj u v → u ∉ R → v ∉ R → d.col u v ≠ none)
  (c : ℕ → Fin 3) (hc1 : ∀ i < p.length, c (prevI p.length i) ≠ c i)
  (hmid : ∀ u x x', u ∉ R → x ∈ R → x' ∈ R → G.Adj u x → G.Adj u x' → x ≠ x' →
    misC p c x ≠ misC p c x')
  (hfar : ∀ u x z, u ∉ R → x ∈ R → z ∉ R → G.Adj u x → G.Adj u z →
    d.col u z ≠ some (misC p c x))

include hp hR hRR hRout hc1 hmid hfar in
theorem asmCol_proper' {u v w : V} {γ : Fin 3} (hv : asmCol G p R d c u v = some γ)
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
    · rw [if_pos hvR] at hv; rw [if_pos hwR] at hw
      by_contra hne
      exact hmid u v w hu hvR hwR huv huw hne (Option.some_injective _ (hv.trans hw.symm))
    · rw [if_pos hvR] at hv; rw [if_neg hwR] at hw
      exact absurd (hw.trans hv.symm) (hfar u v w hu hvR hwR huv huw)
    · rw [if_neg hvR] at hv; rw [if_pos hwR] at hw
      exact absurd (hv.trans hw.symm) (hfar u w v hu hwR hvR huw huv)
    · rw [if_neg hvR] at hv; rw [if_neg hwR] at hw
      exact d.col_proper hv hw

include hp hR hRR hRout hc1 hmid hfar hd in
/-- **Assembly with internal petals.** -/
theorem colorable_of_cycle_colouring' : G.lineGraph.Colorable 3 := by
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
        asmCol_proper' hp R hR pw hRR hRout d c hc1 hmid hfar hv hw }
  refine ⟨e.lineGraphColoring fun u v huv => ?_⟩
  show asmCol G p R d c u v ≠ none
  unfold asmCol
  rw [if_pos huv]
  by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> simp only [hu, hv, ↓reduceIte]
  all_goals first
    | exact Option.some_ne_none _
    | exact hd u v huv hu hv

end Assemble2

end CoreDeg2Lib
