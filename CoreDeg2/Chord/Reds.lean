/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Chord.Reduce
public import Mathlib.Tactic.IntervalCases

/-!
# The five safe reductions

For a block at positions `m … k − 1` of an instance `J`, the restriction seen by a block vertex
`b` from outside the block is `pval m J c' b`: its `ext` colour, or the colour missing (in the
reduced solution `c'`) at its partner in `[0, m)`, or nothing.
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

open Classical in
/-- The restriction of a block vertex. -/
noncomputable def pval (m k' : ℕ) (J : ℕ → VT) (c' : ℕ → Fin 3) (b : ℕ) : Option (Fin 3) :=
  match J b with
  | .ext a => some a
  | .lab l => if h : ∃ i, i < m ∧ J i = .lab l then some (mvAt k' c' (Nat.find h)) else none

theorem pval_ext {m k' : ℕ} {J : ℕ → VT} {c' : ℕ → Fin 3} {b : ℕ} {a : Fin 3} (h : J b = .ext a) :
    pval m k' J c' b = some a := by
  simp [pval, h]

/-- With a unique outside partner `i`, the restriction is the colour missing at `i`. -/
theorem pval_lab {m k' : ℕ} {J : ℕ → VT} {c' : ℕ → Fin 3} {b i : ℕ} {l : ℕ} (hb : J b = .lab l)
    (hi : i < m) (hil : J i = .lab l) (huniq : ∀ i', i' < m → J i' = .lab l → i' = i) :
    pval m k' J c' b = some (mvAt k' c' i) := by
  classical
  have hex : ∃ i, i < m ∧ J i = .lab l := ⟨i, hi, hil⟩
  simp only [pval, hb, dif_pos hex]
  congr 2
  exact huniq _ (Nat.find_spec hex).1 (Nat.find_spec hex).2

theorem pval_free {m k' : ℕ} {J : ℕ → VT} {c' : ℕ → Fin 3} {b : ℕ} {l : ℕ} (hb : J b = .lab l)
    (hno : ∀ i < m, J i ≠ .lab l) : pval m k' J c' b = none := by
  classical
  have : ¬ ∃ i, i < m ∧ J i = .lab l := fun ⟨i, hi, h⟩ => hno i hi h
  simp [pval, hb, dif_neg this]

/-- Uniqueness of outside partners from well-formedness. -/
theorem uniq_of_wf {k m : ℕ} {J : ℕ → VT} (hwf : WFf k J) (hmk : m ≤ k) {b l : ℕ} (hbk : b < k)
    (hbm : m ≤ b) (hb : J b = .lab l) {i : ℕ} (hi : i < m) (hil : J i = .lab l) :
    ∀ i', i' < m → J i' = .lab l → i' = i := by
  intro i' hi' hi'l
  by_contra hne
  exact hwf i' b i ⟨by omega, hbk, by omega, l, hi'l, hb⟩ ⟨hbk, by omega, by omega, l, hb, hil⟩ hne

/-- A block vertex whose missing colour avoids its restriction satisfies its constraints. -/
theorem sat_ext_of_pval {m k' : ℕ} {J : ℕ → VT} {c' : ℕ → Fin 3} {b : ℕ} {v : Fin 3}
    (hv : ∀ x, pval m k' J c' b = some x → v ≠ x) : ∀ a, J b = .ext a → v ≠ a :=
  fun a ha => hv a (pval_ext ha)

theorem sat_AB_of_pval {k m k' : ℕ} {J : ℕ → VT} {c' : ℕ → Fin 3} (hwf : WFf k J) (hmk : m ≤ k)
    {b : ℕ} (hbk : b < k) (hbm : m ≤ b) {v : Fin 3}
    (hv : ∀ x, pval m k' J c' b = some x → v ≠ x) :
    ∀ i < m, ∀ l, J i = .lab l → J b = .lab l → mvAt k' c' i ≠ v := by
  intro i hi l hil hb
  exact (hv _ (pval_lab hb hi hil (uniq_of_wf hwf hmk hbk hbm hb hi hil))).symm

/-! ### Decidable facts about three colours -/

theorem f3_adj : ∀ a b : Fin 3, a ≠ b →
    a ≠ third a b ∧ third a b ≠ b ∧ third a (third a b) ≠ third (third a b) b := by decide

theorem f3_d2A : ∀ a b : Fin 3, a ≠ b →
    a ≠ b ∧ b ≠ third a b ∧ third a b ≠ b ∧ third a b ≠ third (third a b) b ∧
      third b (third a b) = a := by decide

theorem f3_d2B : ∀ a b : Fin 3, a ≠ b →
    a ≠ third a b ∧ third a b ≠ a ∧ a ≠ b ∧ third a (third a b) ≠ third a b ∧
      third (third a b) a = b := by decide

theorem f3_mem : ∀ a b x : Fin 3, a ≠ b → third a b ≠ x → x = a ∨ x = b := by decide

/-! ### Reduction 1: two adjacent vertices with the same label -/

/-- The reduced instance: the block `m, m + 1` becomes one free vertex (label `l`). -/
theorem red_adj {k : ℕ} {J : ℕ → VT} (hk : 3 ≤ k) (hwf : WFf k J) {l : ℕ}
    (h1 : J (k - 2) = .lab l) (h2 : J (k - 1) = .lab l)
    (hs : Solv (k - 1) fun i => if i < k - 2 then J i else .lab l) : Solv k J := by
  obtain ⟨c', hc'⟩ := hs
  set m := k - 2
  have hprop := hc'.1 m (by omega)
  rw [prevI_pos (by omega)] at hprop
  set κ₁ := c' (m - 1)
  set κ₂ := c' m
  obtain ⟨f1, f2, f3⟩ := f3_adj κ₁ κ₂ hprop
  let E : ℕ → Fin 3 := fun j => if j = 0 then κ₁ else if j = 1 then third κ₁ κ₂ else κ₂
  have hno : ∀ i < m, J i ≠ .lab l := fun i hi hil =>
    hwf i (k - 2) (k - 1) ⟨by omega, by omega, by omega, l, hil, h1⟩
      ⟨by omega, by omega, by omega, l, h1, h2⟩ (by omega)
  refine extend (s := 2) (k' := m + 1) (E := E) (by omega) (by omega) le_rfl (by omega) (by omega)
    (by rwa [show m + 1 = k - 1 by omega]) rfl (by simp [E, show m + 1 - 1 = m by omega, κ₂])
    (fun i hi a ha => by simp [hi, ha]) (fun i j hi hj _ l' hil hjl => ⟨l', by simp [hi, hil],
      by simp [hj, hjl]⟩) (fun j hj => ?_) (fun j hj a ha => ?_)
    (fun j j' hj hj' hjj l' hl hl' => ?_) (fun i hi j hj l' hil hjl => ?_)
  · interval_cases j <;> simp [E] <;> assumption
  · interval_cases j
    · rw [show m + 0 = k - 2 by omega, h1] at ha; cases ha
    · rw [show m + 1 = k - 1 by omega, h2] at ha; cases ha
  · interval_cases j <;> interval_cases j'
    · exact absurd rfl hjj
    · simpa [E] using f3
    · simpa [E] using fun h => f3 h.symm
    · exact absurd rfl hjj
  · interval_cases j
    · rw [show m + 0 = k - 2 by omega, h1] at hjl; cases hjl; exact absurd hil (hno i hi)
    · rw [show m + 1 = k - 1 by omega, h2] at hjl; cases hjl; exact absurd hil (hno i hi)


/-! ### Reduction 2: a chord at distance two -/

theorem f3_props : ∀ a b : Fin 3, a ≠ b →
    b ≠ third a b ∧ third a b ≠ b ∧ a ≠ third a b ∧ third a b ≠ a ∧
    third b (third a b) = a ∧ third (third a b) b = a ∧ third (third a b) a = b ∧
    third a (third a b) = b ∧ third a b ≠ third (third a b) b ∧
    third a (third a b) ≠ third a b := by decide

/-- The block `x z y` (`x, y` with the same label) becomes one free vertex. -/
theorem red_dist2 {k : ℕ} {J : ℕ → VT} (hk : 4 ≤ k) (hwf : WFf k J) {l : ℕ}
    (h1 : J (k - 3) = .lab l) (h3 : J (k - 1) = .lab l)
    (hs : Solv (k - 2) fun i => if i < k - 3 then J i else .lab l) : Solv k J := by
  obtain ⟨c', hc'⟩ := hs
  set m := k - 3 with hm
  have hprop := hc'.1 m (by omega)
  rw [prevI_pos (by omega)] at hprop
  set κ₁ := c' (m - 1)
  set κ₂ := c' m
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, P10⟩ := f3_props κ₁ κ₂ hprop
  set t := pval m (k - 2) J c' (m + 1)
  obtain ⟨x, hx, hxt⟩ := fin3_two_vals κ₁ κ₂ (t.getD (third κ₁ κ₂)) hprop
  have hxt' : ∀ y, t = some y → x ≠ y := fun y hy => by rw [hy] at hxt; exact hxt
  have hno : ∀ i < m, J i ≠ .lab l := fun i hi hil =>
    hwf i (k - 3) (k - 1) ⟨by omega, by omega, by omega, l, hil, h1⟩
      ⟨by omega, by omega, by omega, l, h1, h3⟩ (by omega)
  have hz : ∀ l', J (m + 1) = .lab l' → l' ≠ l := fun l' hz hll => by
    subst hll
    exact hwf (k - 3) (m + 1) (k - 1) ⟨by omega, by omega, by omega, l', h1, hz⟩
      ⟨by omega, by omega, by omega, l', hz, h3⟩ (by omega)
  -- option A (`x = κ₁`): edges κ₁ κ₂ μ κ₂; option B (`x = κ₂`): edges κ₁ μ κ₁ κ₂
  let E : ℕ → Fin 3 := fun j =>
    if x = κ₁ then (if j = 0 then κ₁ else if j = 1 then κ₂ else if j = 2 then third κ₁ κ₂ else κ₂)
    else (if j = 0 then κ₁ else if j = 1 then third κ₁ κ₂ else if j = 2 then κ₁ else κ₂)
  have hE0 : E 0 = κ₁ := by simp [E]
  have hE3 : E 3 = κ₂ := by simp [E]
  have hmid : third (E 1) (E 2) = x := by
    by_cases hx1 : x = κ₁
    · simp only [E, if_pos hx1]; simp only [one_ne_zero, if_false, if_true,
        show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega]; rw [hx1]; exact P5
    · have hx2 : x = κ₂ := hx.resolve_left hx1
      simp only [E, if_neg hx1]; simp only [one_ne_zero, if_false, if_true,
        show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega]; rw [hx2]; exact P7
  have hend : third (E 0) (E 1) ≠ third (E 2) (E 3) := by
    by_cases hx1 : x = κ₁
    · simp only [E, if_pos hx1]; simp only [one_ne_zero, if_false, if_true,
        show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 0 by omega,
        show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega]; exact P9
    · simp only [E, if_neg hx1]; simp only [one_ne_zero, if_false, if_true,
        show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 0 by omega,
        show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega]
      exact P10
  have hprops : ∀ j < 3, E j ≠ E (j + 1) := by
    intro j hj
    by_cases hx1 : x = κ₁ <;> interval_cases j <;> simp only [E, hx1, if_true, if_false] <;>
      simp only [one_ne_zero, if_false, if_true, show (2 : ℕ) ≠ 0 by omega,
        show (2 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega,
        show (3 : ℕ) ≠ 2 by omega, Nat.zero_add, show (0 : ℕ) + 1 = 1 from rfl,
        show (1 : ℕ) + 1 = 2 from rfl, show (2 : ℕ) + 1 = 3 from rfl] <;>
      first | exact hprop | exact P1 | exact P2 | exact P3 | exact P4
  have hl0 : J (m + 0) = .lab l := by rw [show m + 0 = k - 3 by omega]; exact h1
  have hl2 : J (m + 2) = .lab l := by rw [show m + 2 = k - 1 by omega]; exact h3
  refine extend (s := 3) (k' := m + 1) (E := E) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by rwa [show m + 1 = k - 2 by omega]) hE0
    (by rw [hE3, show m + 1 - 1 = m by omega])
    (fun i hi a ha => by simp [hi, ha]) (fun i j hi hj _ l' hil hjl => ⟨l', by simp [hi, hil],
      by simp [hj, hjl]⟩) hprops (fun j hj a ha => ?_)
    (fun j j' hj hj' hjj l' hl hl' => ?_) (fun i hi j hj l' hil hjl => ?_)
  · interval_cases j
    · rw [hl0] at ha; cases ha
    · rw [hmid]; exact hxt' a (pval_ext ha)
    · rw [hl2] at ha; cases ha
  · interval_cases j <;> interval_cases j'
    all_goals first
      | exact absurd rfl hjj
      | exact hend | exact hend.symm
      | (rw [hl0] at hl; cases hl; exact absurd rfl (hz _ hl'))
      | (rw [hl2] at hl; cases hl; exact absurd rfl (hz _ hl'))
      | (rw [hl0] at hl'; cases hl'; exact absurd rfl (hz _ hl))
      | (rw [hl2] at hl'; cases hl'; exact absurd rfl (hz _ hl))
  · interval_cases j
    · rw [hl0] at hjl; cases hjl; exact absurd hil (hno i hi)
    · rw [hmid]
      exact sat_AB_of_pval hwf (by omega) (by omega) (by omega) hxt' i hi l' hil hjl
    · rw [hl2] at hjl; cases hjl; exact absurd hil (hno i hi)

end CoreDeg2Lib.Chord
