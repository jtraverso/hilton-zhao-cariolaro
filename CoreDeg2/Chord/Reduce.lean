/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Chord.Func
public import CoreDeg2.Chord.Arc

/-!
# Safe reductions

An instance `J` of length `k` whose last `s` vertices (positions `m … k − 1`, `k = m + s`) form a
block `B` is reduced to an instance `ty'` of length `k' ≥ m` that agrees with `J` on `[0, m)` up to
the types of a few partners of `B`. A solution `c'` of `ty'` extends to `J` (`extend`): keep `c'`
on the edges `0 … m − 1` and on the closing edge, and colour the block edges by a sequence `E`
with `E 0 = c' (m − 1)` and `E s = c' (k' − 1)`. The specific reductions:

* `red_adj`: two adjacent vertices with the same label → one free vertex;
* `red_dist2`: `x z y` with `x, y` sharing a label → one free vertex;
* `red_free`: a free vertex and a neighbour → nothing;
* `red_arc`: an arc `x a₁ … a_{p−1} y` (`p ≥ 3`, chord `xy`, inner partners outside the block) →
  one vertex `ext a`, the partners of `a₁, a_{p−1}` get `ext a`;
* `red_arc_remove`: the same arc with `a₁, a_{p−1}` of types `ext b ≠ ext b'` → nothing.
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

theorem prevI_zero (k : ℕ) : prevI k 0 = k - 1 := by simp [prevI]

theorem prevI_pos {k i : ℕ} (hi : 0 < i) : prevI k i = i - 1 := by
  unfold prevI; rw [if_neg (by omega)]

section Extend

variable {k m s k' : ℕ} {J ty' : ℕ → VT} {c' : ℕ → Fin 3} {E : ℕ → Fin 3}

/-- The extended colouring. -/
def extC (m : ℕ) (c' E : ℕ → Fin 3) : ℕ → Fin 3 := fun i => if i < m then c' i else E (i + 1 - m)

theorem extC_lt {m i : ℕ} {c' E : ℕ → Fin 3} (hi : i < m) : extC m c' E i = c' i := by
  simp [extC, hi]

/-- On `[0, m)` the extended colouring has the same edges at every vertex. -/
theorem extC_agree (hm : 1 ≤ m) (hk : k = m + s) (hs : 1 ≤ s) (hk' : m ≤ k') (hk'1 : 1 ≤ k')
    (hE0 : E 0 = c' (m - 1)) (hEs : E s = c' (k' - 1)) {i : ℕ} (hi : i < m) :
    extC m c' E (prevI k i) = c' (prevI k' i) ∧ extC m c' E i = c' i := by
  refine ⟨?_, extC_lt hi⟩
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [prevI_zero, prevI_zero]
    simp only [extC, show ¬ (k - 1 < m) by omega, if_false, show k - 1 + 1 - m = s by omega, hEs]
  · rw [prevI_pos hpos, prevI_pos hpos, extC_lt (by omega)]

/-- The block vertex `m + j` sees the edges `E j`, `E (j + 1)`. -/
theorem extC_block (hm : 1 ≤ m) (hE0 : E 0 = c' (m - 1)) {j : ℕ} :
    extC m c' E (prevI k (m + j)) = E j ∧ extC m c' E (m + j) = E (j + 1) := by
  refine ⟨?_, by simp only [extC, show ¬ (m + j < m) by omega, if_false,
    show m + j + 1 - m = j + 1 by omega]⟩
  rw [prevI_pos (by omega)]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Nat.add_zero, extC_lt (by omega), hE0]
  · simp only [extC, show ¬ (m + j - 1 < m) by omega, if_false, show m + j - 1 + 1 - m = j by omega]

/-- **Generic extension.** -/
theorem extend (hm : 1 ≤ m) (hk : k = m + s) (hs : 2 ≤ s) (hk' : m ≤ k') (hk'1 : 1 ≤ k')
    (hc' : FSol k' ty' c') (hE0 : E 0 = c' (m - 1)) (hEs : E s = c' (k' - 1))
    (hAext : ∀ i < m, ∀ a, J i = .ext a → ty' i = .ext a)
    (hApair : ∀ i j, i < m → j < m → i ≠ j → ∀ l, J i = .lab l → J j = .lab l →
      ∃ l', ty' i = .lab l' ∧ ty' j = .lab l')
    (hBprop : ∀ j < s, E j ≠ E (j + 1))
    (hBext : ∀ j < s, ∀ a, J (m + j) = .ext a → third (E j) (E (j + 1)) ≠ a)
    (hBpair : ∀ j j', j < s → j' < s → j ≠ j' → ∀ l, J (m + j) = .lab l → J (m + j') = .lab l →
      third (E j) (E (j + 1)) ≠ third (E j') (E (j' + 1)))
    (hAB : ∀ i < m, ∀ j < s, ∀ l, J i = .lab l → J (m + j) = .lab l →
      mvAt k' c' i ≠ third (E j) (E (j + 1))) :
    Solv k J := by
  obtain ⟨h1, h2, h3⟩ := hc'
  have hA := fun {i} (hi : i < m) => extC_agree (k := k) (s := s) hm hk (by omega) hk' hk'1 hE0 hEs hi
  have hmvA : ∀ i < m, mvAt k (extC m c' E) i = mvAt k' c' i := fun i hi => by
    simp only [mvAt, (hA hi).1, (hA hi).2]
  have hmvB : ∀ j, mvAt k (extC m c' E) (m + j) = third (E j) (E (j + 1)) := fun j => by
    simp only [mvAt, (extC_block (k := k) hm hE0).1, (extC_block (k := k) hm hE0).2]
  -- split positions into `A` and `B`
  have hsplit : ∀ i < k, i < m ∨ ∃ j, j < s ∧ i = m + j := fun i hi => by
    rcases Nat.lt_or_ge i m with h | h
    · exact Or.inl h
    · exact Or.inr ⟨i - m, by omega, by omega⟩
  refine ⟨extC m c' E, fun i hi => ?_, fun i hi a ha => ?_, fun i j hi hj hij l hli hlj => ?_⟩
  · rcases hsplit i hi with h | ⟨j, hj, rfl⟩
    · rw [(hA h).1, (hA h).2]; exact h1 i (by omega)
    · rw [(extC_block (k := k) hm hE0).1, (extC_block (k := k) hm hE0).2]; exact hBprop j hj
  · rcases hsplit i hi with h | ⟨j, hj, rfl⟩
    · rw [hmvA i h]; exact h2 i (by omega) a (hAext i h a ha)
    · rw [hmvB j]; exact hBext j hj a ha
  · rcases hsplit i hi with h | ⟨j₁, hj₁, rfl⟩ <;> rcases hsplit j hj with h' | ⟨j₂, hj₂, rfl⟩
    · rw [hmvA i h, hmvA j h']
      obtain ⟨l', e1, e2⟩ := hApair i j h h' hij l hli hlj
      exact h3 i j (by omega) (by omega) hij l' e1 e2
    · rw [hmvA i h, hmvB j₂]; exact hAB i h j₂ hj₂ l hli hlj
    · rw [hmvB j₁, hmvA j h']; exact (hAB j h' j₁ hj₁ l hlj hli).symm
    · rw [hmvB j₁, hmvB j₂]; exact hBpair j₁ j₂ hj₁ hj₂ (by omega) l hli hlj

end Extend

/-! ### Walks as sequences -/

theorem WalkQ.toFun {e e' : Fin 3} {ts : List (Option (Fin 3))} {Q : List (Fin 3 × Fin 3)}
    (h : WalkQ e ts Q e') : ∃ w : ℕ → Fin 3, w 0 = e ∧ w ts.length = e' ∧
      ∀ j < ts.length, okT (ts.getD j none) (w j) (w (j + 1)) := by
  induction h with
  | nil e => exact ⟨fun _ => e, rfl, rfl, fun j hj => absurd hj (by simp)⟩
  | @cons e e₁ e' t ts Q hok _ ih =>
    obtain ⟨w, hw0, hwn, hw⟩ := ih
    refine ⟨fun j => if j = 0 then e else w (j - 1), by simp, by simpa using hwn, fun j hj => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simpa [hw0] using hok
    · simp only [if_neg (show j ≠ 0 by omega), if_neg (show j + 1 ≠ 0 by omega),
        show j + 1 - 1 = j - 1 + 1 by omega]
      have := hw (j - 1) (by simp at hj; omega)
      rwa [show (t :: ts).getD j none = ts.getD (j - 1) none by
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩; simp]

theorem third_ne_of : ∀ a b x : Fin 3, a ≠ b → third a b ≠ x → x = a ∨ x = b := by decide

theorem fin3_two_vals : ∀ (a b t : Fin 3), a ≠ b → ∃ x, (x = a ∨ x = b) ∧ x ≠ t := by decide

theorem fin3_third_choice : ∀ κ t : Fin 3, ∃ δ, δ ≠ κ ∧ third κ δ ≠ t := by decide

end CoreDeg2Lib.Chord
