/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Chord.Reds

/-!
# Reductions of arcs

`red_arc`: an arc `x a₁ … a_{p−1} y` (`p ≥ 3`) closing the instance, whose inner vertices have no
partner inside the arc, is replaced by one vertex `ext a`; the outside partners of `a₁` and
`a_{p−1}` receive `ext a` (`redB`). `red_arc_remove`: when `a₁, a_{p−1}` carry different `ext`
restrictions, the arc is simply deleted.
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

theorem arc_free' {κ₁ κ₂ : Fin 3} (hκ : κ₁ ≠ κ₂) (ts : List (Option (Fin 3)))
    (hlen : 2 ≤ ts.length)
    (hbad : ¬ (ts.getD 0 none = some κ₁ ∧ ts.getD (ts.length - 1) none = some κ₂)) :
    ∃ w : ℕ → Fin 3, w 0 ≠ κ₁ ∧ w ts.length ≠ κ₂ ∧ third κ₁ (w 0) ≠ third (w ts.length) κ₂ ∧
      ∀ j < ts.length, okT (ts.getD j none) (w j) (w (j + 1)) := by
  obtain ⟨t₁, rest, rfl⟩ : ∃ t₁ rest, ts = t₁ :: rest := by
    cases ts with
    | nil => simp at hlen
    | cons a t => exact ⟨a, t, rfl⟩
  rcases List.eq_nil_or_concat rest with rfl | ⟨mid, tl, rfl⟩
  · simp at hlen
  rw [List.concat_eq_append] at *
  have hb : ¬ (t₁ = some κ₁ ∧ tl = some κ₂) := by
    intro h; apply hbad; simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right] using h
  obtain ⟨e0, Q, eL, h0, hw, hL, ht⟩ := arc_free hκ t₁ tl mid hb
  simp only [List.cons_append] at hw
  obtain ⟨w, hw0, hwn, hok⟩ := hw.toFun
  exact ⟨w, by rwa [hw0], by rwa [hwn], by rwa [hw0, hwn], hok⟩

theorem arc_remove' (κ : Fin 3) (ts : List (Option (Fin 3))) (hlen : 2 ≤ ts.length)
    {t₁ tl : Fin 3} (h1 : ts.getD 0 none = some t₁) (h2 : ts.getD (ts.length - 1) none = some tl)
    (ht : t₁ ≠ tl) :
    ∃ w : ℕ → Fin 3, w 0 ≠ κ ∧ w ts.length ≠ κ ∧ third κ (w 0) ≠ third (w ts.length) κ ∧
      ∀ j < ts.length, okT (ts.getD j none) (w j) (w (j + 1)) := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, ts = a :: rest := by
    cases ts with
    | nil => simp at hlen
    | cons a t => exact ⟨a, t, rfl⟩
  rcases List.eq_nil_or_concat rest with rfl | ⟨mid, b, rfl⟩
  · simp at hlen
  rw [List.concat_eq_append] at *
  have ha : a = some t₁ := by simpa using h1
  have hb : b = some tl := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right] using h2
  subst ha; subst hb
  obtain ⟨e0, Q, eL, h0, hw, hL, hth⟩ := arc_remove κ ht mid
  simp only [List.cons_append] at hw
  obtain ⟨w, hw0, hwn, hok⟩ := hw.toFun
  exact ⟨w, by rwa [hw0], by rwa [hwn], by rwa [hw0, hwn], hok⟩

open Classical in
/-- The reduced instance for an arc. -/
noncomputable def redB (k p : ℕ) (J : ℕ → VT) (a : Fin 3) : ℕ → VT := fun i =>
  if i < k - 1 - p then
    (if (∃ l', J (k - p) = .lab l' ∧ J i = .lab l') ∨ (∃ l', J (k - 2) = .lab l' ∧ J i = .lab l')
      then .ext a else J i)
  else .ext a

/-- Common part of the two arc reductions: colouring the block from a walk. -/
theorem arc_extend {k p m k' : ℕ} {J ty' : ℕ → VT} {c' : ℕ → Fin 3} (hp : 3 ≤ p)
    (hm : m = k - 1 - p) (hpk : p + 3 ≤ k) (hk' : m ≤ k') (hk'1 : 1 ≤ k') (hwf : WFf k J)
    {l : ℕ} (hx : J (k - 1 - p) = .lab l) (hy : J (k - 1) = .lab l)
    (hinner : ∀ j j', 1 ≤ j → j < j' → j' ≤ p - 1 → ¬ Partner k J (k - 1 - p + j) (k - 1 - p + j'))
    (hc' : FSol k' ty' c')
    (hAext : ∀ i < m, ∀ a, J i = .ext a → ty' i = .ext a)
    (hApair : ∀ i j, i < m → j < m → i ≠ j → ∀ l, J i = .lab l → J j = .lab l →
      ∃ l', ty' i = .lab l' ∧ ty' j = .lab l')
    {κ₁ κ₂ : Fin 3} (hκ₁ : κ₁ = c' (m - 1)) (hκ₂ : κ₂ = c' (k' - 1))
    (w : ℕ → Fin 3) (hw0 : w 0 ≠ κ₁) (hwn : w (p - 1) ≠ κ₂)
    (hwt : third κ₁ (w 0) ≠ third (w (p - 1)) κ₂)
    (hok : ∀ j, 1 ≤ j → j ≤ p - 1 → okT (pval m k' J c' (m + j)) (w (j - 1)) (w j)) :
    Solv k J := by
  have hm1 : 1 ≤ m := by omega
  have hno : ∀ i, i < k → i ≠ m → i ≠ k - 1 → J i ≠ .lab l := fun i hi h1 h2 hil =>
    hwf i m (k - 1) ⟨hi, by omega, h1, l, hil, by rw [hm]; exact hx⟩
      ⟨by omega, by omega, by omega, l, by rw [hm]; exact hx, hy⟩ h2
  let E : ℕ → Fin 3 := fun j => if j = 0 then κ₁ else if j ≤ p then w (j - 1) else κ₂
  have hE0 : E 0 = κ₁ := by simp [E]
  have hEj : ∀ j, 1 ≤ j → j ≤ p → E j = w (j - 1) := fun j h1 h2 => by
    simp [E, show j ≠ 0 by omega, h2]
  have hEp1 : E (p + 1) = κ₂ := by simp [E]
  have hokj : ∀ j, 1 ≤ j → j ≤ p - 1 → okT (pval m k' J c' (m + j)) (E j) (E (j + 1)) :=
    fun j h1 h2 => by
      rw [hEj j h1 (by omega), hEj (j + 1) (by omega) (by omega),
        show j + 1 - 1 = j by omega]
      exact hok j h1 h2
  have hxm : J (m + 0) = .lab l := by rw [hm]; simpa using hx
  have hyp : J (m + p) = .lab l := by rw [show m + p = k - 1 by omega]; exact hy
  have hin : ∀ j, j < p + 1 → j ≠ 0 → j ≠ p → J (m + j) ≠ .lab l := fun j hj h1 h2 hjl =>
    hno (m + j) (by omega) (by omega) (by omega) hjl
  refine extend (s := p + 1) (k' := k') (E := E) hm1 (by omega) (by omega) hk' hk'1 hc'
    (by rw [hE0, hκ₁]) (by rw [hEp1, hκ₂]) hAext hApair (fun j hj => ?_)
    (fun j hj b hb => ?_) (fun j j' hj hj' hjj l' hl hl' => ?_) (fun i hi j hj l' hil hjl => ?_)
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hE0, hEj 1 le_rfl (by omega)]; exact hw0.symm
    · by_cases hjp : j = p
      · subst hjp
        rw [hEj j hj0 le_rfl, hEp1]; exact hwn
      · exact (hokj j hj0 (by omega)).1
  · have hj0 : j ≠ 0 := by rintro rfl; rw [hxm] at hb; cases hb
    have hjp : j ≠ p := by rintro rfl; rw [hyp] at hb; cases hb
    exact (hokj j (by omega) (by omega)).2 b (pval_ext hb)
  · by_cases h0 : j = 0 <;> by_cases h0' : j' = 0 <;> by_cases hp1 : j = p <;>
      by_cases hp2 : j' = p
    all_goals first
      | omega
      | (subst h0; subst hp2
         rw [hE0, hEj 1 le_rfl (by omega), hEj j' (by omega) le_rfl, hEp1]; exact hwt)
      | (subst h0'; subst hp1
         rw [hE0, hEj 1 le_rfl (by omega), hEj j (by omega) le_rfl, hEp1]; exact hwt.symm)
      | (subst h0; rw [hxm] at hl; cases hl; exact absurd hl' (hin j' hj' h0' hp2))
      | (subst h0'; rw [hxm] at hl'; cases hl'; exact absurd hl (hin j hj h0 hp1))
      | (subst hp1; rw [hyp] at hl; cases hl; exact absurd hl' (hin j' hj' h0' hp2))
      | (subst hp2; rw [hyp] at hl'; cases hl'; exact absurd hl (hin j hj h0 hp1))
      | (exfalso
         rcases Nat.lt_or_gt_of_ne hjj with h | h
         · exact hinner j j' (by omega) h (by omega)
             ⟨by omega, by omega, by omega, l', by rw [← hm]; exact hl, by rw [← hm]; exact hl'⟩
         · exact hinner j' j (by omega) h (by omega)
             ⟨by omega, by omega, by omega, l', by rw [← hm]; exact hl', by rw [← hm]; exact hl⟩)
  · have hj0 : j ≠ 0 := by
      rintro rfl; rw [hxm] at hjl; cases hjl
      exact hno i (by omega) (by omega) (by omega) hil
    have hjp : j ≠ p := by
      rintro rfl; rw [hyp] at hjl; cases hjl
      exact hno i (by omega) (by omega) (by omega) hil
    exact sat_AB_of_pval hwf (by omega) (by omega) (by omega)
      (fun y hy => (hokj j (by omega) (by omega)).2 y hy) i hi l' hil hjl

/-- **The arc reduction.** -/
theorem red_arc {k p : ℕ} {J : ℕ → VT} (hp : 3 ≤ p) (hpk : p + 3 ≤ k) (hwf : WFf k J) {l : ℕ}
    (hx : J (k - 1 - p) = .lab l) (hy : J (k - 1) = .lab l)
    (hinner : ∀ j j', 1 ≤ j → j < j' → j' ≤ p - 1 → ¬ Partner k J (k - 1 - p + j) (k - 1 - p + j'))
    (a : Fin 3) (haf : ∀ b, J (k - p) = .ext b → b ≠ a) (hag : ∀ b, J (k - 2) = .ext b → b ≠ a)
    (hs : Solv (k - p) (redB k p J a)) : Solv k J := by
  classical
  obtain ⟨c', hc'⟩ := hs
  set m := k - 1 - p with hm
  have hprop := hc'.1 m (by omega)
  rw [prevI_pos (by omega)] at hprop
  have hredm : redB k p J a m = .ext a := by simp [redB, hm]
  have hextm : third (c' (m - 1)) (c' m) ≠ a := by
    have := hc'.2.1 m (by omega) a hredm
    rwa [mvAt, prevI_pos (by omega)] at this
  have haκ := f3_mem _ _ a hprop hextm
  let tv : ℕ → Option (Fin 3) := fun j => pval m (k - p) J c' (m + j)
  let ts : List (Option (Fin 3)) := (List.range (p - 1)).map fun j => tv (j + 1)
  have hts_len : ts.length = p - 1 := by simp [ts]
  have hts_get : ∀ j < p - 1, ts.getD j none = tv (j + 1) := fun j hj => by
    simp [ts, List.getD_eq_getElem?_getD, hj]
  -- the restrictions of the inner ends avoid `a`
  have hport : ∀ j, (j = 1 ∨ j = p - 1) → ∀ y, tv j = some y → y ≠ a := by
    intro j hj y hy
    cases hJ : J (m + j) with
    | ext b =>
      rw [show tv j = some b from pval_ext hJ] at hy
      have hby : b = y := Option.some_injective _ hy
      subst hby
      rcases hj with rfl | rfl
      · exact haf b (by rw [show k - p = m + 1 by omega]; exact hJ)
      · exact hag b (by rw [show k - 2 = m + (p - 1) by omega]; exact hJ)
    | lab l' =>
      by_cases hex : ∃ i, i < m ∧ J i = .lab l'
      · obtain ⟨i, hi, hil⟩ := hex
        rw [show tv j = some (mvAt (k - p) c' i) from pval_lab hJ hi hil
          (uniq_of_wf hwf (by omega) (by omega) (by omega) hJ hi hil)] at hy
        cases hy
        have hred : redB k p J a i = .ext a := by
          simp only [redB, if_pos (show i < k - 1 - p by omega)]
          rw [if_pos]
          rcases hj with rfl | rfl
          · exact Or.inl ⟨l', by rw [show k - p = m + 1 by omega]; exact hJ, hil⟩
          · exact Or.inr ⟨l', by rw [show k - 2 = m + (p - 1) by omega]; exact hJ, hil⟩
        exact hc'.2.1 i (by omega) a hred
      · push Not at hex
        rw [show tv j = none from pval_free hJ fun i hi => hex i hi] at hy
        cases hy
  have hbad : ¬ (ts.getD 0 none = some (c' (m - 1)) ∧
      ts.getD (ts.length - 1) none = some (c' m)) := by
    rintro ⟨h1, h2⟩
    rw [hts_get 0 (by omega)] at h1
    rw [hts_len, hts_get _ (by omega), show p - 1 - 1 + 1 = p - 1 by omega] at h2
    rcases haκ with h | h
    · exact hport 1 (Or.inl rfl) _ h1 h.symm
    · exact hport (p - 1) (Or.inr rfl) _ h2 h.symm
  obtain ⟨w, hw0, hwn, hwt, hok⟩ := arc_free' hprop ts (by omega) hbad
  simp only [hts_len] at hwn hwt hok
  -- ports of the reduced instance
  have hnp : ∀ i l', i < m → J i = .lab l' → (∃ j, j < m ∧ j ≠ i ∧ J j = .lab l') →
      redB k p J a i = J i := by
    intro i l' hi hil ⟨j, hj, hji, hjl⟩
    simp only [redB, if_pos (show i < k - 1 - p by omega)]
    rw [if_neg]
    rintro (⟨l'', h1, h2⟩ | ⟨l'', h1, h2⟩) <;> rw [hil] at h2 <;> cases h2
    · exact hwf j i (k - p) ⟨by omega, by omega, hji, l', hjl, hil⟩
        ⟨by omega, by omega, by omega, l', hil, h1⟩ (by omega)
    · exact hwf j i (k - 2) ⟨by omega, by omega, hji, l', hjl, hil⟩
        ⟨by omega, by omega, by omega, l', hil, h1⟩ (by omega)
  refine arc_extend hp hm hpk (k' := m + 1) (by omega) (by omega) hwf hx hy hinner
    (by rwa [show m + 1 = k - p by omega]) (fun i hi b hb => ?_)
    (fun i j hi hj hij l' hil hjl => ⟨l', ?_, ?_⟩) rfl rfl w hw0 hwn hwt (fun j h1 h2 => ?_)
  · simp only [redB, if_pos (show i < k - 1 - p by omega)]
    rw [if_neg]
    · exact hb
    · rintro (⟨l', _, h⟩ | ⟨l', _, h⟩) <;> rw [hb] at h <;> cases h
  · rw [hnp i l' hi hil ⟨j, hj, Ne.symm hij, hjl⟩]; exact hil
  · rw [hnp j l' hj hjl ⟨i, hi, hij, hil⟩]; exact hjl
  · have := hok (j - 1) (by omega)
    rw [hts_get (j - 1) (by omega), show j - 1 + 1 = j by omega] at this
    simpa only [tv, show k - p = m + 1 by omega] using this

/-- **Removal of an arc** whose inner ends carry different `ext` restrictions. -/
theorem red_arc_remove {k p : ℕ} {J : ℕ → VT} (hp : 3 ≤ p) (hpk : p + 3 ≤ k) (hwf : WFf k J)
    {l : ℕ} (hx : J (k - 1 - p) = .lab l) (hy : J (k - 1) = .lab l)
    (hinner : ∀ j j', 1 ≤ j → j < j' → j' ≤ p - 1 → ¬ Partner k J (k - 1 - p + j) (k - 1 - p + j'))
    {b₁ b₂ : Fin 3} (hb₁ : J (k - p) = .ext b₁) (hb₂ : J (k - 2) = .ext b₂) (hb : b₁ ≠ b₂)
    (hs : Solv (k - 1 - p) J) : Solv k J := by
  classical
  obtain ⟨c', hc'⟩ := hs
  set m := k - 1 - p with hm
  let tv : ℕ → Option (Fin 3) := fun j => pval m m J c' (m + j)
  let ts : List (Option (Fin 3)) := (List.range (p - 1)).map fun j => tv (j + 1)
  have hts_len : ts.length = p - 1 := by simp [ts]
  have hts_get : ∀ j < p - 1, ts.getD j none = tv (j + 1) := fun j hj => by
    simp [ts, List.getD_eq_getElem?_getD, hj]
  have h1 : ts.getD 0 none = some b₁ := by
    rw [hts_get 0 (by omega)]
    exact pval_ext (by rw [show m + (0 + 1) = k - p by omega]; exact hb₁)
  have h2 : ts.getD (ts.length - 1) none = some b₂ := by
    rw [hts_len, hts_get _ (by omega)]
    exact pval_ext (by rw [show m + (p - 1 - 1 + 1) = k - 2 by omega]; exact hb₂)
  obtain ⟨w, hw0, hwn, hwt, hok⟩ := arc_remove' (c' (m - 1)) ts (by omega) h1 h2 hb
  simp only [hts_len] at hwn hwt hok
  refine arc_extend hp hm hpk (k' := m) le_rfl (by omega) hwf hx hy hinner hc'
    (fun i hi b hb => hb) (fun i j hi hj hij l' hil hjl => ⟨l', hil, hjl⟩) rfl rfl w hw0 hwn hwt
    (fun j h1 h2 => ?_)
  have := hok (j - 1) (by omega)
  rw [hts_get (j - 1) (by omega), show j - 1 + 1 = j by omega] at this
  exact this

end CoreDeg2Lib.Chord
