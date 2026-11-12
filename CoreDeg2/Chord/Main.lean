/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Chord.ArcRed

/-!
# The chorded-cycle lemma

**Theorem** (`solv_main`). A well-formed instance of length `k ≥ 2` is solvable unless it is
exceptional: (E1) no labels, odd length, all restrictions equal; (E2) the hexagon with three
antipodal chords; (E3) length two with a chord.

Proof by strong induction on `k`. Without chords: `solv_chordless`. Otherwise rotate so that a
chord of minimal cyclic length `p` closes the instance (positions `k − 1 − p` and `k − 1`); then
* `p = 1`: `red_adj`; `p = 2`: `red_dist2`;
* `p ≥ 3`: `red_arc`, with the colour `a` chosen so that the reduced instance is not of type E1,
  or `red_arc_remove` in the one parity case where no colour works.
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

/-- A chord of length `p` closes the instance. -/
def ChordAt (k : ℕ) (J : ℕ → VT) (p : ℕ) : Prop := 1 ≤ p ∧ p < k ∧ Partner k J (k - 1 - p) (k - 1)

theorem mod_add_self' {x k : ℕ} (hx : x < k) : (x + k) % k = x := by
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hx]

/-- A chord `a < b` in a rotation gives a closing chord of length `b − a` in another rotation. -/
theorem chordAt_of_partner {k r : ℕ} {ty : ℕ → VT} {a b : ℕ}
    (h : Partner k (rot k r ty) a b) (hab : a < b) : ChordAt k (rot k (b + 1 + r) ty) (b - a) := by
  obtain ⟨ha, hb, -, l, h1, h2⟩ := h
  refine ⟨by omega, by omega, by omega, by omega, by omega, l, ?_, ?_⟩
  · simp only [rot] at h1 ⊢
    rw [show k - 1 - (b - a) + (b + 1 + r) = (a + r) + k by omega, Nat.add_mod_right]; exact h1
  · simp only [rot] at h2 ⊢
    rw [show k - 1 + (b + 1 + r) = (b + r) + k by omega, Nat.add_mod_right]; exact h2

theorem chordAt_of_partner' {k r : ℕ} {ty : ℕ → VT} {a b : ℕ}
    (h : Partner k (rot k r ty) a b) (hab : a < b) :
    ChordAt k (rot k (a + 1 + r) ty) (k - (b - a)) := by
  obtain ⟨ha, hb, -, l, h1, h2⟩ := h
  refine ⟨by omega, by omega, by omega, by omega, by omega, l, ?_, ?_⟩
  · simp only [rot] at h2 ⊢
    rw [show k - 1 - (k - (b - a)) + (a + 1 + r) = b + r by omega]; exact h2
  · simp only [rot] at h1 ⊢
    rw [show k - 1 + (a + 1 + r) = (a + r) + k by omega, Nat.add_mod_right]; exact h1

theorem hex_all {k : ℕ} {ty : ℕ → VT} (h : HexF k ty) : ∀ i < 6, Partner k ty i ((i + 3) % 6) := by
  obtain ⟨rfl, h⟩ := h
  intro i hi
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · rw [Nat.mod_eq_of_lt (by omega)]; exact h i h3
  · have := (h (i - 3) (by omega)).symm
    rw [show (i + 3) % 6 = i - 3 by omega]
    rwa [show i - 3 + 3 = i by omega] at this

theorem hex_of_rot {k r : ℕ} {ty : ℕ → VT} (h : HexF k (rot k r ty)) : HexF k ty := by
  have hk := h.1
  refine ⟨hk, fun i' hi' => ?_⟩
  subst hk
  set i := (i' + 6 - r % 6) % 6
  have := partner_rot (hex_all h i (by omega))
  rwa [show (i + r) % 6 = i' by omega, show ((i + 3) % 6 + r) % 6 = i' + 3 by omega] at this

theorem hex_partner {k : ℕ} {ty : ℕ → VT} (h : HexF k ty) {i : ℕ} (hi : i < k) :
    ∃ j, Partner k ty i j := by
  have hk := h.1; subst hk
  exact ⟨_, hex_all h i hi⟩

/-- Well-formedness passes to instances whose labels sit at the same positions. -/
theorem wf_of_labels {k k' : ℕ} {J ty' : ℕ → VT} (hk : k' ≤ k) (hwf : WFf k J)
    (h : ∀ i < k', ∀ l, ty' i = .lab l → J i = .lab l) : WFf k' ty' := by
  intro i j m ⟨hi, hj, hij, l, h1, h2⟩ ⟨_, hm, hjm, l', h3, h4⟩ him
  rw [h2] at h3; cases h3
  exact hwf i j m ⟨by omega, by omega, hij, l, h i hi l h1, h j hj l h2⟩
    ⟨by omega, by omega, hjm, l, h j hj l h2, h m hm l h4⟩ him

theorem exists_avoid3 : ∀ x y z : Fin 3, x = y → ∃ a, a ≠ x ∧ a ≠ y ∧ a ≠ z := by decide

theorem exists_avoid2 : ∀ x y : Fin 3, ∃ a, a ≠ x ∧ a ≠ y := by decide

/-- **The chorded-cycle lemma.** -/
theorem solv_main : ∀ (k : ℕ) (ty : ℕ → VT), 2 ≤ k → WFf k ty → ¬ E1F k ty → ¬ HexF k ty →
    ¬ (k = 2 ∧ HasChordF k ty) → Solv k ty := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ty hk hwf hE1 hhex hE3
  classical
  by_cases hch : HasChordF k ty
  swap
  · exact solv_chordless hk hch hE1
  -- a closing chord of minimal length in some rotation
  have hex : ∃ p, ∃ r, ChordAt k (rot k r ty) p := by
    obtain ⟨i, j, hij⟩ := hch
    obtain ⟨hi, hj, hne, l, h1, h2⟩ := hij
    have h0 : ∀ x, x < k → rot k 0 ty x = ty x := fun x hx => by
      simp [rot, Nat.mod_eq_of_lt hx]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨_, _, chordAt_of_partner (r := 0)
        ⟨hi, hj, hne, l, by rw [h0 i hi]; exact h1, by rw [h0 j hj]; exact h2⟩ h⟩
    · exact ⟨_, _, chordAt_of_partner (r := 0)
        ⟨hj, hi, hne.symm, l, by rw [h0 j hj]; exact h2, by rw [h0 i hi]; exact h1⟩ h⟩
  have hfind := Nat.find_spec hex
  have hmin0 : ∀ q, (∃ r, ChordAt k (rot k r ty) q) → Nat.find hex ≤ q :=
    fun q hq => Nat.find_min' hex hq
  generalize Nat.find hex = p at hfind hmin0
  obtain ⟨r, hr⟩ := hfind
  have hmin : ∀ r' a b, Partner k (rot k r' ty) a b → a < b → p ≤ b - a ∧ p ≤ k - (b - a) :=
    fun r' a b h hab => ⟨hmin0 _ ⟨_, chordAt_of_partner h hab⟩,
      hmin0 _ ⟨_, chordAt_of_partner' h hab⟩⟩
  have hwfJ : WFf k (rot k r ty) := wf_rot hwf
  obtain ⟨hp1, hpk, hxy⟩ := hr
  obtain ⟨l, hx, hy⟩ := hxy.2.2.2
  have h2p : p ≤ k - p := by
    have := (hmin r (k - 1 - p) (k - 1) hxy (by omega)).2
    rwa [show k - 1 - (k - 1 - p) = p by omega] at this
  apply solv_of_rot (r := r) (by omega)
  generalize hJ : rot k r ty = J at hwfJ hxy hx hy ⊢
  have hminJ : ∀ a b, Partner k J a b → a < b → p ≤ b - a ∧ p ≤ k - (b - a) :=
    fun a b h hab => hmin r a b (by rw [hJ]; exact h) hab
  -- the three cases
  rcases Nat.lt_or_ge p 3 with hp3 | hp3
  · interval_cases p
    · -- `p = 1`
      have hk3 : 3 ≤ k := by
        by_contra h
        exact hE3 ⟨by omega, ⟨_, _, partner_rot (r := r) (by rw [hJ]; exact hxy)⟩⟩
      rw [show k - 1 - 1 = k - 2 by omega] at hx
      refine red_adj hk3 hwfJ hx hy (ih (k - 1) (by omega) _ (by omega) ?_ ?_ ?_ ?_)
      · refine wf_of_labels (by omega) hwfJ fun i hi l' h => ?_
        by_cases hi2 : i < k - 2
        · simpa [hi2] using h
        · simp only [hi2, if_false] at h; cases h; rwa [show i = k - 2 by omega]
      · rintro ⟨h1, -, -⟩
        exact h1 (k - 2) (by omega) l (by simp)
      · intro hh
        obtain ⟨j, hj⟩ := hex_partner hh (show k - 2 < k - 1 by omega)
        obtain ⟨-, hj1, hne, l', h1, h2⟩ := hj
        simp only [show ¬ (k - 2 < k - 2) by omega, if_false] at h1
        cases h1
        have hj2 : j < k - 2 := by omega
        simp only [hj2, if_true] at h2
        exact hwfJ j (k - 2) (k - 1) ⟨by omega, by omega, by omega, l, h2, hx⟩
          ⟨by omega, by omega, by omega, l, hx, hy⟩ (by omega)
      · rintro ⟨hk2, i, j, hi, hj, hij, l', h1, h2⟩
        have : i = 0 ∨ j = 0 := by omega
        rcases this with rfl | rfl
        · simp only [show (0 : ℕ) < k - 2 by omega, if_true] at h1
          simp only [show ¬ (j < k - 2) by omega, if_false] at h2
          cases h2
          exact hwfJ 0 (k - 2) (k - 1) ⟨by omega, by omega, by omega, l, h1, hx⟩
            ⟨by omega, by omega, by omega, l, hx, hy⟩ (by omega)
        · simp only [show (0 : ℕ) < k - 2 by omega, if_true] at h2
          simp only [show ¬ (i < k - 2) by omega, if_false] at h1
          cases h1
          exact hwfJ 0 (k - 2) (k - 1) ⟨by omega, by omega, by omega, l, h2, hx⟩
            ⟨by omega, by omega, by omega, l, hx, hy⟩ (by omega)
    · -- `p = 2`
      rw [show k - 1 - 2 = k - 3 by omega] at hx
      refine red_dist2 (by omega) hwfJ hx hy (ih (k - 2) (by omega) _ (by omega) ?_ ?_ ?_ ?_)
      · refine wf_of_labels (by omega) hwfJ fun i hi l' h => ?_
        by_cases hi3 : i < k - 3
        · simpa [hi3] using h
        · simp only [hi3, if_false] at h; cases h; rwa [show i = k - 3 by omega]
      · rintro ⟨h1, -, -⟩
        exact h1 (k - 3) (by omega) l (by simp)
      · intro hh
        obtain ⟨j, hj⟩ := hex_partner hh (show k - 3 < k - 2 by omega)
        obtain ⟨-, hj1, hne, l', h1, h2⟩ := hj
        simp only [show ¬ (k - 3 < k - 3) by omega, if_false] at h1
        cases h1
        have hj2 : j < k - 3 := by omega
        simp only [hj2, if_true] at h2
        exact hwfJ j (k - 3) (k - 1) ⟨by omega, by omega, by omega, l, h2, hx⟩
          ⟨by omega, by omega, by omega, l, hx, hy⟩ (by omega)
      · rintro ⟨hk2, i, j, hi, hj, hij, l', h1, h2⟩
        have : i = 0 ∨ j = 0 := by omega
        rcases this with rfl | rfl
        · simp only [show (0 : ℕ) < k - 3 by omega, if_true] at h1
          simp only [show ¬ (j < k - 3) by omega, if_false] at h2
          cases h2
          exact hwfJ 0 (k - 3) (k - 1) ⟨by omega, by omega, by omega, l, h1, hx⟩
            ⟨by omega, by omega, by omega, l, hx, hy⟩ (by omega)
        · simp only [show (0 : ℕ) < k - 3 by omega, if_true] at h2
          simp only [show ¬ (i < k - 3) by omega, if_false] at h1
          cases h1
          exact hwfJ 0 (k - 3) (k - 1) ⟨by omega, by omega, by omega, l, h2, hx⟩
            ⟨by omega, by omega, by omega, l, hx, hy⟩ (by omega)
  · -- `p ≥ 3`: arcs
    obtain ⟨m, hm⟩ : ∃ m, m = k - 1 - p := ⟨_, rfl⟩
    have hm2 : 2 ≤ m := by omega
    have hinner : ∀ j j', 1 ≤ j → j < j' → j' ≤ p - 1 →
        ¬ Partner k J (k - 1 - p + j) (k - 1 - p + j') := fun j j' h1 h2 h3 hpar => by
      have := (hminJ _ _ hpar (by omega)).1
      omega
    -- ports: outside partners of the inner ends
    let port : ℕ → Prop := fun u =>
      (∃ l', J (k - p) = .lab l' ∧ J u = .lab l') ∨ (∃ l', J (k - 2) = .lab l' ∧ J u = .lab l')
    -- a vertex outside the arc which is not a port
    have hu : ∃ u, u < m ∧ ¬ port u := by
      by_contra hall
      push Not at hall
      -- two ports at positions `0, 1` of the same inner end would be three equal labels
      have key : ∀ u v, u < m → v < m → u ≠ v → ∀ q, (q = k - p ∨ q = k - 2) →
          (∃ l', J q = .lab l' ∧ J u = .lab l') → (∃ l', J q = .lab l' ∧ J v = .lab l') → False := by
        intro u v hu hv huv q hq ⟨l₁, h1, h2⟩ ⟨l₂, h3, h4⟩
        rw [h1] at h3; cases h3
        exact hwfJ u q v ⟨by omega, by omega, by omega, l₁, h2, h1⟩
          ⟨by omega, by omega, by omega, l₁, h1, h4⟩ huv
      rcases Nat.lt_or_ge 2 m with hm3 | hm3
      · rcases hall 0 (by omega) with h0 | h0 <;> rcases hall 1 (by omega) with h1 | h1 <;>
          rcases hall 2 (by omega) with h2 | h2
        all_goals first
          | exact key 0 1 (by omega) (by omega) (by omega) _ (Or.inl rfl) h0 h1
          | exact key 0 1 (by omega) (by omega) (by omega) _ (Or.inr rfl) h0 h1
          | exact key 0 2 (by omega) (by omega) (by omega) _ (Or.inl rfl) h0 h2
          | exact key 0 2 (by omega) (by omega) (by omega) _ (Or.inr rfl) h0 h2
          | exact key 1 2 (by omega) (by omega) (by omega) _ (Or.inl rfl) h1 h2
          | exact key 1 2 (by omega) (by omega) (by omega) _ (Or.inr rfl) h1 h2
      · -- `m = 2`, `k = 6`, `p = 3`: the hexagon
        have hm2' : m = 2 := by omega
        have hp3' : p = 3 := by omega
        have hk6 : k = 6 := by omega
        apply hhex
        apply hex_of_rot (r := r)
        rw [hJ]
        refine ⟨hk6, fun i hi => ?_⟩
        subst hk6; subst hp3'
        -- position 1 cannot be the partner of position 3 (a chord of length 2)
        have h13 : ¬ (∃ l', J 3 = .lab l' ∧ J 1 = .lab l') := by
          rintro ⟨l', h1, h2⟩
          have := (hminJ 1 3 ⟨by omega, by omega, by omega, l', h2, h1⟩ (by omega)).1
          omega
        have h0 := hall 0 (by omega)
        have h1 := hall 1 (by omega)
        simp only [port, show 6 - 3 = 3 by rfl, show 6 - 2 = 4 by rfl] at h0 h1
        rcases h1 with h1 | ⟨l₁, h1a, h1b⟩
        · exact absurd h1 h13
        rcases h0 with ⟨l₀, h0a, h0b⟩ | h0
        · interval_cases i
          · exact ⟨by omega, by omega, by omega, l₀, h0b, h0a⟩
          · exact ⟨by omega, by omega, by omega, l₁, h1b, h1a⟩
          · exact ⟨by omega, by omega, by omega, l, hx, hy⟩
        · exfalso
          exact key 0 1 (by omega) (by omega) (by omega) 4 (Or.inr rfl) h0 ⟨l₁, h1a, h1b⟩
    obtain ⟨u, hum, hup⟩ := hu
    -- the case of two inner ends with different `ext` restrictions
    by_cases hEEd : ∃ b₁ b₂, J (k - p) = .ext b₁ ∧ J (k - 2) = .ext b₂ ∧ b₁ ≠ b₂
    · obtain ⟨b₁, b₂, hb₁, hb₂, hb⟩ := hEEd
      by_cases hpar : (∀ i < m, J i = .ext (third b₁ b₂)) ∧ (m + 1) % 2 = 1
      · -- delete the arc
        refine red_arc_remove hp3 (by omega) hwfJ hx hy hinner hb₁ hb₂ hb
          (ih (k - 1 - p) (by omega) J (by omega) (wf_of_labels (by omega) hwfJ fun i _ l' h => h) ?_ ?_ ?_)
        · rintro ⟨-, h, -⟩; omega
        · intro hh
          obtain ⟨j, -, -, -, l', h1, -⟩ := hex_partner hh (show 0 < k - 1 - p by omega)
          rw [hpar.1 0 (by omega)] at h1; cases h1
        · rintro ⟨-, i, j, hi, -, -, l', h1, -⟩
          rw [hpar.1 i (by omega)] at h1; cases h1
      · -- replace the arc by `ext (third b₁ b₂)`
        refine red_arc hp3 (by omega) hwfJ hx hy hinner (third b₁ b₂)
          (fun b h => by rw [hb₁] at h; cases h; exact (third_ne_left b₁ b₂ hb).symm)
          (fun b h => by rw [hb₂] at h; cases h; exact (third_ne_right b₁ b₂ hb).symm)
          (ih (k - p) (by omega) _ (by omega) ?_ ?_ ?_ ?_)
        · refine wf_of_labels (by omega) hwfJ fun i hi l' h => ?_
          simp only [redB] at h
          split_ifs at h <;> first | cases h | exact h
        · rintro ⟨h1, h2, h3⟩
          apply hpar
          refine ⟨fun i hi => ?_, by omega⟩
          have hi3 := h3 i (by omega)
          have hm3 := h3 m (by omega)
          have hredm : redB k p J (third b₁ b₂) m = .ext (third b₁ b₂) := by simp [redB, hm]
          rw [hredm] at hm3
          -- no ports here (the inner ends are `ext`)
          have hnp : ¬ ((∃ l', J (k - p) = .lab l' ∧ J i = .lab l') ∨
              (∃ l', J (k - 2) = .lab l' ∧ J i = .lab l')) := by
            rintro (⟨l', h, -⟩ | ⟨l', h, -⟩)
            · rw [hb₁] at h; cases h
            · rw [hb₂] at h; cases h
          have hri : redB k p J (third b₁ b₂) i = J i := by
            simp only [redB, if_pos (show i < k - 1 - p by omega), if_neg hnp]
          rw [hri, ← hm3] at hi3
          exact hi3
        · intro hh
          obtain ⟨j, -, -, -, l', h1, -⟩ := hex_partner hh (show m < k - p by omega)
          simp [redB, hm] at h1
        · rintro ⟨h2, -⟩; omega
    · -- choose `a` avoiding the `ext` restrictions of the inner ends and of `u`
      have ha : ∃ a, (∀ b, J (k - p) = .ext b → b ≠ a) ∧ (∀ b, J (k - 2) = .ext b → b ≠ a) ∧
          (∀ b, J u = .ext b → b ≠ a) := by
        push Not at hEEd
        cases hf : J (k - p) with
        | ext b₁ =>
          cases hg : J (k - 2) with
          | ext b₂ =>
            have hbb := hEEd b₁ b₂ hf hg
            cases hJu : J u with
            | ext bu =>
              obtain ⟨a, h1, h2, h3⟩ := exists_avoid3 b₁ b₂ bu hbb
              exact ⟨a, fun b h => (by cases h; exact h1.symm), fun b h => (by cases h; exact h2.symm),
                fun b h => (by cases h; exact h3.symm)⟩
            | lab _ =>
              obtain ⟨a, h1, h2⟩ := exists_avoid2 b₁ b₂
              exact ⟨a, fun b h => (by cases h; exact h1.symm), fun b h => (by cases h; exact h2.symm),
                fun b h => (by cases h)⟩
          | lab _ =>
            cases hJu : J u with
            | ext bu =>
              obtain ⟨a, h1, h2⟩ := exists_avoid2 b₁ bu
              exact ⟨a, fun b h => (by cases h; exact h1.symm), fun b h => (by cases h),
                fun b h => (by cases h; exact h2.symm)⟩
            | lab _ =>
              obtain ⟨a, h1, -⟩ := exists_avoid2 b₁ b₁
              exact ⟨a, fun b h => (by cases h; exact h1.symm), fun b h => (by cases h),
                fun b h => (by cases h)⟩
        | lab _ =>
          cases hg : J (k - 2) with
          | ext b₂ =>
            cases hJu : J u with
            | ext bu =>
              obtain ⟨a, h1, h2⟩ := exists_avoid2 b₂ bu
              exact ⟨a, fun b h => (by cases h), fun b h => (by cases h; exact h1.symm),
                fun b h => (by cases h; exact h2.symm)⟩
            | lab _ =>
              obtain ⟨a, h1, -⟩ := exists_avoid2 b₂ b₂
              exact ⟨a, fun b h => (by cases h), fun b h => (by cases h; exact h1.symm),
                fun b h => (by cases h)⟩
          | lab _ =>
            cases hJu : J u with
            | ext bu =>
              obtain ⟨a, h1, -⟩ := exists_avoid2 bu bu
              exact ⟨a, fun b h => (by cases h), fun b h => (by cases h),
                fun b h => (by cases h; exact h1.symm)⟩
            | lab _ => exact ⟨0, fun b h => (by cases h), fun b h => (by cases h), fun b h => (by cases h)⟩
      obtain ⟨a, haf, hag, hau⟩ := ha
      have hredu : redB k p J a u = J u := by
        simp only [redB, if_pos (show u < k - 1 - p by omega)]
        rw [if_neg hup]
      refine red_arc hp3 (by omega) hwfJ hx hy hinner a haf hag
        (ih (k - p) (by omega) _ (by omega) ?_ ?_ ?_ ?_)
      · refine wf_of_labels (by omega) hwfJ fun i hi l' h => ?_
        simp only [redB] at h
        split_ifs at h <;> first | cases h | exact h
      · rintro ⟨h1, h2, h3⟩
        have hu3 := h3 u (by omega)
        have hm3 := h3 m (by omega)
        have hredm : redB k p J a m = .ext a := by simp [redB, hm]
        rw [hredm] at hm3
        rw [hredu, ← hm3] at hu3
        exact hau a hu3 rfl
      · intro hh
        obtain ⟨j, -, -, -, l', h1, -⟩ := hex_partner hh (show m < k - p by omega)
        simp [redB, hm] at h1
      · rintro ⟨h2, -⟩; omega

end CoreDeg2Lib.Chord
