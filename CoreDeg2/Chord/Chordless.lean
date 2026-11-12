/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Chord.Index

/-!
# Instances without chords

An instance in which no label is repeated is solvable unless it is *exceptional of type E1*: odd
length, no labels at all, and all restrictions equal (`chordless_solvable`).
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

/-- Exceptional instances without chords: odd, all `ext` with the same colour. -/
def E1 (I : List VT) : Prop := (∀ l, VT.lab l ∉ I) ∧ I.length % 2 = 1 ∧ ∀ x ∈ I, ∀ y ∈ I, x = y

/-- The type at position `i` (default `ext 0`). -/
def tyOf (I : List VT) (i : ℕ) : VT := I[i]?.getD (.ext 0)

theorem ofFn_tyOf (I : List VT) : List.ofFn (fun i : Fin I.length => tyOf I i) = I := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [tyOf, List.getElem?_eq_getElem h2]

theorem tyOf_eq {I : List VT} {i : ℕ} (hi : i < I.length) : tyOf I i = I[i] := by
  simp [tyOf, List.getElem?_eq_getElem hi]

theorem two_le_count_of_getElem {α : Type*} [BEq α] [LawfulBEq α] {x : α} :
    ∀ (l : List α) (i j : ℕ) (hij : i < j) (hj : j < l.length),
      l[i]'(by omega) = x → l[j] = x → 2 ≤ l.count x
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | a :: t, i, j, hij, hj, hi', hj' => by
    rcases i with _ | i
    · simp only [List.getElem_cons_zero] at hi'
      subst hi'
      have hmem : a ∈ t := by
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp only [List.getElem_cons_succ] at hj'
        rw [← hj']; exact List.getElem_mem _
      rw [List.count_cons_self]
      have := List.count_pos_iff.2 hmem
      omega
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.getElem_cons_succ] at hi' hj'
      have := two_le_count_of_getElem t i j (by omega) (by simpa using hj) hi' hj'
      have h2 := List.count_le_count_cons (a := x) (b := a) (l := t)
      omega

/-- From a cyclic colouring with the "sees" conditions to a solution. -/
theorem solvable_of_seq {I : List VT} (hk : 2 ≤ I.length)
    (hnc : ∀ l, I.count (.lab l) ≤ 1) (F : ℕ → Fin 3)
    (hF : ∀ i (hi : i < I.length) a, I[i] = .ext a → F i = a)
    (hend : F (I.length - 1) ≠ F 0) : Solvable I := by
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_cycle_colouring I.length hk F hend
  have hprev : ∀ i < I.length, c (prevI I.length i) ≠ c i := by
    intro i hi; unfold prevI; split_ifs with h0
    · subst h0; exact hc2
    · exact hc1 i (by omega) hi
  have hsee : ∀ i < I.length, F i = c (prevI I.length i) ∨ F i = c i := by
    intro i hi; unfold prevI; split_ifs with h0
    · subst h0; exact hc4
    · exact hc3 i (by omega) hi
  refine ⟨ofFun I.length (tyOf I) c, ?_, valid_ofFun (by omega) hprev ?_ ?_⟩
  · simp only [ofFun, List.map_ofFn]
    exact ofFn_tyOf I
  · intro i hi a ha
    rw [tyOf_eq hi] at ha
    rw [← hF i hi a ha]
    exact (third_ne_iff _ _ _ (hprev i hi)).2 (hsee i hi)
  · intro i j hij hj l hi hj'
    rw [tyOf_eq (by omega)] at hi
    rw [tyOf_eq hj] at hj'
    have := two_le_count_of_getElem I i j hij hj hi hj'
    have := hnc l
    omega

theorem getElem_rotate' {α : Type*} (I : List α) (r i : ℕ) (hi : i < (I.rotate r).length) :
    (I.rotate r)[i] = I[(i + r) % I.length]'(Nat.mod_lt _ (by simp at hi; omega)) :=
  List.getElem_rotate I r i hi

theorem fin3_ne_add_one : ∀ g : Fin 3, g ≠ g + 1 := by decide

theorem third_g_ne : ∀ g : Fin 3, third g (g + 1) ≠ g ∧ third (g + 1) g ≠ g ∧ g + 1 ≠ g := by
  decide

theorem third_ne_g : ∀ x y g : Fin 3, x ≠ y → (x = g ∨ y = g) → third x y ≠ g := by decide

/-- **Chordless instances.** -/
theorem chordless_solvable {I : List VT} (hk : 2 ≤ I.length)
    (hnc : ∀ l, I.count (.lab l) ≤ 1) (hE : ¬ E1 I) : Solvable I := by
  classical
  have hcnt : ∀ r, ∀ l, (I.rotate r).count (.lab l) ≤ 1 := fun r l => by
    rw [(List.rotate_perm I r).count_eq]; exact hnc l
  by_cases hlab : ∃ i, ∃ hi : i < I.length, ∃ l, I[i] = .lab l
  · -- rotate a label to position `0`
    obtain ⟨i, hi, l, hl⟩ := hlab
    apply solvable_of_rotate (n := i) (by omega)
    have hJl : (I.rotate i).length = I.length := List.length_rotate I i
    have hJ0 : (I.rotate i)[0]'(by omega) = .lab l := by
      rw [getElem_rotate' I i 0, Nat.zero_add]
      simp only [Nat.mod_eq_of_lt hi]; exact hl
    let F0 : ℕ → Fin 3 := fun j => match tyOf (I.rotate i) j with | .ext a => a | .lab _ => 0
    let F : ℕ → Fin 3 := fun j => if j = 0 then F0 ((I.rotate i).length - 1) + 1 else F0 j
    refine solvable_of_seq (by omega) (hcnt i) F (fun j hj a ha => ?_) ?_
    · have hj0 : j ≠ 0 := by
        rintro rfl; rw [hJ0] at ha; cases ha
      simp only [F, if_neg hj0, F0, tyOf_eq hj, ha]
    · simp only [F, if_neg (show (I.rotate i).length - 1 ≠ 0 by omega), ↓reduceIte]
      exact fin3_ne_add_one _
  · push Not at hlab
    have hext : ∀ i (hi : i < I.length), ∃ a, I[i] = .ext a := by
      intro i hi
      cases h : I[i] with
      | ext a => exact ⟨a, rfl⟩
      | lab l => exact absurd h (hlab i hi l)
    by_cases hchange : ∃ j, ∃ hj : j < I.length,
        I[j] ≠ I[(j + 1) % I.length]'(Nat.mod_lt _ (by omega))
    · obtain ⟨j, hj, hne⟩ := hchange
      have hr : (j + 1) % I.length < I.length := Nat.mod_lt _ (by omega)
      apply solvable_of_rotate (n := (j + 1) % I.length) (Nat.le_of_lt hr)
      have hJl : (I.rotate ((j + 1) % I.length)).length = I.length := List.length_rotate _ _
      let G : ℕ → Fin 3 := fun i =>
        match tyOf (I.rotate ((j + 1) % I.length)) i with | .ext a => a | .lab _ => 0
      refine solvable_of_seq (by omega) (hcnt _) G
        (fun i hi a ha => by simp only [G, tyOf_eq hi, ha]) ?_
      have hlast : (I.rotate ((j + 1) % I.length))[(I.rotate ((j + 1) % I.length)).length - 1]'
          (by omega) = I[j] := by
        rw [getElem_rotate' I _ _]
        congr 1
        rw [hJl, Nat.add_mod_mod, show I.length - 1 + (j + 1) = j + I.length by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      have hfirst : (I.rotate ((j + 1) % I.length))[0]'(by omega) =
          I[(j + 1) % I.length]'hr := by
        rw [getElem_rotate' I _ _]
        congr 1
        rw [Nat.zero_add, Nat.mod_mod]
      obtain ⟨a, ha⟩ := hext j hj
      obtain ⟨b, hb⟩ := hext _ hr
      simp only [G, tyOf_eq (show (I.rotate ((j + 1) % I.length)).length - 1 <
        (I.rotate ((j + 1) % I.length)).length by omega),
        tyOf_eq (show 0 < (I.rotate ((j + 1) % I.length)).length by omega), hlast, hfirst, ha, hb]
      intro hab
      subst hab
      exact hne (ha.trans hb.symm)
    · push Not at hchange
      have hall : ∀ j (hj : j < I.length), I[j] = I[0]'(by omega) := by
        intro j hj
        induction j with
        | zero => rfl
        | succ j ih =>
          have := hchange j (by omega)
          simp only [Nat.mod_eq_of_lt hj] at this
          exact this.symm.trans (ih (by omega))
      obtain ⟨g, hg⟩ := hext 0 (by omega)
      have heven : I.length % 2 = 0 := by
        by_contra hodd
        apply hE
        refine ⟨fun l hl => ?_, by omega, fun x hx y hy => ?_⟩
        · obtain ⟨j, hj, hjl⟩ := List.getElem_of_mem hl
          exact hlab j hj l hjl
        · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
          obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hy
          rw [hall j hj, hall j' hj']
      -- alternate `g` and `g + 1`
      let c : ℕ → Fin 3 := fun i => if i % 2 = 0 then g else g + 1
      have hgg : g + 1 ≠ g := fun h => fin3_ne_add_one g h.symm
      have hprev : ∀ i < I.length, c (prevI I.length i) ≠ c i := by
        intro i hi
        unfold prevI
        split_ifs with h0
        · subst h0
          simp only [c, show (I.length - 1) % 2 = 1 by omega, Nat.zero_mod, ↓reduceIte,
            show ¬ ((1 : ℕ) = 0) by omega]
          exact hgg
        · by_cases hp : i % 2 = 0
          · simp only [c, show (i - 1) % 2 = 1 by omega, hp, ↓reduceIte,
              show ¬ ((1 : ℕ) = 0) by omega]
            exact hgg
          · simp only [c, show (i - 1) % 2 = 0 by omega, hp, ↓reduceIte]
            exact hgg.symm
      have hsee : ∀ i < I.length, c (prevI I.length i) = g ∨ c i = g := by
        intro i hi
        by_cases hp : i % 2 = 0
        · right; simp [c, hp]
        · left
          unfold prevI
          rw [if_neg (by omega)]
          simp [c, show (i - 1) % 2 = 0 by omega]
      refine ⟨ofFun I.length (tyOf I) c, ?_, valid_ofFun (by omega) hprev ?_ ?_⟩
      · simp only [ofFun, List.map_ofFn]; exact ofFn_tyOf I
      · intro i hi a ha
        rw [tyOf_eq hi, hall i hi, hg] at ha
        cases ha
        exact third_ne_g _ _ _ (hprev i hi) (hsee i hi)
      · intro i j hij hj l hi
        rw [tyOf_eq (by omega), hall i (by omega), hg] at hi
        cases hi

end CoreDeg2Lib.Chord
