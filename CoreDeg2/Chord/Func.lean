/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Chord.Chordless

/-!
# Instances as functions

An instance of length `k` is a function `ty : ℕ → VT` (only `i < k` matters); a solution is an edge
colouring `c : ℕ → Fin 3` of the cycle (edge `i` joins `i` and `i + 1 mod k`). `FSol k ty c` says
that `c` is proper and the restrictions hold; `Solv k ty` that a solution exists. Rotations
(`rot k r ty`) preserve solvability; instances without repeated labels are handled by
`chordless_solvable`.
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

/-- The colour missing at vertex `i`. -/
def mvAt (k : ℕ) (c : ℕ → Fin 3) (i : ℕ) : Fin 3 := third (c (prevI k i)) (c i)

/-- `c` solves the instance `ty` of length `k`. -/
def FSol (k : ℕ) (ty : ℕ → VT) (c : ℕ → Fin 3) : Prop :=
  (∀ i < k, c (prevI k i) ≠ c i) ∧ (∀ i < k, ∀ a, ty i = .ext a → mvAt k c i ≠ a) ∧
  (∀ i j, i < k → j < k → i ≠ j → ∀ l, ty i = .lab l → ty j = .lab l → mvAt k c i ≠ mvAt k c j)

/-- The instance `ty` of length `k` is solvable. -/
def Solv (k : ℕ) (ty : ℕ → VT) : Prop := ∃ c, FSol k ty c

theorem solv_iff {k : ℕ} (hk : 1 ≤ k) (ty : ℕ → VT) :
    Solv k ty ↔ Solvable (List.ofFn fun i : Fin k => ty i) := by
  constructor
  · rintro ⟨c, h1, h2, h3⟩
    refine ⟨ofFun k ty c, by simp only [ofFun, List.map_ofFn]; rfl, valid_ofFun hk h1 h2 ?_⟩
    intro i j hij hj l hi hj'
    exact h3 i j (by omega) hj (by omega) l hi hj'
  · intro h
    obtain ⟨c, h1, h2, h3⟩ := exists_fun_of_solvable hk h
    refine ⟨c, h1, h2, fun i j hi hj hij l hli hlj => ?_⟩
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact h3 i j h hj l hli hlj
    · exact (h3 j i h hi l hlj hli).symm

theorem solv_congr {k : ℕ} {ty ty' : ℕ → VT} (h : ∀ i < k, ty i = ty' i) (hs : Solv k ty) :
    Solv k ty' := by
  obtain ⟨c, h1, h2, h3⟩ := hs
  exact ⟨c, h1, fun i hi a ha => h2 i hi a (by rw [h i hi]; exact ha),
    fun i j hi hj hij l hli hlj => h3 i j hi hj hij l (by rw [h i hi]; exact hli)
      (by rw [h j hj]; exact hlj)⟩

/-- Rotation of an instance. -/
def rot (k r : ℕ) (ty : ℕ → VT) : ℕ → VT := fun i => ty ((i + r) % k)

theorem ofFn_rot {k : ℕ} (r : ℕ) (ty : ℕ → VT) :
    (List.ofFn fun i : Fin k => ty i).rotate r = List.ofFn fun i : Fin k => rot k r ty i := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  rw [List.getElem_rotate]
  simp [rot]

theorem solv_of_rot {k : ℕ} (hk : 1 ≤ k) {r : ℕ} {ty : ℕ → VT} (h : Solv k (rot k r ty)) :
    Solv k ty := by
  rw [solv_iff hk] at h ⊢
  rw [← ofFn_rot] at h
  have h2 := h.rotate (k - r % k)
  rw [List.rotate_rotate, ← List.rotate_mod] at h2
  have hm : (r + (k - r % k)) % (List.ofFn fun i : Fin k => ty i).length = 0 := by
    rw [List.length_ofFn]
    have := Nat.mod_lt r (show 0 < k by omega)
    have h3 := Nat.div_add_mod r k
    rw [show r + (k - r % k) = k * (r / k + 1) by
      have : k * (r / k + 1) = k * (r / k) + k := Nat.mul_succ k (r / k)
      omega]
    exact Nat.mul_mod_right _ _
  rwa [hm, List.rotate_zero] at h2

theorem rot_rot (k r r' : ℕ) (ty : ℕ → VT) : rot k r' (rot k r ty) = rot k (r' + r) ty := by
  funext i
  simp only [rot, Nat.mod_add_mod, Nat.add_assoc]

/-! ### Structure of instances -/

/-- `i` and `j` are distinct positions carrying the same label. -/
def Partner (k : ℕ) (ty : ℕ → VT) (i j : ℕ) : Prop :=
  i < k ∧ j < k ∧ i ≠ j ∧ ∃ l, ty i = .lab l ∧ ty j = .lab l

/-- No label is carried three times. -/
def WFf (k : ℕ) (ty : ℕ → VT) : Prop :=
  ∀ i j h, Partner k ty i j → Partner k ty j h → i ≠ h → False

/-- A label carried once: a free vertex. -/
def FreeAt (k : ℕ) (ty : ℕ → VT) (i : ℕ) : Prop :=
  i < k ∧ (∃ l, ty i = .lab l) ∧ ∀ j, ¬ Partner k ty i j

/-- Some label is carried twice. -/
def HasChordF (k : ℕ) (ty : ℕ → VT) : Prop := ∃ i j, Partner k ty i j

/-- Exceptional (E1): no labels, odd length, all restrictions equal. -/
def E1F (k : ℕ) (ty : ℕ → VT) : Prop :=
  (∀ i < k, ∀ l, ty i ≠ .lab l) ∧ k % 2 = 1 ∧ ∀ i < k, ty i = ty 0

/-- Exceptional (E2): the hexagon with three antipodal chords. -/
def HexF (k : ℕ) (ty : ℕ → VT) : Prop := k = 6 ∧ ∀ i < 3, Partner k ty i (i + 3)

theorem Partner.symm {k : ℕ} {ty : ℕ → VT} {i j : ℕ} (h : Partner k ty i j) : Partner k ty j i := by
  obtain ⟨hi, hj, hij, l, h1, h2⟩ := h
  exact ⟨hj, hi, hij.symm, l, h2, h1⟩

theorem partner_rot {k r : ℕ} {ty : ℕ → VT} {i j : ℕ} (h : Partner k (rot k r ty) i j) :
    Partner k ty ((i + r) % k) ((j + r) % k) := by
  obtain ⟨hi, hj, hij, l, h1, h2⟩ := h
  have hk : 0 < k := by omega
  refine ⟨Nat.mod_lt _ hk, Nat.mod_lt _ hk, fun he => hij ?_, l, h1, h2⟩
  -- `i ↦ (i + r) % k` is injective on `[0, k)`
  have := Nat.ModEq.add_right_cancel' r (show i + r ≡ j + r [MOD k] from he)
  exact Nat.ModEq.eq_of_lt_of_lt this hi hj

theorem wf_rot {k r : ℕ} {ty : ℕ → VT} (h : WFf k ty) : WFf k (rot k r ty) := by
  intro i j m h1 h2 him
  refine h _ _ _ (partner_rot h1) (partner_rot h2) fun he => him ?_
  have := Nat.ModEq.add_right_cancel' r (show i + r ≡ m + r [MOD k] from he)
  exact Nat.ModEq.eq_of_lt_of_lt this h1.1 h2.2.1

theorem exists_two_of_two_le_count {α : Type*} [DecidableEq α] {x : α} :
    ∀ (l : List α), 2 ≤ l.count x → ∃ i j, ∃ (hij : i < j) (hj : j < l.length),
      l[i]'(by omega) = x ∧ l[j] = x
  | [], h => by simp at h
  | a :: t, h => by
    rw [List.count_cons] at h
    by_cases hax : a = x
    · subst hax
      have hmem : a ∈ t := by
        by_contra hn
        rw [List.count_eq_zero.2 hn] at h
        simp at h
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hmem
      exact ⟨0, j + 1, by omega, by simpa using hj, rfl, by simpa using hjx⟩
    · simp [hax] at h
      obtain ⟨i, j, hij, hj, h1, h2⟩ := exists_two_of_two_le_count t h
      exact ⟨i + 1, j + 1, by omega, by simpa using hj, by simpa using h1, by simpa using h2⟩

/-- Solvability of instances without chords. -/
theorem solv_chordless {k : ℕ} (hk : 2 ≤ k) {ty : ℕ → VT} (hnc : ¬ HasChordF k ty)
    (hE : ¬ E1F k ty) : Solv k ty := by
  rw [solv_iff (by omega)]
  apply chordless_solvable (by simp; omega)
  · intro l
    by_contra hc
    push Not at hc
    obtain ⟨i, j, hij, hj, hi', hj'⟩ :=
      exists_two_of_two_le_count (x := VT.lab l) (List.ofFn fun i : Fin k => ty i) (by omega)
    simp only [List.getElem_ofFn, List.length_ofFn] at hi' hj' hj
    exact hnc ⟨i, j, by omega, hj, by omega, l, hi', hj'⟩
  · rintro ⟨h1, h2, h3⟩
    apply hE
    have h2' : k % 2 = 1 := by simpa using h2
    refine ⟨fun i hi l hl => h1 l ?_, h2', fun i hi => h3 _ ?_ _ ?_⟩
    · rw [← hl]; exact List.mem_ofFn.2 ⟨⟨i, hi⟩, rfl⟩
    · exact List.mem_ofFn.2 ⟨⟨i, hi⟩, rfl⟩
    · exact List.mem_ofFn.2 ⟨⟨0, by omega⟩, rfl⟩

end CoreDeg2Lib.Chord
