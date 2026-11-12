/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.CycleColour
public import Mathlib.Tactic.FinCases

/-!
# The arc lemmas

An arc `x a₁ … a_{p−1} y` of a cycle, entered by an edge of colour `κ₁` and left by an edge of
colour `κ₂`. Each inner vertex `aᵢ` carries an optional forbidden missing colour `tᵢ`; the ends
must miss different colours (they are joined by a chord). We colour the `p` edges of the arc.

* `arc_free`: if `p ≥ 3`, `κ₁ ≠ κ₂` and not (`t₁ = κ₁` and `t_{p−1} = κ₂`), the arc can be coloured;
* `arc_remove`: if `p ≥ 3`, `κ₁ = κ₂` and `t₁ ≠ t_{p−1}` (both given), the arc can be coloured.

Proof: the arc is read by a finite automaton whose state is the set of pairs (colour of the first
arc edge, colour of the current edge) that can be reached; the states reachable after the first
inner vertex are enumerated (`clos`) and checked by `decide`.
-/

@[expose] public section

namespace CoreDeg2Lib.Chord

/-- Admissible colours `e, e'` of the two edges at an inner vertex with restriction `t`. -/
def okT (t : Option (Fin 3)) (e e' : Fin 3) : Prop := e ≠ e' ∧ ∀ a, t = some a → third e e' ≠ a

instance (t : Option (Fin 3)) (e e' : Fin 3) : Decidable (okT t e e') := by
  unfold okT; infer_instance

/-- Walks along the inner vertices: `WalkQ e ts Q e'` — starting with edge colour `e`, reading the
restrictions `ts`, producing the `(in, out)` pairs `Q` and ending with edge colour `e'`. -/
inductive WalkQ : Fin 3 → List (Option (Fin 3)) → List (Fin 3 × Fin 3) → Fin 3 → Prop
  | nil (e : Fin 3) : WalkQ e [] [] e
  | cons {e e₁ e' : Fin 3} {t : Option (Fin 3)} {ts Q} :
      okT t e e₁ → WalkQ e₁ ts Q e' → WalkQ e (t :: ts) ((e, e₁) :: Q) e'

/-- Automaton states: a relation on colours, as nine booleans. -/
structure St where
  b00 : Bool
  b01 : Bool
  b02 : Bool
  b10 : Bool
  b11 : Bool
  b12 : Bool
  b20 : Bool
  b21 : Bool
  b22 : Bool
  deriving DecidableEq

/-- Reading a state. -/
def St.get (s : St) (i j : Fin 3) : Bool :=
  match i, j with
  | 0, 0 => s.b00 | 0, 1 => s.b01 | 0, 2 => s.b02
  | 1, 0 => s.b10 | 1, 1 => s.b11 | 1, 2 => s.b12
  | 2, 0 => s.b20 | 2, 1 => s.b21 | 2, 2 => s.b22

/-- Building a state from a predicate. -/
def St.mk' (f : Fin 3 → Fin 3 → Bool) : St :=
  ⟨f 0 0, f 0 1, f 0 2, f 1 0, f 1 1, f 1 2, f 2 0, f 2 1, f 2 2⟩

theorem St.get_mk' (f : Fin 3 → Fin 3 → Bool) (i j : Fin 3) : (St.mk' f).get i j = f i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- One step of the automaton. -/
def step (s : St) (t : Option (Fin 3)) : St :=
  St.mk' fun e0 e' => decide (∃ e : Fin 3, s.get e0 e = true ∧ okT t e e')

/-- The initial state: the first arc edge `e₀ ≠ κ₁`. -/
def initSt (κ₁ : Fin 3) : St := St.mk' fun e0 e => decide (e0 = e ∧ e0 ≠ κ₁)

/-- Acceptance: the last edge differs from `κ₂` and the ends of the arc miss different colours. -/
def acc (κ₁ κ₂ : Fin 3) (s : St) : Prop :=
  ∃ e0 e : Fin 3, s.get e0 e = true ∧ e ≠ κ₂ ∧ third κ₁ e0 ≠ third e κ₂

instance (κ₁ κ₂ : Fin 3) (s : St) : Decidable (acc κ₁ κ₂ s) := by unfold acc; infer_instance

/-- All restrictions. -/
def letters : List (Option (Fin 3)) := [none, some 0, some 1, some 2]

theorem mem_letters (t : Option (Fin 3)) : t ∈ letters := by
  rcases t with _ | t
  · simp [letters]
  · fin_cases t <;> simp [letters]

/-- The states reachable after the first inner vertex (computed; closure checked below). -/
def clos : Fin 3 → Option (Fin 3) → List St
  | 0, none => [
    ⟨false, false, false, true, false, true, true, true, false⟩,
    ⟨false, false, false, true, true, true, true, true, true⟩,
    ⟨false, false, false, false, true, false, true, true, true⟩,
    ⟨false, false, false, true, true, true, false, false, true⟩,
    ⟨false, false, false, true, true, true, true, true, false⟩,
    ⟨false, false, false, true, true, true, true, false, false⟩,
    ⟨false, false, false, true, true, true, false, true, false⟩,
    ⟨false, false, false, true, true, true, true, false, true⟩,
    ⟨false, false, false, true, true, true, false, true, true⟩,
    ⟨false, false, false, true, false, true, true, true, true⟩,
    ⟨false, false, false, true, false, false, true, true, true⟩,
    ⟨false, false, false, false, false, true, true, true, true⟩,
    ⟨false, false, false, true, true, false, true, true, true⟩,
    ⟨false, false, false, false, true, true, true, true, true⟩]
  | 0, some 0 => [
    ⟨false, false, false, true, false, false, true, false, false⟩,
    ⟨false, false, false, false, true, true, false, true, true⟩,
    ⟨false, false, false, false, true, false, false, true, false⟩,
    ⟨false, false, false, false, false, true, false, false, true⟩,
    ⟨false, false, false, true, true, false, true, true, false⟩,
    ⟨false, false, false, true, true, true, true, true, true⟩,
    ⟨false, false, false, true, false, true, true, false, true⟩]
  | 0, some 1 => [
    ⟨false, false, false, true, false, true, false, true, false⟩,
    ⟨false, false, false, true, true, true, true, false, true⟩,
    ⟨false, false, false, true, true, true, true, false, false⟩,
    ⟨false, false, false, false, true, false, true, false, true⟩,
    ⟨false, false, false, true, true, true, false, false, true⟩,
    ⟨false, false, false, true, true, true, true, true, false⟩,
    ⟨false, false, false, true, true, true, false, true, false⟩,
    ⟨false, false, false, true, true, true, true, true, true⟩,
    ⟨false, false, false, true, false, true, true, true, true⟩,
    ⟨false, false, false, true, false, false, true, true, true⟩,
    ⟨false, false, false, false, false, true, true, true, true⟩,
    ⟨false, false, false, true, true, false, true, true, true⟩,
    ⟨false, false, false, false, true, false, true, true, true⟩,
    ⟨false, false, false, false, true, true, true, true, true⟩,
    ⟨false, false, false, true, true, true, false, true, true⟩]
  | 0, some 2 => [
    ⟨false, false, false, false, false, true, true, true, false⟩,
    ⟨false, false, false, true, true, false, true, true, true⟩,
    ⟨false, false, false, true, false, false, true, true, true⟩,
    ⟨false, false, false, false, true, false, true, true, true⟩,
    ⟨false, false, false, true, true, false, false, false, true⟩,
    ⟨false, false, false, true, true, true, true, true, false⟩,
    ⟨false, false, false, true, true, true, true, false, false⟩,
    ⟨false, false, false, true, true, true, false, true, false⟩,
    ⟨false, false, false, true, true, true, true, false, true⟩,
    ⟨false, false, false, true, true, true, false, false, true⟩,
    ⟨false, false, false, true, true, true, true, true, true⟩,
    ⟨false, false, false, true, true, true, false, true, true⟩,
    ⟨false, false, false, true, false, true, true, true, true⟩,
    ⟨false, false, false, false, false, true, true, true, true⟩,
    ⟨false, false, false, false, true, true, true, true, true⟩]
  | 1, none => [
    ⟨false, true, true, false, false, false, true, true, false⟩,
    ⟨true, true, true, false, false, false, true, true, true⟩,
    ⟨true, false, false, false, false, false, true, true, true⟩,
    ⟨true, true, true, false, false, false, false, false, true⟩,
    ⟨true, true, true, false, false, false, true, true, false⟩,
    ⟨true, true, true, false, false, false, true, false, false⟩,
    ⟨true, true, true, false, false, false, false, true, false⟩,
    ⟨true, true, true, false, false, false, true, false, true⟩,
    ⟨true, true, true, false, false, false, false, true, true⟩,
    ⟨false, true, true, false, false, false, true, true, true⟩,
    ⟨false, true, false, false, false, false, true, true, true⟩,
    ⟨false, false, true, false, false, false, true, true, true⟩,
    ⟨true, true, false, false, false, false, true, true, true⟩,
    ⟨true, false, true, false, false, false, true, true, true⟩]
  | 1, some 0 => [
    ⟨false, true, true, false, false, false, true, false, false⟩,
    ⟨true, true, true, false, false, false, false, true, true⟩,
    ⟨true, false, false, false, false, false, false, true, true⟩,
    ⟨true, true, true, false, false, false, false, true, false⟩,
    ⟨true, true, true, false, false, false, false, false, true⟩,
    ⟨true, true, true, false, false, false, true, true, false⟩,
    ⟨true, true, true, false, false, false, true, false, false⟩,
    ⟨true, true, true, false, false, false, true, true, true⟩,
    ⟨true, true, true, false, false, false, true, false, true⟩,
    ⟨false, true, true, false, false, false, true, true, true⟩,
    ⟨false, true, false, false, false, false, true, true, true⟩,
    ⟨false, false, true, false, false, false, true, true, true⟩,
    ⟨true, true, false, false, false, false, true, true, true⟩,
    ⟨true, false, false, false, false, false, true, true, true⟩,
    ⟨true, false, true, false, false, false, true, true, true⟩]
  | 1, some 1 => [
    ⟨false, true, false, false, false, false, false, true, false⟩,
    ⟨true, false, true, false, false, false, true, false, true⟩,
    ⟨true, false, false, false, false, false, true, false, false⟩,
    ⟨false, false, true, false, false, false, false, false, true⟩,
    ⟨true, true, false, false, false, false, true, true, false⟩,
    ⟨true, true, true, false, false, false, true, true, true⟩,
    ⟨false, true, true, false, false, false, false, true, true⟩]
  | 1, some 2 => [
    ⟨false, false, true, false, false, false, true, true, false⟩,
    ⟨true, true, false, false, false, false, true, true, true⟩,
    ⟨true, false, false, false, false, false, true, true, true⟩,
    ⟨false, true, false, false, false, false, true, true, true⟩,
    ⟨true, true, false, false, false, false, false, false, true⟩,
    ⟨true, true, true, false, false, false, true, true, false⟩,
    ⟨true, true, true, false, false, false, true, false, false⟩,
    ⟨true, true, true, false, false, false, false, true, false⟩,
    ⟨true, true, true, false, false, false, true, false, true⟩,
    ⟨true, true, true, false, false, false, false, false, true⟩,
    ⟨true, true, true, false, false, false, true, true, true⟩,
    ⟨true, true, true, false, false, false, false, true, true⟩,
    ⟨true, false, true, false, false, false, true, true, true⟩,
    ⟨false, false, true, false, false, false, true, true, true⟩,
    ⟨false, true, true, false, false, false, true, true, true⟩]
  | 2, none => [
    ⟨false, true, true, true, false, true, false, false, false⟩,
    ⟨true, true, true, true, true, true, false, false, false⟩,
    ⟨true, false, false, true, true, true, false, false, false⟩,
    ⟨true, true, true, false, true, false, false, false, false⟩,
    ⟨true, true, true, true, false, true, false, false, false⟩,
    ⟨true, true, true, true, false, false, false, false, false⟩,
    ⟨true, true, true, false, false, true, false, false, false⟩,
    ⟨true, true, true, true, true, false, false, false, false⟩,
    ⟨true, true, true, false, true, true, false, false, false⟩,
    ⟨false, true, true, true, true, true, false, false, false⟩,
    ⟨false, true, false, true, true, true, false, false, false⟩,
    ⟨false, false, true, true, true, true, false, false, false⟩,
    ⟨true, true, false, true, true, true, false, false, false⟩,
    ⟨true, false, true, true, true, true, false, false, false⟩]
  | 2, some 0 => [
    ⟨false, true, true, true, false, false, false, false, false⟩,
    ⟨true, true, true, false, true, true, false, false, false⟩,
    ⟨true, false, false, false, true, true, false, false, false⟩,
    ⟨true, true, true, false, true, false, false, false, false⟩,
    ⟨true, true, true, false, false, true, false, false, false⟩,
    ⟨true, true, true, true, true, false, false, false, false⟩,
    ⟨true, true, true, true, false, false, false, false, false⟩,
    ⟨true, true, true, true, true, true, false, false, false⟩,
    ⟨true, true, true, true, false, true, false, false, false⟩,
    ⟨false, true, true, true, true, true, false, false, false⟩,
    ⟨false, true, false, true, true, true, false, false, false⟩,
    ⟨false, false, true, true, true, true, false, false, false⟩,
    ⟨true, true, false, true, true, true, false, false, false⟩,
    ⟨true, false, false, true, true, true, false, false, false⟩,
    ⟨true, false, true, true, true, true, false, false, false⟩]
  | 2, some 1 => [
    ⟨false, true, false, true, false, true, false, false, false⟩,
    ⟨true, false, true, true, true, true, false, false, false⟩,
    ⟨true, false, false, true, true, true, false, false, false⟩,
    ⟨true, false, true, false, true, false, false, false, false⟩,
    ⟨false, false, true, true, true, true, false, false, false⟩,
    ⟨true, true, false, true, true, true, false, false, false⟩,
    ⟨false, true, false, true, true, true, false, false, false⟩,
    ⟨true, true, true, true, true, true, false, false, false⟩,
    ⟨true, true, true, true, false, true, false, false, false⟩,
    ⟨true, true, true, true, false, false, false, false, false⟩,
    ⟨true, true, true, false, false, true, false, false, false⟩,
    ⟨true, true, true, true, true, false, false, false, false⟩,
    ⟨true, true, true, false, true, false, false, false, false⟩,
    ⟨true, true, true, false, true, true, false, false, false⟩,
    ⟨false, true, true, true, true, true, false, false, false⟩]
  | 2, some 2 => [
    ⟨false, false, true, false, false, true, false, false, false⟩,
    ⟨true, true, false, true, true, false, false, false, false⟩,
    ⟨true, false, false, true, false, false, false, false, false⟩,
    ⟨false, true, false, false, true, false, false, false, false⟩,
    ⟨true, false, true, true, false, true, false, false, false⟩,
    ⟨true, true, true, true, true, true, false, false, false⟩,
    ⟨false, true, true, false, true, true, false, false, false⟩]

theorem clos_init : ∀ κ₁ : Fin 3, ∀ t₁ ∈ letters, step (initSt κ₁) t₁ ∈ clos κ₁ t₁ := by
  decide

theorem clos_step : ∀ κ₁ : Fin 3, ∀ t₁ ∈ letters, ∀ s ∈ clos κ₁ t₁, ∀ t ∈ letters,
    step s t ∈ clos κ₁ t₁ := by
  decide

theorem clos_acc_free : ∀ κ₁ κ₂ : Fin 3, κ₁ ≠ κ₂ → ∀ t₁ ∈ letters, ∀ tl ∈ letters,
    ¬ (t₁ = some κ₁ ∧ tl = some κ₂) → ∀ s ∈ clos κ₁ t₁, acc κ₁ κ₂ (step s tl) := by
  decide

theorem clos_acc_remove : ∀ κ t₁ tl : Fin 3, t₁ ≠ tl → ∀ s ∈ clos κ (some t₁),
    acc κ κ (step s (some tl)) := by
  decide

theorem foldl_mem_clos (κ₁ : Fin 3) (t₁ : Option (Fin 3)) :
    ∀ (w : List (Option (Fin 3))) (s : St), s ∈ clos κ₁ t₁ → w.foldl step s ∈ clos κ₁ t₁
  | [], _, hs => hs
  | t :: w, s, hs => foldl_mem_clos κ₁ t₁ w _ (clos_step κ₁ t₁ (mem_letters _) s hs t (mem_letters _))

/-- Soundness of the automaton. -/
theorem sound : ∀ (w : List (Option (Fin 3))) (s : St) (e0 e' : Fin 3),
    (w.foldl step s).get e0 e' = true → ∃ e Q, s.get e0 e = true ∧ WalkQ e w Q e'
  | [], s, e0, e', h => ⟨e', [], h, WalkQ.nil e'⟩
  | t :: w, s, e0, e', h => by
    obtain ⟨e₁, Q, h1, hw⟩ := sound w (step s t) e0 e' h
    rw [step, St.get_mk', decide_eq_true_iff] at h1
    obtain ⟨e, he, hok⟩ := h1
    exact ⟨e, (e, e₁) :: Q, he, WalkQ.cons hok hw⟩

theorem initSt_get {κ₁ e0 e : Fin 3} (h : (initSt κ₁).get e0 e = true) : e0 = e ∧ e0 ≠ κ₁ := by
  rw [initSt, St.get_mk', decide_eq_true_iff] at h; exact h

/-- **Arc lemma, one-vertex replacement.** -/
theorem arc_free {κ₁ κ₂ : Fin 3} (hκ : κ₁ ≠ κ₂) (t₁ tl : Option (Fin 3))
    (mid : List (Option (Fin 3))) (hbad : ¬ (t₁ = some κ₁ ∧ tl = some κ₂)) :
    ∃ e0 Q eL, e0 ≠ κ₁ ∧ WalkQ e0 (t₁ :: mid ++ [tl]) Q eL ∧ eL ≠ κ₂ ∧
      third κ₁ e0 ≠ third eL κ₂ := by
  have hs : (t₁ :: mid).foldl step (initSt κ₁) ∈ clos κ₁ t₁ :=
    foldl_mem_clos κ₁ t₁ mid _ (clos_init κ₁ t₁ (mem_letters _))
  obtain ⟨e0, eL, hget, hne, hthird⟩ :=
    clos_acc_free κ₁ κ₂ hκ t₁ (mem_letters _) tl (mem_letters _) hbad _ hs
  obtain ⟨e, Q, hi, hw⟩ := sound (t₁ :: mid ++ [tl]) (initSt κ₁) e0 eL (by
    rw [List.foldl_append]; simpa using hget)
  obtain ⟨rfl, h0⟩ := initSt_get hi
  exact ⟨e0, Q, eL, h0, hw, hne, hthird⟩

/-- **Arc lemma, removal.** -/
theorem arc_remove (κ : Fin 3) {t₁ tl : Fin 3} (ht : t₁ ≠ tl) (mid : List (Option (Fin 3))) :
    ∃ e0 Q eL, e0 ≠ κ ∧ WalkQ e0 (some t₁ :: mid ++ [some tl]) Q eL ∧ eL ≠ κ ∧
      third κ e0 ≠ third eL κ := by
  have hs : (some t₁ :: mid).foldl step (initSt κ) ∈ clos κ (some t₁) :=
    foldl_mem_clos κ (some t₁) mid _ (clos_init κ (some t₁) (mem_letters _))
  obtain ⟨e0, eL, hget, hne, hthird⟩ := clos_acc_remove κ t₁ tl ht _ hs
  obtain ⟨e, Q, hi, hw⟩ := sound (some t₁ :: mid ++ [some tl]) (initSt κ) e0 eL (by
    rw [List.foldl_append]; simpa using hget)
  obtain ⟨rfl, h0⟩ := initSt_get hi
  exact ⟨e0, Q, eL, h0, hw, hne, hthird⟩

end CoreDeg2Lib.Chord
