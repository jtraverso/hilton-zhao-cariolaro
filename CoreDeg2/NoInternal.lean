/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.Count
public import CoreDeg2.Assemble
public import LeanPool.Vizing.Endpoints

/-!
# A core cycle without internal petals forces class one (`Δ = 3`)

Let `G` be connected with `Δ(G) = 3` and core of maximum degree at most two. Suppose some vertex
`r` of degree three lies in a component `R` of the core that carries no *internal petal*: no
vertex of degree below three is adjacent to two distinct vertices of `R`. Then `G` is of class one
(`colorable_of_noInternalPetal`). This is the case "petal size `∞`" of Cariolaro–Cariolaro
(*Colouring the petals of a graph*, Lemma 7), here for a single core cycle.

Proof. Otherwise `G` is a critical petal graph (Hilton–Zhao). The component `R` is a cycle; every
`x ∈ R` has one neighbour `pw x` of degree two, whose other neighbour `py x` lies outside `R`. By
criticality `G − e` is `3`-edge-colourable for an edge `e` of `R`; uncolouring the edges at `R`
gives a colouring `d` of the rest. If the colours `F x` of the far petal edges `pw x – py x` are
not all equal, the cycle can be recoloured so that every `x` misses a colour other than `F x`
(`exists_cycle_colouring`), and then `G` is `3`-edge-colourable (`colorable_of_cycle_colouring`).
If they are all equal to `g`, swap `g` with another colour on the Kempe chain through `pw r`:
the three petal centres of `r` and its two cycle neighbours are ends of Kempe chains, and no chain
contains three ends (`no_three_endpoints`), so afterwards `F` is not constant.
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CycleWalk

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The core of `G` as a graph on `V`: edges of `G` between vertices of maximum degree. -/
def coreGraph (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => G.Adj u v ∧ G.degree u = G.maxDegree ∧ G.degree v = G.maxDegree

theorem coreGraph_adj {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    (coreGraph G).Adj u v ↔ G.Adj u v ∧ G.degree u = G.maxDegree ∧ G.degree v = G.maxDegree := by
  rw [coreGraph, fromRel_adj]
  constructor
  · rintro ⟨-, h | ⟨h1, h2, h3⟩⟩
    · exact h
    · exact ⟨h1.symm, h3, h2⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

/-- Uncolour every edge meeting `R`. -/
def restrictPEC {G : SimpleGraph V} {C : Type*} (d : PEC G C) (R : Set V) [DecidablePred (· ∈ R)] :
    PEC G C where
  col u v := if u ∈ R ∨ v ∈ R then none else d.col u v
  col_symm u v := by
    by_cases h : u ∈ R ∨ v ∈ R
    · rw [if_pos h, if_pos (Or.symm h)]
    · rw [if_neg h, if_neg (fun h' => h (Or.symm h')), d.col_symm]
  col_adj {u v γ} h := by
    split_ifs at h
    exact d.col_adj h
  col_proper {u v w γ} h1 h2 := by
    split_ifs at h1 h2
    exact d.col_proper h1 h2

theorem fin3_succ_ne : ∀ g : Fin 3, g + 1 ≠ g := by decide

/-- Walks in the core stay among vertices of maximum degree. -/
theorem degree_eq_of_walk {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (q : (coreGraph G).Walk a b) (ha : G.degree a = G.maxDegree) : G.degree b = G.maxDegree := by
  induction q with
  | nil => exact ha
  | cons h _ ih => exact ih (coreGraph_adj.1 h).2.2

/-- A function on vertices that agrees across every core edge inside `R` is constant on the
core component. -/
theorem eq_of_walk {G : SimpleGraph V} [DecidableRel G.Adj] {α : Type*} (f : V → α) {r : V}
    (h : ∀ x x', (coreGraph G).Reachable r x → (coreGraph G).Adj x x' → f x = f x') {a b : V}
    (q : (coreGraph G).Walk a b) (ha : (coreGraph G).Reachable r a) : f a = f b := by
  induction q with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ ha hadj).trans (ih (ha.trans hadj.reachable))

section Main

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Cariolaro–Cariolaro, Lemma 7 (single core cycle).** -/
theorem colorable_of_noInternalPetal (hconn : G.Connected) (hcore : CoreLeTwo G)
    (hΔ : G.maxDegree = 3) {r : V} (hr : G.degree r = 3)
    (hR : ∀ w x y, G.Adj w x → G.Adj w y → x ≠ y → G.degree w ≠ 3 →
      (coreGraph G).Reachable r x → ¬ (coreGraph G).Reachable r y) :
    G.lineGraph.Colorable 3 := by
  classical
  by_contra hcl3
  have hcl : ¬ G.lineGraph.Colorable G.maxDegree := by rwa [hΔ]
  have hcrit := isDeltaCritical G hconn hcore hcl
  obtain ⟨hdeg, hcn, hnb⟩ := petal_structure G hconn hcore hcl hΔ
  set K := coreGraph G with hKdef
  have hKadj : ∀ u v, K.Adj u v ↔ G.Adj u v ∧ G.degree u = 3 ∧ G.degree v = 3 := by
    intro u v; rw [hKdef, coreGraph_adj, hΔ]
  have hKnbr : ∀ v, G.degree v = 3 → K.neighborSet v = ↑(coreNbrs G v) := by
    intro v hv
    ext u
    rw [mem_neighborSet, hKadj, Finset.mem_coe, mem_coreNbrs, hΔ]
    simp [hv]
  have hKcyc : K.IsCycles := by
    intro v ⟨u, hu⟩
    have hv : G.degree v = 3 := ((hKadj v u).1 hu).2.1
    rw [hKnbr v hv, Set.ncard_coe_finset, hcn v hv]
  -- the core component `R` of `r`
  set R : Set V := {v | K.Reachable r v} with hRdef
  have hRcore : ∀ v ∈ R, G.degree v = 3 := by
    intro v hv
    obtain ⟨q⟩ := (show K.Reachable r v from hv)
    have := degree_eq_of_walk q (by rw [hΔ]; exact hr)
    rwa [hΔ] at this
  have hrR : r ∈ R := Reachable.refl r
  -- petal centres
  have hex1 : ∀ x, ∃ w, G.degree x = 3 →
      G.Adj x w ∧ G.degree w ≠ 3 ∧ ∀ w', G.Adj x w' → G.degree w' ≠ 3 → w' = w := by
    intro x
    by_cases hx : G.degree x = 3
    · have h1 := card_filter_add_card_filter_not (s := G.neighborFinset x) (fun u => G.degree u = 3)
      have h2 : (G.neighborFinset x).filter (fun u => G.degree u = 3) = coreNbrs G x := by
        unfold coreNbrs; rw [hΔ]
      rw [h2, hcn x hx, card_neighborFinset_eq_degree, hx] at h1
      obtain ⟨w, hw⟩ := card_eq_one.1 (show #((G.neighborFinset x).filter
        (fun u => ¬ G.degree u = 3)) = 1 by omega)
      have hwmem : w ∈ (G.neighborFinset x).filter (fun u => ¬ G.degree u = 3) := by
        rw [hw]; exact mem_singleton_self w
      rw [mem_filter, mem_neighborFinset] at hwmem
      refine ⟨w, fun _ => ⟨hwmem.1, hwmem.2, fun w' hw' hw'3 => ?_⟩⟩
      have : w' ∈ (G.neighborFinset x).filter (fun u => ¬ G.degree u = 3) := by
        rw [mem_filter, mem_neighborFinset]; exact ⟨hw', hw'3⟩
      rw [hw] at this
      exact mem_singleton.1 this
    · exact ⟨x, fun h => absurd h hx⟩
  choose pw hpw using hex1
  have hex2 : ∀ x, ∃ y, G.degree x = 3 →
      G.Adj (pw x) y ∧ y ≠ x ∧ ∀ z, G.Adj (pw x) z → z = x ∨ z = y := by
    intro x
    by_cases hx : G.degree x = 3
    · obtain ⟨hxw, hw3, -⟩ := hpw x hx
      have hw2 : G.degree (pw x) = 2 := by rcases hdeg (pw x) with h | h <;> [exact h; exact absurd h hw3]
      rw [← card_neighborFinset_eq_degree] at hw2
      obtain ⟨a, b, hab, hN⟩ := card_eq_two.1 hw2
      have hxN : x ∈ G.neighborFinset (pw x) := by rw [mem_neighborFinset]; exact hxw.symm
      have hall : ∀ z, G.Adj (pw x) z → z = a ∨ z = b := by
        intro z hz
        have : z ∈ G.neighborFinset (pw x) := by rw [mem_neighborFinset]; exact hz
        rw [hN] at this
        simpa using this
      rw [hN] at hxN
      rcases mem_insert.1 hxN with rfl | hxb
      · refine ⟨b, fun _ => ⟨?_, hab.symm, fun z hz => hall z hz⟩⟩
        have : b ∈ G.neighborFinset (pw x) := by rw [hN]; simp
        rwa [mem_neighborFinset] at this
      · rw [mem_singleton] at hxb
        subst hxb
        refine ⟨a, fun _ => ⟨?_, hab, fun z hz => (hall z hz).symm⟩⟩
        have : a ∈ G.neighborFinset (pw x) := by rw [hN]; simp
        rwa [mem_neighborFinset] at this
    · exact ⟨x, fun h => absurd h hx⟩
  choose py hpy using hex2
  have hpwR : ∀ x ∈ R, pw x ∉ R := fun x hx h => (hpw x (hRcore x hx)).2.1 (hRcore _ h)
  have hpyR : ∀ x ∈ R, py x ∉ R := by
    intro x hx h
    have hx3 := hRcore x hx
    exact hR (pw x) x (py x) (hpw x hx3).1.symm (hpy x hx3).1 (hpy x hx3).2.1.symm
      (hpw x hx3).2.1 hx h
  have hpw_inj : ∀ x x', x ∈ R → x' ∈ R → pw x = pw x' → x = x' := by
    intro x x' hx hx' h
    by_contra hne
    have hx3 := hRcore x hx
    have hx3' := hRcore x' hx'
    exact hR (pw x) x x' (hpw x hx3).1.symm (h ▸ (hpw x' hx3').1.symm) hne (hpw x hx3).2.1 hx hx'
  have hpy' : ∀ x, x ∈ R → ∀ z, G.Adj (pw x) z → z ∉ R → z = py x := by
    intro x hx z hz hzR
    rcases (hpy x (hRcore x hx)).2.2 z hz with rfl | h
    · exact absurd hx hzR
    · exact h
  have hRout : ∀ u v, u ∈ R → v ∉ R → G.Adj u v → v = pw u := by
    intro u v hu hv huv
    have hu3 := hRcore u hu
    refine (hpw u hu3).2.2 v huv fun hv3 => hv ?_
    exact (show K.Reachable r u from hu).trans ((hKadj u v).2 ⟨huv, hu3, hv3⟩).reachable
  -- colourings of the rest
  let Good : PEC G (Fin 3) → Prop := fun d => ∀ u v, G.Adj u v → u ∉ R → v ∉ R → d.col u v ≠ none
  -- an initial colouring of the rest, from criticality
  obtain ⟨r', hr'⟩ : (coreNbrs G r).Nonempty :=
    card_pos.1 (by rw [hcn r hr]; omega)
  rw [mem_coreNbrs] at hr'
  have hdel : (G.deleteEdges {s(r, r')}).lineGraph.Colorable 3 := by
    rw [← hΔ]; exact hcrit.2.2 s(r, r') hr'.1
  obtain ⟨c₀, hc₀⟩ := exists_colMinus_of_colorable hr'.1 hdel
  set d₀ := restrictPEC c₀ R with hd₀
  have hd₀col : ∀ u v, u ∉ R → v ∉ R → d₀.col u v = c₀.col u v := by
    intro u v hu hv
    show (if u ∈ R ∨ v ∈ R then none else c₀.col u v) = c₀.col u v
    rw [if_neg (by tauto)]
  have hd₀R : ∀ u v, u ∈ R → d₀.col u v = none := by
    intro u v hu
    show (if u ∈ R ∨ v ∈ R then none else c₀.col u v) = none
    rw [if_pos (Or.inl hu)]
  have hgood₀ : Good d₀ := by
    intro u v huv hu hv
    rw [hd₀col u v hu hv]
    refine hc₀.total u v huv fun h => ?_
    have : r ∈ s(u, v) := by rw [h]; exact Sym2.mem_mk_left r r'
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact hu hrR
    · exact hv hrR
  -- the far colours
  have hFsome : ∀ d, Good d → ∀ x ∈ R, d.col (pw x) (py x) ≠ none := fun d hd x hx =>
    hd _ _ (hpy x (hRcore x hx)).1 (hpwR x hx) (hpyR x hx)
  -- step 1: a colouring of the rest whose far colours are not constant on `R`
  have step1 : ∃ d, Good d ∧ ∃ x₁ ∈ R, ∃ x₂ ∈ R, d.col (pw x₁) (py x₁) ≠ d.col (pw x₂) (py x₂) := by
    by_cases hconst : ∀ x ∈ R, d₀.col (pw x) (py x) = d₀.col (pw r) (py r)
    · obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 (hFsome d₀ hgood₀ r hrR)
      set β : Fin 3 := g + 1
      have hβ : β ≠ g := fin3_succ_ne g
      set d₁ := d₀.kempeSwap g β (pw r) with hd₁
      have hgood₁ : Good d₁ := by
        intro u v huv hu hv
        rw [hd₁, kempeSwap_col, ne_eq, kempeSwapFun_isSome]
        exact hgood₀ u v huv hu hv
      -- the petal centres of `R` are ends of Kempe chains
      have hfree : ∀ x ∈ R, d₀.IsFree (pw x) β := by
        intro x hx u hu
        have hadj := d₀.col_adj hu
        rcases (hpy x (hRcore x hx)).2.2 u hadj with rfl | rfl
        · rw [d₀.col_symm, hd₀R _ _ hx] at hu; exact absurd hu (by simp)
        · have h1 : d₀.col (pw x) (py x) = some g := (hconst x hx).trans hg
          exact hβ (Option.some_injective _ (hu.symm.trans h1))
      -- the two cycle neighbours `a, b` of `r`
      obtain ⟨a, b, hab, hNr⟩ := card_eq_two.1 (hcn r hr)
      have ha : a ∈ coreNbrs G r := by rw [hNr]; simp
      have hb : b ∈ coreNbrs G r := by rw [hNr]; simp
      rw [mem_coreNbrs, hΔ] at ha hb
      have haR : a ∈ R := hrR.trans ((hKadj r a).2 ⟨ha.1, hr, ha.2⟩).reachable
      have hbR : b ∈ R := hrR.trans ((hKadj r b).2 ⟨hb.1, hr, hb.2⟩).reachable
      have hra : pw r ≠ pw a := fun h => ha.1.ne (hpw_inj r a hrR haR h)
      have hrb : pw r ≠ pw b := fun h => hb.1.ne (hpw_inj r b hrR hbR h)
      have habw : pw a ≠ pw b := fun h => hab (hpw_inj a b haR hbR h)
      have hdeg2 := kempe_degree_le_two d₀ g β
      have hd1 : ∀ x ∈ R, (d₀.kempeGraph g β).degree (pw x) ≤ 1 := fun x hx =>
        kempe_degree_le_one_of_isFree d₀ (Or.inr rfl) (hfree x hx)
      have hnot : ¬ ((d₀.kempeGraph g β).Reachable (pw r) (pw a) ∧
          (d₀.kempeGraph g β).Reachable (pw r) (pw b)) := fun h =>
        no_three_endpoints hdeg2 hra hrb habw (hd1 r hrR) (hd1 a haR) (hd1 b hbR) h.1 h.2
      have hFr : d₁.col (pw r) (py r) = some β := by
        rw [hd₁, kempeSwap_col, kempeSwapFun_of_reachable d₀ g β (Reachable.refl _)]
        rw [show d₀.col (pw r) (py r) = some g from hg]
        simp
      have hFx : ∀ x ∈ R, ¬ (d₀.kempeGraph g β).Reachable (pw r) (pw x) → d₁.col (pw x) (py x) = some g := by
        intro x hx hnr
        rw [hd₁, kempeSwap_col, kempeSwapFun_of_not_reachable d₀ g β hnr]
        exact (hconst x hx).trans hg
      refine ⟨d₁, hgood₁, r, hrR, ?_⟩
      by_cases hra' : (d₀.kempeGraph g β).Reachable (pw r) (pw a)
      · have hrb' : ¬ (d₀.kempeGraph g β).Reachable (pw r) (pw b) := fun h => hnot ⟨hra', h⟩
        refine ⟨b, hbR, ?_⟩
        rw [hFr, hFx b hbR hrb']
        exact fun h => hβ (Option.some_injective _ h)
      · refine ⟨a, haR, ?_⟩
        rw [hFr, hFx a haR hra']
        exact fun h => hβ (Option.some_injective _ h)
    · push Not at hconst
      obtain ⟨x, hx, hne⟩ := hconst
      exact ⟨d₀, hgood₀, x, hx, r, hrR, hne⟩
  obtain ⟨d, hd, x₁, hx₁, x₂, hx₂, hF12⟩ := step1
  -- step 2: two adjacent vertices of `R` with different far colours
  have step2 : ∃ x ∈ R, ∃ x', K.Adj x x' ∧ d.col (pw x) (py x) ≠ d.col (pw x') (py x') := by
    by_contra hall
    push Not at hall
    have hcst : ∀ v ∈ R, d.col (pw r) (py r) = d.col (pw v) (py v) := by
      intro v hv
      obtain ⟨q⟩ := (show K.Reachable r v from hv)
      exact eq_of_walk (fun v => d.col (pw v) (py v)) (fun x x' hx hxx' => hall x hx x' hxx') q (Reachable.refl r)
    exact hF12 ((hcst x₁ hx₁).symm.trans (hcst x₂ hx₂))
  obtain ⟨x, hx, x', hxx', hFx⟩ := step2
  have hx'R : x' ∈ R := (show K.Reachable r x from hx).trans hxx'.reachable
  -- the cycle through `x`
  have hRsupp : ∀ v, v ∈ R ↔ v ∈ (K.connectedComponentMk x).supp := by
    intro v
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    constructor
    · intro hv; exact (show K.Reachable r v from hv).symm.trans (show K.Reachable r x from hx)
    · intro hv; exact (show K.Reachable r x from hx).trans hv.symm
  -- main claim for an oriented cycle ending in `x'`
  have main : ∀ q : K.Walk x x, q.IsCycle → q.toSubgraph.verts = (K.connectedComponentMk x).supp →
      q.getVert (q.length - 1) = x' → False := by
    intro q hq hqv hqx'
    have hRq : ∀ v, v ∈ R ↔ v ∈ q.support := by
      intro v; rw [hRsupp, ← hqv, Walk.mem_verts_toSubgraph]
    have hRR : ∀ u v, u ∈ R → v ∈ R → G.Adj u v → q.toSubgraph.Adj u v := by
      intro u v hu hv huv
      have hK : K.Adj u v := (hKadj u v).2 ⟨huv, hRcore u hu, hRcore v hv⟩
      exact (hq.adj_toSubgraph_iff_of_isCycles hKcyc
        (by rw [Walk.mem_verts_toSubgraph]; exact (hRq u).1 hu) v).2 hK
    have hk := three_le hq
    set k := q.length with hkdef
    let Fn : ℕ → Fin 3 := fun i => (d.col (pw (q.getVert i)) (py (q.getVert i))).getD 0
    have hFn : ∀ v ∈ R, d.col (pw v) (py v) = some (Fn (idx q v)) := by
      intro v hv
      have := getVert_idx hq ((hRq v).1 hv)
      simp only [Fn, this]
      obtain ⟨γ, hγ⟩ := Option.ne_none_iff_exists'.1 (hFsome d hd v hv)
      rw [hγ]; rfl
    have hFend : Fn (k - 1) ≠ Fn 0 := by
      intro h
      apply hFx
      have h1 := hFn x hx
      have h2 := hFn x' hx'R
      rw [show idx q x = 0 by
        have := idx_getVert hq (show 0 < k by omega); rwa [Walk.getVert_zero] at this] at h1
      rw [show idx q x' = k - 1 by
        have := idx_getVert hq (show k - 1 < k by omega); rwa [hqx'] at this] at h2
      rw [h1, h2, h]
    obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_cycle_colouring k (by omega) Fn hFend
    apply hcl3
    refine colorable_of_cycle_colouring hq R hRq pw py hRR hRout hpw_inj hpy' d hd c
      (fun i hi => ?_) (fun v hv => ?_)
    · unfold prevI
      split_ifs with h0
      · subst h0; exact hc2
      · exact hc1 i (by omega) hi
    · rw [hFn v hv]
      intro h
      have h' := Option.some_injective _ h
      have hi := idx_lt hq ((hRq v).1 hv)
      set i := idx q v
      have hne : c (prevI k i) ≠ c i := by
        unfold prevI; split_ifs with h0
        · rw [h0]; exact hc2
        · exact hc1 i (by omega) hi
      have hsee : Fn i = c (prevI k i) ∨ Fn i = c i := by
        unfold prevI; split_ifs with h0
        · rw [h0]; exact hc4
        · exact hc3 i (by omega) hi
      exact (third_ne_iff _ _ _ hne).2 hsee h'.symm
  -- orient the cycle
  obtain ⟨p, hp, hpv⟩ := hKcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := K.connectedComponentMk x) (by rw [ConnectedComponent.mem_supp_iff]) ⟨x', hxx'⟩
  have hpadj : p.toSubgraph.Adj x x' :=
    (hp.adj_toSubgraph_iff_of_isCycles hKcyc (by simp) x').2 hxx'
  have hk := three_le hp
  obtain ⟨i, hi, h⟩ := exists_of_toSubgraph_adj hp hpadj
  have hx0 : p.getVert 0 = x := Walk.getVert_zero p
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `x' = p.getVert 1`: reverse the cycle
    have hi0 : i = 0 := getVert_inj hp hi (by omega) (h1.symm.trans hx0.symm)
    subst hi0
    refine main p.reverse hp.reverse (by rw [Walk.toSubgraph_reverse]; exact hpv) ?_
    rw [Walk.getVert_reverse, Walk.length_reverse, h2, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < p.length)]
    congr 1; omega
  · have : (i + 1) % p.length = 0 := by
      apply getVert_inj hp (Nat.mod_lt _ (by omega)) (by omega)
      rw [← h2, hx0]
    have hik : i = p.length - 1 := by
      rw [succ_mod_eq hi] at this; split_ifs at this with h <;> omega
    subst hik
    exact main p hp hpv h1.symm

end Main

end CoreDeg2Lib
