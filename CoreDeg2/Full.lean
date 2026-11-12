/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CoreDeg2.NoInternal
public import CoreDeg2.Assemble2
public import CoreDeg2.HexIso
public import CoreDeg2.Chord.Main

/-!
# The Cariolaro–Cariolaro theorem

**Theorem** (`cariolaro`). A connected graph with `Δ = 3` whose core has maximum degree at most two
and which is not `3`-edge-colourable is isomorphic to `P*`.

Proof. `G` is a critical petal graph (Hilton–Zhao). Take a core cycle `R` (a cycle walk `p` of
length `k`), a colouring `d` of the edges not meeting `R` (criticality), and encode `R` as an
instance of the chorded-cycle problem: vertex `i` carries a label (shared with the vertex at the
other end of its petal) if its petal is internal, and otherwise the restriction `ext F`, `F` the
colour of the far petal edge. If the instance is solvable, `G` is `3`-edge-colourable
(`colorable_of_cycle_colouring'`). Otherwise it is exceptional: (E1) `R` has no internal petal,
excluded by `colorable_of_noInternalPetal`; (E2) the hexagon with antipodal petals, and then `G`
is `P*` (`iso_of_hex`); (E3) is impossible since `k ≥ 3`.
-/

@[expose] public section

namespace CoreDeg2Lib

open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CycleWalk Chord

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Cariolaro–Cariolaro (2003), Theorems 1–2.** -/
theorem cariolaro (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hcore : CoreLeTwo G) (hΔ : G.maxDegree = 3) (hcl3 : ¬ G.lineGraph.Colorable 3) :
    Nonempty (pStarL ≃g G) := by
  classical
  have hcl : ¬ G.lineGraph.Colorable G.maxDegree := by rwa [hΔ]
  have hcrit := isDeltaCritical G hconn hcore hcl
  obtain ⟨hdeg, hcn, hnb⟩ := petal_structure G hconn hcore hcl hΔ
  -- a vertex of degree three
  obtain ⟨r, hr⟩ : ∃ r, G.degree r = 3 := by
    have : Nonempty V := hconn.nonempty
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    exact ⟨v, hv.symm.trans hΔ⟩
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
  set R : Set V := {v | K.Reachable r v} with hRdef
  have hRcore : ∀ v ∈ R, G.degree v = 3 := by
    intro v hv
    obtain ⟨q⟩ := (show K.Reachable r v from hv)
    have := degree_eq_of_walk q (by rw [hΔ]; exact hr)
    rwa [hΔ] at this
  have hrR : r ∈ R := Reachable.refl r
  -- petal centres and far ends
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
      have hw2 : G.degree (pw x) = 2 := by
        rcases hdeg (pw x) with h | h <;> [exact h; exact absurd h hw3]
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
  have hRout : ∀ u v, u ∈ R → v ∉ R → G.Adj u v → v = pw u := by
    intro u v hu hv huv
    have hu3 := hRcore u hu
    refine (hpw u hu3).2.2 v huv fun hv3 => hv ?_
    exact (show K.Reachable r u from hu).trans ((hKadj u v).2 ⟨huv, hu3, hv3⟩).reachable
  -- the far end is a core vertex; internal petals are symmetric
  have hpy3 : ∀ x ∈ R, G.degree (py x) = 3 := fun x hx => by
    have hw2 : G.degree (pw x) = 2 := by
      rcases hdeg (pw x) with h | h <;> [exact h; exact absurd h (hpw x (hRcore x hx)).2.1]
    exact hnb (pw x) (py x) hw2 (hpy x (hRcore x hx)).1
  have hpwpy : ∀ x ∈ R, py x ∈ R → pw (py x) = pw x := fun x hx hyR =>
    ((hpw (py x) (hRcore _ hyR)).2.2 (pw x) (hpy x (hRcore x hx)).1.symm
      (hpw x (hRcore x hx)).2.1).symm
  have hpypy : ∀ x ∈ R, py x ∈ R → py (py x) = x := by
    intro x hx hyR
    have h1 := (hpy (py x) (hRcore _ hyR))
    rw [hpwpy x hx hyR] at h1
    rcases (hpy x (hRcore x hx)).2.2 (py (py x)) h1.1 with h | h
    · exact h
    · exact absurd h h1.2.1
  -- a colouring of the rest
  let Good : PEC G (Fin 3) → Prop := fun d => ∀ u v, G.Adj u v → u ∉ R → v ∉ R → d.col u v ≠ none
  obtain ⟨r', hr'⟩ : (coreNbrs G r).Nonempty := card_pos.1 (by rw [hcn r hr]; omega)
  rw [mem_coreNbrs] at hr'
  have hdel : (G.deleteEdges {s(r, r')}).lineGraph.Colorable 3 := by
    rw [← hΔ]; exact hcrit.2.2 s(r, r') hr'.1
  obtain ⟨c₀, hc₀⟩ := exists_colMinus_of_colorable hr'.1 hdel
  set d := restrictPEC c₀ R with hd₀
  have hdcol : ∀ u v, u ∉ R → v ∉ R → d.col u v = c₀.col u v := by
    intro u v hu hv
    show (if u ∈ R ∨ v ∈ R then none else c₀.col u v) = c₀.col u v
    rw [if_neg (by tauto)]
  have hgood : Good d := by
    intro u v huv hu hv
    rw [hdcol u v hu hv]
    refine hc₀.total u v huv fun h => ?_
    have : r ∈ s(u, v) := by rw [h]; exact Sym2.mem_mk_left r r'
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact hu hrR
    · exact hv hrR
  -- the cycle
  obtain ⟨r'', hrr''⟩ : (K.neighborSet r).Nonempty :=
    ⟨r', (hKadj r r').2 ⟨hr'.1, hr, hr'.2.trans hΔ⟩⟩
  obtain ⟨p, hp, hpv⟩ := hKcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := K.connectedComponentMk r) (by rw [ConnectedComponent.mem_supp_iff]) ⟨r'', hrr''⟩
  have hRp : ∀ v, v ∈ R ↔ v ∈ p.support := by
    intro v
    rw [← Walk.mem_verts_toSubgraph, hpv, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact ⟨fun h => (show K.Reachable r v from h).symm, fun h => h.symm⟩
  have hRR : ∀ u v, u ∈ R → v ∈ R → G.Adj u v → p.toSubgraph.Adj u v := by
    intro u v hu hv huv
    exact (hp.adj_toSubgraph_iff_of_isCycles hKcyc
      (by rw [Walk.mem_verts_toSubgraph]; exact (hRp u).1 hu) v).2
      ((hKadj u v).2 ⟨huv, hRcore u hu, hRcore v hv⟩)
  have hk3 := three_le hp
  set k := p.length with hkdef
  have hxR : ∀ i, p.getVert i ∈ R := fun i => (hRp _).2 (getVert_mem_support hp i)
  -- the instance
  let ty : ℕ → VT := fun i =>
    if py (p.getVert i) ∈ R then .lab (min i (idx p (py (p.getVert i))))
    else .ext ((d.col (pw (p.getVert i)) (py (p.getVert i))).getD 0)
  -- equal labels come from the two ends of an internal petal
  have hlab : ∀ i j, i < k → j < k → i ≠ j → ∀ L, ty i = .lab L → ty j = .lab L →
      j = idx p (py (p.getVert i)) := by
    intro i j hi hj hij L h1 h2
    simp only [ty] at h1 h2
    split_ifs at h1 h2 with hyi hyj
    have h2 : min i (idx p (py (p.getVert i))) = min j (idx p (py (p.getVert j))) :=
      (VT.lab.inj h1).trans (VT.lab.inj h2).symm
    have hai := idx_lt hp ((hRp _).1 hyi)
    have hbj := idx_lt hp ((hRp _).1 hyj)
    have hgi := getVert_idx hp ((hRp _).1 hyi)
    have hgj := getVert_idx hp ((hRp _).1 hyj)
    rcases Nat.le_total i (idx p (py (p.getVert i))) with hia | hia <;>
      rcases Nat.le_total j (idx p (py (p.getVert j))) with hjb | hjb
    · rw [Nat.min_eq_left hia, Nat.min_eq_left hjb] at h2; exact absurd h2 hij
    · rw [Nat.min_eq_left hia, Nat.min_eq_right hjb] at h2
      -- `i = idx (py x_j)`: `x_i = py x_j`
      have : p.getVert i = py (p.getVert j) := by rw [h2, hgj]
      have := congrArg py this
      rw [hpypy _ (hxR j) hyj] at this
      rw [this, idx_getVert hp hj]
    · rw [Nat.min_eq_right hia, Nat.min_eq_left hjb] at h2; exact h2.symm
    · rw [Nat.min_eq_right hia, Nat.min_eq_right hjb] at h2
      have : py (p.getVert i) = py (p.getVert j) := by rw [← hgi, ← hgj, h2]
      have := congrArg py this
      rw [hpypy _ (hxR i) hyi, hpypy _ (hxR j) hyj] at this
      exact absurd (getVert_inj hp hi hj this) hij
  have hwf : WFf k ty := by
    intro i j h ⟨hi, hj, hij, L, h1, h2⟩ ⟨_, hh, hjh, L', h3, h4⟩ hih
    rw [h2] at h3; cases h3
    have e1 := hlab i j hi hj hij L h1 h2
    have e2 := hlab i h hi hh hih L h1 h4
    exact hjh (e1.trans e2.symm)
  by_cases hE1 : E1F k ty
  · -- no internal petal: Lemma 7
    exfalso
    apply hcl3
    refine colorable_of_noInternalPetal G hconn hcore hΔ hr fun w x y hwx hwy hxy hw3 hx hy => ?_
    have hwR : w ∉ R := fun h => hw3 (hRcore w h)
    have hxw := hRout x w hx hwR hwx.symm
    subst hxw
    rcases (hpy x (hRcore x hx)).2.2 y hwy with rfl | rfl
    · exact hxy rfl
    · apply hE1.1 (idx p x) (idx_lt hp ((hRp x).1 hx)) (min (idx p x) (idx p (py x)))
      show (if py (p.getVert (idx p x)) ∈ R then _ else _) = _
      rw [getVert_idx hp ((hRp x).1 hx), if_pos (show py x ∈ R from hy)]
  by_cases hhex : HexF k ty
  · -- the hexagon: `G ≅ P*`
    have hk6 : k = 6 := hhex.1
    have hpyx : ∀ i < 3, py (p.getVert i) = p.getVert (i + 3) := by
      intro i hi
      obtain ⟨-, -, hne, L, h1, h2⟩ := hhex.2 i hi
      have := hlab i (i + 3) (by omega) (by omega) hne L h1 h2
      rw [this, getVert_idx hp ((hRp _).1 (by
        simp only [ty] at h1; split_ifs at h1 with h; exact h))]
    have hpyR : ∀ i < 3, py (p.getVert i) ∈ R := fun i hi => by rw [hpyx i hi]; exact hxR _
    refine (iso_of_hex p.getVert (fun c => pw (p.getVert c)) (fun a b ha hb h => getVert_inj hp
      (by omega) (by omega) h) ?_ ?_ ?_ ?_ ?_ ?_).elim fun e => ⟨e⟩
    · -- cycle adjacency
      intro a b ha hb
      constructor
      · intro hab
        have := idx_of_toSubgraph_adj hp (hRR _ _ (hxR a) (hxR b) hab)
        rw [idx_getVert hp (by omega), idx_getVert hp (by omega), ← hkdef, hk6] at this
        exact this
      · rintro (h | h)
        · have := adj_succ hp (show a < p.length by omega)
          rw [← hkdef, hk6, ← h] at this
          exact ((hKadj _ _).1 this).1
        · have := adj_succ hp (show b < p.length by omega)
          rw [← hkdef, hk6, ← h] at this
          exact ((hKadj _ _).1 this).1.symm
    · -- hexagon vertices and petal centres
      intro a c ha hc
      constructor
      · intro h
        have hwR : pw (p.getVert c) ∉ R := hpwR _ (hxR c)
        have h1 := hRout _ _ (hxR a) hwR h
        -- `p.getVert a` is a neighbour of the petal centre of `x c`
        have h2 : G.Adj (pw (p.getVert c)) (p.getVert a) := h.symm
        rcases (hpy (p.getVert c) (hRcore _ (hxR c))).2.2 _ h2 with h3 | h3
        · have := getVert_inj hp (by omega) (by omega) h3; omega
        · rw [hpyx c hc] at h3
          have := getVert_inj hp (by omega) (by omega) h3; omega
      · intro h
        rcases Nat.lt_or_ge a 3 with h3 | h3
        · rw [show c = a by omega]; exact (hpw _ (hRcore _ (hxR a))).1
        · have : p.getVert a = py (p.getVert c) := by rw [hpyx c hc, show c + 3 = a by omega]
          rw [this]; exact (hpy (p.getVert c) (hRcore _ (hxR c))).1.symm
    · -- petal centres are not adjacent
      intro c c' hc hc' h
      have hw2 : G.degree (pw (p.getVert c)) = 2 := by
        rcases hdeg (pw (p.getVert c)) with h' | h' <;> [exact h'; exact absurd h' (hpw _ (hRcore _ (hxR c))).2.1]
      exact (hpw _ (hRcore _ (hxR c'))).2.1 (hnb _ _ hw2 h)
    · intro c a hc ha h
      exact hpwR _ (hxR c) (h ▸ hxR a)
    · intro c c' hc hc' h
      by_contra hne
      have h1 : G.Adj (pw (p.getVert c)) (p.getVert c') := by rw [h]; exact (hpw _ (hRcore _ (hxR c'))).1.symm
      rcases (hpy (p.getVert c) (hRcore _ (hxR c))).2.2 _ h1 with h3 | h3
      · exact hne (getVert_inj hp (by omega) (by omega) h3).symm
      · rw [hpyx c hc] at h3
        have := getVert_inj hp (by omega) (by omega) h3; omega
    · -- every vertex is in the hexagon or a petal centre
      let S : Set V := {v | (∃ a, a < 6 ∧ v = p.getVert a) ∨ (∃ c, c < 3 ∧ v = pw (p.getVert c))}
      have hclosed : ∀ u v, u ∈ S → G.Adj u v → v ∈ S := by
        rintro u v (⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩) huv
        · by_cases hvR : v ∈ R
          · refine Or.inl ⟨idx p v, by rw [← hk6]; exact idx_lt hp ((hRp v).1 hvR), ?_⟩
            exact (getVert_idx hp ((hRp v).1 hvR)).symm
          · have := hRout _ _ (hxR a) hvR huv
            refine Or.inr ⟨a % 3, by omega, ?_⟩
            rw [this]
            rcases Nat.lt_or_ge a 3 with h3 | h3
            · rw [Nat.mod_eq_of_lt h3]
            · have e := hpyx (a % 3) (by omega)
              rw [show a % 3 + 3 = a by omega] at e
              rw [← e, hpwpy _ (hxR _) (hpyR _ (by omega))]
        · rcases (hpy (p.getVert c) (hRcore _ (hxR c))).2.2 v huv with rfl | rfl
          · exact Or.inl ⟨c, by omega, rfl⟩
          · exact Or.inl ⟨c + 3, by omega, hpyx c hc⟩
      have hS0 : p.getVert 0 ∈ S := Or.inl ⟨0, by omega, rfl⟩
      intro v
      obtain ⟨q⟩ := hconn.preconnected (p.getVert 0) v
      suffices ∀ a b (q : G.Walk a b), a ∈ S → b ∈ S from this _ _ q hS0
      intro a b q
      induction q with
      | nil => exact id
      | cons h _ ih => exact fun ha => ih (hclosed _ _ ha h)
  -- otherwise the instance is solvable
  exfalso
  obtain ⟨c, hc1, hc2, hc3⟩ := solv_main k ty (by omega) hwf hE1 hhex (by omega)
  apply hcl3
  have hidx : ∀ v ∈ R, p.getVert (idx p v) = v := fun v hv => getVert_idx hp ((hRp v).1 hv)
  refine colorable_of_cycle_colouring' hp R hRp pw hRR hRout d hgood c hc1 ?_ ?_
  · -- two cycle neighbours of a petal centre: the ends of an internal petal
    intro u v v' hu hv hv' huv huv' hne
    have h1 := hRout v u hv hu huv.symm
    subst h1
    rcases (hpy v (hRcore v hv)).2.2 v' huv' with rfl | rfl
    · exact absurd rfl hne
    · have hiv := idx_lt hp ((hRp v).1 hv)
      have hiv' := idx_lt hp ((hRp _).1 hv')
      have hty1 : ty (idx p v) = .lab (min (idx p v) (idx p (py v))) := by
        simp only [ty, hidx v hv, if_pos hv']
      have hty2 : ty (idx p (py v)) = .lab (min (idx p v) (idx p (py v))) := by
        simp only [ty, hidx _ hv', hpypy v hv hv', if_pos hv, min_comm]
      have hne' : idx p v ≠ idx p (py v) := fun h => hne (idx_inj hp ((hRp v).1 hv)
        ((hRp _).1 hv') h)
      exact hc3 _ _ hiv hiv' hne' _ hty1 hty2
  · -- a cycle vertex and the far end of its external petal
    intro u v z hu hv hz huv huz
    have h1 := hRout v u hv hu huv.symm
    subst h1
    rcases (hpy v (hRcore v hv)).2.2 z huz with rfl | rfl
    · exact absurd hv hz
    · have hiv := idx_lt hp ((hRp v).1 hv)
      obtain ⟨F, hF⟩ := Option.ne_none_iff_exists'.1
        (hgood _ _ (hpy v (hRcore v hv)).1 (hpwR v hv) hz)
      have hty : ty (idx p v) = .ext F := by simp only [ty, hidx v hv, if_neg hz, hF]; rfl
      rw [hF]
      intro h
      exact hc2 _ hiv F hty (Option.some_injective _ h).symm

end CoreDeg2Lib
