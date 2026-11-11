# Notes: sources and exact statements

## Sources consulted (2026-11-11)

* D. Cariolaro, G. Cariolaro, *Colouring the petals of a graph*, Electron. J. Combin. 10 (2003)
  #R6 (open access; local copy `C:\lean\hilton_zhao_downloads\cc2003.pdf`).
* D. W. Cranston, L. Rabern, *The Hilton–Zhao conjecture is true for graphs with maximum degree 4*,
  arXiv:1703.00959 (SIAM J. Discrete Math. 2019) (local copy `cr2017.pdf`).
* Y. Cao, G. Chen, G. Jing, S. Shan, *The core conjecture of Hilton and Zhao II: a proof*,
  arXiv:2108.04399 (abstract only).
* The two Hilton–Zhao papers themselves (Discrete Math. 101 (1992) 135–147; JCMCC 21 (1996)
  97–108) were not accessed; their statements are taken from the citations below.

## What Hilton and Zhao proved, and what they conjectured

The task description attributes to Hilton–Zhao 1996 a theorem "Δ(G_Δ) ≤ 2 ⇒ (Class 2 ⇔ overfull
or P*)". That is **not** a theorem of the 1996 paper: it is the *Hilton–Zhao core conjecture*,
posed there. Exact wording as quoted by Cariolaro–Cariolaro (Conjecture 1):

> Let G be a connected graph such that Δ(G_Δ) ≤ 2. Let G ≠ P*. Then G is Class 2 if and only if
> G is overfull.

(Cranston–Rabern add Δ ≥ 3; Cao–Chen–Jing–Shan: "if G is a simple connected graph with Δ ≥ 3 and
Δ(G_Δ) ≤ 2, then χ'(G) = Δ + 1 implies that G is overfull or G = P*".) It was proved for Δ = 3 by
Cariolaro–Cariolaro (2003; alternative proof by Král', Sereni, Stiebitz in the Stiebitz–Scheide–
Toft–Favrholdt book, pp. 57–63), for Δ = 4 by Cranston–Rabern, and for all Δ ≥ 4 by
Cao–Chen–Jing–Shan.

The **theorem** of Hilton and Zhao that is used everywhere is from the 1992 paper (Discrete Math.
101), quoted by Cariolaro–Cariolaro as Lemma 2:

> Let G be a connected Class 2 graph with Δ(G_Δ) ≤ 2. Then: 1. G is critical; 2. Δ(G_Δ) = 2;
> 3. δ(G) = Δ(G) − 1, unless G is an odd cycle; 4. ∂(G_Δ) = V(G).

and by Cranston–Rabern (Lemma 1, with proof) as: if G is connected with maximum degree k ≥ 3, core
of maximum degree ≤ 2 and χ'(G) > k, then G is critical, has minimum degree k − 1, its core is a
disjoint union of cycles, and every vertex has a Δ-neighbour. Vizing's adjacency lemma moreover
gives every vertex two Δ-neighbours (Cariolaro–Cariolaro, Lemma 1).

This is what part (a) formalizes (`hiltonZhao_*`): criticality, every vertex has ≥ 2 neighbours of
degree Δ (hence the core is 2-regular, i.e. a disjoint union of cycles, and item 4), minimum
degree ≥ Δ − 1, and = Δ − 1 when Δ ≥ 3 (for Δ ≤ 2 the class-two graphs are odd cycles; that
item is not stated).

## Cariolaro–Cariolaro 2003, exact statements

* Petal graph: connected, Δ = 3, δ = 2, G_Δ 2-regular, every edge meets G_Δ.
* Lemma 3: a connected Class 2 graph with Δ = 3 and Δ(G_Δ) ≤ 2 is a petal graph.
* Lemma 7: a petal graph with p(G) = ∞ (no petal has both base points on the same core cycle) is
  Class 1.
* Theorem 1: G connected, Δ(G_Δ) ≤ 2, Δ(G) = 3, G ≠ P* ⇒ Class 1.
* Theorem 2: a petal graph G ≠ P* is Class 1.

Formalized: Lemma 3 (`petal_structure`), a counting consequence (`3|E| = 4|V|`), and a
strengthening of Lemma 7 to a single core cycle (`colorable_of_noInternalPetal`: one core cycle
without internal petals suffices). The proof of Lemma 7 here is not the paper's (which uses its
path-colouring Lemma 4 on G minus the cycle): it recolours the whole cycle through a transfer
argument along the cycle (`exists_cycle_colouring`: every vertex can be made to see a prescribed
colour as soon as the prescribed colours are not all equal) and, when they are all equal, uses a
single Kempe swap and the fact that a Kempe chain has only two ends (registered
`LeanPool.Vizing.no_three_endpoints`).

Not formalized: Theorems 1 and 2 in full, i.e. the case where every core cycle carries an internal
petal (paper: Lemmas 5, 6 and the p ≥ 3 part of the proof of Theorem 2, which for p = 3 is an
induction on the order through a graph surgery — delete the four base points of a 3-petal, join
their outer neighbours, merge two petal centres — plus the case analysis "G* = P*" of Fig. 3).
See the report for the precise wall.

## P*

`pStar` on `Fin 9`: hexagon 0-1-2-3-4-5, petal centres 6, 7, 8 on the antipodal pairs
{0,3}, {1,4}, {2,5}; proved isomorphic to the Petersen graph (outer 5-cycle, spokes i–i+5, inner
pentagram 5-7-9-6-8) minus vertex 0. Class 2 by a pruned finite check (`decide`, 12 edge colours),
not overfull (|E| = 12 = 3·⌊9/2⌋).

## Plan for the full Cariolaro–Cariolaro theorem (2026-11-11, second session)

Reduction already done: in a critical petal graph `H ≠ P*`, a core cycle `R` without internal
petals is impossible (`colorable_of_noInternalPetal`). If `R` carries an internal petal, uncolour
the edges at `R` in a colouring of `H − e` (criticality) and recolour `R`; this is the
*chorded-cycle lemma* below, applied to the cyclic sequence of `R` with chords = internal petals and
external restrictions = colours of the far petal edges. Only the hexagon with three antipodal
chords is excluded, and then `H ≅ P*` (connectedness).

**Chorded-cycle lemma** (combinatorial, on lists). A cyclic list of vertex types `ext a`
(missing colour ≠ a) or `lab l` (vertices with equal label miss different colours; a label used
once = free vertex). A solution: a proper cyclic edge colouring (pairs (in, out) per vertex).
Claim: every well-formed instance of length ≥ 2 is solvable unless (E1) no label repeated, no free
vertex, odd length, all ext equal; (E2) the hexagon with antipodal labels; (E3) length 2 with a
repeated label. Strong induction on the length with *safe reductions* (every solution of the
reduced instance extends), all verified by brute force before formalizing:
1. chord at distance 1 → one free vertex;
2. chord at distance 2 (x z y) → one free vertex, the partner of z becomes free;
3. a free vertex w and a neighbour v (a chord end if possible) → delete both;
4. minimal chord at distance p ≥ 3 (no free vertex): replace the arc x a₁ … a_{p−1} y by one
   vertex `ext a`, the partners of a₁, a_{p−1} get `ext a`, the other partners become free
   (safe by the arc lemma: the arc can be coloured unless t₁ = κ₁ and t_{p−1} = κ₂, where κ are the
   boundary colours and t the restrictions); fallback for the parity case: delete the arc
   (safe when t₁ ≠ t_{p−1}).
The arc lemmas hold for every p: a finite automaton on 9-bit states (pairs (first colour, current
colour)), whose reachable states are enumerated and checked with `decide`.
Chordless instances: the existing cycle-colouring lemma (non-constant restrictions), extended to
free vertices; constant even: alternate. Estimated size ≈ 4–5k lines including the graph bridge
(general assembly with internal petals, hexagon ⇒ `G ≅ P*`).
