# Graphs whose core has maximum degree two (Hilton–Zhao; Cariolaro–Cariolaro, partial)

Lean 4 / Mathlib formalization of results on finite simple graphs `G` whose *core* (the subgraph
induced by the vertices of maximum degree `Δ`) has maximum degree at most two.

* **Hilton–Zhao (1992).** If `G` is connected and of class two, then `G` is `Δ`-critical, every
  vertex has at least two neighbours of degree `Δ` (so the core is `2`-regular), and the minimum
  degree is at least `Δ − 1`, exactly `Δ − 1` when `Δ ≥ 3`. Corollaries: `G` is of class one as
  soon as some vertex of degree `Δ` has at most one neighbour of degree `Δ`, or some vertex has
  degree at most `Δ − 2`.
* **`Δ = 3`.** A connected class-two graph is a *petal graph* (Cariolaro–Cariolaro, Lemma 3), and
  `3 |E| = 4 |V|`; hence `3 |E| ≠ 4 |V|` forces class one.
* **`Δ = 3`, one core cycle without internal petals forces class one** (Cariolaro–Cariolaro,
  Lemma 7, strengthened from "no internal petal anywhere" to "some core cycle has none").
* **`P*`**, the Petersen graph minus a vertex, defined on `Fin 9` and proved isomorphic to the
  Petersen graph minus a vertex: it satisfies the hypotheses, is connected, of class two and not
  overfull.

Not formalized: the full Cariolaro–Cariolaro theorem (`Δ = 3`, `G ≠ P*` ⇒ class one), whose
remaining case is a petal graph in which every core cycle carries an internal petal. See
`NOTES.md` for the exact statements from the sources.

Class one is `G.lineGraph.Colorable G.maxDegree`. The core condition is stated as
`∀ v, G.degree v = G.maxDegree → #((G.neighborFinset v).filter fun u => G.degree u = G.maxDegree) ≤ 2`.

Vizing's theorem and Vizing's adjacency lemma are imported as lake dependencies from the
registered entries PALOMAR-2026-10-15-000004 (jtraverso/vizing) and PALOMAR-2026-11-04-000009
(jtraverso/overfull-critical-graphs).

Statements: `CoreDeg2Challenge.lean`; proofs: `CoreDeg2Solution.lean` and `CoreDeg2/`.

License: Apache 2.0.
