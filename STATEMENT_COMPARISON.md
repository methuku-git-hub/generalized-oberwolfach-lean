# Comparison of the main theorem with the manuscript

This is an agent-produced comparison for review, not an independent human
mathematical endorsement or a Palomar Comparator verdict. It concerns only the
main prescribed-factor theorem, not every corollary or proof in the manuscript.

The final manuscript supplied by Abhishek Methuku is `source/manuscript.tex`,
SHA-256 `5f9cef1149b88a3680cc5ccf193b7a68a18fd12105ab6c495f4f23d893e772d9`.
Its theorem labelled `thm:new:prescribed-factor` occurs at lines 297–305; its
ordinary cycle threshold is defined at line 229, the edge-partition convention
at lines 291–294, and the finite simple graph convention at line 1643.

The earlier development manuscript was a different file, SHA-256
`ffe45b31bcfbd933828da22a9becb6aea23a642d5ffe7abf09d29f45d9d8a201`.
The two main-theorem passages are identical after normalizing LaTeX math
delimiters; their full manuscript sources are not identical. The final
manuscript theorem passage is byte-identical to the corresponding passage in a
separately audited 4 November manuscript (full-file SHA-256
`aa3e013274e13487bbafb857336eda2ce96e2086735bfd4f2137bc35e7faedbd`).

| Manuscript requirement | Formal representation | Comparison |
| --- | --- | --- |
| Every positive margin has a sufficiently large order threshold uniform over allowed sets and factor lists. | `MainTheorem` quantifies `α`, then `N`, then `S`, `n`, `D`, the factors and the host. | The order threshold is chosen before `S` and the factors. |
| Allowed lengths form a nonempty subset of the integers at least three, possibly infinite. | `S : Set ℕ`, `S.Nonempty`, and `∀ r ∈ S, 3 ≤ r`. | The formal set is unrestricted in cardinality. |
| The host has `n` vertices, is `D`-regular, `D` is even, and `D ≥ (δ_S + α)n`. | `SimpleGraph (Fin n)`, `IsRegularOfDegree D`, `Even D`, and the real inequality in `DecompositionAt`. | Natural degrees are cast to reals in the same direction. Any finite `n`-vertex graph can be relabelled by `Fin n`. |
| The prescribed list has `D/2` labelled `n`-vertex 2-regular factors, with all component lengths in `S`. | `Fin (D / 2) → SimpleGraph (Fin n)`, regularity of degree 2, and `AllowedCycleLengths`. | Each reachable-set cardinality records its connected-component size. A separate Lean check shows that every component of a finite 2-regular graph is a cycle and has no additional component edges. |
| The host edges partition into subgraphs isomorphic to the prescribed factors. | `HasFactorDecomposition`, `EdgePartition`, and graph isomorphisms. | The partition is stated for every ordered pair of vertices; symmetry of simple graph adjacency makes this equivalent to partitioning undirected edges. Separate Lean checks establish containment and uniqueness of each piece. |
| `δ_{C_r}` is the infimum of admissible `d ∈ [0,1]` for sufficiently large divisible graphs, and `δ_S` is the supremum over `r ∈ S`. | `CycleDivisible`, `HasCycleDecomposition`, `AdmissibleCycleBound`, `cycleThreshold`, and `allowedThreshold`. | The degree and edge-divisibility conditions agree. A separate Lean check identifies `IsCycleCopy` exactly with an injected copy of Mathlib's `cycleGraph r`, with vertices outside the copy isolated. Other checks show `1` is admissible, every cycle threshold lies in `[0,1]`, and, for nonempty `S`, so does `allowedThreshold S`. |

The additional checked interpretations are in `StatementReview.lean`. They were
checked locally against the previously built candidate's Challenge and Mathlib;
that is not a fresh build of this repository snapshot. Their axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`; the elementary
partition lemmas are axiom-free. As usual, the cycle length is the number of
vertices in the cycle. These checks do not replace the complete mechanical
Challenge/Solution comparison or a qualified human comparison with the paper.

The formal threshold condition uses a pointwise degree bound rather than a
minimum-degree operator. For nonempty graphs these formulations agree. The
asymptotic order threshold can always be enlarged to at least one, so the
convention for the empty graph does not change the theorem. For positive order,
the checked nonnegativity of `δ_S` and the positive margin force the even degree
in the theorem to be positive, regardless of whether a reader's convention for
`2ℕ` includes zero. The formal definitions allow an empty cycle decomposition
of an edgeless graph, as the usual edge-partition definition does.

`Challenge.lean` deliberately contains a theorem placeholder for the comparison.
The locally checked proof is the corresponding theorem imported by
`Solution.lean`. The final source package, including this comparison and the
user-supplied manuscript, still requires checks on its exact eventual commit.
