# Prescribed 2-factor decompositions in Lean

This repository contains a Lean 4 and Mathlib formalization of the main theorem
of *Sharp Dirac thresholds for the generalized Oberwolfach problem*, by Dong Yeap
Kang, Abhishek Methuku and Pablo Oviedo. The formal target is
`Oberwolfach.MainTheorem`, and the proved endpoint is
`Oberwolfach.mainTheoremProof`. The project formalizes this theorem and supporting
material.

## The mathematical statement

For each integer $r \ge 3$, let $\delta_{C_r}$ be the ordinary
$C_r$-decomposition threshold: the infimum of the numbers $d\in[0,1]$ such that,
for all sufficiently large $n$, every $n$-vertex simple graph with minimum degree
at least $dn$, all degrees even and $r$ dividing its number of edges has an
edge-decomposition into copies of $C_r$. For a nonempty set
$S\subseteq\lbrace 3,4,\ldots\rbrace$, put
$\delta_S=\sup_{r\in S}\delta_{C_r}$.

**Theorem.** For every $\alpha>0$ there is an integer $N=N(\alpha)$ such that,
for every nonempty $S\subseteq\lbrace 3,4,\ldots\rbrace$ and every $n\ge N$, the following
holds. Let $D$ be even and let $G$ be an $n$-vertex simple $D$-regular graph
with

$$D\ge(\delta_S+\alpha)n.$$

For every prescribed list $F_1,\ldots,F_{D/2}$ of $2$-regular $n$-vertex
graphs whose cycle lengths all belong to $S$, the edges of $G$ can be partitioned
into spanning subgraphs $G_1,\ldots,G_{D/2}$ with $G_i\cong F_i$ for each $i$.
The choice of $N$ is uniform over $S$ and the prescribed factors; $S$ may be
infinite.

### Exact Lean statement

The following snippets occur inside the existing `Oberwolfach` namespace. The
target [`MainTheorem`](Challenge.lean#L70) chooses `N` before `S`:

```lean
def MainTheorem : Prop :=
  ∀ α : ℝ, 0 < α → ∃ N : ℕ, ∀ S : Set ℕ,
    S.Nonempty → (∀ r ∈ S, 3 ≤ r) → ∀ n ≥ N, DecompositionAt S α n
```

[`DecompositionAt`](Challenge.lean#L62) expands the hypotheses and conclusion:

```lean
def DecompositionAt (S : Set ℕ) (α : ℝ) (n : ℕ) : Prop := by
  classical
  exact ∀ D : ℕ, Even D → (allowedThreshold S + α) * (n : ℝ) ≤ (D : ℝ) →
    ∀ F : Fin (D / 2) → SimpleGraph (Fin n),
      (∀ i, (F i).IsRegularOfDegree 2 ∧ AllowedCycleLengths (F i) S) →
      ∀ G : SimpleGraph (Fin n), G.IsRegularOfDegree D → HasFactorDecomposition G F
```

Here `SimpleGraph (Fin n)` represents a simple graph on `n` labelled vertices,
and `F : Fin (D / 2) → SimpleGraph (Fin n)` represents the prescribed list.
The conclusion [`HasFactorDecomposition`](Challenge.lean#L23) requires an actual
edge partition and graph isomorphisms:

```lean
def HasFactorDecomposition {n q : ℕ} (G : SimpleGraph (Fin n))
    (F : Fin q → SimpleGraph (Fin n)) : Prop :=
  ∃ pieces : Fin q → SimpleGraph (Fin n),
    EdgePartition G pieces ∧ ∀ i, Nonempty (pieces i ≃g F i)
```

[`EdgePartition`](Challenge.lean#L17) requires each edge of `G` to occur in
exactly one piece, and `≃g` denotes graph isomorphism. For each vertex,
[`AllowedCycleLengths`](Challenge.lean#L58) requires the size of its connected
component to lie in `S`; the components of the finite 2-regular factors are
cycles. [`cycleThreshold`](Challenge.lean#L53) represents $\delta_{C_r}$, and
[`allowedThreshold`](Challenge.lean#L55) represents $\delta_S$.

### Proof entry point

[`Challenge.lean`](Challenge.lean) independently states the target and contains
an intentional `sorry` placeholder for the comparison; that placeholder is not
the proof. [`Solution.lean`](Solution.lean) imports the proved endpoint from
[`Oberwolfach/MainTheoremFromProtectedPreparation.lean`](Oberwolfach/MainTheoremFromProtectedPreparation.lean#L16):

```lean
theorem mainTheoremProof : MainTheorem :=
  long_preparation_implies_main long_protected_preparation_from_original
```

The comparison checks the target and proof in separate environments. The
endpoint also supplies a fixed-set intermediate theorem; the supporting
development is in the `Oberwolfach/` modules and need not follow the manuscript
proof line by line.

### Context

For context, the paper describes the degree condition as asymptotically best
possible. The ordinary thresholds are $2/3$ for $r=4$, $1/2$ for even $r\ge6$,
and $1/2+1/(2r-2)$ for odd $r\ge3$. These values follow from work of
Barber–Kühn–Lo–Osthus, Delcourt–Postle, Granet–Horsley, Hou–Hu–Wang and
Granet–Horsley–Santrio, as cited in the manuscript. In particular,
$D\ge(3/4+\alpha)n$ suffices for any prescribed list of spanning 2-regular
graphs.

## Building

The project uses Lean `v4.35.0`, pinned in [`lean-toolchain`](lean-toolchain),
and dependencies pinned in [`lake-manifest.json`](lake-manifest.json). With
[Elan](https://github.com/leanprover/elan) and Git installed, the registered
source snapshot can be checked out and built with:

```bash
git clone https://github.com/methuku-git-hub/generalized-oberwolfach-lean.git
cd generalized-oberwolfach-lean
git checkout c0d30d23c6c58dc41c03c9ce126e1ce1d846519a
lake exe cache get
lake build
lake build Challenge Solution
```

The cache command optionally downloads available Mathlib build artifacts.
`lake build` builds the default target, and the final command builds both named
targets. Building the Challenge alone does not establish a proof because it
contains the intentional placeholder described above. A local build is a
reproducibility check, not a substitute for Palomar's mechanical verification.

Omit the checkout command to build the current `main` branch instead. Palomar's
record applies to the registered commit, not automatically to later changes.
The retained `scripts/verify.py` is a historical helper that rewrites a file and
depends on unavailable local helpers; it is not the verification command for
this release.

## Verification

The selected theorem is registered as
[PALOMAR-2026-11-18-000003, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-18-000003&version=1),
for commit `c0d30d23c6c58dc41c03c9ce126e1ce1d846519a`. The registered
[mechanical report](https://data.palomar-registry.org/evidence/PALOMAR-2026-11-18-000003-v1/2257595110fa2f73c7d439582ff0fe9c741d16c554383c091b96c93e962f184a/mechanical-report.json)
records a pass for the formal statement and proof. Lean's kernel and the
independent NanoDa and Con-Ron checkers accepted the proof; the permitted axioms
are `propext`, `Classical.choice` and `Quot.sound`.

This result concerns the specified source snapshot and selected theorem.
Palomar's statement and disclosure review is automated; it is not an
independent human mathematical peer review of the paper or its correspondence
with the Lean statement.

## Sources and attribution

The mathematical source is theorem `thm:new:prescribed-factor` in *Sharp Dirac
thresholds for the generalized Oberwolfach problem*, by Dong Yeap Kang, Abhishek
Methuku and Pablo Oviedo. The Lean development began from an earlier manuscript
snapshot, with SHA-256
`ffe45b31bcfbd933828da22a9becb6aea23a642d5ffe7abf09d29f45d9d8a201`. The final
manuscript supplied by Abhishek Methuku on 14 November 2026 is
[`source/manuscript.tex`](source/manuscript.tex), SHA-256
`5f9cef1149b88a3680cc5ccf193b7a68a18fd12105ab6c495f4f23d893e772d9`.

The agent-produced [`STATEMENT_COMPARISON.md`](STATEMENT_COMPARISON.md) reports
that the main-theorem passages agree after normalization of LaTeX math
delimiters, although the full manuscript files differ. It also discusses a
separately compared 4 November manuscript. This comparison concerns the selected
statement and is not an independent human assessment of the entire paper.
[`StatementReview.lean`](StatementReview.lean) contains separately checked
elementary interpretations of the definitions.

Abhishek Methuku is the formalization author and responsible maintainer. OpenAI
Codex was used extensively under human direction for Lean formalization,
porting, proof integration, verification and statement comparison, as disclosed
in [`formalization.yaml`](formalization.yaml). This attribution is distinct from
authorship of the mathematical paper.

## License and further reading

The repository is licensed under [Apache 2.0](LICENSE). Notices and provenance
for reused material are in [`third_party/`](third_party/). The included
[manuscript source](source/manuscript.tex),
[statement comparison](STATEMENT_COMPARISON.md),
[project metadata](formalization.yaml), and
[Palomar record](https://palomar-registry.org/entry?id=PALOMAR-2026-11-18-000003&version=1)
provide further details.
