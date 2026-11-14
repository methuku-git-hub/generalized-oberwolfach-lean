# Prescribed 2-factor decompositions: a Lean formalization

## Paper abstract

**Paper authors:** Dong Yeap Kang, Abhishek Methuku and Pablo Oviedo.

We prove an asymptotically sharp Dirac-type generalization of the
Oberwolfach problem posed by Ringel in 1967, allowing decompositions
into a prescribed list of possibly different spanning $2$-regular graphs.

For $r\ge3$, let $C_r$ denote the cycle of length $r$, and let $\delta_{C_r}$ denote the asymptotic minimum-degree threshold for a $C_r$-decomposition, that is, the infimum of $d\in[0,1]$ such that every sufficiently large $n$-vertex graph $G$ with $\delta(G)\ge dn$, all vertex degrees even and $r\mid e(G)$ has a $C_r$-decomposition.

For any nonempty set $\mathcal S\subseteq\{3,4,\ldots\}$ and $\alpha>0$, we show that every sufficiently large $n$-vertex $D$-regular graph with $D$ even and $D\ge(\sup_{r\in\mathcal S}\delta_{C_r}+\alpha)n$ admits an edge-decomposition into any prescribed list $F_1,\ldots,F_{D/2}$ of $2$-regular $n$-vertex graphs whose cycle lengths belong to $\mathcal S$.
The degree condition is asymptotically best possible.

Results of Barber–Kühn–Lo–Osthus on even cycles and of Delcourt–Postle, Granet–Horsley, Hou–Hu–Wang and Granet–Horsley–Santrio on odd cycles determine the cycle-decomposition thresholds:

$$
 \delta_{C_r} =
 \begin{cases}
  2/3,&r=4,\\
  1/2,&r\ge6\text{ even},\\
  1/2+1/(2r-2),&r\ge3\text{ odd}.
 \end{cases}
$$

In particular, $D\ge(3/4+\alpha)n$ suffices for any prescribed list of spanning $2$-regular graphs.
Our theorem settles, in a stronger form, conjectures of Glock–Joos–Kim–Kühn–Osthus (*J. Eur. Math. Soc.*, 2021) and Glock–Kühn–Osthus (*Surveys in Combinatorics 2021*) on sharp Dirac thresholds for the Oberwolfach problem.
It also determines the sharp asymptotic degree threshold for resolvable cycle decompositions of regular graphs.

*Formalization scope:* The Lean project formalizes the selected main theorem; it does not claim to formalize the entire paper or all its corollaries.

**Verification status.** This repository provides a formalization for Palomar
review. The local checks described below and any Palomar verification should be
read against the exact commit they checked; no independent human statement
review had been recorded when this documentation was prepared.

This project formalizes a theorem about edge-decomposing sufficiently large,
even-regular graphs into an arbitrary prescribed list of spanning 2-regular
graphs. The allowed cycle lengths can be any nonempty set of integers at least
three. The host's degree is bounded below using the ordinary cycle-decomposition
thresholds for those lengths. The minimum graph order depends on the degree
margin, uniformly over the allowed set and the prescribed factors. The precise
quantifiers and definitions are in `Challenge.lean`.

The selected declaration is `Oberwolfach.mainTheoremProof`. The proof is in
`Oberwolfach/MainTheoremFromProtectedPreparation.lean` and imported by
`Solution.lean`. The deliberate placeholder in `Challenge.lean` states the
comparison target; it is not the solution proof. The permitted foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The source is *Sharp Dirac thresholds for the generalized Oberwolfach problem*,
by Dong Yeap Kang, Abhishek Methuku and Pablo Oviedo, theorem labelled
`thm:new:prescribed-factor`. The final manuscript source provided by Abhishek
Methuku is included at `source/manuscript.tex`; its SHA-256 is
`5f9cef1149b88a3680cc5ccf193b7a68a18fd12105ab6c495f4f23d893e772d9`.
The theorem and its Lean definitions have been compared by Codex; no independent
human fidelity review has yet been recorded. The project does not claim to
formalize the complete manuscript or all its corollaries. See
`STATEMENT_COMPARISON.md` for the comparison and `StatementReview.lean` for
separately checked elementary interpretations of the definitions.

## Local verification and reproduction

A separate source-stable Lean 4.35.0 candidate passed a full build, a theorem
axiom audit, a blueprint check, a fresh Lean kernel replay, and the original
main-theorem gate. An export of its main theorem was accepted by NanoDa and
con-ron; a subsequent NanoDa replay printed the three permitted axioms and
reported no errors. These results do not by themselves verify this prepared
repository snapshot or constitute Palomar Comparator or registration.

The `lean-toolchain` and `lake-manifest.json` pin Lean and the dependency
revisions. With those dependencies available, the project targets can be built
using `lake build` followed by `lake build Challenge Solution`. A final release
must rerun the appropriate checks and Comparator on the exact submitted commit.
The retained `scripts/verify.py` is a historical verification tool for the
earlier development: it rewrites `BlueprintDeclarations.lean` with an older
import style and expects local audit helpers that are not in this draft. It is
not the verification command for this Lean 4.35 submission; adapt and test it
separately before using it for a release.

## Authorship, automation and licence

Abhishek Methuku is the formalization author and responsible maintainer. The
mathematical source has the three authors named above. OpenAI Codex was used
extensively for formalization, porting, proof integration, local verification,
and statement comparison under human direction. The extent of human mathematical
review is to be confirmed before submission.

The proposed repository licence is Apache 2.0; see `LICENSE`. Retained notices
and provenance for reused formalization material are under `third_party/`.
The maintainer requested that the supplied final manuscript be included.
