# Brouwer dependency

Source: https://github.com/harfe/fixed-point-theorems-lean4
Author: harfe. License: MIT; retained in LICENSE.

Retrieved on 20 October 2026 from the raw `main` files. Direct Git download was unavailable on this host; the text retrieval was checked for every numbered source line, with overlapping chunks checked for equality. `retrieved-source-sha256.json` hashes the reconstructed retrieved text, not original Git blobs. No upstream commit identity is claimed. The vendored port is fully present in `FixedPointTheorems/` and is checked with the project's pinned Lean/mathlib.

Only the five files needed by Brouwer are included; Kakutani is not imported.

Port changes for Lean 4.34:
- Mark each file's definitions noncomputable and restore file-local variable scope in the combined test.
- Set `backward.isDefEq.respectTransparency` to false for elaboration compatibility. This does not change the kernel or permit unproved terms.
- In the child-cube surjectivity proof in cubical_sperner, use `(hcomp I).mp (h4 ▸ h3)` directly after simplification; the surrounding finite-set membership constructors have already been removed by simplification.
- Update two deprecated Set lemma names.

The combined source check passed with only `propext`, `Classical.choice`, and `Quot.sound` for Brouwer. Separate module builds and the project verification pipeline also check the integrated version; consult current logs for their status. This dependency is a proof, not an added fixed-point axiom.
