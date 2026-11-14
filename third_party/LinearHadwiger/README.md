# Selected Norin–Steiner matching development

Source: https://github.com/snorin239/LinearHadwiger
Pinned commit: `9ef0db5fbaba0c4bc15248b9ea83933c262559c1`.
The six imported files are listed with original hashes in PROVENANCE.json.
Their Apache 2.0 licence is retained in LICENSE. The original complete archive
is in the workspace reference directory. The selected source files are at
`HadwigerLean/` in this project.

The original toolchain was Lean 4.32.1. `lean-4.34-port.diff` records three
compatibility edits: the ordered product theorem name, an explicit conversion
in an indexed-hypergraph degree proof, and a transparency option in the
matching iteration. No statement or numerical hypothesis was altered.
All six files and the matching entry theorem built on Lean 4.34.0.
Full fresh kernel replay is recorded by the project's verification runner.

The formal constant is `(ξ / (100*r))^(20*r)`, smaller than the displayed
constant `(ξ/100)^(20*r)` in the linked paper. Our bridge uses the formal
constant, with another factor 1/4 for rounding; it does not claim the stronger
paper constant. The result covers almost all vertices. It does not supply
the simultaneous prescribed weighted sums required by the manuscript's
Ehard–Glock–Joos application.
