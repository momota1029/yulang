# R262 result — bounded comment projection rejected

Primary-only; no independent review.

All eleven `--` occurrences in the pinned 40-source bundle were line-leading
comments. Replacing only those markers with equal-length `//` markers preserved
input lengths and parser round-trips, but the current Y3 parser still produced
474 syntax diagnostics and structural recoveries across 33 modules. The
projection cannot witness Y2 root forms. Its temporary diagnostic test was
removed; no code or retained tests changed.

R260 remains conditional. Find an in-repository Y2 parser/registration route
or prove a broader source/root correspondence before using any Y3 CST count.
R149 sample behavior, parent proofs and production remain open. See the R262
contract and theory note.
