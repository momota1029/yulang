# R262 — comment-only projection falsified as a Y2 root witness

A primary-only scan of the exact 40 bundled standard-library sources found
eleven `--` occurrences. Each was at the start of a line after indentation;
there were no other `--` occurrences in the bundle. A temporary probe changed
only those two-byte markers to `//`, preserving every source length, then ran
the current Y3 `yu_syntax::parse_file` over all 40 projected sources.

The parser round-tripped each projected input, but 33 modules produced a total
of 474 syntax diagnostics and 474 structural recoveries. Examples include
12 missing-module recoveries in `std.yu`, 108 diagnostics in `text/str.yu`,
45 in `data/list.yu`, and 75 in `text/parse.yu`. Seven modules happened to
produce no diagnostics. Thus the line-comment spelling was not the only Y2/Y3
grammar difference; the projected CST and its 318 `BindingStatement` roots
cannot establish Y2 root boundaries or publication classes.

The focused Cargo test was only a temporary diagnostic probe and passed its
projection/count/round-trip assertions; it was removed immediately after
capturing the result. It did not assert that diagnostics were empty and is not
a passing source-compatibility test. No compiler behavior or retained tests
changed. R260 remains conditional and R261's parser boundary stands.

Next evidence must come from an authentic Y2 parser/registration implementation
available within this repository, or a source-to-root correspondence that
accounts for all observed recoveries. See
`tasks/agent-loop/sprints/yulang2-bounded-comment-projection-20261021-r262.md`.
