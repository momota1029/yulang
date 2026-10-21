# R261 — parser dialect boundary for imported-root evidence

Status: primary-only falsifier; no independent review. Read-only result.

## Original goal and boundary

Continue the unchanged Yulang2 Types/Console outcome. R149 imported-root
composition, accepted Types, runtime output, Simple-sub/evaluator A/B,
R70/R71, source/native correspondence, soundness, principality and production
remain OPEN. This sprint only determines whether the current repository's
Y3 parser can serve as the exact parsed-source witness for the pinned Y2
standard-library root census.

## Evidence and result

The 40 sources embedded in `tools/inference-playground/pinned_stdlib.bin` are
the exact R149 library closure (the bundle's tests verify each blob and
resolve all 40 modules). A temporary primary-only probe parsed all 40 with
the current `yu_syntax::parse_file`, retained direct root child kinds and
round-tripped the source bytes. The probe passed byte round-trip, reporting
318 `BindingStatement` and 39 `OperatorChain` roots.

That output is not a Y2 root witness. Y2 sources use `--` line comments; the
current Y3 lexer recognizes `//` line comments (`crates/yu-syntax/src/lexical/
lexer.rs::scan_line_comment`). The Y3 probe classified English text from
`text/config.yu` comment lines as direct `OperatorChain` nodes, including
“warning collection is a future item.”, “duplicate keys are last” and
“entries before any header use section”. This proves the parser accepted the
bytes losslessly, not that it interpreted their Y2 syntax. Other observed
`OperatorChain` roots include real operator declarations and cannot be counted
as runtime expressions from kind alone.

Thus the current tree does not provide the exact per-module Y2 CST/ModuleMap
vector needed to upgrade R260's textual census. R260 stays conditional; its
empty imported-initializer conclusion is neither strengthened nor refuted by
the Y3 parse. No code, test, or source-language semantics changed in this
result.

## Next discriminating step

Find an in-repository Y2-authentic parser/registration interface or establish
an explicitly bounded Y2-to-Y3 source projection whose root correspondence is
proved for all 40 pinned blobs. Falsifiers include a missed Y2 comment form,
changed root boundaries/order, or any difference in binding/body syntax that
changes Value-versus-Computation publication. Until then, do not use Y3 CST
counts as imported runtime roots and do not open the R168 implementation gate.

Primary-only probe: one focused `cargo test -p yu-playground` test invocation,
completed successfully in 0.23s. Its temporary diagnostic test was removed;
no repository code or test output was retained. No independent reviewer was
available. No tests beyond that probe, builds, sample runs, or semantic edits
were made.
