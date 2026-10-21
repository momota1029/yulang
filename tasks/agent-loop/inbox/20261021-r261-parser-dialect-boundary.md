# R261 result — Y2/Y3 parser dialect boundary

Primary-only falsifier; no independent review.

Parsing the pinned 40-file Y2 standard-library bundle with current Y3
`yu_syntax::parse_file` preserves bytes but does not preserve source meaning:
Y2 `--` comment text in `text/config.yu` appears as direct `OperatorChain`
nodes because the Y3 lexer recognizes `//` comments. The observed CST root
counts cannot support R260's imported-root census.

R260 remains conditional. Obtain a Y2-authentic parser/registration witness or
prove a bounded projection over all 40 sources before using parsed-root counts.
Types/Console identity, accepted types, root specialization, Request reachability,
output, parent proofs and production remain open. See R261 contract and theory
note.
