# R266 — inspect direct-root Y2 use CSTs as import evidence

Status: ACTIVE primary-only source investigation.
Branch / baseline: `research/simple-sub-intrusion` / `83288c723`.
Authority: unchanged Types/Console goal; R149 and R261-R265. No semantic
approval, production gate, or parent proof is inferred from CST structure.

## Outcome

R265 showed that the Y3 `scan_header` preamble omits many direct Y2
`UseDeclaration` roots. Inspect whether current `yu_syntax::parse_file`, after
the bounded line-comment projection, retains exact route tokens and source
spans for all direct use roots in the pinned 40-source bundle. This is a
source locator test, not a claim that Y3 import resolution implements Y2.

Success evidence: authenticate all 40 source blobs, parse losslessly, enumerate
all direct-root `UseDeclaration` nodes, record their exact source text/ranges,
and compare node coverage with original source-level use lines. Identify which
routes can be mapped to pinned modules and which grammar forms are unsupported
or ambiguous. Falsifiers include missing/extra use nodes, changed route bytes,
nonempty syntax/structural diagnostics on a route, or an unresolved route not
accounted for by the pinned bundle.

## Scope and resources

Primary-only, read-only source probe; a temporary test may be used and must be
removed. Read the pinned bundle, `yu-syntax` use declaration CST owner and
R265 archive. No retained code/tests, source changes, builds beyond one focused
Cargo test, sample execution, external reads, or semantics edits. Cap 420
seconds; no independent reviewer; result remains provisional.

Even complete CST route extraction does not establish module loading,
re-export semantics, declaration identity, runtime root publication, accepted
Types, output, Simple-sub/evaluator A/B, R70/R71, source/native proofs,
soundness, principality or production. Those gates remain OPEN.
