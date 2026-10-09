# Actual extrusion/intrusion regression evidence

Date: 2026-10-10
Branch: research/simple-sub-intrusion
Baseline: 14cefe847fbb625ee56a99a08833e7eaae102fec
Authority: user-selected parent/copy SCC equality and live level-based schemes
Mode: M1; one independent compiler-referee, one fresh batched repair producer

Five private owning tests exercise actual production operations, rather than
the historical injective-renaming model. Real candidate_extrude creates and
records parent/copy pairs; an actual reverse bound and worklist drain place them
in a dependency SCC. Both kinds and both polarities identify the copy with its
parent, merge minimum level/non-generic state and drain pending propagation.
Without the reverse dependency, provenance alone does not identify the pair.

The transactional test adds a later integer lower through the identified copy,
then fails the route and verifies original bounds, row counts, metadata, levels,
parent inventory and canonical generation. Source tests cover self/mutual
recursion through open roots and actual captured-local extrusion, independent
eligible images, shared older source anchors and late integer result reachability.
Those source tests do not claim their source alone forced a parent/copy SCC merge.

Initial verification passed four tests; the fifth used an unsupported anonymous
lambda input. Independent review also rejected mere integer inventory as proof
of a late result and requested exact source-anchor correspondence. One fresh
repair replaced the input with a supported named declaration, strengthened
value-bound reachability to the answer root and matched original older anchors
to both use images. Expected behavior was preserved.

Final focused command:

```sh
RUSTC_WRAPPER= timeout 180 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests -j 2 --offline -- --test-threads=1
```

Result: 5 passed, 478 filtered, no warnings. Fresh semantic delta review covers
the repaired assertions. Scoped whitespace checks pass. Production code changes
only by cfg(test) module wiring; no resource measurement or benchmark ran.
Broader suites were not repeated for this test-only checkpoint. Full Call,
concrete annotation hygiene, soundness, principality and production cutover
remain outstanding; these tests do not certify those contracts.
