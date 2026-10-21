# R265 — current header scanner misses direct Y2 use roots

The pinned 40-source bundle was authenticated in the temporary probe against
each embedded Git blob ID. For each source, the probe rewrote only the eleven
line-leading Y2 `--` markers, scanned headers, resolved header imports against
the pinned module map, and parsed under the resulting source-local
`SyntaxEnvironment` with provenance for the selected dependency headers.
Environment construction succeeded for all sources, but the resulting
dependency relation is incomplete.

The root CSTs exposed 112 direct `UseDeclaration` nodes, while the current
`scan_header` results exposed only 45 header imports. Twenty of 40 source
modules had different counts. Examples include `std::num` (0 header imports,
1 direct use), `std::io` (0, 3), `std::time` (0, 5), `std::core::ops` (0, 3),
and `std::io::console` (0, 4). Several Y2 files put `use` after `pub mod` or
other root declarations, outside the current header preamble. Therefore these
source-local environments are still not authentic import environments.

The probe parsed all 40 inputs and round-tripped the projected bytes, but
reported 491 syntax diagnostics and structural recoveries. This number is
not a grammar verdict because most source dependency headers were missed.
R262's 474 diagnostic count remains similarly unqualified. The independent
external-module shape observation remains: Y2 `pub mod name;` nodes produce
Missing recoveries in the Y3 parser under empty, global, and these incomplete
source-local environments.

The temporary diagnostic test was removed. Its focused Cargo invocation
passed the blob/projection/parse round-trip assertions; it was not a Y2
compatibility test. Next, inspect direct-root `UseDeclaration` CST owners for a
source-bound import relation, while keeping Y2 re-export and ModuleMap
semantics OPEN. See the R265 contract.
