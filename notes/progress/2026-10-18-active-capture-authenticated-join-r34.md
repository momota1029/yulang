# R34 rev2 native repair — bounded result

## Outcome

R34 rev2 contract SHA-256: `03f7cb94f79a2cfc0d17e67d1fa866f4b6147fdb5221cc4f5f0e12fd91098283`.
The original parent remains OPEN at `0 -> 0`; R30's independent `j0/a0` and
same-event world-action gate remains OPEN. No source law, proof, semantic
adoption, production observer/API, allocation policy or fixture meaning changed.

The three reported test-code compile repairs are in the leased test module:

- Resolve an action's `HirOccurrenceId` by exact equality against retained
  `source.expressions()` occurrences, rather than passing it as a
  `LocalSourceIndex`.
- Use one dereference for the selected pair index in the group-range filter.
- Clone `hir` for inference in the integration test while its local source is
  still borrowed.

The independent active-Link no-FreshUse assertion remains before pair/group/map
joins in the native unit test. The R34 rev1 concern was checked before spending
the only remaining Cargo invocation: allocated images are selected only from
`ReconstructedRowObservation.allocated_fresh_image`, keyed by typed `RowKey`
source representatives. Canonical aliases of allocated rows inherit the same
typed image; rows whose source representative has no recorded allocation retain
the original image and do not enter the fresh-image sets. Assertions now check
per-source image consistency, component-kind preservation, distinct recorded
fresh images, and preservation of shared images. This uses the existing
`prepare_candidate_fresh_use` construction: fresh allocation occurs only when
`row.local && level > graph.boundary && !metadata.non_generic`; canonical rows
are memoized by representative and the retained observations record the
allocation guard and resulting image. This is code-level authentication only;
the assertions were not executed.

## Check and limitation

Spent the one R34 rev2 Cargo allowance on exactly:

`cargo test -p yu-solver --features shadow-apply-candidate active_outer_root_two_helper_uses`

It exited 101 while compiling `tests/candidate_local_self_recursion.rs` at the
borrow/move of `hir`, before the test executable ran. The test had zero runtime
assertions executed. The reported integration borrow was then repaired by
passing `hir.clone()`. No retry or other build, test, or probe ran. Therefore
this packet establishes no executed Link-to-event/pair/group-to-two-map join,
no negative-control execution, and no test pass. The remaining Cargo allowance
is zero under the frozen contract.

The existing join assertions retain exact source occurrence/event, helper
origin and loop receiver, signed pair rows with `RowKey` component kinds,
activated group range, and both helper route maps. They remain candidate test
code awaiting a new authorized verification grant; their presence is not
runtime evidence. Parent source proof remains blocked at the source-owned
Generalize §3.3 introduction for C/D sort, scope/telescope, typed dependencies
and capture action. R32 retention and the R33 obstruction remain applicable.

## Frozen artifacts and runtime

- `candidate_scheme.rs` SHA-256: `619d56861aae4592706a6fb30debe5a1934fbbdecf967d5d88c82fe7084e2460`
- `candidate_local_self_recursion.rs` SHA-256: `6f8bf3f966e7c9304b54699595e12b614a6ad7f93e30320183bb373a2c3fcf5b`
- The single assignment handoff is frozen with this note; their content hashes
  are reported alongside the final receipt to avoid self-referential fields.
- Requested model/effort: Luna/high. Observed model/effort: UNKNOWN; no runtime
  metadata exposed the effective model or effort.
- Observed focused Cargo duration: approximately 6 seconds from tool receipts;
  native assignment duration is not instrumented and is reported UNKNOWN.
- Cargo invocations: prior rev1 compile failure plus this one rev2 compile
  failure; rev2 assertions did not run. No other checks were run.
- All writes stopped after the two leased receipt files were frozen.
