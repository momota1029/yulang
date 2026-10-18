# R32 native active-capture path — observer boundary

## Outcome

The requested two-use native regression is **blocked at the existing observer
boundary**. I did not change the test or production code, add instrumentation,
or run Cargo. The original parent conditions remain **0 → 0**; the candidate
source path is not independently verified by this packet.

The existing source owners confirm the construction sequence in code:

- `yu-hir/src/module/local_source.rs` gives a function initializer a temporary
  self identity and later restores the lexical environment before `Publish`
  installs the local binding.
- `yu-solver/src/candidate_source.rs` retains a private `Action::Link` when a
  local name resolves to an active initializer; `Action::Install` enters the
  `PublishLocal` stage, which installs the exposed local term.
- The action executor turns the link into a candidate value constraint.

These are implementation-source facts, not a trace from the accepted-source
test witness. `CandidateInference::source_call` exposes each source Call and
native terms. `export` exposes graph rows/bounds and `fresh_use` exposes copied
rows. The public observers do not join a source occurrence or Call demand to
the exact active initializer endpoint and its emitted equality/incidence in
that graph. Thus an assertion over `source_call_count`, graph bounds, or row
identity would not establish which Link/Call caused that incidence. The
required active-root Link and demand/equality incidence cannot be identified
with the existing test-visible records.

## Prior evidence reused and rejected

- Reused the R31 closeout (`notes/progress/2026-10-18-r31-active-root-allocation-closeout.md`):
  the missing source-owned `C/D` active-capture demand telescope and equality
  incidences at nested-helper publication remain an open source judgment.
- Reused the pinned source construction owners from R32: local self identity
  and publication in HIR; active initializer Link and publication scheduling
  in candidate source; per-source Call records and FreshUse maps in the
  existing solver observers.
- Rejected any inference from candidate success, a source-call count, or
  endpoint/type equality to the missing `C/D` incidence. Those observations
  do not authenticate that source-to-graph join.

## Verification and boundary

The only authorized focused Cargo command was **not run**: the missing observer
prevents the test from asserting the contract's required path, and adding the
observer is outside this test-only lease. No test, build, probe, or other Cargo
process ran. No scratch or generated paths were created. The test artifact
remains byte-identical to its initial leased state.

This is a provisional source-evidence boundary, not a cutover or theorem result.
Falsifier for the observer claim: an existing public observer can identify, for
the exact nested-helper witness, both the active initializer Link endpoint and
the corresponding demand/equality incidences through publication without
adding instrumentation or relying on unlinked graph-wide equality. Luna owns
any future observer lease and cleanup decision; this worker made no production
or observer change to clean up.

## Remaining premise and next in-envelope action

`R32-NATIVE-OBS-1` is the exact missing evidence request recorded in the paired
handoff. The next related action is for Luna to decide whether an already
existing public record can supply the source-occurrence-to-Link/Call-to-graph
join. If it cannot, the contract requires a new authority/lease decision before
any observer change. The test-only lease is frozen without a behavioral test
result.
