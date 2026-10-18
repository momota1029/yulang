# Replay constructor lineage implementation handoff

Sprint-ID / contract revision and SHA-256:
`npair-replay-constructor-lineage-20261018`, revision 2,
`b04f61d76511ebca81ed5217bf8ba0ec76fdaa3035a212123031e4079005ad80`.

Assignment-ID / handoff revision:
`replay_constructor_impl_20261018`, revision 1.

Parent gate / original theorem and scope locator:
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN with its
original source domain, quantifiers, accepted semantics and fixed `c`.
Original-condition closure remains 0. This instrumentation closes no proof
gate and adopts no compiler semantics.

Baseline / direct dependency hashes:
The r2 contract pins the prior CLEAN audit note
`572884a8df2e8adc19eb1a8121277c77784e3c02fa9925729e292dd629f40308`, prior
handoff `f2c93d65ba96e4a256010e2942096ca21ef714b5b06d81573701eb0b960948ed`,
source inputs `candidate_scheme.rs`
`0c55d3d47bc88166a68eb5f5797043b136a2d2bc0ace55de832e8e27ca20a07f`,
`candidate_context.rs`
`f2ecbadcc33e4439c57429cb6a6ce5bcdfd5c3131f5b5ebb9d1e03a0e224f569`,
`shadow_apply.rs`
`6508a3f39a6d3742110ca1f33e927fa26bd3b112c3f378fc345294675b7f69e3`,
`candidate_source.rs`
`1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e`,
and `candidate_call.rs`
`e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`.
All r2 frozen input hashes were verified at intake. Prior diagnostic stdout,
stderr and metadata remain pinned at `05c536a2d2a5265687b16362fec6d0909a8dfbed178d69c8feb90a83972cf813`,
`6966e24792eb97eaf26498f7e975cdc919fd0d19cb283666b613d78adcac49a3`, and
`6e0dda42a13b1ff8273904a0a4e239ea7d77b789d9cc94ec7d55bfa5ed740f47`.

Role / actual worker ID / current session / launch or resume receipt:
`implementer` / `/root/replay_constructor_impl_20261018` / `current-session`.
Parent accepted the r1 intake ACK and r2 clarification ACK. Runtime launch
telemetry beyond the parent dispatch is unavailable here.

Requested model and effort / observed model and effort:
Requested Luna/high. Observed model and effort UNKNOWN.

Exact leased paths / authors and descendants:
`crates/yu-solver/src/candidate_scheme.rs`,
`crates/yu-solver/src/candidate_context.rs`, and this handoff only. Author:
`/root/replay_constructor_impl_20261018`. No descendants. No other path was
written. Both source files were already modified relative to local HEAD at
intake, while matching the frozen input pins; those bytes were preserved.

Outcome class:
Provisional, test-only source-native instrumentation. Not an implementation
correction, theorem, production behavior change, or ownership classification.

Parent application / current conclusion:
The new exact source test now has construction-time observations to classify
the pinned Module route0/use1 and route1/use2 specimen, or identify a remaining
missing fact. Until independent CLEAN instrumentation review and the one
authorized exact runtime attempt, no runtime classification follows. The
parent theorem remains OPEN and closure remains 0.

Source constructors -> generated constraints -> propagation -> consumer/native
path:
- Capture observations are recorded at `Capture::row`: requested key,
  representative after the existing rep lookup, capture level,
  `non_generic`, graph boundary and stored `local` decision.
- Reconstruction observations are recorded in `prepare_candidate_fresh_use`:
  captured row/key, current representative/level/`non_generic`, stored flag,
  `canonical_rows` hit/miss, first graph-row insertion order, prior mapped
  image, actual allocated-fresh-image decision and resulting row image. The
  existing freshening guard remains inside the canonical-map miss branch.
- The focused observation test prints each retained Module route's occurrence
  and use identity, route row map, capture records and reconstruction records;
  it asserts route0/use1 and route1/use2 remain distinct.
- Context-side test-only lineage reports relation records, source origins,
  adjacent constructor dependencies, admissions and linked emissions. The test
  prints the exact lower/upper/Replay relations, ordered FunctionPort relation
  IDs/pairs/flows, and their ancestry. Test-only Replay drain receipts retain
  child identity, drain index, completion transition count/stage, and the
  enclosing Replay drive return. No authentication predicate or mutation
  control was changed.

Artifact locators and byte hashes / frozen review snapshot:
- `crates/yu-solver/src/candidate_scheme.rs` SHA-256
  `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`
- `crates/yu-solver/src/candidate_context.rs` SHA-256
  `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`
- This handoff's hash is returned to Luna after freezing.
- These bytes are the frozen instrumentation-review target. Do not execute the
  test, build or runtime before an independent CLEAN review.

Checks, coverage, omitted cases and resource budget:
Read-only source/contract inspection and hash verification only. No test,
build, runtime, formatter, broad fixture or old diagnostic rerun was executed.
The exact test retains prior assertions and mutation controls and adds the
observations above. Runtime coverage and final source-to-execution
correspondence are still pending. Allocation: implementation 600s; actual
elapsed time and CPU/RAM telemetry UNKNOWN; no descendants or Astra time.

Provisional boundary, falsifier and cleanup owner:
The source observations are reversible and `#[cfg(test)]`. A reviewer finding
that any observation is outside test-only code, changes the operative map
branch, or fails to bind a printed value to its constructor owner falsifies
this packet and blocks execution. A mismatching exact runtime record also
falsifies the proposed source/runtime correspondence. Luna owns any cleanup or
removal after classification; no cutover is authorized here.

Next related step inside the existing envelope:
Independent reviewer checks the frozen hashes, test-only containment,
canonical-map hit/miss order, owner/use identity, constructor ancestry, all
ports and Replay drain linkage. Only after CLEAN may Luna execute the one exact
test selected by its full test path with `--exact --nocapture`.

Mutual TODOs:
No new cross-lane TODO. The proof lane should apply its source derivation to
the frozen runtime observation, preserve the original parent claim, and leave
any unsupported source occurrence or missing drain link explicitly UNKNOWN.

Worker state / writes stopped receipt / descendant leases:
Writes to the three leased paths are stopped and the artifacts are frozen for
independent instrumentation review. No descendants or generated scratch
outputs. Worker should be recorded STOPPED for writing after Luna acknowledges
this handoff; execution remains blocked on CLEAN review.

Commit-ready milestone or pending review/integration:
Pending independent instrumentation review. No code execution, source
classification, production promotion or Git integration is authorized by this
handoff.
