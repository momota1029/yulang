# R173 Luna implementation packet — candidate

Sprint `source-drain-attribution-and-consumer-join-20261021-r173`, contract
revision 1, SHA-256 `e4e6b0a93b00b69ece7b08ccd8d655a4fe096e351c42996186c1fc650d9511d0`. This packet is
inactive until prospective review is CLEAN and Luna records activation.

Baseline commit `7ec64a378`; R172 exact CLEAN code/query/harness review is
recorded in the implementation handoff for that sprint. Original parent and
quantifiers are frozen in the contract. The central gap is direct-source task
versus Replay child attribution at `start_typed_drain`, where a newly created
seed and an incoming `item.relation` meet at `.or(seed)`.

If activated, Luna/high owns the bounded multi-step implementation across only
these leased paths: `lib.rs`, `candidate_context.rs`, `candidate_scheme.rs`,
`shadow_apply.rs`, the R173 diagnostic example, implementation note and this
handoff. First inspect all actual direct-source call sites and replay child
creation. At the transition, retain source Cause/task, incoming relation and
Replay acknowledgement, new seed, and selected relation as an inert typed
certificate owned by the same origin/drain lifecycle. Ensure it cannot select
solver decisions or alter publication. If a field cannot be sourced
authentically, return unavailable rather than infer it from equal IDs.

Build the borrowed query from those owner records through same-provider
Capture, FreshUse maps and the exact forwarding Apply consumer. Preserve all
dependency alternatives and ordered Replay inputs. Report per-component
completeness; keep parent gates open. A conditional single probe is possible
only after the query can discriminate every required link and a fresh reviewer
is CLEAN on exact source, code, harness and command pins. Otherwise write
`NOT_RUN` with the missing component. No tests, broad build, evaluator, Y2,
network, external oracle or behavior-changing implementation.

Requested Luna/high. Runtime observed model/effort remain UNKNOWN absent a
trusted receipt. Implementation budget 1500 seconds, no descendants. Stop if
the certificate cannot stay behaviorally inert, a necessary owner is not in
the exact leases, failure-path semantics change, dependencies drift, or the
budget is spent. Preserve all unrelated working-tree files. Fresh independent
review follows frozen exact hashes; only Luna stages and integrates reviewed
R173 paths.
