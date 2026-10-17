# Frozen assignment handoff

Sprint-ID: `npair-parser-row-key-separation-20261018`.
Contract revision: 1; SHA-256 `f9e0c7476e2cd03d0d83ef7c608807b01f2cdc9e9bb1677440692556f7d24b96`.
Assignment-ID: `npair-parser-row-key-separation-20261018`; handoff revision: **1**.
Baseline: `515b705f6879bd8fd4a57fd1f6732e11ea9c0a29`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original claim,
quantifiers, accepted domain, F1/FK1 and downstream obligations unchanged.
Parent closure: **0**, OPEN.

Role: constructive parser/source identity prover.
Actual worker: `/root/npair_parser_row_key_separation`, current session;
actual task delivery and bounded source work observed. Requested Sol/high;
observed model/effort UNKNOWN. Cap 240s, Astra0, children0; exact runtime and
CPU/RAM UNKNOWN. Charge full 240s reservation, no inferred refund.
Author: this worker alone; no contributing descendants.

Outcome class: source-native-evidence / conditional obstruction.
Actual result: the visible BracketRow constructor always calls
`crate::cursor::recovery::emit::emit_token_item(open)` after starting its node,
but this emitter and Item/token payload owners are outside the frozen reads.
The actual HIR `parse_row` consumer accepts an empty nontrivia element list and
requires neither bracket, so HIR shape checks do not independently establish
positive row width. No authentic collision demonstrated. Stop condition met:
indispensable owner absent. Primary explicitly requested freeze and STOP.

Parent application: reuse the prior local-cache argument only conditionally;
its exact remaining premise is key separation between every earlier explicit
cache seed and the root result row. This packet does not discharge it.
Owner seam: `type_expr::type_bracket_row_normalized` at mod.rs:1609 ->
`cursor::recovery::emit::emit_token_item`; actual opening emission is the first
missing source evidence. `has_recovery` admission semantics and
`root_statement::parse_root_statements` global constructor coverage also remain
unpinned if a proof needs those routes. No semantic/native claim follows.

Source evidence chain: parser start/emitter/delegated ordinary+recovery body ->
source_annotation::parse_row -> SourceEffectRow.position -> frozen prior
candidate cache traversal/miss proof. Eq/Hash and HIR key transport reused;
no constraint generation, propagation or native behavior changed or executed.
Original Simple-sub operations and lineages preserved.

Artifact: `notes/theory/2026-10-18-npair-parser-row-key-separation.md`.
Artifact SHA-256: `51e756e4ae4cea61688553ee89bd1e7ec10a178d33e127c13946cf1a8189f222`.
Direct source and prior artifact hashes are fully enumerated in that frozen
artifact and verified against contract rev1; all matched. Reused prior
conditional cache author `/root/npair_explicit_row_address_invariant` and
primary-authored Eq/Hash/transport material within their actual premises;
rejected prior unconditional distinct-start claim remains rejected.

Coverage: ordinary empty/populated rows; boundary/EOF/missing-close recovery;
separator/malformed-body retry; foreign closes; nested row body admission;
leading/bracket-arrow continuation recovery; empty/shared-green possibility.
Omitted: actual unleased emitter/payload/recovery-detection/root-delegation
implementations; authentic execution and exhaustive repository constructor
coverage. No hypothetical malformed carrier promoted to source counterexample.

Checks: static cat/sed/rg reads and sha256sum only; no tests/builds/probes,
Cargo/compiler execution, Git, network, children or reviewer appointments.
No extra generated/scratch paths. Exact new/write paths are solely the artifact
above and this inbox. No shared state, compiler, tests or other workers' files
were written.

Mutual TODO `ROW-OPEN-EMISSION-1`: Luna grants a separate exact read envelope
for emit_token_item and its necessary Item/token-kind/payload owners; establish
positive opening emission for every actual ordinary/recovery call. Falsifier:
authentic parser-produced equal-key earlier/root cache rows, or authentic
reachable empty-width row refuting the proposed width invariant. A synthetic
empty row or assumed transition is insufficient. If using exclusion, pin the
actual has_recovery gate. No production implementation TODO justified yet.

Next step: Luna intake and fresh independent source review or exact dependency
extension. No further step inside this stopped assignment. Producer cannot
independently certify its result. Pending review/integration; parent OPEN.

Worker state: **STOPPED**. Writes ceased after this revision and hash receipt;
artifact bytes frozen. No descendants, child leases, background work or pending
worker activity. Reopening requires primary-directed acknowledged new revision.
