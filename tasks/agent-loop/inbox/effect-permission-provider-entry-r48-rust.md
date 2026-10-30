# R48 Rust handoff — provider endpoint common to Internal entry and Catch input

Sprint / contract: EFFECT-PERMISSION-PROVIDER-ENTRY / R48, contract SHA-256
`b4ff4331c8d864023a7f1afbdab779ef93e44ada738ec32fe179d114c4316cdd`.
Baseline supplied by Luna: `5b5b288f3d66b9306675a0e25b3b084f78e681cd`.

Assignment / handoff revision: `/root/r48_rust` / 1. Parent: the R45/R47
Internal permission-entry obligation, now asking for a provider operation
endpoint also present on the original unfiltered Catch input path. This is a
private source-native candidate certificate; it is not provider-arrival
closure, Catch selection, subtraction, hygiene closure, or production policy.

## Runtime, pins, and exact writes

- Worker: `/root/r48_rust`; admitted session: `EFFECT-PERMISSION-PROVIDER-ENTRY/20261031-R48`.
- Requested model / effort: Luna / high. Observed model / effort: UNKNOWN / UNKNOWN.
- Parent acknowledged this worker's pin-matched active acknowledgement. Runtime
  session token and active-work duration are not exposed to this worker; token:
  UNKNOWN. CPU/RSS telemetry: UNKNOWN. No descendants.
- Exact writes: `crates/yu-solver/src/candidate_context.rs`,
  `crates/yu-solver/src/candidate_receiver.rs`, and this handoff only.
- R47 pre-edit leased source hashes: `candidate_context.rs`
  `184f09e91221f8ae0969d1dbc792b7707ef5571ff56d96e276467641215bf32e`;
  `candidate_receiver.rs`
  `1426526cad48d4bc02984e0a5967e30e50cd188cb01fbeb71bc6f15442e59448`.
- Baseline and contract hash were supplied by Luna and the contract hash was
  rechecked. No Git command was run; workspace-wide baseline membership is not
  independently asserted here.

Final source/dependency SHA-256 values:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_context.rs` | `1ba38a85e8575b1d6d3cf50d918a3603c4e23068cb730d1c3645e605148636bc` |
| `crates/yu-solver/src/candidate_receiver.rs` | `ae7d4b12db10f46ba4588bb2c62ef906a71997ae6de184dbc93bfe08644e533a` |
| `crates/yu-solver/src/candidate_effect.rs` | `2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3` |
| `crates/yu-solver/src/candidate_scheme.rs` | `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/lib.rs` | `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4` |
| `notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean` | `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c` |
| `tasks/agent-loop/inbox/effect-permission-current-emission-r47-rust.md` | `6a8e7c60a6bf45733524b457c8cffb43d4ebae5101bb8a526fd9ca0f60a1f8de` |
| `tasks/agent-loop/inbox/effect-permission-current-emission-r47-proof.md` | `ce27378fe9dbc6c25ede25869a238bbf59af14ffe9a64202d3aeb520947a08e1` |
| `tasks/agent-loop/inbox/effect-permission-current-emission-r47-review.md` | `2f2fc7568b67058cd1e3aac50635206687a9c5bfcaf3a4d36065aab01287bc40` |
| `tasks/agent-loop/inbox/effect-permission-internal-incidence-r45-rust.md` | `5ca8058e79015b4896260c19aa2b389449324e223c169419fd873177910c4341` |
| `tasks/agent-loop/inbox/effect-permission-internal-incidence-r45-review.md` | `a4e40d0b5ced25574e821047727cdcba21c35bb7d6701e6641ed0869b6647c6b` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| R48 contract | `b4ff4331c8d864023a7f1afbdab779ef93e44ada738ec32fe179d114c4316cdd` |

## Outcome and source-to-constraint correspondence

Outcome class: provisional private source-native implementation. Added
`ReceivingResidualExperiment::provider_entry_certificate()` and a private
`ProviderEntryCertificate` borrowing the same R45 permission / R47 entry
emission, the exact Catch source fact, exact native operation view/member, and
both retained lower-edge paths.

The source bridge is owner-local and read-only:

1. The experiment's unique complete definition use is checked against the
   assembled relay/answer owners. `internal_formal_permission_incidence`
   supplies the R45 `entry_effect`; the existing R47 query validates the first
   entry-path edge against the same use root and retained source receipt.
2. The Catch root is selected as the unique retained `ConstraintOccurrence`
   whose occurrence is the original schema scrutinee and whose source-local
   slot is exactly 51. Its lower term is translated to the solver's effect
   endpoint; the query does not use the Catch result row or an outcome record.
3. The native terminal is selected only from `ViewOrigin::Operation` whose
   retained occurrence equals the assembled provider occurrence and whose
   declaration is the exact same retained `Arc` as the source operation.
   The member index must name that declaration's effect family. Multiple
   matching origin/member candidates are unavailable.
4. For each traversed row lower edge, the query reconstructs the `BoundKey`
   from the live `effect_bounds` owner/lane/index, reads the indexed current
   row or atom, and requires one retained `BoundEmission` at that exact physical
   slot. Its bound, constructor readback, readback slot, directly referenced
   admission, admission bound, relation and exact relation pair must agree.
   Entry-path relation records must also descend from the same R47 use root.
5. The bounded search compares full endpoint constructors without canonical
   row or family substitution and returns only when exactly one entry path and
   exactly one Catch path meet at the same `AnnotationMember` endpoint.
   Missing, duplicate, stale, reversed, foreign, invalid, disconnected,
   cyclic-only, or work-limited evidence returns unavailable.

No consumer uses this certificate. No routing, propagation, permission
subtraction, Catch outcome, ordinary dispatch, source domain, diagnostics or
semantic expectation changed. This query does not establish that the native
execution succeeds or that all executions are covered.

## Reused evidence and limits

Reused R45's complete Internal-use permission incidence and its reviewed
source identity; reused R47's `current_internal_emission` current physical slot,
owning admission/emission, completed source-drain receipt and dependency
ancestry checks. The R47 independent review was CLEAN for its bounded query and
explicitly left provider arrival/Catch correspondence OPEN. The R47 conditional
Lean result does not prove this new common-endpoint path.

The query's local work cap is `candidate_source::SCOPED_WORK_LIMIT`; search
allocations use fallible reserves and exhaustion returns `SearchLimit`. The
certificate's borrows prevent mutation while it is held. No independent
cross-generation ABA theorem, extraction completeness theorem, source-to-Lean
theorem, or concrete successful runtime instance is claimed. Exact `Arc`
identity is intentionally conservative: if the producer supplies a cloned
declaration rather than the retained original allocation, this query returns
unavailable and needs owner/review adjudication rather than loosening identity.

Falsifiers include wrong or duplicate Catch slot-51 facts; a provider view at a
different occurrence or declaration; mismatched annotation member; missing or
duplicate slot emission; changed current slot/readback/admission; reversed
lower edge; foreign relation pair; failed Internal ancestry; two matching
views, endpoints or paths; and a disconnected Catch or entry root. No tests
were added or run, so these are source-level guards, not executed falsification
results.

## Checks, resources, and remaining TODOs

Checks performed: rehashed R48 and every frozen direct Rust/R45/R47/design pin
listed above; manually inspected the R47 Rust implementation and its frozen
proof/review, R45 source handoff/review, `candidate_receiver.rs` source slot-51
selection and operation-origin consumer, and the current lower-bound/evidence
owners. No build, tests, Cargo, formatter, scratch, cache, target, environment,
worktree, or nested CLI was run, per the contract. No runtime behavior was
observed. No source/test expectations were altered.

Assignment cap: 1,500 seconds. Actual active work spent / remaining: UNKNOWN
from worker runtime metadata; no resource telemetry is available.

Mutual TODO `R48-PROVIDER-COMMON-ENDPOINT-PROOF-1` for the proof lane:
preserve the original provider occurrence/declaration and original slot-51
Catch-input quantifiers; provide a finite checked relation/path for each exact
physical lower edge; prove accepted certificates have the same terminal
AnnotationMember on both paths and inherit exact R47 entry arrival. Inputs are
the frozen R48 contract, this source handoff/source hashes, R45 `accepted_payload`,
and R47 `apply_to_internal`. Proposed output is only the leased R48 Lean file
and proof handoff. Falsify by accepting a stale/reversed/foreign edge, different
terminal endpoints, wrong operation origin, or a Catch path not rooted at the
unique slot-51 fact. Lean acceptance still cannot prove Rust extraction
completeness or runtime success.

Source-owner TODO `R48-PROVIDER-EXTRACTION-REVIEW-1` for Luna/fresh reviewer:
check the exact `Term` to endpoint mapping for the retained source slot-51
fact, relation ancestry of every Internal path edge, exact declaration Arc
identity through the producer, physical-index lifetime/rollback behavior, and
whether any required current edge is omitted from retained admission/emission
records. First missing evidence is an independent source/runtime correspondence
review of these frozen hashes. Output is a review receipt on the primary's
leased review path, not a code change by this worker. Falsify by any accepted
endpoint supported only by family/canonical equality or any physical slot
without its own retained evidence.

The exact unproved source gap is completeness of this private extraction against
the actual generated constraints and propagation lifecycle, plus success on a
concrete running source instance. The certificate remains provisional; it does
not close provider arrival, Catch correspondence, permission consumption,
subtraction, parent A/B, hygiene, or production gates.

No new paths besides the two leased Rust artifacts and this handoff were
created. Existing unrelated untracked disposable candidates observed at startup
were not touched: `.agents/skills/yulang-lean-proofs/scripts/__pycache__/` and
`notes/theory/lean/.task-tmp-selected-module-freshening-r1/`. No scratch or
generated output was created by this assignment.

Worker state: STOPPED after this handoff write; writes ceased. No commit,
staging, Git mutation, or current-state edit was performed. Frozen R48 Rust
handoff revision 1; its final SHA-256 is reported in the intake message.

STOP.
