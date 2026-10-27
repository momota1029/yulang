# Permission projection r8-r4: context frame and corrected conditional boundary

Status: FROZEN revision 1 on submission; producer evidence, NOT_REVIEWED.
Outcome class: bounded static source evidence and conditional derivation.
No reachable preservation theorem, source counterexample or r7 premise removal.

## Assignment, authority and authentication

Actual worker: `/root/formal_permission_projection_source_r8_r4`; separate session
UUID UNKNOWN. ACK/active-work receipt sent before source bodies at
2026-10-27 22:51:30 UTC. Primary subsequently recorded ACK and RUNNING in current
state. Requested model/effort, observed in that record: gpt-6-luna/high;
effective model/effort UNKNOWN. Sole author; no descendants or prover launch.
The yulang-proofs skill governs the source/conditional distinction; this packet
has no dispatch or independent certification authority.

Primary baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`, authenticated as
contract metadata, not independently resolved by Git. All current bytes below
matched their prescribed SHA-256 before source-body inspection. No dependency
hash changed. Baseline hash equality establishes byte identity, not semantics.

| Input | SHA-256 |
| --- | --- |
| Original r8 contract | `99835a8d22b3b61c90500706245fd5e28aeee238905cca1eb217d8c2f274cd46` |
| Amendment 01 | `3c2782ff6e375b4f22278ead3d7f5834b4d2d291f83ab6b9b7b68624c2b040d1` |
| Amendment 02 | `c50bb1d2f500f6604eab456de1ea8c157415ed608518c5ff3be54e675aa3f7fc` |
| Governing amendment 03 | `d8c9ef2120ee2f25396c4dbb54b26370a116f917848dbe316cff06533ab5c03a` |
| r7 contract | `40035df185bb2266f395264a137babf9b433e875922ff86f453836fba278a767` |
| r7 source | `98cf92059d11ea1efd875c7af9d84c86be236f9c52b7b07acadfcac082c8b79d` |
| r7 review | `635e94a1eec04348fdd87b7c1802101bca10a6fa8631e3e82d0eb39f26a12c7c` |
| Corrected frozen r7 outcome | `7fab9c3f7bbe4c6072702b30973e44c705122aa244877addd1ff4d2a9a65eef8` |
| r8 stop handoff | `e9926aaf56c8ea35b1227b7c27693f7c14eb872a46b8b6826ca6cda46951a4c8` |
| r8-r2 source | `19bffa5c2fdfdd38d8205dc1368b61b475811acaf2d00073cccbda0f6fecb8c9` |
| r8-r2 review | `6ff6c8e8a9c343c93aaf673903b69acce4633f0df52a035844b1af6f9870f99a` |
| Frozen r8 outcome | `c69858fa3119d304d5990b8f520855becfe9e81d5f4ab6feba21c119727ade54` |
| Frozen r8-r3 source | `aafd543e2dc727d8999342ff0d76b8419730befd48cbf9a2d8cd6116a0771148` |
| Frozen major review | `19aabd5cee2cd4c92f1bdc7559b60c66022a20403792d70da97a9931538e86f6` |
| candidate_source.rs | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| candidate_intrusion.rs | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| candidate_effect.rs | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| candidate_scheme.rs | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| shadow_apply.rs | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| lib.rs | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| term.rs | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| tools/inference-playground/src/scheme.rs | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| Annotation policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| candidate_extrusion.rs | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| Newly admitted candidate_context.rs | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |

Solver filenames above are under crates/yu-solver/src. Annotation policy is
notes/design/2026-10-10-annotation-effect-hygiene-integration.md. Governing
selected sections remain §§1, 1.1, 1.2 and 4, with §6 retracted; inference
principles §§4–5 preserve necessary abnormal-path safety without a new general
rollback duty. No selected language meaning was reopened. Root/base instructions,
research/design/Git rules, current state, README and exact amendments were read;
some large combined read outputs were truncated, so no exhaustive governance or
transitive-body audit is claimed.

## Concrete context effect derivation

Let P be the pair of complete intrusion parent vectors, including lengths and
allocation ownership; let J be active intrusion Undo identity and its forests
sequence. The following is a bounded frame for the inspected context core,
excluding the terminal session resource sampler and wider unscoped insertion
composition. It uses ordinary sequential safe Rust ownership, nonreentrant std
collection operations and successful return. It is not inferred from &mut self.

At candidate_effect.rs:697, the actual callee is context.rs:4318. After checking
witness.to, candidate_context_pair canonicalizes both endpoints. Its body at
:3349 calls canonical_value/effect; lib.rs:11839/:13491 call read-only
intrusion.value_rep/effect_rep, whose representative loop has no compression.
The callee then borrows the nested context, not either parent Vec or J.

The core's call tree has these concrete effects:

- snapshot (:753) reads group heads and forms a copied coverage record;
  intern_snapshot (:766) reserves and appends snapshots and snapshot_keys, or
  increments snapshot_hits. Neither stores a parent-vector reference.
- transported_scoped (:2867) obtains copied ScopedFlow and rewrites only the
  local demand root; scoped_flow reads relations/scope_flows. post_check_context
  (:3297) reads discharged/residual metadata.
- relation_with_scoped (:3062) checks context/kind restrictions, optionally
  interns scope_flows/keys, then interns relations/keys/pair_heads. Its called
  ScopeInventory::charge is candidate_source.rs:217, not a new owner: it checks
  work_used + work and assigns only work_used. No transformer execution occurs
  on this path. assert_context reads contexts.len().
- dependency (:3153), for Transport, does not call the solver or merge rows.
  It appends dependencies/keys and may add a BundleTransports entry and call
  bundle_edge. The inspected bundle_edge -> bundle_link -> incidence_insert /
  activate_bundle_transports chain (:2677–2741), including BundleTransports::insert
  (:495), updates owned incidence maps/logs/heads and sparse transport maps/logs.
  Its loops follow owned relation IDs; no outer-session callback exists in these
  bodies. Derived dependencies in ordinary bound construction additionally call
  edge, which updates edges/edge_keys/edge_log and uses this same bundle chain.
- evidence.transform (:861) reads antecedents/direct admission association,
  appends transforms/keys, reverse edges and child indices/logs; attach (:3283)
  appends bound_keys and replaces the context bounds head with its previous
  index retained. These are different fields from intrusion.values/effects.

Induction on these concrete calls and loop iterations yields P'=P and J'=J
for the inspected core. Each leaf writes only the enumerated owned nested
containers or locals; composition preserves the frame; each loop iteration
has the same frame. Errors can leave context metadata changed but introduce no
core parent write. This is stronger than preserving two selected roots: it
preserves every parent entry for this subtree. It does not prove that P was
closed initially, or prove the full outer call including resource sampling.

Copied-bound evidence (:1835–1841, :2032–2043) delegates to the inspected evidence
snapshot/intern/admit/reserve/emit bodies. admit saves the old group in group_log
before replacing its admission head; emit likewise saves the old group before
replacing its emission head. Snapshot allocation and emission counters have no
parent-vector effect. Evidence rollback (:664) reverses reverse-head/child logs
and group_log before truncating appended evidence records. Context rollback
(:2076) reverses incidence, relation/pair-head, bound-head and edge logs within
its own Checkpoint; it has no forest-parent access. These are context-local
restoration facts, not proof of the outer checkpoint's completeness.

## Resource, outer mutation and checkpoint boundary

The outer merge at intrusion.rs:613–691 selects roots, appends (copy,from) to
J.forests if an active intrusion Undo exists, journals destination bound storage,
copies both sides, transfers origins, and optionally splices capture incidence
before one final parent write. Bound insertions change bounds/effect_bounds,
flags, counters and intrusion.dirty. Splice (:651) records old buckets and the
old destination-tail link before changing those capture fields. No effective
forest write occurs in those direct statements before the final link.

The resource path is substantive: journal_value/effect_row calls
observe_typed_route_capacity (:9253), which can sample and set failure flags.
The sampler (:10774 -> :10821) calls intrusion/effect/context bytes, including
ScopeInventory::bytes and replay_operation_bytes, and passes shared owned
storage plus mutable ProductionCounters into sample_f4_resource_parts (:11017).
The inspected context byte bodies sum capacities, lengths and owned nested
storage; they call no context execution or row merge. The sampler tail publishes
prepared counters after checked.finish. Term accounting delegates through
lib.rs:3720 into admitted term.rs:867 capacity_snapshot. These inspected pieces
support a resource frame, but this timed packet did not close every transitive
reservation/accounting callee and every branch of the complete outer interval.
In particular record_incoming_bound_capacity_growth (:16669 onward), its full
capacity/reservation tail, and its composition with all source-reachable journal
states have not received a complete body/callee induction here. No extra owner
was opened, and no unadmitted body is asserted necessary.

STOP equation: for EVERY reachable successful merge interval, all helper calls
(including the complete resource/capacity chain) preserve P, graph lifetime and
active J identity/frontier, so that the early inverse is temporally adjacent to
the next effective forest mutation. This equation remains unsupported as a
whole. The bounded context-core frame does not discharge it.

The actual rollback chain is lib.rs:9664 taking the route journal, then
intrusion.rollback, effect_algebra.rollback and context.rollback. Intrusion
replays forests in reverse before truncating the two vectors (:201–223).
This establishes the visible ordering, conditional on a complete log for that
same checkpoint. No-Undo merges intentionally lack an inverse entry; this is
not a successful wrong-image counterexample. Do not infer full checkpoint
association or row lifetime merely from this rollback order.

## Correct conditional application and remaining gates

For each selected same-kind forest separately assume H0: it is a closed finite
forest at interval entry, selected rows are in range and denote the intended
live rows. Assume H1: the COMPLETE interval preserves the whole parent function,
vector identity/lifetime and selected roots. Assume H2: the same active checkpoint
owns every effective forest inverse in temporal order throughout the relevant
history, including subsequent operations and rollback.

H0 + H1 imply whole-forest closure immediately before :679/:691, including all
unselected classes. Then the valid r8-r2 root-link lemma applies to the distinct
self-roots. H2 separately supports reverse replay/truncation under r8-r2's prefix
and lifetime hypotheses. The context-core derivation above supplies only part
of H1. It supplies neither H0 nor complete H1/H2. Correct logging alone cannot
supply H0/H1. This corrected conditional removes no r7 premise.

B, D, reachable whole-forest/lifetime preservation, r1 Lean verification,
original parent A/B, source/native, full inference/executor and production remain
OPEN. No reachable cycle, invalid successful capture or wrong-image export was
found; there is no smallest source witness. No synthetic countermodel is
substituted for source reachability.

## Checks, coverage, resources and next action

Commands: sequential cat/sed/rg/sha256sum and clock; one leased artifact write.
All 26 authentication checks MATCH. No tests, builds, probes, Cargo, Lean/Lake,
compiler edits, Git, network, quarantine access or descendants. No executable
oracle, seeds/ranges or mutations; static source inspection shares Rust/std
ownership and sequential-call assumptions. Hashing independently authenticates
bytes only. No independent review of this output is claimed.

First clock 22:51:30 UTC; last source inspection clock 22:54:19 UTC on
2026-10-27. Exact launch-to-stop CPU/RSS telemetry UNKNOWN; charge full 200s,
one CPU, 1 GiB cap. Prior charges remain intact. Writes stop on submission.
Recommended next action: primary reviews this bounded context frame and assigns
one focused completion of the exact outer resource/journal frame equation above,
using the existing source union and original forest/lifetime premises.

## Commit packet

- Exact leased/changed path: tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r4.md only.
- Baseline SHA: 3cc8a897fe08980576b1582952a95acab55f09d2 (primary pin).
- Dependency hashes changed: none; all 26 pins MATCH.
- Review: NOT_REVIEWED; frozen producer evidence, no independent certification.
- Checks run: required SHA authentication; bounded source/field/callee inspection; no executable verification.
- Proposed commit: `research: bound context transport frame and retain merge preservation premises`.
- Shared deltas left to primary/curator: record STOP/full 200s charge, preserve all OPEN gates, retain corrected conditional and incomplete outer-frame equation, obtain non-author review. No shared files edited.
- Worker: STOP on submission; writes stopped; no descendants or outstanding descendant leases.
