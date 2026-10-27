# Permission projection r8-r6: outer accounting frame and exact residual

Status: FROZEN producer source evidence; NOT_REVIEWED. Full H1 OPEN.
Method: bounded static source/callee inspection, no executable experiment.

## Authority and execution order

Worker `/root/formal_permission_projection_source_r8_r6`; session UUID and effective model/effort UNKNOWN. Primary baseline `3cc8a897fe08980576b1582952a95acab55f09d2` is contract metadata, not independently resolved through Git. Governing contract amendment05 SHA-256 `86066eff5db9b1898c81431ffe0a425cea0d617e5d86f79e9973f1460161c492`. Sole write lease is this file. No changed dependencies.

1. First standalone clock/contract read returned `2026-10-27T23:08:57Z`; deadline `23:10:57Z` (120 seconds).
2. Separate standalone `python3` command authenticated the contract hash, extracted its table with `re.findall(r'^\| `([^`]+)` \| `([0-9a-f]{64})` \|$', text, re.M)`, asserted exactly 30 rows, SHA-256-hashed each file, printed each MATCH, and exited 0. Tool chunk `fddf56`, explicit exit_code 0; terminal line `AUTHENTICATION SUCCESS files= 30 UTC= 2026-10-27T23:09:00.886295+00:00`. It read file bytes only to hash; no source excerpts shared that command.
3. ACK to primary followed authentication, before substantive/source-body inspection. Subsequent governance reads included root/base instructions, research/design/Git rules, proof skill, contract and reviewed r8-r4 source/review. Some combined governance outputs truncated; exhaustive governance inspection is not claimed. The sprint skill applies to the primary; no child team started.
4. First source body command was chunk `3d05da`, after the successful result and ACK. Source reads thereafter were sequential sed/rg; source-r8-r5 excerpts were not consumed or reused. Its process deviation remains preserved.
5. Last source lookup/clock chunk `a60fb2` returned `23:10:38Z`. This artifact's freeze clock appears below. No further source search is planned.

Every manifest row below was individually printed MATCH in step 2 (the prescribed hash equals the observed hash):

| Input | Observed SHA-256 / MATCH |
|---|---|
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8.md` | `99835a8d22b3b61c90500706245fd5e28aeee238905cca1eb217d8c2f274cd46` MATCH |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-01.md` | `3c2782ff6e375b4f22278ead3d7f5834b4d2d291f83ab6b9b7b68624c2b040d1` MATCH |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-02.md` | `c50bb1d2f500f6604eab456de1ea8c157415ed608518c5ff3be54e675aa3f7fc` MATCH |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-03.md` | `d8c9ef2120ee2f25396c4dbb54b26370a116f917848dbe316cff06533ab5c03a` MATCH |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-04.md` | `c56f4a6eb8dcb68cf50309789640b4749943e12fbd11f47a1bbea2969c57c605` MATCH |
| `tasks/agent-loop/history/formal-permission-projection-20261028-r8-addendum-03-outcome.md` | `76657cf7e8bfa7fd6e5af8beb8337063f82826ea51e4bb0222b7e3cb5434271e` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r5.md` | `f3ad25273afd2626a4c7821651e534cd096ad78e5e3412dfbdfa04be6426c381` MATCH |
| `tasks/agent-loop/sprints/formal-permission-projection-20261028-r7.md` | `40035df185bb2266f395264a137babf9b433e875922ff86f453836fba278a767` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r7.md` | `98cf92059d11ea1efd875c7af9d84c86be236f9c52b7b07acadfcac082c8b79d` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r7.md` | `635e94a1eec04348fdd87b7c1802101bca10a6fa8631e3e82d0eb39f26a12c7c` MATCH |
| `tasks/agent-loop/history/formal-permission-projection-20261028-r7-outcome.md` | `7fab9c3f7bbe4c6072702b30973e44c705122aa244877addd1ff4d2a9a65eef8` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8.md` | `e9926aaf56c8ea35b1227b7c27693f7c14eb872a46b8b6826ca6cda46951a4c8` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r2.md` | `19bffa5c2fdfdd38d8205dc1368b61b475811acaf2d00073cccbda0f6fecb8c9` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r2.md` | `6ff6c8e8a9c343c93aaf673903b69acce4633f0df52a035844b1af6f9870f99a` MATCH |
| `tasks/agent-loop/history/formal-permission-projection-20261028-r8-outcome.md` | `c69858fa3119d304d5990b8f520855becfe9e81d5f4ab6feba21c119727ade54` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r3.md` | `aafd543e2dc727d8999342ff0d76b8419730befd48cbf9a2d8cd6116a0771148` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r3.md` | `19aabd5cee2cd4c92f1bdc7559b60c66022a20403792d70da97a9931538e86f6` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r4.md` | `3171fdaec7fe72fa02fd467785a3b4506af0e2c54fbfea34e4e3c7a503d71b94` MATCH |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r4.md` | `893203e14c57d2a6467f1ee0c085a2a772db07df463e6418cedcd74953c8d45f` MATCH |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` MATCH |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` MATCH |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` MATCH |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` MATCH |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` MATCH |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` MATCH |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` MATCH |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` MATCH |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` MATCH |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` MATCH |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` MATCH |

## Frame, concrete effects and remaining equation

Use P for BOTH entire intrusion parent vectors, their lengths, allocations and live-row identities. Use J for the active route journal's intrusion Undo identity and its forests sequence, measured after the prospective `(copy,from)` append. Assume ordinary safe sequential Rust, standard nonreentrant collection allocation, and the reviewed r8-r4 context-core frame at its pinned bytes. This is conditional static evidence, not a reachable-session theorem or oracle result.

Start inspected: lib.rs:16669 `record_incoming_bound_capacity_growth`. In production (`not(test)`), unchanged capacity skips accounting and returns the supplied reservation result after enum conversion. Changed capacity can set `route_attempt_physical_change`, increment `route_journal.incoming_bound_growth_events`, and compute a preflight through checked subtraction/multiplication/addition. Preflight errors set `incoming_route_event_sample_failed` when incoming accounting is active and return immediately. No rollback is called.

The concrete callee `record_bound_capacity_growth` (:16614) precomputes the payload delta and growth/rebuild totals; for old rows it increments `route_journal.retained_bound_growths`; it assigns `bound_payload_bytes` and `execution_counters.bound_table_growths/bound_table_rebuilds`. It accesses the route journal but neither replaces/takes it nor changes `journal.intrusion` or `Undo::forests`. Scalar checked arithmetic and enum conversion (`From<ConstraintError>`, :4175) introduce no session callback. Thus this accounting core preserves P and J on successful returns and on its propagated error prefixes. Accounting changes may survive errors; full restoration is not asserted.

The active-accounting branch invokes `sample_f4_resources` (:10774), through `with_finish_output` (:10791) to `with_term_override` (:10821), then `sample_f4_resource_parts` (:11017). This is a real transitive obligation, not a purity inference from receiver borrowing. Inspected concrete sampling inputs include route-journal capacities, workspace payload bytes, intrusion and intrusion-Undo byte counts, source/local cursor sizes and local-route allocation capacity. The sampler computes into a cloned ProductionCounters value and publishes that value only after checked.finish; production failure does not execute route rollback. `ResourceSampleChecked` (:330) changes only its local Cell overflow flag; its arithmetic iterators close over scalar counts. InstantiationScratch (:8144/:8156) reads its seven owned capacities and calls checked_fixed_capacity_bytes (:378). RouteMutationJournal (:8444/:8459) reads seven capacities, workspace capacity/payload, with the same scalar helper. ConstraintStore (:3720) delegates to term.rs:867 checked_retained_bytes -> :872 capacity_snapshot -> :1007 checked_capacity_bytes; these read term page/map/journal capacities and structural payload counts. No inspected reservation/accounting body changes either parent vector, replaces the candidate graph or takes/replaces the active route journal. Nested intrusion/effect/context byte summaries rely on the reviewed r8-r4 resource/context evidence; this receipt does not promote that prior partial resource audit into complete transitive verification.

Actual journal row calls (:9548/:9597) reserve only `journal.value_rows` or `journal.effect_rows`, sample via observe_typed_route_capacity (:9253), then mark row_seen and append the corresponding row-length/flags/level undo. Production reserve_f5b (:135) dispatches to Vec::try_reserve (:88), maps failure to an enum, and has no solver callback. It can reallocate those row-undo vectors, which are distinct from intrusion parent vectors and intrusion Undo::forests. `preflight_bound_capacity_growth` (:16578) checks scalar headroom only.

The actual insertion macro in candidate_extrusion.rs:702 reserves one of the eight nested bound lanes, calls :16669 and only then pushes the bound. It touches bounds/effect_bounds, associated flags/counters, context emission metadata and intrusion.dirty. The merge passes capture=false, so its candidate_register_capture_bound branch is unreachable here. It still calls candidate_bound_origin_with_evidence before the macro. The scoped BoundTransport branch chooses relation=None; the unscoped branch invokes candidate_context_bound. The reviewed r8-r4 context-core transport induction is reused, not reaudited.

**STOP: first residual equation in completing the outer insertion composition:** for the merge-reachable unscoped branch, candidate_effect.rs:552 `candidate_context_bound(bound, origin)` -> candidate_context.rs:3888 -> :3898 `candidate_context_bound_for(..., BoundConstructionPurpose::Ordinary)` must preserve `(P,J)` for every successful return and every propagated error prefix, including all of that wrapper's session calls, reservation/sampling and its context association. This packet has not supplied that complete wrapper/callee induction. The reviewed r8-r4 core frame explicitly excluded wider unscoped insertion composition; its nested context purity alone cannot fill this gap. No new owner is requested. This is an exact outstanding effect equation, not evidence that the callee mutates a forest. Full outer sampling composition also remains conditional on the prior partial byte-summary evidence, so complete resource closure is not claimed.

No reachable falsifier, minimized source witness, successful wrong-image export, or H1 composition theorem is established. This source cut stops the packet; no further automatic packet is recommended under amendment05.

## Application, limits and resources

Retain the corrected conditional: H0 (entry whole-forest closure and live in-range intended rows) + COMPLETE H1 imply whole-forest closure immediately before the final link; the local distinct-root link lemma then applies. H2 separately supplies same-checkpoint complete temporally ordered inverses and the prefix/lifetime conditions for replay. The bounded accounting core removes neither H0, full H1 nor H2. B, D, reachable forest/lifetime, r1 Lean, original parent A/B, source/native, full inference/executor and production stay OPEN.

No tests, builds, probes, Cargo, Lean, network, Git, descendants, compiler edits or other writes. No random seeds/ranges, mutations or executable oracle; source interpretation shares Rust/std assumptions with the argument. Hash verification independently establishes byte identity only. CPU time and peak RSS UNKNOWN; one CPU and 1 GiB were the caps. Charge the full 120-second grant without returning uninstrumented time. No independent review claimed. Production configuration was the analyzed domain; cfg(test) observers/fault injection and panic/allocator-abort behavior were not proved. Hashes were authenticated once, before source reading; no final reauthentication performed.

Recommended next action: primary preserves the exact residual and all OPEN gates, adjudicates whether this bounded evidence warrants the reserved fresh review, and ends automatic FPP source continuation as contracted.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r6.md` only.
- Baseline SHA: `3cc8a897fe08980576b1582952a95acab55f09d2` (primary pin).
- Dependency hashes changed: none; all 30 manifest entries and amendment05 MATCH before inspection.
- Review status: NOT_REVIEWED, frozen research-only producer evidence.
- Checks already run: standalone python3 30-file SHA-256 authentication, static source/callee reads and clocks; no executable verification.
- Proposed commit: `research: delimit outer merge accounting frame and unscoped composition gap`.
- Shared-record deltas left to primary/curator: full 120s charge; actual source/write cessation; residual candidate_context_bound_for equation; all parent gates OPEN; no further automatic source packet; review/adjudication disposition. No shared record edited.
- Writer STOP after this artifact write; no descendants, background processes or outstanding child leases.

Freeze/write clock: `2026-10-27T23:11:39.608688+00:00`; cap deadline `2026-10-27T23:10:57Z`.
