# Frozen handoff: receive applied Replay attribution

Sprint `npair-replay-durable-capture-20261018`; contract SHA-256
`ec72f581fd6e3857bb3181996da605d0638c3d739960d976093872e2ea77e76b`.
Assignment `RECEIVE-APPLIED-REPLAY-ATTRIBUTION-20261018`, revision1.
Baseline `551773b8692540a55f69014c2194ff081331b2cb`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`: OPEN,
original conditions closed0. Original source domain/quantifiers unchanged.
Role constructive attribution author; actual worker `/root/npair_durable_capture_proof`.
Fresh ACTIVE checkpoint sent to Luna in this session, followed by WAITING until
capture freeze. Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN.
Author only this worker; descendants0. No independent self-certification.

Outcome class: source-native-evidence; complete-capture absence observation.
The complete capture authenticates source_call[3] for the exact companion
received Apply, with all8 exact checks true, no conflicts, exact HIR ownership,
and native demand TermArenaBrand(1)/379. There are zero typed
`candidate.call_replay call=` rows in either complete stream. Therefore no
row-to-source/native join is available in this capture. This discharges the
capture-completeness uncertainty; it establishes no semantic impossibility and
closes none of the original parent conditions.

Source path: actual companion ModuleDef(receive)/ModuleDef(f0) Apply -> retained
candidate call -> authenticated source_call[3]/native demand379. Replay observer
path reads actual retained Replay dependency -> scoped_flow(child).demand ->
original_call index -> native-root and ordered endpoint booleans. The latter
path emits no row in this capture; aggregate/summary output cannot fill it.

Artifact:
`notes/theory/2026-10-18-receive-applied-replay-attribution.md`
SHA-256 `f39055008cd8b1168229ad34993a088ca3fdeabd7b1a1af2548fc081acedf791`.
Direct frozen capture dependencies, authored by `/root/npair_durable_capture_impl`:

- stdout `tasks/agent-loop/runtime/20261018-receive-applied-durable.stdout.log`:
  `5bb1dd3bcbabd97bb94fca9a12fdc17a882d1c9a916c692fe55f1a302984d311`.
- stderr `tasks/agent-loop/runtime/20261018-receive-applied-durable.stderr.log`:
  `9a56194c1d4734309880847cd18ee2a9a0dab194815b0a40aad2378a5448f7e9`.
- metadata `tasks/agent-loop/runtime/20261018-receive-applied-durable.meta.json`:
  `142edef3b35d58279421013c44e81ac96ac8123be50ab4e75186824f583ca2ad`.

Reused conditional source proof, author `/root/npair_local_route_authentication_proof`:
`notes/theory/2026-10-18-receive-applied-source-correspondence.md`, SHA-256
`e636422256e63af9cb04b8962f95fd0fbc845283aabcc7635c07fe5483d4e503`.
All13 contract direct pins reported MATCH by Luna. Source inspections use exact
contract-pinned harness, shadow_apply.rs and candidate_context.rs. Prior
truncated output is rejected as classification evidence, not reinterpreted.

Checks: static source reads, frozen file SHA-256 and byte/row inspection only;
stdout79315 bytes/34 lines, stderr1986 bytes/52 lines; each ends with newline.
Metadata invocation1, observer1, exit0, complete direct capture. No compiler,
runtime, build, tests, Git, generated scratch paths or descendants here.
Unavailable `python` read-only inspection retried using available `python3`;
this was not a harness retry. Budget cap120s; full120s conservatively charged,
remaining0, no rollover; observed CPU/RAM UNKNOWN.

Mutual TODO `REPLAY-DEMAND-DISCRIMINATION-20261018`: original parent unchanged;
first missing evidence is whether retained Replay children have scoped demand
for call3/root379. Owner candidate_context::ContextState::replay_demand_rows
and demand-producing callers. Inputs are these frozen complete logs/source;
proposed next output is bounded actual retained-dependency/demand evidence under
a new Luna lease. Falsifier for an attributed-row claim is absent/different call
index, unequal root, false ordered endpoint certificates or failed source
authentication. No same-command rerun or semantics change is authorized here.

Worker STOPPED; writes ceased after freezing these exact two leased paths.
All new paths are this inbox and the theory artifact; scratch0, descendants0,
unresolved descendant leases0. Frozen revision1 awaits fresh independent review
and Luna integration. No further in-envelope step or writing remains.
