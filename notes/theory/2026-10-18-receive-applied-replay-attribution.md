# Complete-capture Replay attribution

Assignment `RECEIVE-APPLIED-REPLAY-ATTRIBUTION-20261018`, revision1.
Author `/root/npair_durable_capture_proof`; descendants0.
Sprint `npair-replay-durable-capture-20261018`, contract SHA-256
`ec72f581fd6e3857bb3181996da605d0638c3d739960d976093872e2ea77e76b`.
Baseline `551773b8692540a55f69014c2194ff081331b2cb`.
Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`: OPEN,
original conditions closed0. Status: complete capture classified; no Replay row.
Independent review pending; claim class source-native-evidence.

## Attribution criterion and source derivation

Reuse the source correspondence artifact SHA-256
`e636422256e63af9cb04b8962f95fd0fbc845283aabcc7635c07fe5483d4e503`
only within its actual successful-formation and exact companion/HIR premises.
All13 frozen contract pins were reported MATCH by Luna; this author inspected
the pinned harness, `shadow_apply.rs` and `candidate_context.rs` directly.

1. Complete stdout/stderr must be frozen with metadata establishing successful
   command completion, switch enabled, byte counts and matching SHA-256.
2. Successful harness exit must establish its no-conflict check and exactly one
   `candidate.source_call[i]` for the received owner. All printed exact checks
   must be true: owner, Apply, both operands, scopes, ModuleDef(receive)/
   ModuleDef(f0), checking occurrence and cause. Pointer/key/parse ownership
   checks in the harness authenticate this call within this actual HIR.
3. Take the native demand root printed for that same index i. Locate an actual
   stderr `candidate.call_replay call=i ...` row whose demand_root equals that
   root and whose `native_root_matches=true` and ordered
   `endpoint_pairs=(lower:true,upper:true)` both hold. Retain its child/lower/
   upper relation IDs, lower_input/upper_input and use_instance without swapping
   endpoints or identifying different rows.

The source justification is `ContextState::replay_demand_rows`: it selects an
actual retained `Dependency::Replay {child,lower,upper,lower_input,upper_input}`,
requires `scoped_flow(child).demand`, and emits `demand.original_call`. Each
endpoint boolean separately compares that relation's retained ordered pair
with `bound_pair` of the corresponding input. `infer_module_candidate_mode`
in `shadow_apply.rs` fetches candidate_calls.calls[call_index].native and
compares native.demand with demand.root before writing the row. The harness
then authenticates the public source_call at this same index. Thus an accepted
join witnesses one actual demand-bearing Replay associated with this exact
companion application in this execution. An enabled observer summary or
aggregate relation count supplies none of these joins alone.

An absent matching row in a complete capture establishes only absence from
that capture. It proves neither semantic impossibility nor consumer completeness.
The companion source/native identities do not identify the original fixed
semantic c. F1/FK1, universal R/W/Z/domain actions, active-consumer reflection,
NPAIR, Call, N-Transport, soundness, principality and termination retain their
original quantifiers and remain OPEN.

## Runtime classification

Implementation author `/root/npair_durable_capture_impl` froze the sole run:
UTC start `2026-10-17 23:20:14 UTC`, end `2026-10-17 23:20:20 UTC`, exit0,
observer switch1, direct separate stdout/stderr redirection, invocation1.
Metadata reports preflight CLEAN, explicit Luna release and capture_complete=true.
This author independently rehashed the three frozen files and inspected both
streams. Byte counts agree with metadata and both files end with a newline.

| Frozen input | Bytes | SHA-256 |
| --- | --- | --- |
| `tasks/agent-loop/runtime/20261018-receive-applied-durable.stdout.log` | 79315 | `5bb1dd3bcbabd97bb94fca9a12fdc17a882d1c9a916c692fe55f1a302984d311` |
| `tasks/agent-loop/runtime/20261018-receive-applied-durable.stderr.log` | 1986 | `9a56194c1d4734309880847cd18ee2a9a0dab194815b0a40aad2378a5448f7e9` |
| `tasks/agent-loop/runtime/20261018-receive-applied-durable.meta.json` | implementation-owned metadata | `142edef3b35d58279421013c44e81ac96ac8123be50ab4e75186824f583ca2ad` |

Stdout lines26–31 establish ModuleDef(receive)/ModuleDef(f0), parse ownership,
Apply/callee/argument occurrence ordinals18/19/20, candidate.observes_hir=true,
candidate.conflicts=[], and the single authenticated source_call[3] with all
eight exact booleans true. Its validated native demand is
`Term { brand: TermArenaBrand(1), index: 379 }`; its ordered children are
argument375, argument evaluation effect377, invocation effect378 and result376,
all in that same arena. Opaque source keys/root debug renderings are not used
as identity proofs; the reviewed harness's actual pointer/key/owner checks are.

There are **zero** occurrences of the actual row prefix
`candidate.call_replay call=` in either complete stream (stdout34 lines,
stderr52 lines). Stderr contains build warnings and Cargo's execution notice,
with no typed Replay row. Stdout line34 prints only the enabled-observer summary.
Thus the source-call/native-demand half of the join is established, while no
row supplies its other half. In particular no native_root_matches or ordered
endpoint_pairs certificate exists in this capture. Result: **no matching
demand-bearing Replay row observed in the complete capture**.

This resolves the earlier transcript-truncation uncertainty, not the original
theorem obligation. It does not determine whether there was no retained Replay,
whether Replay children lacked scoped demand, or whether another observer
selection premise failed. The exact next discriminating evidence is owned by
`candidate_context::ContextState::replay_demand_rows` and its demand-producing
callers: distinguish retained Replay dependencies from child scoped-flow demand
for authenticated call3/root379. Such instrumentation requires a new Luna lease
and reviewed snapshot; another identical run is not evidence for that premise.

## Resources and ownership

Preparation allocation30s, capture classification allocation90s; total cap120s,
full120s conservatively charged. No budget rollover; CPU/RAM unmeasured.
Read-only static inspection only; no compiler/runtime/build/test/check commands,
Git, generated scratch outputs or descendants. Exact outputs are this note and
`tasks/agent-loop/inbox/20261018-receive-applied-replay-attribution.md`.
Fresh independent review and Luna adjudication remain required. Writer STOPPED
after freezing the assigned note and inbox; no descendant or scratch leases.
One read-only inspection attempted `python`, which was unavailable; the same
byte inspection succeeded with `python3`. Neither invoked the compiler or tests.
