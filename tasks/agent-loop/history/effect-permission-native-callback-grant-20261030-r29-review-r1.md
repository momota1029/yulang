# R29 independent precompile source review — revision 1

**Verdict: REJECT for the exact frozen Rust/schema pair below.** The source gate is not met. No compilation, runtime, mutation result, selected-main result, Lean/Lake audit, checker result or proof has been executed or established by this review. A future source ACCEPT would authorize no execution by itself: Luna must issue a separate stage receipt.

Assignment: fresh independent read-only source review, `/root/r29_review`, R29 current session; requested compiler-referee role. Actual model/effort metadata: UNKNOWN. No authoring collaboration, descendants, Cargo, rustc, test, runtime, Lean, Lake, checker or Git operation. The only written artifact is this leased review handoff. Source, dependencies and governing contract/schema were inspected before the author's handoff; the handoff and source mutation design were treated as claims, not evidence of execution or correctness.

All source locations below are relative to `W=isolated/ep-native-callback-grant-r29/project/tools/inference-playground/src/runtime/`.

## Major 1 — recomputing Grant after owner deactivation rejects the unchanged positive certificate

Locations: `machine.rs:4318`, `4386–4388`, `1755–1760`, `2180–2204`; `receiving.rs:643–649`, `733–734`, `859–868`.

The test first completes `callback.run`, then calls `validate_callback_route_evidence` with `&callback.invocations`. This is the final invocation store. The callback's Catch owner is the relay invocation. After selecting its arm and returning integer 1, the retained `ReceiverReturn` calls `leave_owner(..., true, ...)`, which sets that invocation's `active` field to false. The validator recomputes `local_grant` against that final store. `local_grant` immediately returns false for an inactive receiver, whereas the evidence deliberately retains the successful query-time result true. The final equality at `receiving.rs:734` therefore rejects the unchanged positive candidate. This is a source trace, not a reported test result.

The change retains the actual query result correctly at `machine.rs:2653–2660,2719`; it then crosses the query/completion phase boundary by treating final liveness as query-time liveness. A recorded `active_invocation_at_query` Boolean in the candidate does not restore the independently owned invocation state used by the guard.

Violated requirement: R29 success clauses 1–2 and the schema's actual local Grant query/decision join. An observation snapshot alone cannot authenticate the historical active-owner guard.

Minimum closure: validate at the actual query while the owner is active and retain independently owned authenticated validation evidence, or retain the relevant immutable query-time invocation/guard state separately from the candidate and replay against that state. Preserve normal owner deactivation. The unchanged positive certificate must pass the same owner validator before any mutation can count, and negative mutations must fail for the altered premise rather than universal post-completion inactivity.

## Major 2 — dynamic Catch authentication is still internal duplicate equality

Locations: `machine.rs:127–150`, `2630–2641`, `2743–2749`, `4222–4230`, `4443–4451`; `machine.rs:2493–2506`, `2530–2534`.

The emitted handler ID is repaired: `handler_id` is captured from `installation.occurrence` and emitted at `machine.rs:4132`. The Catch source site remains separate. But `validate_dynamic_catch_consumer` accepts only one mutable candidate consumer plus an event. It compares `handler_id` to `installation_occurrence`, owner to owner, arm to arm, and trusts the candidate's `installation_authenticated` Boolean. All those fields are copied into the same candidate in the same constructor. There is no separate installed-handler table, immutable selected-installation record or independently supplied frame/arm authority in this validator. The real selected frame exists at query time and is then popped at `machine.rs:2763`; its independent installation is not retained for this validation. The frame projection contains source/owner strings, omits dynamic occurrence, and is not read here.

Concrete accepted forgery: clone a valid consumer; set both `handler_id` and `installation_occurrence` to an arbitrary equal nonexistent ordinal; keep the event/Boolean and paired fields equal. The validator returns true. Likewise, jointly replace `installation_owner`/`consumer_owner`, or `consumer_arm`/`selected_arm_source`. It does not even compare the candidate source site or resolved selected arm operation with the actual Catch. The current mutation changes only one duplicate, so it demonstrates inequality rejection, not authentication against installed state.

The production `validate_handler_installation` is a live frame guard (ordinal bound, current owner, activity), not a retained evidence authority for the later mutable certificate validator. Its earlier successful call cannot make arbitrary subsequent candidate fields authentic.

Violated requirement: R29 success clause 3; schema `catch_consumer.installation_authenticated` and selected dynamic handle/owner/arm joins against actual installed-handler state. The serializer symptom is repaired, but the authentication cause remains.

Minimum closure: retain a test-only independently owned selected-installation record at the actual frame/arm selection, including dynamic occurrence, source, owner, resolved operation and selected arm; validate candidate fields against that record, or validate against the real live frame before removal. Add changed-target mutations that remain internally consistent while naming a wrong installation/owner/arm, and require that owner validator to reject them.

## Major 3 — required bound mutation has no later observer in this fixed callback run

Locations: `machine.rs:4314–4323`, `1469–1476`, `3212–3227`, `4453–4467`; `receiving.rs:824–843`, `281–283`, `870–874`.

For the pinned callback source, the operation carrier's `OperationResultConsumer` appends the callback-result execution last, immediately before executing the request. `observe` traverses `executing_views` in order. The selected CallbackResult observation is therefore the last observation of the sole signal request. Its constructor sets `observer_bound = observer + 1`, and the machine's `next_observer` has that same value. The selected arm returns literal 1; the fixture contains no later operation. Running the companion uses another `Machine` and cannot increase this callback machine's observer counter. The harness adds no later callback-machine observation before the mutation.

Consequently, changing this bound to `observer + 2` cannot satisfy `observer_bound_is_currently_plausible(after)` at `machine.rs:4463`. That assertion is expected to fail by the source trace, even after Major 1 is repaired. No executed failure is claimed.

Distinguish the guards: `local_grant` actually checks `observation.observer < self.next_observer`, not the stored construction bound. The old evidence plausibility check is `bound <= next_observer`. The new exact equality with the independent request snapshot correctly protects the construction bound; the required mutation must additionally establish its claimed later-observer setup so that it specifically distinguishes equality from the former inequality check.

Violated requirement: R29 success clause 5 explicitly requires an altered construction bound with a later observer making the old inequality pass, and an applicable changed-target rejecting check. The source-design receipt asserts this setup but does not construct it.

Minimum closure: construct an authentic later test-only observation in the same owning Receiving state, without changing the pinned fixture/runtime decision; establish positive validation at the intended historical guard state, demonstrate the old inequality really passes, then change the exact existing row and show the independent comparison rejects it. Keep this evidence separate from another machine's observer counter.

## Repairs and scope observations

- R28's production-storage defect is repaired: `Observation.observer_bound` and its constructor initializer are both `cfg(test)` (`receiving.rs:131–132,839–840`). Request snapshots, route evidence and validators are test-only. R29 adds `Eq/PartialEq` derives to `ExecutionView`, but no new production storage or decision branch was found. The production local Grant refactoring in `machine.rs:2653–2661` preserves the previous short circuit and rejection condition.
- R28's observation self-comparison cause is substantially repaired: the exact `request.observations` vector is copied separately at `machine.rs:2721–2727`, and the selected candidate observer/bound/event/full `ExecutionView` are checked against that snapshot at `receiving.rs:628–671`. The execution table still comes from `Receiving.executions`. Major 1 concerns additional time-sensitive guard state, not absence of that observation copy.
- Typed callback-use/result/receipt ownership and the selected execution occurrence remain source-directed. Permission, inflow, observation and Grant stay distinct; no fixture edit or broad solver/HIR change appears in the R28-to-R29 source diff inspected here.
- The seven companion owner/frame/request mutation cases remain present, with actual-target assertions and rejection helpers. They do not authenticate the callback's missing historical liveness or dynamic installation authority.
- Callback result 1 and companion result 23 remain unchanged test assertions. This review establishes neither result by execution. Source bytes, direct dependency pins and both frozen target hashes were checked; no full-tree baseline verification or proof closure is claimed.
- No additional minor finding is raised. The three major findings each block source acceptance; no production semantic counterexample or original A/B refutation is claimed.

## Frozen identities

| Input | SHA-256 |
|---|---|
| Contract R1 | `8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f` |
| Schema R1 | `b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379` |
| `machine.rs` | `b50efa79045fbe00529cc72efbc0bff78552b2febecbcacc967a7c4d26bb3ed0` |
| `receiving.rs` | `1c650336b2cf5834c94be8fb75a4a09eadc4b5a838500eb57b0d39aa6ee69a48` |
| Source mutation design | `2397e7c5cc1b10cc418cca5b22dcff6588541805d728ce2a14d0e75783ef553b` |
| Rust handoff R1 | `509572eac5b45a720277efb9e119306a43ed7388f76d41306c80a1c2f6d5749c` |
| Direct dependency `program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| Direct dependency `continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| Companion source | `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7` |

Governing reads: root operating map/base, design authority, current state/README, R29 contract/schema/input manifest, effect policy, original preservation statement and birth-level correction; actual runtime owners, direct program/continuation dependencies and relevant callback/companion harness. Preserved R28 R2 independent findings were compared with the actual R28 archive-to-R29 diff. Only afterward were the mutation design and author handoff read as submissions.

## Resource and STOP receipt

Conservative precompile review charge: **600 / 1,400 seconds**, leaving **800 seconds** for the sprint-wide independent review envelope. Exact active seconds were not instrumented; source inspection and this report are included in that charge. No heavy process or descendant was started. Only reads, searches, archive/diff/hash inspection and this leased handoff write occurred. A failed `python` lookup was followed by a read-only `python3` archive/diff/hash script; it executed no compiler, checker or test.

STOP; writes closed. Compilation/execution gate remains rejected. Lean projection, authenticated runtime certificate, actual mutation receipts, original parent/source-native correspondence and production remain OPEN.
