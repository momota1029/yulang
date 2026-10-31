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

---

# R29 independent precompile source review — revision 2

**Verdict: REJECT for the exact R2 Rust/schema bytes below.** This is a delta review of the three R1 major findings and their direct repair dependencies. The semantic repairs address the three reported causes by source inspection, but the new query-time snapshot field introduces a definite test-target trait obligation failure. Per the packet's instruction to stop on an unresolved major, further review stopped there. No compilation, runtime, mutation, selected-main result, checker, Lean/Lake result or proof has been executed or established.

## Major R2-1 — retained invocation snapshot makes the test evidence Debug derive ill-typed

Exact locations in `W/tools/inference-playground/src/runtime/machine.rs`: `140` (`#[derive(Clone, Debug)]` on `RequestConsumerEvidence`), `166` (`request_invocations_snapshot: Vec<InvocationDescriptor>`), `303–307` (`InvocationDescriptor` derives only `Clone`). A source search found no `Debug` implementation for `InvocationDescriptor`.

Under `cfg(test)`, deriving `Debug` for `RequestConsumerEvidence` requires its `Vec<InvocationDescriptor>` field to implement `Debug`, which requires `InvocationDescriptor: Debug`. That implementation is absent. Thus the required library test target has an unsatisfied trait obligation before the positive certificate or mutations can execute. This conclusion follows from the concrete derive and field types; no compiler diagnostic is claimed.

Violated contract: R29's required compilable test-only certificate/mutation harness and source gate preceding the bounded library test compilation. This finding is directly introduced by the repair of historical query-state ownership, rather than an unrelated style preference.

Minimum closure: make the test evidence's Debug implementation valid—for example, supply a suitable Debug implementation for the descriptor, or remove/replace the containing derive if no consumer requires it. Freeze new source hashes and obtain fresh review before any separate execution-stage authorization. Do not spend Cargo time merely to confirm this known source obligation failure.

## Disposition of the R1 majors at source level

1. **Historical Grant/liveness cause repaired in source.** `machine.rs:2673–2678` clones the actual descriptor vector and indexed active-state projection immediately before the Grant call. Both are test-only and separately passed from the candidate to `validate_callback_route_evidence` (`receiving.rs:609–619`). Recomputed Grant uses the request-owned descriptor snapshot (`receiving.rs:645–651`), while the selected active bit and query owner are checked against independent arguments (`receiving.rs:733–742`). The harness represents unchanged positive validation and asserts both true query-time activity and false final activity (`machine.rs:4453–4463`). It does not reactivate the runtime owner. This ownership repair introduces Major R2-1 above, so no successful positive validation is established.
2. **Dynamic Catch ownership cause repaired in source.** A separate test-only machine vector `selected_catch_installations` owns records of the verified live selected frame (`machine.rs:74–75,127–137,2753–2762`). Candidate consumers retain an index, not ownership of that source record. The validator receives the separately retrieved source record and compares event, occurrence, Catch source-root/occurrence, owner, operation and both arm copies (`machine.rs:4276–4294`). Coordinated candidate occurrence, owner and arm substitutions cannot pass those fixed source comparisons; operation substitution is also checked. The constructor reads the actual selected frame after the existing live installation guard and resolved operation selection, before popping it. Source-site substitutions are directly compared even though there is no added source-site mutation case. No actual mutation rejection is established.
3. **Later-observer cause repaired in source.** `machine.rs:4596–4625` changes the candidate bound while leaving the independent request snapshot unchanged, then calls actual `Receiving::observe` on the authentic selected execution in the same `Receiving`. It asserts original bound `n+1`, later observer ordinal `n+1`, later bound `n+2`, and plausibility of mutated bound `n+2` under the former inequality. Observation does not add an execution-table row, so that construction does not invalidate the retained table comparison. Candidate-to-request bound equality remains required. The actual production local Grant guard still uses observer ordinal against `next_observer`; the stored construction bound remains additional test-only evidence. No mutation execution result is established.

The additions inspected are under `cfg(test)`: selected-installation storage/record, request descriptor/guard snapshots, snapshot capture, validator arguments and harness changes. Production owner deactivation, Observation storage/decisions and pinned source/result assertions remain unchanged in these repairs. The companion mutation path remains separate and present. No new minor finding is raised. This is source-level closure of the three former causes, conditional on resolving the new trait obligation; it is not source ACCEPT, final evidence review or theorem closure.

## Authenticated R2 intake

| Input | SHA-256 |
|---|---|
| Contract R1 | `8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f` |
| Authoritative schema R1 | `b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379` |
| R2 `machine.rs` | `391210906e4d6c8e103bfb7aef357f2447a6ee5904e82b411adc807e823f7278` |
| R2 `receiving.rs` | `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2` |
| R2 source mutation design | `75a408c3cd4f0a8b95a156fb5687cf577d9a927e0a9667c3dd704d154c18c5c2` |
| Rust handoff R2 | `149a2c10007e8ca50e86092a333abd14555cc0f0c22f7b2a3157c8e470e3bf44` |

All listed hashes were independently read from the actual files. The resume packet transcribed the schema hash incorrectly as containing `...78f8f2e9...`; Luna acknowledged the correction and directed review against the unchanged authoritative schema bytes above. Commit `dba519ce7` was named by Luna; no Git command ran in this review, so commit membership is not independently certified here. The R1 report above is preserved.

## R2 resource and STOP receipt

Review resumed at `2026-10-29 23:41:26 UTC`. Conservative R2 charge: **180 seconds**. Cumulative independent review charge: **780 / 1,400 seconds**, leaving **620 seconds**. Only reads, searches, hashes and this leased append occurred; no compiler, runtime, test, source checker, Lean/Lake, Git, heavy process or descendant. The source gate remains REJECTED. Even a later source ACCEPT would require Luna's separate stage receipt before execution. STOP; writes closed.

---

# R29 independent precompile source review — revision 3

**Verdict: ACCEPT for the exact frozen R3 Rust/schema pair below, at the source-only precompile gate.** R2's missing-Debug major is closed. No outstanding major or minor finding remains in this admitted delta review. This accepts source inspection, not compilation, actual mutation rejection, selected-main execution, a certificate, Lean correspondence or parent proof closure. **ACCEPT authorizes only Luna's separate execution-stage receipt; it does not itself authorize compilation or execution.**

## Closure and exact delta

`W/tools/inference-playground/src/runtime/machine.rs:139–141` now declares `RequestConsumerEvidence` with `#[cfg(test)] #[derive(Clone)]`. Removing its Debug derive removes the unsatisfied `InvocationDescriptor: Debug` obligation introduced by the descriptor snapshot field. No broader production trait implementation was added. `InvocationDescriptor` retains its existing Clone implementation, which suffices for the retained snapshot and candidate cloning.

The entire type's declaration, every explicit type reference, its machine storage/construction, validator/serializer arguments, and harness consumer aliases were inspected for whole-struct Debug requirements. No such consumer exists in the target source: assertions/formatting select fields; validator errors are strings or Booleans; candidate mutation copies use Clone. Machine has no Debug derive that would indirectly require the field to be Debug.

Exact byte-delta evidence: replacing the unique R3 byte sequence `#[cfg(test)]\n#[derive(Clone)]\nstruct RequestConsumerEvidence {` with the former `#[cfg(test)]\n#[derive(Clone, Debug)]\nstruct RequestConsumerEvidence {` in memory reconstructs SHA-256 `391210906e4d6c8e103bfb7aef357f2447a6ee5904e82b411adc807e823f7278`, exactly the authenticated R2 machine source. Thus the R2-to-R3 machine delta is only that derive removal. No reconstructed file was written. `receiving.rs` and the mutation design still match their R2 hashes. Commit `a1d53b374` was supplied by Luna; no Git operation was needed or run, so this byte comparison does not independently certify commit membership.

The three R1 semantic repairs reviewed in R2 are consequently unchanged: independent query-time invocation/guard snapshots preserve historical Grant validation despite normal final deactivation; a separately owned verified live Catch selection record authenticates candidate occurrence/source/owner/operation/arm; an authentic later observation in the same Receiving makes mutated bound n+2 pass the former inequality while exact equality against the unchanged request snapshot rejects it. The source harness represents unchanged positive baseline validation before its changed-target mutations. Actual pass/rejection results remain unexecuted and must be obtained at the separately authorized stage.

This one-line test-only trait removal changes no production layout, Grant/Catch decision, source fixture, dependency, lockfile, expected output or scope. Callback 1 and companion 23 remain the pinned assertions. The reviewed frozen contract/schema and prior archived R2 report were read before relying on the author's R3 addendum; the latter is not correctness or execution evidence.

## Authenticated identities

| Input | SHA-256 |
|---|---|
| Contract R1 | `8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f` |
| Schema R1 | `b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379` |
| R3 `machine.rs` | `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425` |
| Unchanged `receiving.rs` | `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2` |
| Unchanged mutation design | `75a408c3cd4f0a8b95a156fb5687cf577d9a927e0a9667c3dd704d154c18c5c2` |
| Rust handoff R3 | `a19b4728042e396b452ace2154e5bd0d8a3f7da55d72eb29b91eec381dd041e8` |

## Resource and STOP receipt

R3 review started at `2026-10-29 23:47:32 UTC`. Conservative R3 charge: **120 seconds**, below its 350-second ceiling. Cumulative independent review charge: **900 / 1,400 seconds**, leaving **500 seconds**. Only reads, searches, SHA/in-memory byte comparison and this leased append occurred. No Cargo, rustc, tests, runtime/compiler, checker, Lean/Lake, Git, heavy process or descendant ran. R1 and R2 text are preserved. No runtime/mutation result, compilation or proof has been established. STOP; writes closed.
