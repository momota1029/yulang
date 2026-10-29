# Sprint ANNOTATION-HYGIENE-TRANSITIONS/20261030-R24

Status: admitted by Luna under the continuing Yulang Rust/Lean goal
Selector: `/root/next_action_selector`, sprint-boundary proposal; Luna validated exact source pins and the default resource ceiling
Branch admission commit: `dd1e13cdaa97a124f26eda9a19da5fa769fc8cc0`
Isolated source base: `9a74a70a32ebda716a00c7203d8e606343cf442a`

## Parent, authority and fixed meaning

Preserve the original Simple-sub A/B claims, quantifiers, accepted source domain and production authority. The original parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`. Governing effect meaning is `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–4 and the approved level-SCC design. R23 is closed incomplete and remains failure evidence only.

For contravariant `[signal]`, annotation grants permission to subtract `signal` at that local boundary; it does not add `signal` to an empty inflow. The owning Catch handles an actual signal request. Removing handled `signal` preserves an independent `write` contribution. Symbolic variables and dependencies remain connected. Covariant annotation remains allowance, not evidence that an effect flows. No solver representation or language behavior changes in this sprint.

The selected source occurrences are distinct and must not share identity evidence:

1. The exact §1.1 callback program in the governing hygiene design: the annotated callback's `signal` request reaches its owning Catch, the local selected arm returns `1`, and the annotated permission is kept distinct from the actual contribution.
2. `tools/inference-playground/examples/original-suffix-outer-receiver.yu`: its inner Catch consumes its own `signal`; its separate `write` request survives to its outer `receive` consumer.

Expected source bytes, fixtures and outputs remain unchanged. No claim extends from these occurrences to every source program.

## One bounded outcome

Construct a source-derived transition table and a test-only observer/validator over owner-minted identities. Validate both unchanged programs when executable evidence is available. In parallel after the transition schema is frozen, construct and check a Lean branching invariant for the same constructor/consumer/lifetime distinctions. Apply a checked theorem only to authenticated records. A source table, synthetic trace, conditional theorem, compile check, or rejected run alone is not runtime execution or parent closure.

The Rust record must keep distinct, typed coordinates for source occurrence, declaration/binding, lambda/formal, Name view, body Apply, invocation, callback entry/use, formal receipt, request payload, Catch owner, exact arm, event and consumer. Each identity is minted at its owning source transition. No substring/debug-name lookup, caller-supplied invocation labels, graph-family inference or equal-result inference may authenticate a join.

The validator and rejection cases must cover:

- exact declaration/formal, schema and Name-view agreement;
- permission evidence separately from actual contribution evidence;
- invocation owner and entry/use identity, request payload, Catch owner, exact selected arm and result;
- required transition order and separate normal-return versus shallow-discard lifetime branches;
- the companion's inner signal consumption linked to the retained write obligation and outer receiver;
- rejection of swapped invocation, entry, use, Name view, formal receipt, payload, arm, Catch owner or event; missing records; schema mismatch; invalid order; premature retirement; and lost `write`.

At least one mutation validator must demonstrably reject each required family. A positive trace with absent permission/contribution or disconnected companion events must fail. Preserve the valid R23 owner-minted ordinal idea; do not reuse its rejected identity joins.

## Rust lane — implementer, requested Luna/high

Luna creates `isolated/ep-hygiene-r24/project` as a detached worktree at the isolated source base. Root `machine.rs` and `receiving.rs` are UNKNOWN_WRITER/quarantined and are never read as a base, copied, overlaid or edited. R23's rejected frozen revision may be read only as diagnostic evidence.

The Rust writer may edit only these exact paths:

- `isolated/ep-hygiene-r24/project/tools/inference-playground/src/runtime/machine.rs`
- `isolated/ep-hygiene-r24/project/tools/inference-playground/src/runtime/receiving.rs`
- `isolated/ep-hygiene-r24/project/tools/inference-playground/src/runtime/program.rs`
- `isolated/ep-hygiene-r24/project/receipts/hygiene.json`
- `isolated/ep-hygiene-r24/project/build-target`
- `tasks/agent-loop/inbox/effect-permission-hygiene-r24-rust.md`

Only behavior-neutral test instrumentation and the validator are allowed. Keep ordinary runtime semantics unchanged. First freeze the owner-derived transition schema/table with hashes and send Luna an intake receipt. After Luna authenticates that schema hash, the proof lane may use it; schema changes require a new sequential revision and invalidate dependent proof/review.

### Compile-only and execution gates

A fresh nonauthor `compiler_referee` reviews exact frozen source/validator hashes and the proposed compile-only argv. Its ACCEPT authorizes only:

`cargo check --tests --locked --offline -p yu-playground`

Use `CARGO_TARGET_DIR=build-target`, one CPU, at most 2 GiB process-tree RSS, at least 4 GiB available memory, and a 120-second cap. Capture argv, raw output/status, elapsed time, resource samples and source hashes. A compile-only ACCEPT or green check grants no test execution.

After all validator/rejection cases and both source routes are frozen, the same independent referee reviews those exact hashes, source/fixture immutability, joins, order, coverage, resource plan and proposed runtime argv. Only explicit fresh exact-hash ACCEPT authorizes `cargo test --locked --offline -p yu-playground`, up to two invocations with combined elapsed time at most 240 seconds, each at most 120 seconds, under the same CPU/RSS/memory caps. Any source correction invalidates ACCEPT and needs bounded re-review. Never run Cargo and Lean concurrently. No package, lockfile, fixture, source example, expected output or production code outside the listed test-only owner files may change.

## Lean lane — registered `lean_prover`

Start after Luna authenticates the frozen transition schema and obtains a fresh selector delta at that cross-lane boundary. The proof paths below are reserved by this contract but are not active leases at admission; Luna adds those exact paths to `current.json` before launching the proof author. Source construction and proof construction may proceed concurrently afterward on disjoint exact paths. The proof author may read the frozen R23/R22 artifacts as unchecked candidate material. Build an explicitly branching transition relation whose constructors correspond to source owners and distinguish annotation permission, actual inflow/contribution, Catch consumption, normal return, shallow discard, and retained companion write. Do not put the desired hygiene conclusion in a premise or identify types by debug text/family alone.

Write only:

- `isolated/ep-hygiene-r24/project/notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean`
- `isolated/ep-hygiene-r24/project/notes/theory/lean/.lake`
- `isolated/ep-hygiene-r24/lean-scratch`
- `tasks/agent-loop/inbox/effect-permission-hygiene-r24-proof.md`

Use pinned Lean 4.35.0 and the project checker; one CPU, at most 1 GiB RSS, at most two selected-module audits and 120 seconds combined. Serialize Lean with Cargo. Report exact theorem types and complete axiom lists. No `sorry`, `admit`, project axioms, or unsupported proof assumptions. State exactly which records and constructors the model represents and which omitted cases remain. A proof over abstract transitions is conditional until source correspondence is authenticated.

## Resources, sequencing and stop conditions

Total sprint cap: **6,400 seconds**, inside the standing 7,200-second default: Rust 2,400; Lean 1,800; independent review 1,600; Luna 600. Astra allocation: zero. Charge dispatch-to-stop wall upper bounds; UNKNOWN elapsed time consumes the full remaining assignment cap. No renewal or borrowing from R23's unusable 245-second Cargo/handoff reserve.

Keep active/reserved/unknown assignments within the six-assignment default and reserve two slots for review/integration. Use the already authenticated capacity override only as recorded; keep every UNKNOWN path quarantined. Exact leases above do not authorize other paths. Child processes are serial; at most one heavy Cargo/Lean process at once. Rust and Lean may overlap only after the shared schema is frozen and their writes are disjoint. Reviewers are read-only and never certify their own work.

Stop on a material semantic/identity counterexample, new dependency or path need, budget exhaustion, failed fresh-hash gate, unavailable pinned tools, or confirmed worker STOP. Freeze the exact first failure and preserve logs. Consult the selector at a material blocker, lease/resource/authority change, integration seam and sprint end. No unreviewed artifact is a parent theorem or production change.

## Required closeout

Either (A) fresh review accepts exact Rust instrumentation/validator, both unchanged source routes execute with authenticated records, and a pinned Lean theorem with complete type/axiom audit is applied to those records; or (B) record the exact first failed source transition and any independently reviewed, checked conditional invariant without claiming runtime evidence. In either case preserve the original A/B claims, source/native correspondence, effect hygiene, soundness, principality, termination and production gates as OPEN until their full obligations are met. Luna records exact hashes, authors, resource charges, residual premises, review, outcome and Git checkpoint, then pushes only the reviewed intended paths.
