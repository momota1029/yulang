# Sprint original-name-source-trace-20261019-r56 — trace the first original-domain exposure

Status: CANDIDATE until all 23 dependency pins match and Luna records primary approval before worker writes. Revision 1.
Branch / baseline: `research/simple-sub-intrusion` / `90f40f4b1cdb2654536d1f78c32feea3980f2b2c`.
Primary: `/root`, session `current-conversation-2026-10-19-r56`.
Authority: original computation-forwarding preservation §§1, 6–7; inference principles §§1–5; local self-recursion decision; reviewed R55 packet and closeout. R50 remains NOT ADOPTED.

## Original outcome and success evidence

Supply the concrete original-domain source-owner input requested at the R55 stop. Freeze and trace this exact source construction, with one in-source concrete `io` act identity:

```text
act io:
    our tick: int -> int

my outer (q:[io] int) = {
  my forward (t:[io] int) = t;
  my loop (x:[io] int) = {
    my a = forward x;
    my z = loop x;
    z
  };
  loop q
}
```

The claim under examination is only whether this source belongs to the unchanged parent’s direct-current-formal/Name fragment and whether its actual owner path supplies an original-provider exposure/alias before a later capture. Do not infer that a displayed source shape proves successful complete solving, an actual invocation, runtime receipt, or parent counterexample.

Success is one of:

1. an owner-derived original-domain alias/exposure with real source occurrence, complete source set, signed parent and physical `BoundKey` provenance, followed to its actual next capture and honest partial endpoint correspondence;
2. an owner-derived exclusion or exact source/reachability obstruction showing this candidate does not instantiate the required transition; or
3. a precise first owner where static constructors do not determine the needed actual history, with the exact next evidence needed.

A source SCC, a symbolic graph, a provenance association mistaken for a physical row alias, or a partial FreshUse memo treated as total `mu` is not success. Preserve the original §1 source domain and all §6 quantifiers. Parent remains OPEN 0→0 absent separately approved proof/refutation. No semantic narrowing, R50 adoption or production promotion.

## Fixed method and case obligations

Trace source binders and the concrete `io` declaration; confirm the parent fragment’s explicit Computation roles and whole current-formal Name arguments; distinguish the `forward x` Local/FreshUse route from recursive `loop x` active-initializer Link and later uses. Derive the candidate reference graph’s actual owners/events and qualification for every Apply in the source. Follow the relevant existing owner path: source schedule → candidate Apply/native Function demand → signed structural and pending-bound traversal → complete source sets / retained parents → qualified settlement and replay → next actual Capture/FreshUse restoration. At each step preserve immutable source references separately from mutable canonical row representatives and physical bound owners.

If any step requires actual solver/execution state that static code ownership cannot determine, stop at that exact missing owner and state what evidence distinguishes the alternatives. This packet authorizes source inspection only: no parser/preflight/solve invocation, tests, builds, runtime, probes, instrumentation, code or semantic edits, expected-output changes, measurement or production change. No source-domain exclusion is licensed by this packet.

## Two continuing lanes

- Sol/high constructive source/domain and physical-owner trace, at most 900 seconds, three stages: freeze exact source/domain; derive event/owner trace; apply only the bounded result to R55’s exact open premise. Leases: `notes/theory/2026-10-19-r56-original-name-source-trace.md`; `tasks/agent-loop/inbox/20261019-r56-proof.md`.
- Luna/high independent read-only source-owner verification, at most 600 seconds. Check binder/annotation/Apply action order, qualification, signed source sets, row aliases, replay and actual capture correspondence; report one concrete prerequisite or `NO_SAFE_CODE_SLICE`. No authored proof certification, parser/solver execution, code or tests. Leases: `notes/progress/2026-10-19-r56-original-name-owner-trace.md`; `tasks/agent-loop/inbox/20261019-r56-implementation.md`.
- After both authors stop, fresh independent compiler referee and spec auditor, 300 seconds each, message-only. Each verifies all frozen targets and 23 pins; neither may be an R56 author.
- Luna integration 300 seconds, exact R56 outputs, contract, state and required task/progress sync only.

Aggregate cap: 2400 seconds: Sol 900; Luna read-only owner trace 600; compiler/spec review 300 each; integration 300. No Astra assignment. No carryover.

## Exact dependency SHA-256 manifest

All listed dependencies are immutable inputs to revision 1. Any mismatch pauses dependent work until Luna revises authority and repins.

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
59af7c1fd429f7c71d5a9c5bb3c6660519b18164329650cd32caaef784b6c1e6  tools/inference-playground/README.md
4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1  tasks/agent-loop/sprints/original-name-core-20261019-r55.md
db5e8115e3f853e7831ffaf525e4c794bdca9892a18d7fb153f395451f94a40b  notes/theory/2026-10-19-r55-original-name-core.md
0e9f5274a4d5eb556ef7e37bd98444a8270213c1e8b7570726fa32c59c5acbdd  tasks/agent-loop/inbox/20261019-r55-core.md
0ebbc5e0e0b1c85b3f89e9017d9759fc3c8cfec80aced22457ed2fdc5867b258  notes/theory/2026-10-19-r55-original-name-attack.md
fcf17066b8a4a3198b4e5a7aabc492b6da5bf571a4bb042d5e40d5eb6f0602a2  tasks/agent-loop/inbox/20261019-r55-attack.md
d1aa7f1a1af5da50a78e012540e9c0f01878a3ec13bb43d2565f75ae279895a4  notes/progress/2026-10-19-r55-original-name-owners.md
2bd40ed7f8ea15fa9d06fae39c2064b06bade04887c007414dd0f0cdc43e3d65  tasks/agent-loop/inbox/20261019-r55-implementation.md
b688f6677a4f6572d7e947ccd5b26883620b951f63585706c7ba866aae6d80ad  notes/progress/2026-10-19-r55-closeout.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
```

## Permissions, stop rules and handoff

Baseline and all pins are rechecked before activation. Each assignment owns only its exact artifact and handoff paths above. Unknown workers retain leases and reservations. Children do not spawn descendants. No tests or execution are requested. A worker stops at a distinct source-owner outcome, exact missing owner, dependency/authority change, STOP, session end or finite cap.

Authors must freeze byte hashes and stop all writes before review. Reviewers return CLEAN or exact findings and independently verify the contract, four R56 output hashes and 23 dependency pins. Any blocking/major finding must be closed in a sequential revision before acceptance. Luna alone owns the central state, adjudication, explicit-path staging, commit and push. Commit/push only a coherent reviewed R56 checkpoint, then inspect the entire outbound range.

R55 established an authentic source seed and this candidate recursive source shape, but no source-qualified alias, exact missing `BoundKey`, universal mapped-admission proof or counterexample. R56 reuses R55 only for those exact reviewed facts. R56’s bounded trace is applied immediately to R55’s OPEN premise; it does not restart the general proof induction.

Primary approval: `/root` approved revision 1 after all 23 dependency hashes matched and before worker writes, in session `current-conversation-2026-10-19-r56`. Requested Sol/high and Luna/high; actual worker/model settings remain UNKNOWN absent live receipts.
