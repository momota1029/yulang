# Sprint candidate: original-name-two-capture-20261019-r57

Status: ACTIVE; primary-approved revision 1 before worker writes.
Branch / baseline: `research/simple-sub-intrusion` / `abef89fb8491c5709173ba55c76af7886897a5bd`.
Previous closeout: R56 commit `bb02202c4` (state receipt `abef89fb8`).
Primary: `/root`, session `current-conversation-2026-10-19-r57`.
Authority: original computation-forwarding preservation §§1,6–7; top-level inference principles §§1–5; local self-recursion decision; reviewed R55/R56 evidence. R50 remains NOT ADOPTED.

## Exact candidate input

Retain R56's concrete effect identity and surrounding declarations. Add only a second direct `forward x` use after the recursive call, and preserve final `z`:

```text
act io:
    our tick: int -> int

my outer (q:[io] int) = {
  my forward (t:[io] int) = t;
  my loop (x:[io] int) = {
    my a = forward x;
    my z = loop x;
    my b = forward x;
    z
  };
  loop q
}
```

The only question is whether, under successful ordinary constructor prefixes, the first `forward x` FreshUse and qualified recursive `z = loop x` construction preserve the original published `forward` closure until `b = forward x` performs a second authentic capture. If so, derive the distinct maps and restored mapped-bound admissions. Otherwise identify the first physical write, alias, reachability, admission or source obstruction. Recompute the changed source's event qualification and complete replay source sets; do not carry over R56's event sets or physical trace without rederiving them.

This source retains the unchanged §1 direct-current-formal/Name shape: all four Apply arguments (`x`, `x`, `x`, `q`) must be the whole current formal Name. It preserves the qualified recursive `loop ↔ z` reference cycle by returning `z`; returning `b` is outside this packet. Establish constructor-domain membership but do not assume complete typing, solver success, termination, invocation, runtime behavior or the target capture result.

## Fixed outcomes and evidence

One bounded outcome is required:

1. **Preservation and second capture:** establish source/action order, complete source-event sets, signed processing/parent records, each physical BoundKey owner and representative transition across the recursive construction, then show the second `Action::Local` capture is of the same published `forward` provider. Derive its distinct FreshUse identity/map and restore the relevant mapped bounds before return.
2. **Authentic interference:** exhibit the first actual constructor-derived write/alias from the recursive path into the original provider closure, with physical keys, complete source set, signed parent and resulting second capture correspondence.
3. **Exact obstruction:** locate the first source-domain, reachability, admission or constructor-prefix condition that prevents the proposed witness, and state what this does and does not establish.

The finite result is conditional on successful ordinary source actions, scalar drains and restorations. It is not observed solver success and does not close universal mapped admission or parent preservation. No narrowing of source domain or quantifiers, no parent counterexample claim from a conditional graph, and no production promotion. Preserve expected-output protection and Simple-sub A/B. R50 supplies no premise.

## Method and boundaries

Trace source identities and binding schedule, including collection-time effects and action execution; distinguish the original provider rows from first-use and second-use rows. Recompute all Apply events and SCC qualification. Follow `a`'s capture, recursive Link/Apply admission, ordered signed structural and pending-bound traversal, full relation source sets, retained parents, qualified settlement, replay, `b`'s actual capture/FreshUse map, and restoration. Separate immutable source associations and evidence metadata from physical BoundKeys and mutable row representatives.

This packet authorizes static source inspection only. No parser/preflight/solve invocation, tests, builds, runtime, probes, instrumentation, code/semantic changes, expected-output edits, measurement, scratch output or production change. Stop at a bounded result, exact first obstruction, changed dependency/authority, STOP, session end or budget bound; do not resume general induction automatically.

## Lanes, leases and review

- Sol/high constructive source/domain, write-footprint/noninterference and second-capture derivation, at most 900 seconds. Exact leases: `notes/theory/2026-10-19-r57-original-name-two-capture.md`; `tasks/agent-loop/inbox/20261019-r57-proof.md`.
- Luna/high independent read-only source/event, physical-owner, replay and actual second-capture trace, at most 600 seconds. Exact leases: `notes/progress/2026-10-19-r57-original-name-owner-trace.md`; `tasks/agent-loop/inbox/20261019-r57-implementation.md`.
- After both writers stop, fresh independent compiler referee and spec auditor review all frozen outputs and pins, 300 seconds each, message-only.
- Luna integration, exact R57 outputs, contract, state and necessary task/progress synchronization only, 300 seconds.

Aggregate cap: 2400 seconds (Sol 900, Luna source-owner 600, compiler/spec reviews 300 each, integration 300). No Astra, no carryover, no descendants. Unknown writers retain leases. Luna alone grants exact leases, accepts reviews, updates central state and performs explicit-path Git integration.

## Exact dependency SHA-256 manifest

All files below are immutable inputs to revision 1. Any mismatch pauses dependent work until Luna revises authority and repins. The 23-file R56 source manifest is revalidated against the new baseline; R56's four frozen outputs and the committed closeout state are added as direct dependencies.

```text
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
b688f6677a4f6572d7e947ccd5b26883620b951f63585706c7ba866aae6d80ad  notes/progress/2026-10-19-r55-closeout.md
d1aa7f1a1af5da50a78e012540e9c0f01878a3ec13bb43d2565f75ae279895a4  notes/progress/2026-10-19-r55-original-name-owners.md
e9442fa05666018bb7bb2eefede2f6ef7867c6355a1e793bbb08ea825587a6d2  notes/progress/2026-10-19-r56-original-name-owner-trace.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
0ebbc5e0e0b1c85b3f89e9017d9759fc3c8cfec80aced22457ed2fdc5867b258  notes/theory/2026-10-19-r55-original-name-attack.md
db5e8115e3f853e7831ffaf525e4c794bdca9892a18d7fb153f395451f94a40b  notes/theory/2026-10-19-r55-original-name-core.md
ee5edcaaa64b32323cd60b1a960aecd7f8cf239e17103a7f0e2bcc14cf8691fd  notes/theory/2026-10-19-r56-original-name-source-trace.md
fcf17066b8a4a3198b4e5a7aabc492b6da5bf571a4bb042d5e40d5eb6f0602a2  tasks/agent-loop/inbox/20261019-r55-attack.md
0e9f5274a4d5eb556ef7e37bd98444a8270213c1e8b7570726fa32c59c5acbdd  tasks/agent-loop/inbox/20261019-r55-core.md
2bd40ed7f8ea15fa9d06fae39c2064b06bade04887c007414dd0f0cdc43e3d65  tasks/agent-loop/inbox/20261019-r55-implementation.md
dac34a1377881f2519ff3486d1d3ce88114cac73d5477837da70ef77a4d747b1  tasks/agent-loop/inbox/20261019-r56-implementation.md
0fcdb5b9046e4beb9538bce4f423678170a02af56bf98d302f9d0708aead63f3  tasks/agent-loop/inbox/20261019-r56-proof.md
4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1  tasks/agent-loop/sprints/original-name-core-20261019-r55.md
052492309a379f3eef24078b9090f8e7081dceaf2e4c7af37ff90c75ffa013cd  tasks/agent-loop/sprints/original-name-source-trace-20261019-r56.md
59af7c1fd429f7c71d5a9c5bb3c6660519b18164329650cd32caaef784b6c1e6  tools/inference-playground/README.md
```

## Approval gate

Before activation, verify the clean branch baseline `abef89fb8491c5709173ba55c76af7886897a5bd`, exact source and outcome, every dependency hash, closed R56 state, live worker identities and leases, and remaining resources. Luna must then explicitly approve this exact revision before either worker writes. Requested settings Sol/high and Luna/high; observed settings remain UNKNOWN absent live receipts.

Primary approval: `/root` approved revision 1 in session `current-conversation-2026-10-19-r57` after confirming the clean branch baseline `abef89fb8491c5709173ba55c76af7886897a5bd`, the exact candidate and outputs, all 28 dependency hashes MATCH, R56 CLOSED with both reviewers STOPPED/CLEAN, and no active or unknown writers. Approval authorizes only the two source-inspection lanes and exact output leases above; it does not authorize solver execution, code changes, tests or production work. Approval is recorded before worker writes.
