# R147 candidate — reviewed decision packet for unchanged countdown sample

Status: **CANDIDATE; no worker or code change is authorized.** This is Luna's
chosen higher-leverage successor direction after R146: prepare a source-correct,
independently reviewed Yulang2 braced-`if` compatibility decision that can
directly unblock the unchanged Web `countdown` sample. The user goal remains
proof-backed inference/evaluator implementation and broad execution of unchanged
Yulang2 Web samples. R147 does not narrow that goal or close any parent gate.

## Fixed outcome and authority

Prepare a reviewed user-decision packet that accurately partitions Yulang2
brace-group dispatch and shows the exact Yulang3 parser/HIR/inference/runtime
owners needed for the unchanged 388-byte
`web/playground/examples/yulang2-ordinary-islands.yu` sample to produce
`countdown_result -> 8`. Present precise choices for narrow countdown
compatibility and shape-compatible braced-arm compatibility. Do not select a
new language meaning on the user's behalf. User approval remains required
before any Yulang3 syntax/HIR or semantic implementation.

Preserve all colon-form behavior and test expectations, all original Simple-sub
and evaluator A/B claims and quantifiers, and R64/R65, source/native and
production gates as OPEN. R146's process-conformance status remains UNVERIFIED;
R147 grants no observation, build, test, CLI, WASM or runtime authority. No
semantic implementation or expected-output change is authorized.

## Required evidence and exact deliverables

- Contract: `tasks/agent-loop/sprints/braced-if-approval-packet-20261020-r147-rev1.md`.
- Revised decision draft: `notes/design/2026-10-20-braced-if-compatibility-r147.md`.
- Revised conditional representation/source note: `notes/theory/2026-10-20-braced-if-elaboration-r147.md`.
- Luna handoff: `tasks/agent-loop/inbox/20261020-r147-decision-packet.md`.
- Luna closeout: `notes/progress/2026-10-20-r147-closeout.md`.

The source account must distinguish predicate routing from parser reachability,
successful record construction, record-spread effects, block sequencing and
omitted non-record mixed-spread items. It must include the actual Y2
`expr/chain.rs`, `expr_syntax.rs`, and `record_lit.rs` dispatch, exact Y3 bare
`else { ... }` recovery/construction, and each current parser/CST, HIR,
candidate constraint, runtime consumer and Web/WASM gate. The corrected
decision must state how each relevant shape is handled or explicitly left for
the user; no blanket rule may silently drop an item.

The source note's singleton argument remains conditional on explicit source
construction and downstream invariance premises. It cannot claim parser
completeness, source/native correspondence, inference soundness, or discharge
the original A/B claims. The handoff records exact unresolved source/consumer
premises and the falsifier for each proposed option.

## Lanes, ownership and review

Luna owns the decision draft, contract, current state, handoff intake, closeout
and all Git. A single proof worker may own only the revised source note and its
one handoff, inspecting the exact Y2/Y3 source below. There is no code-writing
implementation lane because syntax/semantic authority awaits the user's
decision; Luna records `NO_SAFE_CODE_SLICE` for this packet and identifies the
first implementation milestone after approval. No overlapping writers.

Before activation, obtain CLEAN prospective spec/authority and compiler/source
reviews for this exact contract and every dependency pin. After the proof and
draft freeze, obtain a fresh independent compiler/source review of all three
decision artifacts and verify their exact hashes. A major finding returns to
Luna for a sequential new revision and review; it does not authorize code.
Only after a clean reviewed packet may Luna ask the user to choose or approve a
specific semantic option. A separate reviewed implementation contract is
required after approval.

## Baseline and direct dependency pins

Baseline branch: `research/simple-sub-intrusion`, commit
`4d9c9c74e0c56b8e34b60d521b68bcf8504946b2`, complete tree
`e2baa5de4a9796b56fa1a2c85e581346bd54886f`. Luna rechecks baseline/live pins
before activation. Repository code and the unchanged fixture must match the
baseline. Source tree is read-only.

```text
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
2b929dcdd31587c1ed5f0b0569cfc41e2f2bc29bf04a5f21be06bf24620718f3  syntax-reference/en/src/expressions/if-expression.md
08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed  notes/design/2026-08-20-yu-syntax-chasa-architecture.md
509af68c34e11a2a2d5538df8bab84c599d68154a3f03d57c304bbfb04d8cd39  crates/yu-syntax/src/expression/if_expr.rs
d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442  crates/yu-hir/src/module/local_source.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d  tools/inference-playground/src/runtime/program.rs
4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd  tools/inference-playground/src/runtime/machine.rs
f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487  web/playground/examples/yulang2-ordinary-islands.yu
0102f9e8c6ded9c03c51a71356a1532a9db8742de181d649f642ad9d325f4e5b  ../yulang2-oracle-capture/crates/parser/src/expr/control.rs
bb58bd49ec272003e69d4675c2d6ee1de470e3c1ebaed0f632b6f117629acf38  ../yulang2-oracle-capture/crates/parser/src/expr/group.rs
4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963  ../yulang2-oracle-capture/crates/infer/src/lowering/control.rs
661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898  ../yulang2-oracle-capture/crates/infer/src/lowering/expr/block_local.rs
e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6  ../yulang2-oracle-capture/crates/infer/src/lowering/expr/chain.rs
3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085  ../yulang2-oracle-capture/crates/infer/src/lowering/expr_syntax.rs
88ce8e06f83884fd825402565c52ab1f19e8b9932500036eae495d392a5c990c  ../yulang2-oracle-capture/crates/infer/src/lowering/record_lit.rs
```

The exact R135 review result is a source-evidence lead, not authority: final
compiler review previously found that the submitted proposal understated the
shape-sensitive Y2 route and misstated the Y3 bare-else brace path. R147 must
independently verify those locators against the pins above. R146 closeout remains
`notes/progress/2026-10-20-r146-closeout.md` and all its limitations remain.

## Resources and stop conditions

Proposed cap: **1,200 active seconds, Astra 0, no carryover**: contract/pin
preparation 180; prospective reviews 180; proof/source note 420; Luna decision
draft 180; final review 120; closeout 120. No compiler or runtime process is
authorized. The existing three UNKNOWN legacy assignments, board quarantine,
R104 HELD lease, and R146/R145 frozen artifacts remain untouched. Stop on pin
drift, missing Y2 source, any need for an unpinned owner, or semantic ambiguity
that cannot be expressed as a user choice. No successor or implementation
authority follows from this candidate.
