# R41 independent review

## Revision 1 — BLOCKING

Reviewer: `/root/r41_independent_review` (`spec_auditor`), launched after the Rust and Lean writers completed. The reviewer remained read-only; Luna persisted this receipt. Scope and limits follow `tasks/agent-loop/sprints/effect-permission-lambda-incidence-20261031-r41.md`.

### Blocking findings

1. **Graph node index was replaced by the child ordinal.** In `candidate_scheme.rs`, capture reads `children[1]` into `argument_effect_child` (then around line 2861), but stores literal `1` (then around line 2876). FreshUse compares this value with `children[1]` and uses it to index `graph.nodes` (then around lines 4434–4437). The Function child ordinal is not the graph node index. When the actual child node is not node 1, FreshUse returns `ReceiptMismatch`; a coincidental node-1 case hides the defect. This fails the exact incidence preservation required by R41 and the Rust realization of Lean's `capture_preserves` projection.

   Closure: keep the child ordinal and actual graph node index as distinct coordinates, retain the actual node obtained from `children[1]`, then independently inspect a non-node-1 child and its exact row/FreshUse image.

2. **Invalid `let-else` initializer syntax.** The unparenthesized `match` initializer at `candidate_scheme.rs` (then around lines 2865–2868) ends in `}` immediately before `else`, which is excluded by Rust's `let-else` initializer grammar. This was a static syntax finding; no compiler was run.

   Closure: express the extraction using valid Rust syntax and refresh the reviewed source hash.

Both are implementation defects within the admitted source owner; no new semantic decision is needed.

### Independent bounded findings

- Registration is created in the owner-local Lambda scan in `candidate_source.rs:1104–1115`; the same index enters `LambdaRecipe` at `:2099–2104`. `admit_lambda_fact` uses that computation registration and records the exact positive Function after construction. Computation formals omitting slot 3 remain included.
- Capture selects the positive Function endpoint and structurally selects child 1. `canonical_value` leaves structural Function endpoints unchanged. Missing Function endpoints are skipped, so no universal reachability or capture-completeness claim follows.
- Capture checks the child's effect-row representative. FreshUse uses its ordered row map and preserves exact route definition-use identity/context stamp. The node/ordinal defect prevents the full bridge from passing.
- New vectors use fallible reservations. Checkpoint/truncation, graph bytes, FreshUse scratch bytes and retained-map bytes include the metadata. `HirOccurrenceId` clones share an `Arc`; no whole-call rollback or allocation-timing guarantee follows.
- Distinct registration records stay separate under shared row images. The `{signal | e}` / `{write | e}` witness is conditional on a hypothetical consumer and arriving contribution; it establishes no actual provider arrival or compiler defect.
- Existing `f5d_identity_lambda_admits_exact_effect_and_function_facts`, R226 and R227 contracts were inspected, not run or changed. No expectation, snapshot, fixture, diagnostic or semantic test-name change is authorized.

### Independent Lean audit

The reviewer elaborated complete R39 plus R41 source (only the R41 project import removed), then ran `#check @` and `#print axioms` for all nine R41 theorems using the contract's pinned read-only stdin command. Exit 0, empty stderr, 1.337 seconds. Input SHA-256: `d369d0383e59c809e5b8c353d62b72bad01280c3baf0a7e96c3d8f16f7f9cb67`.

| Declarations | Complete axioms |
|---|---|
| `function_child_one`, `lambda_origin`, `capture_preserves`, `freshuse_exact`, `conditional_shared_tail_falsifier` | `propext` |
| `distinct_registration_images`, `shared_row_distinct_labels` | none |
| `entry_to_exact_use`, `empty_entry_incidence` | `propext`, `Quot.sound` |

The theorem types retain R39 validation hypotheses and arbitrary shared maps. No `sorryAx`, project axiom, or checker bypass was found. The finite constructors do not prove Rust realization; `R41-NATIVE-INCIDENCE-REALIZATION-1` remained open and was concretely blocked by finding 1.

### Dirty-base isolation and reviewed identities

Reversing only R41 scheme additions in memory reproduced the pinned dirty baseline exactly: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.

| Artifact | SHA-256 |
|---|---|
| `lib.rs` | `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce` |
| `candidate_context.rs` | `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38` |
| `candidate_scheme.rs` | `73f13e56057efa11d5c9b8f1eff66687b83920257e2c41ba1dcce2ecb3ce3785` |
| R41 Lean module | `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e` |
| Rust handoff r1 | `3b0bb74bd8800dfe8bc035c3b79029657d8b013cb6589872dea9ddf13427fc10` |
| Proof handoff r1 | `1f33b18d0e60d3f244ccf2843cd7a1e0acd6ef6e1bd3a24727fdcb88a12fac84` |

Provider arrival, Catch subtraction/residual, full source/native correspondence, original A/B, whole-language hygiene and production promotion remain OPEN. The reviewer STOPPED. No writes, builds, tests, Cargo/Lake, Git mutations, scratch, cache, worktree, environment or descendants were used.

## Revision 2 — pending re-review

Luna corrected the child ordinal/node-index conflation by storing `argument_effect_child_index` separately from `argument_effect_child_node`, using the actual node selected by `children[1]` throughout capture/FreshUse, and parenthesized the match initializer. Corrected `candidate_scheme.rs` SHA-256: `3cd9dd2d0f55412636dc88bc658d7cfbc23aad6304b90f2ba95247f8d58e1d22`.

The Rust handoff records this correction as revision 2. Independent inspection of the corrected source, including a non-node-1 child coordinate and exact row/FreshUse image, is pending. This review receipt must not be treated as PASS until that re-review completes.

## Revision 2 — bounded PASS

Reviewer `/root/r41_independent_review` rechecked the corrected source and stopped. Both revision-1 blockers are closed; no remaining BLOCKING, major or minor finding was established in the admitted delta.

- **Coordinate correction:** `candidate_scheme.rs:2878–2880` stores child ordinal `argument_effect_child_index: 1` separately from actual graph node `argument_effect_child_node: argument_effect_child`. FreshUse at `:4438–4459` checks the ordinal selects that node, obtains its row, verifies the graph-row coordinate and maps it through the same ordered `rows` vector. Static non-node-1 trace: `children[1] = 7`, `graph.nodes[7] = Node::Row { row: 5, ... }` yields `(child_index=1, child_node=7, graph_row=5)` and FreshUse retains `rows[5]`; the existing term reconstruction uses `terms[7]` for that node. This is a static trace, not an executed test.
- **Syntax correction:** the `match` initializer at `candidate_scheme.rs:2867–2870` is parenthesized before `else`. No compiler execution was performed.
- **Dirty baseline:** reviewer again removed only R41 incidence declarations, vectors, accounting, capture and FreshUse additions in memory, restored the old initializer, and exactly reproduced dirty baseline SHA-256 `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.

Frozen revision-2 identities:

| Artifact | SHA-256 |
|---|---|
| `candidate_scheme.rs` | `3cd9dd2d0f55412636dc88bc658d7cfbc23aad6304b90f2ba95247f8d58e1d22` |
| `lib.rs` | `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce` |
| `candidate_context.rs` | `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38` |
| R41 Lean module | `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e` |
| Rust handoff revision 2 | `14ebc319c075406ccb00c09ffde97554d58877fe4c64e583575a273ec2cd750a` |
| Proof handoff | `1f33b18d0e60d3f244ccf2843cd7a1e0acd6ef6e1bd3a24727fdcb88a12fac84` |

The independent Lean audit from revision 1 remains applicable: all nine theorem types were checked, exit 0 and empty stderr. Axiom sets under `YulangClosure.LambdaArgumentEffectIncidenceR41` are `propext` for `function_child_one`, `lambda_origin`, `capture_preserves`, `freshuse_exact`, `conditional_shared_tail_falsifier`; none for `distinct_registration_images`, `shared_row_distinct_labels`; and `propext`, `Quot.sound` for `entry_to_exact_use`, `empty_entry_incidence`.

This PASS covers only bounded static construction and finite-model correspondence inspection. Mechanically established Rust/native realization remains an explicit premise. Missing exact Function endpoints are skipped; universal capture availability is unproved. Shared-tail witness stays conditional. Provider arrival, Catch/residual subtraction, original A/B, whole-language hygiene and production promotion remain OPEN.

STOP receipt: read-only review; no writes, builds, tests, Cargo/Lake, Git mutations, scratch, caches, environments, worktrees or descendants.

Post-review handoff disposition: after the reviewer stopped, Luna changed only
the Rust handoff's status sentence to record this PASS. The reviewer inspected
the same technical revision and prior handoff SHA-256
`14ebc319c075406ccb00c09ffde97554d58877fe4c64e583575a273ec2cd750a`.
Current Rust handoff SHA-256 is
`484fdb19c8850c4a64af5a2bea2d80453722f1f9969a318ab69ef70e182c9829`; no
source or technical claim changed after review.
