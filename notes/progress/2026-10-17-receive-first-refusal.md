# Receive fixture first-refusal run receipt

Sprint `receive-negative-row-and-refusal-cut-20261017`, contract revision 4
SHA-256 `70bec2000d72d983936445528b9c1c95b7c3c949b95c3a676f0f63bd3a66051c`.
The single authorized primary run used frozen temporary instrumentation from
the implementation handoff SHA-256
`0302408c73177864032ca7b5346ce15a15fc49a5cc544161a8d864fc6655b373` and exact
fixture SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.

## Execution

Command:

```text
timeout 120s env CARGO_TARGET_DIR=/tmp/yulang-research-receive-first-refusal-20261017 cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit code: `2`; completed in 20.7 seconds, within the 120-second cap. This was
the single authorized run, not a test. The isolated target directory compiled
the example and solver sources successfully, then ran the frozen fixture.

## First refusal and observed path

The fixture remained 357 bytes; parsing reported no structural recoveries. HIR
reported the same three errors as the prior receipt, now with raw IDs and exact
attachments: `HirErrorId(0)` UnsupportedItem at DirectRootItem(0), range
`80..130`; `HirErrorId(1)` UnsupportedExpression at the `f0` value, range
`147..162`; and `HirErrorId(2)` UnsupportedExpression at the `receive` value,
range `328..356`. HIR identity and operation-use checks completed; receive's
LocalSource inventory showed eight expressions, including its formal
`f: Unit -> (Unit -> [ctrl] Int)`, the two separate applications `f ()` and
`g ()`, and the intervening local `g` use.

The ordinary `CandidateInference::solve` entrypoint was entered. The first
emitted temporary branch label was:

```text
candidate-refusal: candidate_source::preflight.lambda-formal-annotation
```

It immediately preceded the existing `CandidateError::Unsupported` return for
the lambda formal annotation guard. The harness then reported
`STOPPED at candidate-solve: Unsupported` and exit 2. No later refusal label
was emitted. This localizes the generic result to the already inspected
receiver-formal preflight condition, before placeholder retention, collection,
constraint generation, propagation, or export. It does not execute
`candidate_formal_pair`; that downstream native constructor remains a separate
source-level obstruction if preflight were changed.

The observation agrees with the source prediction for the negative concrete
row at the inner function's result port. It does not prove an accepted source
typing, a subtraction transition, successful inference, historical provenance,
phase-root `R_e`, complete choose semantics, or any production behavior. The
approved permission policy and the native candidate preflight result remain
distinct facts.

## Restoration and limits

Immediately after the run, Luna restored both exact pre-edit snapshots:

- `crates/yu-solver/src/shadow_apply.rs` equals
  `tasks/agent-loop/snapshots/20261017-receive-refusal-shadow-pre.rs`, SHA-256
  `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- `crates/yu-solver/src/candidate_source.rs` equals
  `tasks/agent-loop/snapshots/20261017-receive-refusal-candidate-source-pre.rs`,
  SHA-256 `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.

No retry, test, fixture edit, semantic change, preflight relaxation or export
occurred. Temporary instrumentation is removed. The one-run allowance is
exhausted.

CHOOSE-SOURCE-2 remains OPEN: the source-level proof locates the negative
permission and native refusal, but the source-owned paired negative interface
and transport/consumer through `f ()`, local `g`, then `g ()` are unproved.
F1/FK1/FIRST-RESULT-ADEQUACY/H1/H2/JOINT_DEC/F5, source-Generalize/public
export, principality and production retain their separate OPEN status.
