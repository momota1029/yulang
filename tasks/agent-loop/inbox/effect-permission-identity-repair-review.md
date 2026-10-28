# Independent review — EFFECT-PERMISSION-IDENTITY-REPAIR-20261028/r1

Reviewer: `/root/identity_repair_final_review` (`compiler_referee`), fresh and
non-author. Review was read-only; no Git, build, test, Lean, write, or descendant
actions occurred. Exact contract SHA-256:
`2008579471df100926ca41be4cd6fac780a7c2cc53ae5f5b1555bdec50c19c39`.

Disposition: **INCOMPLETE**. Do not accept the same-witness Rust bridge as
established. Both Rust `Graph` initializer repairs address the build blocker;
the conditional Lean extension is supported by the inspected receipts. Parent,
native, effect-hygiene, principality, termination, and production gates remain
OPEN.

## Findings

### BLOCKING — owner identity lookup prevents required observations

`candidate_effect.rs:2972–2975`, `:2979–2985`, `:3069–3073`, and `:3088–3094`
format `owner` as a bare `DefinitionRootId`. Producers at
`candidate_effect.rs:1582–1583`, `:1787–1788`, and
`candidate_scheme.rs:2993–2994` format `SourceRootId::Definition(owner)`.
`yu-hir/src/module.rs:1300–1304` and
`yu-hir/src/module/source_annotation.rs:125–126` confirm the derived wrapper.
The searches cannot match the emitted owner representation. The two Cargo tests
failed at `candidate_effect.rs:2975` and `:3073` before reaching decisive
identity assertions. Fixing the representation and retaining full trace
diagnostics requires a newly authorized packet and a new passing run; r1 has no
Cargo retry left.

### Major — assertions can miss an occurrence/path falsifier

`candidate_effect.rs:2983–3003` chooses one origin and accepts an export event
with the same row, witness, capture, and owner while ignoring the export's
`source_row` and `path`. It only checks that both events contain `node=`, without
comparing node indices or endpoint polarity; `:3009–3011` also checks graph
membership. Swapping two unequal exported ports while retaining their metadata
can pass after the owner lookup is repaired, even when the witness reaches the
wrong path. The second origin is never joined. Closure requires joining every
permission to its original metadata and full path, the canonical polarized
endpoint, equal intern/export node index, and actual returned port.

### Major — canonical transport and delegated allocations remain absent

`candidate_scheme.rs:1716–1720` canonicalizes before looking up a witness
keyed only by allocated numeric row (`candidate_effect.rs:175–187`). Assertions
at `candidate_effect.rs:2991–3000` and `:3096–3100` require the canonical row
number to equal the original allocation. When allocation `r` canonicalizes to
representative `q`, the trace loses `r`'s witness or gets `q`'s unrelated
witness; it records no `r → q` transport. Sibling tests exercise changed
representatives at `candidate_effect.rs:4319` and `:4353`.

Delegation events at `candidate_effect.rs:2329–2331` identify the symbolic
tail, while fresh delegated signature ports at `:2383–2392` receive no
allocation witnesses. The symbolic test does not establish those ordered
allocations. `:2976` checks only that `parameter_row=` exists, not the required
offset equation. Closure requires original and canonical coordinates plus
their transport, distinct witnesses for both delegated ports and the tail, and
the actual parameter-row mapping.

## Evidence and limits

- Both exhaustive test `Graph` literals initialize
  `formal_capture_trace_id: None` at `shadow_apply.rs:4981` and `:5094`.
- Raw feature-correct Cargo invocation compiled, then reported 0 passed / 2
  failed, exit 101, 65.83 seconds, 1,659,572 KiB RSS. It supports compilation
  and only operations preceding the failed assertions.
- All 11 final Lean extension theorem/type/axiom audit blocks match
  `check-2.log`; all 12 reused SourceOrigin audit blocks match prior `check-1.log`.
  Theorems are conditional on explicit event-history premises and do not assume
  `Origin` or `Construction` conclusions. Their checked catalog result does
  not establish a successful native execution decoder.
- Still open: native execution-to-event decoding, allocation freshness and
  state correspondence, actual view/bound insertion, row/bound/evidence/context
  discovery, canonical transport, capture completion, exact native export,
  original source, parent preservation, and all production gates.

## Frozen artifacts

```text
contract                  2008579471df100926ca41be4cd6fac780a7c2cc53ae5f5b1555bdec50c19c39
candidate_effect.rs       85d624cd2a1c5b4f821b58aa30f4dbf4fb59c1f4c9650f88b51382c07cc95d3a
candidate_scheme.rs       9eaee3528f36fcac180fe3b0e0428c8f353c2911fb0b854e621e57e08720e4d7
shadow_apply.rs           c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff
Rust handoff              7c724916d590b06a52cd55f160b2e2ddf84fce6edf9bd02ea599b839b36adf99
Rust argv                 5ac9f05783b1f35077b3382c3319eeff02c0db5d9605f1d1482aa9e7a010e316
Rust stdout               72744a0f9dc4f8c1bba006815ffd3b3a6b37f95a00b8851e75f3f78b1f8c0927
Rust stderr               a4c61c4db3ac87bd2c188fffbee787c34239a7e96c044802414ce53dc53f22c8
ConstructorRealization   70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9
SourceOrigin             db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd
proof handoff             78c610644f143a575e9e179cd1b9a30c4b1d897824a68170760967886f8b4c76
reviewer identity         /root/identity_repair_final_review
```
