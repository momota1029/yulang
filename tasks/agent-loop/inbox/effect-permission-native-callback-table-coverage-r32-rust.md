# R32 Rust snapshot-coverage handoff

Assignment: `/root/effect_permission_r31_rust`; sole output lease is this file.
Sprint: `EFFECT-PERMISSION-NATIVE-CALLBACK-TABLE-COVERAGE/20261031-R32`.
Requested model/effort: `gpt-6-luna` / `high`; observed model/effort: UNKNOWN.
Fresh packet cap: 1,600 seconds; elapsed active time was not instrumented and
is UNKNOWN. No R31 time is transferred. Writing is stopped at this handoff.

## Finding

The pinned R30 candidate contains a finite, same-HIR set from which R32's
operation/family tables can be constructed for this one callback/Catch
snapshot. It supplies typed source identities internally and a finite-index
serialization in the test certificate. This is source-owner evidence only:
the archive is a recovered R30 overlay, not the quarantined root runtime or
current production source. No Rust code was applied or executed, and no native
extraction theorem follows from this mapping.

The mapping uses HIR declaration indices only as coordinates within the one
immutable `Machine.program._hir` snapshot. It does not use Debug text, spelling,
source spans, or operation names as identity. `SourceNodeKey` Debug text omits
its identity fields and is not a valid table key.

## Pinned inputs and owners

The archive was streamed without extraction. Archive SHA-256:
`5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`.
Candidate members:

- `overlays/tools/inference-playground/src/runtime/machine.rs` — SHA-256
  `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`.
- `overlays/tools/inference-playground/src/runtime/receiving.rs` — SHA-256
  `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.

| Snapshot component | Exact owner and same-snapshot join | Finite coordinate/evidence |
|---|---|---|
| Request operation | In `Machine::propagate_request`, `request.declaration.id` is the `SourceOperationId` on the pending request. The machine's `_hir` owns the source effect declaration vector used by the serializer. | `operation_identity_json(machine, id)` finds the operation's family position in `machine.program._hir.source_effect_declarations()`, then its operation position in that family's `operations`. The coordinate is `(hir_effect_index, operation_declaration_index)`; Debug strings accompanying it are presentation only. |
| Selected Catch operation and arm | Still in the same `propagate_request` iteration, the resolved Catch declaration is retained only when its typed `declaration.id` equals `request.declaration.id`. `SelectedCatchInstallationEvidence.resolved_operation` clones that ID; `selected_arm` clones `arm.source`. | The selected operation is serialized by the same `operation_identity_json(machine, ...)`, so its finite coordinate is in the same HIR index space as the request. The selected arm's own `SourceNodeKey` is not represented faithfully by its Debug text; it is a distinct source-node field, not the operation-table key. Its typed runtime record is retained internally and compared with `consumer_arm` by the Catch validator. |
| Consumer operation | `RequestConsumerEvidence.operation_identity` is cloned from that same pending request's `request.declaration.id` in the same block. `selected_installation_source_index` points to the selected installation record just pushed for this request. | The certificate's consumer `resolved_operation_identity` is built from the consumer's typed ID through the same HIR-relative coordinate function. Internal validator joins also compare the consumer identity directly to the selected installation's typed resolved operation. |
| Complete permission-family row | `CallbackResultSchema::from_parameter` accepts only the checked `() -> [E] int` shape, requires a present, nonempty concrete result row and no row variables, then stores `Arc::from(row.concrete.clone())` in `schema.families`. For the authenticated request, `Receiving::callback_route_for_request` clones every stored family into `CallbackRouteEvidence.resolved_families`; it records the requested family from `request.declaration.id.family`. | The certificate serializes every `resolved_families` member via `effect_identity_json(machine, family)`, which finds its `hir_effect_index` in this same machine HIR. The validator requires the serialized candidate row to equal the retained schema row and requires the requested family both to equal the expected typed family and to belong to the schema. Thus the supplied closed row is a finite family table, not merely a Boolean permission result. |

The operation table for this selected event can be built from the referenced
typed request, consumer, and selected-operation identities. In the candidate,
the Catch resolution guard and clones make these the same structural
`SourceOperationId`; retaining all three references still lets the Lean bridge
prove each decode/round-trip obligation. The family table can be built from
the complete `resolved_families` vector. Both index functions use typed
equality against declarations from the same immutable HIR, so distinct values
in that snapshot cannot acquire the same list position. `SourceOperationId`
is structurally family (`SourceEffectId`, including module and declaration
`SourceNodeKey`) plus operation declaration `SourceNodeKey`; `SourceNodeKey`
equality uses parse identity, green allocation identity, and source start.

## Coverage limits and falsifier

This is enough source data for finite coverage on the pinned closed-row
candidate, provided the Lean table is constructed from these exact referenced
identities and all members of `resolved_families`. It does not cover a row with
variables or prove that a current native execution produced this archive's
candidate snapshot. `operation_identity_json`'s numeric coordinates are
snapshot-relative; mixing a table from another HIR would invalidate the map.
The selected arm node's Debug serialization remains lossy; it cannot be used
as a `SourceNodeKey` table entry. The typed arm remains an internal source
owner, and this handoff claims only operation/family table coverage.

Falsifiers: a typed request/consumer/selected-operation mismatch; two distinct
typed operations or families assigned the same coordinate in this same HIR;
any closed-row family omitted from the constructed table; a permission row
member that cannot decode/round-trip; or identities/indices joined across
different HIR snapshots. The R31 review's empty-table witness remains the
regression falsifier: an empty table must fail coverage for the referenced
request operation and each permission-row member, rather than map them all to
default coordinates or `none` while allowing Catch application.

## Checks, boundaries, and stopped state

Read-only evidence: verified the archive SHA and member inventory; streamed the
two pinned runtime files; traced the constructors, query path, serializer and
validators above; read the frozen R31 review's empty-table counterexample. No
Cargo, tests, Rust compile/runtime, Lean/Lake, source edit, Git mutation,
project copy, archive extraction, target, cache, log, or scratch path was
created. No disposable scratch exists. The quarantined root `machine.rs` and
`receiving.rs` were not read for this mapping and were not edited.

R31 evidence reused: the typed `SourceOperationId`/`SourceNodeKey` identity
definitions and R31 review finding that unchecked empty-table projection is
unfaithful. Rejected any claim that R31's Debug-string failure established a
typed native collision. No change to source semantics, permission policy,
quantifiers, diagnostics, or expected output is proposed.

Status: `FROZEN_SOURCE_QUALIFIED_MAPPING`; independent review pending. The next
in-envelope step is the independent R32 review of this handoff alongside the
covered Lean module. Native extraction and all parent/production gates remain
OPEN.
