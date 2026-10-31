# R33 Rust coordinate-translation handoff — snapshot-token gate OPEN

Assignment: `/root/effect_permission_r31_rust`; exact output paths are this
handoff and `tasks/agent-loop/artifacts/native-callback-coordinate-r33.patch`.
Sprint: `EFFECT-PERMISSION-NATIVE-CALLBACK-COORDINATE/20261031-R33`.
Requested model/effort: `gpt-6-luna` / `high`; observed model/effort: UNKNOWN.
Fresh Rust cap: 1,600 seconds; active interval was not instrumented and is
UNKNOWN. No R32 time transfers. Writes are stopped after these two outputs.

## Result

The pinned R30 candidate does not supply a source-grounded, serialized HIR
snapshot token. The archived `Machine` holds `Arc<RuntimeProgram>` and uses its
`_hir` to enumerate effect declarations, but the archived serializer emits no
token with its HIR-relative coordinates. The `RuntimeProgram` definition and
constructor are not among the pinned archive members. Thus the source proves
how indices are computed and which HIR owner they consult; it does not prove
that an incoming coordinate belongs to that same owner. **Foreign-snapshot
rejection stays OPEN.**

The patch artifact records the smallest owner-level addition and the required
checked decoder behavior. It deliberately contains no applicable source hunk:
the owner constructor/API needed to ground the token is absent from the frozen
source input. No guessed token accessor or identity representation is
proposed. In particular, formatted Debug fields, `SourceNodeKey` Debug,
module spelling, numeric indices, and spans are not substituted for a token.

## Pinned inputs

R33 contract SHA-256:
`77ea1171f71415e889d7391bfac042d3e44f6bd5b1bc1b5e094a5186f0c3aaca`.
R33 inputs manifest SHA-256:
`85d4b904897d911a9b6bc379d1369747a79698756a148573867e7eb72c2a8cc0`.
The R30 archive was streamed without extraction; archive SHA-256:
`5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`.

- `overlays/tools/inference-playground/src/runtime/machine.rs` — SHA-256
  `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`.
- `overlays/tools/inference-playground/src/runtime/receiving.rs` — SHA-256
  `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.

No files were extracted. The token-field search over both pinned members found
no `snapshot_token`, `hir_snapshot`, `hir_identity`, or `hir_token` owner.

## Coordinate construction and validator joins

`Machine` stores `program: Arc<RuntimeProgram>`. `RuntimeProgram::start_with_schedule`
constructs it with `program: self.clone()`. In the archived machine code,
`machine.program._hir.source_effect_declarations()` is the list used by both
identity serializers:

- `effect_identity_json` finds the family position by typed equality on
  `SourceEffectDeclaration.id`, then emits `hir_effect_index` plus Debug
  renderings of the module and declaration. Those Debug renderings are not
  identity evidence.
- `operation_identity_json` obtains that same typed family position, then
  finds the operation position within `declarations[family_index].operations`
  by typed equality on `candidate.id == *operation`. It emits the family
  object, `operation_declaration_index`, and a Debug rendering of the
  operation declaration. Thus the actual finite coordinates are
  `(hir_effect_index, operation_declaration_index)` and
  `hir_effect_index`, respectively, all relative to this one
  `machine.program._hir` list.
- Both helper functions use `expect` when an identity is absent. They do not
  return a typed missing/out-of-range error, and the JSON does not carry an
  owner token against which a foreign coordinate can be rejected.

The archived `propagate_request` joins the request and selected Catch within
one candidate pass. It skips a resolved arm whose typed `declaration.id`
differs from `request.declaration.id`. It clones the selected declaration ID
into `SelectedCatchInstallationEvidence.resolved_operation`, clones the
request ID into `RequestConsumerEvidence.operation_identity`, and stores
`selected_installation_source_index` pointing to that selected record. The
callback certificate serializes the request, consumer, and selected resolved
operation through the same `operation_identity_json(machine, ...)` helper.
These owners support a finite coordinate mapping inside one candidate HIR;
without the token, the serialized indices cannot establish same-owner
provenance.

The selected arm's own `SourceNodeKey` remains a separate issue. The selected
installation record retains typed `selected_arm`, and the Catch validator
compares it with the consumer arm. The callback certificate serializes
`selected_arm`/`consumer_arm` as Debug strings. `SourceNodeKey` Debug omits its
parse brand, green-node allocation identity, and source start; that output
cannot be used as a typed arm key. The operation identity on the selected arm
is instead the separately retained/serialized `resolved_operation`.

For the permission row, `CallbackResultSchema::from_parameter` accepts the
closed reviewed `() -> [E] int` form only: the result row must be present,
nonempty, and have no variables. It stores all `row.concrete` members in
`families`. `Receiving::callback_route_for_request` filters by membership of
the requested typed `SourceEffectId`, then clones every schema family into
`CallbackRouteEvidence.resolved_families`. The serializer maps each member in
order with `effect_identity_json(machine, family)`; the validator compares the
candidate vector to `entry.schema.families.to_vec()` and checks requested
family equality and membership. This supplies a complete finite row for the
pinned closed-row case. A checked translation must preserve every member,
order, and length; it must not filter or default missing/out-of-range entries.

## Minimal owner addition and decoder contract

The first missing premise is an opaque `HirSnapshotToken` minted by the source
owner that binds the immutable HIR to `RuntimeProgram`, stored on that owner,
and serialized beside all family and operation coordinates. Its producer must
distinguish distinct HIR owners even if source text and declaration indices
match. The archive shows `RuntimeProgram` is held by `Machine` and consulted
for HIR declaration lookup, but does not contain the constructor or any such
field. The minimal addition therefore belongs at the `RuntimeProgram`/HIR
binding constructor, then is read through the machine's retained owner. Its
construction rule and exact field API cannot be source-verified from this
archive and remain an explicit owner TODO.

Once that owner token exists, decoding must bind every coordinate to it before
lookup and return typed errors:

1. Compare the coordinate token to the selected immutable owner's token;
   mismatch returns `ForeignSnapshot` before any list lookup.
2. Decode the family using checked `get(family_index)`; absent or out-of-range
   returns `FamilyOutOfRange`.
3. Decode the operation using checked `get(operation_index)` within that
   family; absent or out-of-range returns `OperationOutOfRange`. Return the
   declaration's typed `SourceOperationId` and check R32 membership/round-trip
   by structural equality.
4. Map every permission-row family coordinate in order with a fallible
   traversal. Any failure rejects the whole row; success must equal the source
   row in order and length and establish R32 family membership for every
   member.

No such token-bound decoder can be source-grounded with the current archive.
An `Arc<RuntimeProgram>` exists in memory, but no token derived from that owner
is retained/serialized. Converting its pointer, Debug form, HIR indices, or
lossy source-node display into a purported cross-snapshot token would not close
this gap. The selected-arm Debug limitation also remains OPEN for faithful arm
identity serialization.

## Evidence, checks, and closure boundary

Read-only work: checked the frozen R33 contract/manifest/admission/ledger;
verified the R30 archive hash and both pinned member hashes; streamed only the
two pinned runtime members; traced coordinate serializers, HIR owner use,
request/consumer/selected-operation construction, permission-row construction,
and validator joins. Reused R32's covered finite projection as the local table
target. Rejected the R31 empty-table counterexample only as already repaired
by R32; no new Lean theorem or native execution is claimed.

No source file was edited or applied. No compile, Cargo, test, runtime, Lean,
Lake, Git mutation, project/worktree copy, archive extraction, target/cache,
log/scratch output, environment, or external directory was created. No
disposable scratch exists. The quarantined root `machine.rs` and `receiving.rs`
were not read or modified.

Status: `FROZEN_PROPOSAL; CROSS_SNAPSHOT_GATE_OPEN` because the archived source
does not ground or serialize the required token owner. No source snapshot
translation, native extraction, request emission, Grant provenance, native
History, original A/B closure, or production behavior is claimed. Independent
review remains pending. Writes are stopped.
