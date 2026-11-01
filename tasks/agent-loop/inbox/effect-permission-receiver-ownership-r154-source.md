# R154 implementation handoff — receiver ownership audit

Sprint / contract: `EFFECT-PERMISSION-RECEIVER-OWNERSHIP/20261102-R154`, revision 1, SHA-256 `f17ad7acc09f8045a4edb5bd453b87a310cae4252dff8e5e5bc1409772898a5e`.

Assignment: R154 implementation lane, handoff revision 1. Parent remains the original `YulangClosure.SourceProblem.InferenceSoundness` obligation, source/native correspondence, original A/B claims, and production; all remain OPEN. Baseline `41c1582a26a8e80dbaa95171b298fc229a53d4aa`. Frozen input patch SHA-256 `db49313b2b4dd1e3623f135cc043b4d8be296868c5ec3dbfe90efa6ae5a66438`.

Requested model/effort: Luna/high. Observed model/effort and active-time telemetry: UNKNOWN. No descendants. Exact output leases: this handoff and `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154.patch`. Claim class: source evidence / NO_PATCH. No compiler, Cargo, test, Lean, patch application, source write, Git mutation, scratch, cache, environment probe, or worktree operation was performed.

## Pinned source identity

The frozen patch hash matched. The exact committed blobs were read with `git show` and hashed:

| Baseline Rust blob | SHA-256 |
| --- | --- |
| `candidate_receiver.rs` | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` |
| `candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `candidate_scheme.rs` | `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |

No live dirty receiver/scheme bytes or quarantined runtime paths were read.

## Findings by removed check group

### Owner, batch, and live-state identity

**Classification: independently guaranteed by the current private constructor/caller chain; no source evidence that these three pointer equalities are independently variable at this consumer.** `ProviderNativeContextProjection::capture(owner)` obtains `source_internal` through `owner.source_internal_projection()`, whose `OwnedResidualProjection::capture` binds `owner`, `owner.session`, `owner.session.batch`, and the effect-algebra context directly from that same `owner`. It obtains the provider certificate from `owner.provider_entry_certificate()` and assembles the package from those same borrowed projections. The fields are private and there is no caller parameter for an alternate owner, batch, or state. This is a constructor argument, not a claim that equal ordinals identify owners. These guards may remain useful defensive assertions, but the frozen source does not show a foreign owner reachable through the current constructor path.

### Provider, arm, and operation identity

- `origin.declaration.id == schema.provider_identity`, `schema.provider_identity == schema.operation.id`, and `selected_arm.operation_identity == selected_arm.operation.id`: **independently guaranteed by source construction**. `assemble` obtains resolved source declarations, sets `provider_identity` by cloning the provider operation ID, and sets the selected arm identity by cloning the handled declaration ID. The projection still checks provider occurrence and `Arc::ptr_eq` with the exact provider declaration.
- `selected_arm.operation_identity == schema.provider_identity` and the same equality copied into `InventoryOwnerCall`: **independently guaranteed only on the successful suppression caller path; unsupported for a free-standing projection invocation.** `source_operation_match` compares the complete IDs and successful suppression planning rejects `KnownUnmatched`; the source-internal capture also checks the exact selected arm declaration and family. The projection itself must not be treated as proving this full-ID equality absent that caller condition.
- selected-arm ordinal equality and provider view/member coordinates: **independently guaranteed by shared construction on this packet's private path.** The catch request and owner-call selected-arm ordinal both derive from `owner.schema.selected_arm`; the provider endpoint is destructured once, then checked against the exact owner view index/reference, closed tail, and `allowed[member]` before capture. Dropping copied coordinate fields from the package removes local round-trip checks, but the current caller builds both from that same certificate.
- No provider/source-owner equality is required or inferred. The provider operation is resolved at the answer/caller source occurrence, while the permission owner is the relay's registered Lambda. Returned/local functions can have distinct source owners; operation/permission compatibility here is by resolved operation identity and the actual source-row/arm chain, not owner equality.

### Permission origin and coordinates

- `permission.concrete` provenance: **independently guaranteed for the selected relay permission by the source constructor chain.** `candidate_formal_entry_annotation` creates the retained `FormalEntryPermission` from the exact `Action::FormalEntry` annotation and Lambda occurrence. `SourceInternalProjection::verify_owner_round_trips` ties each retained registration back to that exact action, source Lambda annotation, source owner, annotation position, row position, and equal ordered `row.concrete`. The assembled Catch arm is read from that same relay LocalSource; assembly checks its resolved handled operation family against the singleton Lambda row. On a successful suppression plan, `source_operation_match` ties the provider's full resolved identity to that selected arm. Together these facts imply provider-family membership without equating provider owner and permission owner.
- Permission source owner, occurrence, annotation position, source row, and entry effect metadata are **retained and rechecked** in the modified consumer; the input patch does not remove those scalar comparisons.
- Registration lookup by scanning for exactly one matching record, preserving the compact permission-vector index, and pointer equality to the retained permission: **needs restoration at the package consumer.** The replacement `self.permissions.get(request.registration)` conflates formal registration with compact storage position. R117/R135 explicitly kept those coordinate spaces separate. A missing permission before this registration can make storage index differ from registration; a same-registration wrong/duplicate record must not be accepted by positional coincidence. Restore unique registration search, compare its packed index to the captured `permission_index`, and retain `ptr::eq` against the captured record. R135's accepted consumer finding specifically depends on this distinction.
- Exact concrete-member index / `get(index) == provider_family`: **needs restoration for the R119 ordered-member correspondence claim; not needed to establish boolean family membership on the fully authenticated successful suppression path above.** The removed `permission_member_index` is the first `position` in the exact permission's ordered concrete vector. Without transporting and reading that index, the package no longer preserves R119's first-match/indexed-read evidence (including duplicate families). I found no source basis to reinterpret an arbitrary index as the selected concrete member.
- Concrete-slice pointer equality between the Internal incidence permission and the retained permission inventory: **independently guaranteed by `SourceInternalProjection::verify_owner_round_trips`** on this path, which compares all retained metadata and the concrete allocation pointer. That does not make formal registration, packed record index, and concrete member index interchangeable.

## Disposition and source/native boundary

The frozen input patch removes more than redundant caller-derived checks: it replaces keyed unique permission selection with a registration-as-vector-index lookup, and drops the packed-record and concrete-member coordinates used by R117/R119. These are enough to reject the patch as a safe source slice. The committed baseline already contains the checks, so there is no useful unapplied change against that baseline to submit. `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154.patch` is the exact NO_PATCH marker; it is not a source patch and must not be applied.

This audit does not establish compilation, runtime reachability, source-to-Lean interpretation, R39/R45/R116 closure, original A/B closure, or production readiness. R117's native decoder remains a candidate mapping, R118's source/native correspondence remains open, R119's ordered-member result remains candidate evidence, and R135's review is limited to its exact uncompiled checkpoint. Green tests, source constructors, or these static implications do not close the parent theorem.

## Reused and rejected evidence

Reused exact evidence: R117 native decoder proof handoff `0d5d17927a9b1cd2c7c72fb8b1ba0f7be44c146f7057cd1730b1b31dfcd32e53`; R118 Rust handoff `edec3e3d1747b9b4c78ea6ce19c9cc19de9db1f1ac113e4001c230db9249fd2f`; R119 Rust handoff `731cc66eacc5f271bdf1d70054b8430ac0641ac55ac07281123f9fe5645e8e98`; R135 consumer review `8c11f692c6d2907fc64f27687c24c234e6d47a867b4a10524445bec030175761`.

Rejected as closure: R135 PASS is limited to its exact frozen candidate and explicitly does not establish compilation, runtime, source/native correspondence, theorem closure, or production. R119 establishes an ordered member candidate, not kernel/source interpretation. No prior result licenses using `registration` as the compact permission-vector index.

## Checks, budget, and stop

Checks performed: read the fixed sprint/operating instructions, hash-checked the frozen input and all seven pinned baseline Rust blobs, inspected only those committed Rust blobs, and read the named R117/R118/R119/R135 handoffs/review. No tests/builds/Lean were run, as forbidden. Actual CPU/RSS and active-time telemetry were unavailable; bound was at most 600 seconds. No changed paths beyond the two assigned output leases; no scratch or generated disposable paths. Writes are STOPPED and no child leases remain.

Next related step within this fixed packet: Luna can independently adjudicate the NO_PATCH result and, if continuing this candidate, issue a precise source-only lease to restore the permission registration/packed-index and ordered-member joins. This handoff does not request an expanded lease or authorize source writes.
