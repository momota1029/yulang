# Module entry provenance: source/native data contract

Status: Draft — bounded source/native representation contract
Sprint: `module-reference-materialization-20261017`, revision 2
Baseline: `2b563076a0ac2c4f0b66a277c1b557dac8134313`
Authority: [adopted ModuleEnv-Expose*](2026-10-17-module-environment-exposure-definition.md)
Original conditions closed: 0
Implementation lease: none; candidate source/call paths remain quarantined

## Observed producers and consumers

At the inspected baseline:

- `candidate_source.rs` recognizes a resolved `LocalSourceResolution::ModuleDef`
  while collecting a `LocalSourceForm::Name`. It records
  `PendingDefinitionUse { parent, target, occurrence }` and queues
  `Action::Module(occurrence)`.
- During action execution, a registered `DefinitionUseId` is routed through
  `route_candidate_open_use` when it is an active intrusion use, otherwise
  through `route_incoming`. This chooses a native routing operation from the
  candidate graph state; it does not form or authenticate a source typed
  Published/Family/Mono/Alias/Live entry.
- `CandidateSourceCall::module_callee_target()` observes an already validated
  direct ModuleDef callee name and returns its HIR `DefId`. The observer does
  not inspect solved endpoints, unwrap source wrappers, or produce the source
  occurrence's typing derivation.
- `PendingCallConstruction::suppliers()` explicitly retains
  `ModuleNameSourceTypingAndAdmission` and
  `ModuleUseReceivingExportCorrespondence` for a module callee. These remain
  unsupplied.
- The prior native FreshUse retention result keeps the actual native remap
  alive through its GraphState owner lifetime. It establishes neither source
  constructor classification nor a fieldwise source-to-native interpretation.

These facts give useful structural incidence but not the new semantic owner.
The compiler implementation has no current authority to treat `target` or a
native route as proof of the source entry constructor.

## Required representation boundary

Any future implementation must preserve the distinction between an authentic
source entry and its native image:

| Record | Required data | Owning producer | Current evidence |
|---|---|---|---|
| Binding identity | Declaration identity, binding occurrence and lexical/component scope | HIR/source registration | `target` and `occurrence` are retained; complete typed owner reference is absent |
| Typed entry owner | Exactly one actual Pub/Fam/Mon/Ali/Liv constructor, its derivation and complete contract/root dependencies | Publication, family, capture/rebind, alias or recursive registration rule | No constructor tag or derivation retained in the inspected native record |
| Component environment | Registered component identity, complete simultaneous member relation, exact predecessor publications and each member's Live tuple | Module component registration/publication | Component/action routing exists; typed environment exposure is absent in native records |
| Scope transport | Source/target scopes, composed dependency-preserving map and provenance | Actual module/lexical restriction or import/rebind owner | Not supplied by `DefId`, occurrence or FreshUse remap |
| Occurrence use | Exact resolved incidence, selected typed entry, transport, original branch introduction and whole reference/allocation map | Source Name/use formation | `PendingDefinitionUse` supplies only parent/target/occurrence |
| Native image | Explicit interpretation of every source field into native IDs/maps, with lifetime owner and invalidation rule | Native registration/materialization | FreshUse lifetime is known; source Sig/Phi_u and fieldwise image are missing |
| Call construction | Typed source admission, receiving/export mapping, original complete Gen-Call operands | Original Call/source construction | Two explicit pending suppliers remain in `candidate_call.rs` |

Missing fields are pending, never inferred from successful solving or from a
matching provider ID. The native record may point to an authentic source
certificate once one exists; it cannot itself create that certificate.

## Lifetime and failure behavior

Publication-owned entries must outlive the component-local execution frame
whose later source references use them. A reference to a registered recursive
member must continue pointing to its simultaneous Live tuple after publication;
publication cannot rewrite it as a Pub occurrence. Captures/rebinds and aliases
retain their own actual owner and complete antecedent map. Scope transport
retains all typed dependencies and cannot move EventProof or other dependent
fields before their binders.

The producer must form the complete private typed entry and validate its owner,
scope map and dependencies before making the result visible. Missing or
malformed provenance aborts that private materialization without exposing a
partial typed record. Exact capacity restoration on this failure path is not
required by the governing inference principles. Cache invalidation and
publication atomicity need a concrete native owner design before code is
authorized.

## Implementation boundary and falsifiers

No representation can yet be claimed implementable in the inspected Rust
owners: the source `Sig`, complete component registration relation, actual
environment transport operation, source `Phi_u`, and registered Call root are
not available from the present records. This packet does not add a tag field or
clear either pending Call supplier.

Before a code lease, resolve exact cessation/path ownership for the inherited
UNKNOWN implementation writer, identify the actual source formation producer,
and independently review this contract. Then lease only the smallest concrete
owner set. Falsify a candidate implementation if a typed tag lacks its owning
source derivation; a capture/alias/Live reference is relabelled; transport drops
a dependency; a field claimed as part of the semantic native image has no source
preimage (ordinary native bookkeeping fields are excluded), or a source field
has no native image; or a pending Call supplier is treated as satisfied without
its complete original operands.

Current result: data contract draft only. No compiler change or runtime behavior
is established; no original condition is closed.
