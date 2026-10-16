# NPAIR snapshot owner interface: readiness audit

Status: Draft, read-only design evidence only; no compiler-code authority.
Sprint: `npair-snapshot-owner-interface-20261017`, revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

## Result

The pinned owners contain the records needed in principle, but no existing
single accessor exposes a complete structural snapshot. A private borrow rooted
at `&InferenceSession` can prevent safe mutation while validation runs. The
minimum proposed interface is an owner-local, unforgeable borrowed aggregate
that retains that session borrow, a selected successful `GraphState` route,
its Permission/domain/view inputs, all relevant context relations/dependencies
and origins, and the complete admission/emission records. Its iterators must
preserve distinct source occurrences and every relevant evidence alternative.

This is feasible as a design shape, not yet a ready implementation. Existing
`RetainedInput`/`CircuitEvidence` is useful precedent for borrowed owner-bound
views, but it selects a partial relation closure and does not expose the full
physical BoundEvidence set or private FormalPermission records required here.
The required owner accessors and quiescent successful-route gate are not
presently supplied. The one-shot validator remains **not implementation-ready**
until the owner interfaces are reviewed and the independent proof below is
closed.

## Field-to-accessor and mutation table

| Owner | Required evidence | Existing access | Mutation/lifetime owner | Gap |
| --- | --- | --- | --- | --- |
| `InferenceSession` (`lib.rs`) | Owning session identity; candidate graph; constraint store and endpoint canonicalization; active route/checkpoint state | `candidate_graph`, `store` and route journals are private fields. Canonicalization is read-only through `canonical_value`/`canonical_effect`. Existing owner code repeatedly obtains mutable graph access. | Session route transaction and `route_journal`; `rollback_route_transaction` restores the session and candidate graph together. An `&InferenceSession` borrow excludes safe `&mut self` mutation for its lifetime. | No snapshot constructor checks quiescence, selects one exact successful route or retains an owner-bound handle. The caller must not pass free-standing IDs from another session. |
| `candidate_effect::State` | `formal_domains`; full `FormalPermission` path/occurrence/owner; `View` plus `OperationOrigin`; retained `Contribution`; processing/route association | `formal_domains`, `views`, `contributions` and `processing` are visible to the parent. `formal_permissions` and its record/path types are private; only construction, rollback and accounting read them. There is no full immutable permission iterator. | `candidate_effect::State::checkpoint/rollback` removes domains and truncates permissions/views/contributions. The enclosing intrusion and session route rollback own those checkpoints. | Add a crate-private borrowed Permission view that preserves the raw typed path, source occurrence, owner and domain key; connect its view index to this exact route without cloning. |
| `candidate_context::State` | Every relevant `Relation`, `Dependency` (including both ordered Replay inputs), `Origin`, BoundAdmission, BoundEmission and physical slot for the selected port | Relation/dependency/evidence stores are private. `evidence_snapshot` returns a small copy descriptor; current `CircuitEvidence<'a>` exposes a selected relation/context/view closure, not every bound admission/emission. `BoundEvidence` hides its arrays and group links. | `State::checkpoint/rollback` truncates relations, dependencies, origins, admissions/emissions and restores processing. Evidence IDs are meaningful only inside this owning live State. | Add a read-only owner-bound evidence view with complete group/admission/emission iterators and exact relation/dependency/origin access. Keep all IDs private to the view. |
| `candidate_scheme::GraphState` and selected `Graph` route | Route-local node/row/bound map and the bound-evidence references that tie the selected raw occurrence to candidate context records | `routes`, `graphs`, `local_routes`, `local_use` and `source` are held in one private session GraphState. `Graph` retains `bound_evidence`, nodes, rows, bounds and route root. There is no public snapshot identity or route borrow handle. | Session route journal truncates route vectors and rolls back intrusion/effect/context state. Intrusion has `generation`/`dirty`; those fields do not alone identify every graph/evidence mutation. | Add a route-scoped borrow created only after a successful quiescent route. Keep its route index and references owner-bound; do not treat a generation counter as sufficient identity. |

Relevant locators in the pinned files: `InferenceSession` and its route journal
in `lib.rs:7665–7811, 8200+, 9429+`; `candidate_effect::State`,
`FormalPermission`, `Checkpoint`, `rollback` and `formal_owned_bytes` in
`candidate_effect.rs:117–211, 249–380`; `BoundAdmission`, `BoundEmission`,
`EvidenceSnapshot`, `BoundEvidence`, `CircuitEvidence`, `RetainedInput`, context
`State` and `Checkpoint` in `candidate_context.rs:433–565, 820–1010, 1062–1213,
1732–1862`; `GraphState`, `Graph`, `FreshRoute`, `LocalFreshRoute` and
`refresh_bytes` in `candidate_scheme.rs:6–160, 297+`.

## Smallest proposed borrowed interface

The owner modules should construct an internal, non-public view along these
lines; names are schematic and no API is approved by this Draft:

```text
InferenceSession::borrow_candidate_snapshot(route_selector)
  -> Option<CandidateStructuralSnapshot<'_>>

CandidateStructuralSnapshot<'a> {
  owner: &'a InferenceSession,
  graph: &'a GraphState,
  route: &'a FreshRoute or LocalFreshRoute,
  effects: &'a candidate_effect::State,
  context: &'a candidate_context::State,
  selected source/formal records and bounded owner-local iterators
}
```

Creation is allowed only when the session has no active route journal; the
candidate graph is clean; typed processing/drain and replay continuations are
quiescent; and the exact selected route is retained. The API must establish
these predicates from owner state rather than accept caller assertions. If the
owners cannot identify the route selected by a formal Permission and its raw
`q_perm` occurrence, this is an exact readiness blocker.

The returned certificate keeps the private snapshot borrow, not merely a
lifetime-erased `RouteId`, pointer, generation or vector index. It accepts no
bare relation/admission/emission IDs from the caller. Owner-bound iterators
resolve every index before returning a record and preserve the physical slot,
raw endpoint, canonical representative, source owner/occurrence and provenance.
The borrow excludes safe session/graph/effect/context mutation, so rollback,
truncation and canonicalization changes cannot race the read. The certificate
cannot outlive the borrow or be stored for later reuse. This addresses
cross-session mixing only if all constructors remain private and the same
`owner` borrow accompanies every returned record.

`CircuitEvidence<'a>` demonstrates a borrowed state plus checked iterators, but
its selected closure is not this interface: it allocates masks from all
relation/context/view counts, carries an `Incomplete` result for some
transport inputs, and omits physical admissions/emissions and formal
Permission records. It cannot be promoted by relabeling its roots.

## Enumeration and accounting contract for a later implementation review

For the exact selected `D`/formal-domain negative root/path, enumerate all
qualifying lowers already present at the recovered raw Permission port. For
each lower, enumerate all associated admissions, physical emissions and
relevant Origin/Relation/Dependency alternatives. Validate the current physical
slot against the same owner and route. For each FunctionPort, retain actual
endpoints, field, variance and bound keys. For each Replay, validate and retain
both ordered lower and upper inputs. Keep raw occurrences separate even when
their canonical representative is shared.

Use an iterative worklist and an owner-scoped identity table. A complete
derivation DAG may share validation of the same evidence node, but must retain
every parent/alternative edge. Track active versus completed nodes so a cycle
on an unresolved premise path fails safely. Never select the first Origin or
accept mere graph reachability. If every relevant alternative cannot be
enumerated within a limit, return no certificate.

Count every premise/edge inspection, worklist pop, duplicate/shared reference,
alternative expansion, relation/admission/emission record check and physical
slot lookup. Charge work-stack and identity-table capacity growth, retained
witness capacity and all nested allocations using checked arithmetic before
publication. A unique-node count alone does not bound repeated scans. Stage the
entire finite witness privately and return it atomically; missing, stale,
inconsistent, cyclic-unresolved, incomplete or over-budget evidence returns no
partial certificate. Numeric execution ceilings require a separate reviewed
implementation contract after the owners expose auditable size bounds.

The current code supplies no `BoundEvidence` enumeration API and no
FormalPermission iterator. The snapshot guard must also prove successful route
quiescence; merely holding `&InferenceSession`, checking an intrusion
generation, or borrowing `EvidenceSnapshot` descriptors is insufficient.
These are the present owner-local tasks. No cloning of the solver and no new
semantic identity is proposed.

## Frozen inputs and limitations

- Sprint contract SHA-256
  `243525db31b3999778f6fd79eeb3de52399cff0e1a864c555615bb55bf6afed5`.
- Prior one-shot Draft SHA-256
  `2cf0d473f0c3a3f75474e54a99b5c1d4470ab338320272445eae0a5fe263e23f`.
- Supplier-boundary proof SHA-256
  `1ee864b00d61b774e56c5a965a062448151652ad45ab4ec8956e1f02e7fd685b`.
- Forward native-evidence proof SHA-256
  `1d2c827cdf7661cc77a9edbb869bffd3cdcca7b51afba418789eaae9abf3cb3a`.
- Exact native owner pins are listed in the frozen sprint contract.

This is a bounded static owner audit and interface proposal. It makes no claim
that the borrowed interface exists, that an executable gate is authorized, or
that structural incidence realizes `eta_op`, `realization_op` or adopted
`At(D,w,delta)`. The parent and production gates remain OPEN. No tests, builds,
probes, Cargo, source/compiler execution or code edits ran.
