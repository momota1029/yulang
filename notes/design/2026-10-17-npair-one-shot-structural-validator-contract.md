# NPAIR one-shot structural validator contract

Status: Draft for independent review; no compiler-code or semantic authority.  
Sprint: `npair-operation-contribution-supplier-20261017`, revision 1.  
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

## Purpose and boundary

The previous forward-realization analysis identifies a native structural path
from the Permission construction port through physical emission/admission,
FunctionPort and ordered Replay evidence. The next source-supplier analysis
found no adopted constructor that supplies the original same-w incidence
`eta_op` or its correspondence `realization_op`. Therefore a native validator
can validate **structural incidence only**. This Draft specifies a one-shot,
read-only check of one fixed successful live snapshot. It does not authorize
source admission, compiler changes, an `At` consumer, semantic ingress,
subtraction or production.

The selected historical complete-Call proof bytes named by its adopted
definition are unavailable in the accessible Git history. Current later proof
bytes and the unadopted Operation primitive-image candidate are not substitutes.
This validator Draft uses only the reviewed forward proof's pinned native
evidence and adopted Permission shape; it supplies none of the missing source
constructor evidence.

## Input snapshot and lifetime

The caller supplies a read-only borrow of one successfully completed route
snapshot after the normal formal drains and both ordinary links 43/44. No
concurrent mutation, rollback, slot truncation/reuse or canonicalization change
may occur during the call. If the owning state cannot provide such a stable
borrow, there is no implementation path under this Draft; the owner must first
provide a separately reviewed snapshot guard.

The returned certificate is a temporary view tied to that borrow. It expires
when the borrow ends and cannot be retained in solver state, copied across
checkpoints, generalized, serialized or consumed by later propagation. This
avoids a subscription protocol and a durable invalidation mechanism. A caller
must reacquire and revalidate after every later mutation. Any future persistent
certificate or subscription to later lowers requires a separate live N-Ingress
contract and review.

Within the fixed snapshot, inspect every qualifying lower already present at
the recovered Permission port. A successful certificate requires complete
enumeration of the qualifying current evidence under the finite traversal
bound; inspecting only the first available lower or Origin is invalid. Later
lowers are outside this one-shot result.

## Structural checks

For the one raw Permission port occurrence recovered from the concrete
negative-domain root and its typed Function path, the validator checks:

1. The exact D, formal domain and path identify the same raw effect-port
   occurrence. Validate Function tags, field, variance and links 43/44; validate
   a canonical representative separately and never use representative equality
   to merge distinct raw occurrences.
2. The source Operation declaration/reference, owner and occurrence lead to the
   exact source-owned OperationOrigin, view and member for this signature
   construction. The live physical `Support(view)` lower matches its exact
   BoundAdmission, BoundEmission owner/lane/index and current slot operand.
3. Every FunctionPort premise matches its actual endpoints, Function field,
   variance operation and bound keys. Every Replay premise validates both
   ordered inputs and its endpoints. A relation chain cannot be accepted by
   graph reachability alone.
4. The derivation reaches a lower at the recovered Permission port and checks
   that lower's own admission and optional OwnerEmission.processing relation.
5. Every alternative relevant to the requested incidence is retained in the
   result. Do not select the first Origin, collapse distinct source occurrences
   by row/effect equality, or infer an original semantic witness from a member
   or Contribution ID.

The evidence is represented as finite derivation trees or an equivalent
explicitly checked finite witness object, not an unannotated graph path. A
cycle on an explored premise path is an unresolved derivation and yields no
certificate; it is not silently accepted or pruned. If complete alternative
enumeration cannot finish within the work bound, return no certificate.

## Work, storage and failure

Traversal order must be deterministic. The eventual implementation contract
must set explicit finite limits for visited evidence nodes, derivation depth,
alternative count and retained bytes. It must use checked arithmetic and
account private temporary storage before allocation/publication. This Draft
does not invent numeric production limits; the owning state and evidence
producers must first provide auditable size bounds. If those bounds cannot be
established, implementation is not authorized.

Accumulate the full result privately, validate all endpoints and lifecycle
conditions, then return the temporary certificate atomically. Any missing,
stale, inconsistent, cyclic-unresolved, truncated or over-budget premise
returns a structural-validation failure with no partial certificate. The
validator has no writes or solver effects; it never publishes a residual,
subtraction result, source event, ingress fact or `At(D,w,delta)`. Exhaustion
does not relax the evidence requirements.

## Independent gates remain open

Semantic witness realization remains OPEN until the original Operation
constructor supplies `eta_op` and `realization_op` and every source rule used by
the FunctionPort/Replay derivation lifts the same `w` and dependent coordinates.
Only a separate reviewed owner may then establish adopted `At(D,w,delta)`.

Source admission remains OPEN: the concrete receive formal is refused in
`candidate_source::preflight_formal` before `FormalAnnotation`. A structural
certificate does not alter that refusal or establish an admitted source run.

N-Transport, whole-presentation `rho_u`, actual receive consumption,
subtraction, mixed/multiple-symbolic coverage, F1/FK1, soundness, principality
and production remain OPEN with their original owners and quantifiers.

## Frozen inputs

- Sprint contract SHA-256
  `49d0676e745fc8b0c75f36ea20fd813b11d4f57d017756280488bc5aafa96c71`.
- Original forward proof SHA-256
  `1d2c827cdf7661cc77a9edbb869bffd3cdcca7b51afba418789eaae9abf3cb3a`.
- Operation supplier boundary proof SHA-256
  `1ee864b00d61b774e56c5a965a062448151652ad45ab4ec8956e1f02e7fd685b`.
- Adopted negative-pair proposal SHA-256
  `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`;
  adoption receipt SHA-256
  `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.
- Native source pins: `candidate_effect.rs`
  `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`;
  `candidate_source.rs`
  `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`;
  `candidate_context.rs`
  `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`;
  `candidate_scheme.rs`
  `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`;
  `candidate_extrusion.rs`
  `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b`;
  `shadow_apply.rs`
  `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`;
  `lib.rs` `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`;
  `yu-hir/shadow.rs`
  `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9`.

No tests, builds, probes, Cargo, compiler/source execution or code edits ran.
This Draft requires fresh architecture and specification review. It grants no
implementation lease.
