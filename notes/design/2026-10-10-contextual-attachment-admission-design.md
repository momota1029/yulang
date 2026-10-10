# Contextual annotation attachments and source-cycle admission

Status: Authoritative for the internal carrier and two reviewed source-cycle
acceleration gate; not authority to admit arbitrary concrete formal effect rows
or to publish deferred components
Scope: private successor representation, contextual lifecycle/rollback, and
exact acceleration for the two reviewed paired-ascription cycle shapes
Baseline: `c8da9dfff`
Reviewed-by: independent compiler-referee and spec-auditor; compiler-referee
delta review closed late-edge invalidation finding
Approved-by: user, contextual-attachment-admission q1/a1, 2026-10-10; contextual-attachment-member-identity q1/a1, 2026-10-10 (attachment grouping in §3.1 only)
Initial design draft SHA-256 (before lifecycle repair): `8ea4d90843a10e55c52e5c5380a0fa2824c8127a66df827019753277a04a0a70`
Authority: existing polarity-sensitive effect policy, selected residual
constructor-lineage identity, Simple-sub levels/extrusion, and parent-copy SCC
intrusion
Supersedes: none; §3.1 resolves the attachment-member grouping

## 1. Goal and boundary

This source example was previously paired with a claimed result, but the user
later corrected that result as a mistake. Do not treat the former scheme as an
expected result or source contract; the intended result remains unspecified:

```yulang
my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1
```

The general annotation policy remains unchanged: contravariant `[E]` supplies
local subtraction authority at that annotation position; it does not erase an
unrelated contribution with the same family. Covariant `[E]` continues to admit
concrete `E`, while type variables remain connected to later checks. The
retracted example result establishes no particular output for `run_io` or
handler residual behavior.

The current candidate has no concrete formal-row attachment consumer. It also
has no `Catch` case in `LocalSourceForm`: `catch` falls through to structural
projection. The VM and native backend entrypoints are stubs. The colon spelling
`run_io: cb 1` currently lowers only to an ordinary two-application source
shape; it is not a handler or intrinsic. Therefore this proposal does not
claim that adding attachment metadata alone makes the exact source inferable or
executable. Complete Call behavior and the generic source/runtime handler path
remain required separate owners.

## 2. Existing decisions retained

- Annotation polarity and the hygiene obligations above are Authoritative in
  [`annotation-effect-hygiene-integration.md`](2026-10-10-annotation-effect-hygiene-integration.md).
- Separate residual recipes retain constructor lineage. Applicable current and
  future source lowers fan out to each recipe; qualifying recorded parent/copy
  pairs still become equal through SCC intrusion. See
  [`contextual-residual-lineage-selection.md`](2026-10-10-contextual-residual-lineage-selection.md).
- This design selects the private contextual recipe representation,
  propagation/lifecycle, rollback, and exact two-cycle acceleration described
  below. The broader residual-owner draft remains historical for this selected
  slice; generic mixed-component admission and full concrete-formal enabling
  remain open.
- Existing Simple-sub extrusion and selected parent-copy intrusion remain the
  row identity and level authorities. Context must travel with those rows; it
  cannot replace their equality rules.
- No raw context cap, source restriction, diagnostic, resource threshold, or
  annotation meaning change is selected here.

## 3. Selected private source-owned records

These shapes define the selected private carrier, not a public API or a direct
copy of Oracle's weights:

```text
Attachment {
    attachment_identity,
    annotation_owner,
    exact_occurrence,
    concrete_member_ordinal,
    composed_polarity,
    resolved_effect_operand,
    lexical_scope,
}

ContextExpr = exact operation tree with shared child identity
Relation {
    component_kind,
    lower_endpoint,
    upper_endpoint,
    ContextExpr,
    origin_and_dependency_certificate,
}

ResidualRecipe {
    constructor_lineage,
    source_coordinate,
    retained_concrete_heads,
    residual_context,
    gamma_coordinate,
    live_source_feedback,
    exact_outgoing_gamma_to_tail_relations,
}

FilterRegistration {
    receiving_owner,
    resolved_allowed_set,
    attachment_or_boundary_origin,
    originating_relation,
}
```

`ContextExpr` must retain operation order and shared inputs. Structural
interning may share identical construction nodes; it does not assert semantic
equivalence, discard counts, or terminate the relation worklist. Attachment
identity remains distinct from nominal effect identity and from source
spelling.

### 3.1 Identity grouping within one annotation

The user selected one attachment identity per concrete atom set belonging to
one exact annotation occurrence. Every member keeps its own ordinal and
resolved effect operand under that shared identity. A different annotation
occurrence or fresh local annotation instance receives a distinct identity.
This follows Oracle's set-wide subtraction identity; it does not merge effect
families or grant cancellation authority to unrelated contributions with the
same family. This decision selects only attachment grouping. Simple-sub levels,
extrusion, qualifying parent-copy SCC intrusion, and the scoped propagation and
rollback rules above remain unchanged.

## 4. Proposed transition contract

The candidate uses one typed relation authority for Value and Effect
constraints. Every decision to normalize, memoize, omit, or replay a task reads
the relation record and its retained context, rather than reconstructing the
context from endpoint IDs later.

| Event | Required behavior |
| --- | --- |
| Task admission | Run attachment checks and registrations before endpoint-equality handling. Memo identity contains component kind, endpoints, and exact retained context. |
| Positive wrapper | Prefix the actual left operation and intersect filters at that source constructor. Keep nominal concrete contributions intact. |
| Negative wrapper | Check the allowed set and active-family obligations, register checks on the true receiver, then consume only the filter whose consequences are retained. Preserve right POP operations. |
| Bound insertion | Keep the existing level-selected orientation. Check new lowers against existing registrations, and check/register new filters against existing lowers. Store the post-check context and origins with each admitted bound. |
| Opposite replay | Replay each lower/upper pair in its recorded order and apply directed mix at that node. Keep both parent derivations and shared-input identity. |
| Function ports | Argument Value and ordinary argument Effect reverse endpoints and apply `swap`; result Value and Effect preserve context. Apply `both` only at the source-owned inferred-entry flow, with a certificate distinguishing that flow from a written annotation interface. |
| Concrete residual | Check concrete heads, retain only the attachment-local subtraction, create a lineage-owned gamma, and retain both source-to-head/gamma feedback and each exact gamma-to-tail projection. |
| Extrusion | Reuse existing level/polarity row maps; transport attachments, contexts, registrations, dependencies, and actual parent/copy provenance with the selected rows. |
| Capture/freshening | Capture the reachable relation/recipe/filter graph together. Rename generic coordinates and local attachment instances through one per-use map; preserve shared context inputs within a use and independent local authority between uses. |
| SCC intrusion | Equate only actual recorded parent/copy pairs that qualify in one SCC. Transfer both bound sides, origins, and contextual obligations; replay their Cartesian combination and fan every applicable current/future source lower to retained recipes. |
| Rollback | Journal context nodes, recipes, registrations, watchers, origins, memo entries, bounds, certificate state, certificate-dependent observations, and publication state as one route. Restore the whole route on failure. |

Equal endpoints alone do not justify self-omission. Checks, residual/output
consequences, latent Function obligations, and provenance must remain live or
be proved discharged before omission.

## 5. Admission and termination proposal

The source-reviewed paired-ascription family contains unbounded one-ID
left-PUSH cycles; one nested case generates all natural left `(POP, PUSH)`
count pairs. A raw finite number-of-contexts cap cannot be the admission proof
for that class. The reviewed effect policy also gives no permission to reject
ordinary source solely because its exact contexts are inconvenient.

For those two complete, source-reviewed circuit shapes, the selected exact
acceleration stores a symbolic count relation per contribution and origin:

- PUSH-only identity cycles: `p = 0, n >= 0`.
- The nested left-POP/left-PUSH identity cycles: `p >= 0, n >= 0`.

Finite downstream continuations would be checked against the full relation
with their actual sharing, bracketing, family, and filter data. A certificate
must include the complete generated SCC component, identity seeds, recursive
operators, attachment identities, filter registrations, sharing links, and
the full set of dependent observations. Fixture spelling is never the
recognizer.

When a new edge enters that dependency set, the owning transaction first marks
the certificate dirty and withdraws every observation, memo result, or
publication that depended on its prior generation. It then attempts exact
recertification and recomputes the dependent observations before publication.
If recertification shows the component is outside both certified classes,
retain the new edge and all exact contextual relations. Do not keep old
certificate-derived results, erase the edge, approximate its context, or turn
the private state into a public source rejection. The private candidate must
defer publication for the affected component until an exact general path can
finish it. This is a suspension of the candidate result, not a supported-input
boundary or a claim that arbitrary contexts terminate.

Certificate generation, its dependency edges, and all withdrawn/recomputed
observations are part of route rollback. A failed late-edge route restores the
pre-route certificate, dependency graph, observations, and publication state
atomically. A subsequent supported retry must be able to reuse only the
restored generation. Required implementation evidence includes the transition
from a certified component through a late unsupported Function/swap edge,
withdrawal of its dependent results, private deferral without publication,
and rollback followed by a supported retry.

This acceleration is a candidate for these circuits only. It does not decide
arbitrary mixed recursive components, correlated `both` recursion, or
residual-family/gamma generation. The general mixed-component admission
procedure is unresolved. The private deferral above protects transactional
correctness; it is not an implementation of inference for the deferred source.
Consequently this draft does **not** authorize admitting arbitrary concrete
formal effect rows or claim an output for the callback source example.

## 6. Approved implementation gate

This is M3 because it changes the private inference architecture and defines
how effect authority crosses replay, extrusion, freshening, intrusion, and
rollback. The independent semantic and conformance reviews described in §7
cover operation semantics, source conformance, exactness of the two circuit
relations, invalidation on late edges, and transactional behavior.

The user selected option 1 in contextual-attachment-admission question q1,
answer draft a1: implement this carrier and the exact two-circuit acceleration
as the next internal gate. Preserve the complete unbounded contexts for both
reviewed shapes. General concrete-formal admission, arbitrary mixed recursive
components, the callback example's still-unspecified output, and public/default
cutover remain behind their later gates, including exact mixed-component and
Catch/Call work. This selection does not create a resource cap or source
rejection rule.

This gate does not change the selected annotation policy, residual lineage,
parent-copy intrusion, complete Call requirement, or F5 replacement objective.
Implementation must add focused construction, future-lower, same-family,
filter, fresh-use, extrusion, qualifying intrusion, reverse feedback, and
rollback/retry regressions. The `run_io` source example has no established
expected output; the broader effect-hygiene policy and actual handler/inference
route remain required independently.
Concrete-formal acceptance remains disabled until its later admission gate.

## 7. Review outcome

The initial M3 review found one major lifecycle omission: a late edge could
invalidate a circuit certificate without withdrawing dependent observations
or including certificate state in rollback. The revised §4–5 contract now
marks the certificate dirty before publication, removes dependent results,
attempts exact recertification, retains unsupported contexts without a public
source rejection, defers the private candidate result, and journals the full
certificate generation/dependency/observation state for rollback and retry.

The fresh compiler-referee delta review closed that finding on the repaired
§§4–6 artifact. The independent semantic review found no other polarity,
residual-lineage, Function-port, or intrusion contradiction. The spec-auditor
reviewed the base draft and found no conformance finding; the delta adds
lifecycle safeguards without widening the source or annotation scope. The user
approved the bounded internal gate described in §6. Implementation
correspondence, certificate-recognition code, execution, and general
mixed-component termination remain unverified; approval is not a completion
claim.
