# Draft: authenticated active-Link admission for scoped Apply

Status: **Draft — not adopted**
Scope: candidate protocol for the existing scoped Apply experiment when an
unannotated recursive Local Name is used while its function initializer is
active.
Parent: full Simple-sub inference/evaluator theorem and original A/B remain
**OPEN, 0 -> 0**.
Approval: none. This draft is an approval-ready proposal only. It does not
change language semantics, the approved recursive-binding behavior, or
production/compiler code.

## Decision gap

The approved recursive-binding rule makes each recursive occurrence constrain
the same open monomorphic initializer root through `Action::Link`. It forbids a
LocalScheme/FreshUse route while that initializer is active. The scoped Apply
experiment accepts a bare local callee only when it authenticates the exact
Name occurrence through an installed scheme and occurrence-indexed
`LocalFreshRoute`. The Link and FreshUse protocols describe different source
modes. R49 found no approved bridge between them.

The proposal below keeps those modes distinct. It supplies an explicit
candidate authentication judgment for a successful active Link; it does not
rename the Link evidence as a FreshUse route.

## Candidate protocol

For a source owner `s`, let `o` be the exact HIR occurrence of a recursive Local
Name, `l` its `HirLocalId`, `tau` the active initializer instance for `l`, `r`
its open monomorphic value root, and `t` the value target for that Name. The
source scheduler already distinguishes an active Local Name from an installed
one and emits `Action::Link { occurrence: o, endpoint: r, target: t }` for the
former.

Propose a private `ActiveRootLinkEvidence` record, distinct from
`LocalFreshRoute`, with fields equivalent to:

```text
source owner s
Name occurrence o
local identity l
active initializer token tau
initializer root r
Name target t
Link action identity / source order position
successful execution receipt
```

The precise Rust representation remains open. A source-only boolean, endpoint
pair, or record created solely while building `ApplySourceInput` is insufficient:
it does not prove which Link action ran successfully. The evidence must be
installed only after the exact scheduled Link has been accepted by the private
solver state.

### Required transitions

1. **Schedule.** When HIR resolution identifies `Name(o) -> Local(l)` and `l`
   is in the active-initializer map, create an immutable source descriptor tying
   `(s,o,l,tau,r,t)` to that exact `Action::Link`. Do not create an installed
   scheme, capture, FreshUse, or LocalFreshRoute.
2. **Execute Link.** Before applying the Link, validate that its descriptor
   matches the action occurrence, endpoint and target and that `tau` is still
   the active initializer instance for `l`. Record a successful-Link receipt
   only after the ordinary monomorphic Link update succeeds. A failed or
   skipped Link creates no receipt. Keep this state private to the inference
   attempt.
3. **Authenticate Apply.** For a scoped Apply whose existing
   `LocalCalleeRoute` witness is `(expression, o, l, slot)`, accept the active
   branch only if a successful receipt exists for that same `o`, and all of
   `(s,o,l,tau,r,t)` match the source descriptor and the still-open initializer
   lifetime. The Apply witness remains exact: no sibling or same-endpoint
   occurrence can substitute. Apply the existing native relation to the same
   live root; do not freshen it.
4. **Install / end attempt.** `Install(l,...)` closes `tau`; any pending evidence
   for `tau` becomes unusable and is discarded. Failed private attempts publish
   no route/evidence to a later attempt. Existing installed generalized uses
   continue through `LocalFreshRoute`, `LocalScheme`, `commit_local_use`, and
   their existing rollback boundaries.

The candidate abstract rule is:

```text
ActiveLink(o,l,tau,r,t)   LinkSucceeded(o,r,t)   Active(tau,l,r,s)
LocalCallee(o,l,slot)     SameSourceOwner(o,s)   ApplyBeforeInstall(o,tau)
--------------------------------------------------------------------------
                  AuthenticateScopedActiveApply(o,l,tau,r,t)
```

Every premise needs a producer. In particular `LinkSucceeded` cannot be
reconstructed from endpoint equality, and `Active` must denote the same
initializer instance rather than a reused local ID or stale scope.

## Candidate ownership seams

| Owner | Proposed responsibility | Existing evidence / gap |
|---|---|---|
| `candidate_source::emit_candidate_source` | Attach an active-initializer token and local identity to the exact recursive Link descriptor; preserve source order | Current `Action::Link` has occurrence, endpoint and target, but no local ID or active-instance token |
| `candidate_source::execute_candidate_action` | Validate the descriptor and publish attempt-local successful-Link evidence after the ordinary Link succeeds | Current executor performs the Link update but publishes no route/auth record |
| `candidate_call::authenticate_scoped_apply` | Add a distinct active-Link authentication arm keyed by the exact callee occurrence; retain the existing FreshUse checks for installed locals | Current scoped-local branch requires `local_route_by_occurrence[o]`, installed scheme and authentic FreshUse |
| `shadow_apply::admit_candidate_fact` | Continue invoking the central authenticator before scoped admission | Existing gate already centralizes this check |
| `lib.rs` / attempt owner | Ensure evidence is private to the current candidate attempt and cannot outlive the active initializer or leak after failed publication | Existing LocalUse transaction journals route state; R49 did not establish how a new evidence map joins that journal |

The table identifies possible owners, not an implementation grant. The design
must settle whether successful-Link evidence is action-local or stored in an
attempt-owned occurrence map. It must not be installed in the generalized
`local_route_by_occurrence` map.

## Preservation obligations and falsifiers

A later implementation would need to establish all of the following before
cutover:

- The exact HIR occurrence resolves to the same local identity and owner that
  selected the active initializer root.
- The Link action operates on that root with ordinary monomorphic constraints;
  the Apply path adds no independent root, scheme, or freshened copy.
- The exact Link actually succeeded before its matching Apply is admitted.
- The initializer token is live at both events and closes at the corresponding
  Install; nested helper traversal retains the outer token only while the outer
  initializer is active.
- An installed helper or later local use still requires its own exact
  LocalFreshRoute and authentic FreshUse. The new arm cannot accept ordinary
  locals by endpoint resemblance.
- Evidence is attempt-local. A failed Link, stale token, failed route, or
  discarded candidate attempt cannot leave a successful receipt available to a
  later source or solver attempt.

Reject this proposal or an implementation if any of these substitutions can
admit: a sibling occurrence, a different local with an equal endpoint, an
initializer from another source owner, a closed/reused token, a premature
Install, a failed/unexecuted Link, or a copied boolean without producer
provenance. Also reject it if it changes source action order, monomorphic
constraints, existing effect flow, ordinary generalized-local behavior, or
observable failure boundaries.

## Space, work and failure behavior

A separate occurrence-indexed attempt-local map would use O(k) records for `k`
active recursive Name links and expected O(1) lookup/insert, in addition to the
existing source action storage. A compact action-local certificate may reduce
retained space, but only if the consumer can verify successful Link execution
and active lifetime without reconstructing them from IDs or endpoint equality.
The implementation design must compare these options against current scoped
work limits and ensure allocation failure cannot publish partial evidence.

No choice is made here about same-session replay. The approved recursive
binding design already makes a failed candidate inference discard its private
session. Any use of route-level rollback must journal the new evidence if that
route can fail after recording it; otherwise the attempt owner must discard the
entire evidence state. Do not claim full restoration or retry safety without
tracing the actual owner.

## Required user decision after review

Independent review should identify any missing owner or preservation premise and
confirm that the proposal preserves the approved monomorphic self-recursion
behavior while changing only the candidate scoped-admission evidence protocol.
After a clean review, the user must choose whether to adopt this architecture,
request a revision, or reject it. Adoption still grants no compiler edit. A
separate exact-path implementation contract must then pin the adopted text and
assign producer, consumer, lifecycle, regression and proof obligations.
