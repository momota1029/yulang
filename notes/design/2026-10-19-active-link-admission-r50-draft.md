# Draft: authenticated active-Link admission for scoped Apply

Status: **Draft rev2 — not adopted; independent review pending**  
Scope: candidate protocol for a bare recursive Local Name used while its
function initializer is active.  
Parent: full Simple-sub inference/evaluator theorem and original A/B remain
**OPEN, 0 -> 0**.  
Approval: none. This is an approval-ready proposal only; it changes no language
semantics or compiler code.

## Decision gap

The approved recursive-binding rule makes each recursive Name constrain the
same open monomorphic initializer root through `Action::Link`. It forbids a
`LocalScheme`/FreshUse route while that initializer is active. Scoped Apply
currently authenticates a bare local callee through its exact Name occurrence,
an installed scheme and `LocalFreshRoute`. R49 found no approved bridge between
these source modes.

This proposal adds a distinct active-Link admission rule. It does not call Link
evidence FreshUse and does not freshen the root. The first missing premise is
approval of this consumer rule; the source certificate and consumer path below
are proposed and unimplemented.

## Proposed evidence protocol

Use two linked facts with different lifetimes:

1. **Immutable source origin.** When collection takes the active-initializer
   branch for a recursive Name, seal a typed origin into the immutable source
   plan. It identifies source owner/schedule, Name expression and exact
   occurrence, `HirLocalId`, local slot, initializer endpoint, Name target,
   source-region ancestry, Link action index, and the owning Install boundary.
   Its constructor validates that the HIR Name resolves to that local and that
   the Link action has the exact occurrence/root/target tuple. Derive the
   boundary only from the owning Install/LocalAnnotation. Definition-body Links
   receive no active-local origin. A boolean or endpoint pair is insufficient.
2. **Ephemeral successful-prefix proof.** Do not retain a mutable per-occurrence
   success map. At the current `Action::Candidate(recipe)` step, a guarded source
   driver may pass an ephemeral proof to admission only when the same live frame
   and attempt own the immutable plan, `Stage::Execute` holds, `Frame.next` is
   exactly this Candidate index `j`, and the recipe/witness agree. The matching
   origin's Link index `i` must satisfy `i < j < k`, where `k` is its Install
   boundary. The source driver's monotone cursor advances only after each
   action succeeds, so reaching `j` proves the exact Link action at `i`
   completed in that frame. The guarded context must be passed from the actual
   current-action caller; `graph.source.is_some()` alone is insufficient because
   another caller reaches the admission gate.

At `candidate_call::authenticate_scoped_apply`, retain all existing HIR peeling
and exact `LocalCalleeRoute` checks. The new arm accepts only the bare Name
whose occurrence, expression, local, slot, target and initializer root match
the sealed origin, whose recipe is the current action, whose source region is
within the active initializer, and whose local slot is still unpublished. The
root comparison is source identity, not solver equality. The admission adds no
scheme, route, FreshUse, or new root. Installed generalized locals continue
through the existing exact `LocalFreshRoute`, scheme and authentic-use branch;
they cannot fall through to active-Link admission.

This smaller protocol is preferred over a retained evidence map because the
source frame already owns the immutable ordered schedule and advances its
cursor only after successful action execution. That fact is useful only if the
origin is sealed in the plan and a guarded current-action proof reaches the
consumer. If a future retry, suspension, or invalidation can reuse a frame, it
must add an attempt generation or prove equivalent freshness. No such retry
behavior is assumed here.

## Conditional preservation statement

Assume the approved active-Link admission rule and the proposed source-origin
and guarded-frame checks above. For any scoped Apply whose callee is the exact
bare recursive Name `o`, admission then requires that `o`'s own Link action
successfully constrained the same still-open initializer root before `o`'s
Candidate action and before the owning Install. A sibling occurrence, copied
route, definition-body Link, stale frame, substituted root or unexecuted Link
cannot provide those coordinates. The Apply reuses the monomorphic root and
creates no FreshUse, preserving the approved single-root construction at that
occurrence. This is a conditional local admission/refinement claim, not a
compiler theorem.

For the direct and nested-helper fixture, the two `loop` Names have distinct
occurrences but share the active local/root. Each origin must point to its own
Link and matching Candidate, both before the outer Install; nested-region
ancestry keeps the outer initializer active. Later helper uses still need their
own installed-local FreshUse routes.

## Falsifiers and implementation seams

Reject this proposal or a later implementation if any of these can admit:

- sibling or stale Name occurrence, another source attempt, or copied origin;
- a different local, substituted or merely solver-equal initializer root;
- premature Install, a closed scope, a definition-body Link, or an unexecuted
  or failed Link;
- a Candidate call without the guarded current-frame context;
- an ordinary installed local without its existing exact FreshUse checks.

The future code seam is `candidate_source::emit_candidate_source` for the
sealed origin; `step_candidate_source` / `execute_candidate_action` for the
guarded current-action proof; `candidate_call::authenticate_scoped_apply` for
consumption; and `shadow_apply::admit_candidate_fact` for the gate. Attempt and
transaction lifetime remain owned across `candidate_scheme::GraphState` and
`lib.rs`. The guard must close the alternate admission caller; a bare
`graph.source` check is not adequate. Intrinsic source failure currently drops
the private candidate session. A future retry or alternate publication path
needs its own lifecycle proof.

A later positive fixture must reach the real scoped `session.execute().unwrap()`
on unchanged source, trace both exact Links to their matching Apply actions,
show no FreshUse for those recursive Names, and retain separate exact FreshUse
routes for later helper Names. That would check implementation correspondence,
not prove the original parent.

## Remaining premises and boundary

The active recursion authority approves the monomorphic producer, not the new
consumer interpretation. Therefore approval of active-Link scoped Apply is the
first unsupported premise. The immutable typed origin and guarded frame proof
are also not implemented or independently reviewed yet. Endpoint equality and
`Frame.next` alone do not supply authority. No source typing, `Desc`/`D_q`,
complete Call, effects, F1/FK1, soundness, principality, termination, evaluator
correctness or production correspondence follows. Wrapped recursive callees
and other accepted source forms remain obligations in the original domain.

After fresh independent compiler and spec review, the user can adopt, revise or
reject this proposal. Adoption grants no code edits; implementation needs a
separate exact code contract. No source, fixture, test, build, Cargo or runtime
work is authorized by R50.
