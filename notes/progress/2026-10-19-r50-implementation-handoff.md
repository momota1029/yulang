# R50 design and implementation handoff

Status: **PROPOSED**, read-only source map; no compiler slice authorized.
Parent inference/evaluator theorem and original Simple-sub A/B remain
**OPEN, 0 -> 0**.

## Current source path

- `candidate_source::emit_candidate_source` detects active local function
  initializers and emits an exact-occurrence `Action::Link`; the current action
  carries occurrence, endpoint and target, but not the local identity or an
  active-initializer instance token.
- `candidate_source::execute_candidate_action` applies the Link to the shared
  open value root. It does not create an occurrence-indexed FreshUse route or
  successful-Link authentication record.
- Scoped Apply scheduling preserves a `LocalCalleeRoute` with expression,
  occurrence, local identity and slot. `candidate_call::authenticate_scoped_apply`
  then requires the same occurrence's committed `LocalFreshRoute`, installed
  scheme and authentic FreshUse instance.
- `shadow_apply::admit_candidate_fact` invokes that authenticator before
  admitting the scoped Apply relation.
- `GraphState::commit_local_use` publishes route maps only after a Local use
  completes; transaction rollback removes routes created during that failed
  transaction. R50 has not established an equivalent lifecycle for a new active
  Link evidence record.

The proposed seam is a distinct, private ActiveRootLinkEvidence path connecting
a successful exact Link action to its exact Apply witness. It must preserve one
monomorphic root and must not fabricate a FreshUse route. Two candidate storage
shapes remain for review: an attempt-local occurrence-indexed record, or a
smaller action-local certificate whose producer, successful execution and active
lifetime can all be checked at the consumer. Prefer the smaller shape only if it
retains those proofs directly.

## Candidate implementation sequence (not authorized)

1. Extend the source action descriptor with the exact local/root/active-scope
   identity needed to distinguish this Link from unrelated Link actions.
2. On successful execution, record a producer-backed receipt in private
   attempt state, with a finite per-source bound and safe allocation failure.
3. Add an explicit active-Link arm to scoped authentication, matching the exact
   `LocalCalleeRoute` occurrence and active initializer token; leave installed
   FreshUse authentication unchanged.
4. Close/discard the token and its unused receipts at Install or attempt end;
   prove failure and transaction ownership before claiming cleanup.
5. After user approval and a later exact code grant, add positive direct/nested
   active-recursion coverage and negative sibling/stale/root-substitution/
   failed-Link cases, then focused verification and independent source review.

The first three existing owners inspected are the action producer/executor in
`candidate_source.rs`, the route publisher/transaction in `candidate_scheme.rs`
and `lib.rs`, and the scoped authenticator/gate in `candidate_call.rs` and
`shadow_apply.rs`. They expose no presently authorized code slice under the
existing admission rule. The candidate seam is therefore design-only until the
review/approval boundary.

## Exclusions and status

No source, fixture, expected-output, API, test or semantic edits occurred in
R50. No build, Cargo, test or runtime probe was run. The two tracked test-only
worktree diffs and older R36–R48 artifacts are outside this handoff and remain
untouched. This artifact is not implementation evidence and cannot close a
proof or production gate.
