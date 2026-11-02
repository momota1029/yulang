# Harness workflow simplification

Status: Authoritative — user approved the selected direction on 2026-11-03.
Reviewed-by: independent `spec_auditor` `/root/harness_policy_review`.
Reviewed revision SHA-256: `03b1ca248e18e0955ec51be414b26f68822be14fea7c3448081bb1f801bab45d`.
Implementation and runtime rollout remain separate from this authority decision.
Scope: repository research and maintenance coordination. No language, runtime,
proof statement, test expectation, production permission or existing lease is changed.

## Problem and selected direction

The user requested less restrictive source exploration and simpler handling of
session ownership while keeping write-collision prevention and independent
review. R280 and R282 stopped when their own packets prohibited rendering test
branches. Those prohibitions were packet-specific, not a general protection of
expected outputs. The stops, their evidence and charges remain historical facts.

1. **Explore broadly, authenticate conclusions narrowly.** A new assignment may
   inspect relevant repository source, tests and local dependency implementation
   read-only without a separate grant for each symbol or incidental `cfg(test)`
   branch. A read does not authorize an edit, prove production reachability, or
   change a test expectation. On handoff, identify and hash the actual sources,
   versions and production configuration supporting each claim; freeze these
   for independent review. Respect secrets, external access boundaries and any
   explicit user restriction. Existing admitted packets are not silently revised.
2. **Identify runtime observations by session and runtime identity.** A display
   path such as `/root/x` is not globally unique. Record a session namespace and
   actual runtime identity where available; retain assignment identity separately.
   Missing metadata or a roster scoped to another session cannot prove cessation
   or establish that another user started anything. Preserve exact UNKNOWN path
   quarantines and the distinct capacity-only release rules. Reused display names
   must not authenticate a stale launch, STOP, resume or capacity release.
3. **Do not make compactness a correctness gate.** The 16 KiB current-state size
   remains a diagnostic target, not an admission failure. Validate every worker,
   lease, release receipt, capacity and pending item regardless of size; never
   discard unknown leases or unconsumed results to fit a file. Archive resolved
   history when practical. A size warning does not authenticate a runtime event.
4. **Make review admission possible during a safe handoff.** Read-only review
   uses an explicitly reserved aggregate capacity slot, coordinated with the
   active scheduling owner or covered by an already exclusive reservation. A
   scoped roster alone cannot reserve capacity against another session. If the
   owner and aggregate reservations cannot be reconciled, defer only that
   assignment and continue safe independent work. After a reservation is
   confirmed, a primary unable to write the central record may keep an exclusive
   session receipt of the actual reviewer identity, launch, frozen inputs,
   requested/observed role, STOP and findings. Reconcile the receipt before
   claiming a completed gate or integrating the artifact. The reviewer gets no
   writes, Git, children or shared build/cache. This does not release a lease or
   establish cessation of an unobserved writer. A future atomic cross-session
   reservation mechanism needs its own reviewed rollout; an advisory lock used
   by only one session is insufficient.

## Preserved boundaries and rollout

Exact non-overlapping write and generated-output leases, single Git integrator,
unknown-writer quarantine, user-directed release procedure, independent nonauthor
review, semantic authority, proof quantifiers and question-bundle ownership stay
binding. Read-only exploration does not make a mutable source an accepted proof
dependency. An approved full objective retains standing authority for routine
bounded continuation; resource and material authority changes remain explicit.

The user approved the direction above in this conversation on 2026-11-03.
Before operative implementation the primary obtains independent workflow review,
resolves blocking/major findings, records that approval and review, and marks
this document Authoritative. This narrow decision supersedes only the requirement
in `rules/git-concurrency.md` disjoint-file mode to bound exploratory reads, and
the `rules/goal-driven-sprints.md` section 5 and `tasks/agent-loop/README.md`
16 KiB admission stop. It does not supersede central state ownership, exact
write leases, active-packet authority, or aggregate resource accounting. Then
update the operative rules, assignment template, skill and checker/tests together
and link this decision from the navigation. Apply the new default to new or
explicitly revised packets, never rewrite historical STOPs or treat an old packet
as if it had allowed a prohibited read. If identity collision, overlapping writes, stale
runtime receipt, capacity release of a path, or bypass of independent review is
observed, stop the affected integration and repair the protocol.
