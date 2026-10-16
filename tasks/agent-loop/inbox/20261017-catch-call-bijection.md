# Frozen Catch Apply / CandidateSourceCall bijection handoff

Sprint: `catch-matcher-introduction-and-call-bijection-20261017`, contract
revision 2, SHA-256
`b378170117c13849e0aa40ad32897703b3b2c2b78d7dfc8741c78b5cc28c6ab2`.
Assignment / handoff ID: `assignment-catch-call-bijection-20261017`, revision 1.
Parent: original finite F1 action/Image obligation. `CATCH-EXIT-INPUT-1`,
FK1, FIRST-RESULT-ADEQUACY, H1-H2, JOINT_DEC, F5, source-Generalize/export,
principality and production remain OPEN.

## Runtime, authority and outcome

Worker: `/root/catch_call_bijection_impl`; current session
`current-session`; active-work acknowledgement sent to Luna after reading the
governing sprint rules, README, decision, skill and exact contract. Requested
model/effort: `gpt-6-luna` / high. Observed model/effort: UNKNOWN / UNKNOWN.
Sole author; no descendants.

Outcome class: research-example implementation / partial-HIR source-native
observation. Exact leases were only:

1. `crates/yu-solver/examples/research_catch_source_export.rs`
2. This handoff, `tasks/agent-loop/inbox/20261017-catch-call-bijection.md`.

No API, library, manifest, test, fixture, expected-output, source-domain,
diagnostic or semantic changes. No Simple-sub bypass, new rule, admission,
observation, profile, inference or authority was introduced.

## Behavior and correspondence added

The example now inventories every Apply in each HIR-owned supported
`LocalSource` carrier, validates carrier/root ownership and exact parse-owned
occurrence keys, and resolves the actual callee and argument indices from each
Apply form. For each public `CandidateSourceCall`, it requires exactly one
matching owner + source occurrence + source key; pointer identity then checks
the call source, callee and argument against those exact HIR-owned source
expressions. Per-Apply match counts must all equal one, and total counts must
agree, ruling out missing, duplicate, extra or foreign records.

The example also checks that the checking occurrence refers to the Apply and
that the supplied cause refers to that checking occurrence. The public API
exposes these IDs and internal consistency is checked, but LocalSource has no
independent expected constraint slot/cause identity to compare against without
reconstructing solver state. Other private `ApplySourceInput` fields likewise
remain unavailable to this source-level bijection. The existing observer's
artifact checks are used; no private state is reconstructed.

`UnsupportedItem` and `UnsupportedExpression` are now printed by kind as well
as in the full HIR error list, and the example stops if either prior partial-HIR
diagnostic disappears. The existing 138-byte specimen, parse/HIR attribution,
ordinary solve, conflict gate, fresh-use observation and authentic-root
exports remain in place. The candidate path remains
`LocalSource::Apply` -> ordinary `CandidateInference::solve` /
`CandidateSourceCall` -> borrowed observations and exports. No new generated
constraint, propagation, consumer or runtime execution behavior was added.

This authenticates correspondence only for Apply occurrences retained in
HIR-owned supported LocalSource carriers of the returned partial HIR. The
observed unsupported item/expression diagnostics mean it does not claim source
acceptance, complete source representation, source typing, handler adequacy,
runtime semantics, or parent closure. It does not discharge the proof's
`CATCH-EXIT-INPUT-1` premise.

## Evidence reused and checks

Reused the exact baseline example and prior primary run: the source literal is
138 bytes; the prior run reported `UnsupportedItem` at `0..44` and
`UnsupportedExpression` at `75..138`, three retained result Apply sites,
three source-call matches, and no source acceptance or typing. Reused the
existing public `CandidateSourceCall` accessors (`owner`, `source`,
`callee_source`, `argument_source`, `checking_occurrence`, `checking_cause`),
HIR `source_carrier_outcomes` / `local_source_for` / occurrence-source maps,
and `ParsedFile::owns_source_key`. Rejected prior count-only matching as
insufficient evidence for operand and owner identity. The predecessor
binder-repair's narrow correction was retained; no prior source-authentication
or identity check was removed.

Static checks only: baseline snapshot hash matched the leased baseline;
relevant direct API owner hashes matched contract pins for `candidate_call.rs`,
`shadow_apply.rs`, `module.rs`, and `local_source.rs`; inspected public
signatures and the existing observer's checking/cause validation; reviewed the
exact snapshot diff and output leases. No Cargo, build, test or example run was
performed. No Git operation, dependency mutation, scratch/generated path or
other output was created. The single feature-enabled Cargo invocation belongs
to Luna after fresh CLEAN pre-run review and the review/primary gate.

## Original parent application and missing evidence

No parent theorem progress follows. The frozen proof handoff's stable TODO
`CATCH-EXIT-INPUT-1` remains with Luna / the existing `MatchRequest_H`
source-definition owner: locate or explicitly specify the complete outside
matcher input/entry judgment from the original yielded and exit premises, then
derive its actual typed port incidence. The minimal later provisional native
evidence request is limited to an already-retained typed-entry certificate at
`Work::CatchArms -> candidate_catch_operation` and its actual consumer; absence
must be reported, not reconstructed from Function ports, spelling, conflicts
or successful call lookup. Falsifiers and original quantifiers remain as in
the proof handoff; this assignment grants no new code or semantic authority.

## Frozen outputs, budget and STOP

1. `crates/yu-solver/examples/research_catch_source_export.rs` — SHA-256
   `dfb67257941f628faa2c3c9f31504cedb5c53d8f12e25e08466ff3f8a71f933f`.
2. `tasks/agent-loop/inbox/20261017-catch-call-bijection.md` — this frozen
   handoff; its hash is transmitted separately to avoid self-hash recursion.

Assignment cap: 360 seconds. Active-time instrumentation is unavailable; charge
the full 360 seconds conservatively, zero remaining. No review or Cargo budget
was used. No CPU/peak-memory measurement is claimed. Worker state: STOPPED
after freezing these outputs; writes stop here. No known disposable scratch
paths.

Next in-envelope step: Luna obtains a fresh independent regression review of
these exact frozen bytes and the pins. Only Luna may then decide whether to use
the one feature-enabled Cargo invocation, capped at 120 seconds, with no retry.
Any run remains partial-HIR evidence and requires the separate bounded
post-run receipt review.
