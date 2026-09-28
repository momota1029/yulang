# F5c logical-term preflight failure checkpoint

Status: the fourth supervised preflight passed the earlier closed-probe and
owner-peak checks, emitted its first two fixture tuples, then stopped in the
third synthetic graph fixture at its constructed-term count. The failure is
in the fixture's measurement of logical term count. A spec audit approved the
narrow measurement correction; its code delta is now present but still needs
post-write review and supervised preflight evidence. Diagnostic and matrix
processes remain behind preflight success.

## Failed attempt and evidence

Run ID `20260929-closed-probe-retry-01` exited 101 after 11.046 seconds. It
completed the `IndependentIdentities/D/32` and `IdentityAliases/U/32` cases,
then failed in `SharedAcyclic/D/32/K=32` at
`crates/yu-solver/src/tests/f5c_resource_probe.rs:1866`:

```text
assertion `left == right` failed: constructed terms
left: 6
right: 3
```

The supervisor recorded peak process-group RSS 960,745,472 bytes, minimum
`MemAvailable` 27,409,244,160 bytes, sidecar high-water 2,506,752 bytes,
minimum free disk 666,019,909,632 bytes, and 15 monitor samples.

Preserved evidence:

- `/tmp/f5c-preflight-20260929-closed-probe-retry-01.log`
- `/tmp/f5c-preflight-20260929-closed-probe-retry-01.monitor.jsonl`
- `/tmp/f5c-preflight-20260929-closed-probe-retry-01.summary.json`
- `/tmp/f5c-preflight-20260929-closed-probe-retry-01.events`

## Cause and repair scope

The builder records `terms_before` and `terms_after` by summing every entry of
`TermLaneState.lengths`. In `crates/yu-solver/src/term.rs:785-792`, those six
values include `pages.len()` twice, then page-position and journal lengths as
well as `positions.len()`, the logical term interner cardinality. A new first
page therefore contributes physical metadata alongside the three terms
constructed by the shared acyclic fixture, making the summed delta six. The
guarded-cycle builder uses the same mistaken sum for its `4 * K` term formula.
These assertions run before admission sampling and incoming routes, so the
previously committed closed-probe snapshot fix is not on this failing path.

The F5 foundation §34 requires exact logical term cardinalities. Its formulas
remain three terms per acyclic cone and four terms per guarded-cycle node. A
pre-write `spec_auditor` review confirmed that measuring only
`TermLaneState.lengths[3]` (`positions.len()`) preserves both formulas and the
approved contract. The implementation changes only the before/after count
source in `matrix_acyclic` and `matrix_guarded_cycle`; post-write review and a
focused check are pending.

## Next gate and budget

Post-write spec delta review and the feature-enabled test-target compile must
pass before a fresh supervised preflight. Use run ID
`20260929-logical-term-count-retry-01` with a 45-second process timeout and
10-second termination grace. If it fails again, keep diagnostic and matrix
processes blocked and reassess the exact assertion before another attempt.

The four completed supervised attempts used 16.06, 5.02, 6.03, and 11.05
seconds. The next preflight (45 seconds plus up to 10 seconds grace), the
reviewed 300-second diagnostic, and 150-second replay bring the maximum to
543.16 seconds and seven invocations, leaving 56.84 seconds under the
8-invocation/10-minute budget. One additional 45-second preflight plus its
10-second grace would bring the total to 598.16 seconds and eight invocations;
no further supervised process fits this campaign. The user authorized
autonomous continuation and expanded time/memory budgets; no approval pause is
needed.
