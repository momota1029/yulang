# Transactional retained replay foundation

Date: 2026-10-11
Status: reviewed implementation slice; actual source suspension remains open.

## Scope and authority

This slice implements retained replay-child batches and bound-restoration
continuations in the private candidate context. It follows
[`private candidate suspension contract`](../design/2026-10-11-private-candidate-suspension-contract.md)
§§3–7 and the contextual attachment design §§4–6. It does not claim an
end-to-end source suspension path or close lifecycle certification.

Replay operations now keep distinct queued and consumed cursors. A child is
acknowledged only after its typed drain and associated completion work
succeeds. Enqueue reserves evidence and typed-worklist capacity before
recording the transfer; failure-injection coverage checks ordinary/direct
drains both before and after queue reservation. Restoration retains the
accepted emission, saved opposite count/index, current replay and provenance,
and commits or rolls back its undo state transactionally.

Retained child capacity is accounted in O(1). Commit and rollback visit
route-created IDs and route undo entries rather than historical map capacity.
A structural regression seeds 64 replay and 64 restoration entries with map
capacity 112, then checks that an empty route retires zero candidates. Other
tests cover prior replay-pointer retention/reclamation and byte restoration.

## Review and verification

Selected mode: M3, because replay completion and rollback determine whether
accepted obligations can be lost. Independent compiler-referee and
spec-auditor reviews passed with no findings. Performance review found no
blocking or major issue; residual P3 is unmeasured peak retained storage for a
realistic high-fanout route. No production-performance claim follows.

The implementation worker ran seven sequential, one-job Cargo test
invocations (nine executions, eight distinct directly affected tests),
including the four injected enqueue-failure combinations. Primary ran:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-apply-candidate
git diff --check
```

The check passed with three dormant warnings for retained-input/provenance and
owned-byte fields. Their existing owner is the incomplete full lifecycle path;
removing them would discard approved provenance/accounting state. No RSS or
timing measurement was run.

## Remaining gate

This foundation does not implement actual source suspension, lifecycle
invalidation/recomputation, freshening continuation, or atomic SCC
publication. The q113 source-level A/B decision also remains open: no
authentic failing source witness or exhaustive impossibility proof exists.
The next source-state work must construct the exact original-Y Function field,
its ordered `q <: X` and `X <: Y` comparisons, retained merge, and an
unrescued required omega, or establish exhaustive coverage ruling that route
out. Route-local obstructions and the historical control run do not decide A/B.
