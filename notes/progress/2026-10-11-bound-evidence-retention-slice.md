# Inert bound-evidence retention lifecycle slice

Status: implementation and focused regression slice complete; independently
reviewed for the accepted constructor/test contracts. It does not mint or
consume circuit authorization certificates and does not close the approved
late-edge invalidation/publication lifecycle.

## Retained construction evidence

The candidate context now keeps typed producer records for bound admissions,
physical emissions, evidence groups, snapshots, replay recipes, reverse
construction dependencies, and transported fiber transforms. Evidence records
preserve their exact relation/bound identities and constructor causes. Missing
origin association remains explicit as a coverage gap. The records are inert:
they cannot authorize a circuit, erase a relation, publish a candidate, or
change language semantics.

Bound insertion, replay, extrusion/transport, capture/freshening, resource
accounting, and route rollback retain or undo these records with their owning
operations. Checkpoints remain length/counter snapshots; rollback truncates
new evidence and restores changed group heads and reverse indexes. The
conformance review specifically checked actual reservation-error handling,
partial import, multiple transport fibers, and named Function-port polarity.

Focused regressions now cover:

- a deterministic capacity-overflow error returned by the real
  `try_reserve_exact` call, including charged resource sampling, route rollback,
  no escaped evidence IDs, and retry;
- failure after one snapshot of a multi-snapshot import has succeeded, with
  rollback and retry;
- extrusion/transport of two distinct parent fibers with ambiguous origin
  association, exact antecedents and witnesses, duplicate handling, rollback,
  and retry;
- named Function-port operations: Argument and ArgumentEffect swap; result
  Value and Effect preserve; rollback/retry reproduces the port tuple sequence.

## Review and checks

The accepted three major review findings were closed by these focused tests and
their actual call paths. Independent semantic review found no new issue;
independent performance review found no blocking cost issue; the bounded
specification delta review passed the repaired cases. The reservation test
forces the real `Err` branch through capacity overflow; it does not simulate
allocator exhaustion. No timing benchmark was run.

Command:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib support_retention_ -- --test-threads=1
```

Result: 7 passed, 619 filtered. The scoped `git diff --check` passed. No broad
suite was run.

## Remaining lifecycle gate

The records still have no authorization consumer. The exact two-cycle
recognizer, complete dependency invalidation, rollback of dependent
observations, retention of late edges with private publication deferral, and
supported retry after such withdrawal remain unimplemented. General mixed
recursive components, full effect hygiene, soundness/principality, default
solver routing, and F5 replacement remain open. This slice is not evidence
that those goals are achieved.
