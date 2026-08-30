# Performance policy

Performance is a design property, not a cleanup pass.

## Hot paths

Treat these as hot or potentially hot unless measurement shows otherwise:

- parsing and CST/AST transitions;
- lowering;
- inference and constraint processing;
- normalization and simplification;
- name resolution and scope lookup;
- diagnostics preparation;
- worklists, caches, and incremental invalidation;
- backend transforms over whole modules or functions.

## Avoid hidden work multiplication

Do not introduce:

- repeated calculation of the same fact in multiple phases;
- CST/AST rescans to recover information the owning phase could carry;
- large unnecessary clones;
- per-entrypoint reconstruction of the same table, map, or index;
- cache/invalidation schemes before their authority and rollback are clear;
- inner-loop allocations, hash-set construction, linear cross-checks, or branches without accounting for call volume;
- the assumption that a later cache will make an unclear algorithm acceptable.

Build the smallest clear kernel based on a known algorithm or explicit invariant, then extend it.

## Mandatory performance review triggers

A change needs performance review when it adds or changes any of:

- scan or traversal;
- nontrivial allocation or clone;
- cache, memoization, or invalidation;
- map, table, index, or worklist reconstruction;
- an inner-loop branch;
- recursive algorithm;
- parallelism, locking, or thread count;
- benchmark-motivated behavior;
- a verification command capable of high memory or long runtime.

## Evidence

Performance claims should identify the relevant work unit, input scale, allocation behavior, and wall-time measurement when appropriate. A benchmark result without a semantic-work explanation is incomplete; an asymptotic claim without representative measurements is also incomplete.

When adding a safety cross-check, account for how often it runs. Debug/test-only code can still dominate a suite when invoked on every insertion or solver step.

## Resource safety

Do not run an unscoped or unfamiliar heavy suite merely to be thorough. Establish the current test inventory and expected resource profile first. Historical yulang2 incidents are recorded under `notes/incidents/`; their old skip lists are not current yulang3 policy.
