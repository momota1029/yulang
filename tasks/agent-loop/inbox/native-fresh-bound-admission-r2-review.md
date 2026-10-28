# Phase-1 source-first review — NATIVE-FRESH-BOUND-ADMISSION/r2

Verdict: **REJECT. Do not run bounded checks; close R2 incomplete under its fixed contract.**

Reviewer `/root/native_fresh_bound_admission_review_r2`, session `NATIVE-FRESH-BOUND-ADMISSION-20261028/r2/source-review`; requested Sol/medium, observed model/effort UNKNOWN. ACK preceded source reads. Frozen Rust and Lean sources were inspected before handoffs. Read-only; no writes, Git, descendants, builds, checks, tests, Lean/Lake or formatter execution.

## Findings

1. **BLOCKING — disclosed non-waivable procedure deviation.** The Rust producer disclosed one read-only `git status` despite its no-Git restriction (Rust handoff line 40; contract review gate). No mutation is alleged. The admitted packet says no deviation is waivable, so execution eligibility cannot be restored by technical acceptance. Preserve R2 incomplete; do not retroactively waive the deviation.

2. **MAJOR — completed raw readback is absent from the native association test.** At Rust `candidate_scheme.rs:8128–8157`, the test reaches the actual returned emission and its admission, then checks equality among retained constructor records. It never reads admitted relation → current row → scoped flow → transformer root → raw transformer, and never rereads the addressed physical bound slot after completion. `ConstructorAfterAppend` records what the constructor saw at insertion, not completed raw observation. A wrong current transformer attachment can leave assertions true.

   Required closure: follow each returned emission through admission to current native relation/flow/root/raw lookup, handle logical identity explicitly, and authenticate the addressed physical observation after completion. Do not require prepared-root temporal equality.

3. **MAJOR — required mutations and duplicate ownership authentication are missing.** The new test contains no antecedent, emission, mapped/admitted-pairing or duplicate-association mutation. The unscoped assertion requires only that some mapped ID differs from admitted ID, so changing it to another differing value preserves the assertion. For duplicate records sharing source bound, antecedent and use origin, exchanging returned emission IDs can still yield an internally consistent join per receipt; distinct ordinal ownership is not enforced. Native append behavior permits distinct duplicate occurrences. Existing scoped demand-authentication does not establish the new unscoped recorder predicate.

   Required closure: authentic duplicate occurrences with distinct invocation ownership and non-vacuous rejection of every named field mutation against fixed native evidence on the required routes.

4. **MAJOR — Lean completion remains a conditional association projection.** At `NativeFreshBoundAdmissionR2.lean:308–350,372–389`, `DriverReturns` carries only counters and a saved ID; child constructors model no state transition. `same_bound_from_returned_emission` proves correspondence in the immediate insertion state. `completed_raw_readback` replaces only inventory and assumes the desired current `relationRaw` lookup. There is no relation establishing that actual native restoration preserves referenced admission/emission rows and the physical slot through child operations.

   Required closure: establish successful native completion projection and evidence preservation at the restoration owner, then derive completed association. Ordinary parent/context selection and executable refinement remain separately open.

## Useful progress and unchanged scope

The recorder at `candidate_scheme.rs:4283–4292` captures the actual driver-returned emission ID, improving on R1's preparation-copy approach. Scoped admission reuses the mapped relation; unscoped admission computes an ordinary relation independently. Lean calculates admission, physical append/readback and emission indices rather than directly publishing desired attachments. These advances do not discharge the findings or establish a source-qualified counterexample/regression.

Original inference-soundness quantifiers/shared witness, supported domain, effect policy, Simple-sub A/B, principality, termination, executor and production obligations remain OPEN.

## Authentication and proof status

| Artifact | SHA-256 |
|---|---|
| R2 contract | `415195c283db4b9c03dc9cac17e636507b9810261fa987dfc4ab36e514e900f0` |
| Rust source | `c4e7e86db1354bdda65e76763a5a0f4cde1902b76467a3fcdd604307de8d49bd` |
| Lean source | `d1bff386152537dc48b9ea107564114e4a90c3075b6dbe1478a5290be60c0780` |
| Rust handoff | `0638209417ff329a920b099d521fccb5ee37e79bbedf96082930137807027f23` |
| Proof handoff | `743c58c761e844b6049246fa7b1ce56ba1d13e5e274d460e6b108403a48fbb7b` |

All admitted dependency/manifests, Lean inputs/configuration, authority pins, R1 pins and uninstrumented root scheme hash matched. Lean kernel acceptance, printed types and axiom audits remain **NOT_CHECKED**. Exact elapsed/CPU/RSS UNKNOWN. Reviewer stopped after one read-only verdict.
