# Initialization structural retention, round 3

Date: 2026-10-07
Status: focused feature-on/off verification and independent compiler/spec reviews passed
Scope: default-off read-only structural plumbing; no production cutover
Baseline: 6fb5d7f697d5d592e0a39532ddb4967b54e18090

## Evidence carrier

`ConstraintBatch::shadow_initialization_candidates` explicitly scans the retained
original HIR binding bodies. Only a complete `ResolvedExpr::Name` resolved to
that binding's actual `DefId` is a candidate. The corresponding existing
collection use must have the same branded definition as parent and target.
The owned carrier retains the original HIR, root, RHS occurrence, exact use,
parent, target, and frozen SCC component identities. It survives the consuming
solve without adding production result rows. `SolvedModule::shadow_initialization`
borrows that carrier and rejects a foreign collection, including a second
collection of the identical HIR. Current scheme access uses the existing cold
closed-scheme observer and charges no production query counters.

Source position queries join through the retained original HIR and reject a
foreign parse artifact. Ordinals are explicitly collection-local metadata;
identity comparison retains artifact brands.

## Pending boundaries

Every returned candidate continues to report both original-q1-source-envelope
recognition and pre-execution-enforcement pending. A multi-definition source
can have a structural candidate without satisfying the exact q1 judgment.
No API produces a permitting/rejecting execution outcome, semantic admission,
runtime provider, type fact, solver error, or theorem discharge. Current `Never`
is observed only after structural recognition and never recognizes a candidate.
The q1 executable-source design does not authorize a blanket policy for these
candidates or arbitrary `Never` sources. Production cutover remains prohibited.

## Gate and bounded complexity

Module registration uses `all(feature = "shadow-f5", feature =
"shadow-scc-observer")`, two existing default-off features. There is no new
manifest feature or normal-path call. The explicit scan is O(I) HIR items with
expected constant-time existing use/SCC index joins per candidate (plus actual
HIR identity equality/hash payload costs). It allocates O(C) owned records for
C candidates and one shared HIR/artifact reference. It performs no recursive
expression traversal, parsing, solving, or SCC recomputation. Borrowed iteration
is O(C); solve ownership validation is O(1); current scheme queries use the
existing root index with its actual root hash/equality payload cost. Source
queries use the existing HIR/source crosswalk facilities. Dropping the carrier
removes all new retention; removing the gated module removes the observer.

## Check packet

New focused integration tests cover exact self-edge/current Bottom (`Never`),
unchanged facts/errors/counters, lambda versus whole Name, two-member aliases,
multi-definition pending premises, foreign collection with shared HIR,
same-spelling independent artifacts, original position retention and foreign
source artifact rejection. No existing expectation was edited.

Producer ran no Cargo/build/test/format command under the exclusive primary
verification lease. Primary should run formatting checks limited to the new
Rust paths and the focused `shadow_initialization` test with both features,
then independent review on the frozen three-path artifact. Shared task/design
status synchronization and module registration belong to the primary.

### Primary verification and expected-assertion correction

The primary formatted only the two new Rust files, registered the module
behind both existing default-off features, and ran:

```text
cargo test -p yu-solver --features shadow-f5,shadow-scc-observer \
  --test shadow_initialization --offline -- --test-threads=1
```

The initial run compiled and passed three tests; its fourth compared raw
`SemanticFact` identities from two independently collected term arenas.
Those arenas have different brands by design, so that equality was an
invalid new test premise, not a production discrepancy. The independent
spec auditor approved the exact repair before it was written: snapshot
facts from the same solved module immediately before observer queries and
compare that exact snapshot afterward. Existing baseline counter/error and
current Bottom/owner/identity/position assertions remain. This checks exact
same-arena observer nonmutation; it claims no cross-arena identity equality.

The repaired focused run passed **4 tests, 0 failures** after integrating
remote `6cd43ea8`. Runtime limits were 180 seconds for the one Cargo command,
two Cargo jobs, and one test thread. The command completed in about six
seconds including compilation; no broad suite or Oracle execution was run.
The spec auditor also reviewed the implementation and found no additional
conformance issue. The independent compiler referee then reviewed the final
code/tests and passed without findings. The primary accepted both reviews.
The final feature-off `cargo check -p yu-core -p yu-hir -p yu-solver --offline`
passed in 1.46 seconds under the same two-job/180-second command bounds.
No new semantic rule is implemented here.

Frozen code/test hashes for the final compiler review:

- `src/shadow_initialization.rs`:
  `4eec9c014b92a40a9af45ae4423cfe7b701820a042d4ebd743a69e525adadf30`.
- `tests/shadow_initialization.rs`:
  `00e6d58ce47e44b4f8e73dc48793b7905840e8cd199f0f801b0e7bc9b80ab85d`.
- `src/lib.rs` with the two-line gated registration:
  `8e6f147a53943083a136a7204a0b1b9b8552ab438559a42934d466ab35a44dd5`.

Only review/verification metadata changed after that freeze. See the
[round-3 integration record](2026-10-07-successor-round3-review.md).
