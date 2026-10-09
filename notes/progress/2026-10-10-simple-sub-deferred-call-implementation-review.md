# Deferred Call constraints: actual Simple-sub verification

Date: 2026-10-09 (execution date; filename follows the active research series)
Branch: `research/simple-sub-intrusion`
Reviewed code baseline: `5c8efdcbc18fc493c3188a132f44491db60d739f`
Integrated dependency baseline: `90629b21682e3aecb51df7de4f7cdd801212647a`
Status: independently reviewed and executed test-only construction
Production routing, source acceptance, public contract and F5 cutover: unchanged

## Constructed and verified

Two test modules call the existing `InferenceSession`; neither contains a
replacement constraint solver. The only production-file edit is four lines
registering these modules inside `#[cfg(test)]`, additionally gated by
`shadow-f5`.

`complete_bound_constraints.rs` implements the finite ROW/PATH adapter from
the [complete bound theorem](../theory/2026-10-10-simple-sub-complete-bound-accumulation.md).
An injective map sends synthetic nominal endpoint keys to distinct real rows
at one level. Each key retains its family/scope, reference and role. Every
original edge occurrence and its unsolved proof-slot index remain in insertion
order, including duplicates suppressed by the core's pair memo. A finite BFS
reads the core's actual `direct_upper_rows` and returns a recipe indexed by
original occurrences. It handles cycles and reflexivity without identifying
nodes. `NoPath` excludes only the theorem's Refl/Original/Compose proof grammar.
It does not decide semantic inclusion, constraint satisfiability or the
inhabitance of an original proof slot.

The adapter retains an immutable `Arc<R>` without requiring `R: Clone` or
inspecting `R` to drive any operation. The fixture's ordered provider/world/
suffix tokens discriminate accidental mutation or replacement. They are
synthetic data, not authentic source declarations, full dependent residual
schemas or complete Call certificates. The mathematical residual preservation
theorem is separate from these finite identity observations.

`deferred_call_constraints.rs` verifies the existing scalar Function path:

- Install two demands on one unresolved formal before any Function lower is
  present. Later insert a provider lower. Actual worklist replay creates all
  four argument/effect/result constraints with the correct variances.
- Insert later value and effect bounds and observe propagation through both
  uses of the shared formal. Duplicate submission does not replay a second
  physical pair or erase the retained original occurrence.
- Produce real shape-incompatibility diagnostics by adding an integer lower
  to a Function demand, and by adding a late conflicting Function result.
  Successful collection and initial diagnostic absence do not imply a
  satisfiable whole graph.
- Exercise current flexible-row aging across levels while symbolic effects
  remain unbounded. This is not a proof of polarity-copy extrusion,
  existential guard semantics, protection or complete lifecycle preservation.
- Read actual opt-in HIR for `my invoke f = f 1` and
  `my relay g = g (g 7)`. A syntax-directed walker allocates shared resolved
  formal rows and per-call result/effect rows, then accumulates all call
  plans before the first solver operation. The assertions compare stored
  call/callee/argument occurrences with the actual HIR children. For the
  nested program, the outer demand's argument is exactly the inner call's
  positive result row.

The HIR walker treats the outer Lambda as a body-port traversal. It does not
construct the enclosing Lambda's complete Function Result and is not an
elaborator for arbitrary Lambda-valued arguments or callees. Its documentary
`include_str!` sources retain provenance only. They are not elaborated schemas,
checking witnesses or licenses. Its effect tests cover symbolic row adjacency,
Bottom propagation and absence of an Empty upper, not nonempty effect labels,
handler protection or full source evaluation dependencies. HIR pending errors
remain; the tests do not create a `SolvedModule` or report source acceptance.

## Independent review and repair

The compiler referee and specification auditor independently read both frozen
modules, the exact module hookup, their actual core dependencies and governing
contracts. They received no other review or producer defense. Both reported
no BLOCKING or major finding, and the same minor coverage gap: two correct
call plans could pass the assertions even if the outer argument were changed
from the inner result to an integer leaf.

After both reviews completed, the primary added the exact nested endpoint
assertion and a separate HIR traversal comparing original child occurrence
identities. The pre-write specification review explicitly authorized these
focused assertions. No implementation behavior, diagnostic expectation or
semantic test name changed. Primary diff inspection and the affected test
filter closed this minor-only repair; no fresh independent delta review is
claimed.

Both reviewers also checked the availability boundary. Only the cross-family
guard is asserted atomic: it rejects before endpoint allocation, original-edge
retention or core mutation. An allocation/availability failure elsewhere can
leave a partially built private session; the adapter does not certify retry
after that failure. Successful finite fixtures unwrap those operations. Its
diagnostic occurrence allocator is bounded by checked `u8` conversion. This is
a research implementation of the theorem within that physical envelope, not
an unbounded production API or atomic publication mechanism.

Frozen hashes reviewed by both agents:

- Complete-bound module:
  `d53bd6ff1c4d30300d18201b3b3155210b8b5bc3a15944dba52ba3c56885bbfb`.
- Deferred-call module before the minor assertion repair:
  `08e74d24f9e82096aa53ffb4f34f39aa3e4bed2ada6407874f7f4d996d82a25d`.

Final deferred-call module SHA-256:
`ff3a879f375763f6310b0a7d1e7509ae9e66386d42fd39cc18beb5adddca6327`.
The complete-bound module is unchanged from its reviewed hash.

## Verification

The execution environment initially lacked Rust. The primary downloaded the
official rustup initializer, verified its published SHA-256, and installed a
scratch-local minimal toolchain. These artifacts and build outputs are not
repository changes. Compiler: `rustc 1.99.0 (b940084d7 2026-09-28)`.

All Cargo commands used one build job, one test thread, a separate scratch
target directory, disabled debug information, and a 600-second timeout.
Only one heavy verification process ran at a time. No benchmark, peak-memory
measurement or full workspace suite was run.

Commands below used that toolchain and target with `CARGO_BUILD_JOBS=1`,
`CARGO_PROFILE_DEV_DEBUG=0` and `CARGO_PROFILE_TEST_DEBUG=0`:

```text
cargo test -p yu-solver --features shadow-f5 --lib complete_bound_constraints -- --test-threads=1
cargo test -p yu-solver --features shadow-f5 --lib deferred_call_constraints -- --test-threads=1
cargo check -p yu-solver
rustfmt --edition 2024 --check crates/yu-solver/src/tests/complete_bound_constraints.rs crates/yu-solver/src/tests/deferred_call_constraints.rs
git diff --check
```

Results: **2 complete-bound tests and 5 deferred-call tests passed**, no failed
tests. The ordinary owning package check and targeted formatting check passed.
The first compile attempt exposed a mechanical return-type mismatch in the
adapter: `constrain_live_value` returns a transition count, while `submit`
returns unit. Mapping a successful count to `()` repaired that type mismatch
before the frozen code review. No test expectation was changed to match output.

During integration, remote advanced through the independently reviewed opt-in
multi-parameter HIR change `fc08484` and merge `90629b2`. The primary inspected
the complete incoming diff and fast-forwarded without discarding local work.
It changes the HIR constructor used by the source fixture but not the complete
bound allocation, replay, Function, effect or extrusion branches. The five
deferred-call tests were rerun on this integrated dependency snapshot and all
passed. The ordinary package check also ran on that snapshot. The complete-
bound tests do not depend on the changed multi-parameter/application owner;
their successful run at `5c8efdc` remains the recorded execution evidence.

Rust 1.99 emitted two deprecation warnings in existing brand allocators:
`yu-types::ClosedTypeFinalizationSession::try_new` and
`yu-solver::term::TermBuilder::new`
use `Atomic::fetch_update`. Neither warning originates in these tests.
Their owning compatibility decision is separate from this inference result;
this checkpoint does not silently raise the required Rust version or change
atomic allocation behavior.

## Exact effect on the inference task

The bound theorem's actual-core adapter and the scalar deferred-call spine now
have executed, independently reviewed implementations in a research-only
envelope. Unknown formals, delayed lower bounds, sharing and local path-proof
construction do not require a successful Call or a concrete provider during
generation. No new registry adoption prerequisite is introduced.

This component does not prove that a scalar Function comparison is equivalent
to the complete original checking relation. WholeArg, original typed Call
membership/C0, all production alternatives, same-provider admission and
dependent effect/guarantee consumers are not discharged by pointer retention
or scalar propagation. Complete Generalize, public export and fresh ordinary
use are not exercised here. `JOINT_DEC` remains OPEN-PROOF; no canonical DAG
status changes. The separate theorem and code checkpoints preserve completed
work while those full-source responsibilities are pursued.
