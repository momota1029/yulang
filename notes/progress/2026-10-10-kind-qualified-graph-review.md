# Kind-qualified scalar graph construction: independent review and execution

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Status: reviewed structural research result and bounded test-only implementation
Mode: M3, two independent reviewers per frozen proof/implementation component
Authority: current deferred Simple-sub correction; no source-rule or production adoption

## Completed result and scope

The [construction](../theory/2026-10-10-simple-sub-kind-qualified-graph-construction.md)
derives `RawGraph(S)` from the actual live tables. RAW-EXTRACT retains every
value/effect row, all four ordered list families, levels/metadata/flags, every
admitted typed-pair key, actual components/declared roots and the complete
four-child term closure. RAW-FRESH constructs one kind-qualified row map across
both polarities and an independent nominal term-record map, with an effective
inverse. This is a complete snapshot of its explicitly defined active scalar
projection, not a copy of the entire operational session.

REALIZE proves well-sorted realization through actual constructors while keeping
immutable nominal records separate from interning. SCOPE-RECORDS preserves the
original telescope/reference representation and decoder; it does not establish
semantic naturality of arbitrary predicates under fresh nominal keys. PARTIAL
constructs a finite reverse-incidence closure while retaining its complement.
These optional mathematical extensions are not implemented by the new helper.

`crates/yu-solver/src/tests/kind_qualified_graph.rs` implements the RAW-EXTRACT /
RAW-FRESH core and four discriminating fixtures. Its only existing-file hookup
is a `shadow-f5`-gated child test module in `lib.rs`; production routing and public
APIs are unchanged.

The executed F5 witness reaches an actual unbounded negative effect port under
an unknown formal's Function demand. It checks both the causal `invalid_effects`
flag and the boxed builder's `IdentityExhausted` result. A separate actual
four-port Function comparison derives the effect edge `q <= e` and integer
result lower. This is an actual scalar owner limitation, not an original
complete-source Call rejection or a proof of unsatisfiability.

## Independent mathematical and specification review

The complete proof was frozen at SHA-256
`777f67972fa7724da93cfa54e0b8bb4fdbae9be8612a440ebd1d79087421ffd8`.

- The independent mathematical referee read the full proof and actual owners,
  checked finite extraction, every retained field, nominal inverse, one map
  across opposite ports, residual decoder scope and the actual F5 guard route.
  Verdict: PASS, no BLOCKING/major/minor finding.
- The independent specification auditor checked the exact source/production
  boundary, full four-port preservation, original dependency scope, no source
  eligibility premise, and the distinction between a structural theorem and
  Source Generalize/Call membership. Verdict: PASS, no finding.

After both reviews, the primary updated only status, review/execution links and
the context distinguishing the pinned legacy collector from the later graph
source-effect implementation at `280d399e`. No theorem or constructor changed.
The final theorem SHA-256 is
`c1aedc8d21eb9c7014c86922542767c43b5eb95479ab76153fa3d1778a0454bd`.

## Independent implementation review and repair

The complete 910-line helper was frozen at SHA-256
`eadadadb24b4857a2e89f94e8cf2f48116f3f1cd556d7b57825b10648c74147b`.

- Mathematical/compiler referee: scoped PASS, no findings. Reviewed all fields,
  actual Component-position translation, list multiplicity, finite structural
  cycle validation, original opaque Term identity, inverse dictionaries,
  typed-pair labels, causal F5 failure and actual effect replay. No claim of
  runtime session restoration or full source semantics was accepted.
- Specification auditor: scoped PASS, no BLOCKING/major finding. One minor
  evidence-labeling issue: module comments should explicitly distinguish the
  executed RAW core from optional construction recipes that are not exercised.

The primary waited for both reviews, accepted the minor finding, and added a
comment naming the omitted runtime realization, partial reverse closure,
attached residual/scope fixture, nonempty parameter recipe and distinct
committed equal-shape term fixtures. This changes no assertion or behavior.
The final helper SHA-256 is
`776e934a7852a904a7c90b7f5ea58a44f75f3ce6eee0956f73c1711f291b02f0`.

The helper explicitly panics on malformed research input; it is not a fallible
public extraction API. Distinct frame labels are supplied research identities,
not a certified global allocator. Equal-shape nominal records are preserved by
the algorithm but not separately executed as a committed-term fixture.

## Executed verification

The primary is the sole Cargo owner. Rust 1.99.0 (`b940084d7 2026-09-28`), one
Cargo job, one test thread, debug info disabled, 600-second timeout. No workspace
formatter, broad workspace suite, benchmark or numeric resource experiment ran.

```text
cargo test -p yu-solver --features shadow-f5 --lib kind_qualified_graph -- --test-threads=1
```

PASS: 4 tests, 0 failed, 463 filtered, 0.01 seconds of test execution. The owning
compile completed without warnings. The four cases exercise:

1. The actual private F5 failure at an unbounded negative effect port.
2. Actual four-port provider replay and its directed effect edge/result lower.
3. Complete active extraction including a disconnected effect row, a row-free
   admitted pair and an actual Component root.
4. A real effect cycle, equal V/E ordinals, one effect row in opposite ports,
   a shared nested Function, repeated roots, two fresh frames and an alias,
   with full decoded-record equality.

A subsequent compile under `shadow-apply-candidate` reached a linker error
(undefined hidden internal Rust symbols); no tests ran in that attempt. The
same feature compile with a new target directory and incremental compilation
disabled also reached undefined hidden symbols. This rules out the original
incremental cache as a sufficient explanation, but does not identify the cause.
These failures are not counted as passing candidate execution or attributed to
a source semantics failure.

With `CARGO_INCREMENTAL=0` and `CARGO_PROFILE_TEST_CODEGEN_UNITS=1` in the separate
target directory, the same command under `--features shadow-apply-candidate`
compiled without warnings and PASSed: 4 tests, 0 failed, 472 filtered, 0.01
seconds of test execution (25.73 seconds compile). This isolates a sufficient
build configuration for the owned checks; it does not identify the root cause
of the earlier multi-codegen-unit link failures. No repository build policy,
manifest or toolchain requirement was changed. These are the same four raw-graph
tests under the new feature combination, not the new source pipeline fixtures.

## Integration boundary

The pinned legacy F5/core owners were reviewed independently. Concurrent remote
`21504b7` adds a distinct graph candidate exporter/route; `280d399e` adds actual
Apply/Group symbolic effect flow. Those changes are preserved and are separate
correspondence targets. They do not turn the raw helper into a source Call
emitter, and do not invalidate its legacy F5 witness.

Canonical proof-obligation DAG statuses are unchanged. No complete CallMem/C0,
JOINT_DEC, Source Generalize, public scheme, source eligibility, lawful complete
fresh-use or F5 production gate is closed here. There is no new requirement to
solve a formal, choose a provider, or prove satisfiability during generation.

Shared `tasks/current.md` and `notes/design/INDEX.md` were synchronized after the
reviewed research checkpoint by the primary. No pending question
bundle, production implementation, manifest, lockfile or semantic expectation
is included in this result.
