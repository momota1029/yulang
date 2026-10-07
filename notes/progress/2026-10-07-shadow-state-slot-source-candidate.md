# Shadow State declaration candidate: static source identity premise

Date: 2026-10-07
Status: bounded default-off structural slice; compiler-referee reviewed, pass
Baseline: `21aceb0e4eacb0c09754a26f577f89d4180614fb`
Production inference authority: none

## Scope

The user authorized a shadow/experimental lane for settled identity and
evidence plumbing while proof work continues. Architecture §6.9 decides that
the originating declaration supplies static `StateSlotId` identity and that
this identity is distinct from runtime address, cell, activation and branch
identity. State read, write, capture, escape, effect and restart judgments
remain open. This slice retains only an explicitly caller-selected declaration
candidate and an optional list of caller-supplied source positions. It does
not create an actual `StateSlotId` or classify occurrences.

`ShadowArtifact::pending_state_slot_source_input` checks that the supplied
declaration belongs to the same artifact, is an `IdentifierPattern`, and
contains a direct sigil token. Supplied occurrence positions must belong to
the same artifact, be `IdentifierExpression` nodes, and contain a direct
sigil token. These shape and ownership checks add no lexical resolution or
read/write/handle judgment. Caller-provided association and occurrence roles
remain premises.

## Current source boundary

The focused source is:

```text
my $buffer = 0; my $buffer = 1; my backing = 1; my read = backing
```

Two same-spelling declaration positions produce distinct pending candidate
IDs, so the retained identity is tied to declaration origin rather than the
written name. The first declaration is structurally retained as a pending
candidate. The current recovery-free expression parser does not expose the
State `$` read or `&` write forms as `IdentifierExpression` nodes; positive
occurrence association is therefore not exercised here and remains pending.
A plain identifier use and a sigiled declaration supplied as an occurrence
both fail shape validation. Foreign-artifact positions are rejected.

Ordinary `lower_module` still reports `UnsupportedTarget` for the sigiled
declaration. The shadow skeleton remains unresolved. This slice changes no
production HIR acceptance, constraints, State effect representation, runtime
behavior, soundness premise or inference path. In particular it proves no
write/restart/read law and no multi-activation or multi-shot property.

## Review and checks

Independent compiler-referee review passed after strengthening the test to
isolate artifact ownership, source-node kind and sigil-shape checks, and to
assert the exact ordinary `UnsupportedTarget` refusal. A second delta review
confirmed the same-spelling declaration discriminator remains structural-only.

Focused verification:

```text
RUSTC_WRAPPER= cargo test -p yu-hir --features shadow --test shadow_state_slot_identity -j 2 -- --test-threads=1
```

Result: 1 test passed. Targeted Rust formatting check and
`git diff --check` passed. No broad test suite or performance sample was run.

## Next gate

Keep `STATE-ID`, `STATE-RW` and `STATE-RESUME` open. Extend this carrier only
when recovery-free source identities for the relevant occurrences exist and
the corresponding ownership/resolution premises are specified. Do not infer
them from sigils or from Frozen Oracle behavior. Production acceptance remains
behind the existing proof and conformance gates.

## Reviewed follow-on: declaration-to-initializer carrier

Baseline: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`.

The default-off shadow carrier now also exposes
`ShadowArtifact::pending_state_slot_declaration(BindingStatement)`. It derives
the candidate from the exact direct sigiled `IdentifierPattern`, retains only
the target Pattern's optional direct `PatternTypeAnnotation`, and returns the
existing `BindingBody` wrapper as an opaque initializer position. The
initializer is not lowered or typed here. Unsupported targets, wrong/foreign
identities, and ambiguous direct layouts are rejected. The annotated
same-spelling fixture is recovery-free under the existing parser and
`ShadowArtifact::from_parsed` admission guard; no parser or ordinary-HIR
behavior changed.

The focused test verifies the statement/pattern/header/annotation/body parent
relations and distinct identities for equal-spelling declarations, plus
foreign identity, wrong node, plain/destructuring/extra target shapes,
malformed annotation rejection, and an unannotated candidate. The original
`UnsupportedTarget` assertion remains. No occurrence identity or role,
resolved `StateSlotId`, read/write/handle judgment, effect, transition,
runtime activation, solver fact, or inference acceptance is produced.

Independent compiler-referee review: PASS, no blocking/major/minor findings.
Focused verification, rerun at integration baseline:

```text
RUSTC_WRAPPER= cargo test -p yu-hir --features shadow --test shadow_state_slot_identity -j 2 -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-hir/src/shadow.rs crates/yu-hir/tests/shadow_state_slot_identity.rs
git diff --check -- crates/yu-hir/src/shadow.rs crates/yu-hir/tests/shadow_state_slot_identity.rs
```

Result: all 3 tests passed; formatting and whitespace checks passed. No broad
suite or performance sample was run. `STATE-ID`, `STATE-RW`, and
`STATE-RESUME` remain open, along with production cutover gates.
