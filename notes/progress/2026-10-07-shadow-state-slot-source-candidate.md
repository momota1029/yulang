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

The focused source is `my $buffer = 0; my backing = 1; my read = backing`.
The first declaration is structurally retained as a pending candidate. The
current recovery-free expression parser does not expose the State `$` read or
`&` write forms as `IdentifierExpression` nodes; positive occurrence
association is therefore not exercised here and remains pending. A plain
identifier use and a sigiled declaration supplied as an occurrence both fail
shape validation. Foreign-artifact positions are rejected.

Ordinary `lower_module` still reports `UnsupportedTarget` for the sigiled
declaration. The shadow skeleton remains unresolved. This slice changes no
production HIR acceptance, constraints, State effect representation, runtime
behavior, soundness premise or inference path. In particular it proves no
write/restart/read law and no multi-activation or multi-shot property.

## Review and checks

Independent compiler-referee review passed after strengthening the test to
isolate artifact ownership, source-node kind and sigil-shape checks, and to
assert the exact ordinary `UnsupportedTarget` refusal.

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
