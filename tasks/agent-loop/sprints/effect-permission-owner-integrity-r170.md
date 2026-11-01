# Sprint R170 — verify R169 and restore permission-owner joins

Status: **COMPLETE** under the continuing Yulang Rust/Lean soundness goal.
Branch / baseline: `yulang3` / `a811c9d25` (pushed).
Primary: Luna. Original parent remains
`YulangClosure.SourceProblem.InferenceSoundness` in `Contracts.lean:127`.
R169 is frozen as `CHECK_CAP_EXHAUSTED`; its final Lean source is unchecked.

## Fixed outcomes

1. Verify the frozen R169 module without creating a target, environment, cache,
   scratch source, or persistent audit file. The Lean lane receives the R169
   module as a read-only input and writes a verification receipt only. It must
   first authenticate imported `.olean` inputs against the existing project
   source/toolchain. If it cannot do that in place, stop before execution.
2. Restore authentic same-session and registration identity joins in the
   existing dirty Rust evidence adapter. Do not connect a Catch consumer or
   change inference behavior. Preserve the separately reviewed and pushed
   duplicate-guard deletion in `candidate_receiver.rs`.

Success evidence: one no-output Lean `--stdin` check contains the frozen module
source and all 18 complete theorem type / transitive axiom commands; an
independent proof review checks the frozen receipt and unchanged source hash.
The Rust repair retains route, term arena, effect state, registrations,
LocalSource recipe, permission and provider-member evidence under one
`InferenceSession` / exact registration label; independent compiler review
confirms both selected diffs. No Cargo, Rust build or tests are authorized by
this contract.

## Frozen inputs and exact outputs

- R169 module SHA-256:
  `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4`.
- R169 handoff SHA-256:
  `b08ac4ac3a566802084dba43cb72dfebed3ca72eac2f3e03ad7943692d1fdc61`.
- R169 outcome:
  `tasks/agent-loop/history/effect-permission-formal-prestate-r169-outcome.md`.
- Lean verification receipt (new):
  `tasks/agent-loop/inbox/effect-permission-formal-prestate-r170-verification.md`.
- Rust writer leases, baseline dirty-byte hashes:
  - `crates/yu-solver/src/candidate_scheme.rs` —
    `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470`.
  - `crates/yu-solver/src/candidate_receiver.rs` —
    `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`.
- Rust handoff (new):
  `tasks/agent-loop/inbox/effect-permission-owner-integrity-r170-rust.md`.
- Independent compiler review receipt (new):
  `tasks/agent-loop/history/effect-permission-owner-integrity-r170-rust-review.md`.

The Rust lane may edit only the two assigned source files and its handoff. It
must not overwrite either whole dirty file or unrelated hunks. Preserve all
existing unassigned changes and the pushed R170-independent safe hunk.

## Rust construction requirements

In `candidate_scheme.rs`, restore a session-owned permission binding or an
equivalently sealed same-session projection. Route, term store, permission
state, formal registrations and LocalSource recipe must not be independently
mixable. Rejoin the actual unique registration, Lambda occurrence/source
parameter, raw Function argument row and captured FreshUse representative.
The current `definition_use` / `context_use` copies from one route are not
independent authentication.

In `candidate_receiver.rs`, choose retained permissions by their explicit
`registration` label and reject missing or duplicate matches. Never index the
sparse retained permission vector with a formal-registration ordinal. Restore
the selected provider operation/family, permission-member, Catch arm and
source-owner joins removed by the dirty diff; keep the one independently
reviewed redundant-guard deletion from commit `a811c9d25` intact.

The native consumer remains evidence-only. No provider suppression, Catch
subtraction, production promotion, semantic change or inference-state
mutation is authorized.

## Lean verification method and resource limits

Proof lane: registered `lean_prover`, at most 900 seconds, one cache owner.
Use only the existing pinned Lean 4.35.0 and current `.lake`. Do not invoke
Lake build, the helper that materializes modules, Cargo, test targets, or any
command that creates generated project outputs. The intended check streams the
existing R169 source and all 18 `#check` / `#print axioms` commands into
`lake env lean -j1 -M1024 --stdin`, with stdout/stderr recorded in the leased
handoff. First verify the exact imports already exist and their source/toolchain
hashes match the frozen R169 inputs. The stream itself must create no file.
One full audit invocation plus at most one focused repair-confirmation run;
repair itself is prohibited in this read-only lane. If the frozen source fails,
record the exact diagnostics and stop for a later versioned sprint. No third
attempt.

Rust lane: registered `implementer`, Luna/high, at most 1200 seconds, exact two
source paths and the Rust handoff. No Cargo/build/test, new environment,
target, cache or persistent scratch.

Fresh independent reviews: one read-only proof reviewer and one read-only
compiler referee, 450 seconds each, against frozen hashes. No self-review.
Astra 0; total ceiling 3000 seconds. Checks, CPU and memory stay within the
existing project limits and the 1 GiB Lean cap. `.lake` remains 98 MiB unless
an exact before/after inventory proves otherwise; no growth is authorized.

## Stop conditions and limits

Stop verification if imported artifacts are absent/stale or require any build,
if the streamed audit produces a file, if the full source fails, or if a third
Lean run would be needed. Stop Rust work on source mismatch, writer conflict,
need for whole-file replacement, or any request to change semantics. Keep R169
unaccepted unless every declaration type and full axiom list is captured and
freshly reviewed. Even a passing R169 bridge does not establish actual native
event execution, selected source/operation/endpoint authentication, R45/R54,
Catch consumption, complete effects, principality, termination or the original
shared-witness A/B theorem.

Only Luna stages explicit R170 paths, reviews the full outbound range and
pushes a coherent reviewed checkpoint. Preserve all dirty, untracked, unknown,
quarantined and pending-question paths outside these exact leases.
