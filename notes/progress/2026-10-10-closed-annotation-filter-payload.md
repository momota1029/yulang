# Closed annotation filter payload checkpoint

Status: partial implementation checkpoint for the Authoritative contextual
attachment gate; no source-admission or public-behavior expansion
Baseline: `85b365e1b362beb303d6b47897a690df2a3b6d40`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–4, 6; existing closed covariant annotation behavior

## Change

The private candidate now represents an already-supported closed covariant
annotation allowance with an immutable, source-owned zero-word `LocalWeight`.
It contains the resolved allowed members and the source boundary, owner, and
position. Both operation words have zero length. Only closed annotation views
construct payloads; mixed-tail and operation views continue through their
existing paths.

The task executes the payload through `PrefixLeft` before endpoint memoization
and self-omission. The negative-wrapper path still installs or replays the real
Allowance on the canonical receiving row before discharge, preserving current
and future lower checks and diagnostic derivations. Fresh copied views receive
independent payload identities; the existing per-use view map preserves sharing
within one use. Payload capacity and allowed-member capacity are metered and
rolled back with contextual state.

This substitutes the representation of the existing zero-word closed filter.
It does not introduce nonempty operation evaluation, right POP semantics,
concrete contravariant formal admission, recursive-context certification, or
any new source restriction. No callback result is inferred.

## Review and verification

Selected mode: M3, because this slice moves effect-filter authority through the
context carrier, bound registration, copying, and rollback. The frozen delta
received three independent reviews:

- compiler-referee: PASS, no semantic finding;
- spec-auditor: PASS, no conformance finding;
- performance-auditor: PASS, no accounting or complexity blocker.

The performance review estimates O(k) additional member-handle construction
and retained storage per closed view with k allowed members. Fresh copied views
clone the members into both their View and LocalWeight, a constant-factor
increase. Existing per-use remapping bounds duplicate copies within a use.
Static analysis resolved the gate's complexity and accounting questions; no
timing decision depended on measurement, so benchmark count was zero.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests --offline --jobs=1 -- --test-threads=1` — 23 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests --offline --jobs=1 -- --test-threads=1` — 27 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests --offline --jobs=1 -- --test-threads=1` — 5 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation --offline --jobs=1 -- --test-threads=1` — 17 passed.
- `git diff --check` — passed.

No broad suite or benchmark ran. The ordinary-HIR successor-carrier question
bundle remains untouched and uncommitted; its receipt rejects integration due
the exact draft-content mismatch.

## Remaining gate

Next, construct and execute approved nonempty directed transforms through exact
memoization, Function ports, ordered replay, extrusion, capture/freshening and
intrusion. Then implement exact two-cycle certificate dependency tracking,
late-edge invalidation, result withdrawal, rollback, and supported retry before
admitting recursive contexts. General mixed-component termination, complete
Call, full effect hygiene, soundness/principality, ordinary/default/public
inference, and F5 retirement remain open.
