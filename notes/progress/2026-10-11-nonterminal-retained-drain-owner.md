# Retained nonterminal typed-drain owner

## Gate and authority

This bounded M2 implementation closes the private retained-drain owner seam
under the suspension contract §§3 and 6. It does not enable source-level
suspension, expose `CandidateRun::Suspended`, or certify the contract's §7
source witness. The acknowledgement-prefix derivation and owner-composition
proof remain conditional parent-proof inputs until their source correspondence
is fully established.

## Implementation

The typed drain now has a shared start/step path. Existing candidate production
routes loop synchronously until a `Complete` receipt. A closed `cfg(test)` owner
fixture commits a nonterminal step and resumes the exact retained topmost
frame through the same step implementation.

Each nonterminal step prepares the complete outstanding replay-acknowledgement
suffix before side effects, queue pop/append, or direct Function admission and
enqueue. Terminal acknowledgements retain their prior one-at-a-time contract.
Replay transfer and child completion have distinct `Queued` and `Complete`
outcomes; restoration advances only after `Complete`.

Retained-resume rollback journals queue mutations and diagnostic-frontier
admission/clear, retaining old allocations only when growth or clear occurs.
Rollback restores queue order, frame/replay/parent state and diagnostic
contents without allocating. The diagnostic index is normalized in its
retained allocation after inverse admissions to remove HashMap tombstones and
restore its reported capacity. Successful resumes do not scan or copy the
whole retained workspace. Production journal accounting tracks retained
allocation bytes incrementally; the independent test census enumerates them.
Fresh synchronous routes retain their existing reusable growth-capacity
behavior.

## Evidence

The compiler-referee found no correctness issue in the frozen four-file diff.
The spec-auditor found no §3/§6 conformance issue and confirmed the existing
terminal, empty/final batch, Function-ordering and queued-versus-consumed
contracts remain intact. No expected output, fixtures, diagnostics, or test
names were changed.

Focused verification passed:

- `cargo check -p yu-solver --offline --jobs=1`
- `cargo check -p yu-solver --features shadow-apply-candidate --offline --jobs=1`
- Feature-enabled `retained_` owner tests (22 matching tests)
- `direct_function_steps_prepare_full_retained_prefix_before_admission_or_enqueue`
- `typed_drain_terminal_` (3 tests)
- `owned_function_dispatch_`, `parsed_local_use_retains_`, and
  `internal_restoration_owner_steps_`

All Cargo commands used `RUSTC_WRAPPER=`, offline mode, and one build job.
No broad package suite, formatter, benchmark, or timing sample ran. The
feature-enabled check emits the three already-recorded `dead_code` warnings
for retained-input certificate payloads; their production consumer remains a
separate open gate.

## Remaining gates

The retained driver is private test scaffolding, not an authentic source
continuation. Production suspension, all continuation classes, lifecycle
invalidation and ordered observation withdrawal/recomputation, external
incidence deferral, resumable SCC publication, complete Simple-sub inference,
soundness/principality, and F5 cutover remain open. The parent constructive
proof remains OPEN pending a proof-to-source bridge for actual source paths;
the implementation and focused regressions do not prove that parent theorem.
