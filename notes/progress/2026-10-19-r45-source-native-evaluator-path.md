# R45 source, native and evaluator path map

Status: read-only implementation evidence; `NO_SAFE_CODE_SLICE`
Sprint: `application-output-derivation-20261019-r45`, contract SHA-256
`e8e6460eb19500383d71cc6b6b217f294ae8acbf3bfedb48b6beab5ff8457c77`
Parent: unchanged inference/evaluator theorem and Simple-sub A/B, OPEN 0 → 0
Owner: Luna primary `/root`

## Inspected safe owner records

I read these pinned, committed design/gate records only; I did not inspect the
quarantined Rust files or R35–R41 untracked artifacts.

1. **R42 Apply-to-Result consumer map**, `notes/progress/2026-10-18-call-output-implementation-gate-r42.md`,
   SHA-256 `855c07f2a6de1e156209f91c7c9f9ea2169369feb0381edb63ddeceb013c1758`.
   Its §“Required certificate and path” names the recorded flow
   `ApplySourceInput → native admission → typed FunctionField::Result child
   → Preserve/Dependency::FunctionPort → Context/Dispatch`, and distinguishes
   `NativeInterface.result`, `.demand`, effects, and actual returned provider.
   This is an owner map from the earlier frozen evidence; it is not a fresh
   byte audit of the current implementation.
2. **Typed-computation Application/Call/evaluator owners**,
   `notes/design/2026-10-02-typed-computation-core-elaboration.md`, SHA-256
   `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`.
   §§2–4 define derivation-indexed `Comp(E,A)`, `Result`/`eliminate_p`,
   `ExecuteCallable`, and finite simulation under a supplied source derivation.
   §§6–7 provide scoped synthesis/checking constructions but explicitly retain
   raw-source role and inference premises outside that core.
3. **Source computation/value role owner records**,
   `notes/design/2026-10-02-source-computation-role-elaboration.md`, SHA-256
   `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb`.
   §§3, 10 and 12 separate inert introduction, selected computation
   elimination, complete invocation and future-use simulation. They do not
   derive the target raw-source consumer judgment.

These are the safe owners actually inspected for this lane. The Rust locations
listed in R42 §“Scope, sources and receipt” are explicitly quarantined and were
not opened here. They cannot count as current code evidence or as cleared
write leases.

## Available path and missing certificate edges

The frozen docs give this intended path:

```text
source Application / typed consumer judgment
  → Apply source input and occurrence identity
  → native admission and complete Call interface
  → typed Function.Result relation / Preserve(FunctionPort)
  → Context/Dispatch consumer
  → actual Generalize/CopyScope mapping
  → one-layer designated evaluator consumer
```

The evaluator end is conditionally accounted for: with a complete typed
Application/Call derivation, the existing core executes the declared consumer
once and returns its result value without recursively forcing that value.
The evaluator corollary does not construct the source owner or any source to
native premise.

The required certificate still lacks an authoritative source producer for
`(q, owner, class/sort, sigma_A, D_q, typed inclusion)`, plus the authentic
effect origin, complete result/provider/world/future/receiver/return and
pending/W/Z interfaces, and actual copy lineage at every Generalize boundary.
The exact telescope cannot be reconstructed from a native level, endpoint,
resolved row, or all of `Gamma_q`. The R44 independent reviewers confirmed
these source premises remain open.

## Implementation decision

**`NO_SAFE_CODE_SLICE`.** Two safe design owners and the frozen native gate were
inspected, but the source owner/certificate is not Authoritative, its
source/native/copy proof is absent, and the relevant dirty Rust paths have
unknown writers. There is no exact Rust lease in R45. Editing a native field,
consumer, test or evaluator would guess the certificate's semantics and could
overlap another writer.

No test, expected output, build, Cargo command, runtime execution or Rust source
change was performed. Parent remains OPEN, 0 → 0. Reopen implementation only
after a reviewed source owner, typed source/native/copy correspondence, and
authenticated sequential leases exist.
