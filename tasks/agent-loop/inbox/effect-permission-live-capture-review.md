# Independent review — EFFECT-PERMISSION-LIVE-CAPTURE-20261028/r1

Reviewer: `/root/formal_permission_live_capture_review` (`compiler_referee`),
fresh and independent from both producer lanes. Read-only review of the frozen
Lean/Rust bytes and retained execution receipts. No Lean, Cargo, tests, edits,
Git operations, descendants, or background processes were used. Writes ceased.

## Disposition

Accept the Lean module as conditional research mathematics. The Rust trace has
a **major fixture defect** and does not establish constructor-to-capture
correspondence. All original parent and production gates remain OPEN.

## Findings

### MAJOR — capture uses the wrong row coordinate

`candidate_effect.rs:3630` passes `parameter as u32` to
`capture_candidate_graph`. Construction links the annotated parameter at
`parameter_live_base + parameter` (`:1661`); a neighboring capture fixture uses
that offset at `:3643–3665`, and `lib.rs:10077` initializes the base from the
value-component count. The trace therefore captures `ValueRow(0)` without
establishing that it is the annotated parameter. Its one-node graph and empty
`negative_formal_roots` cannot diagnose failed formal-root arrival along the
intended route. Assertions at `:3632–3633` accept any origin event plus any
graph return, so the test passes while capturing an unrelated row. This misses
the contract requirement to retain endpoint identity and connect construction
to capture.

Closure requires correcting and authenticating parameter-row mapping, asserting
that the captured root represents that row, and obtaining a newly authorized
bounded trace. Preserve the successful run as evidence of the submitted
fixture only. The amended handoff's non-arrival claim is not a meaningful source
locator until this coordinate error is resolved.

### BLOCKING for source/native or parent promotion — auxiliary relations

`FormalPermissionLiveCapture.lean:30–38` models symbolic construction without
advancing the allocation counter and delegates positive explicit ports without
advancing it. Native `candidate_formal_effect_variable`
(`candidate_effect.rs:1365–1383`) allocates on a memo miss, and
`candidate_signature_effect` (`:2190` onward) also allocates. The first
unsupported constructor recurrence is therefore the symbolic memo miss,
followed by signature allocation. `Construction:65–85` derives `Origin` for
represented histories, but does not derive that history from every successful
Rust call. `Transition.discover:253–256` accepts arbitrary endpoint requests;
`Capture:145–148` stores no concrete graph nodes, row/cursor state, or evidence.

Closure requires successful-call realization with scoped memo/view/allocation
state, authenticated metadata decoding, then simulation of concrete node writes
and actual row/bound/context request generation. The proof handoff correctly
retains these seams; no defect was found in the stated conditional theorems.

### BLOCKING for a returned permission port — numbering does not prove presence

`constructed_export_renamed:347–361` holds for arbitrary capture state and
canonical function. With an empty capture, `idxOf` can return numeric zero even
when no port is present. `publish:323–326` correctly requires exact negative
composite presence, but nothing connects that condition to the fixture or
proves universal arrival. Actual export also requires `negative_formal_roots`
and a successful structural walk to an effect row (`shadow_apply.rs:2694–2702`).

Closure requires canonical transport, root/endpoint membership, stored-node and
walk correspondence, and export success from the same retained witnesses.
Neither module nor handoff claims these gates closed.

### MINOR — recorder eagerly formats an event while disabled

`candidate_scheme.rs:1715–1716` eagerly formats `canonical_identity` on every
test-build `intern`, before checking whether tracing is enabled. Both Rust
handoffs claim strings are built only when enabled. This adds allocation/time
overhead to other candidate tests, though it changes no production solver
decision. Move formatting inside the enabled recorder closure, or correct the
dormancy claim and account for the test-build overhead. Other inspected
instrumentation is `#[cfg(test)]`; the private `Debug` derive introduces no
solver transition.

## Evidence authenticated

- All eight assigned contract, amendment, module, source and handoff hashes
  matched. Prior catalog module, `shadow_apply.rs`, and `yu-solver/Cargo.toml`
  hashes also matched.
- Inspected retained Lean `heavy.log` and `heavy.time`; scratch source matched
  the frozen repository module. All 25 authored theorem names have complete
  printed types and transitive axiom reports. `port_emission` and
  `shifted_tuple_origin`: `propext`; both construction-origin theorems:
  `propext, Quot.sound`; the remaining 21:
  `propext, Classical.choice, Quot.sound`. No delivered `sorry`, project axiom,
  or checker bypass was found in the two-module source cone.
- Lean 4.35.0 check: exit 0, 5.21 seconds, 976,396 KiB RSS. No default/root
  integration is established.
- Rust receipts distinguish the initial compile failure (exit 101, zero tests,
  37.32 seconds, 1,159,420 KiB) from the amended run (exit 0, one test,
  41.49 seconds, 1,656,320 KiB). Final source hashes include the `Debug` and
  wrapper corrections. The amended trace matches the observer locations but
  has the wrong-row defect above.
- The fixture bypasses source preflight and never calls the permission export
  helper. No source acceptance, universal live simulation, subtraction/hygiene,
  Simple-sub A/B, whole soundness, principality, progress, termination, or
  production closure follows.

## Hashes checked

| Artifact | SHA-256 |
|---|---|
| Base contract | `08224918615443e37273da946a13c1437a1c0ec7afa37314225d56f8aa543f2b` |
| Amendment 01 | `7187d34d7a0fdf5dba92eccadde029da443d7666f9616e027145dd10054b373a` |
| Lean module | `0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e` |
| Proof handoff | `6f7b51ae52ed23dc8afbe35e856d054e005965e499554b745edfcc4cd903ee56` |
| `candidate_effect.rs` | `f0b08ea8cee26e372b2a2e0b8076b82e4e6e29fa73618fe9cddfe360df117b8f` |
| `candidate_scheme.rs` | `33c066da527c3251d106aa9ca9a4f77d3f54844478ea2f6f2258933a5eb30852` |
| Initial Rust handoff | `3c77c6a39fb100c1cdc4795ba6c89b7ac457109dd620a573c68e43999bf1b44f` |
| Amendment Rust handoff | `487170dde32a33cb9466d3d2248d9ed3b4730f23707b70a762927dc30d503023` |

The original constructor/live-capture/source/native and production obligations
remain OPEN.
