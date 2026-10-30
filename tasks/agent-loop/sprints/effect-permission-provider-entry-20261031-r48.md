# Sprint EFFECT-PERMISSION-PROVIDER-ENTRY / R48

Status: CANDIDATE pending exact-pin validation, Luna admission and live worker acknowledgements.
Branch: `yulang3`; baseline `5b5b288f3d66b9306675a0e25b3b084f78e681cd`.
Authority: user's ongoing Rust/Lean effect-hygiene goal; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2; `rules/goal-driven-sprints.md`.
Previous gate: R47 `CLOSED_BOUNDED_PASS`; its provider-arrival, Catch correspondence, subtraction and parent closure remain OPEN.

## Original outcome and success evidence

Build a private, read-only source/native certificate for the one actual provider endpoint that is both (a) reachable through current lower-bound edges from R47's exact Internal permission entry and (b) reachable through current lower-bound edges from the original, unfiltered Catch-input operand identified by the unique source `slot 51` fact. The terminal endpoint must be an actual `AnnotationMember` whose retained `ViewOrigin::Operation` has the exact provider occurrence and declaration from the original source operation. The certificate must use the same endpoint and same path witnesses at both joins.

Required evidence: exact current physical owner/lane/index reads and owning admission/emission at every addressed lower-bound edge; entry root from the same R45 Internal permission/R47 emission witness; Catch root from the actual unique occurrence/slot-51 source fact; terminal operation provenance from the retained native view. Ambiguous, missing, stale, reversed, foreign, or disconnected evidence returns unavailable. No equality of family, canonical row, hash, source spelling, or endpoint alone may substitute for any ownership/path premise.

Lean must define the corresponding finite checked path relation and prove that accepted certificates imply: exact R47 entry arrival, exact provider occurrence/declaration, and a common endpoint on the original Catch-input path. Compose with R45/R47 using their same witnesses. State Rust extraction completeness and concrete runtime success as separate unproved source obligations.

## Exact lanes and leases

### Rust, Luna/high, at most 1,500 seconds

Write only:
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-provider-entry-r48-rust.md`

Return a private borrowed certificate or precise unavailable reason. Do not alter routing, propagation, production consumers, permission subtraction, Catch outcomes, ordinary dispatch or source semantics. Stop if proof requires a producer or constructor change outside these paths.

### Lean, constructive, at most 1,400 seconds

Write only:
- `notes/theory/lean/YulangClosure/ProviderEntryArrivalR48.lean`
- `tasks/agent-loop/inbox/effect-permission-provider-entry-r48-proof.md`

Use the pinned Lean 4.35.0 toolchain through read-only stdin, one CPU, `-M1024`, and at most 120 seconds per invocation. No Lake, build, tests, extraction, scratch files, cache, `.olean`, target or environment. Record every declaration's full type and transitive axiom audit, failed diagnostics and invocation/resource receipts. Do not assume Rust extraction completeness or runtime success.

### Fresh independent review, at most 900 seconds

Only after both authors stop and freeze hashes, Luna assigns a reviewer with no authorship/coauthor role. Review exact path orientation and current slot reads; operation origin and occurrence/declaration; same terminal endpoint across the exact Catch slot-51 input and R47 entry; mismatched family/shared-row, foreign provider, stale slot, reversed edge and disconnected-scrutinee falsifiers; complete Lean types/axioms; and exact dirty-baseline isolation. Write only `tasks/agent-loop/inbox/effect-permission-provider-entry-r48-review.md` or return a complete frozen report for primary placement.

## Frozen dependencies to rehash before dispatch

- Baseline and upstream: `5b5b288f3d66b9306675a0e25b3b084f78e681cd`.
- R47 Rust: `candidate_context.rs` `184f09e91221f8ae0969d1dbc792b7707ef5571ff56d96e276467641215bf32e`; `candidate_receiver.rs` `1426526cad48d4bc02984e0a5967e30e50cd188cb01fbeb71bc6f15442e59448`.
- Read-only Rust owners: `candidate_effect.rs` `2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3`; `candidate_scheme.rs` `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`; `candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; `lib.rs` `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- R47 Lean `CurrentEmissionOwnershipR47.lean` `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`; R47 proof handoff `ce27378fe9dbc6c25ede25869a238bbf59af14ffe9a64202d3aeb520947a08e1`; R47 independent review `2f2fc7568b67058cd1e3aac50635206687a9c5bfcaf3a4d36065aab01287bc40`.
- R45 Lean `InternalPermissionIncidenceR45.lean` `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`; R45 Rust handoff `5ca8058e79015b4896260c19aa2b389449324e223c169419fd873177910c4341`; review `a4e40d0b5ced25574e821047727cdcba21c35bb7d6701e6641ed0869b6647c6b`.
- Prior residual model `EffectPermissionResidualR38.lean` `e5657e0b8affaaa0ffef6543c8e329957a1519a04a194392dbd245064a623642` is context only; it supplies no provider-arrival premise.
- Lean toolchain `lean-toolchain` `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; project configuration `lakefile.toml` `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`.

## Resources, limits and gates

Aggregate sprint budget: 4,800 seconds: Rust 1,500; Lean 1,400; independent review 900; primary 1,000 including at most 500 seconds closeout; Astra 0. Use the existing checkout and installed toolchain only. No new worktree/environment, scratch, build, test, Cargo, Lake, formatter, cache, target, service or nested CLI. Preserve all 32 pending entries, UNKNOWN observations and quarantined paths. Do not count already-released assignment capacity twice.

Provider operation arrival and exact Catch-input common-endpoint correspondence are the sprint's only success target. Permission consumption, residual subtraction, runtime-machine coverage, original A/B claims, whole-language soundness and production promotion remain OPEN. Stop on pin mismatch, missing physical/provenance link, required producer change, unresolved authority, resource limit, user STOP, or session end. Unknown writers keep quarantined paths; no lease is reclaimed by this packet.

Only Luna integrates, stages exact paths, updates current state, reviews the complete outbound range and pushes a coherent reviewed checkpoint. Keep all unrelated modified/deleted/untracked paths untouched.
