# R14 proof handoff — revision 1, constructed but unchecked

Sprint: `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r14`.
Assignment: `/root/effect_permission_term_call_control_r14_lean`, handoff revision 1.
Contract SHA-256: `8a1fec9211b0962f3f2233f0dc35d097eadfe5c42267df51a7f0ad0b9e1e1a90`.
Input manifest SHA-256: `ec157c6b0a0fca8416873b2bd8c3e44f8bd679a4015f19279368a3d12aa0e584`.
Role: registered lean_prover, sole author; zero descendants. Requested/observed
model and effort: UNKNOWN in this leaf's authenticated launch payload.

Outcome class: **candidate conditional mathematics, constructed but unchecked**.
No Lean/Lake/checker invocation was permitted by the primary's fixed packet.
No kernel acceptance, actual theorem printout, transitive axiom result,
independent review, Rust execution receipt, or production claim is supplied.

## Frozen artifact and inputs

Only these two paths were written:

- `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean`:
  SHA-256 `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc`.
- This handoff; its final byte hash is returned in the delivery message to avoid
  a self-referential hash.

No scratch files, generated files, shared cache writes, root imports, source
edits, tests, dependencies, Git mutations, or other workers' files were written.
All verification/cache/generated-output ownership remains with primary Luna.

Direct accepted inputs remain unchanged:

- R13 `FormalPermissionConnectedCuts.lean`:
  `6427eed5f0c3b84f80a3a37c31797fc782960c725fb77f6bef46cebcc993b023`.
- R12 `FormalPermissionHelperFrames.lean`:
  `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`.
- Frozen R14 source handoff:
  `744c3244b919758360c3e0f966278ebbc3881d2cd1120de19410e345340c65ce`.
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- `lib.rs` and `candidate_effect.rs` use the contract/source handoff pins
  `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
  and `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`.

Read project pin `leanprover/lean4:v4.35.0`; no external packages in manifest.
Toolchain/lakefile/manifest SHA-256 respectively:
`ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`,
`212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`,
`058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
Actual installed Lean/Lake version and executable resolution: NOT_RUN.

## Governing source and original parent

Read root AGENTS.md, AGENTS.pre-sprint.md, goal-driven sprint rules, design
authority, the named skill and both source/execution references, compact current
state/README, the fixed R14 contract and frozen source handoff; read actual
R12/R13 definitions and R11 source-instance declarations.

The local executable source is `InferenceSession::with_term_events`,
`crates/yu-solver/src/lib.rs:10594–10621`, and its sampler at 10804–11036;
`BranchTermArena::take_capacity_events`, `term.rs:955–958`, drains ordered
recorded events. Relevant callers are `candidate_effect.rs::candidate_formal_value_pair`;
R9 source handoff pins argument → result → argument-port → result-port order.

The unchanged original parent is
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5,
SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`,
with authoritative birth-level correction
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6,
SHA-256 `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
Whole-language parent scope was read in `docs/yulang-whole-proof-closure-ja.md`
§§1,3–4, SHA-256
`17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`.
That integration document is a research guide, not new semantic authority.
Every supported source program, lawful finite construction history, actual
retained occurrence, original source scopes and jointly shared witnesses remain
in the parent. This exact-tree local model does not replace that quantification.

## Source-to-definition map and represented cases

Namespace prefix for every new public declaration:
`YulangClosure.FormalPermissionTermCallControl.`

- `ConstructorOutcome` separates final arena contents (`terms`) from the returned
  opaque `Except Nat Nat` Term/error. `mapConstructor` takes an explicit error
  mapper; it does not establish Rust `Into` authenticity.
- `EventOutcome` pairs one ordered snapshot with a supplied production counter
  result and `Except Nat Unit`. It allows counter writes before an error.
  `snapshots` keeps order, duplicates and empty event lists.
- `sampleOps` generates physical-change followed by one R12 `sampleResult`.
  Only executionCounters changes; resourceBoundarySamples/resourceLedger/
  f5cMatrixObserver copy the current values. `sampleState` is the separate
  direct state interpretation. No eventSnapshot/sampleAttempt operation is
  emitted: those source effects are test-only.
- `loopOps`, `loopState`, `loopError` recurse in event order, retaining the first
  error's supplied counter delta, setting eventSampleFailed and omitting every
  later event. No arbitrary operation list is an input.
- `controlOps` always emits constructor then drain. False accounting emits no
  sampler sequence. `controlResult` maps the constructor only after successful
  event processing; a sampler error wins over either constructor outcome.
- `SuccessfulInput` requires explicit `constructorOk` and `samplesOk` for every
  event. These observations are assumptions, never inferred availability.
  `successfulTermCall` constructs the existing R12 TermCall and handling list.
- `SuccessfulPair` generates the negative call at the actual positive final
  state. `sourceCalls` threads these at all eight paired R13 cuts, with cached
  leaf reads and unchanged capacities/backing inputs. No endpoint equality,
  arbitrary Call, initial cut state, TreeFrames or handling list is supplied.

Represented: empty/nonempty events; accounting true/false; constructor Ok/Err;
all samples Ok; first sample Err; later Err following successful samples;
sample error precedence; per-event supplied counter delta; arbitrary initial
allocator and full prior permission prefix; all eight term-call cuts of the
fixed R13 tree, including port/function/tuple paired completions.

Omitted/external: concrete Term/ConstraintError/SolveAvailabilityError encoding;
constructor/event generation; exact counter arithmetic and resource checks;
sampler authenticity for its particular snapshot/state; actual accounting-flag
value at a Rust cut; alias/primitive behavior; actual Rust return/state/path
linkage; reservations; native publication. Test-only snapshots/counts/attempts/
observers are identity fields. No source-language case is removed from the
original parent by this local scope.

## Constructed theorem inventory and exact audit handoff

All 19 public theorem declarations below require printed full types and
`#print axioms` in the primary's isolated pinned audit. The file also has a
private `sample_path` lemma (used by loop_path; its transitive dependencies must
be audited). No printed output or axiom list exists yet.

| Public theorem suffix | Statement/premises represented in source |
| --- | --- |
| `sample_ops_refine` | For every event/state, generated two operations equal direct sampleState. |
| `run_ops_append` | For every two operation lists/state, sequential interpretation composes. |
| `loop_ops_refine` | For every event list/state, runOps loopOps equals loopState, including errors. |
| `control_ops_refine` | For every constructor/events/accounting/state, transcript equals direct controlState. |
| `no_accounting` | False accounting gives exactly constructor/drain and mapped constructor result. |
| `loop_error_none` | Explicit AllSamplesOk events implies no loop error. |
| `constructor_error_preserved` | Constructor Err plus AllSamplesOk gives mapped constructor error under either flag. |
| `loop_first_error` | Successful prefix and designated Err imply exactly that first loop error. |
| `sample_error_precedence` | The same successful-prefix/Err premises under true accounting override any constructor result. |
| `first_failure_stops` | Head Err gives only that sample segment/failure flag; suffix ignored in operations and direct state. |
| `successful_event_order` | Head Ok emits its segment before recursively generated remaining events. |
| `successful_term_call` | Explicit SuccessfulInput gives exact ops, direct state refinement and returned Ok input.term for every error mapper/state. |
| `loop_path` | All loop outcomes preserve path. |
| `loop_test_fields` | All loop outcomes preserve the six test instrumentation fields. |
| `control_test_fields` | Both accounting branches preserve those six fields. |
| `control_preserves_allocator_path` | Every constructor/event/flag outcome preserves allocator/path. |
| `successful_pair_refines` | Paired positive/negative operations equal sequential controlState; function/tuple transcript agrees with port transcript. |
| `source_calls_at_cuts` | Generated pairs equal the actual connect calls at c3,c4,c5,c9,c10,c11,c12,c13; no equality premise. |
| `exact_tree_r9_from_term_control` | For arbitrary source State/initial helper state/level, row-length alignment, Aligned, Reservations and SourceCalls, obtains R13's SAME SourcePair/output, retained entries, four births, advanced state, final alignment and full-prefix append conclusion. |

Exact types are in the frozen .lean declarations, not asserted as checker
printouts here. Audit all inherited R12/R13 roots as required by the contract;
the primary's inventory selects their exact names from the unchanged modules.
Suggested checker entry point (NOT_RUN):
`python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --module YulangClosure.FormalPermissionTermCallControl --theorem YulangClosure.FormalPermissionTermCallControl.exact_tree_r9_from_term_control`.
Expand `--theorem` for every public suffix above and inherited roots, use the
primary-owned fresh copy and resolved pinned Lake, and obey the primary's audit
attempt/time budget. The leaf did not resolve/invoke Lake or create that copy.

## Parent application and precise first remaining premise

`exact_tree_r9_from_term_control` applies
`YulangClosure.FormalPermissionConnectedCuts.exact_tree_r9_from_connected`
with `sourceCalls inputs initial level`, retaining the same source output,
births, prefix and all reservation/alignment hypotheses. The generated cut
shapes are additionally stated by `source_calls_at_cuts`; local helper/pair
refinement is established as candidate proof terms, not Rust correspondence.

First verification premise: primary must obtain kernel acceptance and complete
type/axiom output, then independent review. First semantic premise thereafter:
the actual Rust successful constructor/sampler executions at each named cut
must instantiate `ConstructorOutcome`, ordered `EventOutcome`, accounting and
state data, with authenticated primitive/alias footprint and return encoding.
Owners: Luna assigns source/native/primitive correspondence; term.rs owns
constructor/event generation; sampler/lib.rs owns resource checks and counter
delta; reservation/native/publication owners remain unchanged. This handoff
does not appoint a reviewer or assert a concrete instance exists.

Original effect hygiene, consumer residual, whole-language inference soundness,
principality, progress, termination and production gates remain OPEN.

## Actual execution, resources, failure evidence and STOP

Read-only commands used `cat`, `sed`, `rg`, `sha256sum`, `date` through the
provided exec tool; edits used apply_patch. All returned shell cells exited 0.
The final rg enumerated the 20 declarations (19 public, one private) and found
no sorry/admit/axiom/skipKernel/native_decide match. This static search is not a
kernel or transitive dependency audit. No Lean/Lake command, test, Cargo,
compiler execution, package installation, nested CLI or Git command ran.
No diagnostics or material failed runtime result exists to discard; elaboration
is unobserved, and the candidate may require syntax/proof repair after audit.

Budget: 600 seconds total; all reads/construction/handoff fit within this finite
bound. No heavy process spawned; wall/CPU/RSS measurement is UNKNOWN (only
ordinary UTC timestamps were observed, including 14:02:32 UTC before handoff).
No remaining budget is transferred or inferred. The next step is the primary's
bounded isolated audit of these frozen bytes. No resumption without primary
renewal of the exact leases. **STOPPED; writes stopped on revision-1 delivery;
zero descendants and zero generated-output leases outstanding.**
