# LEAN-CALL-REQUEST-BOUNDARY-20261025/r1

Status: **FROZEN by Luna; Astra author lease may be activated.**
Branch/baseline: `research/simple-sub-intrusion` / `4d15e26ff207993a8e9049fb21f754f219c0a273`.
Authority: unchanged accepted Yulang syntax and represented `CallControlStep`; no semantic or inference rule changes.

## Original goal and sprint outcome

The unchanged user goal is complete Lean proofs of Yulang semantics and type inference over the accepted source domain. This sprint advances the represented Call request boundary. Existing evidence separately proves that a requesting state can unwind through all frames and that response plugging cancels capture binders. It does not yet characterize every finite unwind prefix or connect an arbitrary actual complete request trace to the response-typing theorem.

Prove a universal finite-prefix boundary characterization for every represented requesting state and arbitrary metadata/world: every legal prefix of length at most `frames.length + 1` has the exact state produced by processing that many innermost-first frames (or the unique final `finishRequest` step). The characterization must account for captured continuation syntax, residual frames, metadata/world operation order, scope updates, unchanged observation list and literal suffix, and exact completion length. Preserve the existing `requestBind`, `requestAdapter`, `requestScope`, `requestExpose`, and `finishRequest` constructors; introduce no source restriction or semantic premise.

Luna then composes the checked boundary theorem with existing finite-prefix typing and response-cancellation/typing to establish: for every actual represented finite path from an initially typed Call to a requesting state, the unique completed request boundary retains the exact captured continuation typing; a typed response plugs that continuation through the captured frames and yields the original typed result. This is syntax/typing evidence only. It does not prove a source/native response exists or close Call A/B, source/native correspondence, inference A/B, or production.

## Frozen dependencies

The following source and toolchain inputs are pinned at sprint start; authors must verify these hashes before using them:

| Input | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CallRequestUnwind.lean` | `e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9` |
| `notes/theory/lean/YulangClosure/CallPrefixTyping.lean` | `95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc` |
| `notes/theory/lean/YulangClosure/CallFiniteTyping.lean` | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |
| `notes/theory/lean/YulangClosure/CallCaptureTyping.lean` | `906e8204aa155efd3f4e45d9c2a2a9fbe010858206ef3dd0acfd3d0d607a0de9` |
| `notes/theory/lean/YulangClosure/CallResponseCancellation.lean` | `ab9083bab971acd4e72cb8db95d567b309a240e1773b3fc4544fa6968ffe9488` |
| `notes/theory/lean/YulangClosure/CallCaptureResponse.lean` | `a310f3da1091a2dd7ed1d751aea67c44aefe06ce89fc9bb16cc0d19b530eb1c6` |
| `notes/theory/lean/YulangClosure/CallUnwindTypingRepair.lean` | `1eaea1938f6ee2341352afcc597847fc2ade5b8ce8d3be84dda19926fe217cc3` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

All listed hashes were independently computed from the current worktree before freezing this contract. Relevant definitions are `CallState`, `CallControlStep`, and request transition constructors in `ControlSyntax.lean`; length-indexed `Prefix` in `Contracts.lean`; `captureFrames` and the existential complete unwind in `CallRequestUnwind.lean`; the typed initial-prefix theorem in `CallFiniteTyping.lean`; and response cancellation/typing in `CallCaptureResponse.lean`.

## Proof assignment — Astra, bounded core packet

Prove a reusable boundary function or equivalent exact characterization that represents processing a finite innermost prefix of the original `frames` list. State and prove both directions needed for exactness: the prescribed prefix is realized by actual `CallControlStep` transitions; every actual prefix in the permitted length range has that prescribed endpoint. At `frames.length`, the state is requesting with no frames and `CallState.captureFrames frames continuation`; one additional step is exactly `finishRequest`, yielding the requested head. The partial-prefix cases must expose the correct residual frames and captured syntax, and must preserve fields not changed by their constructors.

Do not assume transition determinism globally; prove only the request-state inversion required by the theorem. Do not omit scope/expose world operations, reverse bind/adapter capture order, infer observed views from frame identities, or conflate completion with a response.

Exact lease:

- `notes/theory/lean/YulangClosure/CallRequestBoundary.lean`
- `tasks/agent-loop/inbox/20261025-call-request-boundary.md`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundary.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundary.ilean`

Use up to 300 aggregate Astra seconds, medium effort, at most three substantive stages. No descendants, no production code, no edits to shared dependencies, no extra paths or nested CLI. Stop on a genuine counterexample, source/constructor mismatch, exhausted grant or frozen handoff.

## Primary composition and verification

After Astra STOP and source freeze, Luna owns:

- `notes/theory/lean/YulangClosure/CallRequestBoundaryComposition.lean`
- `tasks/agent-loop/inbox/20261025-call-request-boundary-composition.md`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundaryComposition.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundaryComposition.ilean`
- `notes/theory/lean/.lake/call-request-boundary-r1-check.lean`
- `tasks/agent-loop/inbox/20261025-call-request-boundary-r1-verification.jsonl`
- `tasks/agent-loop/inbox/20261025-call-request-boundary-r1-review.md`
- `tasks/agent-loop/sprints/call-request-boundary-20261025-r1-outcome.md`

The composition must apply the boundary result to an actual `Prefix` from `CallState.initial`, obtain payload and captured-continuation typing from the existing typing-preservation theorems, then apply the existing response-substitution theorem. Preserve the original literal suffix and existing metadata/world transitions. No assumption that an external resumer is lawful or source-authentic is allowed.

Run at most three serialized `lake env lean -j1 -M1024` invocations, each at most 120 seconds: boundary source, composition, exact public signatures/axioms. Stop at first failure, pin mismatch, missing artifact, timeout, signature drift or unapproved axiom. Record timestamps, exit status, process duration, source/input/output hashes and complete streams in each fsynced receipt row. Allowed axioms are `[propext, Quot.sound]` or a subset.

After all authors stop and artifacts/dependencies freeze, a fresh nonauthor `compiler_referee` reviews the exact sources, prefix-completeness argument, all five frame cases, falsifiers, signature query and complete receipt. Acceptance requires all checks exit 0, exact unrestricted metadata/world quantifiers, no holes/custom axioms, consistent hashes and timestamps, and CLEAN review. The proof author and Luna composition author are not reviewers.

Falsifiers: reverse a bind/adapter capture step; replace `upCall Nat.succ` in response capture; reverse nested scope/view suspension; change completion from `frames.length + 1`; mutate the observed list or literal suffix at a request transition. Explicit small mixed-frame witnesses must distinguish the rejected orders.

## Resources, boundaries and parent application

Fresh cap: **1,800 seconds**, no carryover: Astra 300; Luna composition/adjudication 300; serialized Lean verification 360; independent review 300; integration/current/outcome 90; contingency 450. At most one Astra assignment, two new authors total, one Lean process, one CPU, 1,024 MiB and 120 seconds per invocation. Three pre-existing UNKNOWN quarantines remain reserved and untouched; admit no second author until live capacity is reconciled.

No compiler/runtime edit, source-domain restriction, test/fixture/expected-output change, semantic decision, native correspondence claim or production promotion is authorized. There is no safe production-code slice: the selected proof only characterizes the existing formal Call constructors. Source/native request and response authenticity, complete Call A/B, Force realization, inference A/B and production remain OPEN with their recorded owners.

Success evidence is the frozen universal exact-prefix theorem and its typed actual-request composition. Before: existential unwind plus separate capture/response typing. After: all finite represented request-prefix endpoints are characterized and actual typed request completion composes into typed response plugging. Review is the falsifier/reviewer seam above. Current state and a durable outcome record are updated only after evidence is frozen; the next dispatcher consultation is at sprint completion, material obstruction/counterexample, dependency/authority/lease change or integration seam.
