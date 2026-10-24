# LEAN-CORE-CONTROL-BRIDGE-20261025/r6

Status: FROZEN by Luna as a resource-renewal continuation of the authorized
Lean proof goal. This adds 600 seconds without resetting r3-r5 expenditure.
The full Yulang semantics/type-inference, source/native, and original A/B parent
remains OPEN.

## Original goal, current outcome, and exact scope

The user's unchanged goal is complete Lean proofs of Yulang semantics and type
inference under `notes/theory/lean`, with reviewed milestones committed and
pushed. This bounded continuation targets the existing Original-to-Control
bridge only. It preserves the r3 claim and all its quantifiers, source syntax,
typing domains, four explicit source transitions, literal foreign suffixes,
and source/exit/foreign finite-trace split.

Original bridge declarations in `notes/theory/lean/YulangClosure/CoreControlBridge.lean`:

- `finite_coverage` for every metadata/body, source, target, world, suffix and
  finite prefix length;
- `machine_finite_coverage` for the same unrestricted root-machine prefixes;
- `exit_empty_prefix` for an empty foreign suffix;
- `finite_typed_transfer` for the original fixed-context typing premise;
- `finite_closed_safety`, including typing, Bad exclusion and progress/terminal
  coverage.

No statement may be narrowed, strengthened with an unproved premise, or replaced
by a conditional theorem. The four source transitions remain exactly
`originalEnter`, `originalReturnBind` using `Original.substComp`,
`originalPrincipal`, and explicit `originalExit`. No source constructor,
Control rule, semantic assumption, or production compiler behavior is changed.

## Frozen baseline and direct dependency component

Branch `research/simple-sub-intrusion`, committed baseline
`0bfdc64aff38e08a0e01ffcec28f6013465d8d46`. The r5 check built
`ControlComposition` and failed in `CoreControlBridge` at dependent-index
`Prefix` inductions (`finite_coverage`, `machine_finite_coverage`,
`exit_empty_prefix`, `finite_closed_safety`) and at the
`finite_typed_transfer` induction-hypothesis application. These are Lean proof
elaboration failures; no source-qualified semantic counterexample is known.
The root target was not checked in r5.

Frozen artifact SHA-256 values at r6 start:

| Artifact | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3fcd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `6d7d5da463480fbb618072b086c5092452575c56526579e4f898babd37b4567c` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `2cc68ffc79f17c0cb478802fec10ca2861e1a558a8202796bd7599595e5907ed` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `67e0d5d8840090ad7adf06b33c65725dc0901488c16f9dcc235c5c0372ae0135` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `95cad83ee84e767aecd6314f84e983db40a9efba1e8322c6f54ee79d45c3cfad` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| r5 contract | `30c784d43e0ec5aa5ccb5b74be7cd1d4f32269068f0b761bd6414f5793652b97` |

Pinned toolchain: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Luna rechecks all hashes before
dispatch and before checking/review. `ControlSyntax`, `ControlTyping`,
`ControlComposition`, transitive core files, the root module, and toolchain are
frozen dependencies.

## Proof method, application, and falsifier

The constructive prover owns one coherent repair of `CoreControlBridge.lean`:

1. Prove prefix coverage through a helper whose initial state is a variable
   index and whose premise explicitly identifies that state with the embedded
   Original state. Generalize the dependent start-state index during induction,
   then specialize the helper to the existing `embed` expression without
   changing the public theorem.
2. Establish one generic `Prefix Original.Step` typing-preservation helper with
   its initial typing premise explicitly generalized. Reuse it in
   `finite_typed_transfer` and `finite_closed_safety`; do not rely on the
   current induction hypothesis retaining an outer theorem's fixed premise.
3. Apply the same generalized-index method, or a derived no-step prefix lemma,
   to `exit_empty_prefix`. Reuse the corrected coverage helpers in the public
   safety theorem.

The falsifier is failure to derive every unchanged public statement from these
helpers, any newly required assumption about metadata/body/suffix/source, a
lost finite-trace case, or any changed source transition/substitution. If the
method exposes a real counterexample, stop and return it with the exact source
and theorem premises; do not patch semantics under this lease.

## Exact leases and lane boundary

The constructive prover's sole write leases are:

- `notes/theory/lean/YulangClosure/CoreControlBridge.lean`
- `tasks/agent-loop/inbox/20261025-lean-core-control-induction.md`

No other source, contract, task record, root module, generated/scratch path,
test, configuration, or semantic file is leased. Scratch outputs must stay
outside the repository and be listed in the handoff. The worker has no Git,
review, central-state, or child-dispatch authority and must STOP after its
multi-stage envelope. No descendants are authorized.

Luna owns `current.json`, the outcome receipt, root `YulangClosure.lean`, all
checking, review assignment/adjudication, staging, commit and push. The root is
already set to import the bridge and print axioms for `successor_coverage`,
`machine_finite_coverage`, and `finite_closed_safety`; its current hash is
frozen above. The implementation/source-native lane remains WAITING with zero
new allocation: this proof has a stable frozen source interface, and a
parallel source/native task would not establish or falsify the dependent-index
lemma. The accepted bounded native-event audit remains separate evidence; full
native correspondence and original A/B obligations stay OPEN.

## Renewal accounting and checks

The r3-r5 authorization cap of 3,600 seconds is fully reserved/accounted; its
unused 40-second review reserve and 6.8-second remainder remain untouched.
Luna grants exactly 600 additional seconds for r6, bringing cumulative
authorized capacity to 4,200 seconds without erasing any earlier expenditure:

| Stage | Owner | Maximum |
|---|---|---:|
| Multi-stage constructive repair | `prover` | 240 s |
| Serialized pinned bridge/root checking | Luna | 120 s |
| Checker-driven repair on the same bridge lease | same `prover` | 120 s |
| Fresh isolated independent compiler review | nonauthor `compiler_referee` | 120 s |

The 120-second checking grant covers all initial and post-repair checks and
axiom/hole receipts. Only one Lean process may run at a time. From
`notes/theory/lean`, use the actual project toolchain via
`lake env lean -j1 -M1024`. First run
`lake env lean -j1 -M1024 -o .lake/build/lib/lean/YulangClosure/CoreControlBridge.olean YulangClosure/CoreControlBridge.lean`,
then run
`lake env lean -j1 -M1024 -o .lake/build/lib/lean/YulangClosure.olean YulangClosure.lean`.
These check the current sources and emit the OLean imported by the next target;
the root run must include the three requested `#print axioms` outputs. No tests,
Cargo, native probes, or parallel builds. If the initial check passes, do not
spend the checker-driven repair grant. If the final check fails or any grant
expires, stop construction/review eligibility and record exact diagnostics.

Only after both Lean files check, freeze the artifact and dependency hashes,
scan the reviewed dependency component for `sorry`, `admit`, `axiom`, unsafe
proofs and native decision escapes, and assign a fresh nonauthor reviewer.
Review must confirm exact theorem domains/quantifiers, generalized helper
specialization, all four source transitions, actual substitution, suffix
retention, every embedded successor, source/exit/foreign trace decomposition,
root axiom receipts, and the hole/escape scan. Any blocking finding leaves
acceptance OPEN. The original full semantics/type-inference and source/native
parents remain OPEN even if this bridge passes.

## Review, current-state, and Git boundary

The dispatcher recommended this exact bounded renewal at the r5 material
proof obstruction. Luna approves it under the user's resumed ongoing-goal
authorization. Contract SHA-256 is recorded in `current.json` after freeze.
The prover request is `prover`, Sol/high. The reviewer request is a fresh
`compiler_referee` using its registered read-only route (gpt-6.1-sol/medium).
No old worker is revived; the three unrelated unknown reservations remain
quarantined. Requested/observed model and effort must be recorded separately;
unobserved values remain `UNKNOWN`.

At the next material boundary, Luna freezes an outcome receipt, synchronizes
`current.json` under 16 KiB, adjudicates any review, and stages only explicit
approved paths after inspecting the entire outbound range and remote HEAD.
Only a reviewed and checked milestone may be committed as accepted proof.
Never force-push. Parent closure is not implied by this bridge.
