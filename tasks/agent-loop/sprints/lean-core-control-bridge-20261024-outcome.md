# LEAN-CORE-CONTROL-BRIDGE-20261024 outcome

## Status

**BLOCKED on repair; bridge acceptance OPEN.** The r3
implementation and bridge proof were written and frozen. After the user
confirmed that elan and Lean are installed, the primary verified the system
toolchain and ran the first pinned Lean 4.35.0 check. Independent compiler referee
`/root/core_control_static_review` STOPPED after finding four blocking
elaboration issues in the frozen candidate. The pinned checker confirmed two;
the other two remain static findings, not checker diagnostics or a semantic
refutation. The bridge is not accepted or
theorem-closed. The user's full Yulang semantics and type-inference goal,
including source/native and original A/B obligations, remains OPEN.

The sprint retains revision r3 at
`tasks/agent-loop/sprints/lean-core-control-bridge-20261024-r3.md`, SHA-256
`4853f6713bd6b42b509c4f26085b90c2860156695af8c70f247fa35269400044`.
The typing-domain split keeps ordinary Control judgments and their theorem
domains intact; the Original segment has a separate syntax-directed
`SegmentTyped` judgment. Only the four explicit source transitions are
authorized.

## Frozen candidate and producer receipts

Implementation, assignment `LEAN-CORE-CONTROL-IMPLEMENTATION-20261024`:

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `1c057f1f5303db479d0fc303bd1a0b305ba839f3034770dc467068c9f1869981` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `b2cce8eca5163dc41ef41c7cdeae5bc9dfb5186c67a982a7248194cef44b7437` |
| `tasks/agent-loop/inbox/20261024-lean-core-control-implementation.md` | `78ac38286d7916e4b84f9d9613aa262044c89381aecd40d8e6aaa1649c320399` |

Proof, assignment `LEAN-CORE-CONTROL-PROOF-20261024`:

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `95cad83ee84e767aecd6314f84e983db40a9efba1e8322c6f54ee79d45c3cfad` |
| `tasks/agent-loop/inbox/20261024-lean-core-control-proof.md` | `6d603c84bd6fdf8c1cf1a640a630f03de28c9e97981a174d3e940682bc84e6aa` |

Both writers supplied STOP receipts; no descendants or generated artifacts
were reported. The implementation receipt confirms exactly four source
transition constructors and no implicit empty-stack or foreign-frame exits.
Their requested active time and observed model/effort remain UNKNOWN.

## Independent review

The independent compiler referee performed a preliminary static review of the
frozen hashes above. It found no semantic counterexample to the bridge's
stated simulation shape, syntax preservation, suffix retention, or finite
trace split. It found these four BLOCKING Lean issues:

1. `ControlTyping.lean:112` defines `SegmentTyped` as a Type-valued structure,
but downstream theorem propositions use it under `∨`. The judgment must be
Prop-valued while retaining syntax and typing witnesses; informative
projections from a Prop structure must not be required.
2. `ControlTyping.lean:8–9` derives `DecidableEq` for `Control.Ty` after adding
`Ty.original Original.Ty`, but no `DecidableEq Original.Ty` instance exists in
the frozen source.
3. `ControlComposition.lean:363–369`, `admissible_resume_typed`, omits the
`.originalValue` case. Its `responseOK` premise is contradictory for that
constructor, but the proof still needs an explicit contradiction branch.
4. `ControlComposition.lean:291, 298, 302, 306`, `segment_progress`, rewrites
`s.head` and `s.stack` equalities into goals whose state is still the bare `s`;
the proof does not destructure or reconstruct `s` before rewriting.

Reviewer identity: `/root/core_control_static_review`, configured
`compiler_referee`; observed model/effort UNKNOWN. The review ran no Lean
checker, builds, tests, or edits. It does not establish
elaboration, kernel acceptance, or axiom dependencies. No repair is authorized
by the frozen producer leases; any repair requires a new bounded assignment,
new hashes, pinned checking, and focused review of the changed dependency
component.

## First pinned checker receipt and next dependency

The pinned project toolchain is available through the actual user-managed
`/home/momota1029/.elan/bin` shims. `elan toolchain list`, `lean --version`,
`lake --version`, and `lake env lean --version` report Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. On 2026-10-25, the primary ran
`timeout 120s lake build YulangClosure.CoreControlBridge` from
`notes/theory/lean`. It exited 1 after 4.7 seconds. Contracts,
CoreComposition, CoreSyntax, CoreSubstitution, CoreExecution and ControlSyntax
built. ControlTyping failed with two checker diagnostics: no `DecidableEq`
instance for `Original.Ty` at line 9; and
`original_state_typed_with_suffix` had a non-propositional theorem result at
line 121 because `SegmentTyped` was Type-valued. These confirm two static
review findings. The response-constructor and `segment_progress` findings
remain static until the earliest declarations are repaired. The build created
only ignored `.lake` outputs. No tests ran.

Deferred repair packet, not issued under this sprint: (1) replace Type-valued
`SegmentTyped` with a Prop-valued judgment retaining the same syntax, witnesses
and typing premises; (2) resolve the `Ty.original` equality derivation while
preserving ordinary equality behavior; (3) discharge the impossible
`originalValue` response branch; (4) destructure state before rewriting its
head/stack in `segment_progress`; (5) check every dependent declaration and
obtain focused review of changed hashes. A new bounded repair assignment is
needed.

The pre-repair ControlTyping, ControlComposition and CoreControlBridge bytes
were preserved read-only at `/tmp/yulang-lean-core-control-r3-20261025/` before
the next assignment. The bounded r4 continuation and remaining resource
allocation are in `lean-core-control-bridge-20261025-r4.md`. Until repaired
hashes pass the pinned checker and fresh independent review, the candidate is
unaccepted and no Lean proof gate closes. The native-source audit is separate
and does not supply a proof premise for this bridge.

## Separate source-native result

`notes/theory/2026-10-24-lean-native-event-correspondence.md` revision 2 was
independently accepted as bounded static evidence after its r2 provenance
metadata correction. It found missing immutable Value-birth/path evidence and
an unresolved Replay-source licensing premise; it found **no**
source-qualified counterexample. Native correspondence, source-scoped
strategy, inference soundness/coverage/principality/termination, and original
A/B remain OPEN. This note is already in commit `fa3658387`, which is pushed
to `origin/research/simple-sub-intrusion`.

The frozen Lean candidate and its handoffs are not in that commit and are not
commit-ready. The next record-only checkpoint will contain this outcome and
the synchronized current state, excluding the blocked Lean code and handoffs.
`python3 tools/agent_sprint.py check` passes after current-state reconciliation;
this is static scheduling-state evidence only. No production or semantic
changes were made.
