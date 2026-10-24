# LEAN-CORE-CONTROL-BRIDGE-20261024/r1

## Parent and fixed outcome

The unchanged parent is the user's full objective: complete Lean proofs of
Yulang semantics and type inference in `notes/theory/lean`, including original
source/native and A/B obligations. This sprint does not redefine or close that
parent.

Concrete parent obstruction: `Original.Step.enter` for a typed `let` adds a
syntax-bearing bind frame, while the existing `Control.Step.body` keeps the old
stack unchanged and its body relation only handles `Head.run`. A closed,
well-typed `let x ← Force (Delay (Ret unit)) in Ret x` therefore has no
literal-stack one-step image in the current Control machine. Actual runtime
`begin_local` also pushes `Frame::Local` before evaluating its initializer.

**Fixed outcome:** connect the already proved `Original` fragment (unit,
variable, delay, union/intersection/Top/Bottom, Ret/Force/let/case/choose and
the existing principal steps) to an explicit syntax-bearing family in the
Control machine. Derive typing for the representation from `ValTyped`,
`CompTyped`, `FramesTyped` and actual substitution, then prove a concrete
simulation for entry, return-bind, every included principal step, and arbitrary
finite traces while retaining the old frame suffix. Inspect every Control
successor from the embedded family so the bridge proves coverage as well as a
chosen simulation. No original constructor is encoded as an arbitrary `Nat`
tag. Preserve all existing raw and control rules and their independent typing
judgments. An interface change that cannot retain the original syntax,
substitution, or suffix is a falsifier, not a reason to weaken the parent.

Generic prefix lemmas alone do not meet the outcome. Full Call/wrap/Resume,
all constructor typing, source initialization, actual metadata/observations,
native correspondence, source-scoped coverage/principality/termination and
original inference A/B remain open after this sprint unless directly proved.
Compiler implementation and semantic changes are out of scope.

## Baseline and frozen inputs

- Branch: `research/simple-sub-intrusion`
- Baseline HEAD: `fbbc66cdc63b1f227fff30d33355fc6c35f9dd59`
- Worktree: clean at sprint start.
- Lean toolchain: `notes/theory/lean/lean-toolchain` (Lean 4.35.0); no added
  dependencies.

| Direct input | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `6d7d5da463480fbb618072b086c5092452575c56526579e4f898babd37b4567c` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `2cc68ffc79f17c0cb478802fec10ca2861e1a558a8202796bd7599595e5907ed` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `76b250485b899bf9f7f5d0b9445d869f4c5961b155a21a520b0802678a1db46f` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `33ddb90ec39e8136c1ec9bb72b0ef4edf35d85fb32c1884cff3a2bcc5819ebfa` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `23c7b251ef307a61ccaca7e2ec959d4a5583b649309a26cf27eff1eb9e9cb791` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `notes/theory/2026-10-24-lean-core-correspondence.md` | `5aa9c3c417c98b3f6e69e3cb1ecb8872b49db836a10d0ca72e2606c0399dcbb0` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md` | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `5893555fe89c594feabca200d1d8f26631877200da61e6ae39c80d375f748bb1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |

Governing correction: use the current Core/Control and corrected lifetime
correspondences. Do not import old uniform resume freshening or treat a
conditional `BodyLaws` field as the concrete body proof this outcome requires.

## Leases and lanes

1. **Lean machine implementation**, owner `/root/lean_control_prefix_impl`:
   exclusive writes to `notes/theory/lean/YulangClosure/ControlSyntax.lean`,
   `ControlTyping.lean`, `ControlComposition.lean`, and
   `tasks/agent-loop/inbox/20261024-lean-core-control-implementation.md`.
   Add the smallest explicit syntax-bearing representation and actual
   suffix-preserving entry/return transitions needed for the fixed outcome;
   derive typing from the existing Original judgments, not an assumed body
   safety law. First return a concise interface proposal to Luna before the
   proof lane writes. Continue implementation only after Luna freezes that
   interface. No descendants, generated files, tests, Cargo, production code,
   network or Git.

2. **Constructive bridge proof**, owner `/root/lean_core_control_prover`:
   exclusive writes to `notes/theory/lean/YulangClosure/CoreControlBridge.lean`
   and `tasks/agent-loop/inbox/20261024-lean-core-control-proof.md`. Start
   read-only interface preparation; begin the leased proof only after Luna
   sends the frozen interface revision. Prove concrete state/frame embedding,
   entry and return-bind correspondence, preservation of every included
   principal step, all-successor coverage, and arbitrary finite trace transfer.
   Do not edit implementation modules or infer source/native/A-B closure.

3. **Independent inference source correspondence**, owner
   `/root/lean_native_event_audit`: exclusive writes to
   `notes/theory/2026-10-24-lean-native-event-correspondence.md` and
   `tasks/agent-loop/inbox/20261024-lean-native-event-correspondence.md`.
   Trace actual birth/event/copy provenance through qualification, replay,
   retained pairs and equality consumers against `Contracts.Qualifies` and the
   unchanged original source-scoped A/B claim. Search for a source-qualified
   counterexample or state the exact missing constructor/consumer evidence.
   This is read-only toward compiler files and cannot promote or revise
   semantics. Do not assume same-birth alone proves whole-domain strategy.

Luna owns the frozen interface, root imports, Lean README/correspondence,
contract/outcome, `current.json`, checks, adjudication, review assignment and
all Git operations. No other writer may touch the leased paths. Children do
not start teams or alter leases.

## Evidence, review and resources

Success evidence: pinned Lean 4.35.0 kernel acceptance of the new bridge and
updated Control modules; theorem statements quantify over the actual embedded
fragment and arbitrary old suffixes; exhaustive successor coverage for that
embedded family; no `sorry`, `admit`, project axioms, unsafe proof, native
decision escape or arbitrary-`Nat` encoding of Original values; fresh
independent review of frozen proof and source correspondence. Static scans or
tests alone do not prove the bridge.

Falsifiers include: let entry loses/reorders the suffix; return-bind differs
from `substComp`/`substitute_top`; any additional Control successor escapes the
simulation; source values are collapsed into unproved tags; or the bridge
assumes the very body-preservation obligation it claims to establish.

Resource cap: 3,600 seconds total across assignments, including up to 1,200
seconds each for implementation and constructive proof, 600 seconds for source
correspondence, and 400 seconds for fresh review. One Lean checker/build process
at a time; primary checks with the pinned local toolchain, `-j1 -M1024`, bounded
to 120 seconds per invocation. No Cargo/tests/native probes. Astra allocation:
zero. Missing observed model/effort/duration remains UNKNOWN. STOP and freeze
each assignment at its bound; unconfirmed writer cessation keeps its paths
quarantined.

Fresh reviewer must not be an author or source-counterexample contributor.
Review the frozen code/source alignment, exact theorem hypotheses, all
embedded-family successors, suffix preservation, checker output and axiom
dependencies. Primary adjudicates findings. A conditional or candidate result
does not close the original parent.

## Integration boundary

At a substantial reviewed milestone, primary updates compact current state and
one outcome receipt, verifies direct hashes and intended paths, checks the full
outbound range, commits explicit paths and performs an ordinary non-forced push
to the inspected upstream. Never include protected questions or generated
`.lake` outputs. Preserve all three UNKNOWN quarantined legacy reservations.
Consult the dispatcher again at an interface contradiction, material
dependency/lease change, review seam, resource boundary or sprint end.
