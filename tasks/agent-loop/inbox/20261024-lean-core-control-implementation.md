Sprint-ID / contract revision and SHA-256:
LEAN-CORE-CONTROL-BRIDGE-20261024/r3; contract SHA-256
4853f6713bd6b42b509c4f26085b90c2860156695af8c70f247fa35269400044.

Assignment-ID / handoff revision (positive integer):
LEAN-CORE-CONTROL-IMPLEMENTATION-20261024 / revision 1.

Parent gate / original theorem and scope locator:
The unchanged parent is full Yulang semantics/type inference and source/native/A-B
closure. This packet addresses the Control source-entry/body-stack obstruction in
`tasks/agent-loop/sprints/lean-core-control-bridge-20261024-r3.md`; it does not
close that parent.

Baseline / direct dependency hashes:
Baseline HEAD `fbbc66cdc63b1f227fff30d33355fc6c35f9dd59`.
`CoreSyntax.lean` 4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001;
`CoreSubstitution.lean` 6d7d5da463480fbb618072b086c5092452575c56526579e4f898babd37b4567c;
`CoreExecution.lean` 2cc68ffc79f17c0cb478802fec10ca2861e1a558a8202796bd7599595e5907ed.

Role / actual worker ID / current session / launch or resume receipt:
Implementation lane; worker `/root/lean_control_prefix_impl`; session
`LEAN-CORE-CONTROL-BRIDGE-20261024/root-turn-1`. Runtime launch metadata was not
reported to this worker.

Requested model and effort / observed model and effort (UNKNOWN if absent):
Requested Luna/high; observed model UNKNOWN; observed effort UNKNOWN.

Exact leased paths / all authors and contributing descendants:
Leased and changed: `notes/theory/lean/YulangClosure/ControlSyntax.lean`,
`notes/theory/lean/YulangClosure/ControlTyping.lean`,
`notes/theory/lean/YulangClosure/ControlComposition.lean`, and this inbox file.
Author: `/root/lean_control_prefix_impl`. No descendants.

Outcome class:
Implementation candidate; checker acceptance and independent review pending.

Parent application: what follows now; exact remaining premise and owner:
Control now has syntax-bearing `Head.original`, `Value.originalValue`,
`Frame.originalBind`, `Frame.originalBoundary`, and `Ty.original`. The four frozen
`ControlStep` source transitions are `originalEnter`, `originalReturnBind`,
`originalPrincipal`, and `originalExit`. `SegmentTyped` records the actual
`Original.StateTyped emptyContext` derivation, literal source-frame/boundary/old-
suffix embedding, and independently typed foreign suffix. The ordinary
`HeadTyped`, `FrameTyped`, `FramesTyped`, `StateTyped`, and generic Control
progress domains remain unchanged. `segment_progress` maps actual
`Original.progress` cases using only the four frozen transitions.

Remaining: pinned Lean kernel acceptance, source-segment preservation and
exhaustive successor classification, arbitrary finite trace decomposition, and
fresh independent review. The constructive bridge owner owns these in
`CoreControlBridge.lean`; Luna owns primary checking/adjudication.

Source constructors -> generated constraints -> propagation -> consumer/native path:
This Lean packet starts from the established syntax-directed
`Original.ValTyped`/`CompTyped`/`FramesTyped` judgments and actual
`substComp (single v)`/`Original.Principal` reductions. It embeds active source
syntax and bind frames before a typed old Control suffix, then hands a source
return across the metatheoretic boundary as an actual `Original.Val`. It does
not claim inference-constraint generation, solver propagation, source/native
correspondence, compiler execution, or A/B closure.

Artifact locators and byte hashes / frozen review snapshot:
`ControlSyntax.lean` 801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9;
`ControlTyping.lean` 1c057f1f5303db479d0fc303bd1a0b305ba839f3034770dc467068c9f1869981;
`ControlComposition.lean` b2cce8eca5163dc41ef41c7cdeae5bc9dfb5186c67a982a7248194cef44b7437.
Review snapshot: these exact bytes, pending primary checker and fresh review.

Checks, coverage, omitted cases and resource budget spent/remaining:
No Lean invocation, test, build, Cargo process, network request, Git mutation,
scratch file, or generated output was used. Therefore Lean 4.35 kernel acceptance
and axiom-dependency output are UNKNOWN and must be checked by Luna under the
contract's serialized checker allowance. Implemented interface covers the
existing typed Original fragment; proof of every Control successor and arbitrary
finite traces is owned by the proof lane. Full Call/wrap/Resume, all constructor
typing, source initialization, metadata/observations, native correspondence,
source-scoped inference A/B, and termination remain open.
Assignment cap: 1,200 seconds. Actual active duration was not exposed by runtime;
spent and remaining are UNKNOWN. Keep the unobserved grant charged/reserved.

Next related step inside the existing envelope, or exact boundary needing Luna:
Proof owner consumes these declarations and proves state/frame embedding,
source-step correspondence, all-successor coverage, and arbitrary finite trace
transfer. No authority or lease expansion requested.

Mutual TODOs:
`LEAN-CORE-CONTROL-PROOF-INTERFACE-1`; original parent is the r3 fixed bridge
outcome; first missing evidence is pinned Lean acceptance plus exhaustive
successor/trace proofs; source owner is `/root/lean_core_control_prover`; inputs
are the four Control transitions, `SegmentTyped`,
`original_state_typed_with_suffix`, and `segment_progress`; proposed outputs are
the leased `CoreControlBridge.lean` and proof inbox; falsifiers are any lost or
reordered suffix, return-bind differing from actual substitution, or unexplained
successor from an embedded segment.

Worker state / writes stopped receipt / unresolved descendant leases:
STOPPED for writes immediately after the final handoff hash is computed and sent
to Luna; no descendants. The exact frozen artifact hashes are recorded above;
the handoff SHA-256 is the submission-message receipt. No write lease remains
active after this receipt.

Commit-ready milestone or explicit pending review/integration:
Not commit-ready. Pending primary Lean check, proof-lane result, and independent
review. No self-certification is claimed.
