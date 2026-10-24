# LEAN-CORE-CONTROL-BRIDGE-20261025/r4

Continuation of the fixed r3 outcome under a bounded repair envelope. The
original full Yulang semantics/type-inference parent and all source/native/A-B
quantifiers remain OPEN and unchanged.

## Outcome and observed evidence

Obtain pinned Lean 4.35.0 acceptance and focused independent review of the
syntax-bearing Original-to-Control bridge with arbitrary old Control suffixes,
without changing the r3 source constructors, four transitions, or theorem
domains. The separate syntax-directed `SegmentTyped` judgment remains required;
ordinary Control typing and progress retain their established domains.

The actual system toolchain is available through `/home/momota1029/.elan/bin`.
`elan toolchain list`, `lean --version`, `lake --version`, and `lake env lean
--version` identify Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
On 2026-10-25, `timeout 120s lake build YulangClosure.CoreControlBridge`
exited 1 after 4.7 seconds. Contracts, CoreComposition, CoreSyntax,
CoreSubstitution, CoreExecution, and ControlSyntax built. ControlTyping
produced two actual diagnostics: missing `DecidableEq Original.Ty` at line 9;
and a non-propositional theorem result at line 121 because `SegmentTyped` is
Type-valued. The frozen r3 referee's remaining two findings (the
`originalValue` response branch and state destructuring in `segment_progress`)
are still static findings, not checker diagnostics.

## Frozen r3 snapshot and inputs

The pre-repair candidate was copied read-only to
`/tmp/yulang-lean-core-control-r3-20261025/` before this assignment:

| Artifact | SHA-256 |
|---|---|
| `ControlTyping.lean` | `1c057f1f5303db479d0fc303bd1a0b305ba839f3034770dc467068c9f1869981` |
| `ControlComposition.lean` | `b2cce8eca5163dc41ef41c7cdeae5bc9dfb5186c67a982a7248194cef44b7437` |
| `CoreControlBridge.lean` | `95cad83ee84e767aecd6314f84e983db40a9efba1e8322c6f54ee79d45c3cfad` |
| `ControlSyntax.lean` (frozen dependency) | `801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9` |
| r3 contract | `4853f6713bd6b42b509c4f26085b90c2860156695af8c70f247fa35269400044` |

Current branch baseline: `704675a348f188961ec4e4dcd335f4d931e4829b`.
Original fragment dependencies and r3 source correspondence remain as recorded
in the r3 contract and outcome. Do not modify `ControlSyntax.lean` or broaden
the frozen interface.

## Exact repair lease

One implementer owns only these paths:

- `notes/theory/lean/YulangClosure/ControlTyping.lean`
- `notes/theory/lean/YulangClosure/ControlComposition.lean`
- `notes/theory/lean/YulangClosure/CoreControlBridge.lean`
- `tasks/agent-loop/inbox/20261025-lean-core-control-repair.md`

The writer may repair the four identified blockers and directly resulting
elaboration errors while preserving all theorem statements' source domains,
transition constructors and suffix quantifiers. Make `SegmentTyped` a
Prop-valued syntax-directed judgment that retains the original source state,
syntax, suffix and typing evidence without informative Prop projections. The
`Ty.original` equality issue may be resolved locally; a repository search found
no caller of `DecidableEq Control.Ty` beyond its derivation. Explicitly
discharge the impossible `.originalValue` response case and destructure the
Control state before using head/stack equalities in `segment_progress`.

The writer does not run Lean/Lake, tests, Cargo, or native probes; Luna owns the
serialized check and all generated `.lake` files. Stop at any semantic or
interface contradiction and return it without changing the r3 contract.

## Resources, evidence and review

The r3 allocation reserved 3,400 seconds across implementation, proof, source
correspondence and review. The primary's new checker receipt used 4.7 seconds.
At most 195.3 seconds remain under the frozen 3,600-second r3 cap. This
continuation reserves at most 90 seconds for repair, 60 seconds for Luna's
serialized pinned checks, and 40 seconds for a fresh independent compiler
referee review (190 seconds total); preserve the remaining 5.3-second reserve.
Charge each full grant when issued; actual duration stays UNKNOWN if not
reported. No Astra or source/native worker is allocated in this continuation.

After the writer freezes all four leased paths and stops, Luna checks
`YulangClosure.CoreControlBridge` and the root module with the pinned toolchain,
`-j1 -M1024`, within the 60-second allowance. Luna owns any root import and
axiom-audit additions. On successful checking, record axiom output for
`successor_coverage`, `machine_finite_coverage`, and `finite_closed_safety`;
scan the accepted bridge and dependencies for `sorry`, `admit`, unsafe proofs,
project axioms and native decision escapes. Do not treat scheduling checks or
green Lean files as proof of source/native or original A/B closure.

Then obtain a fresh, nonauthor compiler referee on the exact frozen repaired
hashes and checker receipts. The review must inspect the actual theorem
domains, all embedded-family successors, suffix retention, return substitution,
finite trace split, axiom output and proof-hole scan. Any blocker keeps bridge
acceptance OPEN. Full source initialization, all constructors, source/native,
inference coverage/principality/termination and original A/B remain OPEN.

Falsifiers: any changed source transition; lost/reordered suffix or syntax;
erased typing evidence; narrowed source or suffix quantifiers; an unexplained
successor; reliance on an unproved body-safety premise; or any remaining Lean
error, hole, unsafe proof, project axiom or native decision escape.

Luna remains sole owner of current state, outcome, root imports, review
adjudication, explicit Git staging, commits and non-forced pushes. The
three unrelated UNKNOWN_QUARANTINED reservations remain untouched. Next
dispatcher consultation is at a new proof/interface obstruction, the frozen
review seam, or this resource boundary.
