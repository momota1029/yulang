# R9 independent review

Verdict: **ACCEPT for the R9 conditional transcription only.** No blocking or major finding remains within this packet.

## Authenticated artifact and audit

The frozen artifact `notes/theory/lean/YulangClosure/FormalPermissionSourceAllocation.lean` is 19391 bytes, SHA-256 `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a`. Its proof handoff is 8727 bytes, SHA-256 `abad2cde5603cb1e6270abb61d949b7aea9c94c51534a21ec8ad9c4ef7360ed0`. The reviewer independently authenticated all 104 manifest entries: 103 exact matches and the single authorized R7 revision-2→R9 artifact successor. All 14 isolated project copies, seven tool hashes, frozen plan, copy receipt and four raw execution receipts match their recorded hashes.

Raw stdout has all 13 ordered audit BEGIN/END markers, 13 printed theorem types, 13 transitive axiom reports and 13 PASS lines. Lean 4.35.0 focused build and audit exited 0 in 14.04 seconds with maximum RSS 973804 KiB.

Complete transitive axiom sets:

| Axioms | Declarations |
|---|---|
| none | `nonallocating_helpers_frame`, `AllocationTrace.append` |
| `propext` | `fresh_success_ordinal`, `fresh_step_equations`, `source_port_event`, `source_port_allocation` |
| `propext`, `Quot.sound` | `port_decoder`, `source_pair_decoder_correspondence`, `source_tuples_decoder`, `successful_pair_allocation_footprint`, `successful_tuples_allocation`, `successful_pair_permission_entries` |
| `propext`, `Classical.choice`, `Quot.sound` | `r5_source_allocation_instance` |

## Construction and source findings

All 13 public statements match the frozen R7 baseline after whitespace normalization. Relation constructors, availability/frame premises, polarity, tuple guards and selected source cut remain unchanged. Paired derivation induction generalizes changing indices. Eliminating `hao` before constructing the dependent result-port witness transports the complete context. Function composition preserves argument → result → argument-port → result-port order; tuple composition threads the actual head output state.

The frozen audit plan at `audit-inputs-1.json:10` retained inherited R7 handoff/contract/manifest/preflight descriptions. The immutable plan's R9 artifact, project, argv, input manifest and successor transition are correct. Supplement SHA `cbf1cc5a3d56e9aab0476ec04a292320c57119f99335bb076ec2805eca80111d` identifies the stale fields and authenticates their R9 replacements. The plan remains unchanged; this supplement sufficiently bounds the documentary discrepancy.

## Remaining boundaries

`HelperFrames` still assumes projected preservation; `FreshStep` supplies availability witnesses; the R5 theorem assumes an exact `SourcePair`. Concrete helper execution, exact-tree construction, permission-prefix preservation, Rust/native correspondence and native entry State 21 remain unproved. Original parent preservation, effect hygiene, consumer residual, unequal transport, soundness, principality, termination and production gates remain OPEN.

Read-only review. No edits, Lean/Lake/checker/Cargo/tests or descendants were run.
