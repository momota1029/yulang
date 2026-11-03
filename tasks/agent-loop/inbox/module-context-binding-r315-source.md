# R315 source/native handoff — revision 2

Sprint contract: `tasks/agent-loop/sprints/module-context-binding-r315.md`,
SHA-256 `00e98ec431011a89bd42ffd0ea872bc0a631880f34206004786917b9a55953fd`.
Baseline `a87db9a8e`; assignment `R315-SOURCE-NATIVE`; parent remains the
unchanged R159 claim. Requested model/effort Luna/high; observed model, effort,
runtime session and active seconds UNKNOWN. Worker `/root/r315_module_native`;
no descendants.

## Outcome

Extended the existing R314 accepted-run exporter in test-only code. The single
artifact is emitted from the same `Machine`, retained HIR, parse and return
snapshot used by the R314 test. `R314Artifact` contains the actual `relay`
source rows, runtime events and return snapshot. `R315MakeArtifact` contains
the complete `make` local-source root, source nodes, formals and annotations.
`R315Artifact` joins its declaration to the executed `make` Name use and
materialized definition cell.

The module inventory follows actual `HirModule.items()` order and records
every binding's DefId payload, DefinitionRoot identity, declaration key/range,
realm, path, HIR visibility, source-index public flag, root annotation Option
and runtime cell. `make` is `Private` and `sourceIndexPublic = false`; its
publication here is the runtime module definition cell, not a public import.
The actual use is a `ModuleDef(make)` at the `relay` source coordinate, in the
`relay` parameter environment. It resolves through `definition_indices` to the
same global cell; no lexical `Machine::lookup` entry for `make` is asserted.
The cell contains the `make` value closure with matching source root, formal,
body label, value interface and initializer environment. The exporter now
requires the supplied return snapshot to be pointer-identical to the snapshot
owned by that Machine, and verifies the cell's actual `ReceivedValue.interface`
is `Value` before emitting the value interface. Use environment, parent
binder, and dispatch context are serialized from that same Return snapshot.
`R314Artifact.runId`, `ReturnSnapshot.runId` and
`R315Artifact.makeBindingUse.runId` use the same existing Machine-pointer
identity written during one exporter call. This is only same-process evidence,
not a cross-process identity.

Source/code validation retains and checks `Operation`, `Block`, and
`StatementBlock` links. Expression statements remain expression statements;
binding statements preserve source ordinal, local binder id and initializer
label. Wrong source ownership, wrong code resolution, missing or duplicate
`make` declarations, missing definition cells, uninitialized cells and
mismatched provider roots fail closed. The source adapter previously failed
closed on the actual `StatementBlock`; typed serialization and source/code
pair checks cover it.

## Frozen evidence and checks

- Lean-readable artifact: `/tmp/yulang-r315-native/module-context-binding-r3.lean`,
  SHA-256 `de228fdc6b984373048107ff1bc69a25620dea6a36cb3340f143b6b161f6fc95`.
  R2 and R3 are byte-identical after normalizing the ephemeral `runId` pointer
  value. R1 was rejected by the proof check for a missing namespace close and
  unqualified R314 schema constructors. R2 fixed those issues; R3 keeps the
  same schema and incorporates native-only validation/test changes.
- Current source hashes: `program.rs`
  `2c03ff8681c50520e0527f139a86ac8427097c27aeafcf247e76673310be4b0c`,
  `machine.rs`
  `c21a014fba4249e88f3f2d859031222860be4b8972b075c7653a94b8db08cfd9`,
  `dispatch.rs`
  `d99acad3e344bc06970faf0486ff7d10ba92bc7514cfb7eec58df8bbb28f6360`.
- Direct frozen R314 input hashes remain those in the sprint contract. Source
  and return-snapshot conventions reuse the R314 source/native handoff revision
  4 and its independent review. R314's omission of the `make` declaration
  inventory and use-to-global-cell join was not treated as evidence for this
  R315 edge.
- Focused command:
  `YULANG_R315_LEAN_WITNESS=/tmp/yulang-r315-native/module-context-binding-r3.lean cargo test --locked --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib`
  — 1 passed. It includes same-length altered-source, foreign-parse, and
  second-Machine snapshot rejection. New R315 negative cases reject a cloned
  snapshot, a snapshot owned by a separately executed Machine over the same
  HIR, and a snapshot whose `make` cell interface alone was changed to
  `Computation`.
- `git diff --check -- tools/inference-playground/src/runtime/program.rs
  tools/inference-playground/src/runtime/machine.rs
  tools/inference-playground/src/runtime/dispatch.rs` — passed.
- Dedicated mutation cases for altered DefId/realm/scope and duplicate-name
  ambiguity are not implemented; the exporter currently checks the actual HIR,
  source index, ModuleDef, and inventory ownership relations on this fixture.
  Independent source/native review should decide whether those mutations are
  needed before any promotion.
- R3 has not yet been checked by Lean. The R1 proof run exposed an annotation
  domain seam: emitted binding annotation has type
  `Option R314Artifact.Annotation`, while the unchanged parent proof's source
  constructor uses `Option OriginalSource.Annotation`. The fixture's outer
  `make` annotation is explicitly `none`; the proof lane must preserve that
  source-domain distinction and report any unresolved conversion.

The frozen artifact is a finite source/native witness, not a proof that the
runtime cell implements the original mathematical Context or closes the R159
parent. The proof owner must check the generated Lean module against the
unchanged parent. The evidence establishes a private same-module runtime
binding, not imported/public publication. `q_c`, independent arms, semantic
Return, Checking and admission remain open.

## Provisional boundary and ownership

All event observation, serialization, run-id output, guards and mutation tests
are `#[cfg(test)]`; runtime decisions and public APIs do not change. Falsifier:
any mismatch in exact source/code pairing, HIR DefinitionRoot/DefId,
module-item order, source-index declaration coordinates, ModuleDef use,
definition cell/interface, provider source root, or Machine-owned snapshot
invalidates this finite export. Luna owns cleanup after independent
source/native review and proof consumption. Exporter and witness remain
provisional; no cutover is authorized.

Repository writes are confined to the three leased Rust files and this handoff; `dispatch.rs` was unchanged.
Scratch under `/tmp/yulang-r315-native`: R1/R2/R3 Lean artifacts, R2 check
artifact, normalized comparison files, and preserved R1 handoff. Cargo used the
workspace `target/` as generated scratch and it was not manually cleaned. No
Git operations or dependency edits. Worker writes stopped after revision 2
was frozen; no process remains active.
