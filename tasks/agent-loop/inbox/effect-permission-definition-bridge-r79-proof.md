# R79 constructive proof handoff — candidate revision 1, unchecked

Assignment R79-PROOF, worker `/root/r79_proof`, no descendants. Exact writes: `notes/theory/lean/YulangClosure/CollectedDefinitionBridgeR79.lean` and this handoff. No other path was written. Baseline `7b9573c98cb29c594ece49f4268c887998176f76`; contract `tasks/agent-loop/sprints/effect-permission-definition-bridge-20261031-r79.md` SHA-256 `38f6b80a6466f51cc68b7c7e155313730d353357ec47ad2464680babe9656189`. Frozen inputs are in that sprint's inputs-r1 manifest. Effective model/effort metadata is UNKNOWN.

## Original claim and governing sources read

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` sections 1, 3, 5; whole-language target `docs/yulang-whole-proof-closure-ja.md` sections 1 and 4. Governing corrections: `notes/design/2026-10-11-yulang-inference-top-level-principles.md` sections 1–5 and `notes/design/2026-10-24-birth-level-scc-intrusion.md` sections 2–6. The parent quantifies every supported source program and lawful finite history, preserving original scope, full Call/effect evidence and one joint strategy/witness. This packet supplies a finite identity-bridge candidate only. It leaves original A/B, soundness, principality, progress, termination, full source/native correspondence and production OPEN. Research drafts confer no semantic authority; Contracts/CoreComposition's LocalLaws and proposition definitions do not instantiate source judgments.

Read skill `.agents/skills/yulang-lean-proofs/SKILL.md`, its sources/execution references, root AGENTS/base map, goal-driven sprint rules, design-authority rule, selected sprint/manifest, Lean project configuration and README, literal R77/R78 modules, R78 independent rejection, R66 sourceProbe/Incidence/Root and actual compiler definitions. Source API reference: installed Lean 4.35.0 `src/lean/Init/Data/List/Lemmas.lean` and `Nat/Range.lean` for filter/map/zipIdx membership.

## Source mapping and construction

`yu-hir/src/module.rs` DefId (module identity, spelling, same-name ordinal), HirBinding.id/definition_root, HirModule.owns_definition_root; `yu-solver/src/lib.rs` DefinitionOrderId (artifact pointer and admitted-binding ordinal), CollectedDefinition, ConstraintBatch retained HIR/root/definition indexes, collection-time temporary definition_by_hir_id and endpoint resolution. R78 independent review identifies the missing nominal bridge at both target consumers. The current Rust author owns the replacement lookup; this proof does not modify compiler files.

`HirDef` and `CollectedDef` are different Lean structures. Nat fields model exact identity tokens; no equality, cast, spelling fallback or ordinal-only comparison crosses these types. `locatedBindings` enumerates all admitted bindings of all retained HIRs in order. `candidates` counts every exact-HirDef competitor, then `lookup` validates the unique binding through the root-position and retained record chain. `RowChecks` verifies exact owner artifact, root/HIR position, record root, full collected artifact+ordinal and reverse definition index. Malformed unrelated bindings remain in the inventory but do not reject another lookup. The model scans competitors before row validation; Rust can validate during its scan because only the final Option result, rather than diagnostic order/cost, is represented. Association lists model finite map contents; duplicate map keys fail closed, whereas a HashMap cannot represent duplicate keys.

`collectionMap` independently synthesizes full collected IDs from the source admitted-binding order. `OrderedRoots` is the explicit structural collection invariant that the retained root-position table agrees with that order. It assumes neither target-ID equality nor agreement of lookup results. `lookup_agrees_with_collection_map` proves membership; `collection_map_target_unique` proves every collection-map target for that exact query equals the computed result. `fixture_ordered_roots` constructs this invariant for the finite witness. General authenticated extraction of OrderedRoots from Rust collection remains an external correspondence obligation, not silently proved by this module.

## Declaration types and parent application

Every declaration is qualified by `YulangClosure.CollectedDefinitionBridgeR79`.

- `singleton_eq_some`: singleton parser succeeds iff the entire list is exactly that singleton.
- `check_row_sound`: computed row-check success gives actual indexed records and RowChecks.
- `lookup_sound_and_unique`: any computed successful lookup has exactly one exact-ID binding and an authenticated record chain.
- `located_provenance`: every flattened located binding comes from the indexed retained HIR and its actual binding inventory.
- `lookup_preserves_exact_coordinates`: preserves the exact HIR owner, binding ID/root, HIR position, root map index, definition record, full collection ID and reverse map.
- `lookup_agrees_with_collection_map`, `collection_map_target_unique`: under the explicit collection-order invariant, the computed target is exactly the unique collection-time target.
- `duplicate_exact_bindings_reject`, `absent_exact_identity_rejects`, `wrong_collection_artifact_rejects`: generic rejection results, including same local ordinal from a foreign batch.
- `bridged_capture_applies_r78`: uses a target computed by lookup, encoded as Key.source of the complete CollectedDef, in literal R78 capture; preserves the same complete calls list, Name/use versus Apply/checking coordinates, exact use, R65 plan, actual R66 ownerSelection and parameter recipe. No HirDef/CollectedDef identity equality is assumed.
- Four finite theorems construct the ordered bridge, distinguish equal spelling with distinct exact identities, and reject wrong batch artifact/ordinal, root ownership, HIR position, record root/reverse map, duplicate root map or exact-ID bindings, repeated HIR inventories and foreign-module same-name identity. An unrelated malformed binding is retained and does not defeat the valid first binding.

First remaining parent premise: authenticated Rust-to-Lean inventory/OrderedRoots extraction, then genuine R66 sourceProbe/Incidence with OwnerReads/Identity/permission/receipt/positive-function-child and genuine Root/physical joins. Owner: primary source/native integration. Whole-language constructor coverage and original shared semantic witnesses remain independent obligations. R78's full complete-call inventory is passed unchanged through bridgeCapture; no new call filter occurs.

## Execution and resource record

Outcome class: candidate / constructed-but-unchecked. No Lean, Lake, checker, version invocation, Rust compiler, test, build, formatter, cache, target, scratch, environment or worktree was run/created. Only read commands and the two leased file writes occurred. No Git operation. Pinned project configuration read: Lean 4.35.0, -j1/-M1024, no external packages. No actual theorem-type output, exit status or axiom census exists yet. The bundled checker is incompatible with this packet's explicit Lake/build/output prohibition; the permitted alternative is the exact stdin slice below. Standard axioms must be reported from actual output, not inferred from source.

At most two separately authorized stdin invocations (120 seconds each) belong to primary. No invocation is authorized by this candidate proposal. Exact executable `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, pinned SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; args `-j1 -M1024 --stdin`, LEAN_NUM_THREADS=1, cwd `notes/theory/lean`. Full stdout/stderr, hashes, command/exit/elapsed and any failed evidence must be retained here after primary authorization; no stale olean/import closure claim follows from slices.

Module bytes: 15442; SHA-256 `9860e461fb844505fbf10baa1102fc48d9cf136fdf2d0e493d8282214af9cf1b`. Proposed stdin: 74161 bytes, SHA-256 `55d0959c72c98378cc481038f64ffc6b796c850ba6466c903b0591afd91dc045`. All 15 theorem types and complete transitive axiom lists are requested. The first 14 dependency slices are R78 final slices, unchanged; the final slice contains every R79 declaration, excluding only its import line.

```json
{
  "segments": [
    {
      "path": "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean",
      "source_sha256": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
      "first_line": 12,
      "last_line": 75,
      "slice_sha256": "62f6622e56aee18a37b9ae8c0772de82154b5a2db5d6808cc7743b6545671b98",
      "slice_bytes": 1444
    },
    {
      "path": "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean",
      "source_sha256": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
      "first_line": 12,
      "last_line": 88,
      "slice_sha256": "9c82d93bc87236e7aa9bea822fd75cbe4f296ee02d81c5ac83e4ae0f11f65eeb",
      "slice_bytes": 2298
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalContextR55.lean",
      "source_sha256": "7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123",
      "first_line": 10,
      "last_line": 154,
      "slice_sha256": "cdbc3c9afbe6bc9fadd5543bdb400343440c6582fbf108e9b2f92c3bf2aa0c82",
      "slice_bytes": 6344
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "source_sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63",
      "first_line": 6,
      "last_line": 34,
      "slice_sha256": "8af4d69ded66f267115ae7622e7fe663b2ef33cd6e0cee5d5cbdc0cfe331db05",
      "slice_bytes": 1356
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "source_sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63",
      "first_line": 785,
      "last_line": 801,
      "slice_sha256": "8d268cf72a44da0ca6c28ea413986883a2c5a618fcb071c4e588da36dff14c34",
      "slice_bytes": 1417
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 10,
      "last_line": 41,
      "slice_sha256": "3fd09684a169ff331579d7e0faf4ba045e590e3c62ecc3c1c9a0dd96c94d717d",
      "slice_bytes": 669
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 43,
      "last_line": 45,
      "slice_sha256": "73a909efee11b7b5ed8c763a3d4ac22bff169f24a081eaf7946d3e291a9b527b",
      "slice_bytes": 175
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 52,
      "last_line": 66,
      "slice_sha256": "342ca11b82022512e1af286984dd3e34b5b5f640e60032a981080224bd22f0b8",
      "slice_bytes": 648
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 215,
      "last_line": 226,
      "slice_sha256": "c6ba0292d1900c6d344014640f60c76015327025e70c1a1cafc0cb0aed5874a0",
      "slice_bytes": 539
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 246,
      "last_line": 251,
      "slice_sha256": "cd6b69b54ba338acfeaff738f60ab81ce7d118ea3d2b8d9910c83d1a0e1c19da",
      "slice_bytes": 330
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 417,
      "last_line": 419,
      "slice_sha256": "d03134598123298a949bc59da11760329d19b9582160f3581ccec39099f77945",
      "slice_bytes": 230
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedConsumerR66.lean",
      "source_sha256": "5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1",
      "first_line": 14,
      "last_line": 33,
      "slice_sha256": "c13495d0114d9499fc076b956dce9b5d9cdf6489123387f98b5886d4f0c0c106",
      "slice_bytes": 1047
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_sha256": "0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682",
      "first_line": 3,
      "last_line": 548,
      "slice_sha256": "1b5aead5f58864f47bc038147199dbaeabf8906ec31033b1b9c03d532600ec2b",
      "slice_bytes": 28682
    },
    {
      "path": "notes/theory/lean/YulangClosure/IntegratedSourceAlignmentR78.lean",
      "source_sha256": "bfe304c33e6018910739d58d37c2122a4a475fac57e00091e1a700a965510029",
      "first_line": 3,
      "last_line": 175,
      "slice_sha256": "3d9cc5038f232329b00811dd74c77ad52708ebae491edda74dc059dc4af784b0",
      "slice_bytes": 10680
    },
    {
      "path": "notes/theory/lean/YulangClosure/CollectedDefinitionBridgeR79.lean",
      "source_sha256": "9860e461fb844505fbf10baa1102fc48d9cf136fdf2d0e493d8282214af9cf1b",
      "first_line": 3,
      "last_line": 308,
      "slice_sha256": "9fcdbdcb0c3993f56bd129def9e4520afb2a98bdc916470639e1f992fbc1b507",
      "slice_bytes": 15391
    }
  ],
  "theorems": [
    "YulangClosure.CollectedDefinitionBridgeR79.singleton_eq_some",
    "YulangClosure.CollectedDefinitionBridgeR79.check_row_sound",
    "YulangClosure.CollectedDefinitionBridgeR79.lookup_sound_and_unique",
    "YulangClosure.CollectedDefinitionBridgeR79.located_provenance",
    "YulangClosure.CollectedDefinitionBridgeR79.lookup_preserves_exact_coordinates",
    "YulangClosure.CollectedDefinitionBridgeR79.lookup_agrees_with_collection_map",
    "YulangClosure.CollectedDefinitionBridgeR79.collection_map_target_unique",
    "YulangClosure.CollectedDefinitionBridgeR79.duplicate_exact_bindings_reject",
    "YulangClosure.CollectedDefinitionBridgeR79.absent_exact_identity_rejects",
    "YulangClosure.CollectedDefinitionBridgeR79.wrong_collection_artifact_rejects",
    "YulangClosure.CollectedDefinitionBridgeR79.bridged_capture_applies_r78",
    "YulangClosure.CollectedDefinitionBridgeR79.fixture_ordered_roots",
    "YulangClosure.CollectedDefinitionBridgeR79.finite_constructed_bridge",
    "YulangClosure.CollectedDefinitionBridgeR79.finite_rejects_corrupt_coordinates",
    "YulangClosure.CollectedDefinitionBridgeR79.finite_unrelated_malformed_binding_retained"
  ],
  "stdin_bytes": 74161,
  "stdin_sha256": "55d0959c72c98378cc481038f64ffc6b796c850ba6466c903b0591afd91dc045"
}
```

Exact reconstruction uses `parts = [b'import Std\n']`, wraps the first 12 segments exactly as the R78 handoff recipe (close each changed namespace; explicitly open R66 with `open ProviderNativeContextR57`), closes final R66, appends segments 13–15 verbatim, then appends `b'\nset_option pp.universes true\nset_option pp.fullNames true\n'` and `f'#check @{name}\n#print axioms {name}\n'.encode()` for every listed theorem. No implicit separators or output files. The R78 recipe's loop boundary changes from `segments[:-2]` to `segments[:12]`, and its full-module loop to `segments[12:]`.

Submission R79-PROOF / revision 1. **WRITES STOPPED** after this handoff is frozen. No descendants, generated outputs or scratch leases. Await primary exact-input freeze/committed authorization; no self-certification or independent-review claim.
