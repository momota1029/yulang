# R81 proof handoff — revision 1, constructed but unchecked

Worker `/root/r81_proof`; baseline `661b40348a712120f921cc4dbcbbbce2e467821e`. Exact writes: `notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean` and this handoff only. No descendants, Git actions or shared records edited. Contract SHA-256 `33e8f586a6c033af19050d5855c2976058a102c400a4105807097639f199bff4`; frozen-input manifest SHA-256 `b70d608d22e0544c9171462bf704a7142f2ee113cecb2c54783b08c1a860ec87`. Effective model/effort telemetry UNKNOWN. Writer freezes at this submission.

## Original obligation and governing source

Read root AGENTS/base invariants, goal-driven sprint rules, exact R81 contract, Lean skill and both references, actual R45/R55/R65/R66/R77/R79 definitions, R80 source/review and retained audit-2 diagnostics, pinned Lean configuration and relevant README. Original manuscript `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5 retains every supported original source program, lawful finite construction history, actual extrusion occurrence and polarity pair, original lexical/type/event scopes and one shared witness/strategy. Corrections are the 2026-10-11 top-level principles and authoritative 2026-10-24 birth-level SCC decision §§2–6. Whole-language target: `docs/yulang-whole-proof-closure-ja.md` §§1,4. These parent statements are unchanged and OPEN. Drafts supply no semantic authority.

This packet repairs the exact R80 finite-record application to existing R66 `Incidence`: computed R77 aligned choice → native records → actual R45 owner/identity equations → parameter recipe → R66 probe agreement → `Incidence`. The R66 type, input inventories, primitive hypotheses, permission and coordinates are unchanged. Name/use=100 and Apply/checking=102 stay distinct; slot-0 and slot-2 readers count the complete provenance keys before fact identity. Registration selection precedes Function/entry images; formal native root=700 remains separate from Lambda recipe root=300. Exact annotation/row and duplicate concrete entries [7,7,11] remain retained.

## Diagnostic repairs

The retained R80 audit2 includes an earlier `error(lean.synthInstanceFailed)` at flattened line 1692: synthesis of `Decidable (PrimitiveRecords ...)` failed. R80 review summarized later symptoms but omitted this first failure. Its rejected instance left error-recovery terms in the decision procedure, so `decide` over later constructions could not reduce. This packet preserves R80 byte-for-byte and repairs the same 29 primitive checks under a *local* `synthInstance.maxSize 512` elaboration bound (default is 128 in pinned `Lean/Meta/SynthInstance.lean`). There is no evaluator, proposition, accepted source domain, kernel-check bypass or process resource change.

Role and receipt-kind conversion proofs now explicitly expose the finite constructor maps and rewrite their exact native equalities. Probe agreement first `change`s to reader-normal form, including reduced request/use coordinates and the dependent `if` decision, then uses restricted simplification of the computed R77 equations. This avoids R80's failed `rw` motive containing an unreduced request-specific Decidable term.

The successful witness is now explicit: `fixtureChoiceWitness`, `fixtureAlignedWitness`, `fixtureRecords` and `fixtureOutput`. `finite_aligned_reader` and `finite_native_reader` equate actual computed readers to these data. `finite_primitive_records` checks all original primitives on that one witness; `fixtureOutput` uses the real `assemble`. `finite_constructs_output` proves actual `construct` returns that precise output, from which the unchanged nonempty and permission/root theorems follow. Rejection data/statements are unchanged: local/global Lambda mismatch, foreign shared images, permission registration/annotation substitutions, parameter and Lambda recipe changes, duplicate slot-0/slot-2 provenance and parameter-root substitution.

## Exact theorem surface

All names below are in `YulangClosure.ConstructedSourceIncidenceR81`; arbitrary S,T use their original DecidableEq instances. The following are literal source signatures, not printed kernel output. `constructed_applies_r45` takes an already inhabited `Constructed`; `bridged_target_in_collection` takes `BridgedConstructed` and R79 `OrderedRoots`. Their conditional status does not establish construction or extraction. All twelve theorems are included in the proposed type/axiom audit.

```lean
theorem primitive_records_derive_fields (s : Source S T) (inventory : Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)
    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :
    InternalPermissionIncidenceR45.OwnerReads
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (request u receiving target c annotation row) (projected c d) ∧
    InternalPermissionIncidenceR45.Identity
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (request u receiving target c annotation row) (projected c d) ∧
    s.parameterRecipes[(projected c d).formal.recipe]? = some (projected c d).formal.parameter

theorem primitive_records_derive_source_probe (s : Source S T) (inventory : Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)
    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :
    OccurrenceQualifiedConsumerR66.sourceProbe s inventory
      (request u receiving target c annotation row) = some (projected c d)

theorem constructed_applies_r45 (s : Source S T) (inventory : Inventory S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target annotation row : Key S T)
    (out : Constructed s inventory source calls u receiving target annotation row) :
    PeelsTo source.expressions out.aligned.alignment.call.callee u.occurrence target ∧
    InternalPermissionIncidenceR45.extract
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (request u receiving target out.aligned.choice annotation row) out.incidence.probe =
      some (InternalPermissionIncidenceR45.certificate
        (request u receiving target out.aligned.choice annotation row) out.incidence.probe)

theorem bridged_target_in_collection (b : CollectedDefinitionBridgeR79.Batch)
    (ordered : CollectedDefinitionBridgeR79.OrderedRoots b)
    (query : CollectedDefinitionBridgeR79.HirDef)
    (s : Source CollectedDefinitionBridgeR79.CollectedDef Nat)
    (inventory : Inventory CollectedDefinitionBridgeR79.CollectedDef Nat)
    (source : OwnerSource (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (calls : List (SourceCall (Key CollectedDefinitionBridgeR79.CollectedDef Nat)))
    (u : Use Nat (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (receiving annotation row : Key CollectedDefinitionBridgeR79.CollectedDef Nat)
    (out : BridgedConstructed b query s inventory source calls u receiving annotation row) :
    (query, out.target) ∈ CollectedDefinitionBridgeR79.collectionMap b

theorem finite_aligned_reader :
    constructAligned fixture fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse
      (.source 10) (.source 1) = some fixtureAlignedWitness

theorem finite_native_reader :
    readRecords fixture SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1)
      fixtureChoiceWitness = some fixtureRecords

theorem finite_primitive_records :
    PrimitiveRecords fixture fixtureInventory SourceInternalChoiceR77.fixtureUse
      (.source 10) (.source 1) fixtureChoiceWitness fixtureRecords (.source 6) (.source 5)

theorem finite_constructs_output : fixtureResult = some fixtureOutput

theorem nonempty_successful_finite_witness :
    fixtureResult.isSome = true ∧ SourceInternalChoiceR77.fixtureUse.occurrence ≠ fixtureCall.checking ∧
    ProviderNativeContextR57.fixtureFormal.nativeRoot = some 700

theorem finite_permission_and_root_identity :
    match fixtureResult with
    | none => False
    | some out => out.incidence.probe.permission.concrete = [.source 7, .source 7, .source 11] ∧
        out.incidence.probe.registeredRoot = 300 ∧ out.incidence.probe.registeredRoot ≠ 700

theorem local_global_and_shared_foreign_rejected :
    (SourceInternalChoiceR77.constructAligned mismatchedLocalGlobal fixtureSource fixtureCalls
      SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1)).isSome = true ∧
    (construct mismatchedLocalGlobal fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse
      (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    SourceInternalChoiceR77.foreignOrigin.function = ProviderNativeContextR57.fixtureConstruction.function ∧
    SourceInternalChoiceR77.foreignOrigin.entryEffect = ProviderNativeContextR57.fixtureConstruction.entryEffect ∧
    (construct SourceInternalChoiceR77.foreignSource fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse
      (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false

theorem adversarial_inventories_rejected :
    (construct {fixture with constructions
```

## Verification boundary and remaining premises

No Lean/Lake/checker/version invocation, compiler, Cargo, tests, builds, formatter, cache/target/scratch output, environment or worktree was used/created. Pinned project files specify Lean 4.35.0, -j1/-M1024, no external packages. Only primary may separately authorize the ≤120s exact stdin audits; this handoff authorizes none. No theorem has fresh kernel acceptance or printed axioms yet. Expected transitive axioms are only standard `propext`, `Quot.sound`, possibly `Classical.choice`; the audit must print actual complete lists for all twelve declarations and reject any `sorryAx` or project/native-evaluation axiom. No `sorry`, `admit`, project axiom or checker bypass is present in this candidate. No new known mathematical obstruction; elaboration remains unchecked until primary audit. Preserve actual failure evidence if any audit fails.

The skill helper/Lake path is unavailable within this packet's no-build/no-cache restriction; primary owns the bounded in-memory stdin process and exact receipt. Parent application `assemble` returns literal R66 Incidence, with R45 acceptance on the same permission; `constructBridged` preserves R79's typed HIR→collected identity lookup. The first remaining R66 Root premise is `sameArtifact`, then exact native entry-row equality and actual `BeforeAncestry` physical/current-slot/admission/relation/source-root records. Owner: primary source/native lane. Authenticated extraction, R79 OrderedRoots, physical/ancestry identity joins, compiled Rust behavior, Lake import closure, original A/B and whole-language soundness/principality/progress/termination and production stay OPEN. Finite Internal records omit none of those cases from the parent obligation.

## Exact proposed stdin manifest

Construction: start `import Std\n`; append every segment's UTF-8 `before`, inclusive literal source lines with line endings preserved, and UTF-8 `after`; append `\nset_option pp.universes true\nset_option pp.fullNames true\n`; for each theorem append `#check @{{name}}\n#print axioms {{name}}\n`. No other separators or files. Reauthenticate full-source and slice hashes before use. Module bytes 25638 SHA-256 `baba8d0dce9e75dfeb24d5eb6dcf381ec6b103ddaf8aac5b803fcc59142f7c4b`. Proposed stdin bytes 107431 SHA-256 `35a379150757ec307d17da62048d64de23ab6e9c014183e1ac5a79bd99daedd6`.

```json
{
  "segments": [
    {
      "path": "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean",
      "source_sha256": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
      "first_line": 12,
      "last_line": 95,
      "slice_sha256": "8fd38c41a50b0238bb7e9ce602a98ccbdc0740031158e0c96bf17de15e69a041",
      "slice_bytes": 2328,
      "before": "",
      "after": "\nend YulangClosure.ComputationPermissionEntryR39\n"
    },
    {
      "path": "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean",
      "source_sha256": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
      "first_line": 12,
      "last_line": 166,
      "slice_sha256": "16ee83e0ef774bfc3e9795720cda25e9b42609867853a59c8879469ea8f33104",
      "slice_bytes": 6461,
      "before": "",
      "after": "\nend YulangClosure.InternalPermissionIncidenceR45\n"
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalContextR55.lean",
      "source_sha256": "7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123",
      "first_line": 10,
      "last_line": 154,
      "slice_sha256": "cdbc3c9afbe6bc9fadd5543bdb400343440c6582fbf108e9b2f92c3bf2aa0c82",
      "slice_bytes": 6344,
      "before": "",
      "after": "\nend YulangClosure.SourceInternalContextR55\n"
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "source_sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63",
      "first_line": 6,
      "last_line": 34,
      "slice_sha256": "8af4d69ded66f267115ae7622e7fe663b2ef33cd6e0cee5d5cbdc0cfe331db05",
      "slice_bytes": 1356,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "source_sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63",
      "first_line": 785,
      "last_line": 801,
      "slice_sha256": "8d268cf72a44da0ca6c28ea413986883a2c5a618fcb071c4e588da36dff14c34",
      "slice_bytes": 1417,
      "before": "",
      "after": "\nend YulangClosure.ProviderNativeContextR57\n"
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 10,
      "last_line": 66,
      "slice_sha256": "d1802c0ee9d284c4676c45635fc3f873197a2f2d5064b8baf9279c2c2965d7e4",
      "slice_bytes": 1839,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 215,
      "last_line": 226,
      "slice_sha256": "c6ba0292d1900c6d344014640f60c76015327025e70c1a1cafc0cb0aed5874a0",
      "slice_bytes": 539,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 246,
      "last_line": 251,
      "slice_sha256": "cd6b69b54ba338acfeaff738f60ab81ce7d118ea3d2b8d9910c83d1a0e1c19da",
      "slice_bytes": 330,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 398,
      "last_line": 408,
      "slice_sha256": "c7b16f4581fb93737dc18b5d1945c559f5e0b9f019f478b821e1a0536d5aa3da",
      "slice_bytes": 723,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "source_sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "first_line": 417,
      "last_line": 419,
      "slice_sha256": "d03134598123298a949bc59da11760329d19b9582160f3581ccec39099f77945",
      "slice_bytes": 230,
      "before": "",
      "after": "\nend YulangClosure.OccurrenceQualifiedFactReadersR65\n"
    },
    {
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedConsumerR66.lean",
      "source_sha256": "5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1",
      "first_line": 14,
      "last_line": 55,
      "slice_sha256": "5c98d6191932ed53c0a465e8d3d3c4d14ef8c6ddd259e0308d574509d8190938",
      "slice_bytes": 2855,
      "before": "namespace YulangClosure.OccurrenceQualifiedConsumerR66\nopen ProviderNativeContextR57\n",
      "after": "\nend YulangClosure.OccurrenceQualifiedConsumerR66\n"
    },
    {
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_sha256": "0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682",
      "first_line": 3,
      "last_line": 548,
      "slice_sha256": "1b5aead5f58864f47bc038147199dbaeabf8906ec31033b1b9c03d532600ec2b",
      "slice_bytes": 28682,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/IntegratedSourceAlignmentR78.lean",
      "source_sha256": "bfe304c33e6018910739d58d37c2122a4a475fac57e00091e1a700a965510029",
      "first_line": 3,
      "last_line": 175,
      "slice_sha256": "3d9cc5038f232329b00811dd74c77ad52708ebae491edda74dc059dc4af784b0",
      "slice_bytes": 10680,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/CollectedDefinitionBridgeR79.lean",
      "source_sha256": "6dff2ab5f1a5f2403822c180c21074cc1a063ed84b697bd484017705d53222ac",
      "first_line": 3,
      "last_line": 313,
      "slice_sha256": "c29d67b3651f70c90492f7ee1ae81569410ee984af7dad56305277f4d3db8aaa",
      "slice_bytes": 15573,
      "before": "",
      "after": ""
    },
    {
      "path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_sha256": "baba8d0dce9e75dfeb24d5eb6dcf381ec6b103ddaf8aac5b803fcc59142f7c4b",
      "first_line": 3,
      "last_line": 411,
      "slice_sha256": "71c82389e179e4aef7d90b8bd5b63bbb6d066c97afd581ab25ae9573967beb42",
      "slice_bytes": 25587,
      "before": "",
      "after": ""
    }
  ],
  "theorems": [
    "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_fields",
    "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
    "YulangClosure.ConstructedSourceIncidenceR81.constructed_applies_r45",
    "YulangClosure.ConstructedSourceIncidenceR81.bridged_target_in_collection",
    "YulangClosure.ConstructedSourceIncidenceR81.finite_aligned_reader",
    "YulangClosure.ConstructedSourceIncidenceR81.finite_native_reader",
    "YulangClosure.ConstructedSourceIncidenceR81.finite_primitive_records",
    "YulangClosure.ConstructedSourceIncidenceR81.finite_constructs_output",
    "YulangClosure.ConstructedSourceIncidenceR81.nonempty_successful_finite_witness",
    "YulangClosure.ConstructedSourceIncidenceR81.finite_permission_and_root_identity",
    "YulangClosure.ConstructedSourceIncidenceR81.local_global_and_shared_foreign_rejected",
    "YulangClosure.ConstructedSourceIncidenceR81.adversarial_inventories_rejected"
  ],
  "stdin_bytes": 107431,
  "stdin_sha256": "35a379150757ec307d17da62048d64de23ab6e9c014183e1ac5a79bd99daedd6"
}
```

R81-PROOF/r1: construction only; WRITES STOPPED / frozen for primary audit and independent review. Only the two exact leased files were written; no scratch/generated outputs. Construction elapsed approximately 12 minutes, within the 1,200-second author bound; actual model/resource telemetry otherwise UNKNOWN.
