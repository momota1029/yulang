# Native Value ports r4 — frozen primary author handoff

Author: `/root`. Baseline: `8472a1ca49da055a1ea298ccfa87745c2a6f5ce4`.
Independent review required; this is not self-certification.

## Frozen scope and original application

The complete explanation and source crosswalk are in
`notes/theory/2026-10-26-native-value-ports.md`. The construction supplies actual
Function/Tuple/Record/Variant child lists, complete native port keys, full deferred
demand handling, exact Context/transformer construction, and the two-phase
admission/enqueue history. It applies at the original Value-dispatch child owner;
whole native/source inference soundness remains OPEN at the exact residuals in the
note. No compiler/native/expected-output/toolchain/configuration change occurred.

`drive_success_readback` is the principal execution root: a successful finite
computation of `drive` from the original children/arena/queue constructs one list
of jobs, same-order source coverage, exact resulting queue and all corresponding
full AdmissionResult records in the same output arena. It assumes neither child
semantic success nor a completed owner. `admit_constructs` derives Context/Flow
and registered full keys from the local computed constructor. Original source
semantics and authentic native readback remain distinct obligations.

## Exact frozen hashes

| File | SHA-256 |
| --- | --- |
| `NativeValuePorts.lean` | `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa` |
| Construction note | `4f39788f4dee30f5f413b0b373965ea583892b7d07e5b95de63ccb93f2819b5b` |
| Complete origin census | `e801f97f2ae5e77505eb87751fc4c09b0d9fd5fd0132d8abb6052f7b9fc3ae22` |

## Source correspondence and residuals

All native owners, branches, retained fields and omissions are described in the
note. The snapshot contains all ValueEndpoint variants and all five ScopedDemand
fields. Child keys preserve current canonical pair, post-check Context operation,
source-set ID, full Flow and exact port indices. Function effect transformers are
constructed and their exact pointwise changes are proved. Existing NativeRecordPlan
supplies its complete scan without a new payload-safety premise. Variant duplicates
remain separate obligations. One entire raw source-order vector is reconstructed
from the actual reversed admission/front-enqueue stages.

No generic LocalLaws or full SourceT/CompleteRelation oracle is used. Raw table
lookups and input structural validity are explicit inputs/readbacks. The Arena is
a decoded-key representation; physical ScopedFlowId interning, scoped-enabled and
capacity/inventory/allocator/error behavior remain actual native refinement work.
Other Value-dispatch branches, shared mutable/committed/versioned histories and
full original semantic witness construction retain their named owners. This is not
an input-language restriction or a new source checking pass.

## Material repairs and bounded checks

Calls 01–06 were ordinary elaboration repairs: reserved identifiers, missing type
annotations, if/do normalization, case-alternative binders and record layout.
Call 07 first checked the child constructor and two-stage invariant. Call 08 fixed
Except-map branches, and call 09 fixed witness reduction for Except equality;
call 10 checked all then-current 49 roots. Review of the native Context assertion
showed that the concrete example used an unallocated post-check ID; although its
algebraic calculation was valid, that was not a valid native input example. The
example now starts with a formed Context arena and existing parent, and the new
general Context formation/ID-bound lemmas make the actual structural premise
explicit. Call 11 exposed one dependent proof rewrite error; call 12 repairs it
and checks all final 56 roots. Call 13 is the complete originating census.
All failed logs/snapshots are retained; no failure or superseded example is counted
as final correspondence evidence. A separate read-only Python census parser was
interrupted (exit130) for a greedy DOTALL header, then fixed with line-bounded names.
It changed no checker source/output. The final parser verified all blocks and roots.

Budget: 2,700 wall seconds and max20 focused calls. Used13/20. Every Lean process
used one thread and `-M1024`, an owned TMPDIR/cache and a <=119-second outer bound;
wrapper+Lake sampled aggregate ceiling1280MiB. The exact commands, logs, input
snapshots, resource usage and process IDs follow. No live checker remains.

Total checker wall seconds: 89.861396; peak sampled aggregate RSS: 1179955200 bytes.

## Complete origin inventory

```json
{
  "declarations": 891,
  "theorems": 348,
  "roots": 56,
  "all_axioms": {
    "none": 705,
    "propext": 161,
    "Quot.sound, propext": 25
  },
  "theorem_axioms": {
    "none": 235,
    "propext": 88,
    "Quot.sound, propext": 25
  },
  "root_axioms": {
    "Quot.sound, propext": 24,
    "propext": 28,
    "none": 4
  },
  "log_sha256": "e801f97f2ae5e77505eb87751fc4c09b0d9fd5fd0132d8abb6052f7b9fc3ae22",
  "replacement_characters": 0,
  "omitted_type_terms": 0
}
```

All348 originating theorem constants, including private/generated ones, have full printed types and transitive axiom reports in the appendix below. All891 originating declarations were printed in the complete census; no project axiom is allowed. The 56 authored roots are a subset, not a replacement inventory.

## Frozen inputs and exact receipts

```json
{
  "baseline": "8472a1ca49da055a1ea298ccfa87745c2a6f5ce4",
  "started": "2026-10-26T11:34:16.967866+00:00",
  "project": {
    "notes/theory/lean/.lake/R22Audit.lean": "ff63bb4a3a557699c7a88beca4d26008f7f71039eaa066a6324c4f1ae309182c",
    "notes/theory/lean/.lake/call-entry-spine-r1-check.lean": "3a51fe2832d496516071f0e677be40433a35cf046bad1d28c1a44fbbe891ac5e",
    "notes/theory/lean/.lake/call-entry-spine-r2-check.lean": "4b2722280ad703f81ce172f7426a3cc694083459f74bf14121b1cfe2d3da45ed",
    "notes/theory/lean/.lake/call-entry-spine-r3-check.lean": "5e54e62da9aeff020127b20112ccbd6e669e3cb7ff5ae03adbfffd317d2b4389",
    "notes/theory/lean/.lake/call-progress-obstruction-r3-check.lean": "c249ae83737295e01aab6c5f6397f1367c10f907ba25f22c6ebcbed0b269905d",
    "notes/theory/lean/.lake/call-unwind-r2-check.lean": "77a685433f4815977207ee32a5ba9cf49d707a993e43a29c169cb12954f0df0b",
    "notes/theory/lean/AuditExecutionProofs.lean": "aa16f7e520fc56b6694e04d42e81a6f58c0ffe64b4db30c432fb2bd77692052f",
    "notes/theory/lean/AuditInferenceProofs.lean": "b6c5e8dac8fa9d0f01f558cb82d9eb492d1112f7382038b3ff1ff62d3ff085e1",
    "notes/theory/lean/AuditProofAdvancement.lean": "95a10406b14ad9e073e17857b012c9a3c2940bac84c32e21a5fca268562a52dd",
    "notes/theory/lean/YulangClosure.lean": "3c38da4bb2e017249fa973e0ee28f243d44ba6d52b6f173ac617b605f1fce9e8",
    "notes/theory/lean/YulangClosure/BirthLevelSCC.lean": "2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0",
    "notes/theory/lean/YulangClosure/BoundaryQueryClosure.lean": "7dad22c1b94e404be5dc4aaa51203e8d3882fd4c61006eb8b0c5f6f87a30f727",
    "notes/theory/lean/YulangClosure/CallCaptureResponse.lean": "a310f3da1091a2dd7ed1d751aea67c44aefe06ce89fc9bb16cc0d19b530eb1c6",
    "notes/theory/lean/YulangClosure/CallCaptureTyping.lean": "906e8204aa155efd3f4e45d9c2a2a9fbe010858206ef3dd0acfd3d0d607a0de9",
    "notes/theory/lean/YulangClosure/CallContextTyping.lean": "09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125",
    "notes/theory/lean/YulangClosure/CallDeclaredLiteralResponse.lean": "f9c7f3b8b0c2ad0552df531a6a13ad1fb4863340bb0ea837319bf144a2bae255",
    "notes/theory/lean/YulangClosure/CallEntrySpine.lean": "6c6bd7b4c912e86196434465a94a1ada02fe1d28cc8c0e5343b247a2dd7961b6",
    "notes/theory/lean/YulangClosure/CallEntrySpineComposition.lean": "a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf",
    "notes/theory/lean/YulangClosure/CallEntrySpineRepair.lean": "ad4a2e1b49b13dc71b77b079b80b0c6c6355327915a4be343276b9b9497f7d89",
    "notes/theory/lean/YulangClosure/CallEntryTyping.lean": "21850ac899060ade9f9db5139b20e5e1779b4f18b67d6d1127501827ec146ba2",
    "notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean": "f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39",
    "notes/theory/lean/YulangClosure/CallEnvironmentRealization.lean": "8b9e4c38224f103557c5f6a036c6d4d06ba7799264947f4843fa7029195f66b6",
    "notes/theory/lean/YulangClosure/CallFailureUnwind.lean": "2d7422bc4c83310a1a1d0a2bcaa5528bb6a8801520c42db2f2ada6b12224b89c",
    "notes/theory/lean/YulangClosure/CallFiniteTyping.lean": "555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588",
    "notes/theory/lean/YulangClosure/CallLiteralResponse.lean": "62cffcd2bcf5ce879c3c7b75ff6908b19470a27e5ca73e5973ec1affbeaac3fb",
    "notes/theory/lean/YulangClosure/CallNativeLiteralResponse.lean": "7b0c27ba851f982d3e13fa3e27c258fe907a56585a92123af14f9ad4d765d2cd",
    "notes/theory/lean/YulangClosure/CallPeelingTyping.lean": "f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44",
    "notes/theory/lean/YulangClosure/CallPrefixTyping.lean": "95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc",
    "notes/theory/lean/YulangClosure/CallProgressObstruction.lean": "8dc8b1b72c952dc45c431fb965a438b700dc86902a68b8d77a3de0b7d47858b7",
    "notes/theory/lean/YulangClosure/CallRequestBoundary.lean": "28ffc2943c18d324c35dacf18b4dd70921d4cc462ffd6ffdce989475ef46cce6",
    "notes/theory/lean/YulangClosure/CallRequestBoundaryComposition.lean": "fed00f06cdbf2a5bdc1b3c18957acc33c7b281e890f277ca5bd1d20ece53ee76",
    "notes/theory/lean/YulangClosure/CallRequestUnwind.lean": "e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9",
    "notes/theory/lean/YulangClosure/CallResponseCancellation.lean": "ab9083bab971acd4e72cb8db95d567b309a240e1773b3fc4544fa6968ffe9488",
    "notes/theory/lean/YulangClosure/CallStepTyping.lean": "4b3b40ae3c295666470c1cda73ac38f0abdc62ea86626be58f10249092d3c3ab",
    "notes/theory/lean/YulangClosure/CallStepTypingRepair.lean": "2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586",
    "notes/theory/lean/YulangClosure/CallTerminalTyping.lean": "319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d",
    "notes/theory/lean/YulangClosure/CallUnwindTyping.lean": "57afc331d735c7b9680c8b1391ced1f86b72a0ab10ca37e9f620cf0388af1cc1",
    "notes/theory/lean/YulangClosure/CallUnwindTypingRepair.lean": "1eaea1938f6ee2341352afcc597847fc2ade5b8ce8d3be84dda19926fe217cc3",
    "notes/theory/lean/YulangClosure/CallViewedForceReachability.lean": "ce6e45da496ceb3f5d7e1150f57ebdf5f62dd0495ee3a8deb1b61035b39cee8c",
    "notes/theory/lean/YulangClosure/CallViewedForceStuck.lean": "71164cef48ca86866ef4aae9661ea2e9388e9741062e159a97f3c26b42614ae9",
    "notes/theory/lean/YulangClosure/Contracts.lean": "2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e",
    "notes/theory/lean/YulangClosure/ControlComposition.lean": "4e8e4cb4fdf106bbffa11e21cd9f7030bda1f296f14e1a554560ea802f02dc5e",
    "notes/theory/lean/YulangClosure/ControlSyntax.lean": "1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0",
    "notes/theory/lean/YulangClosure/ControlTyping.lean": "e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f",
    "notes/theory/lean/YulangClosure/CoreComposition.lean": "1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c",
    "notes/theory/lean/YulangClosure/CoreControlBridge.lean": "30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a",
    "notes/theory/lean/YulangClosure/CoreExecution.lean": "86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e",
    "notes/theory/lean/YulangClosure/CoreSubstitution.lean": "ae1dfd4947d9e87c05dfa893b93067175d860ed3b5da000d61257d7789208b55",
    "notes/theory/lean/YulangClosure/CoreSyntax.lean": "c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375",
    "notes/theory/lean/YulangClosure/DeclSubst.lean": "f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258",
    "notes/theory/lean/YulangClosure/FiniteGuardDecision.lean": "a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa",
    "notes/theory/lean/YulangClosure/ForceAdmin.lean": "620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97",
    "notes/theory/lean/YulangClosure/ForceCompletion.lean": "6baeb9a786e916d0f7b60bd4d5c8286657da2adba4acdab36f2e45e0921aeb22",
    "notes/theory/lean/YulangClosure/GraphContinuationExtension.lean": "cae749a64bb641131aa6fdc19a71fe0c635dbe007433556f3dc9efe4388105ec",
    "notes/theory/lean/YulangClosure/GraphExtensionTransport.lean": "a41bbdb417d3a5f9c1784b690520d5a973d1178c5a1ab47b6b5b80cdd629dac1",
    "notes/theory/lean/YulangClosure/GuardedValueGraph.lean": "4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55",
    "notes/theory/lean/YulangClosure/HandlerGraphCorrespondence.lean": "94a6c2d24045bf9959121f4b31efea2f0630abc53c5bb776ab356d3ff108f964",
    "notes/theory/lean/YulangClosure/HandlerGraphEmbedding.lean": "36b616d809554feb585f32203fa72c1a084c7136beb4141a46d3a27a5145f656",
    "notes/theory/lean/YulangClosure/HandlerGraphInteraction.lean": "a5094f70dc2ec2843a431cfb24f0111166fbc9172b7e6df08d0d8c800a8ce018",
    "notes/theory/lean/YulangClosure/HandlerGraphRecAllocation.lean": "5563163a5fe2741dc4cb1968329e5ec417a170099448978b653dc487cd136dfd",
    "notes/theory/lean/YulangClosure/HandlerGraphRecInteraction.lean": "dc1f89a1e1b8b0b4a9e2e95fdcc47334b1b7578a8fef3f947574678ce8dfdba7",
    "notes/theory/lean/YulangClosure/HandlerGraphRecursiveTrace.lean": "bd07ea464ba42b1073b69b2af0bc5d26c1ca148a58598d6d10973ba54dc29909",
    "notes/theory/lean/YulangClosure/HandlerGraphSafety.lean": "554c5a1a003f27c3b8657d77455aa4f5eda7852338254034e3dd63a6db42a558",
    "notes/theory/lean/YulangClosure/HandlerGraphSyntax.lean": "2a6b3f455e408336290bbe28616d7db8ee928f1b342b4c80f975bbacb419c24c",
    "notes/theory/lean/YulangClosure/HandlerGraphTransport.lean": "a869e61005910dba00cf9cfa57065a45afeac08413974e343d9bcc16821f629d",
    "notes/theory/lean/YulangClosure/HigherOrderEmbedding.lean": "2b773edf831d04cd4319e1fb980865dff0fb9a38f7d64b21f3d228ea2a0e1457",
    "notes/theory/lean/YulangClosure/HigherOrderEntry.lean": "c9cb839ff6b34ed97c5d72f9e020437d32175cf517a5841a3a024764747c213b",
    "notes/theory/lean/YulangClosure/HigherOrderEnvironment.lean": "84a461fdff85e7321cf090ba2bb72a7d90415515a2da1eb15e1287ef0361ab83",
    "notes/theory/lean/YulangClosure/HigherOrderGraphObservation.lean": "8817db7bc5181481745f49696d7b7d2e4dc927a715353ab83bc36f4ed53420cc",
    "notes/theory/lean/YulangClosure/HigherOrderGraphSafety.lean": "de67122c098579b5ba088ff832ef8ca36e233537faf064ab8e36520cf2532533",
    "notes/theory/lean/YulangClosure/HigherOrderGraphSyntax.lean": "2dca03ee408f7f35545c02847d03fae47ab1887c2761c82e8b59cc9ad6001886",
    "notes/theory/lean/YulangClosure/HigherOrderHandlerInteraction.lean": "a0920fc7214055fd213bc66729e865b571698f95bd42ae289c432b6cf5730d3f",
    "notes/theory/lean/YulangClosure/HigherOrderHandlerSafety.lean": "f74c35666d8f4f5ab1af52009c005d5cb0be9958f7f8d64185c31750b2dd38ef",
    "notes/theory/lean/YulangClosure/HigherOrderHandlerSyntax.lean": "4578e2d3c8b06a57937dd652e06eabb8c9271113a7eb3388dc718856d64b249d",
    "notes/theory/lean/YulangClosure/HigherOrderInteraction.lean": "45f2b8c74e2837e503db84aed3c9f55767a32d19e4008546e25a01cef1202875",
    "notes/theory/lean/YulangClosure/HigherOrderRecAllocation.lean": "30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd",
    "notes/theory/lean/YulangClosure/HigherOrderSafety.lean": "16a38dbb649677ed5e6b6371a61228a1724b9e899136eeb2119b755ecab30336",
    "notes/theory/lean/YulangClosure/HigherOrderSubstitution.lean": "19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30",
    "notes/theory/lean/YulangClosure/HigherOrderSyntax.lean": "ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972",
    "notes/theory/lean/YulangClosure/InferenceProofs.lean": "dff8f66fb20d1a75cd1ff72ab72babecf30cfb8ad816b5e758c540c1b166afea",
    "notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean": "39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957",
    "notes/theory/lean/YulangClosure/NativeContextExpansion.lean": "9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8",
    "notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean": "d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070",
    "notes/theory/lean/YulangClosure/NativeDrainOwnership.lean": "d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18",
    "notes/theory/lean/YulangClosure/NativeExecutionHistory.lean": "44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6",
    "notes/theory/lean/YulangClosure/NativeFrameRollback.lean": "274e9a9ac1c43bc81d3b962edb6846dd5e4fa2adb2b645ebd92d6d5f38bd9964",
    "notes/theory/lean/YulangClosure/NativeIntegerArithmetic.lean": "5adb30eb53f64fa4ccad80e83ed78c27f442436f20a8eceb8bc4fb59aac33ad1",
    "notes/theory/lean/YulangClosure/NativeIntegerComparison.lean": "2352602b7047611e9f9722d788ed1acdf9f4960d178c48f6a08b1a7054f93e79",
    "notes/theory/lean/YulangClosure/NativeLiteralReadback.lean": "53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54",
    "notes/theory/lean/YulangClosure/NativeMergeExpansion.lean": "f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e",
    "notes/theory/lean/YulangClosure/NativeProfileRestriction.lean": "527d89b982b962e423cfaa15ecf76a2d778603102bfc9e8d12b22af2eb1c7fb2",
    "notes/theory/lean/YulangClosure/NativeRecordPlan.lean": "3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43",
    "notes/theory/lean/YulangClosure/NativeReplayAcknowledgement.lean": "5264c6b6d9904a43ec0b50c3ac0100a05612b724f52a8601e3a93c771f8204df",
    "notes/theory/lean/YulangClosure/NativeReplayCoverage.lean": "e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e",
    "notes/theory/lean/YulangClosure/NativeReplayCurrent.lean": "fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088",
    "notes/theory/lean/YulangClosure/NativeRowModel.lean": "30016f40295a803df2ed3d9b46efd256d1427400f55bda1810e22a00f89d7780",
    "notes/theory/lean/YulangClosure/NativeRowSaturation.lean": "9f8e2cf43ade40c17a09387d5888833002ee42791eff0d2d608f83d6ca39e974",
    "notes/theory/lean/YulangClosure/NativeTemplateReplay.lean": "cae76713a1756a5d15d13232a094437003931b33b6cc2e5a44ca946d83175d32",
    "notes/theory/lean/YulangClosure/PaperAllocationExecution.lean": "d5cd9f4499ec0c6e67e73a9444634671e43b507368c418b1d9ecec7fd57f0aa4",
    "notes/theory/lean/YulangClosure/PaperCallEntryFormation.lean": "2465c5620b0b66f6029ab294134d9860cd8bf810ac25c5f30763cb709c7da31e",
    "notes/theory/lean/YulangClosure/PaperCombinedExecution.lean": "58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1",
    "notes/theory/lean/YulangClosure/PaperCoreControl.lean": "71594dfb24af402f7b4835dc54b5383a46106faba959b687295cc0431361530e",
    "notes/theory/lean/YulangClosure/PaperCoreStep.lean": "6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144",
    "notes/theory/lean/YulangClosure/PaperEliminationExamples.lean": "d7b412df9bf7cfe47c538b48e1fb6ebfd8fc6c177d484cc3912573608d53071d",
    "notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean": "568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a",
    "notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean": "5fcb0334dfa77c3385f5f460669e36578a01642a54d17e357c072fd012fc73fe",
    "notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean": "d3a10c0891b0518fef7ed6e02c899b996d3ac6de618e07bddde11c89ef616bfe",
    "notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean": "cb0941ef8842551da53fbf2b14cca181c10849178288de29cef1145f1d575cc7",
    "notes/theory/lean/YulangClosure/PaperExtendedExecution.lean": "a29c5cc15748e8a91338f2a068e94ff7dc58c2a19adad564ba3f5a6fea337ea7",
    "notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean": "7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925",
    "notes/theory/lean/YulangClosure/PaperHeapExecution.lean": "46a9e8e76f5745cbaffc40b7bb95ff37064941a84532fa5edc07672ddad3d59f",
    "notes/theory/lean/YulangClosure/PaperHeapObservation.lean": "19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f",
    "notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean": "175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77",
    "notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean": "2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0",
    "notes/theory/lean/YulangClosure/PaperResumeExecution.lean": "5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935",
    "notes/theory/lean/YulangClosure/PaperTemplateExecution.lean": "3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792",
    "notes/theory/lean/YulangClosure/PaperTermSubstitution.lean": "d2dde517343a18b03a8fb0fe113b1d0fceeef2751f53792ef39886d8ed5e9c94",
    "notes/theory/lean/YulangClosure/PaperTermSubstitutionAlgebra.lean": "b35a14e1872cec5284a68cb38e9ea6fd0c9dc23cbd6d8017c82a550ec60a379d",
    "notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean": "7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d",
    "notes/theory/lean/YulangClosure/PaperTypeApplicationPreservation.lean": "60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556",
    "notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean": "0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8",
    "notes/theory/lean/YulangClosure/PaperTypeFormation.lean": "29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13",
    "notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean": "02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861",
    "notes/theory/lean/YulangClosure/PaperViewExecution.lean": "e7c6c959d2bcc780ca7198aae09a0368f4d98625001bdfe5b8f8c259c9cb3f85",
    "notes/theory/lean/YulangClosure/PrimitiveOperationInstance.lean": "c3b0f2ad86fd49f9ebcf22c80388b996951ff0704695e18afa546863ddcf8773",
    "notes/theory/lean/YulangClosure/ProofAdvancement.lean": "db2f2f3a548b0b20b15b2435f08a362e903c3e52a035c7eca5580925f08dd598",
    "notes/theory/lean/YulangClosure/RecordBoundaryExecution.lean": "865c4db37b3eed02d8cc376cf07b469c85ef364aeed7914823b207d14730cda2",
    "notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean": "1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056",
    "notes/theory/lean/YulangClosure/SimpleSubConstraintSoundness.lean": "33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293",
    "notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean": "a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6",
    "notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean": "3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246",
    "notes/theory/lean/YulangClosure/SimpleSubGrowingInference.lean": "865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeCertificates.lean": "55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeDecision.lean": "a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeGrowingInference.lean": "1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean": "c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3",
    "notes/theory/lean/YulangClosure/SimpleSubRegularCompletion.lean": "d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa",
    "notes/theory/lean/YulangClosure/SimpleSubRegularConstraintSoundness.lean": "1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33",
    "notes/theory/lean/YulangClosure/SimpleSubRegularDecision.lean": "6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d",
    "notes/theory/lean/YulangClosure/SimpleSubRegularGraphExtension.lean": "0b45d0e6d58701cba9f7df00d2a63897327e357ed3047b36e96d8fb6c49893d8",
    "notes/theory/lean/YulangClosure/SimpleSubRegularPublication.lean": "18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99",
    "notes/theory/lean/YulangClosure/SimpleSubRegularSolutions.lean": "755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29",
    "notes/theory/lean/YulangClosure/SimpleSubScopedPublication.lean": "d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f",
    "notes/theory/lean/YulangClosure/SourceFunctionMembership.lean": "8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424",
    "notes/theory/lean/YulangClosure/SourceGeneratedInteraction.lean": "16952fef6ea505cce0d7f8afa6bf39cd3609119626f7857d6beaa88737c5b003",
    "notes/theory/lean/YulangClosure/SourceIdentityLambda.lean": "831b297998509eb261f7a0596792c826c56078661d5a3ab66fc9afd67238d7a4",
    "notes/theory/lean/YulangClosure/SourceIdentityWorld.lean": "6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168",
    "notes/theory/lean/lake-manifest.json": "058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3",
    "notes/theory/lean/lakefile.toml": "cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd",
    "notes/theory/lean/lean-toolchain": "ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c"
  },
  "inputs": {
    "AGENTS.md": "ce73e9754ba9fd00bd2c4395d322ce77730a26aafb586d51de8ad169d7f8d48f",
    "AGENTS.pre-sprint.md": "34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562",
    ".agents/skills/yulang-lean-proofs/SKILL.md": "05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7",
    ".agents/skills/yulang-lean-proofs/references/sources.md": "cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a",
    ".agents/skills/yulang-lean-proofs/references/execution.md": "a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b",
    ".agents/skills/yulang-lean-proofs/scripts/check_lean.py": "a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6",
    "rules/goal-driven-sprints.md": "e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a",
    "crates/yu-solver/src/lib.rs": "ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07",
    "crates/yu-solver/src/candidate_context.rs": "57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e",
    "crates/yu-solver/src/candidate_scope.rs": "9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a",
    "notes/theory/2026-10-26-native-context-expansion-construction.md": "0bddd394a8dc7d686b1708ef099808c8b24c1e217242eaa7d0df5c1f6e9bed95",
    "notes/theory/2026-10-26-native-drain-ownership.md": "1e725751031322517c213662b0e0f1cf7b6e96bef656e2a6e45a40d67aee24e6",
    "notes/theory/lean/YulangClosure/NativeContextExpansion.lean": "9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8",
    "notes/theory/lean/YulangClosure/NativeDrainOwnership.lean": "d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18",
    "notes/theory/lean/YulangClosure/NativeRecordPlan.lean": "3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43"
  },
  "checker_budget": 20,
  "wall_seconds": 2700
}
```

### 01-port-construction

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:35:56.813589+00:00",
  "wall_seconds": 2.5632565270061605,
  "exit": 1,
  "peak_aggregate_rss_bytes": 945020928,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "8a97242c5c452e792e2bdb8742d1fa64464774295a6e206fa619b1f27c8e33f7",
  "log_sha256": "3710be7c93c1bb3ea967d36e7b2335b0ba0067dce3cd72785be2675271725a98",
  "seen_pids": [
    122587,
    122591,
    122595,
    122599,
    122603,
    122609
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 02-port-construction

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:36:32.094750+00:00",
  "wall_seconds": 2.822641904000193,
  "exit": 1,
  "peak_aggregate_rss_bytes": 948297728,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "adccd4201963a65555c3db8cdefbe3261077eaf8635a76945cefb23bc6268456",
  "log_sha256": "97a279c6e878e3cabb1bfb7ffb147f1cc00b5c8d41141d3d9468eacdd3c1eaf4",
  "seen_pids": [
    122783,
    122786,
    122790,
    122794,
    122797,
    122803
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 03-child-admission

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:37:17.217255+00:00",
  "wall_seconds": 4.223562510996999,
  "exit": 1,
  "peak_aggregate_rss_bytes": 954613760,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "32422a1a014be7fe6ede653b893d4fa7405ab066bde11ea46b6772cf1568e0ed",
  "log_sha256": "92bfb81fd6e0de76ef38ccbe9e06ee5b2aa30818837ac8e9fda377af59a974bc",
  "seen_pids": [
    122959,
    122962,
    122966,
    122970,
    122973,
    122979
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 04-child-admission

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:37:58.365475+00:00",
  "wall_seconds": 4.155812693999906,
  "exit": 1,
  "peak_aggregate_rss_bytes": 953643008,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "2205981d928bb9cdd56f30be0efbf20540b297f32cfb5b9c7800f7d7e69b4f47",
  "log_sha256": "2f25351f4c43579dfb252b45432597903a0a125552e821b2e667ee250a431e29",
  "seen_pids": [
    123097,
    123100,
    123104,
    123108,
    123111,
    123117
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 05-child-admission

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:39:24.636778+00:00",
  "wall_seconds": 3.3655018049976206,
  "exit": 1,
  "peak_aggregate_rss_bytes": 953913344,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "0614d28c7f7db72debfa4c2f8eee848e0a77da9be30118ac555e50f1e4530c9c",
  "log_sha256": "06b8560c64696b0cbd585b12421677c5ee82156aed9622289069a69464522172",
  "seen_pids": [
    123236,
    123238,
    123242,
    123246,
    123249,
    123255
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 06-two-phase-dispatch

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:40:29.405102+00:00",
  "wall_seconds": 3.8935970429956797,
  "exit": 1,
  "peak_aggregate_rss_bytes": 962596864,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "3ad0f990b92c14f3e6ef2891e5039a65eeb9e8bc4c39d321f6a9eec11544f037",
  "log_sha256": "696316ad4facc1e0ee05c765c40f7bd00a3fc994ab15b82fa069157cb06c7e80",
  "seen_pids": [
    123541,
    123543,
    123547,
    123551,
    123554,
    123560
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 07-two-phase-dispatch

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:41:04.383925+00:00",
  "wall_seconds": 13.364907891998882,
  "exit": 0,
  "peak_aggregate_rss_bytes": 1141747712,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "9510b156771c8fd5c95a353260c4c7032363368e7d127652234ba6930cb58aa6",
  "log_sha256": "3d329f23a0496871175d2e996f33dea554dac8c11fac7ee8cbd74e0eccbc9f1b",
  "seen_pids": [
    123718,
    123721,
    123725,
    123729,
    123732,
    123738,
    123752,
    123756
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 08-structured-child-lists

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:42:50.600498+00:00",
  "wall_seconds": 21.362195966998115,
  "exit": 1,
  "peak_aggregate_rss_bytes": 972152832,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "e3d8cd8d0f0b75db266ba8dea4055fbd515b874d24c7530514de3d278ca2eaf3",
  "log_sha256": "5c370306ac79145d665dbfa86f1933baaded3a582d58fd0f910ac4df2508d04b",
  "seen_pids": [
    124118,
    124120,
    124126,
    124130,
    124133,
    124140,
    124156,
    124172
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 09-computed-dispatch

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:43:53.185959+00:00",
  "wall_seconds": 4.454023137004697,
  "exit": 1,
  "peak_aggregate_rss_bytes": 977960960,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "39f2a51fd511bbebb23a87e6e3c0a5f84ba0fc9438c28cb45d2ce68b7ac92609",
  "log_sha256": "f1a165c9806bdb5eb1e43fc70919034150c921ea8c0affae073cb5ab8dbf4fdf",
  "seen_pids": [
    124367,
    124370,
    124374,
    124378,
    124381,
    124388
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 10-all-port-roots

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.stamp_input_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.stamp_preserves_protections",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_body_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_other_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_preserves_inputs",
    "--theorem",
    "YulangClosure.NativeValuePorts.extends_refl",
    "--theorem",
    "YulangClosure.NativeValuePorts.extends_trans",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_found",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_extends",
    "--theorem",
    "YulangClosure.NativeValuePorts.arena_extends_refl",
    "--theorem",
    "YulangClosure.NativeValuePorts.arena_extends_trans",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.transformer_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.relation_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.transformer_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_extends",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.flow_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.admit_constructs",
    "--theorem",
    "YulangClosure.NativeValuePorts.structural_demand_preserved",
    "--theorem",
    "YulangClosure.NativeValuePorts.every_port_dependency",
    "--theorem",
    "YulangClosure.NativeValuePorts.derived_dependency_iff",
    "--theorem",
    "YulangClosure.NativeValuePorts.nonidentity_effect_self_rejected",
    "--theorem",
    "YulangClosure.NativeValuePorts.function_children_whole",
    "--theorem",
    "YulangClosure.NativeValuePorts.tuple_children_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.record_children_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_arm_all_matches",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_children_no_omission",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_missing_discards_prefix",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_first_missing",
    "--theorem",
    "YulangClosure.NativeValuePorts.argument_effect_scope",
    "--theorem",
    "YulangClosure.NativeValuePorts.result_effect_scope",
    "--theorem",
    "YulangClosure.NativeValuePorts.admission_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.initial_cursor_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.dispatch_step_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.dispatch_run_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.next_source_index",
    "--theorem",
    "YulangClosure.NativeValuePorts.finished_pending_none",
    "--theorem",
    "YulangClosure.NativeValuePorts.completed_dispatch_readback",
    "--theorem",
    "YulangClosure.NativeValuePorts.drive_constructs_run",
    "--theorem",
    "YulangClosure.NativeValuePorts.drive_success_readback",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.function_drive_returns",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.function_drive_whole",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.variant_duplicate_requirements",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.record_original_indices",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.prefixed_argument_context"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:44:52.787468+00:00",
  "wall_seconds": 9.514449860005698,
  "exit": 0,
  "peak_aggregate_rss_bytes": 1176584192,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "e9a9159a220f97768c672dad8d9b753f1447712f2052426b28e3e412b5c1e100",
  "log_sha256": "8c740257aeb148318a684441f11b9fcb9912bbf15a2b3c01de3da8a22e09b8e1",
  "seen_pids": [
    124606,
    124608,
    124612,
    124616,
    124619,
    124626,
    124653,
    124658
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 11-context-formation

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.stamp_input_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.stamp_preserves_protections",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_body_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_other_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_preserves_inputs",
    "--theorem",
    "YulangClosure.NativeValuePorts.extends_refl",
    "--theorem",
    "YulangClosure.NativeValuePorts.extends_trans",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_found",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_extends",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_length",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_reuse_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.arena_extends_refl",
    "--theorem",
    "YulangClosure.NativeValuePorts.arena_extends_trans",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.transformer_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.relation_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_index_bound",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_preserves_formation",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_length",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.transformer_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_extends",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_formed",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.flow_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.admit_constructs",
    "--theorem",
    "YulangClosure.NativeValuePorts.structural_demand_preserved",
    "--theorem",
    "YulangClosure.NativeValuePorts.every_port_dependency",
    "--theorem",
    "YulangClosure.NativeValuePorts.derived_dependency_iff",
    "--theorem",
    "YulangClosure.NativeValuePorts.nonidentity_effect_self_rejected",
    "--theorem",
    "YulangClosure.NativeValuePorts.function_children_whole",
    "--theorem",
    "YulangClosure.NativeValuePorts.tuple_children_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.record_children_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_arm_all_matches",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_children_no_omission",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_missing_discards_prefix",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_first_missing",
    "--theorem",
    "YulangClosure.NativeValuePorts.argument_effect_scope",
    "--theorem",
    "YulangClosure.NativeValuePorts.result_effect_scope",
    "--theorem",
    "YulangClosure.NativeValuePorts.admission_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.initial_cursor_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.dispatch_step_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.dispatch_run_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.next_source_index",
    "--theorem",
    "YulangClosure.NativeValuePorts.finished_pending_none",
    "--theorem",
    "YulangClosure.NativeValuePorts.completed_dispatch_readback",
    "--theorem",
    "YulangClosure.NativeValuePorts.drive_constructs_run",
    "--theorem",
    "YulangClosure.NativeValuePorts.drive_success_readback",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.arena_context_formed",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.function_drive_returns",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.function_drive_whole",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.variant_duplicate_requirements",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.record_original_indices",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.prefixed_argument_context"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:47:05.085733+00:00",
  "wall_seconds": 4.525750046996109,
  "exit": 1,
  "peak_aggregate_rss_bytes": 981274624,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "0535e09366f74f9d9127d19f8d8bd4fc826bb4d7f3c73bcd380ca3cee2cb02b5",
  "log_sha256": "58be846b84bcdb0b5716baf76fc8ebb6895c09a16732d09cce6e49b3ab83fb24",
  "seen_pids": [
    124995,
    124998,
    125002,
    125006,
    125009,
    125016
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 12-final-port-roots

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeValuePorts",
    "--theorem",
    "YulangClosure.NativeValuePorts.stamp_input_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.stamp_preserves_protections",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_body_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_other_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.protect_preserves_inputs",
    "--theorem",
    "YulangClosure.NativeValuePorts.extends_refl",
    "--theorem",
    "YulangClosure.NativeValuePorts.extends_trans",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_found",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_extends",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_length",
    "--theorem",
    "YulangClosure.NativeValuePorts.intern_reuse_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.arena_extends_refl",
    "--theorem",
    "YulangClosure.NativeValuePorts.arena_extends_trans",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.transformer_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.relation_constructed",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_index_bound",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_preserves_formation",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_length",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.transformer_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_extends",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_context_formed",
    "--theorem",
    "YulangClosure.NativeValuePorts.build_flow_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.flow_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.context_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.admit_constructs",
    "--theorem",
    "YulangClosure.NativeValuePorts.structural_demand_preserved",
    "--theorem",
    "YulangClosure.NativeValuePorts.every_port_dependency",
    "--theorem",
    "YulangClosure.NativeValuePorts.derived_dependency_iff",
    "--theorem",
    "YulangClosure.NativeValuePorts.nonidentity_effect_self_rejected",
    "--theorem",
    "YulangClosure.NativeValuePorts.function_children_whole",
    "--theorem",
    "YulangClosure.NativeValuePorts.tuple_children_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.record_children_exact",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_arm_all_matches",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_children_no_omission",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_missing_discards_prefix",
    "--theorem",
    "YulangClosure.NativeValuePorts.variant_first_missing",
    "--theorem",
    "YulangClosure.NativeValuePorts.argument_effect_scope",
    "--theorem",
    "YulangClosure.NativeValuePorts.result_effect_scope",
    "--theorem",
    "YulangClosure.NativeValuePorts.admission_result_kept",
    "--theorem",
    "YulangClosure.NativeValuePorts.initial_cursor_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.dispatch_step_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.dispatch_run_valid",
    "--theorem",
    "YulangClosure.NativeValuePorts.next_source_index",
    "--theorem",
    "YulangClosure.NativeValuePorts.finished_pending_none",
    "--theorem",
    "YulangClosure.NativeValuePorts.completed_dispatch_readback",
    "--theorem",
    "YulangClosure.NativeValuePorts.drive_constructs_run",
    "--theorem",
    "YulangClosure.NativeValuePorts.drive_success_readback",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.arena_context_formed",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.function_drive_returns",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.function_drive_whole",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.variant_duplicate_requirements",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.record_original_indices",
    "--theorem",
    "YulangClosure.NativeValuePorts.Witness.prefixed_argument_context"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:47:47.361489+00:00",
  "wall_seconds": 13.005619472001854,
  "exit": 0,
  "peak_aggregate_rss_bytes": 1179955200,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa",
  "log_sha256": "df8c7a9a46170b68f4747ad7787138734d9fd71c5e49834337d53963b3746139",
  "seen_pids": [
    125106,
    125109,
    125113,
    125117,
    125120,
    125127,
    125155,
    125159
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

### 13-originating-census

```json
{
  "command": [
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--no-cache",
    "env",
    "lean",
    "-j1",
    "-M1024",
    "AuditNativeValuePorts.lean"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/value-ports-r4/project",
  "started_utc": "2026-10-26T11:48:23.536610+00:00",
  "wall_seconds": 2.6100773660000414,
  "exit": 0,
  "peak_aggregate_rss_bytes": 1146605568,
  "cpu_affinity": [
    8
  ],
  "termination": null,
  "source_sha256": "f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa",
  "log_sha256": "e801f97f2ae5e77505eb87751fc4c09b0d9fd5fd0132d8abb6052f7b9fc3ae22",
  "seen_pids": [
    125249,
    125254
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "aggregate_rss_ceiling_mib": 1280
}
```

## All originating theorem types and axioms

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_4

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_4 : ∀
  (motive : YulangClosure.NativeValuePorts.FunctionField → Sort u_1)
  (h_1 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argument)
  (h_2 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.result)
  (h_3 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argumentEffect)
  (h_4 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.resultEffect),
  (match YulangClosure.NativeValuePorts.FunctionField.resultEffect with
    | YulangClosure.NativeValuePorts.FunctionField.argument => h_1 ()
    | YulangClosure.NativeValuePorts.FunctionField.result => h_2 ()
    | YulangClosure.NativeValuePorts.FunctionField.argumentEffect => h_3 ()
    | YulangClosure.NativeValuePorts.FunctionField.resultEffect => h_4 ()) =
    h_4 ()
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Key.mk.injEq

```lean
YulangClosure.NativeValuePorts.Key.mk.injEq : ∀ (pair : YulangClosure.NativeValuePorts.Pair) (context : Nat)
  (sources : Option Nat) (flow : YulangClosure.NativeValuePorts.Flow) (pair_1 : YulangClosure.NativeValuePorts.Pair)
  (context_1 : Nat) (sources_1 : Option Nat) (flow_1 : YulangClosure.NativeValuePorts.Flow),
  ({ pair := pair, context := context, sources := sources, flow := flow } =
      { pair := pair_1, context := context_1, sources := sources_1, flow := flow_1 }) =
    (pair = pair_1 ∧ context = context_1 ∧ sources = sources_1 ∧ flow = flow_1)
'YulangClosure.NativeValuePorts.Key.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.relation_constructed

```lean
YulangClosure.NativeValuePorts.relation_constructed : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (key : YulangClosure.NativeValuePorts.Key),
  (arena.relation key).fst.relations[(arena.relation key).snd]? = Option.some key ∧
    arena.Extends (arena.relation key).fst
'YulangClosure.NativeValuePorts.relation_constructed' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.AdmissionResult.flow_exact

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.flow_exact : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    YulangClosure.NativeValuePorts.FlowResult arena parent child.port receipt.child.flow
'YulangClosure.NativeValuePorts.AdmissionResult.flow_exact' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Pair.value.injEq

```lean
YulangClosure.NativeValuePorts.Pair.value.injEq : ∀
  (lower upper lower_1 upper_1 : YulangClosure.NativeValuePorts.ValueEndpoint),
  (YulangClosure.NativeValuePorts.Pair.value lower upper = YulangClosure.NativeValuePorts.Pair.value lower_1 upper_1) =
    (lower = lower_1 ∧ upper = upper_1)
'YulangClosure.NativeValuePorts.Pair.value.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.AdmissionResult.guards

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.guards : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    YulangClosure.NativeValuePorts.Allowed receipt.child
'YulangClosure.NativeValuePorts.AdmissionResult.guards' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_9

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_9 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant a =
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant a
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_9' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_8

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_8 : ∀ (a b : Nat),
  ¬a = b → YulangClosure.NativeValuePorts.Port.tuple a = YulangClosure.NativeValuePorts.Port.tuple b → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_8' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_4 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : Nat) (a_3 : YulangClosure.NativeValuePorts.Port) (a_4 : Bool) (b : Nat)
  (b_1 : YulangClosure.NativeValuePorts.Port) (b_2 : Bool),
  ¬a_2 = b →
    { parent := a, child := a_1, relation := a_2, port := a_3, derived := a_4 } =
        { parent := a, child := a_1, relation := b, port := b_1, derived := b_2 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_7

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_7 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord term →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord term = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_7' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_4 : ∀ (a : Nat) (a_1 : Bool) (a_2 : List Nat)
  (b : Nat) (b_1 : Bool) (b_2 : List Nat),
  ¬a = b →
    { scope := a, keepInitial := a_1, missing := a_2 } = { scope := b, keepInitial := b_1, missing := b_2 } → False
'YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.FunctionField.resultEffect.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.FunctionField.resultEffect.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.FunctionField.resultEffect =
  1
'YulangClosure.NativeValuePorts.FunctionField.resultEffect.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.function.injEq

```lean
YulangClosure.NativeValuePorts.Port.function.injEq : ∀ (field field_1 : YulangClosure.NativeValuePorts.FunctionField),
  (YulangClosure.NativeValuePorts.Port.function field = YulangClosure.NativeValuePorts.Port.function field_1) =
    (field = field_1)
'YulangClosure.NativeValuePorts.Port.function.injEq' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_7.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_7.eq_1 : ∀
  (motive : Nat → YulangClosure.NativeValuePorts.Cursor → Sort u_1) (cursor : YulangClosure.NativeValuePorts.Cursor)
  (h_1 : (cursor : YulangClosure.NativeValuePorts.Cursor) → motive 0 cursor)
  (h_2 : (n : Nat) → (cursor : YulangClosure.NativeValuePorts.Cursor) → motive n.succ cursor),
  (match 0, cursor with
    | 0, cursor => h_1 cursor
    | n.succ, cursor => h_2 n cursor) =
    h_1 cursor
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_7.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_1 : ∀ (a : Nat)
  (a_1 : Option YulangClosure.NativeContextExpansion.ScopedDemand),
  { transformer := a, demand := a_1 } = { transformer := a, demand := a_1 }
'YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_2 : ∀
  (a : List YulangClosure.NativeContextExpansion.Expr) (a_1 : List YulangClosure.NativeValuePorts.Transformer)
  (a_2 b : List YulangClosure.NativeValuePorts.Key),
  ¬a_2 = b →
    { contexts := a, transformers := a_1, relations := a_2 } = { contexts := a, transformers := a_1, relations := b } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.derived_dependency_iff

```lean
YulangClosure.NativeValuePorts.derived_dependency_iff : ∀ (receipt : YulangClosure.NativeValuePorts.Receipt),
  YulangClosure.NativeValuePorts.Dependency.derived receipt.parent receipt.child ∈ receipt.dependencies ↔
    receipt.derived = Bool.true
'YulangClosure.NativeValuePorts.derived_dependency_iff' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_6

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_6 : ∀ (a b : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction a =
        YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_6' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.context_preserves_formation

```lean
@YulangClosure.NativeValuePorts.context_preserves_formation : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {node : YulangClosure.NativeContextExpansion.Expr},
  YulangClosure.NativeValuePorts.ContextsFormed arena.contexts →
    (∀ (input : Nat), input ∈ YulangClosure.NativeValuePorts.contextInputs node → input ≤ arena.contexts.length) →
      YulangClosure.NativeValuePorts.ContextsFormed (arena.context node).fst.contexts
'YulangClosure.NativeValuePorts.context_preserves_formation' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_5 : ∀
  (field : YulangClosure.NativeValuePorts.FunctionField) (lowerIndex upperIndex payloadIndex : Nat),
  YulangClosure.NativeValuePorts.Port.function field =
      YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.FunctionField.ofNat_ctorIdx

```lean
YulangClosure.NativeValuePorts.FunctionField.ofNat_ctorIdx : ∀ (x : YulangClosure.NativeValuePorts.FunctionField),
  YulangClosure.NativeValuePorts.FunctionField.ofNat x.ctorIdx = x
'YulangClosure.NativeValuePorts.FunctionField.ofNat_ctorIdx' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_2 : ∀
  (a b : YulangClosure.NativeValuePorts.FunctionField),
  ¬a = b → YulangClosure.NativeValuePorts.Port.function a = YulangClosure.NativeValuePorts.Port.function b → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.sizeOf_spec : ∀ (term : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant term) = 1 + SizeOf.sizeOf term
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.sizeOf_spec' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_1 : ∀
  (motive : YulangClosure.NativeContextExpansion.Expr → Sort u_1) (weight input : Nat)
  (h_1 : (weight input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.prefix weight input))
  (h_2 : (input weight : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.suffix input weight))
  (h_3 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.swap input))
  (h_4 : (input certificate : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.both input certificate))
  (h_5 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.without input))
  (h_6 : (lower upper : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.replay lower upper)),
  (match YulangClosure.NativeContextExpansion.Expr.prefix weight input with
    | YulangClosure.NativeContextExpansion.Expr.prefix weight input => h_1 weight input
    | YulangClosure.NativeContextExpansion.Expr.suffix input weight => h_2 input weight
    | YulangClosure.NativeContextExpansion.Expr.swap input => h_3 input
    | YulangClosure.NativeContextExpansion.Expr.both input certificate => h_4 input certificate
    | YulangClosure.NativeContextExpansion.Expr.without input => h_5 input
    | YulangClosure.NativeContextExpansion.Expr.replay lower upper => h_6 lower upper) =
    h_1 weight input
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.row.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.row.injEq : ∀ (id id_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.row id = YulangClosure.NativeValuePorts.ValueEndpoint.row id_1) =
    (id = id_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.row.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_20

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_20 : ∀ (a a_1 a_2 : Nat),
  YulangClosure.NativeValuePorts.Port.variant a a_1 a_2 = YulangClosure.NativeValuePorts.Port.variant a a_1 a_2
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_20' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_3 : ∀ (a : Nat) (a_1 : List Nat) (b : Nat)
  (b_1 : List Nat), ¬a = b → { tag := a, payloads := a_1 } = { tag := b, payloads := b_1 } → False
'YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.structural_demand_preserved

```lean
@YulangClosure.NativeValuePorts.structural_demand_preserved : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    (∀ (field : YulangClosure.NativeValuePorts.FunctionField),
        child.port ≠ YulangClosure.NativeValuePorts.Port.function field) →
      receipt.child.flow = parent.flow
'YulangClosure.NativeValuePorts.structural_demand_preserved' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.injEq : ∀ (term term_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction term =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction term_1) =
    (term = term_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.intern_extends

```lean
@YulangClosure.NativeValuePorts.intern_extends : ∀ {α : Type u_1} [inst : DecidableEq α] (items : List α) (value : α),
  YulangClosure.NativeValuePorts.Extends items (YulangClosure.NativeValuePorts.intern items value).fst
'YulangClosure.NativeValuePorts.intern_extends' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_1 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (id : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.row id →
    YulangClosure.NativeValuePorts.ValueEndpoint.row id = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_13

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_13 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord a =
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord a
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_13' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.drive.eq_def

```lean
YulangClosure.NativeValuePorts.drive.eq_def : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool) (x : Nat)
  (x_1 : YulangClosure.NativeValuePorts.Cursor),
  YulangClosure.NativeValuePorts.drive views qv qe parent post derived x x_1 =
    match x, x_1 with
    | 0, cursor => if cursor.todo = [] then Option.some cursor else Option.none
    | n.succ, cursor =>
      match cursor.todo with
      | [] => Option.some cursor
      | child :: rest =>
        match cursor.pending with
        | Option.none => do
          let __x ← YulangClosure.NativeValuePorts.admit cursor.arena views qv qe parent post derived child
          match __x with
            | (arena, receipt) =>
              YulangClosure.NativeValuePorts.drive views qv qe parent post derived n (cursor.admitted arena receipt)
        | Option.some receipt =>
          YulangClosure.NativeValuePorts.drive views qv qe parent post derived n (cursor.enqueued child rest receipt)
'YulangClosure.NativeValuePorts.drive.eq_def' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.stamp_input_exact

```lean
YulangClosure.NativeValuePorts.stamp_input_exact : ∀ (input i : Nat) (initial : Nat → Prop),
  (YulangClosure.NativeValuePorts.Transformer.stamp input).input initial i ↔ initial i ∨ i = input
'YulangClosure.NativeValuePorts.stamp_input_exact' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Child.mk.inj

```lean
@YulangClosure.NativeValuePorts.Child.mk.inj : ∀ {port : YulangClosure.NativeValuePorts.Port}
  {task : YulangClosure.NativeValuePorts.Pair} {port_1 : YulangClosure.NativeValuePorts.Port}
  {task_1 : YulangClosure.NativeValuePorts.Pair},
  { port := port, task := task } = { port := port_1, task := task_1 } → port = port_1 ∧ task = task_1
'YulangClosure.NativeValuePorts.Child.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.record.inj

```lean
@YulangClosure.NativeValuePorts.Port.record.inj : ∀ {lowerIndex upperIndex lowerIndex_1 upperIndex_1 : Nat},
  YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex =
      YulangClosure.NativeValuePorts.Port.record lowerIndex_1 upperIndex_1 →
    lowerIndex = lowerIndex_1 ∧ upperIndex = upperIndex_1
'YulangClosure.NativeValuePorts.Port.record.inj' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_5.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_5.eq_1 : ∀
  (motive : List YulangClosure.NativeValuePorts.Child → Sort u_1) (h_1 : Unit → motive [])
  (h_2 :
    (child : YulangClosure.NativeValuePorts.Child) →
      (rest : List YulangClosure.NativeValuePorts.Child) → motive (child :: rest)),
  (match [] with
    | [] => h_1 ()
    | child :: rest => h_2 child rest) =
    h_1 ()
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_5.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_4 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant term →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant term = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.build_context_exact

```lean
YulangClosure.NativeValuePorts.build_context_exact : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (localWeight : Option Nat) (post : Nat) (swap : Bool),
  YulangClosure.NativeValuePorts.ContextResult
    (YulangClosure.NativeValuePorts.buildContext arena localWeight post swap).fst localWeight post swap
    (YulangClosure.NativeValuePorts.buildContext arena localWeight post swap).snd
'YulangClosure.NativeValuePorts.build_context_exact' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_17

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_17 : ∀ (a a_1 b b_1 : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple a a_1 =
        YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple b b_1 →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_17' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_6

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_6 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : YulangClosure.NativeValuePorts.Port),
  YulangClosure.NativeValuePorts.Dependency.port a a_1 a_2 = YulangClosure.NativeValuePorts.Dependency.port a a_1 a_2
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_6' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Work.mk.inj

```lean
@YulangClosure.NativeValuePorts.Work.mk.inj : ∀ {source : YulangClosure.NativeValuePorts.Child}
  {receipt : YulangClosure.NativeValuePorts.Receipt} {source_1 : YulangClosure.NativeValuePorts.Child}
  {receipt_1 : YulangClosure.NativeValuePorts.Receipt},
  { source := source, receipt := receipt } = { source := source_1, receipt := receipt_1 } →
    source = source_1 ∧ receipt = receipt_1
'YulangClosure.NativeValuePorts.Work.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.record_children_exact

```lean
@YulangClosure.NativeValuePorts.record_children_exact : ∀ {terms : YulangClosure.NativeValuePorts.TermEndpoints}
  {boundary : YulangClosure.NativeValuePorts.Key} {lower upper : List (YulangClosure.RecordBoundary.Field Nat)}
  {children : List YulangClosure.NativeValuePorts.Child},
  YulangClosure.NativeValuePorts.recordChildren terms boundary lower upper = Except.ok children →
    ∃ slots,
      YulangClosure.NativeRecordPlan.shape boundary lower 0 upper = Except.ok slots ∧
        YulangClosure.NativeRecordPlan.ValidShape lower boundary 0 upper slots ∧
          children =
            List.map (YulangClosure.NativeValuePorts.recordChild terms) (YulangClosure.NativeRecordPlan.children slots)
'YulangClosure.NativeValuePorts.record_children_exact' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.variantChildren.match_1.eq_2

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.variantChildren.match_1.eq_2 : ∀
  (motive : Nat → List YulangClosure.NativeValuePorts.Alternative → Sort u_1) (index : Nat)
  (actual : YulangClosure.NativeValuePorts.Alternative) (rest : List YulangClosure.NativeValuePorts.Alternative)
  (h_1 : (x : Nat) → motive x [])
  (h_2 :
    (index : Nat) →
      (actual : YulangClosure.NativeValuePorts.Alternative) →
        (rest : List YulangClosure.NativeValuePorts.Alternative) → motive index (actual :: rest)),
  (match index, actual :: rest with
    | x, [] => h_1 x
    | index, actual :: rest => h_2 index actual rest) =
    h_2 index actual rest
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.variantChildren.match_1.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.AdmissionResult.parent_same

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.parent_same : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    receipt.parent = parent
'YulangClosure.NativeValuePorts.AdmissionResult.parent_same' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_9

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_9 : ∀ (index lowerIndex upperIndex : Nat),
  YulangClosure.NativeValuePorts.Port.tuple index = YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_9' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.variant_first_missing

```lean
@YulangClosure.NativeValuePorts.variant_first_missing : ∀ {terms : YulangClosure.NativeValuePorts.TermEndpoints}
  {upper before after : List YulangClosure.NativeValuePorts.Alternative} {start : Nat}
  {actual : YulangClosure.NativeValuePorts.Alternative},
  (∀ (candidate : YulangClosure.NativeValuePorts.Alternative),
      candidate ∈ before → upper.any (YulangClosure.NativeValuePorts.matching candidate) = Bool.true) →
    upper.any (YulangClosure.NativeValuePorts.matching actual) = Bool.false →
      YulangClosure.NativeValuePorts.variantChildren terms upper start (before ++ actual :: after) =
        Except.error (start + before.length)
'YulangClosure.NativeValuePorts.variant_first_missing' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.row.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.row.inj : ∀ {id id_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.row id = YulangClosure.NativeValuePorts.ValueEndpoint.row id_1 →
    id = id_1
'YulangClosure.NativeValuePorts.ValueEndpoint.row.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Arena.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Arena.mk.sizeOf_spec : ∀ (contexts : List YulangClosure.NativeContextExpansion.Expr)
  (transformers : List YulangClosure.NativeValuePorts.Transformer)
  (relations : List YulangClosure.NativeValuePorts.Key),
  SizeOf.sizeOf { contexts := contexts, transformers := transformers, relations := relations } =
    1 + SizeOf.sizeOf contexts + SizeOf.sizeOf transformers + SizeOf.sizeOf relations
'YulangClosure.NativeValuePorts.Arena.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Transformer.protection.eq_1

```lean
YulangClosure.NativeValuePorts.Transformer.protection.eq_1 : ∀ (t : YulangClosure.NativeValuePorts.Transformer)
  (inputs scopes : Nat → Prop) (scope : Nat),
  t.protection inputs scopes scope =
    match List.find? (fun entry => Decidable.decide (entry.scope = scope)) t.scopes with
    | Option.none => scopes scope
    | Option.some entry => entry.keepInitial = Bool.true ∧ scopes scope ∨ ∃ input, input ∈ entry.missing ∧ ¬inputs input
'YulangClosure.NativeValuePorts.Transformer.protection.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.inj : ∀ {term term_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction term =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction term_1 →
    term = term_1
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.dispatch_run_valid

```lean
@YulangClosure.NativeValuePorts.dispatch_run_valid : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {before after : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.DispatchRun views qv qe parent post derived before after →
    YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue before →
      YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue after
'YulangClosure.NativeValuePorts.dispatch_run_valid' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.variant_missing_discards_prefix

```lean
@YulangClosure.NativeValuePorts.variant_missing_discards_prefix : ∀
  {terms : YulangClosure.NativeValuePorts.TermEndpoints} {upper lower : List YulangClosure.NativeValuePorts.Alternative}
  {index : Nat} {actual : YulangClosure.NativeValuePorts.Alternative},
  upper.any (YulangClosure.NativeValuePorts.matching actual) = Bool.false →
    YulangClosure.NativeValuePorts.variantChildren terms upper index (actual :: lower) = Except.error index
'YulangClosure.NativeValuePorts.variant_missing_discards_prefix' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_2 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : Nat) (a_3 : YulangClosure.NativeValuePorts.Port) (a_4 b : Bool),
  ¬a_4 = b →
    { parent := a, child := a_1, relation := a_2, port := a_3, derived := a_4 } =
        { parent := a, child := a_1, relation := a_2, port := a_3, derived := b } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.inj : ∀ {term term_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant term =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant term_1 →
    term = term_1
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.inj' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_5.eq_2

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_5.eq_2 : ∀
  (motive : List YulangClosure.NativeValuePorts.Child → Sort u_1) (child : YulangClosure.NativeValuePorts.Child)
  (rest : List YulangClosure.NativeValuePorts.Child) (h_1 : Unit → motive [])
  (h_2 :
    (child : YulangClosure.NativeValuePorts.Child) →
      (rest : List YulangClosure.NativeValuePorts.Child) → motive (child :: rest)),
  (match child :: rest with
    | [] => h_1 ()
    | child :: rest => h_2 child rest) =
    h_2 child rest
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_5.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_2 : ∀
  (a a_1 b : YulangClosure.NativeValuePorts.Key),
  ¬a_1 = b →
    YulangClosure.NativeValuePorts.Dependency.derived a a_1 = YulangClosure.NativeValuePorts.Dependency.derived a b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_2' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_2

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_2 : ∀
  (motive : YulangClosure.NativeContextExpansion.Expr → Sort u_1) (input weight : Nat)
  (h_1 : (weight input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.prefix weight input))
  (h_2 : (input weight : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.suffix input weight))
  (h_3 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.swap input))
  (h_4 : (input certificate : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.both input certificate))
  (h_5 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.without input))
  (h_6 : (lower upper : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.replay lower upper)),
  (match YulangClosure.NativeContextExpansion.Expr.suffix input weight with
    | YulangClosure.NativeContextExpansion.Expr.prefix weight input => h_1 weight input
    | YulangClosure.NativeContextExpansion.Expr.suffix input weight => h_2 input weight
    | YulangClosure.NativeContextExpansion.Expr.swap input => h_3 input
    | YulangClosure.NativeContextExpansion.Expr.both input certificate => h_4 input certificate
    | YulangClosure.NativeContextExpansion.Expr.without input => h_5 input
    | YulangClosure.NativeContextExpansion.Expr.replay lower upper => h_6 lower upper) =
    h_2 input weight
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_4 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Nat) (a_2 : Option Nat) (a_3 : YulangClosure.NativeValuePorts.Flow) (b : Nat) (b_1 : Option Nat)
  (b_2 : YulangClosure.NativeValuePorts.Flow),
  ¬a_1 = b →
    { pair := a, context := a_1, sources := a_2, flow := a_3 } =
        { pair := a, context := b, sources := b_1, flow := b_2 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.FlowResult.eq_2

```lean
YulangClosure.NativeValuePorts.FlowResult.eq_2 : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (parent : YulangClosure.NativeValuePorts.Key) (port : YulangClosure.NativeValuePorts.Port)
  (flow : YulangClosure.NativeValuePorts.Flow),
  (∀ (field : YulangClosure.NativeValuePorts.FunctionField),
      port = YulangClosure.NativeValuePorts.Port.function field → False) →
    YulangClosure.NativeValuePorts.FlowResult arena parent port flow = (flow = parent.flow)
'YulangClosure.NativeValuePorts.FlowResult.eq_2' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_2 : ∀ (a : YulangClosure.NativeValuePorts.Port)
  (a_1 b : YulangClosure.NativeValuePorts.Pair),
  ¬a_1 = b → { port := a, task := a_1 } = { port := a, task := b } → False
'YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.inj : ∀ {term arity term_1 arity_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple term arity =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple term_1 arity_1 →
    term = term_1 ∧ arity = arity_1
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.inj' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_5.eq_2

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_5.eq_2 : ∀
  (motive : YulangClosure.NativeValuePorts.Port → Sort u_1) (x : YulangClosure.NativeValuePorts.Port)
  (h_1 :
    (field : YulangClosure.NativeValuePorts.FunctionField) →
      motive (YulangClosure.NativeValuePorts.Port.function field))
  (h_2 : (x : YulangClosure.NativeValuePorts.Port) → motive x),
  (∀ (field : YulangClosure.NativeValuePorts.FunctionField),
      x = YulangClosure.NativeValuePorts.Port.function field → False) →
    (match x with
      | YulangClosure.NativeValuePorts.Port.function field => h_1 field
      | x => h_2 x) =
      h_2 x
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_5.eq_2' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Witness.record_original_indices

```lean
YulangClosure.NativeValuePorts.Witness.record_original_indices : YulangClosure.NativeValuePorts.recordChildren
    YulangClosure.NativeValuePorts.Witness.terms YulangClosure.NativeValuePorts.Witness.parent
    [(7, { ty := 1, optional := Bool.false })]
    [(5, { ty := 2, optional := Bool.true }), (7, { ty := 3, optional := Bool.false })] =
  Except.ok
    [{ port := YulangClosure.NativeValuePorts.Port.record 0 1,
        task :=
          YulangClosure.NativeValuePorts.Pair.value (YulangClosure.NativeValuePorts.ValueEndpoint.row 1)
            (YulangClosure.NativeValuePorts.ValueEndpoint.row 3) }]
'YulangClosure.NativeValuePorts.Witness.record_original_indices' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_15

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_15 : ∀ (a a_1 : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple a a_1 =
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple a a_1
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_15' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_10

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_10 : ∀ (a b : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant a =
        YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_10' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_3 : ∀ (a : List Nat)
  (a_1 : List YulangClosure.NativeValuePorts.Protection) (b : List Nat)
  (b_1 : List YulangClosure.NativeValuePorts.Protection),
  ¬a = b → { stamped := a, scopes := a_1 } = { stamped := b, scopes := b_1 } → False
'YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.NativeWork.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.NativeWork.mk.sizeOf_spec : ∀ (task : YulangClosure.NativeValuePorts.Pair)
  (relation : Option Nat) (replayAck : Option (Nat × Nat)),
  SizeOf.sizeOf { task := task, relation := relation, replayAck := replayAck } =
    1 + SizeOf.sizeOf task + SizeOf.sizeOf relation + SizeOf.sizeOf replayAck
'YulangClosure.NativeValuePorts.NativeWork.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_1 : ∀
  (a : List YulangClosure.NativeContextExpansion.Expr) (a_1 : List YulangClosure.NativeValuePorts.Transformer)
  (a_2 : List YulangClosure.NativeValuePorts.Key),
  { contexts := a, transformers := a_1, relations := a_2 } = { contexts := a, transformers := a_1, relations := a_2 }
'YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Key.mk.inj

```lean
@YulangClosure.NativeValuePorts.Key.mk.inj : ∀ {pair : YulangClosure.NativeValuePorts.Pair} {context : Nat}
  {sources : Option Nat} {flow : YulangClosure.NativeValuePorts.Flow} {pair_1 : YulangClosure.NativeValuePorts.Pair}
  {context_1 : Nat} {sources_1 : Option Nat} {flow_1 : YulangClosure.NativeValuePorts.Flow},
  { pair := pair, context := context, sources := sources, flow := flow } =
      { pair := pair_1, context := context_1, sources := sources_1, flow := flow_1 } →
    pair = pair_1 ∧ context = context_1 ∧ sources = sources_1 ∧ flow = flow_1
'YulangClosure.NativeValuePorts.Key.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_4 : ∀ (a a_1 a_2 a_3 b b_1 b_2 : Nat),
  ¬a_1 = b →
    { argument := a, argumentEffect := a_1, resultEffect := a_2, result := a_3 } =
        { argument := a, argumentEffect := b, resultEffect := b_1, result := b_2 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.protect_preserves_inputs

```lean
YulangClosure.NativeValuePorts.protect_preserves_inputs : ∀ (scope input i : Nat) (inputs : Nat → Prop),
  (YulangClosure.NativeValuePorts.Transformer.protect scope input).input inputs i ↔ inputs i
'YulangClosure.NativeValuePorts.protect_preserves_inputs' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_5.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_5.eq_1 : ∀
  (motive : YulangClosure.NativeValuePorts.Port → Sort u_1) (field : YulangClosure.NativeValuePorts.FunctionField)
  (h_1 :
    (field : YulangClosure.NativeValuePorts.FunctionField) →
      motive (YulangClosure.NativeValuePorts.Port.function field))
  (h_2 : (x : YulangClosure.NativeValuePorts.Port) → motive x),
  (match YulangClosure.NativeValuePorts.Port.function field with
    | YulangClosure.NativeValuePorts.Port.function field => h_1 field
    | x => h_2 x) =
    h_1 field
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_5.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Witness.arena.eq_1

```lean
YulangClosure.NativeValuePorts.Witness.arena.eq_1 : YulangClosure.NativeValuePorts.Witness.arena =
  { contexts := [YulangClosure.NativeContextExpansion.Expr.without 0],
    relations := [YulangClosure.NativeValuePorts.Witness.parent] }
'YulangClosure.NativeValuePorts.Witness.arena.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.bottomNegative.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.bottomNegative.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.bottomNegative =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.bottomNegative.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_4 : ∀
  (parent child parent_1 child_1 : YulangClosure.NativeValuePorts.Key) (port : YulangClosure.NativeValuePorts.Port),
  YulangClosure.NativeValuePorts.Dependency.derived parent child =
      YulangClosure.NativeValuePorts.Dependency.port parent_1 child_1 port →
    False
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.FunctionTerms.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.FunctionTerms.mk.sizeOf_spec : ∀ (argument argumentEffect resultEffect result : Nat),
  SizeOf.sizeOf
      { argument := argument, argumentEffect := argumentEffect, resultEffect := resultEffect, result := result } =
    1 + SizeOf.sizeOf argument + SizeOf.sizeOf argumentEffect + SizeOf.sizeOf resultEffect + SizeOf.sizeOf result
'YulangClosure.NativeValuePorts.FunctionTerms.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Alternative.mk.inj

```lean
@YulangClosure.NativeValuePorts.Alternative.mk.inj : ∀ {tag : Nat} {payloads : List Nat} {tag_1 : Nat}
  {payloads_1 : List Nat},
  { tag := tag, payloads := payloads } = { tag := tag_1, payloads := payloads_1 } → tag = tag_1 ∧ payloads = payloads_1
'YulangClosure.NativeValuePorts.Alternative.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_1 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Nat) (a_2 : Option Nat) (a_3 : YulangClosure.NativeValuePorts.Flow),
  { pair := a, context := a_1, sources := a_2, flow := a_3 } =
    { pair := a, context := a_1, sources := a_2, flow := a_3 }
'YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_4 : ∀
  (field : YulangClosure.NativeValuePorts.FunctionField) (lowerIndex upperIndex : Nat),
  YulangClosure.NativeValuePorts.Port.function field =
      YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_3 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Nat) (a_2 : Option Nat) (a_3 : YulangClosure.NativeValuePorts.Flow) (b : Option Nat)
  (b_1 : YulangClosure.NativeValuePorts.Flow),
  ¬a_2 = b →
    { pair := a, context := a_1, sources := a_2, flow := a_3 } =
        { pair := a, context := a_1, sources := b, flow := b_1 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.transformer_kept

```lean
@YulangClosure.NativeValuePorts.transformer_kept : ∀ {before after : YulangClosure.NativeValuePorts.Arena},
  before.Extends after →
    ∀ {id : Nat} {transformer : YulangClosure.NativeValuePorts.Transformer},
      before.transformerAt id = Option.some transformer → after.transformerAt id = Option.some transformer
'YulangClosure.NativeValuePorts.transformer_kept' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_18

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_18 : ∀ (a a_1 : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple a a_1 =
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple a a_1
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_18' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.injEq : ∀ (term term_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction term =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction term_1) =
    (term = term_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_5 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction a =
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction a
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.function.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Port.function.sizeOf_spec : ∀ (field : YulangClosure.NativeValuePorts.FunctionField),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Port.function field) = 1 + SizeOf.sizeOf field
'YulangClosure.NativeValuePorts.Port.function.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_4 : ∀
  (lower upper : YulangClosure.NativeValuePorts.ValueEndpoint)
  (lower_1 upper_1 : YulangClosure.NativeMergeExpansion.Endpoint),
  YulangClosure.NativeValuePorts.Pair.value lower upper = YulangClosure.NativeValuePorts.Pair.effect lower_1 upper_1 →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.TermEndpoints.mk.injEq

```lean
YulangClosure.NativeValuePorts.TermEndpoints.mk.injEq : ∀
  (positiveValue negativeValue : Nat → YulangClosure.NativeValuePorts.ValueEndpoint)
  (positiveEffect negativeEffect : Nat → YulangClosure.NativeMergeExpansion.Endpoint)
  (positiveValue_1 negativeValue_1 : Nat → YulangClosure.NativeValuePorts.ValueEndpoint)
  (positiveEffect_1 negativeEffect_1 : Nat → YulangClosure.NativeMergeExpansion.Endpoint),
  ({ positiveValue := positiveValue, negativeValue := negativeValue, positiveEffect := positiveEffect,
        negativeEffect := negativeEffect } =
      { positiveValue := positiveValue_1, negativeValue := negativeValue_1, positiveEffect := positiveEffect_1,
        negativeEffect := negativeEffect_1 }) =
    (positiveValue = positiveValue_1 ∧
      negativeValue = negativeValue_1 ∧ positiveEffect = positiveEffect_1 ∧ negativeEffect = negativeEffect_1)
'YulangClosure.NativeValuePorts.TermEndpoints.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Pair.effect.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Pair.effect.sizeOf_spec : ∀ (lower upper : YulangClosure.NativeMergeExpansion.Endpoint),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Pair.effect lower upper) = 1 + SizeOf.sizeOf lower + SizeOf.sizeOf upper
'YulangClosure.NativeValuePorts.Pair.effect.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_5 : ∀ (a a_1 a_2 a_3 b b_1 b_2 b_3 : Nat),
  ¬a = b →
    { argument := a, argumentEffect := a_1, resultEffect := a_2, result := a_3 } =
        { argument := b, argumentEffect := b_1, resultEffect := b_2, result := b_3 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.tuple_children_exact

```lean
@YulangClosure.NativeValuePorts.tuple_children_exact : ∀ {terms : YulangClosure.NativeValuePorts.TermEndpoints}
  {lowerArity upperArity : Nat} {lower upper : List Nat} {children : List YulangClosure.NativeValuePorts.Child},
  YulangClosure.NativeValuePorts.tupleChildren terms lowerArity upperArity lower upper = Option.some children →
    lowerArity = upperArity ∧
      lower.length = lowerArity ∧
        upper.length = upperArity ∧
          children.length = lowerArity ∧
            ∀ (index lo hi : Nat),
              lower[index]? = Option.some lo →
                upper[index]? = Option.some hi →
                  children[index]? =
                    Option.some
                      { port := YulangClosure.NativeValuePorts.Port.tuple index,
                        task :=
                          YulangClosure.NativeValuePorts.Pair.value (terms.positiveValue lo) (terms.negativeValue hi) }
'YulangClosure.NativeValuePorts.tuple_children_exact' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_12

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_12 : ∀ (a b : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord a =
        YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_12' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.extends_refl

```lean
@YulangClosure.NativeValuePorts.extends_refl : ∀ {α : Type u_1} (items : List α),
  YulangClosure.NativeValuePorts.Extends items items
'YulangClosure.NativeValuePorts.extends_refl' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_17

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_17 : ∀ (lowerIndex upperIndex payloadIndex : Nat)
  (field : YulangClosure.NativeValuePorts.FunctionField),
  YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex =
      YulangClosure.NativeValuePorts.Port.function field →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_17' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.NativeWork.mk.injEq

```lean
YulangClosure.NativeValuePorts.NativeWork.mk.injEq : ∀ (task : YulangClosure.NativeValuePorts.Pair)
  (relation : Option Nat) (replayAck : Option (Nat × Nat)) (task_1 : YulangClosure.NativeValuePorts.Pair)
  (relation_1 : Option Nat) (replayAck_1 : Option (Nat × Nat)),
  ({ task := task, relation := relation, replayAck := replayAck } =
      { task := task_1, relation := relation_1, replayAck := replayAck_1 }) =
    (task = task_1 ∧ relation = relation_1 ∧ replayAck = replayAck_1)
'YulangClosure.NativeValuePorts.NativeWork.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.AdmissionResult.sources_same

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.sources_same : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    receipt.child.sources = parent.sources
'YulangClosure.NativeValuePorts.AdmissionResult.sources_same' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_1 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.row a = YulangClosure.NativeValuePorts.ValueEndpoint.row a
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.variantChildren.eq_1

```lean
YulangClosure.NativeValuePorts.variantChildren.eq_1 : ∀ (terms : YulangClosure.NativeValuePorts.TermEndpoints)
  (upper : List YulangClosure.NativeValuePorts.Alternative) (x : Nat),
  YulangClosure.NativeValuePorts.variantChildren terms upper x [] = Except.ok []
'YulangClosure.NativeValuePorts.variantChildren.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.initial_cursor_valid

```lean
YulangClosure.NativeValuePorts.initial_cursor_valid : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool)
  (children : List YulangClosure.NativeValuePorts.Child) (queue : List YulangClosure.NativeValuePorts.NativeWork)
  (arena : YulangClosure.NativeValuePorts.Arena),
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue
    (YulangClosure.NativeValuePorts.initialCursor arena children queue)
'YulangClosure.NativeValuePorts.initial_cursor_valid' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.sizeOf_spec : ∀ (term : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction term) = 1 + SizeOf.sizeOf term
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.tuple.inj

```lean
@YulangClosure.NativeValuePorts.Port.tuple.inj : ∀ {index index_1 : Nat},
  YulangClosure.NativeValuePorts.Port.tuple index = YulangClosure.NativeValuePorts.Port.tuple index_1 → index = index_1
'YulangClosure.NativeValuePorts.Port.tuple.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.FunctionField.result.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.FunctionField.result.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.FunctionField.result =
  1
'YulangClosure.NativeValuePorts.FunctionField.result.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_21

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_21 : ∀
  (x x_1 : YulangClosure.NativeValuePorts.ValueEndpoint), ¬x.ctorIdx = x_1.ctorIdx → x = x_1 → False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_21' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_9

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_9 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term arity : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple term arity →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple term arity = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_9' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.context_preserves_formation._proof_1_1

```lean
@YulangClosure.NativeValuePorts.context_preserves_formation._proof_1_1 : ∀
  {arena : YulangClosure.NativeValuePorts.Arena} {node : YulangClosure.NativeContextExpansion.Expr} (index : Nat),
  ¬index < arena.contexts.length → index < arena.contexts.length + 1 → ¬index = arena.contexts.length → False
'YulangClosure.NativeValuePorts.context_preserves_formation._proof_1_1' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.injEq : ∀ (term term_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord term =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord term_1) =
    (term = term_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.variant_arm_all_matches

```lean
@YulangClosure.NativeValuePorts.variant_arm_all_matches : ∀ {terms : YulangClosure.NativeValuePorts.TermEndpoints}
  {lowerIndex upperIndex payloadIndex : Nat} {lower expected : YulangClosure.NativeValuePorts.Alternative}
  {upper : List YulangClosure.NativeValuePorts.Alternative} {lo hi : Nat},
  upper[upperIndex]? = Option.some expected →
    YulangClosure.NativeValuePorts.matching lower expected = Bool.true →
      lower.payloads[payloadIndex]? = Option.some lo →
        expected.payloads[payloadIndex]? = Option.some hi →
          { port := YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex,
              task := YulangClosure.NativeValuePorts.Pair.value (terms.positiveValue lo) (terms.negativeValue hi) } ∈
            YulangClosure.NativeValuePorts.variantArmChildren terms lowerIndex lower upper
'YulangClosure.NativeValuePorts.variant_arm_all_matches' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_11

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_11 : ∀ (lowerIndex upperIndex : Nat)
  (field : YulangClosure.NativeValuePorts.FunctionField),
  YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex =
      YulangClosure.NativeValuePorts.Port.function field →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_11' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.every_port_dependency

```lean
YulangClosure.NativeValuePorts.every_port_dependency : ∀ (receipt : YulangClosure.NativeValuePorts.Receipt),
  YulangClosure.NativeValuePorts.Dependency.port receipt.parent receipt.child receipt.port ∈ receipt.dependencies
'YulangClosure.NativeValuePorts.every_port_dependency' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Flow.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Flow.mk.sizeOf_spec : ∀ (transformer : Nat)
  (demand : Option YulangClosure.NativeContextExpansion.ScopedDemand),
  SizeOf.sizeOf { transformer := transformer, demand := demand } = 1 + SizeOf.sizeOf transformer + SizeOf.sizeOf demand
'YulangClosure.NativeValuePorts.Flow.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.CursorValid.checked

```lean
@YulangClosure.NativeValuePorts.CursorValid.checked : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue cursor →
    ∀ (work : YulangClosure.NativeValuePorts.Work),
      work ∈ cursor.records →
        YulangClosure.NativeValuePorts.AdmissionResult cursor.arena views qv qe parent post derived work.source
          work.receipt
'YulangClosure.NativeValuePorts.CursorValid.checked' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_18

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_18 : ∀ (lowerIndex upperIndex payloadIndex index : Nat),
  YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex =
      YulangClosure.NativeValuePorts.Port.tuple index →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_18' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_3.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_3.eq_1 : ∀
  (motive : Option YulangClosure.NativeValuePorts.Receipt → Sort u_1) (h_1 : Unit → motive Option.none)
  (h_2 : (receipt : YulangClosure.NativeValuePorts.Receipt) → motive (Option.some receipt)),
  (match Option.none with
    | Option.none => h_1 ()
    | Option.some receipt => h_2 receipt) =
    h_1 ()
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_3.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_23

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_23 : ∀ (a a_1 a_2 b b_1 b_2 : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.Port.variant a a_1 a_2 = YulangClosure.NativeValuePorts.Port.variant b b_1 b_2 →
      False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_23' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Alternative.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Alternative.mk.sizeOf_spec : ∀ (tag : Nat) (payloads : List Nat),
  SizeOf.sizeOf { tag := tag, payloads := payloads } = 1 + SizeOf.sizeOf tag + SizeOf.sizeOf payloads
'YulangClosure.NativeValuePorts.Alternative.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_3 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction a =
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction a
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Pair.value.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Pair.value.sizeOf_spec : ∀ (lower upper : YulangClosure.NativeValuePorts.ValueEndpoint),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Pair.value lower upper) = 1 + SizeOf.sizeOf lower + SizeOf.sizeOf upper
'YulangClosure.NativeValuePorts.Pair.value.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Child.mk.injEq

```lean
YulangClosure.NativeValuePorts.Child.mk.injEq : ∀ (port : YulangClosure.NativeValuePorts.Port)
  (task : YulangClosure.NativeValuePorts.Pair) (port_1 : YulangClosure.NativeValuePorts.Port)
  (task_1 : YulangClosure.NativeValuePorts.Pair),
  ({ port := port, task := task } = { port := port_1, task := task_1 }) = (port = port_1 ∧ task = task_1)
'YulangClosure.NativeValuePorts.Child.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_13

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_13 : ∀ (a a_1 : Nat),
  YulangClosure.NativeValuePorts.Port.record a a_1 = YulangClosure.NativeValuePorts.Port.record a a_1
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_13' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_6

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_6 : ∀ (index : Nat)
  (field : YulangClosure.NativeValuePorts.FunctionField),
  YulangClosure.NativeValuePorts.Port.tuple index = YulangClosure.NativeValuePorts.Port.function field → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_6' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_1.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_1.eq_1 : ∀
  (motive : YulangClosure.NativeValuePorts.Arena × YulangClosure.NativeValuePorts.Receipt → Sort u_1)
  (arena : YulangClosure.NativeValuePorts.Arena) (receipt : YulangClosure.NativeValuePorts.Receipt)
  (h_1 :
    (arena : YulangClosure.NativeValuePorts.Arena) →
      (receipt : YulangClosure.NativeValuePorts.Receipt) → motive (arena, receipt)),
  (match (arena, receipt) with
    | (arena, receipt) => h_1 arena receipt) =
    h_1 arena receipt
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_1.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Witness.function_drive_returns

```lean
YulangClosure.NativeValuePorts.Witness.function_drive_returns : YulangClosure.NativeValuePorts.Witness.completed.isSome =
  Bool.true
'YulangClosure.NativeValuePorts.Witness.function_drive_returns' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_5

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_5 : ∀
  (motive : YulangClosure.NativeContextExpansion.Expr → Sort u_1) (input : Nat)
  (h_1 : (weight input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.prefix weight input))
  (h_2 : (input weight : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.suffix input weight))
  (h_3 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.swap input))
  (h_4 : (input certificate : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.both input certificate))
  (h_5 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.without input))
  (h_6 : (lower upper : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.replay lower upper)),
  (match YulangClosure.NativeContextExpansion.Expr.without input with
    | YulangClosure.NativeContextExpansion.Expr.prefix weight input => h_1 weight input
    | YulangClosure.NativeContextExpansion.Expr.suffix input weight => h_2 input weight
    | YulangClosure.NativeContextExpansion.Expr.swap input => h_3 input
    | YulangClosure.NativeContextExpansion.Expr.both input certificate => h_4 input certificate
    | YulangClosure.NativeContextExpansion.Expr.without input => h_5 input
    | YulangClosure.NativeContextExpansion.Expr.replay lower upper => h_6 lower upper) =
    h_5 input
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.protect_body_exact

```lean
YulangClosure.NativeValuePorts.protect_body_exact : ∀ (scope input : Nat) (inputs scopes : Nat → Prop),
  (YulangClosure.NativeValuePorts.Transformer.protect scope input).protection inputs scopes scope ↔
    scopes scope ∨ ¬inputs input
'YulangClosure.NativeValuePorts.protect_body_exact' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.Pair.effect.inj

```lean
@YulangClosure.NativeValuePorts.Pair.effect.inj : ∀
  {lower upper lower_1 upper_1 : YulangClosure.NativeMergeExpansion.Endpoint},
  YulangClosure.NativeValuePorts.Pair.effect lower upper = YulangClosure.NativeValuePorts.Pair.effect lower_1 upper_1 →
    lower = lower_1 ∧ upper = upper_1
'YulangClosure.NativeValuePorts.Pair.effect.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFunctionField._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqFunctionField._proof_1 : ∀
  (x y : YulangClosure.NativeValuePorts.FunctionField), x.ctorIdx = y.ctorIdx → x = y
'YulangClosure.NativeValuePorts.instDecidableEqFunctionField._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.dispatch_step_valid

```lean
@YulangClosure.NativeValuePorts.dispatch_step_valid : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {before after : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.DispatchStep views qv qe parent post derived before after →
    YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue before →
      YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue after
'YulangClosure.NativeValuePorts.dispatch_step_valid' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_7

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_7 : ∀
  (a a_1 b : YulangClosure.NativeMergeExpansion.Endpoint),
  ¬a_1 = b → YulangClosure.NativeValuePorts.Pair.effect a a_1 = YulangClosure.NativeValuePorts.Pair.effect a b → False
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_7' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.tuple.injEq

```lean
YulangClosure.NativeValuePorts.Port.tuple.injEq : ∀ (index index_1 : Nat),
  (YulangClosure.NativeValuePorts.Port.tuple index = YulangClosure.NativeValuePorts.Port.tuple index_1) =
    (index = index_1)
'YulangClosure.NativeValuePorts.Port.tuple.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.extends_trans

```lean
@YulangClosure.NativeValuePorts.extends_trans : ∀ {α : Type u_1} {a b c : List α},
  YulangClosure.NativeValuePorts.Extends a b →
    YulangClosure.NativeValuePorts.Extends b c → YulangClosure.NativeValuePorts.Extends a c
'YulangClosure.NativeValuePorts.extends_trans' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Arena.transformerAt.eq_1

```lean
YulangClosure.NativeValuePorts.Arena.transformerAt.eq_1 : ∀ (arena : YulangClosure.NativeValuePorts.Arena) (id : Nat),
  arena.transformerAt id =
    if id = 0 then Option.some YulangClosure.NativeValuePorts.Transformer.identity else arena.transformers[id - 1]?
'YulangClosure.NativeValuePorts.Arena.transformerAt.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.drive_success_readback

```lean
@YulangClosure.NativeValuePorts.drive_success_readback : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {arena : YulangClosure.NativeValuePorts.Arena} {fuel : Nat} {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.drive views qv qe parent post derived fuel
        (YulangClosure.NativeValuePorts.initialCursor arena children queue) =
      Option.some cursor →
    cursor.pending = Option.none ∧
      ∃ jobs,
        List.map YulangClosure.NativeValuePorts.Work.source jobs = children ∧
          cursor.queue = List.map YulangClosure.NativeValuePorts.Work.native jobs ++ queue ∧
            (∀ (work : YulangClosure.NativeValuePorts.Work),
                work ∈ jobs →
                  YulangClosure.NativeValuePorts.AdmissionResult cursor.arena views qv qe parent post derived
                    work.source work.receipt) ∧
              ∀ (work : YulangClosure.NativeValuePorts.Work), work ∈ jobs → work.native.replayAck = Option.none
'YulangClosure.NativeValuePorts.drive_success_readback' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_3 : ∀ (a : YulangClosure.NativeValuePorts.Child)
  (a_1 : YulangClosure.NativeValuePorts.Receipt) (b : YulangClosure.NativeValuePorts.Child)
  (b_1 : YulangClosure.NativeValuePorts.Receipt),
  ¬a = b → { source := a, receipt := a_1 } = { source := b, receipt := b_1 } → False
'YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Transformer.input.eq_1

```lean
YulangClosure.NativeValuePorts.Transformer.input.eq_1 : ∀ (t : YulangClosure.NativeValuePorts.Transformer)
  (initial : Nat → Prop) (input : Nat), t.input initial input = (initial input ∨ input ∈ t.stamped)
'YulangClosure.NativeValuePorts.Transformer.input.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.record.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Port.record.sizeOf_spec : ∀ (lowerIndex upperIndex : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex) =
    1 + SizeOf.sizeOf lowerIndex + SizeOf.sizeOf upperIndex
'YulangClosure.NativeValuePorts.Port.record.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.completed_dispatch_readback

```lean
@YulangClosure.NativeValuePorts.completed_dispatch_readback : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {arena : YulangClosure.NativeValuePorts.Arena} {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.DispatchRun views qv qe parent post derived
      (YulangClosure.NativeValuePorts.initialCursor arena children queue) cursor →
    cursor.todo = [] →
      ∃ jobs,
        List.map YulangClosure.NativeValuePorts.Work.source jobs = children ∧
          cursor.queue = List.map YulangClosure.NativeValuePorts.Work.native jobs ++ queue ∧
            (∀ (work : YulangClosure.NativeValuePorts.Work),
                work ∈ jobs →
                  YulangClosure.NativeValuePorts.AdmissionResult cursor.arena views qv qe parent post derived
                    work.source work.receipt) ∧
              ∀ (work : YulangClosure.NativeValuePorts.Work), work ∈ jobs → work.native.replayAck = Option.none
'YulangClosure.NativeValuePorts.completed_dispatch_readback' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.sizeOf_spec : ∀ (term : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant term) = 1 + SizeOf.sizeOf term
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.sizeOf_spec : ∀ (term arity : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple term arity) =
    1 + SizeOf.sizeOf term + SizeOf.sizeOf arity
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.context_index_bound

```lean
YulangClosure.NativeValuePorts.context_index_bound : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (node : YulangClosure.NativeContextExpansion.Expr),
  (arena.context node).snd ≤ (arena.context node).fst.contexts.length
'YulangClosure.NativeValuePorts.context_index_bound' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.dispatch_step_valid._simp_1_3

```lean
@YulangClosure.NativeValuePorts.dispatch_step_valid._simp_1_3 : ∀ {α : Type u_1} {a b : α}, (a ∈ [b]) = (a = b)
'YulangClosure.NativeValuePorts.dispatch_step_valid._simp_1_3' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.sizeOf_spec : ∀ (term arity : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple term arity) =
    1 + SizeOf.sizeOf term + SizeOf.sizeOf arity
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_3 : ∀
  (field : YulangClosure.NativeValuePorts.FunctionField) (index : Nat),
  YulangClosure.NativeValuePorts.Port.function field = YulangClosure.NativeValuePorts.Port.tuple index → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.FlowResult.eq_1

```lean
YulangClosure.NativeValuePorts.FlowResult.eq_1 : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (parent : YulangClosure.NativeValuePorts.Key) (flow : YulangClosure.NativeValuePorts.Flow)
  (field : YulangClosure.NativeValuePorts.FunctionField),
  YulangClosure.NativeValuePorts.FlowResult arena parent (YulangClosure.NativeValuePorts.Port.function field) flow =
    (parent.flow.transformer = 0 ∧
      match parent.flow.demand with
      | Option.none => flow = parent.flow
      | Option.some demand =>
        YulangClosure.NativeValuePorts.genuineDemand parent demand ∧
          flow.demand = Option.none ∧
            match field with
            | YulangClosure.NativeValuePorts.FunctionField.argument => flow.transformer = 0
            | YulangClosure.NativeValuePorts.FunctionField.result => flow.transformer = 0
            | YulangClosure.NativeValuePorts.FunctionField.argumentEffect =>
              arena.transformerAt flow.transformer =
                Option.some (YulangClosure.NativeValuePorts.Transformer.stamp demand.inputRoute)
            | YulangClosure.NativeValuePorts.FunctionField.resultEffect =>
              arena.transformerAt flow.transformer =
                Option.some (YulangClosure.NativeValuePorts.Transformer.protect demand.outputScope demand.inputRoute))
'YulangClosure.NativeValuePorts.FlowResult.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_5 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : Nat) (a_3 : YulangClosure.NativeValuePorts.Port) (a_4 : Bool) (b : YulangClosure.NativeValuePorts.Key)
  (b_1 : Nat) (b_2 : YulangClosure.NativeValuePorts.Port) (b_3 : Bool),
  ¬a_1 = b →
    { parent := a, child := a_1, relation := a_2, port := a_3, derived := a_4 } =
        { parent := a, child := b, relation := b_1, port := b_2, derived := b_3 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Receipt.mk.inj

```lean
@YulangClosure.NativeValuePorts.Receipt.mk.inj : ∀ {parent child : YulangClosure.NativeValuePorts.Key} {relation : Nat}
  {port : YulangClosure.NativeValuePorts.Port} {derived : Bool} {parent_1 child_1 : YulangClosure.NativeValuePorts.Key}
  {relation_1 : Nat} {port_1 : YulangClosure.NativeValuePorts.Port} {derived_1 : Bool},
  { parent := parent, child := child, relation := relation, port := port, derived := derived } =
      { parent := parent_1, child := child_1, relation := relation_1, port := port_1, derived := derived_1 } →
    parent = parent_1 ∧ child = child_1 ∧ relation = relation_1 ∧ port = port_1 ∧ derived = derived_1
'YulangClosure.NativeValuePorts.Receipt.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Key.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Key.mk.sizeOf_spec : ∀ (pair : YulangClosure.NativeValuePorts.Pair) (context : Nat)
  (sources : Option Nat) (flow : YulangClosure.NativeValuePorts.Flow),
  SizeOf.sizeOf { pair := pair, context := context, sources := sources, flow := flow } =
    1 + SizeOf.sizeOf pair + SizeOf.sizeOf context + SizeOf.sizeOf sources + SizeOf.sizeOf flow
'YulangClosure.NativeValuePorts.Key.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.unitPositive.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.unitPositive.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.unitPositive =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.unitPositive.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.build_context_extends

```lean
YulangClosure.NativeValuePorts.build_context_extends : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (localWeight : Option Nat) (post : Nat) (swap : Bool),
  arena.Extends (YulangClosure.NativeValuePorts.buildContext arena localWeight post swap).fst
'YulangClosure.NativeValuePorts.build_context_extends' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_20

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_20 : ∀ (a a_1 b b_1 : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple a a_1 =
        YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple b b_1 →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_20' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Dependency.port.injEq

```lean
YulangClosure.NativeValuePorts.Dependency.port.injEq : ∀ (parent child : YulangClosure.NativeValuePorts.Key)
  (port : YulangClosure.NativeValuePorts.Port) (parent_1 child_1 : YulangClosure.NativeValuePorts.Key)
  (port_1 : YulangClosure.NativeValuePorts.Port),
  (YulangClosure.NativeValuePorts.Dependency.port parent child port =
      YulangClosure.NativeValuePorts.Dependency.port parent_1 child_1 port_1) =
    (parent = parent_1 ∧ child = child_1 ∧ port = port_1)
'YulangClosure.NativeValuePorts.Dependency.port.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Receipt.dependencies.eq_1

```lean
YulangClosure.NativeValuePorts.Receipt.dependencies.eq_1 : ∀ (receipt : YulangClosure.NativeValuePorts.Receipt),
  receipt.dependencies =
    (if receipt.derived = Bool.true then
        [YulangClosure.NativeValuePorts.Dependency.derived receipt.parent receipt.child]
      else []) ++
      [YulangClosure.NativeValuePorts.Dependency.port receipt.parent receipt.child receipt.port]
'YulangClosure.NativeValuePorts.Receipt.dependencies.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Dependency.derived.injEq

```lean
YulangClosure.NativeValuePorts.Dependency.derived.injEq : ∀
  (parent child parent_1 child_1 : YulangClosure.NativeValuePorts.Key),
  (YulangClosure.NativeValuePorts.Dependency.derived parent child =
      YulangClosure.NativeValuePorts.Dependency.derived parent_1 child_1) =
    (parent = parent_1 ∧ child = child_1)
'YulangClosure.NativeValuePorts.Dependency.derived.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqFunctionField._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqFunctionField._proof_2 : ∀
  (x y : YulangClosure.NativeValuePorts.FunctionField), ¬x.ctorIdx = y.ctorIdx → x = y → False
'YulangClosure.NativeValuePorts.instDecidableEqFunctionField._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.variant.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Port.variant.sizeOf_spec : ∀ (lowerIndex upperIndex payloadIndex : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex) =
    1 + SizeOf.sizeOf lowerIndex + SizeOf.sizeOf upperIndex + SizeOf.sizeOf payloadIndex
'YulangClosure.NativeValuePorts.Port.variant.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.boolPositive.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.boolPositive.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.boolPositive =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.boolPositive.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.function.inj

```lean
@YulangClosure.NativeValuePorts.Port.function.inj : ∀ {field field_1 : YulangClosure.NativeValuePorts.FunctionField},
  YulangClosure.NativeValuePorts.Port.function field = YulangClosure.NativeValuePorts.Port.function field_1 →
    field = field_1
'YulangClosure.NativeValuePorts.Port.function.inj' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.variantChildren.match_1.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.variantChildren.match_1.eq_1 : ∀
  (motive : Nat → List YulangClosure.NativeValuePorts.Alternative → Sort u_1) (x : Nat) (h_1 : (x : Nat) → motive x [])
  (h_2 :
    (index : Nat) →
      (actual : YulangClosure.NativeValuePorts.Alternative) →
        (rest : List YulangClosure.NativeValuePorts.Alternative) → motive index (actual :: rest)),
  (match x, [] with
    | x, [] => h_1 x
    | index, actual :: rest => h_2 index actual rest) =
    h_1 x
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.variantChildren.match_1.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.build_flow_exact

```lean
@YulangClosure.NativeValuePorts.build_flow_exact : ∀ {arena after : YulangClosure.NativeValuePorts.Arena}
  {parent : YulangClosure.NativeValuePorts.Key} {port : YulangClosure.NativeValuePorts.Port}
  {flow : YulangClosure.NativeValuePorts.Flow},
  YulangClosure.NativeValuePorts.buildFlow arena parent port = Option.some (after, flow) →
    arena.Extends after ∧ YulangClosure.NativeValuePorts.FlowResult after parent port flow
'YulangClosure.NativeValuePorts.build_flow_exact' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.Cursor.mk.inj

```lean
@YulangClosure.NativeValuePorts.Cursor.mk.inj : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {done todo : List YulangClosure.NativeValuePorts.Child} {pending : Option YulangClosure.NativeValuePorts.Receipt}
  {records : List YulangClosure.NativeValuePorts.Work} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {arena_1 : YulangClosure.NativeValuePorts.Arena} {done_1 todo_1 : List YulangClosure.NativeValuePorts.Child}
  {pending_1 : Option YulangClosure.NativeValuePorts.Receipt} {records_1 : List YulangClosure.NativeValuePorts.Work}
  {queue_1 : List YulangClosure.NativeValuePorts.NativeWork},
  { arena := arena, done := done, todo := todo, pending := pending, records := records, queue := queue } =
      { arena := arena_1, done := done_1, todo := todo_1, pending := pending_1, records := records_1,
        queue := queue_1 } →
    arena = arena_1 ∧ done = done_1 ∧ todo = todo_1 ∧ pending = pending_1 ∧ records = records_1 ∧ queue = queue_1
'YulangClosure.NativeValuePorts.Cursor.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_2 : ∀ (a : List Nat)
  (a_1 b : List YulangClosure.NativeValuePorts.Protection),
  ¬a_1 = b → { stamped := a, scopes := a_1 } = { stamped := a, scopes := b } → False
'YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.inj : ∀ {term term_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant term =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant term_1 →
    term = term_1
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.nonidentity_effect_self_rejected

```lean
YulangClosure.NativeValuePorts.nonidentity_effect_self_rejected : ∀ (pairContext : Nat) (sources : Option Nat)
  (flow : YulangClosure.NativeValuePorts.Flow) (endpoint : YulangClosure.NativeMergeExpansion.Endpoint),
  flow.transformer ≠ 0 →
    ¬YulangClosure.NativeValuePorts.Allowed
        { pair := YulangClosure.NativeValuePorts.Pair.effect endpoint endpoint, context := pairContext,
          sources := sources, flow := flow }
'YulangClosure.NativeValuePorts.nonidentity_effect_self_rejected' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Alternative.mk.injEq

```lean
YulangClosure.NativeValuePorts.Alternative.mk.injEq : ∀ (tag : Nat) (payloads : List Nat) (tag_1 : Nat)
  (payloads_1 : List Nat),
  ({ tag := tag, payloads := payloads } = { tag := tag_1, payloads := payloads_1 }) =
    (tag = tag_1 ∧ payloads = payloads_1)
'YulangClosure.NativeValuePorts.Alternative.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.flow_result_kept

```lean
@YulangClosure.NativeValuePorts.flow_result_kept : ∀ {before after : YulangClosure.NativeValuePorts.Arena},
  before.Extends after →
    ∀ {parent : YulangClosure.NativeValuePorts.Key} {port : YulangClosure.NativeValuePorts.Port}
      {flow : YulangClosure.NativeValuePorts.Flow},
      YulangClosure.NativeValuePorts.FlowResult before parent port flow →
        YulangClosure.NativeValuePorts.FlowResult after parent port flow
'YulangClosure.NativeValuePorts.flow_result_kept' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.FunctionTerms.mk.inj

```lean
@YulangClosure.NativeValuePorts.FunctionTerms.mk.inj : ∀
  {argument argumentEffect resultEffect result argument_1 argumentEffect_1 resultEffect_1 result_1 : Nat},
  { argument := argument, argumentEffect := argumentEffect, resultEffect := resultEffect, result := result } =
      { argument := argument_1, argumentEffect := argumentEffect_1, resultEffect := resultEffect_1,
        result := result_1 } →
    argument = argument_1 ∧ argumentEffect = argumentEffect_1 ∧ resultEffect = resultEffect_1 ∧ result = result_1
'YulangClosure.NativeValuePorts.FunctionTerms.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_10

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_10 : ∀ (index lowerIndex upperIndex payloadIndex : Nat),
  YulangClosure.NativeValuePorts.Port.tuple index =
      YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_10' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.CursorValid.pending

```lean
@YulangClosure.NativeValuePorts.CursorValid.pending : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue cursor →
    ∀ (receipt : YulangClosure.NativeValuePorts.Receipt),
      cursor.pending = Option.some receipt →
        ∃ child rest,
          cursor.todo = child :: rest ∧
            YulangClosure.NativeValuePorts.AdmissionResult cursor.arena views qv qe parent post derived child receipt
'YulangClosure.NativeValuePorts.CursorValid.pending' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Flow.mk.injEq

```lean
YulangClosure.NativeValuePorts.Flow.mk.injEq : ∀ (transformer : Nat)
  (demand : Option YulangClosure.NativeContextExpansion.ScopedDemand) (transformer_1 : Nat)
  (demand_1 : Option YulangClosure.NativeContextExpansion.ScopedDemand),
  ({ transformer := transformer, demand := demand } = { transformer := transformer_1, demand := demand_1 }) =
    (transformer = transformer_1 ∧ demand = demand_1)
'YulangClosure.NativeValuePorts.Flow.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_3 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Option Nat) (a_2 : Option (Nat × Nat)) (b : Option Nat) (b_1 : Option (Nat × Nat)),
  ¬a_1 = b → { task := a, relation := a_1, replayAck := a_2 } = { task := a, relation := b, replayAck := b_1 } → False
'YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Arena.mk.injEq

```lean
YulangClosure.NativeValuePorts.Arena.mk.injEq : ∀ (contexts : List YulangClosure.NativeContextExpansion.Expr)
  (transformers : List YulangClosure.NativeValuePorts.Transformer) (relations : List YulangClosure.NativeValuePorts.Key)
  (contexts_1 : List YulangClosure.NativeContextExpansion.Expr)
  (transformers_1 : List YulangClosure.NativeValuePorts.Transformer)
  (relations_1 : List YulangClosure.NativeValuePorts.Key),
  ({ contexts := contexts, transformers := transformers, relations := relations } =
      { contexts := contexts_1, transformers := transformers_1, relations := relations_1 }) =
    (contexts = contexts_1 ∧ transformers = transformers_1 ∧ relations = relations_1)
'YulangClosure.NativeValuePorts.Arena.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.admit_constructs

```lean
@YulangClosure.NativeValuePorts.admit_constructs : ∀ {arena after : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.admit arena views qv qe parent post derived child = Option.some (after, receipt) →
    arena.Extends after ∧
      YulangClosure.NativeValuePorts.AdmissionResult after views qv qe parent post derived child receipt
'YulangClosure.NativeValuePorts.admit_constructs' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.sizeOf_spec : ∀ (term : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord term) = 1 + SizeOf.sizeOf term
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.transformer_constructed

```lean
YulangClosure.NativeValuePorts.transformer_constructed : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (transformer : YulangClosure.NativeValuePorts.Transformer),
  (arena.transformer transformer).fst.transformerAt (arena.transformer transformer).snd = Option.some transformer ∧
    arena.Extends (arena.transformer transformer).fst
'YulangClosure.NativeValuePorts.transformer_constructed' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.arena_extends_refl

```lean
YulangClosure.NativeValuePorts.arena_extends_refl : ∀ (arena : YulangClosure.NativeValuePorts.Arena),
  arena.Extends arena
'YulangClosure.NativeValuePorts.arena_extends_refl' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_3 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction term →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction term = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.build_context_formed

```lean
@YulangClosure.NativeValuePorts.build_context_formed : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {weight : Option Nat} {post : Nat} {swap : Bool},
  YulangClosure.NativeValuePorts.ContextsFormed arena.contexts →
    post ≤ arena.contexts.length →
      YulangClosure.NativeValuePorts.ContextsFormed
          (YulangClosure.NativeValuePorts.buildContext arena weight post swap).fst.contexts ∧
        (YulangClosure.NativeValuePorts.buildContext arena weight post swap).snd ≤
          (YulangClosure.NativeValuePorts.buildContext arena weight post swap).fst.contexts.length
'YulangClosure.NativeValuePorts.build_context_formed' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.contextInputs.eq_5

```lean
YulangClosure.NativeValuePorts.contextInputs.eq_5 : ∀ (input : Nat),
  YulangClosure.NativeValuePorts.contextInputs (YulangClosure.NativeContextExpansion.Expr.without input) = [input]
'YulangClosure.NativeValuePorts.contextInputs.eq_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_8

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_8 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : YulangClosure.NativeValuePorts.Port) (b : YulangClosure.NativeValuePorts.Key)
  (b_1 : YulangClosure.NativeValuePorts.Port),
  ¬a_1 = b →
    YulangClosure.NativeValuePorts.Dependency.port a a_1 a_2 = YulangClosure.NativeValuePorts.Dependency.port a b b_1 →
      False
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_8' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_1

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_1 : ∀
  (motive : YulangClosure.NativeValuePorts.FunctionField → Sort u_1)
  (h_1 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argument)
  (h_2 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.result)
  (h_3 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argumentEffect)
  (h_4 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.resultEffect),
  (match YulangClosure.NativeValuePorts.FunctionField.argument with
    | YulangClosure.NativeValuePorts.FunctionField.argument => h_1 ()
    | YulangClosure.NativeValuePorts.FunctionField.result => h_2 ()
    | YulangClosure.NativeValuePorts.FunctionField.argumentEffect => h_3 ()
    | YulangClosure.NativeValuePorts.FunctionField.resultEffect => h_4 ()) =
    h_1 ()
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_3 : ∀ (a a_1 a_2 a_3 b b_1 : Nat),
  ¬a_2 = b →
    { argument := a, argumentEffect := a_1, resultEffect := a_2, result := a_3 } =
        { argument := a, argumentEffect := a_1, resultEffect := b, result := b_1 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.contextInputs.eq_1

```lean
YulangClosure.NativeValuePorts.contextInputs.eq_1 : ∀ (weight input : Nat),
  YulangClosure.NativeValuePorts.contextInputs (YulangClosure.NativeContextExpansion.Expr.prefix weight input) = [input]
'YulangClosure.NativeValuePorts.contextInputs.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Child.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Child.mk.sizeOf_spec : ∀ (port : YulangClosure.NativeValuePorts.Port)
  (task : YulangClosure.NativeValuePorts.Pair),
  SizeOf.sizeOf { port := port, task := task } = 1 + SizeOf.sizeOf port + SizeOf.sizeOf task
'YulangClosure.NativeValuePorts.Child.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.arena_extends_trans

```lean
@YulangClosure.NativeValuePorts.arena_extends_trans : ∀ {a b c : YulangClosure.NativeValuePorts.Arena},
  a.Extends b → b.Extends c → a.Extends c
'YulangClosure.NativeValuePorts.arena_extends_trans' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Witness.function_drive_whole

```lean
YulangClosure.NativeValuePorts.Witness.function_drive_whole : ∃ cursor,
  YulangClosure.NativeValuePorts.Witness.completed = Option.some cursor ∧
    cursor.pending = Option.none ∧
      ∃ jobs,
        List.map YulangClosure.NativeValuePorts.Work.source jobs = YulangClosure.NativeValuePorts.Witness.children ∧
          cursor.queue = List.map YulangClosure.NativeValuePorts.Work.native jobs ∧
            (∀ (work : YulangClosure.NativeValuePorts.Work),
                work ∈ jobs →
                  YulangClosure.NativeValuePorts.AdmissionResult cursor.arena
                    YulangClosure.NativeValuePorts.Witness.views id id YulangClosure.NativeValuePorts.Witness.parent 1
                    Bool.true work.source work.receipt) ∧
              ∀ (work : YulangClosure.NativeValuePorts.Work), work ∈ jobs → work.native.replayAck = Option.none
'YulangClosure.NativeValuePorts.Witness.function_drive_whole' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.context_length

```lean
YulangClosure.NativeValuePorts.context_length : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (node : YulangClosure.NativeContextExpansion.Expr), arena.contexts.length ≤ (arena.context node).fst.contexts.length
'YulangClosure.NativeValuePorts.context_length' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.Cursor.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Cursor.mk.sizeOf_spec : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (done todo : List YulangClosure.NativeValuePorts.Child) (pending : Option YulangClosure.NativeValuePorts.Receipt)
  (records : List YulangClosure.NativeValuePorts.Work) (queue : List YulangClosure.NativeValuePorts.NativeWork),
  SizeOf.sizeOf { arena := arena, done := done, todo := todo, pending := pending, records := records, queue := queue } =
    1 + SizeOf.sizeOf arena + SizeOf.sizeOf done + SizeOf.sizeOf todo + SizeOf.sizeOf pending + SizeOf.sizeOf records +
      SizeOf.sizeOf queue
'YulangClosure.NativeValuePorts.Cursor.mk.sizeOf_spec' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_3

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_3 : ∀
  (motive : YulangClosure.NativeValuePorts.FunctionField → Sort u_1)
  (h_1 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argument)
  (h_2 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.result)
  (h_3 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argumentEffect)
  (h_4 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.resultEffect),
  (match YulangClosure.NativeValuePorts.FunctionField.argumentEffect with
    | YulangClosure.NativeValuePorts.FunctionField.argument => h_1 ()
    | YulangClosure.NativeValuePorts.FunctionField.result => h_2 ()
    | YulangClosure.NativeValuePorts.FunctionField.argumentEffect => h_3 ()
    | YulangClosure.NativeValuePorts.FunctionField.resultEffect => h_4 ()) =
    h_3 ()
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Dependency.derived.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Dependency.derived.sizeOf_spec : ∀ (parent child : YulangClosure.NativeValuePorts.Key),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Dependency.derived parent child) =
    1 + SizeOf.sizeOf parent + SizeOf.sizeOf child
'YulangClosure.NativeValuePorts.Dependency.derived.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.intern_length

```lean
@YulangClosure.NativeValuePorts.intern_length : ∀ {α : Type u_1} (items : List α) [inst : DecidableEq α] (value : α),
  items.length ≤ (YulangClosure.NativeValuePorts.intern items value).fst.length
'YulangClosure.NativeValuePorts.intern_length' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_2 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction term →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction term = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_3 : ∀ (a : Nat) (a_1 : Bool) (a_2 : List Nat)
  (b : Bool) (b_1 : List Nat),
  ¬a_1 = b →
    { scope := a, keepInitial := a_1, missing := a_2 } = { scope := a, keepInitial := b, missing := b_1 } → False
'YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.variantChildren.eq_2

```lean
YulangClosure.NativeValuePorts.variantChildren.eq_2 : ∀ (terms : YulangClosure.NativeValuePorts.TermEndpoints)
  (upper : List YulangClosure.NativeValuePorts.Alternative) (x : Nat)
  (actual : YulangClosure.NativeValuePorts.Alternative) (rest : List YulangClosure.NativeValuePorts.Alternative),
  YulangClosure.NativeValuePorts.variantChildren terms upper x (actual :: rest) =
    if upper.any (YulangClosure.NativeValuePorts.matching actual) = Bool.true then
      Except.map (fun x_1 => YulangClosure.NativeValuePorts.variantArmChildren terms x actual upper ++ x_1)
        (YulangClosure.NativeValuePorts.variantChildren terms upper (x + 1) rest)
    else Except.error x
'YulangClosure.NativeValuePorts.variantChildren.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_9

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_9 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : YulangClosure.NativeValuePorts.Port) (b b_1 : YulangClosure.NativeValuePorts.Key)
  (b_2 : YulangClosure.NativeValuePorts.Port),
  ¬a = b →
    YulangClosure.NativeValuePorts.Dependency.port a a_1 a_2 =
        YulangClosure.NativeValuePorts.Dependency.port b b_1 b_2 →
      False
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_9' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.dispatch_step_valid._simp_1_2

```lean
@YulangClosure.NativeValuePorts.dispatch_step_valid._simp_1_2 : ∀ {α : Type u_1} {a : α} {s t : List α},
  (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t)
'YulangClosure.NativeValuePorts.dispatch_step_valid._simp_1_2' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_1 : ∀
  (a a_1 : YulangClosure.NativeValuePorts.ValueEndpoint),
  YulangClosure.NativeValuePorts.Pair.value a a_1 = YulangClosure.NativeValuePorts.Pair.value a a_1
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.strPositive.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.strPositive.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.strPositive =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.strPositive.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.AdmissionResult.port_same

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.port_same : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    receipt.port = child.port
'YulangClosure.NativeValuePorts.AdmissionResult.port_same' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.injEq : ∀ (term arity term_1 arity_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple term arity =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple term_1 arity_1) =
    (term = term_1 ∧ arity = arity_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_7

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_7 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant a =
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant a
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_7' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.variant.injEq

```lean
YulangClosure.NativeValuePorts.Port.variant.injEq : ∀
  (lowerIndex upperIndex payloadIndex lowerIndex_1 upperIndex_1 payloadIndex_1 : Nat),
  (YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex =
      YulangClosure.NativeValuePorts.Port.variant lowerIndex_1 upperIndex_1 payloadIndex_1) =
    (lowerIndex = lowerIndex_1 ∧ upperIndex = upperIndex_1 ∧ payloadIndex = payloadIndex_1)
'YulangClosure.NativeValuePorts.Port.variant.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.injEq : ∀ (term term_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant term =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant term_1) =
    (term = term_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Arena.contextAt.eq_1

```lean
YulangClosure.NativeValuePorts.Arena.contextAt.eq_1 : ∀ (arena : YulangClosure.NativeValuePorts.Arena) (id : Nat),
  arena.contextAt id = if id = 0 then Option.none else arena.contexts[id - 1]?
'YulangClosure.NativeValuePorts.Arena.contextAt.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_11

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_11 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord a =
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord a
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_11' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.TermEndpoints.mk.inj

```lean
@YulangClosure.NativeValuePorts.TermEndpoints.mk.inj : ∀
  {positiveValue negativeValue : Nat → YulangClosure.NativeValuePorts.ValueEndpoint}
  {positiveEffect negativeEffect : Nat → YulangClosure.NativeMergeExpansion.Endpoint}
  {positiveValue_1 negativeValue_1 : Nat → YulangClosure.NativeValuePorts.ValueEndpoint}
  {positiveEffect_1 negativeEffect_1 : Nat → YulangClosure.NativeMergeExpansion.Endpoint},
  { positiveValue := positiveValue, negativeValue := negativeValue, positiveEffect := positiveEffect,
        negativeEffect := negativeEffect } =
      { positiveValue := positiveValue_1, negativeValue := negativeValue_1, positiveEffect := positiveEffect_1,
        negativeEffect := negativeEffect_1 } →
    positiveValue = positiveValue_1 ∧
      negativeValue = negativeValue_1 ∧ positiveEffect = positiveEffect_1 ∧ negativeEffect = negativeEffect_1
'YulangClosure.NativeValuePorts.TermEndpoints.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.AdmissionResult.context_exact

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.context_exact : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    ∃ weight,
      YulangClosure.NativeValuePorts.sourceWeight views (YulangClosure.NativeValuePorts.Pair.rename qv qe child.task) =
          Option.some weight ∧
        YulangClosure.NativeValuePorts.ContextResult arena weight post child.port.swaps receipt.child.context
'YulangClosure.NativeValuePorts.AdmissionResult.context_exact' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_4 : ∀
  (a : List YulangClosure.NativeContextExpansion.Expr) (a_1 : List YulangClosure.NativeValuePorts.Transformer)
  (a_2 : List YulangClosure.NativeValuePorts.Key) (b : List YulangClosure.NativeContextExpansion.Expr)
  (b_1 : List YulangClosure.NativeValuePorts.Transformer) (b_2 : List YulangClosure.NativeValuePorts.Key),
  ¬a = b →
    { contexts := a, transformers := a_1, relations := a_2 } =
        { contexts := b, transformers := b_1, relations := b_2 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_14

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_14 : ∀ (a b : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord a =
        YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_14' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.injEq : ∀ (term term_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant term =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant term_1) =
    (term = term_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Arena.context.eq_1

```lean
YulangClosure.NativeValuePorts.Arena.context.eq_1 : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (node : YulangClosure.NativeContextExpansion.Expr),
  arena.context node =
    ({ contexts := (YulangClosure.NativeValuePorts.intern arena.contexts node).fst, transformers := arena.transformers,
        relations := arena.relations },
      (YulangClosure.NativeValuePorts.intern arena.contexts node).snd + 1)
'YulangClosure.NativeValuePorts.Arena.context.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.strNegative.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.strNegative.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.strNegative =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.strNegative.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.contextInputs.eq_3

```lean
YulangClosure.NativeValuePorts.contextInputs.eq_3 : ∀ (input : Nat),
  YulangClosure.NativeValuePorts.contextInputs (YulangClosure.NativeContextExpansion.Expr.swap input) = [input]
'YulangClosure.NativeValuePorts.contextInputs.eq_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.unitNegative.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.unitNegative.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.unitNegative =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.unitNegative.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.FunctionField.argument.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.FunctionField.argument.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.FunctionField.argument =
  1
'YulangClosure.NativeValuePorts.FunctionField.argument.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_11

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_11 : ∀ (parent : YulangClosure.NativeValuePorts.Key)
  (lower upper : YulangClosure.NativeMergeExpansion.Endpoint),
  parent.pair = YulangClosure.NativeValuePorts.Pair.effect lower upper →
    YulangClosure.NativeValuePorts.Pair.effect lower upper = parent.pair
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_11' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.injEq : ∀ (term term_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord term =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord term_1) =
    (term = term_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_3 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : Nat) (a_3 : YulangClosure.NativeValuePorts.Port) (a_4 : Bool) (b : YulangClosure.NativeValuePorts.Port)
  (b_1 : Bool),
  ¬a_3 = b →
    { parent := a, child := a_1, relation := a_2, port := a_3, derived := a_4 } =
        { parent := a, child := a_1, relation := a_2, port := b, derived := b_1 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_15

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_15 : ∀ (a a_1 b b_1 : Nat),
  ¬a = b → YulangClosure.NativeValuePorts.Port.record a a_1 = YulangClosure.NativeValuePorts.Port.record b b_1 → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_15' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Dependency.port.inj

```lean
@YulangClosure.NativeValuePorts.Dependency.port.inj : ∀ {parent child : YulangClosure.NativeValuePorts.Key}
  {port : YulangClosure.NativeValuePorts.Port} {parent_1 child_1 : YulangClosure.NativeValuePorts.Key}
  {port_1 : YulangClosure.NativeValuePorts.Port},
  YulangClosure.NativeValuePorts.Dependency.port parent child port =
      YulangClosure.NativeValuePorts.Dependency.port parent_1 child_1 port_1 →
    parent = parent_1 ∧ child = child_1 ∧ port = port_1
'YulangClosure.NativeValuePorts.Dependency.port.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_21

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_21 : ∀ (a a_1 a_2 b : Nat),
  ¬a_2 = b →
    YulangClosure.NativeValuePorts.Port.variant a a_1 a_2 = YulangClosure.NativeValuePorts.Port.variant a a_1 b → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_21' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_16

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_16 : ∀ (a a_1 b : Nat),
  ¬a_1 = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple a a_1 =
        YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple a b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_16' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_4

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_4 : ∀
  (motive : YulangClosure.NativeContextExpansion.Expr → Sort u_1) (input certificate : Nat)
  (h_1 : (weight input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.prefix weight input))
  (h_2 : (input weight : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.suffix input weight))
  (h_3 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.swap input))
  (h_4 : (input certificate : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.both input certificate))
  (h_5 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.without input))
  (h_6 : (lower upper : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.replay lower upper)),
  (match YulangClosure.NativeContextExpansion.Expr.both input certificate with
    | YulangClosure.NativeContextExpansion.Expr.prefix weight input => h_1 weight input
    | YulangClosure.NativeContextExpansion.Expr.suffix input weight => h_2 input weight
    | YulangClosure.NativeContextExpansion.Expr.swap input => h_3 input
    | YulangClosure.NativeContextExpansion.Expr.both input certificate => h_4 input certificate
    | YulangClosure.NativeContextExpansion.Expr.without input => h_5 input
    | YulangClosure.NativeContextExpansion.Expr.replay lower upper => h_6 lower upper) =
    h_4 input certificate
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_10

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_10 : ∀ (parent : YulangClosure.NativeValuePorts.Key)
  (lower upper : YulangClosure.NativeValuePorts.ValueEndpoint),
  parent.pair = YulangClosure.NativeValuePorts.Pair.value lower upper →
    YulangClosure.NativeValuePorts.Pair.value lower upper = parent.pair
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_10' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_5 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant term →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeVariant term = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_4 : ∀ (a b : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction a =
        YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.finished_pending_none

```lean
@YulangClosure.NativeValuePorts.finished_pending_none : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue cursor →
    cursor.todo = [] → cursor.pending = Option.none
'YulangClosure.NativeValuePorts.finished_pending_none' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_12

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_12 : ∀ (parent : YulangClosure.NativeValuePorts.Key),
  parent.pair = parent.pair
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_12' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_16

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_16 : ∀
  (lowerIndex upperIndex lowerIndex_1 upperIndex_1 payloadIndex : Nat),
  YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex =
      YulangClosure.NativeValuePorts.Port.variant lowerIndex_1 upperIndex_1 payloadIndex →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_16' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Work.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Work.mk.sizeOf_spec : ∀ (source : YulangClosure.NativeValuePorts.Child)
  (receipt : YulangClosure.NativeValuePorts.Receipt),
  SizeOf.sizeOf { source := source, receipt := receipt } = 1 + SizeOf.sizeOf source + SizeOf.sizeOf receipt
'YulangClosure.NativeValuePorts.Work.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.boolNegative.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.boolNegative.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.boolNegative =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.boolNegative.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_1 : ∀ (a : List Nat)
  (a_1 : List YulangClosure.NativeValuePorts.Protection),
  { stamped := a, scopes := a_1 } = { stamped := a, scopes := a_1 }
'YulangClosure.NativeValuePorts.instDecidableEqTransformer.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.NativeWork.mk.inj

```lean
@YulangClosure.NativeValuePorts.NativeWork.mk.inj : ∀ {task : YulangClosure.NativeValuePorts.Pair}
  {relation : Option Nat} {replayAck : Option (Nat × Nat)} {task_1 : YulangClosure.NativeValuePorts.Pair}
  {relation_1 : Option Nat} {replayAck_1 : Option (Nat × Nat)},
  { task := task, relation := relation, replayAck := replayAck } =
      { task := task_1, relation := relation_1, replayAck := replayAck_1 } →
    task = task_1 ∧ relation = relation_1 ∧ replayAck = replayAck_1
'YulangClosure.NativeValuePorts.NativeWork.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.intNegative.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.intNegative.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.intNegative =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.intNegative.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_2 : ∀ (a : Nat)
  (a_1 b : Option YulangClosure.NativeContextExpansion.ScopedDemand),
  ¬a_1 = b → { transformer := a, demand := a_1 } = { transformer := a, demand := b } → False
'YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.topNegative.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.topNegative.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.topNegative =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.topNegative.sizeOf_spec' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_3.eq_2

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_3.eq_2 : ∀
  (motive : Option YulangClosure.NativeValuePorts.Receipt → Sort u_1) (receipt : YulangClosure.NativeValuePorts.Receipt)
  (h_1 : Unit → motive Option.none)
  (h_2 : (receipt : YulangClosure.NativeValuePorts.Receipt) → motive (Option.some receipt)),
  (match Option.some receipt with
    | Option.none => h_1 ()
    | Option.some receipt => h_2 receipt) =
    h_2 receipt
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_3.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_1 : ∀
  (a : YulangClosure.NativeValuePorts.FunctionField),
  YulangClosure.NativeValuePorts.Port.function a = YulangClosure.NativeValuePorts.Port.function a
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_1 : ∀ (a a_1 a_2 a_3 : Nat),
  { argument := a, argumentEffect := a_1, resultEffect := a_2, result := a_3 } =
    { argument := a, argumentEffect := a_1, resultEffect := a_2, result := a_3 }
'YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_1 : ∀
  (a a_1 : YulangClosure.NativeValuePorts.Key),
  YulangClosure.NativeValuePorts.Dependency.derived a a_1 = YulangClosure.NativeValuePorts.Dependency.derived a a_1
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Pair.value.inj

```lean
@YulangClosure.NativeValuePorts.Pair.value.inj : ∀
  {lower upper lower_1 upper_1 : YulangClosure.NativeValuePorts.ValueEndpoint},
  YulangClosure.NativeValuePorts.Pair.value lower upper = YulangClosure.NativeValuePorts.Pair.value lower_1 upper_1 →
    lower = lower_1 ∧ upper = upper_1
'YulangClosure.NativeValuePorts.Pair.value.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.variant_children_no_omission

```lean
@YulangClosure.NativeValuePorts.variant_children_no_omission : ∀ {terms : YulangClosure.NativeValuePorts.TermEndpoints}
  {upper lower : List YulangClosure.NativeValuePorts.Alternative} {start : Nat}
  {children : List YulangClosure.NativeValuePorts.Child},
  YulangClosure.NativeValuePorts.variantChildren terms upper start lower = Except.ok children →
    ∀ (offset : Nat) (actual : YulangClosure.NativeValuePorts.Alternative),
      lower[offset]? = Option.some actual →
        ∀ (child : YulangClosure.NativeValuePorts.Child),
          child ∈ YulangClosure.NativeValuePorts.variantArmChildren terms (start + offset) actual upper →
            child ∈ children
'YulangClosure.NativeValuePorts.variant_children_no_omission' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.AdmissionResult.pair_exact

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.pair_exact : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    receipt.child.pair = YulangClosure.NativeValuePorts.Pair.rename qv qe child.task
'YulangClosure.NativeValuePorts.AdmissionResult.pair_exact' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Allowed.eq_1

```lean
YulangClosure.NativeValuePorts.Allowed.eq_1 : ∀ (key : YulangClosure.NativeValuePorts.Key),
  YulangClosure.NativeValuePorts.Allowed key =
    match key.pair with
    | YulangClosure.NativeValuePorts.Pair.value lower upper => key.flow.transformer = 0
    | YulangClosure.NativeValuePorts.Pair.effect lower upper =>
      key.flow.demand = Option.none ∧ (key.flow.transformer = 0 ∨ lower ≠ upper)
'YulangClosure.NativeValuePorts.Allowed.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.TermEndpoints.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.TermEndpoints.mk.sizeOf_spec : ∀
  (positiveValue negativeValue : Nat → YulangClosure.NativeValuePorts.ValueEndpoint)
  (positiveEffect negativeEffect : Nat → YulangClosure.NativeMergeExpansion.Endpoint),
  SizeOf.sizeOf
      { positiveValue := positiveValue, negativeValue := negativeValue, positiveEffect := positiveEffect,
        negativeEffect := negativeEffect } =
    1
'YulangClosure.NativeValuePorts.TermEndpoints.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_8

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_8 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term arity : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple term arity →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple term arity = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_8' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.record.injEq

```lean
YulangClosure.NativeValuePorts.Port.record.injEq : ∀ (lowerIndex upperIndex lowerIndex_1 upperIndex_1 : Nat),
  (YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex =
      YulangClosure.NativeValuePorts.Port.record lowerIndex_1 upperIndex_1) =
    (lowerIndex = lowerIndex_1 ∧ upperIndex = upperIndex_1)
'YulangClosure.NativeValuePorts.Port.record.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_2 : ∀ (a : YulangClosure.NativeValuePorts.Child)
  (a_1 b : YulangClosure.NativeValuePorts.Receipt),
  ¬a_1 = b → { source := a, receipt := a_1 } = { source := a, receipt := b } → False
'YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_6

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_6 : ∀
  (a a_1 : YulangClosure.NativeMergeExpansion.Endpoint),
  YulangClosure.NativeValuePorts.Pair.effect a a_1 = YulangClosure.NativeValuePorts.Pair.effect a a_1
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_6' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_22

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_22 : ∀ (a a_1 a_2 b b_1 : Nat),
  ¬a_1 = b →
    YulangClosure.NativeValuePorts.Port.variant a a_1 a_2 = YulangClosure.NativeValuePorts.Port.variant a b b_1 → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_22' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.result_effect_scope

```lean
@YulangClosure.NativeValuePorts.result_effect_scope : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {task : YulangClosure.NativeValuePorts.Pair} {receipt : YulangClosure.NativeValuePorts.Receipt}
  {demand : YulangClosure.NativeContextExpansion.ScopedDemand},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived
      { port := YulangClosure.NativeValuePorts.Port.function YulangClosure.NativeValuePorts.FunctionField.resultEffect,
        task := task }
      receipt →
    parent.flow.demand = Option.some demand →
      YulangClosure.NativeValuePorts.genuineDemand parent demand ∧
        receipt.child.flow.demand = Option.none ∧
          arena.transformerAt receipt.child.flow.transformer =
            Option.some (YulangClosure.NativeValuePorts.Transformer.protect demand.outputScope demand.inputRoute)
'YulangClosure.NativeValuePorts.result_effect_scope' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.inj : ∀ {term arity term_1 arity_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple term arity =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple term_1 arity_1 →
    term = term_1 ∧ arity = arity_1
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_19

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_19 : ∀ (a a_1 b : Nat),
  ¬a_1 = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple a a_1 =
        YulangClosure.NativeValuePorts.ValueEndpoint.negativeTuple a b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_19' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Work.mk.injEq

```lean
YulangClosure.NativeValuePorts.Work.mk.injEq : ∀ (source : YulangClosure.NativeValuePorts.Child)
  (receipt : YulangClosure.NativeValuePorts.Receipt) (source_1 : YulangClosure.NativeValuePorts.Child)
  (receipt_1 : YulangClosure.NativeValuePorts.Receipt),
  ({ source := source, receipt := receipt } = { source := source_1, receipt := receipt_1 }) =
    (source = source_1 ∧ receipt = receipt_1)
'YulangClosure.NativeValuePorts.Work.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_1 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Option Nat) (a_2 : Option (Nat × Nat)),
  { task := a, relation := a_1, replayAck := a_2 } = { task := a, relation := a_1, replayAck := a_2 }
'YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.variant.inj

```lean
@YulangClosure.NativeValuePorts.Port.variant.inj : ∀
  {lowerIndex upperIndex payloadIndex lowerIndex_1 upperIndex_1 payloadIndex_1 : Nat},
  YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex =
      YulangClosure.NativeValuePorts.Port.variant lowerIndex_1 upperIndex_1 payloadIndex_1 →
    lowerIndex = lowerIndex_1 ∧ upperIndex = upperIndex_1 ∧ payloadIndex = payloadIndex_1
'YulangClosure.NativeValuePorts.Port.variant.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Receipt.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Receipt.mk.sizeOf_spec : ∀ (parent child : YulangClosure.NativeValuePorts.Key)
  (relation : Nat) (port : YulangClosure.NativeValuePorts.Port) (derived : Bool),
  SizeOf.sizeOf { parent := parent, child := child, relation := relation, port := port, derived := derived } =
    1 + SizeOf.sizeOf parent + SizeOf.sizeOf child + SizeOf.sizeOf relation + SizeOf.sizeOf port + SizeOf.sizeOf derived
'YulangClosure.NativeValuePorts.Receipt.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.admission_result_kept

```lean
@YulangClosure.NativeValuePorts.admission_result_kept : ∀ {before after : YulangClosure.NativeValuePorts.Arena},
  before.Extends after →
    ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
      {derived : Bool} {child : YulangClosure.NativeValuePorts.Child}
      {receipt : YulangClosure.NativeValuePorts.Receipt},
      YulangClosure.NativeValuePorts.AdmissionResult before views qv qe parent post derived child receipt →
        YulangClosure.NativeValuePorts.AdmissionResult after views qv qe parent post derived child receipt
'YulangClosure.NativeValuePorts.admission_result_kept' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.function_children_whole

```lean
YulangClosure.NativeValuePorts.function_children_whole : ∀ (terms : YulangClosure.NativeValuePorts.TermEndpoints)
  (lower upper : YulangClosure.NativeValuePorts.FunctionTerms),
  List.map YulangClosure.NativeValuePorts.Child.port
        (YulangClosure.NativeValuePorts.functionChildren terms lower upper) =
      [YulangClosure.NativeValuePorts.Port.function YulangClosure.NativeValuePorts.FunctionField.argument,
        YulangClosure.NativeValuePorts.Port.function YulangClosure.NativeValuePorts.FunctionField.argumentEffect,
        YulangClosure.NativeValuePorts.Port.function YulangClosure.NativeValuePorts.FunctionField.resultEffect,
        YulangClosure.NativeValuePorts.Port.function YulangClosure.NativeValuePorts.FunctionField.result] ∧
    (YulangClosure.NativeValuePorts.functionChildren terms lower upper).length = 4
'YulangClosure.NativeValuePorts.function_children_whole' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_3 : ∀
  (a a_1 b b_1 : YulangClosure.NativeValuePorts.Key),
  ¬a = b →
    YulangClosure.NativeValuePorts.Dependency.derived a a_1 = YulangClosure.NativeValuePorts.Dependency.derived b b_1 →
      False
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.AdmissionResult.registered

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.registered : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    arena.relations[receipt.relation]? = Option.some receipt.child
'YulangClosure.NativeValuePorts.AdmissionResult.registered' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_12

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_12 : ∀ (lowerIndex upperIndex index : Nat),
  YulangClosure.NativeValuePorts.Port.record lowerIndex upperIndex = YulangClosure.NativeValuePorts.Port.tuple index →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_12' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.injEq

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.injEq : ∀ (term arity term_1 arity_1 : Nat),
  (YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple term arity =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple term_1 arity_1) =
    (term = term_1 ∧ arity = arity_1)
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveTuple.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.protect_other_exact

```lean
@YulangClosure.NativeValuePorts.protect_other_exact : ∀ {scope other input : Nat},
  other ≠ scope →
    ∀ (inputs scopes : Nat → Prop),
      (YulangClosure.NativeValuePorts.Transformer.protect scope input).protection inputs scopes other ↔ scopes other
'YulangClosure.NativeValuePorts.protect_other_exact' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Protection.mk.inj

```lean
@YulangClosure.NativeValuePorts.Protection.mk.inj : ∀ {scope : Nat} {keepInitial : Bool} {missing : List Nat}
  {scope_1 : Nat} {keepInitial_1 : Bool} {missing_1 : List Nat},
  { scope := scope, keepInitial := keepInitial, missing := missing } =
      { scope := scope_1, keepInitial := keepInitial_1, missing := missing_1 } →
    scope = scope_1 ∧ keepInitial = keepInitial_1 ∧ missing = missing_1
'YulangClosure.NativeValuePorts.Protection.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_8

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_8 : ∀
  (a a_1 b b_1 : YulangClosure.NativeMergeExpansion.Endpoint),
  ¬a = b → YulangClosure.NativeValuePorts.Pair.effect a a_1 = YulangClosure.NativeValuePorts.Pair.effect b b_1 → False
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_8' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_1 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : Nat) (a_3 : YulangClosure.NativeValuePorts.Port) (a_4 : Bool),
  { parent := a, child := a_1, relation := a_2, port := a_3, derived := a_4 } =
    { parent := a, child := a_1, relation := a_2, port := a_3, derived := a_4 }
'YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.DispatchRun.brecOn

```lean
@YulangClosure.NativeValuePorts.DispatchRun.brecOn : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {motive :
    (a a_1 : YulangClosure.NativeValuePorts.Cursor) →
      YulangClosure.NativeValuePorts.DispatchRun views qv qe parent post derived a a_1 → Prop}
  {a a_1 : YulangClosure.NativeValuePorts.Cursor}
  (t : YulangClosure.NativeValuePorts.DispatchRun views qv qe parent post derived a a_1),
  (∀ (a a_2 : YulangClosure.NativeValuePorts.Cursor)
      (t : YulangClosure.NativeValuePorts.DispatchRun views qv qe parent post derived a a_2),
      YulangClosure.NativeValuePorts.DispatchRun.below t → motive a a_2 t) →
    motive a a_1 t
'YulangClosure.NativeValuePorts.DispatchRun.brecOn' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Port.swaps._sparseCasesOn_1.else_eq

```lean
@YulangClosure.NativeValuePorts.Port.swaps._sparseCasesOn_1.else_eq : ∀
  {motive : YulangClosure.NativeValuePorts.Port → Sort u_1} (t : YulangClosure.NativeValuePorts.Port)
  (function :
    (field : YulangClosure.NativeValuePorts.FunctionField) →
      motive (YulangClosure.NativeValuePorts.Port.function field))
  («else» : Nat.hasNotBit 1 t.ctorIdx → motive t) (h : Nat.hasNotBit 1 t.ctorIdx),
  YulangClosure.NativeValuePorts.Port.swaps._sparseCasesOn_1 t function «else» = «else» h
'YulangClosure.NativeValuePorts.Port.swaps._sparseCasesOn_1.else_eq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.context_kept

```lean
@YulangClosure.NativeValuePorts.context_kept : ∀ {before after : YulangClosure.NativeValuePorts.Arena},
  before.Extends after →
    ∀ {id : Nat} {node : YulangClosure.NativeContextExpansion.Expr},
      before.contextAt id = Option.some node → after.contextAt id = Option.some node
'YulangClosure.NativeValuePorts.context_kept' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.contextInputs.eq_2

```lean
YulangClosure.NativeValuePorts.contextInputs.eq_2 : ∀ (input weight : Nat),
  YulangClosure.NativeValuePorts.contextInputs (YulangClosure.NativeContextExpansion.Expr.suffix input weight) = [input]
'YulangClosure.NativeValuePorts.contextInputs.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Flow.mk.inj

```lean
@YulangClosure.NativeValuePorts.Flow.mk.inj : ∀ {transformer : Nat}
  {demand : Option YulangClosure.NativeContextExpansion.ScopedDemand} {transformer_1 : Nat}
  {demand_1 : Option YulangClosure.NativeContextExpansion.ScopedDemand},
  { transformer := transformer, demand := demand } = { transformer := transformer_1, demand := demand_1 } →
    transformer = transformer_1 ∧ demand = demand_1
'YulangClosure.NativeValuePorts.Flow.mk.inj' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_7.eq_2

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_7.eq_2 : ∀
  (motive : Nat → YulangClosure.NativeValuePorts.Cursor → Sort u_1) (n : Nat)
  (cursor : YulangClosure.NativeValuePorts.Cursor)
  (h_1 : (cursor : YulangClosure.NativeValuePorts.Cursor) → motive 0 cursor)
  (h_2 : (n : Nat) → (cursor : YulangClosure.NativeValuePorts.Cursor) → motive n.succ cursor),
  (match n.succ, cursor with
    | 0, cursor => h_1 cursor
    | n.succ, cursor => h_2 n cursor) =
    h_2 n cursor
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.drive.match_7.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_2 : ∀ (a a_1 a_2 a_3 b : Nat),
  ¬a_3 = b →
    { argument := a, argumentEffect := a_1, resultEffect := a_2, result := a_3 } =
        { argument := a, argumentEffect := a_1, resultEffect := a_2, result := b } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqFunctionTerms.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_7

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_7 : ∀ (a : Nat),
  YulangClosure.NativeValuePorts.Port.tuple a = YulangClosure.NativeValuePorts.Port.tuple a
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_7' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Port.tuple.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Port.tuple.sizeOf_spec : ∀ (index : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Port.tuple index) = 1 + SizeOf.sizeOf index
'YulangClosure.NativeValuePorts.Port.tuple.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Witness.variant_duplicate_requirements

```lean
YulangClosure.NativeValuePorts.Witness.variant_duplicate_requirements : YulangClosure.NativeValuePorts.variantChildren
    YulangClosure.NativeValuePorts.Witness.terms [{ tag := 7, payloads := [2] }, { tag := 7, payloads := [3] }] 0
    [{ tag := 7, payloads := [1] }] =
  Except.ok
    [{ port := YulangClosure.NativeValuePorts.Port.variant 0 0 0,
        task :=
          YulangClosure.NativeValuePorts.Pair.value (YulangClosure.NativeValuePorts.ValueEndpoint.row 1)
            (YulangClosure.NativeValuePorts.ValueEndpoint.row 2) },
      { port := YulangClosure.NativeValuePorts.Port.variant 0 1 0,
        task :=
          YulangClosure.NativeValuePorts.Pair.value (YulangClosure.NativeValuePorts.ValueEndpoint.row 1)
            (YulangClosure.NativeValuePorts.ValueEndpoint.row 3) }]
'YulangClosure.NativeValuePorts.Witness.variant_duplicate_requirements' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_2 : ∀
  (a a_1 b : YulangClosure.NativeValuePorts.ValueEndpoint),
  ¬a_1 = b → YulangClosure.NativeValuePorts.Pair.value a a_1 = YulangClosure.NativeValuePorts.Pair.value a b → False
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.inj : ∀ {term term_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord term =
      YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord term_1 →
    term = term_1
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.intern_reuse_exact

```lean
@YulangClosure.NativeValuePorts.intern_reuse_exact : ∀ {α : Type u_1} [inst : DecidableEq α] (items : List α)
  (first second : α),
  (YulangClosure.NativeValuePorts.intern items first).snd =
      (YulangClosure.NativeValuePorts.intern (YulangClosure.NativeValuePorts.intern items first).fst second).snd →
    first = second
'YulangClosure.NativeValuePorts.intern_reuse_exact' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_3 : ∀ (a : YulangClosure.NativeValuePorts.Port)
  (a_1 : YulangClosure.NativeValuePorts.Pair) (b : YulangClosure.NativeValuePorts.Port)
  (b_1 : YulangClosure.NativeValuePorts.Pair), ¬a = b → { port := a, task := a_1 } = { port := b, task := b_1 } → False
'YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_3' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_2

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_2 : ∀
  (motive : YulangClosure.NativeValuePorts.FunctionField → Sort u_1)
  (h_1 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argument)
  (h_2 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.result)
  (h_3 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.argumentEffect)
  (h_4 : Unit → motive YulangClosure.NativeValuePorts.FunctionField.resultEffect),
  (match YulangClosure.NativeValuePorts.FunctionField.result with
    | YulangClosure.NativeValuePorts.FunctionField.argument => h_1 ()
    | YulangClosure.NativeValuePorts.FunctionField.result => h_2 ()
    | YulangClosure.NativeValuePorts.FunctionField.argumentEffect => h_3 ()
    | YulangClosure.NativeValuePorts.FunctionField.resultEffect => h_4 ()) =
    h_2 ()
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.buildFlow.match_1.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_3 : ∀
  (a : List YulangClosure.NativeContextExpansion.Expr) (a_1 : List YulangClosure.NativeValuePorts.Transformer)
  (a_2 : List YulangClosure.NativeValuePorts.Key) (b : List YulangClosure.NativeValuePorts.Transformer)
  (b_1 : List YulangClosure.NativeValuePorts.Key),
  ¬a_1 = b →
    { contexts := a, transformers := a_1, relations := a_2 } = { contexts := a, transformers := b, relations := b_1 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqArena.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_5 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Nat) (a_2 : Option Nat) (a_3 : YulangClosure.NativeValuePorts.Flow) (b : YulangClosure.NativeValuePorts.Pair)
  (b_1 : Nat) (b_2 : Option Nat) (b_3 : YulangClosure.NativeValuePorts.Flow),
  ¬a = b →
    { pair := a, context := a_1, sources := a_2, flow := a_3 } =
        { pair := b, context := b_1, sources := b_2, flow := b_3 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.intern_found

```lean
@YulangClosure.NativeValuePorts.intern_found : ∀ {α : Type u_1} [inst : DecidableEq α] (items : List α) (value : α),
  (YulangClosure.NativeValuePorts.intern items value).fst[(YulangClosure.NativeValuePorts.intern items value).snd]? =
    Option.some value
'YulangClosure.NativeValuePorts.intern_found' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_19

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_19 : ∀
  (lowerIndex upperIndex payloadIndex lowerIndex_1 upperIndex_1 : Nat),
  YulangClosure.NativeValuePorts.Port.variant lowerIndex upperIndex payloadIndex =
      YulangClosure.NativeValuePorts.Port.record lowerIndex_1 upperIndex_1 →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_19' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_8

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_8 : ∀ (a b : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant a =
        YulangClosure.NativeValuePorts.ValueEndpoint.positiveVariant b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_8' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Transformer.mk.inj

```lean
@YulangClosure.NativeValuePorts.Transformer.mk.inj : ∀ {stamped : List Nat}
  {scopes : List YulangClosure.NativeValuePorts.Protection} {stamped_1 : List Nat}
  {scopes_1 : List YulangClosure.NativeValuePorts.Protection},
  { stamped := stamped, scopes := scopes } = { stamped := stamped_1, scopes := scopes_1 } →
    stamped = stamped_1 ∧ scopes = scopes_1
'YulangClosure.NativeValuePorts.Transformer.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Protection.mk.injEq

```lean
YulangClosure.NativeValuePorts.Protection.mk.injEq : ∀ (scope : Nat) (keepInitial : Bool) (missing : List Nat)
  (scope_1 : Nat) (keepInitial_1 : Bool) (missing_1 : List Nat),
  ({ scope := scope, keepInitial := keepInitial, missing := missing } =
      { scope := scope_1, keepInitial := keepInitial_1, missing := missing_1 }) =
    (scope = scope_1 ∧ keepInitial = keepInitial_1 ∧ missing = missing_1)
'YulangClosure.NativeValuePorts.Protection.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_14

```lean
YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_14 : ∀ (a a_1 b : Nat),
  ¬a_1 = b → YulangClosure.NativeValuePorts.Port.record a a_1 = YulangClosure.NativeValuePorts.Port.record a b → False
'YulangClosure.NativeValuePorts.instDecidableEqPort.decEq._proof_14' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Cursor.mk.injEq

```lean
YulangClosure.NativeValuePorts.Cursor.mk.injEq : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (done todo : List YulangClosure.NativeValuePorts.Child) (pending : Option YulangClosure.NativeValuePorts.Receipt)
  (records : List YulangClosure.NativeValuePorts.Work) (queue : List YulangClosure.NativeValuePorts.NativeWork)
  (arena_1 : YulangClosure.NativeValuePorts.Arena) (done_1 todo_1 : List YulangClosure.NativeValuePorts.Child)
  (pending_1 : Option YulangClosure.NativeValuePorts.Receipt) (records_1 : List YulangClosure.NativeValuePorts.Work)
  (queue_1 : List YulangClosure.NativeValuePorts.NativeWork),
  ({ arena := arena, done := done, todo := todo, pending := pending, records := records, queue := queue } =
      { arena := arena_1, done := done_1, todo := todo_1, pending := pending_1, records := records_1,
        queue := queue_1 }) =
    (arena = arena_1 ∧ done = done_1 ∧ todo = todo_1 ∧ pending = pending_1 ∧ records = records_1 ∧ queue = queue_1)
'YulangClosure.NativeValuePorts.Cursor.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_1 : ∀ (a : YulangClosure.NativeValuePorts.Child)
  (a_1 : YulangClosure.NativeValuePorts.Receipt), { source := a, receipt := a_1 } = { source := a, receipt := a_1 }
'YulangClosure.NativeValuePorts.instDecidableEqWork.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.buildFlow.eq_1

```lean
YulangClosure.NativeValuePorts.buildFlow.eq_1 : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (parent : YulangClosure.NativeValuePorts.Key) (field : YulangClosure.NativeValuePorts.FunctionField),
  YulangClosure.NativeValuePorts.buildFlow arena parent (YulangClosure.NativeValuePorts.Port.function field) =
    if parent.flow.transformer ≠ 0 then Option.none
    else
      match parent.flow.demand with
      | Option.none => Option.some (arena, parent.flow)
      | Option.some demand =>
        if ¬YulangClosure.NativeValuePorts.genuineDemand parent demand then Option.none
        else
          match field with
          | YulangClosure.NativeValuePorts.FunctionField.argument => Option.some (arena, { })
          | YulangClosure.NativeValuePorts.FunctionField.result => Option.some (arena, { })
          | YulangClosure.NativeValuePorts.FunctionField.argumentEffect =>
            have result := arena.transformer (YulangClosure.NativeValuePorts.Transformer.stamp demand.inputRoute);
            Option.some (result.fst, { transformer := result.snd })
          | YulangClosure.NativeValuePorts.FunctionField.resultEffect =>
            have result :=
              arena.transformer
                (YulangClosure.NativeValuePorts.Transformer.protect demand.outputScope demand.inputRoute);
            Option.some (result.fst, { transformer := result.snd })
'YulangClosure.NativeValuePorts.buildFlow.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.FunctionField.argumentEffect.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.FunctionField.argumentEffect.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.FunctionField.argumentEffect =
  1
'YulangClosure.NativeValuePorts.FunctionField.argumentEffect.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_2 : ∀ (a : Nat) (a_1 : Bool) (a_2 b : List Nat),
  ¬a_2 = b →
    { scope := a, keepInitial := a_1, missing := a_2 } = { scope := a, keepInitial := a_1, missing := b } → False
'YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_2 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Option Nat) (a_2 b : Option (Nat × Nat)),
  ¬a_2 = b → { task := a, relation := a_1, replayAck := a_2 } = { task := a, relation := a_1, replayAck := b } → False
'YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_5 : ∀
  (lower upper : YulangClosure.NativeMergeExpansion.Endpoint)
  (lower_1 upper_1 : YulangClosure.NativeValuePorts.ValueEndpoint),
  YulangClosure.NativeValuePorts.Pair.effect lower upper = YulangClosure.NativeValuePorts.Pair.value lower_1 upper_1 →
    False
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_5' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.CursorValid.split

```lean
@YulangClosure.NativeValuePorts.CursorValid.split : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue cursor →
    cursor.done ++ cursor.todo = children.reverse
'YulangClosure.NativeValuePorts.CursorValid.split' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_2 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Nat) (a_2 : Option Nat) (a_3 b : YulangClosure.NativeValuePorts.Flow),
  ¬a_3 = b →
    { pair := a, context := a_1, sources := a_2, flow := a_3 } =
        { pair := a, context := a_1, sources := a_2, flow := b } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqKey.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Dependency.port.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Dependency.port.sizeOf_spec : ∀ (parent child : YulangClosure.NativeValuePorts.Key)
  (port : YulangClosure.NativeValuePorts.Port),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.Dependency.port parent child port) =
    1 + SizeOf.sizeOf parent + SizeOf.sizeOf child + SizeOf.sizeOf port
'YulangClosure.NativeValuePorts.Dependency.port.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.drive.eq_2

```lean
YulangClosure.NativeValuePorts.drive.eq_2 : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool)
  (x : YulangClosure.NativeValuePorts.Cursor) (n : Nat),
  YulangClosure.NativeValuePorts.drive views qv qe parent post derived n.succ x =
    match x.todo with
    | [] => Option.some x
    | child :: rest =>
      match x.pending with
      | Option.none => do
        let __x ← YulangClosure.NativeValuePorts.admit x.arena views qv qe parent post derived child
        match __x with
          | (arena, receipt) =>
            YulangClosure.NativeValuePorts.drive views qv qe parent post derived n (x.admitted arena receipt)
      | Option.some receipt =>
        YulangClosure.NativeValuePorts.drive views qv qe parent post derived n (x.enqueued child rest receipt)
'YulangClosure.NativeValuePorts.drive.eq_2' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.inj : ∀ {term term_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord term =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord term_1 →
    term = term_1
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Transformer.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Transformer.mk.sizeOf_spec : ∀ (stamped : List Nat)
  (scopes : List YulangClosure.NativeValuePorts.Protection),
  SizeOf.sizeOf { stamped := stamped, scopes := scopes } = 1 + SizeOf.sizeOf stamped + SizeOf.sizeOf scopes
'YulangClosure.NativeValuePorts.Transformer.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Protection.mk.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.Protection.mk.sizeOf_spec : ∀ (scope : Nat) (keepInitial : Bool) (missing : List Nat),
  SizeOf.sizeOf { scope := scope, keepInitial := keepInitial, missing := missing } =
    1 + SizeOf.sizeOf scope + SizeOf.sizeOf keepInitial + SizeOf.sizeOf missing
'YulangClosure.NativeValuePorts.Protection.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.buildFlow.eq_2

```lean
YulangClosure.NativeValuePorts.buildFlow.eq_2 : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (parent : YulangClosure.NativeValuePorts.Key) (port : YulangClosure.NativeValuePorts.Port),
  (∀ (field : YulangClosure.NativeValuePorts.FunctionField),
      port = YulangClosure.NativeValuePorts.Port.function field → False) →
    YulangClosure.NativeValuePorts.buildFlow arena parent port = Option.some (arena, parent.flow)
'YulangClosure.NativeValuePorts.buildFlow.eq_2' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.contextInputs.eq_4

```lean
YulangClosure.NativeValuePorts.contextInputs.eq_4 : ∀ (input certificate : Nat),
  YulangClosure.NativeValuePorts.contextInputs (YulangClosure.NativeContextExpansion.Expr.both input certificate) =
    [input]
'YulangClosure.NativeValuePorts.contextInputs.eq_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.AdmissionResult.derived_same

```lean
@YulangClosure.NativeValuePorts.AdmissionResult.derived_same : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {child : YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived child receipt →
    receipt.derived = derived
'YulangClosure.NativeValuePorts.AdmissionResult.derived_same' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Transformer.protect.eq_1

```lean
YulangClosure.NativeValuePorts.Transformer.protect.eq_1 : ∀ (scope input : Nat),
  YulangClosure.NativeValuePorts.Transformer.protect scope input =
    { stamped := [], scopes := [{ scope := scope, keepInitial := Bool.true, missing := [input] }] }
'YulangClosure.NativeValuePorts.Transformer.protect.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Cursor.enqueued.eq_1

```lean
YulangClosure.NativeValuePorts.Cursor.enqueued.eq_1 : ∀ (cursor : YulangClosure.NativeValuePorts.Cursor)
  (child : YulangClosure.NativeValuePorts.Child) (rest : List YulangClosure.NativeValuePorts.Child)
  (receipt : YulangClosure.NativeValuePorts.Receipt),
  cursor.enqueued child rest receipt =
    { arena := cursor.arena, done := cursor.done ++ [child], todo := rest,
      records := cursor.records ++ [{ source := child, receipt := receipt }],
      queue := { source := child, receipt := receipt }.native :: cursor.queue }
'YulangClosure.NativeValuePorts.Cursor.enqueued.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Witness.prefixed_argument_context

```lean
YulangClosure.NativeValuePorts.Witness.prefixed_argument_context : have result :=
  YulangClosure.NativeValuePorts.buildContext YulangClosure.NativeValuePorts.Witness.arena (Option.some 7) 1 Bool.true;
result.fst.contexts =
    [YulangClosure.NativeContextExpansion.Expr.without 0, YulangClosure.NativeContextExpansion.Expr.prefix 7 0,
      YulangClosure.NativeContextExpansion.Expr.swap 1, YulangClosure.NativeContextExpansion.Expr.prefix 7 3] ∧
  result.snd = 4
'YulangClosure.NativeValuePorts.Witness.prefixed_argument_context' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.stamp_preserves_protections

```lean
YulangClosure.NativeValuePorts.stamp_preserves_protections : ∀ (input scope : Nat) (inputs scopes : Nat → Prop),
  (YulangClosure.NativeValuePorts.Transformer.stamp input).protection inputs scopes scope ↔ scopes scope
'YulangClosure.NativeValuePorts.stamp_preserves_protections' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Transformer.mk.injEq

```lean
YulangClosure.NativeValuePorts.Transformer.mk.injEq : ∀ (stamped : List Nat)
  (scopes : List YulangClosure.NativeValuePorts.Protection) (stamped_1 : List Nat)
  (scopes_1 : List YulangClosure.NativeValuePorts.Protection),
  ({ stamped := stamped, scopes := scopes } = { stamped := stamped_1, scopes := scopes_1 }) =
    (stamped = stamped_1 ∧ scopes = scopes_1)
'YulangClosure.NativeValuePorts.Transformer.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.drive_constructs_run

```lean
@YulangClosure.NativeValuePorts.drive_constructs_run : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool} {fuel : Nat}
  {before after : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.drive views qv qe parent post derived fuel before = Option.some after →
    YulangClosure.NativeValuePorts.DispatchRun views qv qe parent post derived before after ∧ after.todo = []
'YulangClosure.NativeValuePorts.drive_constructs_run' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.Receipt.mk.injEq

```lean
YulangClosure.NativeValuePorts.Receipt.mk.injEq : ∀ (parent child : YulangClosure.NativeValuePorts.Key) (relation : Nat)
  (port : YulangClosure.NativeValuePorts.Port) (derived : Bool) (parent_1 child_1 : YulangClosure.NativeValuePorts.Key)
  (relation_1 : Nat) (port_1 : YulangClosure.NativeValuePorts.Port) (derived_1 : Bool),
  ({ parent := parent, child := child, relation := relation, port := port, derived := derived } =
      { parent := parent_1, child := child_1, relation := relation_1, port := port_1, derived := derived_1 }) =
    (parent = parent_1 ∧ child = child_1 ∧ relation = relation_1 ∧ port = port_1 ∧ derived = derived_1)
'YulangClosure.NativeValuePorts.Receipt.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.FunctionTerms.mk.injEq

```lean
YulangClosure.NativeValuePorts.FunctionTerms.mk.injEq : ∀
  (argument argumentEffect resultEffect result argument_1 argumentEffect_1 resultEffect_1 result_1 : Nat),
  ({ argument := argument, argumentEffect := argumentEffect, resultEffect := resultEffect, result := result } =
      { argument := argument_1, argumentEffect := argumentEffect_1, resultEffect := resultEffect_1,
        result := result_1 }) =
    (argument = argument_1 ∧ argumentEffect = argumentEffect_1 ∧ resultEffect = resultEffect_1 ∧ result = result_1)
'YulangClosure.NativeValuePorts.FunctionTerms.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.Arena.mk.inj

```lean
@YulangClosure.NativeValuePorts.Arena.mk.inj : ∀ {contexts : List YulangClosure.NativeContextExpansion.Expr}
  {transformers : List YulangClosure.NativeValuePorts.Transformer} {relations : List YulangClosure.NativeValuePorts.Key}
  {contexts_1 : List YulangClosure.NativeContextExpansion.Expr}
  {transformers_1 : List YulangClosure.NativeValuePorts.Transformer}
  {relations_1 : List YulangClosure.NativeValuePorts.Key},
  { contexts := contexts, transformers := transformers, relations := relations } =
      { contexts := contexts_1, transformers := transformers_1, relations := relations_1 } →
    contexts = contexts_1 ∧ transformers = transformers_1 ∧ relations = relations_1
'YulangClosure.NativeValuePorts.Arena.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.argument_effect_scope

```lean
@YulangClosure.NativeValuePorts.argument_effect_scope : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat}
  {derived : Bool} {task : YulangClosure.NativeValuePorts.Pair} {receipt : YulangClosure.NativeValuePorts.Receipt}
  {demand : YulangClosure.NativeContextExpansion.ScopedDemand},
  YulangClosure.NativeValuePorts.AdmissionResult arena views qv qe parent post derived
      {
        port :=
          YulangClosure.NativeValuePorts.Port.function YulangClosure.NativeValuePorts.FunctionField.argumentEffect,
        task := task }
      receipt →
    parent.flow.demand = Option.some demand →
      YulangClosure.NativeValuePorts.genuineDemand parent demand ∧
        receipt.child.flow.demand = Option.none ∧
          arena.transformerAt receipt.child.flow.transformer =
            Option.some (YulangClosure.NativeValuePorts.Transformer.stamp demand.inputRoute)
'YulangClosure.NativeValuePorts.argument_effect_scope' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_3 : ∀
  (a a_1 b b_1 : YulangClosure.NativeValuePorts.ValueEndpoint),
  ¬a = b → YulangClosure.NativeValuePorts.Pair.value a a_1 = YulangClosure.NativeValuePorts.Pair.value b b_1 → False
'YulangClosure.NativeValuePorts.instDecidableEqPair.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.row.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.row.sizeOf_spec : ∀ (id : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.row id) = 1 + SizeOf.sizeOf id
'YulangClosure.NativeValuePorts.ValueEndpoint.row.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_6

```lean
YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_6 : ∀
  (upper : YulangClosure.NativeValuePorts.ValueEndpoint) (term : Nat),
  upper = YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord term →
    YulangClosure.NativeValuePorts.ValueEndpoint.positiveRecord term = upper
'YulangClosure.NativeValuePorts.instDecidableGenuineDemand._proof_6' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.context_constructed

```lean
YulangClosure.NativeValuePorts.context_constructed : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (node : YulangClosure.NativeContextExpansion.Expr),
  (arena.context node).fst.contextAt (arena.context node).snd = Option.some node ∧
    arena.Extends (arena.context node).fst
'YulangClosure.NativeValuePorts.context_constructed' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValuePorts.Dependency.derived.inj

```lean
@YulangClosure.NativeValuePorts.Dependency.derived.inj : ∀
  {parent child parent_1 child_1 : YulangClosure.NativeValuePorts.Key},
  YulangClosure.NativeValuePorts.Dependency.derived parent child =
      YulangClosure.NativeValuePorts.Dependency.derived parent_1 child_1 →
    parent = parent_1 ∧ child = child_1
'YulangClosure.NativeValuePorts.Dependency.derived.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.contextInputs.eq_6

```lean
YulangClosure.NativeValuePorts.contextInputs.eq_6 : ∀ (lower upper : Nat),
  YulangClosure.NativeValuePorts.contextInputs (YulangClosure.NativeContextExpansion.Expr.replay lower upper) =
    [lower, upper]
'YulangClosure.NativeValuePorts.contextInputs.eq_6' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_1 : ∀ (a : Nat) (a_1 : List Nat),
  { tag := a, payloads := a_1 } = { tag := a, payloads := a_1 }
'YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.next_source_index

```lean
@YulangClosure.NativeValuePorts.next_source_index : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {cursor : YulangClosure.NativeValuePorts.Cursor} {child : YulangClosure.NativeValuePorts.Child}
  {rest : List YulangClosure.NativeValuePorts.Child},
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue cursor →
    cursor.todo = child :: rest → children.reverse[cursor.done.length]? = Option.some child
'YulangClosure.NativeValuePorts.next_source_index' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_1 : ∀ (a : YulangClosure.NativeValuePorts.Port)
  (a_1 : YulangClosure.NativeValuePorts.Pair), { port := a, task := a_1 } = { port := a, task := a_1 }
'YulangClosure.NativeValuePorts.instDecidableEqChild.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Transformer.stamp.eq_1

```lean
YulangClosure.NativeValuePorts.Transformer.stamp.eq_1 : ∀ (input : Nat),
  YulangClosure.NativeValuePorts.Transformer.stamp input = { stamped := [input], scopes := [] }
'YulangClosure.NativeValuePorts.Transformer.stamp.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.initialCursor.eq_1

```lean
YulangClosure.NativeValuePorts.initialCursor.eq_1 : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (children : List YulangClosure.NativeValuePorts.Child) (queue : List YulangClosure.NativeValuePorts.NativeWork),
  YulangClosure.NativeValuePorts.initialCursor arena children queue =
    { arena := arena, todo := children.reverse, queue := queue }
'YulangClosure.NativeValuePorts.initialCursor.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_2 : ∀ (a : Nat) (a_1 b : List Nat),
  ¬a_1 = b → { tag := a, payloads := a_1 } = { tag := a, payloads := b } → False
'YulangClosure.NativeValuePorts.instDecidableEqAlternative.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.CursorValid.records

```lean
@YulangClosure.NativeValuePorts.CursorValid.records : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue cursor →
    List.map YulangClosure.NativeValuePorts.Work.source cursor.records = cursor.done
'YulangClosure.NativeValuePorts.CursorValid.records' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.bottomPositive.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.bottomPositive.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.bottomPositive =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.bottomPositive.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.variantChildren.eq_def

```lean
YulangClosure.NativeValuePorts.variantChildren.eq_def : ∀ (terms : YulangClosure.NativeValuePorts.TermEndpoints)
  (upper : List YulangClosure.NativeValuePorts.Alternative) (x : Nat)
  (x_1 : List YulangClosure.NativeValuePorts.Alternative),
  YulangClosure.NativeValuePorts.variantChildren terms upper x x_1 =
    match x, x_1 with
    | x, [] => Except.ok []
    | index, actual :: rest =>
      if upper.any (YulangClosure.NativeValuePorts.matching actual) = Bool.true then
        Except.map (fun x => YulangClosure.NativeValuePorts.variantArmChildren terms index actual upper ++ x)
          (YulangClosure.NativeValuePorts.variantChildren terms upper (index + 1) rest)
      else Except.error index
'YulangClosure.NativeValuePorts.variantChildren.eq_def' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.drive.eq_1

```lean
YulangClosure.NativeValuePorts.drive.eq_1 : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool)
  (x : YulangClosure.NativeValuePorts.Cursor),
  YulangClosure.NativeValuePorts.drive views qv qe parent post derived 0 x =
    if x.todo = [] then Option.some x else Option.none
'YulangClosure.NativeValuePorts.drive.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_7

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_7 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 b : YulangClosure.NativeValuePorts.Port),
  ¬a_2 = b →
    YulangClosure.NativeValuePorts.Dependency.port a a_1 a_2 = YulangClosure.NativeValuePorts.Dependency.port a a_1 b →
      False
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_7' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Pair.effect.injEq

```lean
YulangClosure.NativeValuePorts.Pair.effect.injEq : ∀
  (lower upper lower_1 upper_1 : YulangClosure.NativeMergeExpansion.Endpoint),
  (YulangClosure.NativeValuePorts.Pair.effect lower upper =
      YulangClosure.NativeValuePorts.Pair.effect lower_1 upper_1) =
    (lower = lower_1 ∧ upper = upper_1)
'YulangClosure.NativeValuePorts.Pair.effect.injEq' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_3

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_3 : ∀
  (motive : YulangClosure.NativeContextExpansion.Expr → Sort u_1) (input : Nat)
  (h_1 : (weight input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.prefix weight input))
  (h_2 : (input weight : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.suffix input weight))
  (h_3 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.swap input))
  (h_4 : (input certificate : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.both input certificate))
  (h_5 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.without input))
  (h_6 : (lower upper : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.replay lower upper)),
  (match YulangClosure.NativeContextExpansion.Expr.swap input with
    | YulangClosure.NativeContextExpansion.Expr.prefix weight input => h_1 weight input
    | YulangClosure.NativeContextExpansion.Expr.suffix input weight => h_2 input weight
    | YulangClosure.NativeContextExpansion.Expr.swap input => h_3 input
    | YulangClosure.NativeContextExpansion.Expr.both input certificate => h_4 input certificate
    | YulangClosure.NativeContextExpansion.Expr.without input => h_5 input
    | YulangClosure.NativeContextExpansion.Expr.replay lower upper => h_6 lower upper) =
    h_3 input
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_3' does not depend on any axioms
```

### _private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_6

```lean
_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_6 : ∀
  (motive : YulangClosure.NativeContextExpansion.Expr → Sort u_1) (lower upper : Nat)
  (h_1 : (weight input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.prefix weight input))
  (h_2 : (input weight : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.suffix input weight))
  (h_3 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.swap input))
  (h_4 : (input certificate : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.both input certificate))
  (h_5 : (input : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.without input))
  (h_6 : (lower upper : Nat) → motive (YulangClosure.NativeContextExpansion.Expr.replay lower upper)),
  (match YulangClosure.NativeContextExpansion.Expr.replay lower upper with
    | YulangClosure.NativeContextExpansion.Expr.prefix weight input => h_1 weight input
    | YulangClosure.NativeContextExpansion.Expr.suffix input weight => h_2 input weight
    | YulangClosure.NativeContextExpansion.Expr.swap input => h_3 input
    | YulangClosure.NativeContextExpansion.Expr.both input certificate => h_4 input certificate
    | YulangClosure.NativeContextExpansion.Expr.without input => h_5 input
    | YulangClosure.NativeContextExpansion.Expr.replay lower upper => h_6 lower upper) =
    h_6 lower upper
'_private.YulangClosure.NativeValuePorts.0.YulangClosure.NativeValuePorts.contextInputs.match_1.eq_6' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_4

```lean
YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_4 : ∀ (a : YulangClosure.NativeValuePorts.Pair)
  (a_1 : Option Nat) (a_2 : Option (Nat × Nat)) (b : YulangClosure.NativeValuePorts.Pair) (b_1 : Option Nat)
  (b_2 : Option (Nat × Nat)),
  ¬a = b → { task := a, relation := a_1, replayAck := a_2 } = { task := b, relation := b_1, replayAck := b_2 } → False
'YulangClosure.NativeValuePorts.instDecidableEqNativeWork.decEq._proof_4' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.context_result_kept

```lean
@YulangClosure.NativeValuePorts.context_result_kept : ∀ {before after : YulangClosure.NativeValuePorts.Arena},
  before.Extends after →
    ∀ {weight : Option Nat} {post id : Nat} {swap : Bool},
      YulangClosure.NativeValuePorts.ContextResult before weight post swap id →
        YulangClosure.NativeValuePorts.ContextResult after weight post swap id
'YulangClosure.NativeValuePorts.context_result_kept' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_1

```lean
YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_1 : ∀ (a : Nat) (a_1 : Bool) (a_2 : List Nat),
  { scope := a, keepInitial := a_1, missing := a_2 } = { scope := a, keepInitial := a_1, missing := a_2 }
'YulangClosure.NativeValuePorts.instDecidableEqProtection.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.CursorValid.queue_exact

```lean
@YulangClosure.NativeValuePorts.CursorValid.queue_exact : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {children : List YulangClosure.NativeValuePorts.Child} {queue : List YulangClosure.NativeValuePorts.NativeWork}
  {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived children queue cursor →
    cursor.queue = List.map YulangClosure.NativeValuePorts.Work.native cursor.records.reverse ++ queue
'YulangClosure.NativeValuePorts.CursorValid.queue_exact' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.intPositive.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.intPositive.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeValuePorts.ValueEndpoint.intPositive =
  1
'YulangClosure.NativeValuePorts.ValueEndpoint.intPositive.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_3

```lean
YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_3 : ∀ (a : Nat)
  (a_1 : Option YulangClosure.NativeContextExpansion.ScopedDemand) (b : Nat)
  (b_1 : Option YulangClosure.NativeContextExpansion.ScopedDemand),
  ¬a = b → { transformer := a, demand := a_1 } = { transformer := b, demand := b_1 } → False
'YulangClosure.NativeValuePorts.instDecidableEqFlow.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.Witness.arena_context_formed

```lean
YulangClosure.NativeValuePorts.Witness.arena_context_formed : YulangClosure.NativeValuePorts.ContextsFormed
  YulangClosure.NativeValuePorts.Witness.arena.contexts
'YulangClosure.NativeValuePorts.Witness.arena_context_formed' depends on axioms: [propext]
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.inj

```lean
@YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.inj : ∀ {term term_1 : Nat},
  YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction term =
      YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction term_1 →
    term = term_1
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeFunction.inj' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_2

```lean
YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_2 : ∀ (a b : Nat),
  ¬a = b →
    YulangClosure.NativeValuePorts.ValueEndpoint.row a = YulangClosure.NativeValuePorts.ValueEndpoint.row b → False
'YulangClosure.NativeValuePorts.instDecidableEqValueEndpoint.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.sizeOf_spec : ∀ (term : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord term) = 1 + SizeOf.sizeOf term
'YulangClosure.NativeValuePorts.ValueEndpoint.negativeRecord.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.sizeOf_spec

```lean
YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.sizeOf_spec : ∀ (term : Nat),
  SizeOf.sizeOf (YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction term) = 1 + SizeOf.sizeOf term
'YulangClosure.NativeValuePorts.ValueEndpoint.positiveFunction.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_6

```lean
YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_6 : ∀ (a a_1 : YulangClosure.NativeValuePorts.Key)
  (a_2 : Nat) (a_3 : YulangClosure.NativeValuePorts.Port) (a_4 : Bool) (b b_1 : YulangClosure.NativeValuePorts.Key)
  (b_2 : Nat) (b_3 : YulangClosure.NativeValuePorts.Port) (b_4 : Bool),
  ¬a = b →
    { parent := a, child := a_1, relation := a_2, port := a_3, derived := a_4 } =
        { parent := b, child := b_1, relation := b_2, port := b_3, derived := b_4 } →
      False
'YulangClosure.NativeValuePorts.instDecidableEqReceipt.decEq._proof_6' does not depend on any axioms
```

### YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_5

```lean
YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_5 : ∀
  (parent child : YulangClosure.NativeValuePorts.Key) (port : YulangClosure.NativeValuePorts.Port)
  (parent_1 child_1 : YulangClosure.NativeValuePorts.Key),
  YulangClosure.NativeValuePorts.Dependency.port parent child port =
      YulangClosure.NativeValuePorts.Dependency.derived parent_1 child_1 →
    False
'YulangClosure.NativeValuePorts.instDecidableEqDependency.decEq._proof_5' does not depend on any axioms
```

## Ownership and stop

Primary-owned exact paths: `NativeValuePorts.lean`, the construction note, and this inbox. All other artifacts are under `/workspace/scratch/f98087c7ac1a/value-ports-r4/`. All source/code/documentation writes for this packet stopped at 2026-10-26T11:54:23.588939+00:00. The primary continues unrelated integration and live-team work; these frozen packet files will not be edited during review without a new explicit revision. No descendant authored this packet.
